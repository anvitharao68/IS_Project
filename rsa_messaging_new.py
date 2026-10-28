import hashlib
import secrets
import sys
import time

HASH = hashlib.sha256
HLEN = HASH().digest_size
SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


def is_prime(n, rounds=40):
    if n < 2:
        return False
    for p in SMALL_PRIMES:
        if n == p:
            return True
        if n % p == 0:
            return False
    d, r = n - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for _ in range(rounds):
        a = secrets.randbelow(n - 3) + 2
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def generate_prime(bits):
    while True:
        c = secrets.randbits(bits) | (1 << (bits - 1)) | (1 << (bits - 2)) | 1
        if is_prime(c):
            return c


def generate_keypair(bits=2048, e=65537):
    while True:
        p = generate_prime(bits // 2)
        q = generate_prime(bits // 2)
        if p == q:
            continue
        phi = (p - 1) * (q - 1)
        if phi % e == 0:
            continue
        n = p * q
        if n.bit_length() != bits:
            continue
        d = pow(e, -1, phi)
        return (n, e), (n, d)


def mgf1(seed, length):
    out = b""
    counter = 0
    while len(out) < length:
        out += HASH(seed + counter.to_bytes(4, "big")).digest()
        counter += 1
    return out[:length]


def xor(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def key_size(n):
    return (n.bit_length() + 7) // 8


def oaep_encode(message, k, label=b""):
    if len(message) > k - 2 * HLEN - 2:
        raise ValueError("message too long")
    l_hash = HASH(label).digest()
    ps = b"\x00" * (k - len(message) - 2 * HLEN - 2)
    db = l_hash + ps + b"\x01" + message
    seed = secrets.token_bytes(HLEN)
    masked_db = xor(db, mgf1(seed, k - HLEN - 1))
    masked_seed = xor(seed, mgf1(masked_db, HLEN))
    return b"\x00" + masked_seed + masked_db


def oaep_decode(encoded, k, label=b""):
    if len(encoded) != k or k < 2 * HLEN + 2:
        raise ValueError("decryption error")
    masked_seed = encoded[1:1 + HLEN]
    masked_db = encoded[1 + HLEN:]
    seed = xor(masked_seed, mgf1(masked_db, HLEN))
    db = xor(masked_db, mgf1(seed, k - HLEN - 1))
    l_hash = HASH(label).digest()
    rest = db[HLEN:]
    idx = rest.find(b"\x01")
    valid = (
        encoded[0] == 0
        and secrets.compare_digest(db[:HLEN], l_hash)
        and idx != -1
        and rest[:idx].count(b"\x00") == idx
    )
    if not valid:
        raise ValueError("decryption error")
    return rest[idx + 1:]


def encrypt(plaintext, public_key):
    n, e = public_key
    k = key_size(n)
    step = k - 2 * HLEN - 2
    blocks = []
    for i in range(0, max(len(plaintext), 1), step):
        chunk = plaintext[i:i + step]
        m = int.from_bytes(oaep_encode(chunk, k), "big")
        blocks.append(pow(m, e, n).to_bytes(k, "big"))
    return b"".join(blocks)


def decrypt(ciphertext, private_key):
    n, d = private_key
    k = key_size(n)
    if len(ciphertext) % k:
        raise ValueError("invalid ciphertext length")
    out = b""
    for i in range(0, len(ciphertext), k):
        c = int.from_bytes(ciphertext[i:i + k], "big")
        if c >= n:
            raise ValueError("decryption error")
        out += oaep_decode(pow(c, d, n).to_bytes(k, "big"), k)
    return out


def pkcs1_pad(message, k):
    digest = HASH(message).digest()
    prefix = bytes.fromhex("3031300d060960864801650304020105000420")
    t = prefix + digest
    return b"\x00\x01" + b"\xff" * (k - len(t) - 3) + b"\x00" + t


def sign(message, private_key):
    n, d = private_key
    k = key_size(n)
    m = int.from_bytes(pkcs1_pad(message, k), "big")
    return pow(m, d, n).to_bytes(k, "big")


def verify(message, signature, public_key):
    n, e = public_key
    k = key_size(n)
    if len(signature) != k:
        return False
    s = int.from_bytes(signature, "big")
    if s >= n:
        return False
    return pow(s, e, n).to_bytes(k, "big") == pkcs1_pad(message, k)


def fingerprint(public_key):
    n, e = public_key
    raw = n.to_bytes(key_size(n), "big") + e.to_bytes(4, "big")
    h = hashlib.sha256(raw).hexdigest()
    return ":".join(h[i:i + 4] for i in range(0, 32, 4))


class User:
    def __init__(self, name, bits=2048):
        self.name = name
        self.public_key, self._private_key = generate_keypair(bits)

    def send(self, server, recipient, text):
        pub = server.lookup(recipient)
        data = text.encode()
        envelope = {
            "sender": self.name,
            "recipient": recipient,
            "ciphertext": encrypt(data, pub),
            "signature": sign(data, self._private_key),
            "timestamp": time.time(),
        }
        server.deliver(envelope)

    def read_inbox(self, server):
        messages = []
        for env in server.fetch(self.name):
            try:
                data = decrypt(env["ciphertext"], self._private_key)
            except ValueError:
                messages.append((env["sender"], env["timestamp"], None, False))
                continue
            ok = verify(data, env["signature"], server.lookup(env["sender"]))
            messages.append((env["sender"], env["timestamp"], data.decode(errors="replace"), ok))
        return messages


class Server:
    def __init__(self):
        self.directory = {}
        self.mailboxes = {}

    def register(self, name, public_key):
        if name in self.directory:
            raise ValueError("username taken")
        self.directory[name] = public_key
        self.mailboxes[name] = []

    def lookup(self, name):
        if name not in self.directory:
            raise KeyError("unknown user")
        return self.directory[name]

    def deliver(self, envelope):
        self.mailboxes[self.lookup_name(envelope["recipient"])].append(envelope)

    def lookup_name(self, name):
        if name not in self.mailboxes:
            raise KeyError("unknown user")
        return name

    def fetch(self, name):
        return list(self.mailboxes[name])


def fmt_time(ts):
    return time.strftime("%H:%M:%S", time.localtime(ts))


def demo():
    server = Server()
    alice = User("alice")
    bob = User("bob")
    server.register("alice", alice.public_key)
    server.register("bob", bob.public_key)
    print("alice fingerprint:", fingerprint(alice.public_key))
    print("bob fingerprint:  ", fingerprint(bob.public_key))
    alice.send(server, "bob", "Hi Bob, the meeting is at 10 AM.")
    bob.send(server, "alice", "Got it Alice. See you there.")
    print("\nciphertext on server (hex, truncated):")
    print(server.mailboxes["bob"][0]["ciphertext"].hex()[:96] + "...")
    for owner in (bob, alice):
        print(f"\n{owner.name}'s inbox:")
        for sender, ts, text, ok in owner.read_inbox(server):
            print(f"[{fmt_time(ts)}] {sender}: {text}  (signature {'valid' if ok else 'INVALID'})")
    long_msg = "x" * 1000
    alice.send(server, "bob", long_msg)
    last = bob.read_inbox(server)[-1]
    print("\nlong message round trip:", last[2] == long_msg)
    env = dict(server.mailboxes["bob"][0])
    tampered = bytearray(env["ciphertext"])
    tampered[10] ^= 1
    try:
        decrypt(bytes(tampered), bob._private_key)
        print("tamper test: not detected")
    except ValueError:
        print("tamper test: detected")


def cli():
    server = Server()
    users = {}
    menu = "\n1) Register user\n2) List users\n3) Send message\n4) Read inbox\n5) Show raw ciphertext\n6) Exit"
    print("RSA Secure Messaging System", flush=True)

    def pick(prompt):
        if not users:
            print("no users registered, use option 1 first")
            return None
        name = input(f"{prompt} {list(users)}: ").strip()
        if name not in users:
            print("unknown user")
            return None
        return name

    while True:
        try:
            print(menu, flush=True)
            choice = input("> ").strip()
        except (EOFError, KeyboardInterrupt):
            break
        if choice == "1":
            name = input("username: ").strip()
            if not name or name in users:
                print("invalid or taken")
                continue
            bits = input("key size [1024/2048, default 2048]: ").strip() or "2048"
            if bits not in ("1024", "2048"):
                print("invalid key size")
                continue
            print("generating keys...")
            u = User(name, int(bits))
            users[name] = u
            server.register(name, u.public_key)
            print("registered, fingerprint:", fingerprint(u.public_key))
        elif choice == "2":
            if not server.directory:
                print("no users registered")
            for name, pub in server.directory.items():
                print(name, fingerprint(pub), f"{pub[0].bit_length()}-bit")
        elif choice == "3":
            s = pick("from")
            if s is None:
                continue
            r = pick("to")
            if r is None:
                continue
            users[s].send(server, r, input("message: "))
            print("sent")
        elif choice == "4":
            name = pick("user")
            if name is None:
                continue
            msgs = users[name].read_inbox(server)
            if not msgs:
                print("inbox empty")
            for sender, ts, text, ok in msgs:
                print(f"[{fmt_time(ts)}] {sender}: {text}  (signature {'valid' if ok else 'INVALID'})")
        elif choice == "5":
            name = pick("user")
            if name is None:
                continue
            envs = server.fetch(name)
            if not envs:
                print("inbox empty")
            for env in envs:
                print(env["sender"], env["ciphertext"].hex()[:128] + "...")
        elif choice == "6":
            break
        else:
            print("enter a number from 1 to 6")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "demo":
        demo()
    else:
        cli()
