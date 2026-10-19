"""Ethereum hex/word/calldata helpers for Liquity V2 historical archive reads."""
import hashlib

_RC = (
    0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
)
_ROT = (
    (0, 36, 3, 41, 18),
    (1, 44, 10, 45, 2),
    (62, 6, 43, 15, 61),
    (28, 55, 25, 21, 56),
    (27, 20, 39, 8, 14),
)
_MASK64 = (1 << 64) - 1


def keccak256(data: bytes) -> str:
    """Compute Ethereum Keccak-256 hex digest with 0x prefix using standard sponge."""
    msg = bytearray(data) + b'\x01'
    while len(msg) % 136 != 0:
        msg.append(0)
    msg[-1] ^= 0x80
    state = [[0] * 5 for _ in range(5)]
    for off in range(0, len(msg), 136):
        for i in range(17):
            state[i % 5][i // 5] ^= int.from_bytes(msg[off + i * 8 : off + i * 8 + 8], 'little')
        for rc in _RC:
            c = [state[x][0] ^ state[x][1] ^ state[x][2] ^ state[x][3] ^ state[x][4] for x in range(5)]
            d = [c[(x - 1) % 5] ^ (((c[(x + 1) % 5] << 1) | (c[(x + 1) % 5] >> 63)) & _MASK64) for x in range(5)]
            for x in range(5):
                for y in range(5):
                    state[x][y] ^= d[x]
            b = [[0] * 5 for _ in range(5)]
            for x in range(5):
                for y in range(5):
                    r = _ROT[x][y]
                    v = state[x][y]
                    b[y][(2 * x + 3 * y) % 5] = ((v << r) | (v >> (64 - r))) & _MASK64 if r else v
            for x in range(5):
                b0, b1, b2, b3, b4 = b[x][0], b[x][1], b[x][2], b[x][3], b[x][4]
                for y in range(5):
                    state[x][y] = b[x][y] ^ ((~b[(x + 1) % 5][y]) & b[(x + 2) % 5][y])
            state[0][0] ^= rc
    return '0x' + b''.join(state[i % 5][i // 5].to_bytes(8, 'little') for i in range(4)).hex()


def integer(x) -> int:
    """Convert hex string or integer representation to Python int."""
    if isinstance(x, str) and x.startswith(('0x', '0X')):
        return 0 if len(x) <= 2 else int(x, 16)
    return int(x)


def words(data: str) -> list[int]:
    """Decode 0x-prefixed hex return data into 32-byte unsigned integer words."""
    s = data[2:] if isinstance(data, str) and data.startswith(('0x', '0X')) else str(data or '')
    return [int(s[i : i + 64], 16) for i in range(0, len(s), 64) if s[i : i + 64]]


def calldata(sig: str, *args) -> str:
    """Format 4-byte function selector and 32-byte ABI-encoded static arguments."""
    if sig.startswith(('0x', '0X')) and len(sig) == 10:
        selector = sig.lower()
    else:
        try:
            selector = keccak256(sig.encode('utf-8'))[:10]
        except Exception:
            selector = '0x' + hashlib.sha3_256(sig.encode('utf-8')).hexdigest()[:8]
    encoded = []
    for a in args:
        v = integer(a)
        if v < 0:
            v += 1 << 256
        encoded.append(f'{v:064x}')
    return selector + ''.join(encoded)
