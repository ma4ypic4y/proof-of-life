#!/usr/bin/env python3
"""Render a soup checkpoint as a mosaic: one 8x8 tile per program, one pixel per byte.

Tiles whose bytes match the genome (>= 48 of 64) are painted in the + colour,
tiles matching the reversed genome in the - colour; everything else shows its
bytes by instruction class on a dark ground. Writes a PNG via ffmpeg (no numpy).

usage: render_soup.py soup.dat genome_hex out.png [--cols 256] [--rows 128] [--scale 1] [--code]

--code: classify tiles by identity at the genome's instruction positions only
(>= 80%), which tolerates drifted filler bytes.
"""
import os, struct, subprocess, sys

src, genome_hex, out = sys.argv[1:4]
opt = lambda k, d: int(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
cols, rows, scale = opt("--cols", 256), opt("--rows", 128), opt("--scale", 1)

data = open(src, "rb").read()
_, n, _ = struct.unpack("<QQQ", data[:24])
soup = data[24:]
p = bytes.fromhex(genome_hex)
r = p[::-1]
CODE = "--code" in sys.argv
OPSET = set(b"<>{}+-.,[]")
ip = [i for i in range(64) if p[i] in OPSET]
ir = [i for i in range(64) if r[i] in OPSET]

BG = (12, 17, 16)
OPC = {60: (154, 140, 245), 62: (154, 140, 245), 123: (154, 140, 245), 125: (154, 140, 245),
       43: (240, 163, 58), 45: (240, 163, 58), 46: (240, 90, 162), 44: (240, 90, 162),
       91: (44, 195, 156), 93: (44, 195, 156)}
PLUS, MINUS = (91, 155, 255), (255, 138, 76)
FILL = (30, 40, 38)


def shade(c, k):
    return tuple(int(x * k) for x in c)


W, H = cols * 8, rows * 8
img = bytearray(W * H * 3)
for t in range(min(n, cols * rows)):
    prog = soup[t * 64:(t + 1) * 64]
    if CODE:
        f = sum(prog[i] == p[i] for i in ip) / len(ip)
        g = sum(prog[i] == r[i] for i in ir) / len(ir)
        tint = PLUS if f >= 0.8 and f >= g else MINUS if g >= 0.8 else None
    else:
        f = sum(a == b for a, b in zip(prog, p))
        g = sum(a == b for a, b in zip(prog, r))
        tint = PLUS if f >= 48 else MINUS if g >= 48 else None
    tx, ty = (t % cols) * 8, (t // cols) * 8
    for i, v in enumerate(prog):
        if tint:
            c = shade(tint, 0.55) if v in OPC else tint
        else:
            c = shade(OPC[v], 0.8) if v in OPC else (200, 60, 45) if v == 0 else FILL
        o = ((ty + i // 8) * W + tx + i % 8) * 3
        img[o:o + 3] = bytes(c)
raw = out + ".rgb"
open(raw, "wb").write(img)
subprocess.run([os.environ.get("FFMPEG", "ffmpeg"), "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{W}x{H}",
                "-i", raw, "-vf", f"scale={W * scale}:{H * scale}:flags=neighbor", out], check=True)
os.remove(raw)
print(out, W * scale, "x", H * scale)
