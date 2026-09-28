#!/usr/bin/env python3
"""One pixel per program: render every snapshot in a directory as a frame.

+ lineage (>= 80% of the genome's instruction bytes in place) is blue, the
mirror lineage orange; any other program is grey, brighter with more
instruction bytes. usage: render_dots.py <snap_dir> <genome_hex> <out_dir> [--cols 512]"""
import glob, os, struct, subprocess, sys

snap_dir, genome_hex, out_dir = sys.argv[1:4]
cols = int(sys.argv[sys.argv.index("--cols") + 1]) if "--cols" in sys.argv else 512
FF = os.environ.get("FFMPEG", "ffmpeg")
OPS = set(b"<>{}+-.,[]")
p = bytes.fromhex(genome_hex); r = p[::-1]
ip = [i for i in range(64) if p[i] in OPS]; ir = [i for i in range(64) if r[i] in OPS]
PLUS, MINUS = bytes((91, 155, 255)), bytes((255, 138, 76))
GREY = [bytes((14 + k, 19 + k, 18 + k)) for k in range(40)]  # dark, so the strands stand out
os.makedirs(out_dir, exist_ok=True)
stats = []
for f in sorted(glob.glob(os.path.join(snap_dir, "snap_*.dat")), key=lambda x: int(x.split("_")[-1][:-4])):
    epoch = int(f.split("_")[-1][:-4])
    data = open(f, "rb").read()
    n = struct.unpack("<QQQ", data[:24])[1]
    soup = data[24:]
    rows = n // cols
    img = bytearray(n * 3)
    plus = minus = 0
    for t in range(n):
        q = soup[t * 64:(t + 1) * 64]
        a = sum(q[i] == p[i] for i in ip) / len(ip)
        b = sum(q[i] == r[i] for i in ir) / len(ir)
        if a >= 0.8 and a >= b: c = PLUS; plus += 1
        elif b >= 0.8: c = MINUS; minus += 1
        else: c = GREY[min(39, sum(x in OPS for x in q) * 2)]
        img[t * 3:t * 3 + 3] = c
    raw = os.path.join(out_dir, f"{epoch}.rgb")
    open(raw, "wb").write(img)
    subprocess.run([FF, "-y", "-loglevel", "error", "-f", "rawvideo", "-pix_fmt", "rgb24", "-s", f"{cols}x{rows}",
                    "-i", raw, "-vf", "scale=iw*2:ih*2:flags=neighbor", os.path.join(out_dir, f"{epoch:06d}.png")], check=True)
    os.remove(raw)
    stats.append((epoch, plus, minus))
    print(epoch, plus, minus, flush=True)
open(os.path.join(out_dir, "stats.csv"), "w").write("epoch,plus,minus\n" + "".join(f"{e},{a},{b}\n" for e, a, b in stats))
