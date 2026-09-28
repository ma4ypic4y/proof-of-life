#!/usr/bin/env python3
"""Assemble a time-lapse from render_dots.py frames.

Frames before the lineage appears and after it has taken over play fast; the
frames in between (the origin itself) play slowly. Writes <out>.mp4, a poster
PNG (last frame) and a JSON timeline so a page can show the epoch and strand
counts in sync with video.currentTime.

usage: make_film.py <frames_dir> <out_prefix> [--seed 52] [--slow 0.4] [--fast 0.07] [--hold 2.0]
"""
import csv, json, os, subprocess, sys

frames, out = sys.argv[1:3]
arg = lambda k, d: type(d)(sys.argv[sys.argv.index(k) + 1]) if k in sys.argv else d
seed, slow, fast, hold = arg("--seed", 52), arg("--slow", 0.4), arg("--fast", 0.07), arg("--hold", 2.0)
width = arg("--width", 0)  # 0 = frame size; e.g. 512 halves the 2x frames back to one pixel per program
crf = arg("--crf", 18)
FF = os.environ.get("FFMPEG", "ffmpeg")

rows = list(csv.DictReader(open(os.path.join(frames, "stats.csv"))))
N = 131072
epoch = [int(r["epoch"]) for r in rows]
plus = [int(r["plus"]) for r in rows]
minus = [int(r["minus"]) for r in rows]
peak = max(p + m for p, m in zip(plus, minus))
dur = []
for i, (p, m) in enumerate(zip(plus, minus)):
    live = p + m
    dur.append(slow if 0 < live < 0.9 * peak else fast)
dur[-1] = hold
# lead-in: hold the first (noise) frame a little
dur[0] = max(dur[0], 0.8)
t, acc = [], 0.0
for d in dur:
    t.append(round(acc, 3))
    acc += d
lst = out + ".concat.txt"
with open(lst, "w") as f:
    for e, d in zip(epoch, dur):
        f.write(f"file '{os.path.abspath(os.path.join(frames, f'{e:06d}.png'))}'\nduration {d}\n")
    f.write(f"file '{os.path.abspath(os.path.join(frames, f'{epoch[-1]:06d}.png'))}'\n")
subprocess.run([FF, "-y", "-loglevel", "error", "-f", "concat", "-safe", "0", "-i", lst,
                "-vf", ("fps=30," + (f"scale={width}:-2:flags=neighbor," if width else "") + "format=yuv420p"),
                "-c:v", "libx264", "-preset", "slow", "-crf", str(crf),
                "-movflags", "+faststart", out + ".mp4"], check=True)
subprocess.run([FF, "-y", "-loglevel", "error", "-i", os.path.join(frames, f"{epoch[-1]:06d}.png"), out + "-poster.png"], check=True)
os.remove(lst)
json.dump({"seed": seed, "epoch": epoch, "plus": plus, "minus": minus, "t": t, "duration": round(acc, 3)},
          open(out + ".json", "w"), separators=(",", ":"))
print(out + ".mp4", f"{acc:.1f}s", os.path.getsize(out + ".mp4"), "bytes")
