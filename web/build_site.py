#!/usr/bin/env python3
"""Build the public GitHub Pages site into docs/:
  docs/index.html        landing page with the video
  docs/proof/            Proof of Life (Lean atlas + birth certificate)
  docs/life/             Life Copied Backwards (the mirror-strand study)
Run web/build.py and web/build_proof.py first."""
import os, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..")
DOCS = os.path.join(ROOT, "docs")
REPO = "https://github.com/ma4ypic4y/proof-of-life"
HEAD = ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">'
        '<style>html{color-scheme:light dark}body{margin:0}</style></head><body>')
TAIL = "</body></html>\n"


def page(src, dst_dir, extra_repl=()):
    html = open(src).read()
    for a, b in extra_repl:
        html = html.replace(a, b)
    os.makedirs(dst_dir, exist_ok=True)
    open(os.path.join(dst_dir, "index.html"), "w").write(HEAD + html + TAIL)


if os.path.exists(DOCS):
    shutil.rmtree(DOCS)
os.makedirs(DOCS)
code_link = f' Code, proofs and data: <a href="{REPO}">{REPO.replace("https://", "")}</a>.</footer>'
page(os.path.join(HERE, "dist-proof/index.html"), os.path.join(DOCS, "proof"),
     [("https://claude.ai/artifact/SgUQ4tQDTmwbqrzp7pgqyY", "../life/"), (".</footer>", "." + code_link)])
page(os.path.join(HERE, "dist/index.html"), os.path.join(DOCS, "life"),
     [(" the prompt soup are ours.</footer>", " the prompt soup are ours." + code_link)])
shutil.copytree(os.path.join(HERE, "dist/img"), os.path.join(DOCS, "life/img"))
os.makedirs(os.path.join(DOCS, "media"))
shutil.copy(os.path.join(ROOT, "media/proof_of_life_720p.mp4"), os.path.join(DOCS, "media/proof_of_life_720p.mp4"))
shutil.copy(os.path.join(ROOT, "media/poster.png"), os.path.join(DOCS, "media/poster.png"))
landing = open(os.path.join(HERE, "src/landing.html")).read().replace("{{REPO}}", REPO)
open(os.path.join(DOCS, "index.html"), "w").write(HEAD + landing + TAIL)
open(os.path.join(DOCS, ".nojekyll"), "w").write("")
print("docs/ built:", sorted(os.listdir(DOCS)))
