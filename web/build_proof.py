#!/usr/bin/env python3
"""Inline web/data/proof.json into web/src/proof.html -> web/dist-proof/index.html."""
import os
here = os.path.dirname(os.path.abspath(__file__))
page = open(os.path.join(here, "src/proof.html")).read()
page = page.replace("/*PROOF_JSON*/", open(os.path.join(here, "data/proof.json")).read().replace("</", "<\\/"))
os.makedirs(os.path.join(here, "dist-proof"), exist_ok=True)
open(os.path.join(here, "dist-proof/index.html"), "w").write(page)
with open(os.path.join(here, "dist-proof/preview.html"), "w") as f:
    f.write('<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"></head><body>' + page + "</body></html>")
print("dist-proof/index.html", len(page), "bytes")
