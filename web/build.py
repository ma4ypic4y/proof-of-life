#!/usr/bin/env python3
"""Inline data and the JS engine into one self-contained page: web/dist/index.html."""
import os
here = os.path.dirname(os.path.abspath(__file__))
page = open(os.path.join(here, "src/page.html")).read()
page = page.replace("/*ATLAS_JSON*/", open(os.path.join(here, "data/atlas.json")).read().replace("</", "<\\/"))
gj = os.path.join(here, "data/copygeo.json")
if os.path.exists(gj):
    page = page.replace("/*COPYGEO_JSON*/", open(gj).read())
fj = os.path.join(here, "data/film52.json")
if os.path.exists(fj):
    page = page.replace("/*FILM_JSON*/", open(fj).read())
uj = os.path.join(here, "data/universal.json")
if os.path.exists(uj):
    page = page.replace("/*UNIVERSAL_JSON*/", open(uj).read())
eng = os.path.join(here, "bff-engine.js")
if os.path.exists(eng):
    src = open(eng).read()
    assert "</script" not in src
    page = page.replace("/*ENGINE_JS*/", src)
ps = os.path.join(here, "src/prompt-soup-section.html")
if os.path.exists(ps):
    sec = open(ps).read()
    pj = os.path.join(here, "data/psoup.json")
    if os.path.exists(pj):
        sec = sec.replace("/*PSOUP_JSON*/", open(pj).read().replace("</", "<\\/"))
    page = page.replace("<!--PROMPT_SOUP_SECTION-->", sec)
os.makedirs(os.path.join(here, "dist"), exist_ok=True)
open(os.path.join(here, "dist/index.html"), "w").write(page)
import shutil
shutil.copytree(os.path.join(here, "img"), os.path.join(here, "dist/img"), dirs_exist_ok=True)
print("dist/index.html", len(page), "bytes")
