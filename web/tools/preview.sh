#!/bin/zsh
# Wrap dist/index.html in the skeleton the Artifact host adds, for local preview/capture.
cd "$(dirname "$0")/.."
{ printf '<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover"><style>body{margin:0}</style></head><body>'; cat dist/index.html; printf '</body></html>'; } > dist/preview.html
