#!/usr/bin/env python3
"""Tiny no-cache static server for previewing the Spectra docs site.

Serves the repo's ``docs/`` directory and disables HTTP caching so edits to
CSS/JS are always picked up on reload. Usage:  python3 @Meta/devserver.py 8099
"""
import functools
import http.server
import socketserver
import sys
from pathlib import Path

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8099
ROOT = (Path(__file__).resolve().parent.parent / "docs")


class NoCacheHandler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
        self.send_header("Pragma", "no-cache")
        self.send_header("Expires", "0")
        super().end_headers()

    def log_message(self, *args):  # quiet
        pass


Handler = functools.partial(NoCacheHandler, directory=str(ROOT))
with socketserver.TCPServer(("", PORT), Handler) as httpd:
    httpd.allow_reuse_address = True
    print(f"serving {ROOT} at http://localhost:{PORT}  (no-cache)")
    httpd.serve_forever()
