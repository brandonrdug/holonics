import os, sys, json, shutil, importlib
sys.path.insert(0, os.path.dirname(__file__))
from lib import *

OUT = os.path.join(os.path.dirname(__file__), 'out')
ARCHIVE_SRC = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'canvas-extract')

# registry: (file, title, w, h, page, builder)
BOARDS = []
def board(file, title, w, h, page):
    def deco(fn):
        BOARDS.append((file, title, w, h, page, fn)); return fn
    return deco

PAGES = [
    ("page-atlas", "Atlas"),
    ("page-ontology", "Ontology and types"),
    ("page-views", "Views"),
    ("page-library", "Component library"),
    ("page-machinery", "Machinery"),
    ("page-crates", "Crate branch"),
    ("page-archive", "Archive"),
]
NOTES = []  # (id, page, x, y, w, text)
def note_on(id, page, x, y, w, text): NOTES.append((id, page, x, y, w, text))

def build():
    for m in ["boards_atlas", "boards_views", "boards_views2", "boards_views3", "boards_types", "boards_library", "boards_machinery", "boards_crates"]:
        try: importlib.import_module(m)
        except ModuleNotFoundError as e:
            if m in str(e): print("skip", m); continue
            raise
    if os.path.isdir(OUT): shutil.rmtree(OUT)
    os.makedirs(OUT)
    art = []
    # lay out per page: 2 columns, gaps 100/160
    pos = {}
    for pid, _ in PAGES:
        x = y = 0; rowh = 0; colw = 0; n = 0
        for (file, title, w, h, page, fn) in BOARDS:
            if page != pid: continue
            if n % 2 == 1 and x + w > 3400:
                pass
            if n % 2 == 0 and n > 0:
                x = 0; y += rowh + 160; rowh = 0
            pos[file] = (x, y); x += w + 100; rowh = max(rowh, h); n += 1
    for (file, title, w, h, page, fn) in BOARDS:
        html = fn()
        with open(os.path.join(OUT, file), 'w') as f: f.write(html)
        x, y = pos[file]
        art.append({"file": file, "x": x, "y": y, "w": w, "h": h, "title": title, "page": page})
    # archive: previous artboards, untouched, on the archive page
    with open(os.path.join(ARCHIVE_SRC, 'canvas.json')) as f: old = json.load(f)
    ay = 0; ax = 0; rowh = 0; n = 0
    for a in old["artboards"]:
        shutil.copy(os.path.join(ARCHIVE_SRC, a["file"]), os.path.join(OUT, a["file"]))
        if n % 2 == 0 and n > 0: ax = 0; ay += rowh + 160; rowh = 0
        art.append({"file": a["file"], "x": ax, "y": ay, "w": a["w"], "h": a["h"],
                    "title": a["title"].replace(" (cached)", "") + " (archived)", "page": "page-archive",
                    "is_interactive": a.get("is_interactive", False)})
        ax += a["w"] + 100; rowh = max(rowh, a["h"]); n += 1
    canvas = {"artboards": art,
              "pages": [{"id": i, "name": nm} for i, nm in PAGES],
              "launch": {"view": "canvas", "page": "page-atlas"}}
    if NOTES:
        canvas["annotations"] = [{"id": i, "x": x, "y": y, "w": w, "text": t, "page": p} for (i, p, x, y, w, t) in NOTES]
    with open(os.path.join(OUT, 'canvas.json'), 'w') as f: json.dump(canvas, f, indent=1)
    print("boards:", len(art), "notes:", len(NOTES))
    return [a["file"] for a in art]

if __name__ == "__main__":
    build()
