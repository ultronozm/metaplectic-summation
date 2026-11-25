#!/usr/bin/env python3
"""Build the portable HTML edition: one file that reads the sketches of the paper and shows its text.

    python3 portable/build.py            # writes output/html/metaplectic-sketches.html
    make html                            # the same

The file needs nothing but a browser: no server, no network, no installation.  It is generated from
schwartz-space-n-fold-cover-sl2.tex (the rigorous text), sketches.tex (the informal prose), and media.toml with the
figures of portable/figures (the pictures).  See portable/README.md.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

import audit  # noqa: E402
import edition  # noqa: E402
import media  # noqa: E402
from edition import PAPER, EditionError, esc, key  # noqa: E402

MAIN_TEX = ROOT / f"{PAPER}.tex"
SKETCHES_TEX = ROOT / "sketches.tex"
MEDIA_TOML = HERE / "media.toml"
AUDIT_TOML = HERE / "audit.toml"
REFS_BIB = ROOT / "refs.bib"
KATEX = HERE / "vendor" / "katex"
OUTPUT = ROOT / "output" / "html" / "metaplectic-sketches.html"
WORK = ROOT / "build" / "portable"
KEEP_SNAPSHOTS = 4


# ---------------------------------------------------------------- the sources, and LaTeX's numbers for them

def tex_inputs(main: Path, root: Path = ROOT) -> list[Path]:
    """The files that the paper reads with \\input or \\include, found relative to the repository as TeX would."""
    found, queue = [], [main]
    while queue:
        for name in re.findall(r"\\(?:input|include)\{([^}]+)\}", queue.pop().read_text()):
            path = root / (name if Path(name).suffix else name + ".tex")
            if path.is_file() and path not in found:
                found.append(path)
                queue.append(path)
    return found


def sources() -> list[Path]:
    return [MAIN_TEX, SKETCHES_TEX, REFS_BIB, *tex_inputs(MAIN_TEX)]


def snapshot(files: list[Path], root: Path, work: Path, keep: int = KEEP_SNAPSHOTS) -> Path:
    """Copy the sources once, into a directory named by their content.

    The text, LaTeX's numbers for it, and the checks of one build then all describe the same bytes, whatever is
    edited meanwhile, and a number is never taken from a build of some other version of the paper.  Old copies are
    pruned.
    """
    contents = {str(path.relative_to(root)): path.read_bytes() for path in files}
    digest = hashlib.sha256()
    for name in sorted(contents):
        digest.update(hashlib.sha256(name.encode()).digest() + hashlib.sha256(contents[name]).digest())
    work.mkdir(parents=True, exist_ok=True)
    directory = work / digest.hexdigest()[:16]
    for name, data in contents.items():
        target = directory / name
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_bytes() != data:
            target.write_bytes(data)
    directory.touch()
    others = sorted((d for d in work.iterdir() if d.is_dir() and d != directory), key=lambda d: d.stat().st_mtime, reverse=True)
    for old in others[max(keep - 1, 0):]:
        shutil.rmtree(old, ignore_errors=True)
    return directory


def numbering(source: Path) -> Path:
    """The auxiliary file with LaTeX's own numbers for a snapshot, made once for each distinct content."""
    done = source / ".numbered"
    if not done.exists():
        print("Numbering the paper with latexmk ...", flush=True)
        result = subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", f"{PAPER}.tex"],
                                cwd=source, capture_output=True, text=True)
        if result.returncode:
            raise EditionError(f"latexmk failed on {PAPER}.tex:\n" + result.stdout[-2000:])
        done.touch()
    return source / f"{PAPER}.aux"


# ---------------------------------------------------------------- assets

def katex_css() -> str:
    """KaTeX's stylesheet with its fonts inline, as woff2 only (every current browser reads it)."""
    css = (KATEX / "katex.min.css").read_text()

    def inline(match):
        name = match.group(1)
        data = base64.b64encode((KATEX / "fonts" / f"{name}.woff2").read_bytes()).decode()
        return f'url(data:font/woff2;base64,{data}) format("woff2")'
    # Each font-face lists woff2, woff, and ttf sources; keep the first.
    css = re.sub(r'url\(fonts/([A-Za-z0-9_-]+)\.woff2\) format\("woff2"\),url\(fonts/[^)]*\) format\("woff"\),url\(fonts/[^)]*\) format\("truetype"\)', inline, css)
    if "fonts/" in css:
        raise EditionError("Some KaTeX font was not inlined; the stylesheet has a form this build does not know")
    return css


def katex_version() -> str:
    match = re.search(r'version:"(\d+\.\d+\.\d+)"', (KATEX / "katex.min.js").read_text())
    return match.group(1) if match else "unknown"


def git(*args: str) -> str:
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    return result.stdout.strip() if result.returncode == 0 else ""


def provenance(source: Path) -> dict:
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()[:12]  # noqa: E731
    tracked = [f"{PAPER}.tex", "sketches.tex", "portable"]
    return {
        "commit": git("rev-parse", "--short", "HEAD") or "unknown",
        "date": git("log", "-1", "--format=%cs") or "unknown",
        "dirty": bool(git("status", "--porcelain", "--", *tracked)),
        "main": digest(source / f"{PAPER}.tex"), "sketches": digest(source / "sketches.tex"), "media": digest(MEDIA_TOML),
    }


def about_html(info: dict, title: str) -> str:
    licenses = [("KaTeX (MIT), version " + katex_version(), HERE / "licenses" / "KATEX-LICENSE.txt"),
                ("KaTeX fonts (SIL Open Font License 1.1)", HERE / "licenses" / "KATEX-FONTS-OFL.txt")]
    legend = "".join(f'<dt><span class="mtag {tag}">{tag}</span></dt><dd>{html.escape(text)}</dd>' for tag, text in media.TAG_HELP.items())
    legend += f'<dt><span class="mtag recheck">re-check</span></dt><dd>{html.escape(media.RECHECK)}</dd>'
    state = ("built outside a git checkout" if info["commit"] == "unknown"
             else "built from uncommitted changes" if info["dirty"] else "built from a clean checkout")
    texts = "".join(f"<details><summary>{html.escape(name)}</summary><pre>{html.escape(path.read_text())}</pre></details>" for name, path in licenses)
    return f"""<button id="about-close" type="button" class="close">Close</button>
<h2>About this edition</h2>
<p>The informal sketches of <i>{title}</i>, in the order of their targets in the paper, with the paper's own text one click away.  The prose of the sketches is <code>sketches.tex</code>; the paper is <code>{PAPER}.tex</code>.  Neither is copied by hand: this page is generated from them.</p>
<h3>Reading</h3>
<dl>
<dt>Paper</dt><dd>Opens the precise text of the unit beside the sketch, or over it in a narrow window.  A reference in a sketch or in the paper opens its target the same way.</dd>
<dt>Lean</dt><dd>Beside a statement that the paper marks as checked in Lean: opens its row in the appendix on Lean, which links to the declaration's source at the pinned commit.</dd>
<dt>Esc, &#10005;, or Back</dt><dd>Closes the paper and leaves the sketches where you were.  In the paper, Back returns to the previous place.</dd>
<dt>Sketch</dt><dd>Beside a unit of the paper that has a sketch: returns to that sketch.</dd>
<dt>No sketch</dt><dd>A heading marked so has no sketch; open its paper text with Paper.</dd>
</dl>
<h3>Pictures</h3>
<p>A picture under a sketch starts closed and opens in place.  Each carries a tag:</p>
<dl>{legend}</dl>
<h3>Provenance</h3>
<p>Repository commit {html.escape(info['commit'])} of {html.escape(info['date'])}: {state}.  Content hashes: {PAPER}.tex {info['main']}, sketches.tex {info['sketches']}, media.toml {info['media']}.</p>
<h3>Third-party software</h3>
<p>This file contains the following, with their licenses.</p>
{texts}"""


# ---------------------------------------------------------------- the build

def render_captions(paper, renderer, config: dict) -> dict[str, str]:
    """The titles and captions of the figures, rendered like the sketches, with references into the paper."""
    out = {}
    for figure in media.figures(config):
        where = f"media.toml:{figure['id']}"
        try:
            caption = paper.render(figure["caption"], source={"path": "media.toml", "line": 1})
            title = paper.render_title(figure["title"])
        except edition.PaperError as error:
            raise EditionError(f"{where}: {error}") from error
        out[figure["id"]] = edition.bind_punctuation(edition.retarget(caption, renderer.valid, where))
        out[figure["id"] + ":title"] = edition.retarget(title, renderer.valid, where)
    return out


def build(output: Path, source: Path, lock_path: Path = AUDIT_TOML) -> dict:
    started = time.time()
    aux = numbering(source)
    built = edition.build_edition(source / f"{PAPER}.tex", source / "sketches.tex", aux)
    paper, reading, renderer, sketches = built["paper"], built["reading"], built["renderer"], built["sketches"]

    config = media.load_config(MEDIA_TOML)
    media.check_placements(config, {sketch.label for sketch in sketches})
    media.check_inventory(config, HERE / "MEDIA.md")
    media.check_no_statement_numbers(HERE / "MEDIA.md", HERE / "README.md", MEDIA_TOML)
    unknown = sorted(label for f in media.figures(config) for label in media.figure_labels(f) if label not in paper.labels)
    if unknown:
        raise EditionError("media.toml: a figure depends on labels the paper does not have: " + ", ".join(unknown))
    captions = render_captions(paper, renderer, config)
    lock = audit.read_lock(lock_path)
    stale = audit.assess(paper, audit.dependencies(config), lock)
    notes = {item: audit.note_html(paper, changes) for item, changes in stale.items()}
    placed = media.media_html(config, captions, notes)

    numbers = {label: number for label, number in paper.numbers.items() if label in paper.labels}
    numbers.update({key(row["node"]): renderer.number(row["node"]) for row in reading["rows"] if row["row"] == "head"})
    section_of, current = {"document": "document"}, None
    for row in reading["rows"]:
        if row["row"] == "head" and row["level"] == 1:
            current = key(row["node"])
        elif row["row"] == "sketch" and row["sketch"].label != "document":
            section_of[row["sketch"].label] = current
    jump = ['<option value="document">Title and abstract</option>']
    for row in reading["rows"]:
        if row["row"] == "head" and row["level"] == 1:
            jump.append(f'<option value="{esc(key(row["node"]))}">&sect;{esc(renderer.number(row["node"]))} {html.escape(re.sub("<[^>]+>", "", renderer.title(row["node"])))}</option>')
    jump.append('<option value="references">References</option>')

    data = {"title": paper.title, "macros": paper.macros, "numbers": numbers, "sectionOf": section_of}

    headline = paper.render_title(paper.title)
    column, pane = renderer.reading_column(placed), renderer.paper_pane()
    edition.verify_fidelity(built, column, pane, {f["id"]: f["caption"] for f in media.figures(config)})
    page = (HERE / "src" / "template.html").read_text()
    parts = {
        "TITLE": html.escape(re.sub(r"<[^>]+>", "", headline)),
        "HEADLINE": headline,
        "CSS": katex_css() + "\n" + (HERE / "src" / "reader.css").read_text(),
        "CONTENTS": renderer.contents(),
        "COLUMN": column,
        "JUMP": "\n".join(jump),
        "PANE": pane,
        "ABOUT": about_html(provenance(source), headline),
        "DATA": json.dumps(data, ensure_ascii=False).replace("</", "<\\/"),
        "KATEX_JS": (KATEX / "katex.min.js").read_text(),
        "READER_JS": (HERE / "src" / "reader.js").read_text(),
    }
    for name, value in parts.items():
        if "</script" in value.lower() and name in ("KATEX_JS", "READER_JS"):
            value = re.sub(r"</(script)", r"<\\/\1", value, flags=re.I)
        page = page.replace("{{" + name + "}}", value)
    leftover = re.findall(r"\{\{[A-Z_]+\}\}", page)
    if leftover:
        raise EditionError("Unfilled template slots: " + ", ".join(leftover))
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(page, encoding="utf-8")
    return {
        "output": output, "bytes": output.stat().st_size, "seconds": time.time() - started,
        "sketches": len(sketches), "rows": len(reading["rows"]), "figures": len(media.figures(config)),
        "report": audit.report(stale, lock, len(media.figures(config))),
        "stale": bool(stale),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, default=OUTPUT, help="where to write the page (default: %(default)s)")
    parser.add_argument("--audit-lock", type=Path, default=AUDIT_TOML, help="the record of what each figure was compared with (default: %(default)s)")
    parser.add_argument("--require-audited", action="store_true",
                        help="fail if a figure cites or sits beside a statement that changed since it was last compared with the paper")
    args = parser.parse_args()
    source = snapshot(sources(), ROOT, WORK / "src")
    try:
        result = build(args.output.resolve(), source, args.audit_lock.resolve())
    except (EditionError, edition.PaperError) as error:
        print("Build failed: " + str(error).replace(str(source), str(ROOT)), file=sys.stderr)
        sys.exit(1)
    print(f"Wrote {result['output']}  ({result['bytes'] / 1e6:.1f} MB, {result['seconds']:.0f} s)")
    print(f"  {result['sketches']} sketches in {result['rows']} rows; {result['figures']} figures placed")
    if result["report"]:
        print("  " + "\n  ".join(result["report"]) + ("\n  (python3 portable/audit.py status, diff, accept)" if result["stale"] else ""))
    if args.require_audited and result["stale"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
