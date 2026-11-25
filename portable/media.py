"""The pictures of the portable edition: static SVG figures, each under the sketch it illustrates.

A figure is a file in figures/, made by figures/make_figures.py, with its title, tag, and caption in media.toml.  The
caption is TeX, rendered with the paper's macros like the sketches, so a reference in it is a link into the paper and
a number in it is LaTeX's.  A figure is named by an id and placed by the label of its sketch.  The build fails if a
figure is not placed, not named in MEDIA.md, or its file is missing, and if MEDIA.md, README.md, or media.toml writes a
statement number by hand.
"""
from __future__ import annotations

import re
import tomllib
from pathlib import Path

from edition import EditionError, esc

HERE = Path(__file__).resolve().parent

TAG_HELP = {
    "exact": "drawn from the paper's definitions, in a case where they can be computed exactly",
    "schematic": "a drawing, with illustrative constants",
}

RECHECK = "the paper changed after this was last compared with it; its caption may be out of date"

STATEMENT_NUMBER = re.compile(
    r"\b(?:Theorem|Proposition|Lemma|Corollary|Definition|Example|Remark|Section|Appendix|Equation)s?\s*~?\(?\d+(?:\.\d+)*\b"
    r"|§\s*\d+(?:\.\d+)*|\\S\s*\d")

FIGURE_LABEL = re.compile(r"\\(?:eq)?ref\{([^}]+)\}")


def load_config(path: Path) -> dict:
    config = tomllib.loads(path.read_text())
    seen = set()
    for figure in config.get("figure", []):
        for key in ("id", "sketch", "file", "tag", "title", "caption"):
            if key not in figure:
                raise EditionError(f"{path.name}: figure {figure.get('id', '?')!r} has no {key}")
        if figure["id"] in seen:
            raise EditionError(f"{path.name}: figure {figure['id']!r} is listed twice")
        seen.add(figure["id"])
        if figure["tag"] not in TAG_HELP:
            raise EditionError(f"{path.name}: figure {figure['id']!r} has tag {figure['tag']!r}; the tags are {', '.join(TAG_HELP)}")
        if not (HERE / figure["file"]).is_file():
            raise EditionError(f"{path.name}: the file {figure['file']} of figure {figure['id']!r} is missing; run figures/make_figures.py")
    return config


def figures(config: dict) -> list[dict]:
    return config.get("figure", [])


def check_placements(config: dict, sketched: set[str]) -> None:
    for figure in figures(config):
        if figure["sketch"] not in sketched:
            raise EditionError(f"media.toml: figure {figure['id']!r} is placed under {figure['sketch']!r}, which has no sketch")


def check_inventory(config: dict, inventory: Path) -> None:
    text = inventory.read_text()
    missing = [f["id"] for f in figures(config) if f"`{f['id']}`" not in text]
    if missing:
        raise EditionError(f"{inventory.name} does not name the figures: " + ", ".join(missing))


def check_no_statement_numbers(*paths: Path) -> None:
    """The numbers of the paper change with the paper, so these documents name a unit by its label instead."""
    found = []
    for path in paths:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            match = STATEMENT_NUMBER.search(line)
            if match:
                found.append(f"{path.name}:{number}: {match.group(0)}")
    if found:
        raise EditionError("a statement number is written by hand (it would go stale; name the unit by its label):\n  "
                           + "\n  ".join(found[:12]))


def figure_labels(figure: dict) -> set[str]:
    """The labels a figure's caption cites, with those it declares in `depends`."""
    return set(FIGURE_LABEL.findall(figure["caption"])) | set(figure.get("depends", []))


def svg(figure: dict) -> str:
    """The SVG of a figure, inline, without its XML declaration, and with ids made unique to the figure."""
    text = (HERE / figure["file"]).read_text()
    text = re.sub(r"<\?xml[^>]*\?>\s*", "", text)
    text = re.sub(r"<!DOCTYPE[^>]*>\s*", "", text)
    if re.search(r"<script|\son[a-z]+=", text, re.I):
        raise EditionError(f"{figure['file']}: a figure must not contain scripts")
    prefix = "fig-" + figure["id"] + "-"
    text = re.sub(r'\bid="([^"]+)"', lambda m: f'id="{prefix}{m.group(1)}"', text)
    text = re.sub(r'url\(#([^)]+)\)', lambda m: f"url(#{prefix}{m.group(1)})", text)
    text = re.sub(r'href="#([^"]+)"', lambda m: f'href="#{prefix}{m.group(1)}"', text)
    return text


def media_html(config: dict, captions: dict[str, str], notes: dict[str, str] | None = None) -> dict:
    """Markup for the figures under each sketch.  Each starts closed, as a row with its tag, and opens in place."""
    notes = notes or {}
    placed: dict[str, list[str]] = {}
    for figure in figures(config):
        ident = figure["id"]
        recheck = f'<span class="mtag recheck" title="{esc(RECHECK)}">re-check</span>' if ident in notes else ""
        placed.setdefault(figure["sketch"], []).append(
            f'<details class="explore figure" id="f:{esc(ident)}" data-media="{esc(ident)}"><summary>'
            f'<span class="mtag {esc(figure["tag"])}" title="{esc(TAG_HELP[figure["tag"]])}">{esc(figure["tag"])}</span>{recheck}'
            f'<span class="what">{captions[ident + ":title"]}</span><span class="how">picture</span></summary>'
            + notes.get(ident, "")
            + f'<div class="explore-body"><div class="figure-art">{svg(figure)}</div>'
            f'<div class="figure-caption">{captions[ident]}</div></div></details>')
    return {label: '<div class="media">' + "".join(items) + "</div>" for label, items in placed.items()}
