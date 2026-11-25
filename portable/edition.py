"""The sketches-first reading of the paper: sources in, ordered HTML out.

The informal prose comes from sketches.tex and the rigorous text from
schwartz-space-n-fold-cover-sl2.tex.  Both are rendered by converter/paper.py, the
converter of the effective-nelson-venkatesh reader, so that neither is copied into
a second source.  Nothing here edits either file.

Order and coverage follow the documented semantics of the sketches package
(~/work/sketches): sketches are read in the order of their targets in the paper,
the sketch of the whole paper comes first, each section is listed, and a section's
subsections are listed when one of them contains a sketch.  A unit without a sketch
appears only as a heading.
"""
from __future__ import annotations

import html
import re
import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent / "converter"))
from paper import Paper, PaperError, _mask_comments  # noqa: E402


PAPER = "schwartz-space-n-fold-cover-sl2"


class EditionError(ValueError):
    """A problem with the sources, reported with a file and line where possible."""


@dataclass
class Sketch:
    label: str
    body: str
    line: int
    html: str = ""
    kind: str = ""
    position: int = 0
    media: list = field(default_factory=list)


# ---------------------------------------------------------------- sketches.tex

_BEGIN = re.compile(r"\\begin\s*\{(sketch\*?)\}\s*(?:\[([^\]]*)\])?")


def read_sketches(path: Path, paper: Paper) -> list[Sketch]:
    """Parse the sketch environments of a file of sketches kept beside the paper.

    Every sketch needs a target label, so that it can be placed without editing
    the paper.  A target that the paper lacks, a second sketch of one unit, or a
    construction that the package forbids is an error here, not a silent omission.
    """
    text = path.read_text()
    masked = _mask_comments(text)
    sketches: dict[str, Sketch] = {}
    for match in _BEGIN.finditer(masked):
        name, label = match.group(1), (match.group(2) or "").strip()
        line = masked.count("\n", 0, match.start()) + 1
        where = f"{path}:{line}"
        if name == "sketch*":
            raise EditionError(f"{where}: sketch* is printed as part of the paper and is not supported in a file of sketches")
        if not label:
            raise EditionError(f"{where}: a sketch in a file of its own needs a target label, as in \\begin{{sketch}}[label]")
        end = masked.find("\\end{sketch}", match.end())
        if end < 0:
            raise EditionError(f"{where}: unclosed sketch environment")
        body = masked[match.end():end]
        if re.search(r"\\label\s*\{", body):
            raise EditionError(f"{where}: a sketch must not define labels")
        if re.search(r"\\begin\s*\{(?:equation|align|gather|multline|eqnarray)\*?\}", body) and re.search(r"\\begin\s*\{(?:equation|align|gather|multline|eqnarray)\}", body):
            raise EditionError(f"{where}: numbered displays are not allowed in a sketch; use \\[ ... \\]")
        if label != "document" and label not in paper.labels:
            raise EditionError(f"{where}: sketch of {label!r}, but the paper has no such label")
        if label in sketches:
            raise EditionError(f"{where}: second sketch of {label!r}; each unit has at most one sketch")
        offset = masked.count("\n", 0, match.end())
        sketches[label] = Sketch(label, body, offset + 1)
    if not sketches:
        raise EditionError(f"{path}: no sketches found")
    return list(sketches.values())


def refuse_embedded_sketches(paper: Paper) -> None:
    """Sketches written inside the paper are a supported form of the package but not of this build."""
    for name, text in paper.files.items():
        if name.endswith(".tex") and re.search(r"\\begin\s*\{sketch\*?\}", _mask_comments(text)):
            raise EditionError(f"{name} contains sketches; this build reads only a file of sketches kept beside the paper")


# ---------------------------------------------------------------- the paper

def label_nodes(tree: dict) -> dict:
    """Map every label of the outline to its node, with the headings above it."""
    found = {}

    def visit(node, section, subsection):
        if node["kind"] == "section":
            section, subsection = node, None
        elif node["kind"] in ("subsection", "subsubsection"):
            subsection = node
        for label in ([node["label"]] if node.get("label") else []) + node.get("aliases", []):
            found.setdefault(label, (node, section, subsection))
        for child in node.get("children", []):
            visit(child, section, subsection)

    visit(tree, None, None)
    return found


def key(node: dict) -> str:
    """The identifier of a unit: its label, or the converter's stable identifier for an unlabeled heading."""
    return node.get("label") or node["id"]


def heading_numbers(paper: Paper, tree: dict) -> dict:
    """Section numbers by node, counted as LaTeX does, and checked against the auxiliary file.

    Unlabeled headings have no entry in the auxiliary file.  The counting is verified on
    every labeled heading, so a starred heading or an unusual sectioning command fails
    the build instead of misnumbering the reading.
    """
    numbers, counters = {}, [0, 0, 0]
    levels = {"section": 0, "subsection": 1, "subsubsection": 2}
    # After \appendix, sections are lettered A, B, ... and counted afresh.
    appendix = re.search(r"\\appendix\b", paper._masked)
    appendix_line = paper._masked.count("\n", 0, appendix.start()) + 1 if appendix else None
    lettered = [False]

    def visit(node):
        if node["kind"] in levels:
            if node["tex"].lstrip().startswith(tuple("\\" + name + "*" for name in levels)):
                raise EditionError(f"paper:{node['line']}: starred headings are not supported")
            depth = levels[node["kind"]]
            if depth == 0 and appendix_line and node["line"] > appendix_line and not lettered[0]:
                lettered[0], counters[0] = True, 0
            counters[depth] += 1
            for deeper in range(depth + 1, 3):
                counters[deeper] = 0
            parts = [str(c) for c in counters[:depth + 1]]
            if lettered[0]:
                parts[0] = chr(ord("A") + counters[0] - 1)
            number = ".".join(parts)
            numbers[node["id"]] = number
            recorded = paper.numbers.get(node.get("label"))
            if node.get("label") and recorded != number:
                raise EditionError(f"paper:{node['line']}: {node['label']} is numbered {recorded} by LaTeX but {number} by the reading; rebuild the paper")
        for child in node.get("children", []):
            visit(child)

    visit(tree)
    return numbers


def split_heading(number: str | None, title_html: str) -> str:
    """The title of a heading without its number, which the outline prepends."""
    if number and title_html.startswith(html.escape(number) + "  "):
        return title_html[len(html.escape(number)) + 2:]
    return title_html


def unit_title(paper: Paper, label: str, node: dict) -> tuple[str, str]:
    """(kind and number, optional title) of a sketched unit, as typeset HTML."""
    entry = paper.labels[label]
    if node["kind"] == "statement":
        number = paper.numbers.get(label)
        head = paper.theorems[entry["environment"]] + (" " + number if number else "")
        unit = paper._label_units[label]
        title = paper.render_title(unit.title) if unit.title else ""
        return html.escape(head), title
    if node["kind"] == "equation":
        return html.escape(entry["title"]), ""
    raise EditionError(f"Sketches of a {node['kind']} ({label}) are not supported")


# ---------------------------------------------------------------- the reading

def build_reading(paper: Paper, tree: dict, sketches: list[Sketch]) -> dict:
    """Place every sketch, in the order of its target, among the headings of the paper."""
    nodes = label_nodes(tree)
    by_label = {s.label: s for s in sketches}
    for sketch in sketches:
        if sketch.label == "document":
            sketch.kind, sketch.position = "document", -1
            continue
        node = nodes.get(sketch.label)
        if node is None:
            raise EditionError(f"The outline of the paper has no unit for the target {sketch.label!r}")
        sketch.kind = node[0]["kind"]
        sketch.position = paper._label_positions[sketch.label]
    ordered = sorted(sketches, key=lambda s: s.position)

    # A section's subsections are listed when one of them contains a sketch.
    expanded = set()
    for sketch in ordered:
        if sketch.label == "document":
            continue
        _, section, subsection = nodes[sketch.label]
        if section is not None and subsection is not None:
            expanded.add(section["id"])

    rows, covered = [], set()

    def walk(node, section=None):
        for child in node.get("children", []):
            kind = child["kind"]
            if kind == "section":
                rows.append({"row": "head", "level": 1, "node": child})
                emit_sketches(child)
                walk(child, child)
            elif kind in ("subsection", "subsubsection"):
                if section is not None and section["id"] in expanded or child.get("label") in by_label:
                    rows.append({"row": "head", "level": 2, "node": child})
                    emit_sketches(child)
                walk(child, section)
            else:
                emit_sketches(child)

    def emit_sketches(node):
        for label in ([node["label"]] if node.get("label") else []) + node.get("aliases", []):
            if label in by_label and label not in covered:
                covered.add(label)
                rows.append({"row": "sketch", "sketch": by_label[label], "node": node})

    if "document" in by_label:
        rows.append({"row": "sketch", "sketch": by_label["document"], "node": tree})
        covered.add("document")
    walk(tree)

    missing = [label for label in by_label if label not in covered]
    if missing:
        raise EditionError("Sketches that the reading could not place: " + ", ".join(missing))
    order = [row["sketch"].label for row in rows if row["row"] == "sketch"]
    expected = [s.label for s in ordered]
    if order != expected:
        raise EditionError("The reading order differs from the order of the targets in the paper:\n  " + "\n  ".join(a + " != " + b for a, b in zip(order, expected) if a != b))
    return {"rows": rows, "expanded": expanded, "nodes": nodes, "numbers": heading_numbers(paper, tree)}


# ---------------------------------------------------------------- HTML

def esc(value) -> str:
    return html.escape(str(value), quote=True)


def retarget(fragment: str, valid: set, where: str, prefix: str = "p:") -> str:
    """Point every reference at the paper's unit, and refuse a reference with no target."""
    def ref(match):
        label = match.group(2)
        if label not in valid:
            raise EditionError(f"{where}: reference to {label!r}, which has no target in the paper")
        text = match.group(3)
        if text == "?":
            raise EditionError(f"{where}: reference to {label!r} has no number; rebuild the paper")
        return f'<a class="ref" href="#{prefix}{esc(label)}" data-label="{esc(label)}">{text}</a>'
    return re.sub(r'<a class="ref" href="#([^"]*)" data-label="([^"]*)">(.*?)</a>', ref, fragment)


def bind_punctuation(fragment: str) -> str:
    """Keep a formula and the punctuation around it on one line.

    A browser may break between an inline formula and the comma that follows it, which leaves the comma at the
    start of the next line.  The converter writes inline formulas as span.m, with TeX that holds no markup.
    """
    pattern = re.compile(r'([(\[]?)(<span class="m">[^<]*</span>)([,.;:!?)\]]*)')
    return pattern.sub(lambda m: f'<span class="nb">{m.group(0)}</span>' if m.group(1) or m.group(3) else m.group(0), fragment)


def anchors_to_ids(fragment: str) -> str:
    """Labels written by the converter as data-anchor attributes become element ids."""
    fragment = re.sub(r'<span class="paper-anchor" data-anchor="([^"]*)"></span>',
                      lambda m: f'<span class="paper-anchor" id="p:{m.group(1)}"></span>', fragment)

    def display(match):
        labels = match.group(1).split()
        extra = "".join(f'<span class="paper-anchor" id="p:{label}"></span>' for label in labels[1:])
        return f'<div class="display" id="p:{labels[0]}" data-anchors="{match.group(1)}">{extra}'
    return re.sub(r'<div class="display" data-anchors="([^"]*)">', display, fragment)


def proof_details(proof_html: str, title: str) -> str:
    """A proof, open by default, that the reader can fold."""
    match = re.match(r'\s*<section class="paper-proof"><h4>(.*?)</h4>(.*)</section>\s*$', proof_html, re.S)
    if not match:
        raise EditionError("Unexpected markup for a proof")
    name = re.sub(r"\.\s*$", "", match.group(1))
    return f'<details class="p-proof" open><summary>{name}</summary><div class="p-proof-body">{match.group(2)}</div></details>'


class Renderer:
    def __init__(self, paper: Paper, tree: dict, reading: dict, bibliography: set):
        self.paper, self.tree, self.reading = paper, tree, reading
        self.numbers = reading["numbers"]
        self.sketched = {row["sketch"].label for row in reading["rows"] if row["row"] == "sketch"}
        self.valid = set(paper.labels) | {"document"} | {key(row["node"]) for row in reading["rows"] if row["row"] == "head"}
        self.bibliography = bibliography

    def number(self, node) -> str:
        return self.numbers.get(node["id"], "")

    def title(self, node) -> str:
        return split_heading(self.number(node), node.get("titleHtml") or esc(node["title"]))

    # -- Lean

    def lean_decls(self, label) -> list[str]:
        """The Lean declarations that the paper marks with \\lean{...} in a statement, without its proof."""
        unit = self.paper._label_units.get(label)
        if unit is None or unit.kind != "statement":
            return []
        return [d.strip() for d in re.findall(r"\\lean\s*\{([^}]*)\}", self.paper._masked[unit.start:unit.end])]

    def lean_tab(self, label) -> str:
        """A small link to the statement's row in the appendix on Lean, which links to the source."""
        decls = self.lean_decls(label)
        if not decls:
            return ""
        return (f'<a class="to-lean" href="#p:lean:{esc(decls[0])}" data-decls="{esc(" ".join(decls))}" '
                f'title="Checked in Lean: {esc(", ".join(decls))}">Lean</a>')

    # -- the paper pane

    def sketch_tab(self, label) -> str:
        if label not in self.sketched:
            return ""
        return f'<a class="to-sketch" href="#s:{esc(label)}" title="Back to the sketch">Sketch</a>'

    def paper_node(self, node) -> str:
        kind, label = node["kind"], node.get("label")
        data = f' data-sketch="{esc(label)}"' if label in self.sketched else ""
        if kind in ("section", "subsection", "subsubsection"):
            tag = {"section": "h2", "subsection": "h3"}.get(kind, "h4")
            inner = "".join(self.paper_node(child) for child in node.get("children", []))
            return (f'<section class="p-sec p-{kind}" id="p:{esc(key(node))}"{data}><{tag} class="p-head">'
                    f'<span class="num">{esc(self.number(node))}</span><span class="p-title">{self.title(node)}</span>'
                    f'{self.sketch_tab(label)}</{tag}>{inner}</section>')
        if node.get("error"):
            raise EditionError(f"paper:{node.get('line')}: {node['error']}")
        if kind == "statement":
            # The wrapper carries the statement's own label, so that the converter's anchor for it is dropped.
            body = node["statementHtml"].replace(f'<span class="paper-anchor" data-anchor="{label}"></span>', "", 1) if label else node["statementHtml"]
            if node.get("proofHtml"):
                body += proof_details(node["proofHtml"], node.get("proofTitle") or "Proof")
            if label and label in self.sketched:
                body = body.replace("</h4>", self.sketch_tab(label) + "</h4>", 1)
            ident = f' id="p:{esc(label)}"' if label else ""
            env = f' data-env="{esc(self.paper.labels[label]["environment"])}"' if label else ""
            return f'<div class="p-stmt"{ident}{data}{env}>{body}</div>'
        if kind == "bibliography":
            return self.bibliography_html(node)
        return node.get("html", "")

    def bibliography_html(self, node) -> str:
        body = re.sub(r'<li class="bibliography-entry"><span class="bibliography-label">\[([^\]]*)\]</span>',
                      lambda m: f'<li class="bibliography-entry" id="p:bib:{m.group(1)}"><span class="bibliography-label">[{m.group(1)}]</span>',
                      node["html"])
        return f'<section class="p-sec p-refs" id="p:references"><h2 class="p-head"><span class="p-title">References</span></h2>{body}</section>'

    def link_citations(self, fragment: str) -> str:
        def cite(match):
            label = match.group(2)
            if label not in self.bibliography:
                return match.group(0)
            return f'<a class="cite" href="#p:bib:{label}" data-key="{match.group(1)}">{label}</a>'
        return re.sub(r'<span class="cite" data-key="([^"]*)">([^<]*)</span>', cite, fragment)

    def paper_pane(self) -> str:
        front, rest = [], []
        for child in self.tree["children"]:
            (rest if rest or child["kind"] in ("section", "bibliography") else front).append(child)
        title = self.paper.render_title(self.paper.title)
        date = date_of(self.paper)
        head = f'<h1 class="p-doc-title">{title}</h1>' + (f'<p class="p-date">{esc(date)}</p>' if date else "")
        data = ' data-sketch="document"' if "document" in self.sketched else ""
        body = (f'<div class="p-front" id="p:document"{data}>{head}{self.sketch_tab("document")}'
                + "".join(self.paper_node(n) for n in front) + "</div>"
                + "".join(self.paper_node(n) for n in rest))
        body = retarget(anchors_to_ids(body), self.valid | {"references"}, "paper")
        body = bind_punctuation(self.link_citations(body))
        ids = re.findall(r' id="([^"]*)"', body)
        repeated = sorted({i for i in ids if ids.count(i) > 1})
        if repeated:
            raise EditionError("Repeated ids in the paper: " + ", ".join(repeated))
        return body

    # -- the reading column

    def heading_row(self, row) -> str:
        node, level = row["node"], row["level"]
        ident = key(node)
        has = node.get("label") in self.sketched
        tag = "h2" if level == 1 else "h3"
        mark = "" if has else '<span class="no-sketch">no sketch</span>'
        return (f'<{tag} class="r-head r-level{level}{"" if has else " bare"}" id="h:{esc(ident)}" data-label="{esc(ident)}">'
                f'<span class="num">{esc(self.number(node))}</span><span class="ttl">{self.title(node)}</span>{mark}'
                f'<a class="to-paper" href="#p:{esc(ident)}" title="Open the paper at this {"section" if level == 1 else "subsection"}">Paper</a></{tag}>')

    def sketch_row(self, row, media_html: dict) -> str:
        sketch, node = row["sketch"], row["node"]
        label, kind, head = sketch.label, sketch.kind, ""
        if kind == "document":
            head = ('<header class="unit-head"><span class="unit-kind">The paper</span>'
                    '<a class="to-paper" href="#p:document" title="Open the title and abstract">Paper</a></header>')
        elif kind in ("statement", "equation"):
            what, name = unit_title(self.paper, label, node)
            head = (f'<header class="unit-head"><span class="unit-kind">{what}</span>'
                    + (f'<span class="unit-title">{name}</span>' if name else "")
                    + self.lean_tab(label)
                    + f'<a class="to-paper" href="#p:{esc(label)}" title="Open the paper at {what}">Paper</a></header>')
        body = bind_punctuation(retarget(sketch.html, self.valid, f"sketches.tex:{sketch.line}"))
        return (f'<article class="sketch kind-{kind}" id="s:{esc(label)}" data-label="{esc(label)}">{head}'
                f'<div class="sketch-body">{body}</div>{media_html.get(label, "")}</article>')

    def reading_column(self, media_html: dict) -> str:
        return "".join(self.heading_row(row) if row["row"] == "head" else self.sketch_row(row, media_html)
                       for row in self.reading["rows"])

    def contents(self) -> str:
        """The contents; a unit without a sketch of its own is marked."""
        items = []
        for row in self.reading["rows"]:
            if row["row"] != "head":
                continue
            node, ident = row["node"], key(row["node"])
            dot = "" if node.get("label") in self.sketched else ' <span class="toc-bare" title="No sketch of this unit"></span>'
            items.append(f'<li class="{"toc-sub" if row["level"] == 2 else "toc-sec"}"><a href="#h:{esc(ident)}" data-target="{esc(ident)}">'
                         f'<span class="num">{esc(self.number(node))}</span> {self.title(node)}{dot}</a></li>')
        return '<ol class="toc">' + "".join(items) + "</ol>"


def date_of(paper: Paper) -> str:
    match = re.search(r"\\date\s*\{([^}]*)\}", paper._masked)
    return match.group(1).strip() if match else ""


# ---------------------------------------------------------------- the whole edition

# Explicit expansions for what KaTeX and the converter lack: \qedhere only places the PDF's end-of-proof mark, and
# the bibliography style defines \cprime in the .bbl.
MACROS = {"qedhere": "", "cprime": "$'$"}


def build_edition(main_tex: Path, sketches_tex: Path, aux: Path, validate_math: bool = True) -> dict:
    paper = Paper(main_tex, aux=aux, macros=MACROS, validate_math=validate_math)
    if paper.diagnostics:
        raise EditionError("The paper could not be indexed cleanly:\n  " + "\n  ".join(paper.diagnostics))
    refuse_embedded_sketches(paper)
    sketches = read_sketches(sketches_tex, paper)
    for sketch in sketches:
        try:
            sketch.html = paper.render(sketch.body, source={"path": str(sketches_tex), "line": sketch.line})
        except PaperError as error:
            raise EditionError(str(error)) from error
        if "paper-anchor" in sketch.html or "data-anchors" in sketch.html:
            raise EditionError(f"{sketches_tex}:{sketch.line}: a sketch must not define labels")
    tree = paper.outline()
    reading = build_reading(paper, tree, sketches)
    bibliography = {entry["label"].strip("{}") for entry in paper._bibliography_entries}
    renderer = Renderer(paper, tree, reading, bibliography)
    return {"paper": paper, "tree": tree, "sketches": sketches, "reading": reading, "renderer": renderer}


# ---------------------------------------------------------------- nothing dropped

def _source_words(tex: str) -> Counter:
    """The words of a TeX source outside formulas and commands (a reference prints a number, not its label)."""
    tex = re.sub(r"\$\$.*?\$\$", " ", tex, flags=re.S)
    tex = re.sub(r"(?<!\\)\$.*?(?<!\\)\$", " ", tex, flags=re.S)
    tex = re.sub(r"\\\[.*?\\\]|\\\(.*?\\\)", " ", tex, flags=re.S)
    tex = re.sub(r"\\begin\{(equation|align|gather|multline|eqnarray|displaymath|split)\*?\}.*?\\end\{\1\*?\}", " ", tex, flags=re.S)
    tex = re.sub(r"\\(?:eq)?ref\{[^}]*\}|\\label\{[^}]*\}|\\cite(?:\[[^\]]*\])?\{[^}]*\}|\\bibliography(?:style)?\{[^}]*\}", " ", tex)
    # A Lean link prints "Lean", and a row of the appendix its declaration; the file and line are in the link.
    tex = re.sub(r"\\lean\{[^}]*\}", " Lean ", tex)
    tex = re.sub(r"\\leanentry\{([^}]*)\}\{[^}]*\}\{[^}]*\}", r" \1 ", tex)
    tex = re.sub(r"\\setcounter\{[^}]*\}\{[^}]*\}|\\begin\{tabular\}\{(?:[^{}]|\{[^{}]*\})*\}", " ", tex)
    tex = re.sub(r"\\(?:begin|end)\{[^}]*\}|\\[A-Za-z]+\*?", " ", tex)
    return Counter(word.lower() for word in re.findall(r"[A-Za-z]{4,}", tex))


def _html_words(fragment: str) -> Counter:
    fragment = re.sub(r'<span class="m[^"]*">.*?</span>', " ", fragment, flags=re.S)
    fragment = re.sub(r"<[^>]+>", " ", fragment)
    return Counter(word.lower() for word in re.findall(r"[A-Za-z]{4,}", html.unescape(fragment)))


def _source_math(tex: str) -> int:
    count = len(re.findall(r"\\begin\{(?:equation|align|gather|multline|eqnarray|displaymath)\*?\}", tex))
    count += len(re.findall(r"\\\[", tex)) + len(re.findall(r"\\\(", tex))
    # Inline formulas inside a display, as in \text{if $c \neq 0$}, belong to the display.
    tex = re.sub(r"\\begin\{(equation|align|gather|multline|eqnarray|displaymath)(\*?)\}.*?\\end\{\1\2\}", " ", tex, flags=re.S)
    tex = re.sub(r"\\\[.*?\\\]", " ", tex, flags=re.S)
    plain = tex.replace("\\$", "")
    return count + len(re.findall(r"(?<!\$)\$(?!\$)", plain)) // 2 + len(re.findall(r"\$\$", plain)) // 2


def verify_fidelity(built: dict, column: str, pane: str, captions: dict[str, str] | None = None) -> None:
    """Fail unless every word and every formula of the sources is in the generated page.

    The converter is strict about what it cannot read; this catches what could still be lost between it and the
    page: a sketch card missing a paragraph or a formula, or a passage of the paper missing from the pane.
    """
    problems = []
    for sketch in built["sketches"]:
        card = re.search(r'<article class="sketch [^"]*" id="s:%s".*?</article>' % re.escape(sketch.label), column, re.S)
        if not card:
            problems.append(f"{sketch.label}: no card")
            continue
        lost = _source_words(sketch.body) - _html_words(card.group(0))
        if lost:
            problems.append(f"sketch {sketch.label}: words missing from the page: {', '.join(sorted(lost)[:6])}")
        text = re.sub(r'<div class="media">.*', "", card.group(0), flags=re.S)
        written, shown = _source_math(sketch.body), len(re.findall(r'<span class="m[ "]', text))
        if written != shown:
            problems.append(f"sketch {sketch.label}: {written} formulas in sketches.tex, {shown} in the page")
    for ident, caption in (captions or {}).items():
        box = re.search(r'<details class="explore figure" id="f:%s".*?</details>' % re.escape(ident), column, re.S)
        if not box:
            problems.append(f"figure {ident}: not in the page")
            continue
        lost = _source_words(caption) - _html_words(box.group(0))
        if lost:
            problems.append(f"figure {ident}: caption words missing from the page: {', '.join(sorted(lost)[:6])}")
    paper = built["paper"]
    body = paper._masked[paper._body_start:paper._body_end]
    lost = _source_words(body) - _html_words(pane)
    if lost:
        problems.append("paper: words missing from the page: " + ", ".join(sorted(lost)[:8]))
    # The bibliography comes from the .bbl, not from the paper, so its formulas are not counted.
    text = pane.split('<section class="p-sec p-refs"')[0]
    written, shown = _source_math(body), len(re.findall(r'<span class="m[ "]', text))
    if written != shown:
        problems.append(f"paper: {written} formulas in the source, {shown} in the page")
    if problems:
        raise EditionError("The page does not contain all of its sources:\n  " + "\n  ".join(problems))
