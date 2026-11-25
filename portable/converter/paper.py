"""A source-preserving adapter for a documented, common subset of LaTeX.

This is not a TeX interpreter.  Literal local inputs, labeled headings, theorem
environments, adjacent proofs, displays, simple macros, and ordinary mathematical
prose are supported.  Unsupported *selected* content raises PaperError; unrelated
packages and unselected prose do not prevent indexing.  Exact source is always
available with get(..., render=False), including when HTML conversion fails.

Copied from ~/work/effective-nelson-venkatesh/interactive/authoring/paper.py, with
these additions for the metaplectic-summation paper: multline displays, simple
tabular environments, the Lean links \\lean{Decl} and \\leanentry{Decl}{file}{line}
of its preamble, \\url of a macro, and the layout commands \\sloppy and \\small.
"""

from __future__ import annotations

import hashlib
import html
import importlib.util
import json
import re
import shutil
import subprocess
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Callable
from urllib.parse import quote

_HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("_authoring_existing_converter", _HERE / "build_paper.py")
_converter = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_converter)
_KATEX = _HERE.parent / "vendor/katex/katex.min.js"
_COMMAND = re.compile(r"\\([A-Za-z@]+|[^\n])")
_HEADINGS = {"part": 0, "chapter": 1, "section": 2, "subsection": 3, "subsubsection": 4, "paragraph": 5, "subparagraph": 6}
_DISPLAYS = {"equation", "equation*", "align", "align*", "gather", "gather*", "multline", "multline*", "displaymath"}
_STANDARD_THEOREMS = {name: name.capitalize() for name in ("theorem", "proposition", "lemma", "corollary", "hypothesis", "definition", "remark", "example", "claim", "conjecture")}


class PaperError(ValueError):
    """A diagnostic with a usable source location, never a silent substitution."""

    def __init__(self, message, source=None, line=None, column=None):
        self.message, self.source, self.line, self.column = message, str(source) if source else None, line, column
        location = self.source or "LaTeX"
        if line is not None:
            location += f":{line}"
        if column is not None:
            location += f":{column}"
        super().__init__(f"{location}: {message}")


def _mask_comments(text):
    chars = list(text)
    for match in re.finditer("%", text):
        i = match.start() - 1
        while i >= 0 and text[i] == "\\":
            i -= 1
        if (match.start() - i - 1) % 2:
            continue
        end = text.find("\n", match.start())
        end = len(text) if end < 0 else end
        chars[match.start():end] = " " * (end - match.start())
    return "".join(chars)


def _space(text, i):
    while i < len(text) and text[i].isspace():
        i += 1
    return i


def _group(text, i, opening="{", closing="}"):
    i = _space(text, i)
    if i >= len(text) or text[i] != opening:
        raise ValueError(f"Expected {opening}")
    start, depth = i + 1, 1
    i += 1
    while i < len(text):
        if text[i] == "\\":
            command = _COMMAND.match(text, i)
            i = command.end() if command else i + 1
            continue
        if text[i] == opening:
            depth += 1
        elif text[i] == closing:
            depth -= 1
            if not depth:
                return text[start:i], i + 1
        i += 1
    raise ValueError(f"Unclosed {opening}{closing} group")


def _optional(text, i):
    i = _space(text, i)
    return _group(text, i, "[", "]") if i < len(text) and text[i] == "[" else (None, i)



# Text accents and special letters that occur in bibliography entries.
_ACCENTS = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302", "~": "\u0303", "=": "\u0304", ".": "\u0307"}
_SPECIAL_LETTERS = {"l": "ł", "L": "Ł", "o": "ø", "O": "Ø", "ss": "ß", "aa": "å", "AA": "Å", "ae": "æ", "AE": "Æ", "oe": "œ", "OE": "Œ", "i": "ı", "j": "ȷ"}

@dataclass
class _Span:
    start: int
    end: int
    path: Path
    source_start: int
    source_end: int


@dataclass
class _Unit:
    kind: str
    start: int
    end: int
    body_start: int
    body_end: int
    title: str = ""
    env: str = ""
    level: int = 99
    proof: _Unit | None = None


@dataclass
class _Macro:
    body: str
    nargs: int = 0
    unsupported: str | None = None


class _Converter(_converter.Converter):
    def __init__(self, owner):
        super().__init__(owner.numbers, owner.bibliography)
        self.owner = owner

    def ref(self, key, eq=False):
        if key not in self.owner.labels and key not in self.labels:
            raise ValueError(f"Unknown reference {key!r}; add the source file or correct the label")
        value = self.labels.get(key) or key
        value = f"({value})" if eq else value
        if key not in self.owner.labels:
            return f'<span class="ref external-ref" data-label="{html.escape(key)}" title="Number supplied by the auxiliary file; source not indexed">{html.escape(value)}</span>'
        return f'<a class="ref" href="{html.escape(self.owner.reference_base + quote(key, safe=":"))}" data-label="{html.escape(key)}">{html.escape(value)}</a>'

    def cite(self, opt, keys):
        result = []
        for key in keys.split(","):
            key = key.strip()
            value = self.bib.get(key, {}).get("label", key)
            # This adapter indexes manuscript labels, not complete bibliography
            # records.  Preserve the citation without inventing a dead target.
            value = value.replace("{", "").replace("}", "")
            result.append(f'<span class="cite" data-key="{html.escape(key)}">{html.escape(value)}</span>')
        return "[" + ", ".join(result) + (", " + self.text(opt) if opt else "") + "]"


class Paper:
    """Index an existing manuscript without changing it.

    ``get(label, part='auto', render=True)`` returns an excerpt dictionary.
    ``part`` may be auto, statement, proof, both, or section.  Auto/both include
    an adjacent proof for a statement; both also works for an equation/section.
    A list of labels selects multiple exact excerpts in the requested order.
    ``macros`` provides explicit expansions for otherwise unsupported commands.
    """

    def __init__(self, path, aux=None, macros=None, reference_base="#", validate_math=True):
        self.path = Path(path).expanduser().resolve()
        self.reference_base = reference_base
        self.validate_math = validate_math
        self.files: dict[str, str] = {}
        self.watch_files: set[str] = set()
        self.diagnostics = []
        self._macro_defs: dict[str, _Macro] = {}
        self.macros = {}
        self.theorems = dict(_STANDARD_THEOREMS)
        self._validated_math = set()
        self._text, self._spans = self._expand(self.path, [])
        self._masked = _mask_comments(self._text)
        self._discover_declarations()
        for name, value in (macros or {}).items():
            name = name if name.startswith("\\") else "\\" + name
            if not isinstance(value, str):
                raise PaperError(f"Configured macro {name} must be a TeX expansion string")
            nargs = max([int(n) for n in re.findall(r"#([1-9])", value)] or [0])
            self.macros[name] = value
            self._macro_defs[name] = _Macro(value, nargs)
        self.macro_fingerprint = hashlib.sha256(json.dumps(self.macros, sort_keys=True).encode()).hexdigest()
        self.numbers, self.aux = self._read_aux(aux)
        self.bibliography = self._read_bibliography()
        self.title = self.path.stem
        title = re.search(r"\\title(?:\s*\[[^]]*\])?\s*\{", self._masked)
        if title:
            try:
                self.title = _group(self._masked, title.end() - 1)[0]
            except ValueError:
                pass
        self._index()
        self._conv = _Converter(self)

    def _expand(self, path, stack):
        path = path.resolve()
        self.watch_files.add(str(path))
        if path in stack:
            raise PaperError("Cyclic local input: " + " → ".join(p.name for p in stack + [path]), path)
        try:
            source = path.read_text()
        except OSError as error:
            raise PaperError(str(error), path) from error
        self.files[str(path)] = source
        clean = _mask_comments(source)
        chunks, spans, cursor, size = [], [], 0, 0

        def literal(start, end):
            nonlocal size
            if end > start:
                chunks.append(source[start:end])
                spans.append(_Span(size, size + end - start, path, start, end))
                size += end - start

        # Only literal local filenames are expanded.  Dynamic input commands are
        # retained, and cause a diagnostic if the containing passage is selected.
        for match in re.finditer(r"\\(?:input|include)\b\s*(?:\{([^{}\\]+)\}|([A-Za-z0-9_./~-]+))", clean):
            filename = (match.group(1) or match.group(2)).strip()
            relative = Path(filename)
            if not relative.suffix:
                relative = relative.with_suffix(".tex")
            # TeX is normally run from the main document directory.  Also accept
            # a literal file next to its includer, a common split-document layout.
            candidates = [self.path.parent / relative, path.parent / relative]
            target = next((candidate for candidate in candidates if candidate.exists()), candidates[0])
            try:
                included, child_spans = self._expand(target, stack + [path])
            except PaperError as error:
                self.diagnostics.append(str(error))
                continue
            literal(cursor, match.start())
            chunks.append(included)
            spans.extend(_Span(s.start + size, s.end + size, s.path, s.source_start, s.source_end) for s in child_spans)
            size += len(included)
            cursor = match.end()
        literal(cursor, len(source))
        return "".join(chunks), spans

    def _where(self, offset):
        for span in self._spans:
            if span.start <= offset < span.end:
                position = span.source_start + offset - span.start
                text = self.files[str(span.path)]
                return str(span.path), text.count("\n", 0, position) + 1, position - text.rfind("\n", 0, position)
        return str(self.path), 1, 1

    def _discover_declarations(self):
        clean = self._masked
        pattern = re.compile(r"\\(newcommand|renewcommand|providecommand|DeclareMathOperator|newtheorem|def)\*?")
        for match in pattern.finditer(clean):
            kind, i = match.group(1), match.end()
            try:
                i = _space(clean, i)
                if kind == "newtheorem":
                    name, i = _group(clean, i)
                    _, i = _optional(clean, i)
                    title, i = _group(clean, i)
                    self.theorems[name] = title
                    continue
                if clean[i] == "{":
                    name, i = _group(clean, i)
                else:
                    command = _COMMAND.match(clean, i)
                    if not command:
                        continue
                    name, i = command.group(0), command.end()
                if not re.fullmatch(r"\\[A-Za-z@]+", name):
                    continue
                unsupported, nargs = None, 0
                if kind == "def":
                    end = clean.find("{", i)
                    parameters = clean[i:end].strip()
                    if parameters and not re.fullmatch(r"(?:#[1-9])+", parameters):
                        unsupported = "delimited parameters"
                    nargs = len(re.findall(r"#[1-9]", parameters))
                    i = end
                elif kind != "DeclareMathOperator":
                    count, i = _optional(clean, i)
                    nargs = int(count) if count is not None else 0
                    default, i = _optional(clean, i)
                    if default is not None:
                        unsupported = "optional/default parameters"
                body, i = _group(clean, i)
                if kind == "DeclareMathOperator":
                    body = r"\operatorname" + ("*" if match.group(0).endswith("*") else "") + "{" + body + "}"
                if kind == "providecommand" and name in self._macro_defs:
                    continue
                self._macro_defs[name] = _Macro(body, nargs, unsupported)
                if not unsupported:
                    self.macros[name] = body
            except (ValueError, IndexError):
                # Package implementation code is not this adapter's language.
                # A use of an unrecognized definition is diagnosed on selection.
                continue

    def lean_url(self, path, line):
        """The URL of a line of the Lean sources at the commit pinned by \\leancommit, as \\leanurl gives it."""
        repo, commit = self.macros.get("\\leanrepo"), self.macros.get("\\leancommit")
        if not repo or not commit:
            raise PaperError("\\leanentry needs \\leanrepo and \\leancommit in the preamble")
        return f"{repo}/blob/{commit}/lean/{path}#L{line}"

    def _read_aux(self, aux):
        candidates = [Path(aux).expanduser()] if aux else [self.path.with_suffix(".aux"), self.path.parent / "build" / (self.path.stem + ".aux")]
        path = next((p.resolve() for p in candidates if p.exists()), None)
        if aux and path is None:
            raise PaperError("Requested auxiliary file does not exist", aux)
        numbers, seen = {}, set()

        def read(file):
            if file in seen or not file.exists():
                return
            seen.add(file)
            text = _mask_comments(file.read_text())
            for match in re.finditer(r"\\newlabel\s*\{", text):
                try:
                    key, i = _group(text, match.end() - 1)
                    value, i = _group(text, i)
                    number, _ = _group(value, 0)
                    numbers[key] = number
                except ValueError:
                    continue
            for included in re.findall(r"\\@input\{([^}]+)\}", text):
                read(file.parent / included)

        if path:
            read(path)
        return numbers, path

    def _read_bibliography(self):
        path = self.aux.with_suffix(".bbl") if self.aux else self.path.with_suffix(".bbl")
        self._bibliography_path = path.resolve()
        self.watch_files.add(str(self._bibliography_path))
        self._bibliography_entries = []
        self._bibliography_error = None
        result = {}
        if path.exists():
            source = path.read_text()
            self.files[str(self._bibliography_path)] = source
            clean = _mask_comments(source)
            items = list(re.finditer(r"\\bibitem\b", clean))
            ending = re.search(r"\\end\s*\{thebibliography\}", clean)
            for index, match in enumerate(items):
                try:
                    label, cursor = _optional(clean, match.end())
                    key, cursor = _group(clean, cursor)
                    last = items[index + 1].start() if index + 1 < len(items) else ending.start() if ending else len(source)
                    entry = {"key": key, "label": label or key, "body": source[cursor:last], "bodyStart": cursor,
                             "start": match.start(), "end": last, "tex": source[match.start():last]}
                    self._bibliography_entries.append(entry)
                    result[key] = {"label": entry["label"]}
                except ValueError as error:
                    self._bibliography_error = str(PaperError("Malformed ordinary bibliography entry: " + str(error), path, source.count("\n", 0, match.start()) + 1))
            if not items and not re.search(r"\\begin\s*\{thebibliography\}", clean):
                self._bibliography_error = str(PaperError("This compiled bibliography does not use ordinary \\bibitem entries; inspect the original source or use a fuller bibliography adapter", path))
        return result

    def _bibliography_outline(self, trigger):
        """Render ordinary BibTeX output without changing the paper's macros."""
        node = {**trigger, "kind": "bibliography", "title": "References", "titleHtml": "References", "id": "paper-references"}
        # The reader displays the node title, as for other non-statement units.
        heading = '<section class="paper-bibliography">'
        path = self._bibliography_path
        if str(path) not in self.files:
            message = f"Compiled bibliography not found at {path}.  Compile the paper's bibliography to show its references; the original bibliography command is retained below."
            node["error"] = str(PaperError(message, trigger["source"], trigger["line"]))
            node["html"] = heading + '<p class="source-fallback">' + html.escape(message) + '</p></section>'
            return node
        source = self.files[str(path)]
        end_line = source.count("\n", 0, max(0, len(source) - 1)) + 1
        span = {"source": str(path), "start": 0, "end": len(source), "line": 1, "endLine": end_line, "tex": source}
        node.update(source=str(path), line=1, endLine=end_line, tex=source, sources=[span],
                    bibliographyCommand={key: trigger[key] for key in ("tex", "source", "line", "endLine", "sources")},
                    fingerprint=hashlib.sha256(json.dumps({"tex": source, "macros": self.macros}, sort_keys=True).encode()).hexdigest())
        if self._bibliography_error:
            node["error"] = self._bibliography_error
            node["html"] = heading + '<p class="source-fallback">' + html.escape(self._bibliography_error) + '</p></section>'
            return node
        entries, errors = [], []
        for entry in self._bibliography_entries:
            position = entry["bodyStart"]
            location = {"path": str(path), "line": source.count("\n", 0, position) + 1,
                        "column": position - source.rfind("\n", 0, position)}
            try:
                label = self.render_title(entry["label"])
                body = self.render(entry["body"], source=location)
            except PaperError as error:
                errors.append(str(error))
                label = html.escape(entry["label"])
                body = '<p class="source-fallback">' + html.escape(str(error)) + '</p><pre>' + html.escape(entry["body"]) + '</pre>'
            entries.append('<li class="bibliography-entry"><span class="bibliography-label">[' + label + ']</span> ' + body + '</li>')
        node["html"] = heading + '<ul class="bibliography-list">' + "".join(entries) + '</ul></section>'
        if errors:
            node["error"] = "\n".join(errors)
        return node

    def _index(self):
        text = self._masked
        document = re.search(r"\\begin\s*\{document\}", text)
        start = document.end() if document else 0
        finish = re.search(r"\\end\s*\{document\}", text[start:])
        end = start + finish.start() if finish else len(text)
        self._body_start, self._body_end = start, end
        bibliography_boundaries = [start + match.start() for match in re.finditer(r"\\(?:bibliography|bibliographystyle|printbibliography)\b|\\begin\s*\{thebibliography\}", text[start:end])]
        units, headings, labels, stack = [], [], [], []
        for command in re.finditer(r"\\bibliography\b", text[start:end]):
            position = start + command.start()
            try:
                _, after = _group(text, start + command.end())
                units.append(_Unit("bibliography", position, after, position, after, "References"))
            except ValueError:
                pass
        pattern = re.compile(r"\\(begin|end|label|" + "|".join(_HEADINGS) + r")\b\*?")
        for match in pattern.finditer(text, start, end):
            kind = match.group(1)
            try:
                if kind in _HEADINGS:
                    _, i = _optional(text, match.end())
                    title, i = _group(text, i)
                    headings.append(_Unit(kind, match.start(), end, i, end, title, level=_HEADINGS[kind]))
                elif kind == "label":
                    label, _ = _group(text, match.end())
                    labels.append((label, match.start()))
                elif kind == "begin":
                    env, i = _group(text, match.end())
                    title, body = _optional(text, i) if env in self.theorems or env in {"proof", "enumerate", "itemize"} else (None, i)
                    stack.append((env, match.start(), body, title or ""))
                else:
                    env, i = _group(text, match.end())
                    if stack and stack[-1][0] == env:
                        _, beginning, body, title = stack.pop()
                        unit_kind = "statement" if env in self.theorems else "equation" if env in _DISPLAYS else env if env in {"proof", "abstract"} else "prose" if env in {"itemize", "enumerate", "quote", "quotation", "center"} else None
                        if unit_kind:
                            units.append(_Unit(unit_kind, beginning, i, body, match.start(), title, env))
                    else:
                        self.diagnostics.append(f"{self._where(match.start())[0]}: unmatched environment end {env!r}")
            except ValueError:
                self.diagnostics.append(f"{self._where(match.start())[0]}: malformed {kind} command")
        for i, heading in enumerate(headings):
            heading_end = next((other.start for other in headings[i + 1:] if other.level <= heading.level), end)
            heading.end = heading.body_end = next((boundary for boundary in bibliography_boundaries if heading.start < boundary < heading_end), heading_end)
        units += headings
        proofs = sorted((u for u in units if u.kind == "proof"), key=lambda u: u.start)
        for unit in units:
            if unit.kind == "statement":
                following = next((p for p in proofs if p.start >= unit.end), None)
                if following and not text[unit.end:following.start].strip():
                    unit.proof = following
        self._units, self._label_units, self._ambiguous = units, {}, set()
        self._label_positions = {}
        self._anchors = {}
        self.labels = {}
        for label, position in labels:
            enclosing = [u for u in units if u.kind not in _HEADINGS and u.start <= position < u.end]
            if not enclosing:
                # A section owns labels immediately after its heading, not every
                # otherwise-unattached label in its body.  The latter identify
                # ordinary prose paragraphs, including existing informal text.
                enclosing = [u for u in headings if u.body_start <= position < u.end and not re.sub(r"\\label\s*\{[^}]+\}", "", text[u.body_start:position]).strip()]
            unit = min(enclosing, key=lambda u: u.end - u.start) if enclosing else None
            if unit is None:
                breaks = list(re.finditer(r"\n[ \t]*\n", text[start:end]))
                before = [start + b.end() for b in breaks if start + b.end() <= position]
                after = [start + b.start() for b in breaks if start + b.start() > position]
                first, last = (before[-1] if before else start), (after[0] if after else end)
                if not re.sub(r"\\label\s*\{[^}]+\}", "", text[first:last]).strip():
                    following = _space(text, last)
                    boundary = re.search(r"\n[ \t]*\n", text[following:end])
                    last = following + boundary.start() if boundary else end
                unit = _Unit("paragraph", first, last, first, last)
            if label in self.labels:
                self._ambiguous.add(label)
            self._label_units[label] = unit
            self._label_positions[label] = position
            source, line, column = self._where(position)
            self.labels[label] = {"label": label, "kind": unit.kind, "environment": unit.env or None, "title": self._title(label, unit), "number": self.numbers.get(label), "source": source, "line": line, "column": column, "hasProof": unit.proof is not None, "url": self.reference_base + quote(label, safe=":")}

    def add_anchor(self, alias, within_label, heading=None, part="section"):
        """Name an exact source heading or its introductory setup externally.

        ``within_label`` must identify a heading.  ``heading`` selects exactly
        one heading with that literal TeX title inside its range; None selects
        the labeled heading itself.  A setup includes the heading and prose or
        displays before its first nested heading or theorem-like statement.
        Setup aliases are excerpt selectors, so adding them never duplicates
        the introduction in the ordinary paper outline.
        """
        if not isinstance(alias, str) or not alias.strip():
            raise PaperError("An anchor alias must be a nonempty string", self.path)
        if alias in self.labels:
            raise PaperError(f"Anchor alias {alias!r} already exists; choose a distinct label", self.path)
        if part not in {"section", "setup"}:
            raise PaperError(f"Unknown anchor part {part!r}; use 'section' or 'setup'", self.path)
        # Apply the usual missing and duplicate-label diagnostics before using
        # a label's range as a selector.
        self.get(within_label, render=False)
        within = self._label_units[within_label]
        if within.level == 99:
            raise PaperError(f"Anchor scope {within_label!r} must label a section or another heading", self.path)
        if heading is None:
            selected = within
        else:
            matches = [unit for unit in self._units if unit.level != 99
                       and within.start <= unit.start < within.end
                       and unit.end <= within.end and unit.title == heading]
            if not matches:
                raise PaperError(f"No heading with exact title {heading!r} within {within_label!r}", self.path)
            if len(matches) != 1:
                locations = ", ".join(f"{path}:{line}" for path, line, _ in (self._where(unit.start) for unit in matches))
                raise PaperError(f"Ambiguous heading {heading!r} within {within_label!r}: {len(matches)} matches ({locations}); select a narrower labeled heading", self.path)
            selected = matches[0]
        original_labels = [key for key, unit in self._label_units.items()
                           if unit is selected and key not in self._ambiguous]
        number = next((self.numbers[key] for key in original_labels if key in self.numbers), None)
        unit = selected
        if part == "setup":
            boundary = min([other.start for other in self._units
                            if selected.body_start <= other.start < selected.end
                            and (other.level != 99 or other.kind == "statement")]
                           or [selected.end])
            unit = _Unit("setup", selected.start, boundary, selected.body_start, boundary, selected.title + ": setup")
        if number is not None:
            self.numbers[alias] = number
        source, line, column = self._where(unit.start)
        self._label_units[alias] = unit
        self._label_positions[alias] = unit.start
        self._anchors[alias] = {"within": within_label, "heading": heading, "part": part}
        self.labels[alias] = {"label": alias, "kind": unit.kind, "environment": None,
                              "title": self._title(alias, unit), "number": number,
                              "source": source, "line": line, "column": column,
                              "hasProof": False, "url": self.reference_base + quote(alias, safe=":"),
                              "anchor": dict(self._anchors[alias])}
        return dict(self.labels[alias])

    def _title(self, label, unit):
        number = self.numbers.get(label)
        if unit.kind == "statement":
            title = self.theorems[unit.env] + (" " + number if number else "")
            return title + (".  " + unit.title if unit.title else "")
        if unit.kind == "equation":
            return "Equation " + (f"({number})" if number else f"[{label}]")
        if unit.kind == "proof":
            return unit.title or f"Proof [{label}]"
        return ((number + "  ") if number else "") + (unit.title or label)

    def _source_parts(self, start, end):
        parts = []
        for span in self._spans:
            first, last = max(start, span.start), min(end, span.end)
            if last <= first:
                continue
            a, b = span.source_start + first - span.start, span.source_start + last - span.start
            path, text = str(span.path), self.files[str(span.path)]
            if parts and parts[-1]["source"] == path and parts[-1]["end"] == a:
                parts[-1]["end"] = b
                parts[-1]["endLine"] = text.count("\n", 0, max(a, b - 1)) + 1
                parts[-1]["tex"] += text[a:b]
            else:
                parts.append({"source": path, "start": a, "end": b, "line": text.count("\n", 0, a) + 1, "endLine": text.count("\n", 0, max(a, b - 1)) + 1, "tex": text[a:b]})
        return parts

    def get(self, label, part="auto", render=True):
        if isinstance(label, (list, tuple)):
            excerpts = [self.get(item, part, render=render) for item in label]
            if not excerpts:
                raise PaperError("Select at least one paper label", self.path)
            result = dict(excerpts[0])
            result.update(label=list(label), title="; ".join(e["title"] for e in excerpts), tex="\n\n".join(e["tex"] for e in excerpts), sources=[s for e in excerpts for s in e["sources"]], fingerprint=hashlib.sha256("".join(e["fingerprint"] for e in excerpts).encode()).hexdigest())
            if render:
                result["html"] = "".join(e["html"] for e in excerpts)
            return result
        if label not in self._label_units:
            raise PaperError(f"Unknown paper label {label!r}", self.path)
        if label in self._ambiguous:
            raise PaperError(f"Duplicate paper label {label!r}; its source is ambiguous", self.path)
        if part not in {"auto", "statement", "proof", "both", "section"}:
            raise PaperError(f"Unknown selection part {part!r}", self.path)
        unit = self._label_units[label]
        start, end = unit.start, unit.end
        if part == "proof":
            if unit.kind == "proof":
                pass
            elif unit.proof:
                start, end = unit.proof.start, unit.proof.end
            else:
                raise PaperError(f"No adjacent proof for {label!r}; select its separately labeled proof or subsection explicitly", **{k: self.labels[label][k] for k in ("source", "line", "column")})
        elif part == "section" and unit.kind != "setup":
            if unit.kind == "paragraph" and unit.level == 99:
                raise PaperError(f"{label!r} labels a paragraph; select a section's own label for a section excerpt", self.path)
            enclosing = [u for u in self._units if u.kind in _HEADINGS and u.start <= unit.start < u.end]
            if not enclosing:
                raise PaperError(f"No enclosing section for {label!r}", self.path)
            selected = min(enclosing, key=lambda u: u.end - u.start)
            start, end = selected.start, selected.end
        elif part in {"auto", "both"} and unit.proof:
            end = unit.proof.end
        while start < end and self._text[start].isspace():
            start += 1
        while end > start and self._text[end - 1].isspace():
            end -= 1
        sources = self._source_parts(start, end)
        tex = self._text[start:end]
        fingerprint_data = {"sources": [{"source": str(Path(s["source"]).relative_to(self.path.parent)) if Path(s["source"]).is_relative_to(self.path.parent) else s["source"], "tex": s["tex"]} for s in sources], "macros": self.macros}
        last_same_source = next(s for s in reversed(sources) if s["source"] == sources[0]["source"])
        result = {**self.labels[label], "part": part, "tex": tex, "sources": sources, "span": [start, end], "source": sources[0]["source"], "line": sources[0]["line"], "endLine": last_same_source["endLine"], "multipleSources": len({s["source"] for s in sources}) > 1, "fingerprint": hashlib.sha256(json.dumps(fingerprint_data, sort_keys=True).encode()).hexdigest(), "macroFingerprint": self.macro_fingerprint}
        if render:
            result["html"] = self._render(tex, lambda offset: self._where(start + offset))
        return result

    def labels_within(self, start, end):
        """Labels whose source position lies in the given range of the combined text."""
        return [label for label, position in self._label_positions.items() if start <= position < end]

    def raw(self, label, part="auto"):
        return self.get(label, part, render=False)

    def outline(self, scope=None):
        """Return the paper in source order, with optional labels for overlays.

        Heading nodes own only their heading, and have ordered children.  Prose
        between structural units is retained as anonymous leaves.  Statements
        and their adjacent proofs occupy one leaf; contained equation labels are
        aliases, so their mathematics is not copied a second time.  Each leaf
        can fail to render independently while retaining exact source and an
        actionable ``error``.  No annotation is needed to obtain this tree.
        """
        if scope is not None:
            # Reuse the public validation for unknown/ambiguous source labels.
            self.get(scope, render=False)
            scoped = self._label_units[scope]
        else:
            scoped = None

        candidates, seen = [], set()
        extra_units = [unit for label, unit in self._label_units.items()
                       if self._anchors.get(label, {}).get("part") != "setup" or label == scope]
        for unit in [*self._units, *extra_units]:
            signature = (unit.kind, unit.start, unit.end, unit.env)
            if signature not in seen:
                seen.add(signature)
                candidates.append(unit)
        candidates.sort(key=lambda unit: (unit.start, -unit.end))
        label_order = sorted((label for label in self._label_positions
                              if self._anchors.get(label, {}).get("part") != "setup" or label == scope),
                             key=self._label_positions.get)
        anonymous_ids = {}
        occurrences = {}
        for unit in candidates:
            path, _, _ = self._where(unit.start)
            key = (str(Path(path).relative_to(self.path.parent)) if Path(path).is_relative_to(self.path.parent) else path, unit.kind, unit.env, unit.title)
            occurrences[key] = occurrences.get(key, 0) + 1
            anonymous_ids[id(unit)] = "paper-" + hashlib.sha256(json.dumps([*key, occurrences[key]]).encode()).hexdigest()[:14]

        def equivalent(first, second):
            return (first.kind, first.start, first.end, first.env) == (second.kind, second.start, second.end, second.env)

        def own_labels(unit):
            labels = [key for key in label_order if key not in self._ambiguous and equivalent(self._label_units[key], unit)]
            # Source labels remain canonical even though external aliases point
            # to the beginning of a heading, before its literal \\label command.
            return sorted(labels, key=lambda key: key in self._anchors)

        def extent(unit):
            return unit.proof.end if unit.kind == "statement" and unit.proof else unit.end

        def payload(first, last, kind, title="", label=None, identifier=None):
            while first < last and self._text[first].isspace():
                first += 1
            while last > first and self._text[last - 1].isspace():
                last -= 1
            spans = self._source_parts(first, last)
            path, line, _ = self._where(first)
            tex = self._text[first:last]
            identity = identifier or label or "paper-prose-" + hashlib.sha256((path + "\0" + tex).encode()).hexdigest()[:14]
            same_file = [span for span in spans if span["source"] == path]
            return {"id": identity, "label": label, "aliases": [], "nestedAliases": [], "title": title, "kind": kind,
                    "html": "", "tex": tex, "source": path, "line": line,
                    "endLine": same_file[-1]["endLine"] if same_file else line,
                    "sources": spans, "fingerprint": hashlib.sha256(json.dumps({"tex": tex, "macros": self.macros}, sort_keys=True).encode()).hexdigest(),
                    "children": []}

        def render_range(first, last):
            return self._render(self._text[first:last], lambda offset: self._where(first + offset))

        prose_occurrences = {}

        def prose(first, last):
            output = []
            for a, b in self._paragraph_ranges(first, last):
                if not self._masked[a:b].strip():
                    continue
                node = payload(a, b, "prose")
                # Repeated identical prose in the same source remains distinct.
                base = node["id"]
                prose_occurrences[base] = prose_occurrences.get(base, 0) + 1
                if prose_occurrences[base] > 1:
                    node["id"] += "-" + str(prose_occurrences[base])
                try:
                    node["html"] = render_range(a, b)
                except PaperError as error:
                    node["error"] = str(error)
                if node["html"] or node.get("error"):
                    output.append(node)
            return output

        def sequence(first, last, parent=None):
            children, cursor = [], first
            for unit in candidates:
                if unit is parent or unit.start < cursor or unit.start < first or extent(unit) > last:
                    continue
                children.extend(prose(cursor, unit.start))
                children.append(build(unit))
                cursor = extent(unit)
            children.extend(prose(cursor, last))
            return children

        def build(unit):
            labels = own_labels(unit)
            label = labels[0] if labels else None
            identity = label or anonymous_ids.get(id(unit))
            if unit.level != 99:
                heading_end = unit.body_start
                while True:
                    next_label = re.match(r"\s*\\label\s*\{[^}]+\}", self._masked[heading_end:unit.end])
                    if not next_label:
                        break
                    heading_end += next_label.end()
                title = self._title(label, unit) if label else unit.title
                node = payload(unit.start, heading_end, unit.kind, title, label, identity)
                node["headingLevel"] = unit.level
                node["aliases"] = labels[1:]
                node["children"] = sequence(heading_end, unit.end, unit)
                node["fingerprint"] = hashlib.sha256(json.dumps({"heading": node["fingerprint"], "children": [child["fingerprint"] for child in node["children"]]}).encode()).hexdigest()
                try:
                    renderer = _Renderer(self, lambda offset: self._where(unit.start + offset))
                    node["titleHtml"] = renderer.inline_fragment(title, 0, 0)
                    self._check_math(renderer.math)
                except PaperError as error:
                    node["error"] = str(error)
                return node

            last = extent(unit)
            title = self._title(label, unit) if label else self.theorems.get(unit.env, unit.title or {"proof": "Proof", "abstract": "Abstract"}.get(unit.kind, ""))
            node = payload(unit.start, last, unit.kind, title, label, identity)
            contained = [key for key in label_order if unit.start <= self._label_positions[key] < last and key != label and key not in self._ambiguous]
            node["aliases"] = contained
            node["nestedAliases"] = [key for key in contained if not equivalent(self._label_units[key], unit)]
            if unit.kind == "bibliography":
                return self._bibliography_outline(node)
            try:
                if unit.kind == "statement":
                    node["statementHtml"] = render_range(unit.start, unit.end)
                    node["proofHtml"] = render_range(unit.proof.start, unit.proof.end) if unit.proof else ""
                    node["proofTitle"] = unit.proof.title or "Proof" if unit.proof else ""
                    node["html"] = node["statementHtml"] + node["proofHtml"]
                else:
                    node["html"] = render_range(unit.start, last)
            except PaperError as error:
                node["html"] = ""
                node["error"] = str(error)
            return node

        if scoped:
            canonical = next(unit for unit in candidates if equivalent(unit, scoped))
            return build(canonical)
        root = payload(self._body_start, self._body_start, "document", self.title, identifier="paper-document")
        root["children"] = sequence(self._body_start, self._body_end)
        root["fingerprint"] = hashlib.sha256(json.dumps([child["fingerprint"] for child in root["children"]]).encode()).hexdigest()
        return root

    def _paragraph_ranges(self, first, last):
        """Split interstitial prose without cutting a list, group, or formula."""
        text, cursor, start, groups, environments = self._masked, first, first, 0, []
        result = []
        while cursor < last:
            if text[cursor] == "\\":
                command = _COMMAND.match(text, cursor)
                if command:
                    name, after = command.group(1), command.end()
                    if name in {"(", "["}:
                        delimiter = r"\)" if name == "(" else r"\]"
                        end = text.find(delimiter, after, last)
                        cursor = end + len(delimiter) if end >= 0 else last
                        continue
                    if name in {"begin", "end"}:
                        try:
                            env, after = _group(text, after)
                            if name == "begin":
                                environments.append(env)
                            elif environments:
                                environments.pop()
                        except ValueError:
                            pass
                    cursor = after
                    continue
            if text[cursor] == "$":
                delimiter = "$$" if text.startswith("$$", cursor) else "$"
                end = cursor + len(delimiter)
                while True:
                    end = text.find(delimiter, end, last)
                    if end < 0:
                        cursor = last
                        break
                    back = end - 1
                    while back >= first and text[back] == "\\":
                        back -= 1
                    if (end - back - 1) % 2 == 0:
                        cursor = end + len(delimiter)
                        break
                    end += len(delimiter)
                continue
            if text[cursor] == "{":
                groups += 1
            elif text[cursor] == "}":
                groups = max(0, groups - 1)
            if text[cursor] == "\n" and not groups and not environments:
                blank = re.match(r"\n[ \t]*\n", text[cursor:last])
                if blank:
                    result.append((start, cursor))
                    cursor += blank.end()
                    start = cursor
                    continue
            cursor += 1
        if start < last:
            result.append((start, last))
        return result

    def render(self, tex, source=None):
        if isinstance(source, dict):
            path = str(source.get("path", source.get("file", self.path)))
            first_line, first_column = source.get("line", 1), source.get("column", 1)
        else:
            path, first_line, first_column = str(source or self.path), 1, 1

        def where(offset):
            lines = tex.count("\n", 0, offset)
            column = offset - tex.rfind("\n", 0, offset)
            return path, first_line + lines, column + (first_column - 1 if lines == 0 else 0)

        return self._render(tex, where)

    def render_title(self, tex):
        renderer = _Renderer(self, lambda offset: (str(self.path), 1, offset + 1))
        result = renderer.inline_fragment(tex, 0, 0)
        self._check_math(renderer.math)
        return result

    def _render(self, tex, where):
        renderer = _Renderer(self, where)
        result = renderer.fragment(_mask_comments(tex))
        self._check_math(renderer.math)
        return result

    def _check_math(self, expressions):
        pending = [e for e in expressions if (e["tex"], e["display"]) not in self._validated_math]
        if not pending or not self.validate_math:
            return
        node = shutil.which("node")
        if not node or not _KATEX.exists():
            raise PaperError("Math validation needs Node and the bundled KaTeX.  Pass validate_math=False only to retain explicitly unvalidated TeX.", self.path)
        script = """const fs=require('fs'),k=require(process.argv[1]),d=JSON.parse(fs.readFileSync(0,'utf8'));let errors=[];d.math.forEach((m,i)=>{try{k.renderToString(m.tex,{displayMode:m.display,macros:d.macros,throwOnError:true,strict:false})}catch(e){errors.push({i,message:e.message})}});process.stdout.write(JSON.stringify(errors));"""
        result = subprocess.run([node, "-e", script, str(_KATEX)], input=json.dumps({"math": pending, "macros": self.macros}), text=True, capture_output=True)
        if result.returncode:
            raise PaperError("KaTeX validation failed to run: " + result.stderr.strip(), self.path)
        errors = json.loads(result.stdout)
        if errors:
            error = errors[0]
            source, line, column = pending[error["i"]]["where"]
            raise PaperError(error["message"] + ".  Define a supported macro or supply an explicit adapter expansion; exact TeX remains available via render=False.", source, line, column)
        self._validated_math.update((e["tex"], e["display"]) for e in pending)


class _Renderer:
    """Strict structure around the existing converter's prose and math output."""

    def __init__(self, paper, where: Callable):
        self.paper, self.conv, self.where, self.math = paper, paper._conv, where, []

    def error(self, message, offset):
        raise PaperError(message, *self.where(offset))

    def _math(self, tex, display, offset, env=None):
        labels = re.findall(r"\\label\{([^}]+)\}", tex)
        clean = re.sub(r"\\label\{[^}]+\}", "", tex).strip()
        # KaTeX has no \sideset; \sideset{}{'}\bigotimes, the restricted tensor product, becomes \bigotimes'.
        clean = re.sub(r"\\sideset\s*\{\}\s*\{([^{}]*)\}\s*(\\[A-Za-z]+)", r"\2\1", clean)
        if env and env.startswith("align"):
            clean = r"\begin{aligned}" + clean + r"\end{aligned}"
        elif env and env.startswith(("gather", "multline")):
            clean = r"\begin{gathered}" + clean + r"\end{gathered}"
        numbers = list(dict.fromkeys(self.paper.numbers[key] for key in labels if self.paper.numbers.get(key)))
        if display and len(numbers) == 1 and not re.search(r"\\tag\*?\s*\{", clean):
            clean += r"\tag{" + numbers[0] + "}"
        self.math.append({"tex": clean, "display": display, "where": self.where(offset)})
        tags = '<span class="equation-tags" aria-label="Equation numbers">' + ", ".join("(" + html.escape(number) + ")" for number in numbers) + '</span>' if display and len(numbers) > 1 else ""
        # Labels become anchors, so that a reader can jump to this display.
        anchors = f' data-anchors="{html.escape(" ".join(labels))}"' if display and labels else ""
        return (f'<div class="display"{anchors}><span class="m display">' if display else '<span class="m">') + html.escape(clean) + ("</span>" + tags + "</div>" if display else "</span>")

    def _tabular(self, inner, offset, depth):
        """A simple tabular: column specification, rows ended by \\\\, cells separated by &, rules ignored."""
        spec, start = _group(inner, 0)
        rows, cell_start, nesting, row = [], start, 0, []
        for match in re.finditer(r"\{|\}|\\\\|&|\\.", inner[start:]):
            token, at = match.group(0), start + match.start()
            if token == "{":
                nesting += 1
            elif token == "}":
                nesting -= 1
            elif nesting == 0 and token in ("&", "\\\\"):
                row.append((cell_start, at))
                cell_start = start + match.end()
                if token == "\\\\":
                    rows.append(row)
                    row = []
        if inner[cell_start:].strip():
            row.append((cell_start, len(inner)))
        if row:
            rows.append(row)
        out = []
        for index, cells in enumerate(rows):
            tag = "th" if index == 0 else "td"
            out.append("<tr>" + "".join(f"<{tag}>" + self.inline_fragment(re.sub(r"\\hline\b", " ", inner[a:b]).strip(), offset + a, depth + 1) + f"</{tag}>" for a, b in cells) + "</tr>")
        return '<div class="paper-table"><table>' + "".join(out) + "</table></div>"

    def _environment_end(self, text, start, name, offset):
        stack = [name]
        for match in re.finditer(r"\\(begin|end)\s*\{([^}]+)\}", text[start:]):
            if match.group(1) == "begin":
                stack.append(match.group(2))
            elif not stack or stack.pop() != match.group(2):
                self.error("Mismatched environment end " + match.group(2), offset + start + match.start())
            if not stack:
                return start + match.start(), start + match.end()
        self.error("Unclosed environment " + name, offset + start)

    def inline_fragment(self, text, offset, depth):
        value = self.fragment(text, offset, depth)
        prefix, suffix = '<div class="paper-paragraph">', '</div>'
        if value.startswith(prefix) and value.endswith(suffix):
            value = value[len(prefix):-len(suffix)]
        if re.search(r"<(?:div|section|h[1-6]|ul|ol|aside)\b", value):
            self.error("Block content is not supported inside an inline command or heading", offset)
        return value

    def fragment(self, text, offset=0, depth=0):
        if depth > 35:
            self.error("Macro expansion or environment nesting exceeds the supported depth; check for recursion", offset)
        out, buf, paragraph = [], [], False

        def close():
            nonlocal paragraph
            if paragraph:
                out.append("</div>")
                paragraph = False

        def inline(value):
            nonlocal paragraph
            if not paragraph:
                out.append('<div class="paper-paragraph">')
                paragraph = True
            out.append(value)

        def flush():
            value = "".join(buf)
            buf.clear()
            for bit in re.split(r"(\n\s*\n)", value):
                if re.fullmatch(r"\n\s*\n", bit):
                    close()
                elif bit and (bit.strip() or paragraph):
                    inline(self.conv.plain(bit))

        def block(value):
            flush()
            close()
            out.append(value)

        i = 0
        while i < len(text):
            if text[i] == "{":
                # Ordinary BibTeX styles use scoped declarations such as
                # {\em Journal Name}.  Preserve their text and emphasis without
                # interpreting general TeX font or package programming.
                try:
                    inner, after = _group(text, i)
                    emphasis = re.match(r"\s*\\(?:em|itshape)\b\s*", inner)
                    if emphasis:
                        flush()
                        inline('<em>' + self.inline_fragment(inner[emphasis.end():], offset + i + 1 + emphasis.end(), depth + 1) + '</em>')
                        i = after
                        continue
                except ValueError:
                    pass
            if text[i] == "$":
                delimiter = "$$" if text.startswith("$$", i) else "$"
                end = i + len(delimiter)
                while True:
                    end = text.find(delimiter, end)
                    if end < 0:
                        self.error("Unclosed mathematical delimiter " + delimiter, offset + i)
                    if not end or text[end - 1] != "\\":
                        break
                    end += len(delimiter)
                flush()
                value = self._math(text[i + len(delimiter):end], delimiter == "$$", offset + i)
                block(value) if delimiter == "$$" else inline(value)
                i = end + len(delimiter)
                continue
            if text[i] != "\\":
                buf.append(text[i]); i += 1; continue
            match = _COMMAND.match(text, i)
            if not match:
                self.error("Incomplete control sequence", offset + i)
            command, j = match.group(1), match.end()
            flush()
            try:
                if command in {"(", "["}:
                    delimiter = r"\)" if command == "(" else r"\]"
                    end = text.find(delimiter, j)
                    if end < 0:
                        self.error("Unclosed mathematical delimiter", offset + i)
                    value = self._math(text[j:end], command == "[", offset + i)
                    block(value) if command == "[" else inline(value)
                    i = end + 2; continue
                if command == "begin":
                    env, body_start = _group(text, j)
                    optional, body_start = _optional(text, body_start) if env in self.paper.theorems or env in {"proof", "enumerate", "itemize"} else (None, body_start)
                    end, after = self._environment_end(text, body_start, env, offset)
                    inner = text[body_start:end]
                    if env in _DISPLAYS:
                        block(self._math(inner, True, offset + i, env))
                    elif env in self.paper.theorems or env == "proof":
                        own_label = next((key for key in re.findall(r"\\label\{([^}]+)\}", inner) if self.paper.labels.get(key, {}).get("environment") == env), None)
                        number = self.paper.numbers.get(own_label) if own_label else None
                        title = "Proof" if env == "proof" else self.paper.theorems[env]
                        if number and env != "proof":
                            title += " " + number
                        if optional:
                            title += " (" + optional + ")"
                        title_html = self.inline_fragment(title, offset + i, depth + 1)
                        block('<section class="paper-' + ("proof" if env == "proof" else "statement") + '"><h4>' + title_html + '.</h4>' + self.fragment(inner, offset + body_start, depth + 1) + '</section>')
                    elif env in {"itemize", "enumerate"}:
                        items, nesting, item_start = [], 0, None
                        for item in re.finditer(r"\\(begin|end)\s*\{[^}]+\}|\\item\b", inner):
                            if item.group(1) == "begin":
                                nesting += 1
                            elif item.group(1) == "end":
                                nesting -= 1
                            elif nesting == 0:
                                if item_start is not None:
                                    items.append((item_start, item.start()))
                                item_start = item.end()
                        if item_start is not None:
                            items.append((item_start, len(inner)))
                        if not items or inner[:items[0][0] - len(r"\item")].strip():
                            self.error("A list must begin with a supported \\item", offset + body_start)
                        tag = "ul" if env == "itemize" else "ol"
                        item_html = []
                        for first, last in items:
                            marker, content_start = _optional(inner, first)
                            lead = '<strong class="item-label">' + self.inline_fragment(marker, offset + body_start + first, depth + 1) + '</strong> ' if marker else ""
                            item_html.append("<li>" + lead + self.fragment(inner[content_start:last], offset + body_start + content_start, depth + 1) + "</li>")
                        block(f'<{tag}>' + "".join(item_html) + f'</{tag}>')
                    elif env == "abstract":
                        block('<section class="paper-abstract"><h4>Abstract</h4>' + self.fragment(inner, offset + body_start, depth + 1) + '</section>')
                    elif env == "tabular":
                        block(self._tabular(inner, offset + body_start, depth))
                    elif env in {"quote", "quotation", "center"}:
                        block('<div class="paper-' + env + '">' + self.fragment(inner, offset + body_start, depth + 1) + '</div>')
                    else:
                        self.error(f"Unsupported environment {env!r}.  Select a smaller labeled passage or add a supported adapter for this environment", offset + i)
                    i = after; continue
                if command in _HEADINGS:
                    if text[j:j + 1] == "*":
                        j += 1
                    _, j = _optional(text, j)
                    title, after = _group(text, j)
                    own_label = re.match(r"\s*\\label\{([^}]+)\}", text[after:])
                    number = self.paper.numbers.get(own_label.group(1)) if own_label else None
                    block('<h4 class="paper-heading">' + (html.escape(number) + "  " if number else "") + self.inline_fragment(title, offset + j, depth + 1) + '</h4>')
                    i = after; continue
                if command in {"label", "ref", "eqref"}:
                    value, after = _group(text, j)
                    if command != "label":
                        inline(self.conv.ref(value, command == "eqref"))
                    else:
                        inline('<span class="paper-anchor" data-anchor="' + html.escape(value.strip()) + '"></span>')
                    i = after; continue
                if command == "cite":
                    note, j = _optional(text, j)
                    keys, after = _group(text, j)
                    inline(self.conv.cite(None, keys)[:-1] + (", " + self.inline_fragment(note, offset + j, depth + 1) if note else "") + "]")
                    i = after; continue
                if command in {"emph", "textit", "textbf", "textrm", "textsf", "texttt", "textsc", "text"}:
                    inner, after = _group(text, j)
                    tag = {"emph": "em", "textit": "em", "textbf": "strong", "texttt": "code"}.get(command, "span")
                    inline(f'<{tag}>' + self.inline_fragment(inner, offset + j + 1, depth + 1) + f'</{tag}>')
                    i = after; continue
                if command == "lean":
                    # \lean{Decl}: a link to the row of Decl in the paper's appendix on Lean.
                    decl, after = _group(text, j)
                    decl = decl.strip()
                    inline(f'<a class="lean" href="#p:lean:{html.escape(decl, quote=True)}" data-decl="{html.escape(decl, quote=True)}" title="Lean: {html.escape(decl, quote=True)}">Lean</a>')
                    i = after; continue
                if command == "leanentry":
                    # \leanentry{Decl}{file}{line}: the row of Decl, linking to its source at the pinned commit.
                    decl, after = _group(text, j)
                    path, after = _group(text, after)
                    line, after = _group(text, after)
                    url = self.paper.lean_url(path.strip(), line.strip())
                    inline(f'<span class="paper-anchor" data-anchor="lean:{html.escape(decl.strip(), quote=True)}"></span>'
                           f'<a class="lean-entry" href="{html.escape(url, quote=True)}"><code>{html.escape(decl.strip())}</code></a>')
                    i = after; continue
                if command in {"title", "date", "setcounter"}:
                    # The reader shows the title and date itself; \setcounter changes only the PDF.
                    _, j = _optional(text, j)
                    for _ in range(2 if command == "setcounter" else 1):
                        _, j = _group(text, j)
                    i = j; continue
                if command in {"author", "address", "email", "curraddr", "urladdr", "subjclass", "keywords", "thanks"}:
                    # The front matter of amsart, as short paragraphs.
                    year, j = _optional(text, j)
                    value, after = _group(text, j)
                    lead = {"subjclass": (year + " " if year else "") + "Mathematics Subject Classification. ", "keywords": "Key words and phrases. "}.get(command, "")
                    block(f'<p class="p-front-{command}">' + html.escape(lead) + self.inline_fragment(value, offset + j + 1, depth + 1) + "</p>")
                    i = after; continue
                if command in {"url", "href"}:
                    url, after = _group(text, j)
                    if re.fullmatch(r"\s*\\[A-Za-z]+\s*", url) and url.strip() in self.paper.macros:
                        url = self.paper.macros[url.strip()]
                    title, after = _group(text, after) if command == "href" else (url, after)
                    if re.match(r"(?i)(javascript|data|vbscript):", url.strip()):
                        self.error("Unsupported URL scheme", offset + i)
                    inline('<a href="' + html.escape(url, quote=True) + '">' + (self.inline_fragment(title, offset + j, depth + 1) if command == "href" else html.escape(title)) + '</a>')
                    i = after; continue
                if command == "footnote":
                    inner, after = _group(text, j)
                    block('<aside class="paper-footnote"><strong>Footnote.</strong> ' + self.fragment(inner, offset + j, depth + 1) + '</aside>')
                    i = after; continue
                if command == "bibliographystyle":
                    _, i = _group(text, j)
                    continue
                if command == "newblock":
                    inline(" ")
                    i = j; continue
                if command in {"noindent", "medskip", "smallskip", "bigskip", "par", "qedhere", "allowbreak", "relax", "maketitle", "tableofcontents", "appendix", "sloppy", "small", "hline", "centering"}:
                    if command in {"par", "medskip", "smallskip", "bigskip"}:
                        close()
                    i = j; continue
                if command in {"emergencystretch", "tolerance", "pretolerance", "hbadness", "hfuzz"}:
                    # A line-breaking parameter, such as \emergencystretch=1em: it affects only
                    # the PDF's layout, so the assignment is dropped with its value.
                    value = re.match(r"\s*=?\s*[-+]?(?:\d+(?:\.\d*)?|\.\d+)\s*(?:pt|em|ex|mm|cm|in|bp|sp)?", text[j:])
                    i = j + (value.end() if value else 0); continue
                if command in _ACCENTS:
                    # A text accent, as in \"e, \"{e} or \'{\i}, in bibliography entries.
                    if text[j:j + 1] == "{":
                        base, after = _group(text, j)
                    else:
                        base, after = text[j:j + 1], j + 1
                    base = base.strip()
                    base = _SPECIAL_LETTERS.get(base[1:], base) if base.startswith("\\") else base
                    if len(base) != 1:
                        self.error(f"Unsupported accented text {base!r}", offset + i)
                    inline(html.escape(unicodedata.normalize("NFC", base + _ACCENTS[command])))
                    i = after; continue
                if command in _SPECIAL_LETTERS:
                    inline(_SPECIAL_LETTERS[command])
                    i = j; continue
                if command in {"S", "ldots", "dots", "TeX", "LaTeX", "quad", "qquad"}:
                    inline({"S": "§", "ldots": "…", "dots": "…", "TeX": "TeX", "LaTeX": "LaTeX", "quad": "&emsp;", "qquad": "&emsp;&emsp;"}[command])
                    i = j; continue
                if len(command) == 1 and command in "%&#$_, \\{}":
                    inline(self.conv.plain(text[i:j]))
                    i = j; continue
                name = "\\" + command
                if name in self.paper._macro_defs:
                    macro = self.paper._macro_defs[name]
                    if macro.unsupported:
                        self.error(f"Macro {name} uses unsupported {macro.unsupported}; supply an explicit adapter expansion", offset + i)
                    arguments = []
                    for _ in range(macro.nargs):
                        argument, j = _group(text, j)
                        arguments.append(argument)
                    expanded = re.sub(r"#([1-9])", lambda m: arguments[int(m.group(1)) - 1], macro.body)
                    inline(self.inline_fragment(expanded, offset + i, depth + 1))
                    i = j; continue
                self.error(f"Unsupported prose command {name}.  Define a simple macro, configure an explicit expansion, or use a fuller LaTeX adapter; exact source remains available with render=False", offset + i)
            except PaperError:
                raise
            except (ValueError, IndexError) as error:
                self.error(str(error), offset + i)
        flush()
        close()
        return "".join(out)


def load_paper(path, **options):
    return Paper(path, **options)
