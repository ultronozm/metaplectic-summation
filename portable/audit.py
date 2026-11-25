#!/usr/bin/env python3
"""Which pictures may have fallen behind the paper.

The captions and drawings of the figures cannot be derived from the paper, so they can go out of date: a definition
changes, and a figure about it goes on showing the old thing.  A figure depends on what its caption cites (`\\ref{...}`),
on the labels listed under `depends` in media.toml, and on what it is placed beside: the target of its sketch, and
the statements in it when that is a section.
audit.toml records a fingerprint of each of these statements as the picture was last compared with it.  The build
lists the pictures whose fingerprints no longer match and marks them on the page.  It does not fail, because the
paper is edited all the time; `build.py --require-audited` does, for a build that is about to be shared.

    python3 portable/audit.py status                  # which pictures are out of date, and why
    python3 portable/audit.py diff PICTURE            # what changed in the statements it depends on
    python3 portable/audit.py accept [PICTURE ...]    # record the paper as it is now (every picture if none is named)
    python3 portable/audit.py accept --at COMMIT      # ... or as it was at a commit

Accept only after reading the diff and correcting the text of the picture where it needs it.  A fingerprint ignores
whitespace, comments, `\\label`, the author's `\\pn` notes, emphasis, and the spellings that mean the same to a reader
(see `VARIANTS`), so that a pass over the style of the paper leaves it alone.  It covers a statement without its proof.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import html
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import edition  # noqa: E402
import media  # noqa: E402
from edition import PAPER  # noqa: E402
from edition import EditionError, esc  # noqa: E402

LOCK = HERE / "audit.toml"
ROOT = HERE.parent

HEADER = """\
# Which statements of the paper each picture was last compared with: a fingerprint of each statement it cites or sits
# beside, and the version of the paper it was compared with.  The build marks a picture on the page when a fingerprint
# no longer matches, and python3 portable/audit.py explains why and records the new version once the picture's text has
# been checked.  Written by audit.py; read by build.py.
"""


# ---------------------------------------------------------------- fingerprints

def strip_command(text: str, name: str) -> str:
    """Remove every \\name{...} from the text, with balanced braces."""
    out, i, opening = [], 0, re.compile(r"\\" + name + r"\s*\{")
    while True:
        match = opening.search(text, i)
        if not match:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:match.start()])
        depth, j = 1, match.end()
        while j < len(text) and depth:
            if text[j] == "\\":
                j += 1
            else:
                depth += (text[j] == "{") - (text[j] == "}")
            j += 1
        i = j


def unwrap_command(text: str, name: str) -> str:
    """Replace every \\name{...} by its argument, which may itself contain balanced braces."""
    out, i, opening = [], 0, re.compile(r"\\" + name + r"\s*\{")
    while True:
        match = opening.search(text, i)
        if not match:
            out.append(text[i:])
            return "".join(out)
        out.append(text[i:match.start()])
        depth, j = 1, match.end()
        while j < len(text) and depth:
            if text[j] == "\\":
                j += 1
            else:
                depth += (text[j] == "{") - (text[j] == "}")
            j += 1
        out.append(unwrap_command(text[match.end():j - 1], name))
        i = j


# How the author spells things that mean the same to a reader: ellipses, the size of a delimiter, thin spaces, braces
# around a bracketed symbol, an operator that common.tex declares, a definition marked with `:=`, and how a section
# is cited.
VARIANTS = [
    (re.compile(r"\\(?:ldots|cdots|dots[bcmio])(?![A-Za-z])"), lambda m: "\\dots"),
    (re.compile(r"\\(?:left|right|[bB]ig|[bB]igg)[lrm]?(?![A-Za-z])"), lambda m: ""),
    (re.compile(r"(?<!\\)\\[,;:! ]|~|\\q?quad(?![A-Za-z])"), lambda m: ""),
    (re.compile(r"\{(\[[^\[\]{}]*\])\}"), lambda m: m.group(1)),
    (re.compile(r"\\(?:operatorname|mathrm)\{(reg|stab|temp|nt)\}"), lambda m: "\\" + m.group(1)),
    (re.compile(r"\\operatorname\{([A-Za-z]+)\}"), lambda m: "\\" + m.group(1)),
    (re.compile(r"\\(overline|underline|widetilde|widehat|hat|tilde|bar|check|vec)\s*\{(\\[A-Za-z]+|[A-Za-z0-9])\}"),
     lambda m: "\\" + m.group(1) + " " + m.group(2)),
    (re.compile(r"\\[td]frac(?![A-Za-z])"), lambda m: "\\frac"),
    (re.compile(r"\\le(?![A-Za-z])"), lambda m: "\\leq"),
    (re.compile(r"\\ge(?![A-Za-z])"), lambda m: "\\geq"),
    (re.compile(r"\\ne(?![A-Za-z])"), lambda m: "\\neq"),
    (re.compile(r":=|\\coloneqq(?![A-Za-z])"), lambda m: "="),
    (re.compile(r"(?:Sections?|(?:\\S){1,2})\s*(?=\\ref)"), lambda m: "\\S"),
]


def canonical(tex: str) -> str:
    """The text of a unit with its `\\label`s, `\\pn` notes, emphasis, and variant spellings removed, but not its whitespace."""
    for name in ("pn", "label"):
        tex = strip_command(tex, name)
    tex = unwrap_command(tex, "emph")
    for pattern, replacement in VARIANTS:
        tex = pattern.sub(replacement, tex)
    return tex


def normalize(tex: str) -> str:
    """The text of a unit as far as it matters to a picture: `canonical`, without any whitespace."""
    return re.sub(r"\s+", "", canonical(tex))


def readable(tex: str) -> str:
    """`normalize`, but with a space kept between two letters, so that a difference can be read."""
    text = re.sub(r"\s+", " ", canonical(tex))
    return re.sub(r"(?<![A-Za-z]) | (?![A-Za-z])", "", text)


def unit_text(paper: edition.Paper, label: str) -> str:
    """What a label names, as the paper writes it, without comments.

    A statement is its statement alone, not its proof; an equation or a paragraph is itself; a section is the
    statements in it, or its heading when it has none.
    """
    unit = paper._label_units[label]
    if unit.level == 99:
        return paper._masked[unit.start:unit.end]
    inside = sorted((u for u in paper._units if u.kind == "statement" and unit.start <= u.start and u.end <= unit.end),
                    key=lambda u: u.start)
    return "\n".join(paper._masked[u.start:u.end] for u in inside) or paper._masked[unit.start:unit.body_start]


def fingerprint(paper: edition.Paper, label: str) -> str:
    return hashlib.sha256(normalize(unit_text(paper, label)).encode()).hexdigest()[:12]


def dependencies(config: dict) -> dict[str, set[str]]:
    """For each figure: the labels of the paper that its caption cites or it declares, and the target of its sketch."""
    return {figure["id"]: media.figure_labels(figure) | {figure["sketch"]} for figure in media.figures(config)}


# ---------------------------------------------------------------- the record

def read_lock(path: Path = LOCK) -> dict:
    return tomllib.loads(path.read_text()).get("figure", {}) if path.is_file() else {}


def toml_key(name: str) -> str:
    return name if re.fullmatch(r"[A-Za-z0-9_-]+", name) else '"' + name.replace('"', '\\"') + '"'


def write_lock(lock: dict, order: list[str], path: Path = LOCK) -> None:
    lines = [HEADER]
    for item in [i for i in order if i in lock]:
        entry = lock[item]
        lines += [f"[figure.{toml_key(item)}]", f'at = "{entry["at"]}"', f"[figure.{toml_key(item)}.statements]"]
        lines += [f'"{label}" = "{entry["statements"][label]}"' for label in sorted(entry["statements"])]
        lines.append("")
    path.write_text("\n".join(lines))


def assess(paper: edition.Paper, deps: dict[str, set[str]], lock: dict) -> dict[str, list[tuple[str, str]]]:
    """For each picture that may be out of date: the labels, each with `changed` or `new` (never recorded)."""
    now: dict[str, str] = {}
    stale: dict[str, list[tuple[str, str]]] = {}
    for item, labels in deps.items():
        recorded = lock.get(item, {}).get("statements", {})
        for label in sorted(labels & set(paper.labels)):
            if label not in now:
                now[label] = fingerprint(paper, label)
            if recorded.get(label) != now[label]:
                stale.setdefault(item, []).append((label, "new" if label not in recorded else "changed"))
    return stale


# ---------------------------------------------------------------- the page

def short_name(paper: edition.Paper, label: str) -> str:
    """How a reader names the unit: Theorem 3.1, Equation (2), §4.2."""
    number, entry = paper.numbers.get(label), paper.labels[label]
    if not number:
        return label
    if entry["kind"] == "statement":
        return f"{paper.theorems[entry['environment']]} {number}"
    if entry["kind"] == "equation":
        return f"Equation ({number})"
    return f"\u00a7{number}" if paper._label_units[label].level != 99 else label


def note_html(paper: edition.Paper, changes: list[tuple[str, str]]) -> str:
    links = ", ".join(f'<a class="ref" href="#p:{esc(label)}" data-label="{esc(label)}">{html.escape(short_name(paper, label))}</a>'
                      for label, _ in changes)
    return f'<p class="recheck-note">Not re-checked since the paper changed: {links}.  This picture may be out of date.</p>'


# ---------------------------------------------------------------- the paper as it is, or as it was

def current_paper() -> tuple[edition.Paper, Path]:
    import build
    source = build.snapshot(build.sources(), build.ROOT, build.WORK / "src")
    return edition.Paper(source / f"{PAPER}.tex", macros=edition.MACROS, validate_math=False), source


def git(*args: str) -> str:
    result = subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True)
    if result.returncode:
        raise EditionError(f"git {' '.join(args)}: {result.stderr.strip()[:300]}")
    return result.stdout


def paper_at(rev: str) -> edition.Paper:
    with tempfile.TemporaryDirectory() as tmp:
        queue, seen = [f"{PAPER}.tex"], set()
        while queue:
            name = queue.pop()
            if name in seen:
                continue
            seen.add(name)
            text = git("show", f"{rev}:{name}")
            (Path(tmp) / name).parent.mkdir(parents=True, exist_ok=True)
            (Path(tmp) / name).write_text(text)
            queue += [n if Path(n).suffix else n + ".tex" for n in re.findall(r"\\(?:input|include)\{([^}]+)\}", text)]
        return edition.Paper(Path(tmp) / f"{PAPER}.tex", macros=edition.MACROS, validate_math=False)


def word_diff(old: str, new: str, context: int = 6) -> list[str]:
    """The changes between two texts, each with a few words around it: [-removed-]{+added+}."""
    a, b = old.split(), new.split()
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        before, after = " ".join(a[max(i1 - context, 0):i1]), " ".join(a[i2:i2 + context])
        gone = f"[-{' '.join(a[i1:i2])}-]" if i2 > i1 else ""
        came = f"{{+{' '.join(b[j1:j2])}+}}" if j2 > j1 else ""
        out.append(f"  ...{before} {gone}{came} {after}...")
    return out


# ---------------------------------------------------------------- the commands

def setup() -> tuple[dict, None, dict[str, set[str]]]:
    config = media.load_config(media.HERE / "media.toml")
    return config, None, dependencies(config)


def report(stale: dict, lock: dict, total: int) -> list[str]:
    if not stale:
        return [f"All {total} pictures were last compared with the paper as it is now."]
    lines = [f"{len(stale)} of {total} pictures cite, or sit beside, statements that changed since they were last compared with the paper:"]
    for item, changes in stale.items():
        since = lock.get(item, {}).get("at", "never")
        lines.append(f"  {item} (compared with {since}): " + ", ".join(f"{label} ({why})" for label, why in changes))
    return lines


def command_status(args) -> int:
    _, _, deps = setup()
    paper, _ = current_paper()
    lock = read_lock()
    stale = assess(paper, deps, lock)
    print("\n".join(report(stale, lock, len(deps))))
    return 1 if stale else 0


def command_diff(args) -> int:
    _, _, deps = setup()
    if args.picture not in deps:
        raise EditionError(f"{args.picture!r} is not a placed picture; the pictures are: " + ", ".join(deps))
    paper, _ = current_paper()
    lock = read_lock()
    stale = assess(paper, deps, lock).get(args.picture, [])
    at = lock.get(args.picture, {}).get("at")
    if not stale:
        print(f"{args.picture}: nothing it depends on has changed since it was compared with {at or 'the paper'}.")
        return 0
    old = None
    if at and not at.endswith("+worktree"):
        old = paper_at(at)
    else:
        print(f"(the version it was compared with, {at or 'none'}, is not in the history; showing which statements changed)")
    for label, why in stale:
        print(f"{label} ({why}); now {short_name(paper, label)}")
        if old is not None and label in old.labels:
            lines = word_diff(readable(unit_text(old, label)), readable(unit_text(paper, label)))
            print("\n".join(lines) if lines else "  (only spacing, comments, labels, or spellings differ)")
        elif old is not None:
            print("  (not in the version it was compared with)")
    return 0


def command_accept(args) -> int:
    _, _, deps = setup()
    chosen = args.pictures or list(deps)
    unknown = [item for item in chosen if item not in deps]
    if unknown:
        raise EditionError("not placed pictures: " + ", ".join(unknown) + "; the pictures are: " + ", ".join(deps))
    if args.at:
        paper, at = paper_at(args.at), git("rev-parse", "--short", args.at).strip()
    else:
        paper, _ = current_paper()
        dirty = git("status", "--porcelain", "--", f"{PAPER}.tex").strip()
        at = git("rev-parse", "--short", "HEAD").strip() + ("+worktree" if dirty else "")
    lock = {item: entry for item, entry in read_lock().items() if item in deps}
    for item in chosen:
        lock[item] = {"at": at, "statements": {label: fingerprint(paper, label) for label in sorted(deps[item] & set(paper.labels))}}
    write_lock(lock, list(deps))
    print(f"Recorded {len(chosen)} pictures as compared with the paper at {at}: {LOCK.relative_to(ROOT)}")
    return 0


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("status").set_defaults(run=command_status)
    diff = commands.add_parser("diff")
    diff.add_argument("picture")
    diff.set_defaults(run=command_diff)
    accept = commands.add_parser("accept")
    accept.add_argument("pictures", nargs="*")
    accept.add_argument("--at", metavar="COMMIT", help="record the paper as it was at this commit")
    accept.set_defaults(run=command_accept)
    args = parser.parse_args()
    try:
        sys.exit(args.run(args))
    except (EditionError, edition.PaperError) as error:
        print("audit failed: " + str(error), file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
