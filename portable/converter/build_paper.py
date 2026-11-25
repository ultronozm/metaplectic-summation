#!/usr/bin/env python3
"""Copied from ~/work/effective-nelson-venkatesh/interactive/scripts/build_paper.py.  Only its Converter class is
used here, by paper.py; the rest describes the effective-nelson-venkatesh repository and is not run.

Convert main.tex into data/paper.json for the interactive reader.

The output is an ordered list of blocks (sections, paragraphs, statements, proofs,
displays), with TeX math left for KaTeX and text converted to HTML.  Numbers come
from build/main.aux, bibliography labels from build/main.bbl.  Run after `make`.
"""
import html
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = Path(__file__).resolve().parents[1] / "data" / "paper.json"

STATEMENTS = ["theorem", "proposition", "lemma", "corollary", "hypothesis", "remark", "example"]

# Text accents and special letters, as in bibliography entries.
ACCENTS = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302", "~": "\u0303", "=": "\u0304", ".": "\u0307"}
LETTERS = {"l": "ł", "L": "Ł", "o": "ø", "O": "Ø", "ss": "ß", "aa": "å", "AA": "Å", "ae": "æ", "oe": "œ", "i": "ı"}


def accents(s):
    """Replace \\"e, \\"{e}, \\'{\\i} and \\l{} by the characters they denote."""
    import unicodedata
    s = re.sub(r"\\(l|L|o|O|ss|aa|AA|ae|oe|i)(?![A-Za-z])(\{\})?\s?", lambda m: LETTERS[m.group(1)], s)
    return re.sub(r"\\([\"'`^~=.])\s*(?:\{([^{}])\}|([A-Za-zıȷ]))",
                  lambda m: unicodedata.normalize("NFC", (m.group(2) or m.group(3)) + ACCENTS[m.group(1)]), s)
DISPLAYS = ["equation", "equation*", "align", "align*"]


def strip_comments(s):
    out = []
    for line in s.split("\n"):
        m = re.search(r"(?<!\\)%", line)
        out.append(line[: m.start()] if m else line)
    return "\n".join(out)


def proofs_aux():
    """Numbers as in the paper with proofs shown: compile a proofs-visible copy of main.tex.

    The author's saved switch in main.tex is left untouched."""
    import subprocess
    build = ROOT / "build"
    tex = ROOT / "main-with-proofs.tex"
    aux = build / "main-with-proofs.aux"
    main = ROOT / "main.tex"
    if aux.exists() and aux.stat().st_mtime > main.stat().st_mtime:
        return aux
    src = main.read_text().replace("\\showproofsfalse", "\\showproofstrue", 1)
    tex.write_text(src)
    try:
        subprocess.run(["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error", "-outdir=build", tex.name],
                       cwd=ROOT, check=True, capture_output=True)
    finally:
        tex.unlink(missing_ok=True)
    return aux


def read_aux():
    labels = {}
    aux = proofs_aux().read_text()
    for m in re.finditer(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{([^}]*)\}", aux):
        labels[m.group(1)] = m.group(2)
    return labels


def read_macros():
    """The paper's own math macros without arguments, from common.tex and the preamble of main.tex.

    \\DeclareMathOperator{\\res}{res} becomes \\operatorname{res}; \\newcommand{\\X}{...} and \\def\\X{...} without
    arguments are taken as written.  The reader adds them to KaTeX's macros, so no list is kept by hand."""
    src = strip_comments((ROOT / "common.tex").read_text()) + "\n" + strip_comments((ROOT / "main.tex").read_text()).split(r"\begin{document}")[0]
    macros = {}
    for m in re.finditer(r"\\DeclareMathOperator(\*?)\{\\([A-Za-z]+)\}\{([^{}]*)\}", src):
        macros["\\" + m.group(2)] = r"\operatorname" + m.group(1) + "{" + m.group(3) + "}"
    for m in re.finditer(r"\\(?:re)?newcommand\*?\{\\([A-Za-z]+)\}(?!\[)\{", src):
        k = find_group(src, m.end() - 1)
        macros.setdefault("\\" + m.group(1), src[m.end():k - 1])
    for m in re.finditer(r"\\def\\([A-Za-z]+)\{", src):
        k = find_group(src, m.end() - 1)
        macros.setdefault("\\" + m.group(1), src[m.end():k - 1])
    return macros


def read_bbl():
    bib = {}
    bbl = (ROOT / "build" / "main-with-proofs.bbl").read_text()
    for m in re.finditer(r"\\bibitem\[(.*?)\]\{([^}]*)\}(.*?)(?=\\bibitem|\\end\{thebibliography\})", bbl, re.S):
        label = re.sub(r"[{}]", "", m.group(1))
        body = accents(re.sub(r"\\newblock\s*", " ", m.group(3)))
        body = re.sub(r"\{\\em\s+([^}]*)\}", r"<em>\1</em>", body)
        body = re.sub(r"\$([^$]*)\$", r'<span class="m">\1</span>', body)
        body = body.replace("~", " ").replace("--", "–")
        body = re.sub(r"[{}]", "", body)
        bib[m.group(2)] = {"label": label, "text": " ".join(body.split())}
    return bib


def find_group(s, i):
    """s[i] == '{'; return index after the matching '}'."""
    depth = 0
    for j in range(i, len(s)):
        if s[j] == "{" and (j == 0 or s[j - 1] != "\\"):
            depth += 1
        elif s[j] == "}" and s[j - 1] != "\\":
            depth -= 1
            if depth == 0:
                return j + 1
    raise ValueError("unbalanced braces")


class Converter:
    def __init__(self, labels, bib):
        self.labels = labels
        self.bib = bib

    def ref(self, key, eq=False):
        num = self.labels.get(key, "??")
        text = f"({num})" if eq else num
        return f'<a class="ref" href="#{html.escape(key)}" data-label="{html.escape(key)}">{text}</a>'

    def cite(self, opt, keys):
        parts = []
        for k in keys.split(","):
            k = k.strip()
            lab = self.bib.get(k, {}).get("label", k)
            parts.append(f'<a class="cite" href="#bib-{k}" data-key="{k}">{lab}</a>')
        inner = ", ".join(parts)
        if opt:
            inner += ", " + self.text(opt)
        return f"[{inner}]"

    def display(self, env, body):
        tags = [self.labels.get(m, "") for m in re.findall(r"\\label\{([^}]*)\}", body)]
        keys = re.findall(r"\\label\{([^}]*)\}", body)
        body = re.sub(r"\\label\{[^}]*\}", "", body).strip()
        if env.startswith("align"):
            body = r"\begin{aligned}" + body + r"\end{aligned}"
        tagtex = ""
        if len(tags) == 1 and tags[0]:
            tagtex = r"\tag{" + tags[0] + "}"
        anchors = "".join(f'<span class="anchor" id="{html.escape(k)}"></span>' for k in keys)
        extra = ""
        if len(tags) > 1:
            extra = f' data-tags="{html.escape(", ".join("(" + t + ")" for t in tags))}"'
        return (f'<div class="display"{extra}>{anchors}<span class="m display">'
                f"{html.escape(body + tagtex)}</span></div>")

    def math(self, s):
        return f'<span class="m">{html.escape(s)}</span>'

    def text(self, s):
        """Convert a TeX text fragment (with math) to HTML."""
        out = []
        i = 0
        n = len(s)
        buf = []

        def flush():
            if buf:
                out.append(self.plain("".join(buf)))
                buf.clear()

        while i < n:
            if s.startswith(r"\[", i):
                j = s.index(r"\]", i)
                flush(); out.append(self.display("equation*", s[i + 2 : j])); i = j + 2; continue
            m = re.match(r"\\begin\{(equation\*?|align\*?)\}", s[i:])
            if m:
                env = m.group(1)
                end = s.index(r"\end{" + env + "}", i)
                flush(); out.append(self.display(env, s[i + m.end() : end])); i = end + len(r"\end{" + env + "}"); continue
            m = re.match(r"\\begin\{(enumerate|itemize)\}(\[[^\]]*\])?", s[i:])
            if m:
                env = m.group(1)
                end = s.index(r"\end{" + env + "}", i)
                items = re.split(r"\\item\s*", s[i + m.end() : end])[1:]
                tag = "ol" if env == "enumerate" else "ul"
                cls = ' class="roman"' if m.group(2) and "i" in m.group(2) else ""
                flush()
                out.append(f"<{tag}{cls}>" + "".join(f"<li>{self.text(it.strip())}</li>" for it in items) + f"</{tag}>")
                i = end + len(r"\end{" + env + "}")
                continue
            m = re.match(r"\\(emph|textbf|textit)\s*\{", s[i:])
            if m:
                k = find_group(s, i + m.end() - 1)
                inner = self.text(s[i + m.end() : k - 1])
                flush(); out.append(f"<b>{inner}</b>" if m.group(1) == "textbf" else f"<em>{inner}</em>")
                i = k
                continue
            if s[i] == "$" and (i == 0 or s[i - 1] != "\\"):
                j = i + 1
                while not (s[j] == "$" and s[j - 1] != "\\"):
                    j += 1
                flush(); out.append(self.math(s[i + 1 : j])); i = j + 1; continue
            buf.append(s[i]); i += 1
        flush()
        return "".join(out)

    def plain(self, s):
        """Text without math: commands, quotes, dashes."""
        res = []
        i = 0
        while i < len(s):
            c = s[i]
            if c == "\\":
                m = re.match(r"\\([a-zA-Z]+)\*?", s[i:])
                if not m:
                    nxt = s[i + 1] if i + 1 < len(s) else ""
                    res.append({"%": "%", "&": "&amp;", "_": "_", "#": "#", "$": "$", ",": "\u2009", " ": " ", "\\": "<br>"}.get(nxt, nxt))
                    i += 2
                    continue
                cmd = m.group(1)
                j = i + m.end()
                opt = None
                if j < len(s) and s[j] == "[" and cmd in ("cite",):
                    k = s.index("]", j)
                    opt = s[j + 1 : k]
                    j = k + 1
                arg = None
                if cmd in ("emph", "textbf", "textit", "ref", "eqref", "cite", "label", "text", "mathrm", "textsc"):
                    while j < len(s) and s[j] == " ":
                        j += 1
                    if j < len(s) and s[j] == "{":
                        k = find_group(s, j)
                        arg = s[j + 1 : k - 1]
                        j = k
                if cmd == "emph" or cmd == "textit":
                    res.append(f"<em>{self.text(arg)}</em>")
                elif cmd == "textbf":
                    res.append(f"<b>{self.text(arg)}</b>")
                elif cmd == "ref":
                    res.append(self.ref(arg))
                elif cmd == "eqref":
                    res.append(self.ref(arg, eq=True))
                elif cmd == "cite":
                    res.append(self.cite(opt, arg))
                elif cmd == "label":
                    res.append(f'<span class="anchor" id="{html.escape(arg)}"></span>')
                elif cmd == "S":
                    res.append("§")
                elif cmd in ("ldots", "dots"):
                    res.append("…")
                elif cmd in ("noindent", "medskip", "smallskip", "bigskip", "par"):
                    pass
                else:
                    res.append(html.escape(arg if arg is not None else ""))
                i = j
                continue
            if s.startswith("---", i):
                res.append("—"); i += 3; continue
            if s.startswith("--", i):
                res.append("–"); i += 2; continue
            if s.startswith("``", i):
                res.append("“"); i += 2; continue
            if s.startswith("''", i):
                res.append("”"); i += 2; continue
            if c == "~":
                res.append("&nbsp;"); i += 1; continue
            if c in "{}":
                i += 1; continue
            res.append(html.escape(c))
            i += 1
        return "".join(res)


def paragraphs(conv, body, offset=0):
    """Split running text into paragraph blocks (displays stay inside paragraphs).

    Each block records its [start, end) offsets in the preprocessed body."""
    blocks = []
    pos = 0
    for chunk in re.split(r"(\n\s*\n)", body):
        start = pos
        pos += len(chunk)
        if chunk.strip() and not re.fullmatch(r"\n\s*\n", chunk):
            blocks.append({"type": "para", "html": conv.text(chunk.strip()), "src": [offset + start, offset + pos]})
    return blocks


def preprocess():
    """Return (title, abstract, body) of main.tex; block offsets refer to `body`."""
    src = strip_comments((ROOT / "main.tex").read_text())
    title = re.search(r"\\title\{([^}]*)\}", src).group(1)
    body = src[src.index(r"\begin{document}") + len(r"\begin{document}") : src.index(r"\end{document}")]
    abstract = re.search(r"\\begin\{abstract\}(.*?)\\end\{abstract\}", body, re.S).group(1)
    body = body[body.index(r"\end{abstract}") + len(r"\end{abstract}") :]
    body = re.sub(r"\\(maketitle|tableofcontents|bibliographystyle\{[^}]*\}|bibliography\{[^}]*\})", "", body)
    # Line-breaking parameters such as \emergencystretch=1em affect only the PDF.
    lb = r"\\(?:emergencystretch|tolerance|pretolerance|hbadness|hfuzz)\s*=?\s*[-+]?[\d.]+\s*(?:pt|em|ex|mm|cm|in|bp|sp)?"
    abstract, body = re.sub(lb, "", abstract), re.sub(lb, "", body)
    return title, abstract, body


def main():
    labels = read_aux()
    bib = read_bbl()
    conv = Converter(labels, bib)
    title, abstract, body = preprocess()

    blocks = [{"type": "abstract", "html": conv.text(abstract.strip())}]
    pattern = re.compile(
        r"\\(section|subsection)\{((?:[^{}]|\{[^{}]*\})*)\}(\\label\{([^}]*)\})?"
        r"|\\begin\{(" + "|".join(STATEMENTS) + r"|proof)\}(\[((?:[^\[\]]|\[[^\]]*\])*)\])?")
    pos = 0
    sec_no = sub_no = 0
    last_statement = None
    for m in pattern.finditer(body):
        if m.start() < pos:
            continue
        blocks += paragraphs(conv, body[pos : m.start()], pos)
        if m.group(1):
            kind, ttl, label = m.group(1), m.group(2), m.group(4)
            if kind == "section":
                sec_no += 1; sub_no = 0
                num = str(sec_no)
            else:
                sub_no += 1
                num = f"{sec_no}.{sub_no}"
            if label and labels.get(label):
                num = labels[label]
            blocks.append({"type": kind, "number": num, "title": conv.text(ttl), "label": label,
                           "id": label or f"sec-{num}"})
            pos = m.end()
            last_statement = None
            continue
        env = m.group(5)
        end_tag = r"\end{" + env + "}"
        end = body.index(end_tag, m.end())
        inner = body[m.end() : end]
        pos = end + len(end_tag)
        if env == "proof":
            blk = {"type": "proof", "paras": [b["html"] for b in paragraphs(conv, inner)], "src": [m.start(), pos]}
            if blocks and blocks[-1] is last_statement and last_statement is not None:
                blk["of"] = last_statement.get("label")
            blocks.append(blk)
            continue
        lm = re.match(r"\s*\\label\{([^}]*)\}", inner)
        label = lm.group(1) if lm else None
        if lm:
            inner = inner[lm.end() :]
        blk = {"type": "statement", "kind": env, "label": label, "id": label,
               "number": labels.get(label, ""), "title": conv.text(m.group(7)) if m.group(7) else "",
               "paras": [b["html"] for b in paragraphs(conv, inner)], "src": [m.start(), pos]}
        blocks.append(blk)
        last_statement = blk
    blocks += paragraphs(conv, body[pos:], pos)

    refs = [{"key": k, **v} for k, v in bib.items()]
    used = set(re.findall(r"\\[A-Za-z]+", body))
    macros = {k: v for k, v in read_macros().items() if k in used}
    OUT.write_text(json.dumps({"title": title, "blocks": blocks, "labels": labels, "bib": refs, "macros": macros}, ensure_ascii=False))
    counts = {}
    for b in blocks:
        counts[b["type"]] = counts.get(b["type"], 0) + 1
    print(f"wrote {OUT} ({OUT.stat().st_size // 1024} KB): {counts}")


if __name__ == "__main__":
    main()
