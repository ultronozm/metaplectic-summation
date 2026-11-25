#!/usr/bin/env python3
"""Keep the paper's links to the Lean formalization current.

The paper cites Lean declarations with \\lean{Decl} (leanblueprint syntax) and
lists them in Appendix C as \\leanentry{Decl}{file}{line}{...}.  This script

  * finds every declaration cited with \\lean or listed with \\leanentry,
  * locates its source line under lean/ (tracking `namespace`/`section` blocks),
  * rewrites the file and line arguments of each \\leanentry,
  * sets \\leancommit to the last commit touching lean/ (with --commit), and
  * fails if a cited declaration is missing from the appendix or from the sources.

Usage: python3 scripts/lean-links.py [--commit] [--check]
  --commit  also update \\leancommit (requires a clean lean/ tree)
  --check   only report; exit 1 if the paper would change
"""
import pathlib, re, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPER = ROOT / 'schwartz-space-n-fold-cover-sl2.tex'
LEAN = ROOT / 'lean'
SOURCES = [LEAN / 'Challenge.lean'] + sorted((LEAN / 'MetaplecticSummation').rglob('*.lean'))

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
    r'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+([^\s:(\[{]+)')


def declarations():
    """Map fully qualified names to (path relative to lean/, line number)."""
    found = {}
    for path in SOURCES:
        stack = []  # entries: list of name components, or None for an unnamed section
        for number, line in enumerate(path.read_text(encoding='utf-8').splitlines(), 1):
            stripped = line.strip()
            m = re.match(r'namespace\s+(\S+)', stripped)
            if m:
                stack.append(('namespace', m.group(1).split('.')))
                continue
            m = re.match(r'(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$', stripped)
            if m:
                stack.append(('section', []))
                continue
            m = re.match(r'end(?:\s+(\S+))?\s*$', stripped)
            if m and stack:
                stack.pop()
                continue
            m = DECL.match(line)
            if m:
                prefix = [c for kind, comps in stack for c in comps]
                name = '.'.join(prefix + [m.group(1)])
                found.setdefault(name, (str(path.relative_to(LEAN)), number))
    return found


COMMENT = re.compile(r'(?<!\\)%.*$')


def code(tex):
    """The text with TeX comments removed."""
    return '\n'.join(COMMENT.sub('', line) for line in tex.splitlines())


def main():
    args = set(sys.argv[1:])
    tex = PAPER.read_text(encoding='utf-8')
    body = code(tex)
    decls = declarations()
    cited = set()
    for group in re.findall(r'\\lean\{([^}]*)\}', body):
        cited.update(name.strip() for name in group.split(',') if name.strip())
    entry = re.compile(r'\\leanentry\{([^}]*)\}\{[^}]*\}\{[^}]*\}')
    listed = set(entry.findall(body))
    errors = []
    for name in sorted(cited - listed):
        errors.append(f'cited with \\lean but not listed in the appendix: {name}')
    for name in sorted(cited | listed):
        if name not in decls:
            errors.append(f'not found under lean/: {name}')
    if errors:
        print('\n'.join(errors), file=sys.stderr)
        sys.exit(1)

    def update(m):
        path, line = decls[m.group(1)]
        return f'\\leanentry{{{m.group(1)}}}{{{path}}}{{{line}}}'

    def update_line(line):
        m = COMMENT.search(line)
        cut = m.start() if m else len(line)
        return entry.sub(update, line[:cut]) + line[cut:]

    new = '\n'.join(update_line(line) for line in tex.split('\n'))
    if '--commit' in args:
        status = subprocess.run(['git', 'status', '--porcelain', '--', 'lean'], cwd=ROOT,
                                capture_output=True, text=True, check=True).stdout
        if status.strip():
            sys.exit('lean/ has uncommitted changes; commit them before pinning \\leancommit')
        sha = subprocess.run(['git', 'log', '-1', '--format=%H', '--', 'lean'], cwd=ROOT,
                             capture_output=True, text=True, check=True).stdout.strip()
        new = re.sub(r'\\newcommand\{\\leancommit\}\{[^}]*\}',
                     lambda _: f'\\newcommand{{\\leancommit}}{{{sha}}}', new)
    if '--check' in args:
        if new != tex:
            sys.exit('the paper\'s Lean links are out of date; run scripts/lean-links.py')
        print(f'{len(cited | listed)} declarations, links current')
        return
    PAPER.write_text(new, encoding='utf-8')
    print(f'{len(cited | listed)} declarations linked')


if __name__ == '__main__':
    main()
