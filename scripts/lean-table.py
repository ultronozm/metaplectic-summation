#!/usr/bin/env python3
"""Write the landing page's table of statements checked in Lean.

The table in index.org, between the lines `# lean-table begin` and
`# lean-table end`, is generated from the table of Appendix C of the paper:
one row per statement, with its number (from the paper's aux file), a link to
the statement in the HTML version, its Lean declarations linked to their
source lines at \\leancommit, and the hypotheses and scope.  Declarations are
located with scripts/lean-links.py.

Usage: python3 scripts/lean-table.py AUXFILE [--check]
  AUXFILE  the aux file of a compiled paper, for the statement numbers
  --check  only report; exit 1 if index.org would change
"""
import importlib.util, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PAPER = ROOT / 'schwartz-space-n-fold-cover-sl2.tex'
HTML = PAPER.with_suffix('.html').name
INDEX = ROOT / 'index.org'
BEGIN, END = '# lean-table begin', '# lean-table end'

spec = importlib.util.spec_from_file_location('lean_links', ROOT / 'scripts' / 'lean-links.py')
lean_links = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lean_links)


def labels(aux):
    """Map labels to their printed numbers."""
    found = {}
    for m in re.finditer(r'\\newlabel\{([^}]*)\}\{\{([^}]*)\}', aux.read_text(encoding='utf-8')):
        found[m.group(1)] = m.group(2)
    return found


def to_org(tex, numbers):
    """Render a short LaTeX fragment of the scope column as Org with MathJax."""
    def ref(m):
        return numbers.get(m.group(2), '??') if m.group(1) == 'ref' else f'({numbers.get(m.group(2), "??")})'
    out = re.sub(r'\\(ref|eqref)\{([^}]*)\}', ref, tex)
    out = out.replace('\\S', '§').replace('~', ' ').replace('\\\\', '').strip()
    return re.sub(r'\s+', ' ', out)


def rows(tex, numbers, decls, repo, commit):
    body = lean_links.code(tex)
    table = body[body.index(r'\label{sec:lean}'):]
    table = table[table.index(r'\hline') + len(r'\hline'):table.index(r'\end{tabular}')]
    result = []
    for row in filter(None, (r.strip() for r in table.split('\\\\\n'))):
        paper, lean, scope = (c.strip() for c in row.rstrip('\\').split(' & '))
        refs = re.findall(r'\\(ref|eqref)\{([^}]*)\}', paper)
        kind = paper.split('~')[0]
        number = ''.join(numbers[l] if k == 'ref' else f'({numbers[l]})' for k, l in refs)
        statement = f'[[file:{HTML}#{refs[-1][1]}][{kind} {number}]]'
        names = re.findall(r'\\leanentry\{([^}]*)\}', lean)
        links = ' '.join(
            f'[[{repo}/blob/{commit}/lean/{decls[n][0]}#L{decls[n][1]}][~{n}~]]' for n in names)
        result.append(f'| {statement} | {links} | {to_org(scope, numbers)} |')
    return result


def main():
    args = sys.argv[1:]
    check = '--check' in args
    aux = [a for a in args if a != '--check']
    if len(aux) != 1:
        sys.exit(__doc__)
    tex = PAPER.read_text(encoding='utf-8')
    repo = re.search(r'\\newcommand\{\\leanrepo\}\{([^}]*)\}', tex).group(1)
    commit = re.search(r'\\newcommand\{\\leancommit\}\{([^}]*)\}', tex).group(1)
    lines = ['| Paper | Lean | Hypotheses and scope |', '|-', *rows(tex, labels(pathlib.Path(aux[0])),
                                                               lean_links.declarations(), repo, commit)]
    index = INDEX.read_text(encoding='utf-8')
    head, rest = index.split(BEGIN + '\n')
    _, tail = rest.split(END + '\n')
    new = head + BEGIN + '\n' + '\n'.join(lines) + '\n' + END + '\n' + tail
    if check:
        if new != index:
            sys.exit('the Lean table in index.org is out of date; run ./preview-site.sh')
        print('Lean table current')
        return
    INDEX.write_text(new, encoding='utf-8')
    print(f'Lean table: {len(lines) - 2} statements')


if __name__ == '__main__':
    main()
