# A Schwartz space for the n-fold cover of SL₂

The paper *A Schwartz space for the n-fold cover of SL₂* (Paul D. Nelson) and
its Lean 4 formalization for number fields.  The site built from this
repository has a landing page (`index.org`) linking the paper (HTML, PDF, TeX)
and a table of the statements checked in Lean.

| Path | Contents |
| --- | --- |
| `schwartz-space-n-fold-cover-sl2.tex` | The paper, with a self-contained preamble.  `refs.bib` holds the cited references. |
| `lean/` | The Lean project: the development (`MetaplecticSummation/`), the statement file `Challenge.lean`, its proof `Solution.lean`, and the Palomar files `comparator.json` and `formalization.yaml`.  See [`lean/README.md`](lean/README.md) for a map of the development. |
| `index.org` | The site's landing page.  Its Lean table is generated; see [Links between paper and Lean](#links-between-paper-and-lean). |
| `preview-site.sh` | Builds the site locally into `_site/`. |
| `scripts/` | `lean-links.py` keeps the paper's links to Lean current; `lean-table.py` writes the landing page's Lean table; `check-site/` checks a served build in headless Chrome. |
| `tex2html-local.el` | Site-specific HTML postprocessing: theorem numbers, citations, tables of contents and tables as in the PDFs. |
| `.github/`, `compile.sh`, `convert.sh`, `make-index.sh`, `tex2html.el`, `tex.css`, `config.json` | Site machinery from [tex-site](https://github.com/ultronozm/tex-site): PDF and HTML builds deployed to GitHub Pages. |
| `Makefile` | `make paper` builds the PDF into `output/pdf/`. |

The paper is kept under a short name rather than its notes-directory name
(`20261118T190000--schwartz-space-n-fold-cover-sl2.tex`), because tex-site
derives the PDF and HTML URLs from the file name.

Work not in the release is kept on branches, not on `main`: informal sketches
of the paper and a portable HTML reader for them on `sketches`, and the main
thread of the paper as four exercise sheets, drafted by AI agents and wired
into the site, on `exercises`.

## Building

### The paper

```sh
latexmk -pdf schwartz-space-n-fold-cover-sl2.tex     # or: make paper
./convert.sh schwartz-space-n-fold-cover-sl2.tex     # HTML, as on the site (pandoc, Emacs)
```

### The site

```sh
./preview-site.sh                                    # build into _site/
python3 -m http.server -d _site 8000                 # serve
node scripts/check-site/check.mjs http://127.0.0.1:8000/   # check in headless Chrome
```

`preview-site.sh` mirrors the CI build (`.github/workflows/build.yml`, then
`make-index.yml`) from `HEAD` plus uncommitted changes to tracked files.  It
checks the paper's Lean links, compiles and converts every document in CI
order, regenerates the Lean table in `index.org` (also in
the working tree: commit it if it changed), and exports the landing page.  It
fails on a failed build, on unresolved references in the LaTeX logs, and on
`??` in the HTML.  It builds into `_site.new/` and swaps it in only at the
end, so a running server keeps serving the previous build meanwhile; logs go
to `_site-logs/`.

The check opens every page linked from the landing page and fails on script
errors, MathJax errors, `??`, and links within the site that do not resolve,
anchors included.  Links leaving the site are counted, not fetched.
Screenshots go to `_site/screenshots/`.

Requirements: TeX Live with `latexmk`, `pandoc`, `jq`, Emacs (29 or later),
Python 3; for the check, Node 22 or later and Chrome.

### The Lean project

Lean v4.35.0-rc2, Mathlib at the `v4.35.0-rc2` tag:

```sh
cd lean
lake exe cache get
lake build                       # development, Challenge and Solution
lake env lean experiments/class-field-theory/MainAudit.lean   # admission and axiom audit
```

To check `Solution` against `Challenge` as Palomar does (Linux with `bwrap`),
use `scripts/verify-comparator.sh` from the
[Palomar starter](https://github.com/PalomarRegistry/PalomarTemplate).  On
macOS, `lake comparator --inadvisably-no-sandbox` with `comparator.json`
(plus the bundled `nanoda_bin` and `con-ron` as `external_kernels`) runs the
same checks without the sandbox.

`lean/Solution.lean` is generated: edit `lean/Challenge.lean` and
`lean/scripts/solution-proofs.lean-fragment`, then run
`lean/scripts/make-solution.py`.

## Status

- The development has no `sorry`.  Every declaration linked from the paper,
  and every theorem compared by Comparator, depends only on `propext`,
  `Classical.choice` and `Quot.sound`.  `Challenge.lean` states Theorem 10.33
  (twisted sums of Gauss sums of order n) and Corollary 10.39 (the quadratic
  dual) against Mathlib alone, for number fields, quantifying over self-dual
  measures and Hilbert symbols with their defining properties and giving the
  local transform by the explicit integral (10.15).  `Solution.lean` proves
  them.  The Poisson formula, Fourier inversion, the archimedean smoothness
  and decay results of §§4, 8 and 10 and the rest are proved in the
  development.  Appendix C of the paper lists what is checked and with which
  hypotheses; `lean/formalization.yaml` records scope, provenance and AI
  involvement.
- Not formalized: global function fields; the remark comparing the transform
  with Kubota's over ℂ; and, at archimedean places, the smoothness across
  μ = 0 of the extensions in Proposition 8.1.
- `lake comparator` accepts the solution with Lean's kernel, NanoDa and
  con-ron (run locally without the sandbox, 2026-11-25).

## Links between paper and Lean

`\lean{Decl}` (the syntax of leanblueprint) after a statement marks its Lean
declaration; use one `\lean` per declaration.  In the PDF the mark links to
the declaration's source line at the commit `\leancommit`; in the HTML version
it links to the declaration's entry in Appendix C, which carries that link.
The repository URL `\leanrepo` and the commit are defined once in the
preamble.  Every declaration cited with `\lean` must also have a
`\leanentry` in Appendix C.  After changing the Lean sources, commit them and
run

```sh
scripts/lean-links.py --commit   # update file and line of each entry; pin \leancommit
scripts/lean-links.py --check    # fail if a link is stale or a name is unknown
./preview-site.sh                # regenerate the Lean table of index.org
```

The table on the landing page is generated from the table of Appendix C by
`scripts/lean-table.py`, between the lines `# lean-table begin` and
`# lean-table end` of `index.org`; do not edit it by hand.

The pinned commit must reach GitHub unchanged (do not squash or rebase the
history before pushing), or be re-pinned afterwards.

## Licence

- The Lean code in `lean/` is licensed under the Apache License 2.0 (`LICENSE`).
- The text of the paper (`schwartz-space-n-fold-cover-sl2.tex` and the files built from it) is licensed under the Creative Commons Attribution 4.0 International licence (`LICENSE-paper.txt`).
- `lean/vendor/ground-theory/` contains 35 modules copied from the Lean archive released with Alpöge's proof of the generalized Riemann hypothesis (https://alpo.ge/remark.pdf), which states no licence; they are included here with credit to that archive and its authors, and remain theirs.  Other vendored code carries the licences in `lean/licenses/`.

## Next steps

- Palomar (submit with project path `lean`): every `.lean` file must use Lean's module system.  The port is not mechanical: a module cannot import a non-module file, and the development imports 14 modules of the pinned dependency `FiniteAbelianGlobalReciprocityv2`, whose import closure is 877 files (about 376,000 lines), of which 18 are modules.  That dependency must be ported first; then the development, `Challenge.lean` and `Solution.lean`, and Comparator rerun.  `Challenge.lean` (398 lines, of which 319 are definitions) still needs a human audit against the paper.
- [Lean Pool](https://github.com/LeanPool/lean-pool) prefers projects already registered in Palomar.
- When the Lean code changes, re-pin the paper's links with `scripts/lean-links.py --commit` and rebuild with `./preview-site.sh`.

## Keeping the parts in sync

The site machinery tracks tex-site:

```sh
git fetch upstream && git merge upstream/main
```

`tex2html.el` here differs from tex-site's: it carries grh-workbook's changes
(cross-document links to the target's own anchor, and the
`tex2html-local.el` hook) and a guard in the toggle-all-proofs script; these
belong upstream.

`lean/` was added with `git subtree add` from the standalone
`MetaplecticSummation` repository and keeps its history.  To take later work
from that repository:

```sh
git subtree pull --prefix=lean <path-to-the-Lean-repository> main
```
