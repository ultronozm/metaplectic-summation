# A Schwartz space for the n-fold cover of SL₂

The paper *A Schwartz space for the n-fold cover of SL₂* (Paul D. Nelson) and
its Lean 4 formalization.

| Path | Contents |
| --- | --- |
| `schwartz-space-n-fold-cover-sl2.tex` | The paper, with a self-contained preamble.  `refs.bib` holds the cited references. |
| `lean/` | The Lean project: the development (`MetaplecticSummation/`), the statement file `Challenge.lean`, its proof `Solution.lean`, and the Palomar files `comparator.json` and `formalization.yaml`.  See [`lean/README.md`](lean/README.md) for a map of the development. |
| `scripts/lean-links.py` | Keeps the paper's links to Lean declarations current. |
| `Makefile` | `make paper` builds the PDF into `output/pdf/`. |
| `.github/`, `*.sh`, `tex2html.el`, `index.org`, `tex.css`, `config.json` | Site machinery from [tex-site](https://github.com/ultronozm/tex-site): PDF and HTML builds deployed to GitHub Pages. |

The paper is kept under a short name rather than its notes-directory name
(`20261118T190000--schwartz-space-n-fold-cover-sl2.tex`), because tex-site
derives the PDF and HTML URLs from the file name.

## Building

Paper:

```sh
latexmk -pdf schwartz-space-n-fold-cover-sl2.tex
./convert.sh schwartz-space-n-fold-cover-sl2.tex   # HTML, as on the site
```

Lean (Lean v4.35.0-rc2, Mathlib at the `v4.35.0-rc2` tag):

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

- The development has no `sorry`.  `Challenge.lean` states Theorem 10.33
  (twisted sums of Gauss sums of order n) and Corollary 10.39 (the quadratic
  dual) against Mathlib alone, for number fields, quantifying over self-dual
  measures and Hilbert symbols with their defining properties and giving the
  local transform by the explicit integral (10.15).  `Solution.lean` proves
  them, and every compared theorem depends only on `propext`,
  `Classical.choice` and `Quot.sound`.  The Poisson formula, Theorem 7.1 and
  the rest are proved in the development (Appendix C of the paper).
- `lake comparator` accepts the solution with Lean's kernel, NanoDa and
  con-ron (run locally without the sandbox, 2026-11-25).
- Appendix C of the paper lists what is checked and with which hypotheses;
  `lean/formalization.yaml` records scope, provenance and AI involvement.

## Links between paper and Lean

`\lean{Decl}` (the syntax of leanblueprint) after a statement marks its Lean
declaration.  In the PDF the mark links to the declaration's source line at
the commit `\leancommit`; in the HTML version it links to the declaration's
entry in Appendix C, which carries that link.  The repository URL
`\leanrepo` and the commit are defined once in the preamble.  After changing
the Lean sources, commit them and run

```sh
scripts/lean-links.py --commit   # update file and line of each entry; pin \leancommit
scripts/lean-links.py --check    # fail if a link is stale or a name is unknown
```

The pinned commit must reach GitHub unchanged (do not squash or rebase the
history before pushing), or be re-pinned afterwards.

## Before publishing

- Create the GitHub repository and check `\leanrepo` in the paper and
  `site.githubRepository` in `config.json` (both assume
  `ultronozm/metaplectic-summation`).
- Palomar (submit with project path `lean`):
  - Every `.lean` file in the repository must use Lean's module system.  None
    of the 295 files does yet, and the port is not mechanical: a module cannot
    import a non-module file, and the development imports 14 modules of the
    pinned dependency `FiniteAbelianGlobalReciprocityv2`, whose import closure
    is 877 files (about 376,000 lines) of which 18 are modules.  The
    dependency (or that closure, vendored) must be ported first; then the
    development, `Challenge.lean` and `Solution.lean` (`module`,
    `public import`, `@[expose] public section`, and the 160 files with
    `private` declarations checked), and Comparator rerun.  `Challenge.lean`
    imports only Mathlib, so its own port is mechanical.
  - Add a root `LICENSE` matching `project.license` in
    `lean/formalization.yaml` (Apache-2.0 there; the vendored code is
    Apache-2.0, see `lean/licenses/`).
  - Audit `Challenge.lean` (398 lines, of which 319 are definitions; Palomar
    prefers at most 300) and update `review.status` and the automation details in
    `formalization.yaml`.
- [Lean Pool](https://github.com/LeanPool/lean-pool) prefers projects already
  registered in Palomar.

## Keeping the parts in sync

The site machinery tracks tex-site:

```sh
git fetch upstream && git merge upstream/main
```

`lean/` was added with `git subtree add` from the standalone
`MetaplecticSummation` repository and keeps its history.  To take later work
from that repository:

```sh
git subtree pull --prefix=lean ~/work/lean/MetaplecticSummation main
```
