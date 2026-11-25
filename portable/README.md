# The portable HTML edition

One HTML file that reads the sketches of the paper in the order of their targets, with the paper's precise text one click away and the figures under the sketches they illustrate.  It needs nothing but a web browser: no server, no network, no Python, Node, or TeX.

The informal prose is [sketches.tex](../sketches.tex) and the rigorous text is [schwartz-space-n-fold-cover-sl2.tex](../schwartz-space-n-fold-cover-sl2.tex).  Neither is copied by hand into the page; the page is generated from them.  The reader is that of `~/work/effective-nelson-venkatesh/portable`, adapted to this paper; it is not the tex-site HTML of the paper (`convert.sh`), which is unchanged.

## Open it

Double-click `output/html/metaplectic-sketches.html` (or open it from a browser's File menu).  It works from disk, offline.  **Paper** beside a sketch opens the paper's text at that unit, beside the sketch in a wide window and over it in a narrow one.  Esc closes the paper and returns you to your place in the sketches; so do ✕, the Back button of the browser, and, from the paper, the Sketch tab beside a unit that has a sketch.  **Lean** beside a statement that the paper marks with `\lean{...}` opens its row in the appendix on Lean, which links to the declaration's source at the pinned commit; the paper's own small Lean marks link there too.

## Share it

Copy `output/html/metaplectic-sketches.html` (in `output/`, which Git ignores) and send or attach it.  The recipient downloads the file and double-clicks it.  It is about 1.3 MB, most of it KaTeX and its fonts.  Nothing is uploaded or published by the build.  The links to the Lean sources point at `\leanrepo` on GitHub, so they work once the repository is published (see the main README).

## Build it

From the repository root:

    make html                 # or: python3 portable/build.py

This writes `output/html/metaplectic-sketches.html`, the same for the same sources.  It needs Python 3.11 or later (for `tomllib`; set `PYTHON=python3.14` or similar if `python3` is older), Node, for checking the formulas with the vendored KaTeX, and TeX, for the paper's own numbers.  The build copies the paper, `refs.bib`, and `sketches.tex` into `build/portable/src/` under a name made from their content, runs `latexmk` on that copy once, and builds from the copy, so the text, the numbers, and the checks of one build describe the same bytes.  Nothing tracked changes.

The build fails, with a message that names the source, instead of dropping anything: a sketch whose target label the paper lacks, a second sketch of one unit, a reference with no target, a formula KaTeX cannot typeset, a figure that is not named in [MEDIA.md](MEDIA.md) or whose file is missing, a statement number written by hand in this README, in `MEDIA.md`, or in `media.toml` (the numbers are the paper's and change with it, so a unit is named by its label), and any word or formula of `sketches.tex`, of a caption, or of the paper that is not in the page.

## Check it

    make check-html           # or: node portable/check/check.mjs

This opens the built file from disk in headless Chrome (set `CHROME` to its path if it is not in the usual place), with the network switched off, and checks: the file is self-contained; every sketch of `sketches.tex` is present, in the order of the paper; every link has a target; no script error and no request; all formulas typeset; every reference in a sketch opens its target in the paper and Esc returns to the same place; Back, Forward, and the Sketch tab; every Lean link opens a row of the appendix, and that row links to the source; every section of the paper is reachable; every fold (figures and proofs) opens and shows its content; and nothing overflows at 1440×900, 1280×720, 760×900, and 390×844.  Screenshots go to `build/portable/check/`.

## How it is put together

| | |
|---|---|
| `build.py` | the build command |
| `edition.py` | reads `sketches.tex`, places each sketch by the position of its target in the paper, and renders both through `converter/paper.py` |
| `converter/` | the TeX-to-HTML converter of the effective-nelson-venkatesh readers (`paper.py`, `build_paper.py`), with additions for this paper listed in its docstring: `multline`, `tabular`, `\lean`, `\leanentry`, and amsart front matter |
| `media.toml`, `media.py`, `figures/` | which figure goes under which sketch, by target label; the figures and the script that checks and draws them |
| `audit.py`, `audit.toml` | which figures may have fallen behind the paper |
| `src/reader.js`, `src/reader.css`, `src/template.html` | the reader |
| `check/` | the browser check |
| `vendor/katex/`, `licenses/` | KaTeX (MIT) with its fonts (SIL OFL 1.1), also shown in the page under About |

The reading follows the documented semantics of the [sketches package](/Users/au710211/work/sketches): the sketch of the whole paper first; then, in the order of the paper, each section's heading and its sketches; a section's subsections are listed when one of them contains a sketch, and a unit without a sketch appears as a heading marked *no sketch*.  A reference in a sketch or in the paper opens its target in the paper; the paper itself is in the page once.

## Keeping the figures in step with the paper

The drawings and captions of the figures are not generated from the paper, so they can fall behind it.  [audit.toml](audit.toml) records a fingerprint of each statement a figure depends on, as the figure was last compared with it (whitespace, comments, `\label`, emphasis, and spellings that mean the same do not count, and a statement is taken without its proof).  When one changes, the build lists the figure and the page marks it *re-check*, with a note that links to the statements.  Nothing fails; `build.py --require-audited` fails, for a build about to be shared.

    python3 portable/audit.py status           # which figures are out of date, and why (also: make audit-html)
    python3 portable/audit.py diff lines       # what changed in what it depends on, word by word
    python3 portable/audit.py accept lines     # record the paper as it is, after the figure has been checked
    python3 portable/audit.py accept           # ... for every figure

## Limitations

- Tested in headless Chrome on macOS.  Other browsers are untested; the page uses only features that browsers have had since 2021.
- The page typesets formulas with KaTeX, so their typography differs from the PDF's.  The text, numbering, and macros are the paper's.  KaTeX has no `\sideset`, so the restricted tensor product is shown as `\bigotimes'`.
- Sketches written inside the paper (rather than in a file beside it) and `sketch*` are not supported; the build refuses them.
- Find in page searches the paper's text only while the paper is open.
- The PDF made by `sketched.tex` (`make sketched`) remains the form for printing; it has no figures.
