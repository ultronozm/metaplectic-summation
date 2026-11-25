# Figures

The pictures of the sketches reading, where each goes, and what it shows.  The placements are in [media.toml](media.toml), keyed by the labels that `sketches.tex` targets; the build fails if a figure there is not named here, if its file is missing, or if it is placed under a label that has no sketch.

## What there is

Two static SVG figures, both for F = ℝ and n = 2, drawn in the paper's own terms: the charts U_X (x ≠ 0) and U_Y (y ≠ 0) and the transition relation Φ_X = {x, y}₂ Φ_Y, where {x, y}₂ is −1 exactly when x < 0 and y < 0.  They are made by [figures/make_figures.py](figures/make_figures.py), which first checks numerically what they depict against the paper's definitions and then writes the SVG files.  The files are committed; `make figures` remakes them.

| Sketch (target label) | Figure | Tag | What it shows |
|---|---|---|---|
| `sec:genuine` | `charts` | exact | the charts and the sign {x, y}₂ on their overlap; a point of the torsor followed once around the origin, labelled ζ = ±1 in the chart in use: the label is multiplied by {x, y}₂ at each change of chart, so by −1 once, in the third quadrant; monodromy −1, no section |
| `definition:lines` | `lines` | exact | lines x y′ − y x′ = τ² and, along each, the label read by the integrand of R_X in U_X ({x, −x′}₂) and in U_Y ({x, b y}₂); and the label at the point of tangency as the line turns, which jumps once, where x′ = 0 |

A figure starts closed, as a row with its tag, and opens in place.  Its caption is TeX from `media.toml`, typeset like the sketches, so its references open the paper.

## What is checked

Over a chart the two points of the torsor above v carry the labels ζ = ±1, and a genuine function takes the value ζ Φ_X(v), resp. ζ Φ_Y(v), at them; the point labelled ζ in U_X is labelled {x, y}₂ ζ in U_Y.  Before drawing, `make_figures.py` checks:

- the transition relation `eq:transition-relation` and the smoothness of each chart, for the genuine functions of `lemma:jacquet-surjective` (defined in the charts) and for functions whose support meets the axes;
- that the sign at the four changes of chart around the origin is +1, +1, −1, +1, so that a point returns with the other label (monodromy −1); the crossing in the drawing is placed from these computed signs;
- along lines at 24 angles, that the integrand of `definition:lines` equals {x, −x′}₂ Φ_X and {x, b y}₂ Φ_Y, that each label changes only where its chart ends, and that the integrand is continuous along the line;
- that at the point of tangency the label is +1 in U_Y and {cos α, sin α}₂ in U_X, so that it jumps at α = π (x′ = 0) and nowhere else.

The functions whose support meets the axes are produced, for convenience, from odd functions f on ℂ^× via Φ_Y = f(√z), Φ_X = f({x, y}₂ √z): over ℝ the torsor happens to be the squaring map of ℂ^×.  Nothing drawn depends on this.

## Keeping the figures in step with the paper

`audit.toml` records, for each figure, a fingerprint of each statement it depends on (those its caption cites, those listed under `depends`, and the target of its sketch) as last compared.  When one changes, the build lists the figure and the page marks it *re-check*.  See [README.md](README.md).

## Not done

- The figures are not printed in `sketched.pdf`, whose sketches are text only, as in the effective-nelson-venkatesh edition.
- No figure for p-adic fields or for n ≥ 3, where the torsor has no comparably faithful picture.
