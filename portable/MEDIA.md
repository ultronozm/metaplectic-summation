# Figures

The pictures of the sketches reading, where each goes, and what it shows.  The placements are in [media.toml](media.toml), keyed by the labels that `sketches.tex` targets; the build fails if a figure there is not named here, if its file is missing, or if it is placed under a label that has no sketch.

## What there is

Two static SVG figures, both for F = ℝ and n = 2, the one case in which Deligne's torsor can be drawn faithfully.  They are made by [figures/make_figures.py](figures/make_figures.py), which first checks numerically the model they depict against the paper's definitions and then writes the SVG files.  The files are committed; `make figures` remakes them.

| Sketch (target label) | Figure | Tag | What it shows |
|---|---|---|---|
| `sec:genuine` | `double-cover` | exact | the torsor over the circle of directions of v, drawn as a curve in the torus of pairs (arg v, arg w): once around the base, a point returns on the other sheet, so the torsor has no section over the punctured plane |
| `definition:lines` | `lines` | exact | four lines x y′ − y x′ = τ² turning about the origin, and their preimages under w ↦ w², with the branch whose values the integrand of R_X reads: the branch is continuous along each line, but jumps once as the line turns, where x′ = 0 |

A figure starts closed, as a row with its tag, and opens in place.  Its caption is TeX from `media.toml`, typeset like the sketches, so its references open the paper.

## The model, and what is checked

For F = ℝ and n = 2, the Hilbert symbol {x, y}₂ is −1 exactly when x < 0 and y < 0.  Write z = x + iy and √z for the principal square root.  For a smooth odd function f on ℂ^×, the pair Φ_Y(v) = f(√z), Φ_X(v) = f({x, y}₂ √z) is a genuine function, and every genuine function arises so: the torsor is the double cover w ↦ w².  This model is not in the paper.  Before drawing, `make_figures.py` checks:

- the transition relation `eq:transition-relation` for the model, at random points, and the continuity of each chart across the half-axis where the principal root jumps;
- that the cocycle {x, y}₂ has monodromy −1 around the origin, so that the cover is connected;
- along lines at 24 angles, that the integrand of `definition:lines`, Φ_X(x, (x y′ − τ²)/x′) {x, −x′}₂, equals f(σ(z)) with σ(z) = {x, b y}₂ √z and (a, b) = (y′, −x′); that σ(z)² = z, so that σ lies on the hyperbola Re((a − ib) w²) = τ²; that σ is continuous along the line; and that σ is the principal root where the line meets the y-axis;
- that, for the line tangent to the unit circle at e^{iα}, the chosen lift of the point of tangency is e^{iα/2} for α in (−π, π), so that the choice jumps from i to −i where the line becomes x = −1, and nowhere else.

The drawings are computed from the same functions, so what is drawn is what is checked.  The colours (green where σ = √z, blue where σ = −√z, and on the torus the sheet of √z or of −√z) are read off from the model, not drawn by hand.

## Keeping the figures in step with the paper

`audit.toml` records, for each figure, a fingerprint of each statement it depends on (those its caption cites, those listed under `depends`, and the target of its sketch) as last compared.  When one changes, the build lists the figure and the page marks it *re-check*.  See [README.md](README.md).

## Not done

- The figures are not printed in `sketched.pdf`, whose sketches are text only, as in the effective-nelson-venkatesh edition.
- No figure for p-adic fields or for n ≥ 3, where the torsor has no comparably faithful picture.
