#!/usr/bin/env python3
"""Draw the figures of the sketches, after checking what they depict against the paper's definitions.

    python3 portable/figures/make_figures.py      # writes charts.svg and lines.svg beside this file

Both figures are for F = R and n = 2, in the paper's own terms: the charts U_X (x != 0) and U_Y (y != 0), on each
of which Deligne's torsor is trivial, glued by the transition relation (eq:transition-relation)

    Phi_X(x, y) = {x, y}_2 Phi_Y(x, y),        {x, y}_2 = -1 exactly when x < 0 and y < 0.

Over a chart, the two points of the torsor above v carry the labels zeta = +1 and -1, and a genuine function takes
the value zeta Phi_X(v), resp. zeta Phi_Y(v), there.  The point labelled zeta in U_X is labelled {x, y}_2 zeta in U_Y.

charts.svg follows a point once around the origin through the four arcs of the charts; the labels cross exactly where
{x, y}_2 = -1, so the monodromy is -1.  lines.svg shows, along lines x y' - y x' = tau^2, the label read by the
integrand of R_X (Definition definition:lines) in each chart, and at the point of tangency as the line turns.

The checks use genuine functions of two kinds: that of Lemma lemma:jacquet-surjective, defined in the charts, and,
for functions whose support meets the axes, odd functions f on C^x through Phi_Y = f(sqrt z), Phi_X = f({x, y}_2 sqrt z)
with the principal root.  The second kind is a convenience of the real case (there the torsor happens to be the
squaring map of C^x); nothing drawn depends on it.

Nothing here is imported by the build; the SVG files are committed, and the build checks that they exist.
"""
from __future__ import annotations

import cmath
import html
import math
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent

# ---------------------------------------------------------------- the definitions, and the checks


def hilbert2(x: float, y: float) -> int:
    """The real quadratic Hilbert symbol {x, y}_2."""
    return -1 if x < 0 and y < 0 else 1


def bump(t: float, lo: float, hi: float) -> float:
    if not lo < t < hi:
        return 0.0
    s = (t - lo) / (hi - lo)
    return math.exp(-1 / (s * (1 - s)))


def lemma_genuine():
    """Lemma lemma:jacquet-surjective: Phi_X = |x|^-1 W(x) beta(y/x), Phi_Y = {y, x}_2 Phi_X, Phi_Y(0, y) = 0."""
    W = lambda x: bump(x, 0.3, 1.7) - 0.6 * bump(x, -2.0, -0.4)  # noqa: E731  (in C_c^infty(R^x))
    beta = lambda u: bump(u, -1.5, 2.0)  # noqa: E731

    def phi_x(x, y):
        assert x != 0
        return W(x) * beta(y / x) / abs(x)

    def phi_y(x, y):
        assert y != 0
        return 0.0 if x == 0 else hilbert2(y, x) * phi_x(x, y)
    return phi_x, phi_y


def model_genuine(seed: int):
    """A genuine function whose support meets both axes: f odd on C^x, read through the principal square root."""
    rng = random.Random(seed)
    coeffs = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(6)]

    def f(w: complex) -> complex:
        z = w * w
        poly = sum(c * z ** k * z.conjugate() ** j for (k, j), c in zip([(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)], coeffs))
        return w * poly * math.exp(-abs(z))

    def phi_x(x, y):
        assert x != 0
        return f(hilbert2(x, y) * cmath.sqrt(complex(x, y)))

    def phi_y(x, y):
        assert y != 0
        return f(cmath.sqrt(complex(x, y)))
    return phi_x, phi_y


def check_transition() -> None:
    """The transition relation, and the smoothness of each chart on its whole domain, for both kinds of function."""
    rng = random.Random(1)
    for phi_x, phi_y in (lemma_genuine(), model_genuine(7)):
        for _ in range(4000):
            x, y = rng.uniform(-3, 3), rng.uniform(-3, 3)
            if abs(x) < 1e-9 or abs(y) < 1e-9:
                continue
            assert abs(phi_x(x, y) - hilbert2(x, y) * phi_y(x, y)) < 1e-12
        for x in (-2.0, -0.7, -0.1, 0.4, 1.3):       # Phi_X across y = 0, inside U_X
            assert abs(phi_x(x, 1e-9) - phi_x(x, -1e-9)) < 1e-6
        for y in (-2.0, -0.3, 0.4, 1.5):              # Phi_Y across x = 0, inside U_Y
            assert abs(phi_y(-1e-9, y) - phi_y(1e-9, y)) < 1e-6


# The arcs of the circle around the origin on which a chart is used, and the angles in the quadrants where one passes
# from a chart to the next.  Any angle in a quadrant would do: the sign is constant on each quadrant.
ARCS = [("X", -45, 45), ("Y", 45, 135), ("X", 135, 225), ("Y", 225, 315)]


def switch_signs() -> list[tuple[int, int]]:
    """(angle, {x, y}_2) at each change of chart, in degrees."""
    out = []
    for _, _, end in ARCS:
        t = math.radians(end)
        out.append((end, hilbert2(math.cos(t), math.sin(t))))
    return out


def follow_once_around() -> list[int]:
    """The label of a point followed counterclockwise from zeta_X = +1 at angle 0, after each change of chart."""
    zeta, labels = 1, [1]
    for _, sign in switch_signs():
        zeta *= sign   # zeta_Y = {x, y} zeta_X and zeta_X = {x, y} zeta_Y: the sign is its own inverse
        labels.append(zeta)
    return labels


def check_monodromy() -> None:
    signs = [s for _, s in switch_signs()]
    assert signs == [1, 1, -1, 1], signs          # only the change in the third quadrant has sign -1
    assert follow_once_around()[-1] == -1          # back at angle 0 in U_X, with the other label


def line_point(a: float, b: float, t: float, s: float) -> tuple[float, float]:
    """The point of a x + b y = t, for (a, b) of length one, at signed distance s from the foot (t a, t b)."""
    return t * a - b * s, t * b + a * s


def label_x(x: float, xp: float) -> int:
    """The label in U_X read by the integrand of R_X: the factor {x, -x'}_2 in Definition definition:lines."""
    return hilbert2(x, -xp)


def label_y(x: float, y: float, b: float) -> int:
    """The same point's label in U_Y: {x, -x'}_2 {x, y}_2 = {x, b y}_2, since b = -x'."""
    return hilbert2(x, b * y)


def check_lines() -> None:
    for phi_x, phi_y in (lemma_genuine(), model_genuine(11)):
        for alpha in [k * math.pi / 12 + 0.01 for k in range(24)]:
            tau = 0.8
            t = tau ** 2
            a, b = math.cos(alpha), math.sin(alpha)          # (a, b) = (y', -x')
            xp, yp = -b, a
            previous = None
            for k in range(-3000, 3001):
                s = k / 500
                x, y = line_point(a, b, t, s)
                assert abs(x * yp - y * xp - t) < 1e-9      # the point is on the line x y' - y x' = tau^2
                if abs(x) < 1e-9 or abs(y) < 1e-9:
                    continue
                # the paper's integrand, with y = (x y' - tau^2) / x'
                integrand = phi_x(x, (x * yp - t) / xp) * hilbert2(x, -xp)
                assert abs(integrand - label_x(x, xp) * phi_x(x, y)) < 1e-9
                assert abs(integrand - label_y(x, y, b) * phi_y(x, y)) < 1e-9
                # each label changes only where its chart ends
                if previous is not None:
                    px, py, lx, ly = previous
                    if (px > 0) == (x > 0):
                        assert lx == label_x(x, xp)
                    if (py > 0) == (y > 0):
                        assert ly == label_y(x, y, b)
                    # the integrand is continuous along the line, also across the axes
                    assert abs(integrand - previous_value) < 0.05, (alpha, s)
                previous, previous_value = (x, y, label_x(x, xp), label_y(x, y, b)), integrand
    # At the point of tangency (cos alpha, sin alpha) of a x + b y = 1: the label is +1 in U_Y off the x-axis, and
    # {cos alpha, sin alpha}_2 in U_X off the y-axis; so it jumps at alpha = pi (x' = 0) and nowhere else.
    for k in range(720):
        alpha = math.radians(k / 2)
        x, y = math.cos(alpha), math.sin(alpha)
        if abs(y) > 1e-9:
            assert label_y(x, y, y) == 1
        if abs(x) > 1e-9:
            assert label_x(x, -y) == hilbert2(x, y)
    below, above = math.pi - 1e-3, math.pi + 1e-3
    assert label_x(math.cos(below), -math.sin(below)) == 1 and label_x(math.cos(above), -math.sin(above)) == -1
    assert label_x(math.cos(1e-3), -math.sin(1e-3)) == label_x(math.cos(-1e-3), -math.sin(-1e-3)) == 1


# ---------------------------------------------------------------- SVG helpers

INK, MUTED, GREEN, BLUE, RED, GRID = "#25332b", "#6b766f", "#1f7a4d", "#2f5d9e", "#b23a2a", "#c9d1cb"
XCOL, YCOL = "#8a5a1f", "#6b4c9a"                       # the charts U_X and U_Y
LABEL_COLOR = {1: GREEN, -1: BLUE}


def fmt(value: float) -> str:
    return f"{value:.2f}".rstrip("0").rstrip(".") if abs(value) > 1e-9 else "0"


def polyline(points, **style) -> str:
    attrs = " ".join(f'{k.replace("_", "-")}="{v}"' for k, v in style.items())
    return f'<polyline fill="none" points="{" ".join(fmt(x) + "," + fmt(y) for x, y in points)}" {attrs}/>'


def text(x, y, body, size=13, anchor="middle", fill=INK, italic=False, weight="normal") -> str:
    style = ' font-style="italic"' if italic else ""
    return (f'<text x="{fmt(x)}" y="{fmt(y)}" font-size="{size}" text-anchor="{anchor}" fill="{fill}"'
            f' font-weight="{weight}"{style}>{html.escape(body, quote=False)}</text>')


def svg(width, height, body, title) -> str:
    return (f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {width} {height}" width="{width}" height="{height}"'
            f' font-family="Iowan Old Style, Palatino, Georgia, serif" role="img" aria-label="{html.escape(title)}">\n'
            f"<title>{html.escape(title)}</title>\n{body}\n</svg>\n")


def runs(points, keep):
    """Split a sampled curve into maximal runs on which keep(i) is constant: [(flag, [points])]."""
    out = []
    for i, p in enumerate(points):
        flag = keep(i)
        if not out or out[-1][0] != flag:
            out.append((flag, [p] if not out else [out[-1][1][-1], p]))
        else:
            out[-1][1].append(p)
    return out


def arrow_defs(color=MUTED) -> str:
    return (f'<defs><marker id="arrow" viewBox="0 0 10 10" refX="8" refY="5" markerUnits="userSpaceOnUse" markerWidth="12" markerHeight="12" orient="auto">'
            f'<path d="M0,0 L10,5 L0,10 z" fill="{color}"/></marker></defs>')


# ---------------------------------------------------------------- figure 1: the charts and the monodromy

def figure_charts() -> str:
    parts = [text(18, 24, "The torsor over a circle around the origin, in the charts U_X and U_Y", 13.5, "start", INK, weight="600")]
    # --- the plane, with the charts and the sign on their overlap
    px, py, half = 150, 210, 105
    parts.append(text(px, 62, "the charts, and {x, y}₂ on U_X ∩ U_Y", 12, "middle", MUTED))
    for (qx, qy), sx, sy in [((1, -1), 1, 1), ((-1, -1), -1, 1), ((-1, 1), -1, -1), ((1, 1), 1, -1)]:
        x0 = px if qx > 0 else px - half
        y0 = py if qy > 0 else py - half
        sign = hilbert2(sx, sy)
        parts.append(f'<rect x="{x0}" y="{y0}" width="{half}" height="{half}" fill="{RED if sign < 0 else "#ffffff"}" opacity="{0.12 if sign < 0 else 0}" stroke="{GRID}"/>')
        parts.append(text(px + qx * half / 2, py + qy * half / 2 + 5, f"{'+1' if sign > 0 else '−1'}", 16, "middle", RED if sign < 0 else INK))
    parts.append(f'<line x1="{px}" y1="{py - half}" x2="{px}" y2="{py + half}" stroke="{XCOL}" stroke-width="3" stroke-dasharray="2 4"/>')
    parts.append(f'<line x1="{px - half}" y1="{py}" x2="{px + half}" y2="{py}" stroke="{YCOL}" stroke-width="3" stroke-dasharray="2 4"/>')
    parts.append(f'<circle cx="{px}" cy="{py}" r="4" fill="#fff" stroke="{INK}"/>')
    parts.append(text(px + 6, py - half - 8, "x = 0: not in U_X", 11.5, "middle", XCOL))
    parts.append(text(px - half, py - 8, "y = 0: not in U_Y", 11.5, "start", YCOL))
    # --- the ring: a point followed once around, labelled in the chart in use
    cx, cy, r_out, r_in = 520, 230, 135, 98
    sign_at = dict(switch_signs())
    window = 14  # degrees over which the tracks pass from one chart to the next

    def at(radius, degrees):
        t = math.radians(degrees)
        return cx + radius * math.cos(t), cy - radius * math.sin(t)

    def arc(radius, d0, d1, steps=60):
        return [at(radius, d0 + (d1 - d0) * k / steps) for k in range(steps + 1)]

    labels = follow_once_around()
    for index, (chart, d0, d1) in enumerate(ARCS):
        color = XCOL if chart == "X" else YCOL
        for radius in (r_out, r_in):
            parts.append(polyline(arc(radius, d0 + window / 2, d1 - window / 2), stroke=color, stroke_width="2.2", opacity="0.55"))
        mid = (d0 + d1) / 2
        name = {("X", 0): "U_X, x > 0", ("Y", 90): "U_Y, y > 0", ("X", 180): "U_X, x < 0", ("Y", 270): "U_Y, y < 0"}[(chart, int(mid) % 360)]
        lx, ly = at(r_out + 16, mid)
        anchor = {0: "start", 90: "middle", 180: "end", 270: "middle"}[int(mid) % 360]
        dy = {0: 52, 90: -4, 180: 4, 270: 14}[int(mid) % 360]
        parts.append(text(lx, ly + dy, name, 12, anchor, color, weight="600"))
    for degrees, sign in sign_at.items():
        a0, a1 = degrees - window / 2, degrees + window / 2
        if sign > 0:
            for radius in (r_out, r_in):
                parts.append(polyline(arc(radius, a0, a1, 12), stroke=MUTED, stroke_width="2.2", opacity="0.55"))
        else:
            for start, end in ((r_out, r_in), (r_in, r_out)):
                pts = [at(start + (end - start) * (1 - math.cos(math.pi * k / 24)) / 2, a0 + (a1 - a0) * k / 24) for k in range(25)]
                parts.append(polyline(pts, stroke=RED, stroke_width="2.2"))
        tx, ty = at(r_in - 30, degrees)
        parts.append(text(tx, ty + 4, f"{'+1' if sign > 0 else '−1'}", 12.5, "middle", RED if sign < 0 else MUTED, weight="600"))
    parts.append(text(cx - 20, cy - 4, "{x, y}₂ at each", 11, "middle", MUTED))
    parts.append(text(cx - 20, cy + 10, "change of chart", 11, "middle", MUTED))
    # the path of one point, starting outside (label +1 in U_X) at angle 0
    path, radius = [], r_out
    for index, (chart, d0, d1) in enumerate(ARCS):
        radius = r_out if labels[index] > 0 else r_in
        start = 0 if index == 0 else d0 + window / 2
        path += arc(radius, start, d1 - window / 2, 40)
        nxt = r_out if labels[index + 1] > 0 else r_in
        a0, a1 = d1 - window / 2, d1 + window / 2
        path += [at(radius + (nxt - radius) * (1 - math.cos(math.pi * k / 24)) / 2, a0 + (a1 - a0) * k / 24) for k in range(25)]
    end_radius = r_out if labels[-1] > 0 else r_in
    path += arc(end_radius, 315 + window / 2, 360, 20)
    parts.append(polyline(path, stroke=INK, stroke_width="3.2", stroke_linecap="round", opacity="0.85", marker_end="url(#arrow)"))
    for radius, label, dy in [(r_out, "start: ζ_X = +1 (outer)", -10), (end_radius, f"end: ζ_X = {'+1' if labels[-1] > 0 else '−1'} (inner)", 12)]:
        x, y = at(radius, 0)
        parts.append(f'<circle cx="{fmt(x)}" cy="{fmt(y)}" r="4.5" fill="{INK}"/>')
        parts.append(text(cx + r_out + 10, cy + dy, label, 12.5, "start", INK, weight="600"))
    # legend
    y0 = 440
    parts.append(text(18, y0, "On each arc, the outer track is the label ζ = +1 and the inner track ζ = −1, in the chart in use.", 12, "start"))
    parts.append(text(18, y0 + 18, "Passing to the next chart multiplies the label by {x, y}₂: the tracks continue where it is +1 and cross", 12, "start"))
    parts.append(text(18, y0 + 36, "where it is −1, in the third quadrant.  Once around, a point returns with the other label: monodromy −1.", 12, "start"))
    return svg(820, y0 + 52, arrow_defs(INK) + "\n" + "\n".join(parts), "Deligne's torsor for n = 2 over the real numbers, in its two charts")


# ---------------------------------------------------------------- figure 2: lines

def figure_lines() -> str:
    # (a, b) = (cos alpha, sin alpha) = (y', -x'); the line a x + b y = 1 is tangent to the unit circle at (a, b)
    panels = [(math.pi / 4, "α = π/4"), (3 * math.pi / 4, "α = 3π/4"), (math.pi - 0.18, "α just below π"), (math.pi + 0.18, "α just above π")]
    width, panel_w, top, z_h = 760, 182, 70, 190
    scale = 32
    parts = [text(14, 24, "The label read by the integrand of R_X along lines a x + b y = τ² (here τ² = 1, (a, b) = (cos α, sin α))", 13.5, "start", INK, weight="600")]
    parts.append(text(14, 44, "Along each line: outer strip, its label in U_X, {x, −x′}₂; inner strip, its label in U_Y, {x, b y}₂.  Each has a gap where its chart ends.", 11.5, "start", MUTED))
    for index, (alpha, label) in enumerate(panels):
        cx = 18 + panel_w / 2 + index * (panel_w + 4)
        cy = top + 14 + z_h / 2
        a, b = math.cos(alpha), math.sin(alpha)
        xp = -b
        clip = f"clip{index}"
        parts.append(f'<clipPath id="{clip}"><rect x="{fmt(cx - panel_w / 2 + 6)}" y="{fmt(top + 14)}" width="{fmt(panel_w - 12)}" height="{z_h}"/></clipPath>')
        g = [f'<g clip-path="url(#{clip})">']
        g.append(f'<rect x="{fmt(cx - 200)}" y="{fmt(cy)}" width="200" height="200" fill="{RED}" opacity="0.08"/>')
        g.append(f'<line x1="{fmt(cx - 100)}" y1="{fmt(cy)}" x2="{fmt(cx + 100)}" y2="{fmt(cy)}" stroke="{YCOL}" stroke-width="1.4" stroke-dasharray="2 3"/>')
        g.append(f'<line x1="{fmt(cx)}" y1="{fmt(cy - 120)}" x2="{fmt(cx)}" y2="{fmt(cy + 120)}" stroke="{XCOL}" stroke-width="1.4" stroke-dasharray="2 3"/>')
        circle = [(cx + scale * math.cos(s), cy - scale * math.sin(s)) for s in [2 * math.pi * k / 120 for k in range(121)]]
        g.append(polyline(circle, stroke=GRID, stroke_width="1", stroke_dasharray="3 3"))
        # outward normal (a, b): the U_X strip on the far side of the line, the U_Y strip on the side of the origin
        nx, ny = a * 4.5, -b * 4.5
        pts = []
        for k in range(-300, 301):
            x, y = line_point(a, b, 1.0, k / 50)
            pts.append((x, y))
        screen = [(cx + scale * x, cy - scale * y) for x, y in pts]
        g.append(polyline(screen, stroke=MUTED, stroke_width="1"))
        for offset, which in ((1, "X"), (-1, "Y")):
            def value(i):
                x, y = pts[i]
                if which == "X":
                    return None if abs(x) < 0.03 else label_x(x, xp)
                return None if abs(y) < 0.03 else label_y(x, y, b)
            shifted = [(sx + offset * nx, sy + offset * ny) for sx, sy in screen]
            for lab, run in runs(shifted, value):
                if lab is not None:
                    g.append(polyline(run, stroke=LABEL_COLOR[lab], stroke_width="3.4"))
        g.append("</g>")
        parts += g
        tx, ty = cx + scale * a, cy - scale * b
        parts.append(f'<circle cx="{fmt(tx)}" cy="{fmt(ty)}" r="3.4" fill="{INK}"/>')
        parts.append(text(cx, top + 6, label, 12.5, "middle", INK, weight="600"))
    # --- the label at the point of tangency, as the line turns
    y0 = top + z_h + 58
    x0, x1 = 120, 730
    parts.append(text(14, y0 - 22, "The label read at the point of tangency (cos α, sin α), as the line turns once:", 12.5, "start", INK, weight="600"))
    to_x = lambda deg: x0 + (x1 - x0) * deg / 360  # noqa: E731
    rows = [("in U_Y", lambda d: None if math.sin(math.radians(d)) == 0 or abs(math.sin(math.radians(d))) < 1e-9 else label_y(math.cos(math.radians(d)), math.sin(math.radians(d)), math.sin(math.radians(d))), YCOL),
            ("in U_X", lambda d: None if abs(math.cos(math.radians(d))) < 1e-9 else label_x(math.cos(math.radians(d)), -math.sin(math.radians(d))), XCOL)]
    for row, (name, fn, color) in enumerate(rows):
        yy = y0 + 22 * row
        parts.append(text(x0 - 10, yy + 4, name, 12, "end", color, weight="600"))
        degrees = [d / 4 for d in range(0, 1441)]
        segs = runs([(to_x(d), yy) for d in degrees], lambda i: fn(degrees[i]))
        for lab, run in segs:
            if lab is not None:
                parts.append(polyline(run[1:-1] if len(run) > 3 else run, stroke=LABEL_COLOR[lab], stroke_width="7"))
    axis_y = y0 + 44
    parts.append(f'<line x1="{x0}" y1="{axis_y}" x2="{x1}" y2="{axis_y}" stroke="{MUTED}" stroke-width="1"/>')
    for deg, name in [(0, "0"), (90, "π/2"), (180, "π"), (270, "3π/2"), (360, "2π")]:
        parts.append(f'<line x1="{fmt(to_x(deg))}" y1="{axis_y - 3}" x2="{fmt(to_x(deg))}" y2="{axis_y + 3}" stroke="{MUTED}"/>')
        parts.append(text(to_x(deg), axis_y + 16, name, 11.5, "middle", MUTED))
    parts.append(text(x1 + 8, axis_y + 4, "α", 12, "start", MUTED, italic=True))
    for alpha, _ in panels:
        parts.append(f'<circle cx="{fmt(to_x(math.degrees(alpha)))}" cy="{axis_y}" r="2.6" fill="{INK}"/>')
    jx = to_x(180)
    parts.append(f'<line x1="{fmt(jx)}" y1="{y0 - 12}" x2="{fmt(jx)}" y2="{y0 + 32}" stroke="{RED}" stroke-width="1.4" stroke-dasharray="3 2"/>')
    parts.append(text(jx, y0 + 76, "the choice jumps here: x′ = 0, outside U_X, and U_Y does not reach the point (−1, 0)", 11.5, "middle", RED))
    legend_y = y0 + 102
    parts.append(f'<line x1="18" y1="{legend_y - 4}" x2="42" y2="{legend_y - 4}" stroke="{GREEN}" stroke-width="3.4"/>')
    parts.append(text(48, legend_y, "label +1", 12, "start"))
    parts.append(f'<line x1="130" y1="{legend_y - 4}" x2="154" y2="{legend_y - 4}" stroke="{BLUE}" stroke-width="3.4"/>')
    parts.append(text(160, legend_y, "label −1", 12, "start"))
    parts.append(text(250, legend_y, "shaded: x < 0, y < 0, where the labels in the two charts differ;  dots: the panels above", 12, "start", MUTED))
    return svg(width, legend_y + 14, "\n".join(parts), "Lines in the punctured plane and the label read by the line integral R_X, in the two charts")


def main() -> None:
    check_transition()
    check_monodromy()
    check_lines()
    (HERE / "charts.svg").write_text(figure_charts())
    (HERE / "lines.svg").write_text(figure_lines())
    print("Checked the transition relation, the monodromy, and the line integrands; wrote charts.svg and lines.svg")


if __name__ == "__main__":
    main()
