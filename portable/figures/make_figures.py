#!/usr/bin/env python3
"""Draw the figures of the sketches, after checking the model they depict against the paper's definitions.

    python3 portable/figures/make_figures.py      # writes double-cover.svg and lines.svg beside this file

Both figures are for F = R and n = 2.  There the Hilbert symbol {x, y}_2 is -1 exactly when x < 0 and y < 0, and
the dilations by F^{x2} are those by positive reals.  The figures use the following model of genuine functions, which
the checks below verify against the transition relation (eq:transition-relation) and the line integrals of
Definition definition:lines.  Write z = x + iy and let sqrt be the principal square root, which is smooth off the
negative real axis.  For an odd function f on C^x (f(-w) = -f(w)),

    Phi_Y(v) := f(sqrt(z)),        Phi_X(v) := f({x, y}_2 sqrt(z))

is a genuine function, and every genuine function arises so.  Thus the torsor is the double cover w -> w^2 of the
punctured plane, Phi_Y is read off on the sheet of the principal root, and Phi_X on the sheet that differs from it
exactly over the third quadrant.

Along a line a x + b y = t with t = tau^2 > 0 and b = -x' != 0, the integrand of R_X is
Phi_X(x, y) {x, -x'}_2 = f(sigma(z)) with sigma(z) := {x, b y}_2 sqrt(z), a continuous choice of square root along the
line: one branch of the hyperbola Re(conj(c) w^2) = t, c = a + ib, which lies over the line.

Nothing here is imported by the build; the SVG files are committed, and the build checks that they exist.
"""
from __future__ import annotations

import cmath
import html
import math
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent

# ---------------------------------------------------------------- the model, and the checks against the paper


def hilbert2(x: float, y: float) -> int:
    """The real quadratic Hilbert symbol {x, y}_2."""
    return -1 if x < 0 and y < 0 else 1


def principal_sqrt(z: complex) -> complex:
    return cmath.sqrt(z)  # branch cut along the negative real axis, Re >= 0


def make_genuine(f):
    """The genuine function attached to an odd function f on C^x."""
    def phi_x(x, y):
        assert x != 0
        return f(hilbert2(x, y) * principal_sqrt(complex(x, y)))

    def phi_y(x, y):
        assert y != 0
        return f(principal_sqrt(complex(x, y)))
    return phi_x, phi_y


def odd_test_function(seed: int):
    """A smooth odd function on C^x: w times a polynomial in w^2 and its conjugate, damped (only its oddness matters)."""
    rng = random.Random(seed)
    coeffs = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(6)]

    def f(w: complex) -> complex:
        z = w * w
        poly = sum(c * z ** k * z.conjugate() ** j for (k, j), c in zip([(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)], coeffs))
        return w * poly * math.exp(-abs(z))
    return f


def check_model() -> None:
    rng = random.Random(1)
    f = odd_test_function(7)
    phi_x, phi_y = make_genuine(f)
    # The transition relation Phi_X = {x, y}_2 Phi_Y on U_X cap U_Y.
    for _ in range(4000):
        x, y = rng.uniform(-3, 3), rng.uniform(-3, 3)
        if abs(x) < 1e-9 or abs(y) < 1e-9:
            continue
        assert abs(phi_x(x, y) - hilbert2(x, y) * phi_y(x, y)) < 1e-12
    # Each chart is continuous where the principal root is not: Phi_X across the negative real axis (y = 0, x < 0),
    # which lies in U_X, and Phi_Y across the axis x = 0, which lies in U_Y.
    for x in (-2.0, -0.7, -0.1):
        above, below = phi_x(x, 1e-9), phi_x(x, -1e-9)
        assert abs(above - below) < 1e-6, (x, above, below)
    for y in (-2.0, -0.3, 0.4, 1.5):
        left, right = phi_y(-1e-9, y), phi_y(1e-9, y)
        assert abs(left - right) < 1e-6, (y, left, right)
    # The cover is connected: following the chart values once around a circle returns the opposite sign.
    # This is the monodromy of the cocycle {x, y}_2 on the four arcs of the circle.
    sign, charts = 1, [("X", 0.0), ("Y", math.pi / 2), ("X", math.pi), ("Y", 3 * math.pi / 2)]
    for (chart, _), (next_chart, middle) in zip(charts, charts[1:] + charts[:1]):
        overlap = middle - math.pi / 4  # the quadrant between the two arcs
        x, y = math.cos(overlap), math.sin(overlap)
        # moving from chart to next_chart across the overlap
        sign *= hilbert2(x, y)
    assert sign == -1


def line_integrand_paper(phi_x, xp: float, yp: float, tau: float):
    """The integrand of R_X Phi((x', y'), tau) of Definition definition:lines, as a function of x (n = 2)."""
    def integrand(x):
        y = (x * yp - tau ** 2) / xp
        return phi_x(x, y) * hilbert2(x, -xp)
    return integrand


def branch_on_line(a: float, b: float, t: float, x: float) -> complex:
    """sigma(z) = {x, b y}_2 sqrt(z) at the point of a x + b y = t with first coordinate x."""
    y = (t - a * x) / b
    return hilbert2(x, b * y) * principal_sqrt(complex(x, y))


def check_lines() -> None:
    f = odd_test_function(11)
    phi_x, _ = make_genuine(f)
    for alpha in [k * math.pi / 12 + 0.01 for k in range(24)]:
        tau = 0.8
        t = tau ** 2
        a, b = math.cos(alpha), math.sin(alpha)          # (a, b) = (y', -x')
        xp, yp = -b, a
        if abs(b) < 1e-6:
            continue
        integrand = line_integrand_paper(phi_x, xp, yp, tau)
        xs = [-6 + 12 * k / 6000 for k in range(6001)]
        previous = None
        for x in xs:
            if abs(x) < 1e-12:
                continue
            w = branch_on_line(a, b, t, x)
            # the paper's integrand is f along sigma
            assert abs(integrand(x) - f(w)) < 1e-12
            # sigma lies over the line: w^2 is the point (x, y), and on the hyperbola Re(conj(c) w^2) = t
            y = (t - a * x) / b
            assert abs(w * w - complex(x, y)) < 1e-9
            assert abs((complex(a, -b) * w * w).real - t) < 1e-9
            # sigma is continuous along the line: consecutive points stay on one branch
            if previous is not None:
                assert abs(w - previous) < 0.2, (alpha, x, w, previous)
            previous = w
        # sigma agrees with the principal root where the line meets the y-axis
        y0 = t / b
        assert abs(branch_on_line(a, b, t, 1e-9) - principal_sqrt(complex(0, y0))) < 1e-4
    # The chosen branch, followed once around: the lift of the tangent point e^{i alpha} is e^{i alpha / 2} for
    # alpha in (-pi, pi), so it jumps from i to -i where the line becomes x = -1 (x' = 0, outside U_X), and nowhere else.
    for alpha in [-math.pi + 0.05 + k * 0.1 for k in range(62)]:
        a, b = math.cos(alpha), math.sin(alpha)
        if abs(b) < 1e-6:
            continue
        w = branch_on_line(a, b, 1.0, a)  # the tangent point (cos alpha, sin alpha) of a x + b y = 1
        assert abs(w - cmath.exp(0.5j * alpha)) < 1e-9, (alpha, w)


# ---------------------------------------------------------------- SVG helpers

INK, MUTED, GREEN, RED, BLUE, GRID = "#25332b", "#6b766f", "#1f7a4d", "#b23a2a", "#2f5d9e", "#c9d1cb"


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


# ---------------------------------------------------------------- figure 1: the cover inside a torus

R_BIG, R_SMALL = 2.0, 0.78
ELEV = math.radians(32)


def torus_point(theta, phi):
    rho = R_BIG + R_SMALL * math.cos(phi)
    return (rho * math.cos(theta), rho * math.sin(theta), R_SMALL * math.sin(phi))


def view(p):
    """Orthographic view from elevation ELEV, looking at the origin from the side of negative y."""
    x, y, z = p
    u = x
    v = -(z * math.cos(ELEV) + y * math.sin(ELEV))   # screen y grows downward
    depth = -y * math.cos(ELEV) + z * math.sin(ELEV)  # larger is nearer the viewer
    return u, v, depth


VIEWER = (0.0, -math.cos(ELEV), math.sin(ELEV))


def torus_sdf(p):
    x, y, z = p
    return math.hypot(math.hypot(x, y) - R_BIG, z) - R_SMALL


def visible(p) -> bool:
    """Whether a point of the torus is seen: march toward the viewer and look for the surface."""
    step, s = 0.02, 0.03
    while s < 8:
        q = tuple(p[i] + s * VIEWER[i] for i in range(3))
        d = torus_sdf(q)
        if d < -1e-3:
            return False
        s += max(step, d * 0.9)
    return True


def figure_double_cover() -> str:
    scale, ox, oy = 80, 330, 212
    to_screen = lambda p: (ox + scale * view(p)[0], oy + scale * view(p)[1])  # noqa: E731
    parts = []
    # the wireframe: parallels (fixed phi) and meridians (fixed theta), drawn faintly, hidden parts omitted
    for phi in [k * math.pi / 6 for k in range(12)]:
        pts = [torus_point(2 * math.pi * k / 240, phi) for k in range(241)]
        for shown, run in runs(pts, lambda i: visible(pts[i])):
            if shown:
                parts.append(polyline([to_screen(p) for p in run], stroke=GRID, stroke_width="0.8"))
    for theta in [k * math.pi / 8 for k in range(16)]:
        pts = [torus_point(theta, 2 * math.pi * k / 120) for k in range(121)]
        for shown, run in runs(pts, lambda i: visible(pts[i])):
            if shown:
                parts.append(polyline([to_screen(p) for p in run], stroke=GRID, stroke_width="0.8"))
    # the silhouette, approximately: the outer equator and the outline in phi where the normal is perpendicular
    # to the view; drawn by sampling the visible boundary is fussy, so we outline the outer and inner rims instead.
    # the cover: phi = theta / 2, theta in [0, 4 pi), one closed curve; colored by the sheet of the Y-chart
    samples = 1600
    pts, sheet = [], []
    for k in range(samples + 1):
        theta = 4 * math.pi * k / samples
        phi = theta / 2
        pts.append(torus_point(theta, phi))
        # the point of the torsor is w = e^{i phi} (times sqrt r); it is the principal root when cos(phi) > 0,
        # or phi = pi/2 exactly over the negative axis, which has measure zero here
        sheet.append(math.cos(phi) >= 0)
    for (shown, principal), run in runs(pts, lambda i: (visible(pts[i]), sheet[i])):
        color = GREEN if principal else BLUE
        if shown:
            parts.append(polyline([to_screen(p) for p in run], stroke=color, stroke_width="2.6", stroke_linecap="round"))
        else:
            parts.append(polyline([to_screen(p) for p in run], stroke=color, stroke_width="1.4", stroke_dasharray="4 4", opacity="0.65"))
    # the two points over the direction theta = 0, and an arrow along the curve
    for phi, label, dx in [(0.0, "+√r", 14), (math.pi, "−√r", 14)]:
        x, y = to_screen(torus_point(0.0, phi))
        parts.append(f'<circle cx="{fmt(x)}" cy="{fmt(y)}" r="4.2" fill="{INK}"/>')
        parts.append(text(x + dx, y + 4, label, 13, "start"))
    # the base circle, below: directions of v, with the third quadrant marked
    bx, by, brad = ox, 468, 1.45

    def base(theta, radius=brad):
        u, v, _ = view((radius * math.cos(theta), radius * math.sin(theta), 0.0))
        return bx + scale * u, by + scale * v
    circle = [base(2 * math.pi * k / 240) for k in range(241)]
    parts.append(polyline(circle, stroke=INK, stroke_width="1.6"))
    q3 = [base(math.pi + (math.pi / 2) * k / 60) for k in range(61)]
    parts.append(polyline(q3, stroke=RED, stroke_width="5", stroke_linecap="round", opacity="0.85"))
    for theta, label, anchor, dx in [(0, "x > 0, y = 0", "start", 10), (math.pi / 2, "y > 0", "middle", 0),
                                     (math.pi, "x < 0, y = 0", "end", -10), (3 * math.pi / 2, "y < 0", "middle", 0)]:
        x, y = base(theta, brad * (1.0 if dx else 1.25))
        parts.append(text(x + dx, y + 4, label, 11.5, anchor, MUTED))
    x, y = base(5 * math.pi / 4, brad * 0.62)
    parts.append(text(x, y + 4, "{x, y}₂ = −1", 12.5, "middle", RED))
    x0, y0 = base(0.0)
    parts.append(f'<circle cx="{fmt(x0)}" cy="{fmt(y0)}" r="3.6" fill="{INK}"/>')
    # projection arrow
    parts.append(f'<line x1="{ox + 250}" y1="318" x2="{ox + 250}" y2="392" stroke="{MUTED}" stroke-width="1.2" marker-end="url(#arrow)"/>')
    parts.append(text(ox + 258, 360, "arg v", 12, "start", MUTED))
    # legend
    parts.append(text(18, 22, "The torsor over the circle of directions of v, inside the torus of pairs (arg v, arg w)", 13.5, "start", INK, weight="600"))
    parts.append(f'<line x1="20" y1="576" x2="46" y2="576" stroke="{GREEN}" stroke-width="2.6"/>')
    parts.append(text(52, 580, "w = √z, the principal root of z = x + iy (the sheet on which Φ_Y is read)", 12, "start"))
    parts.append(f'<line x1="20" y1="596" x2="46" y2="596" stroke="{BLUE}" stroke-width="2.6"/>')
    parts.append(text(52, 600, "w = −√z;   dashed: behind the torus", 12, "start"))
    parts.append(text(18, 626, "Once around the base circle, the point +√r of the cover returns as −√r: there is no global section.", 12, "start", MUTED))
    defs = (f'<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">'
            f'<path d="M0,0 L10,5 L0,10 z" fill="{MUTED}"/></marker></defs>')
    return svg(660, 640, defs + "\n" + "\n".join(parts), "Deligne's torsor for n = 2 over the real numbers, drawn in a torus")


# ---------------------------------------------------------------- figure 2: lines and their lifts

def figure_lines() -> str:
    # alpha is the direction of c = a + ib = y' - i x'; the line is a x + b y = 1, tangent to the unit circle at e^{i alpha}
    panels = [(math.pi / 4, "α = π/4"), (3 * math.pi / 4, "α = 3π/4"), (math.pi - 0.18, "α just below π"), (-math.pi + 0.18, "α just above π")]
    width, panel_w, top, z_h, gap = 760, 182, 58, 170, 40
    scale_z, scale_w = 30, 52
    parts = [text(14, 24, "Lines a x + b y = τ² (here τ² = 1) and the branch of their preimage chosen by R_X", 13.5, "start", INK, weight="600")]
    parts.append(text(14, 44, "top: the line in the plane of v = (x, y); bottom: its preimage under w ↦ w², the hyperbola Re((a − ib) w²) = 1", 11.5, "start", MUTED))
    for index, (alpha, label) in enumerate(panels):
        cx = 18 + panel_w / 2 + index * (panel_w + 4)
        a, b = math.cos(alpha), math.sin(alpha)
        # --- the plane of v
        zy = top + 14 + z_h / 2
        clip = f"clipz{index}"
        parts.append(f'<clipPath id="{clip}"><rect x="{fmt(cx - panel_w / 2 + 6)}" y="{fmt(top + 14)}" width="{fmt(panel_w - 12)}" height="{z_h}"/></clipPath>')
        g = [f'<g clip-path="url(#{clip})">']
        # third quadrant shaded
        g.append(f'<rect x="{fmt(cx - 200)}" y="{fmt(zy)}" width="200" height="200" fill="{RED}" opacity="0.08"/>')
        g.append(f'<line x1="{fmt(cx - 100)}" y1="{fmt(zy)}" x2="{fmt(cx + 100)}" y2="{fmt(zy)}" stroke="{GRID}" stroke-width="1"/>')
        g.append(f'<line x1="{fmt(cx)}" y1="{fmt(zy - 100)}" x2="{fmt(cx)}" y2="{fmt(zy + 100)}" stroke="{GRID}" stroke-width="1"/>')
        circle = [(cx + scale_z * math.cos(s), zy - scale_z * math.sin(s)) for s in [2 * math.pi * k / 120 for k in range(121)]]
        g.append(polyline(circle, stroke=GRID, stroke_width="1", stroke_dasharray="3 3"))
        # the line, colored where sigma is the principal root (green) or its negative (blue)
        ts = [-6 + 12 * k / 480 for k in range(481)]
        pts, flags = [], []
        for s in ts:
            x, y = a - b * s, b + a * s   # the tangent point plus s times the direction (-b, a)
            pts.append((cx + scale_z * x, zy - scale_z * y))
            w = hilbert2(x, b * y) * principal_sqrt(complex(x, y))
            flags.append(abs(w - principal_sqrt(complex(x, y))) < 1e-9)
        for principal, run in runs(pts, lambda i: flags[i]):
            g.append(polyline(run, stroke=GREEN if principal else BLUE, stroke_width="2.4"))
        g.append("</g>")
        parts += g
        tx, ty = cx + scale_z * a, zy - scale_z * b
        parts.append(f'<circle cx="{fmt(tx)}" cy="{fmt(ty)}" r="3.2" fill="{INK}"/>')
        parts.append(text(cx, top + 8, label, 12.5, "middle", INK, weight="600"))
        # --- the plane of w
        wy = top + 14 + z_h + gap + z_h / 2
        clip = f"clipw{index}"
        parts.append(f'<clipPath id="{clip}"><rect x="{fmt(cx - panel_w / 2 + 6)}" y="{fmt(wy - z_h / 2)}" width="{fmt(panel_w - 12)}" height="{z_h}"/></clipPath>')
        g = [f'<g clip-path="url(#{clip})">']
        g.append(f'<line x1="{fmt(cx - 100)}" y1="{fmt(wy)}" x2="{fmt(cx + 100)}" y2="{fmt(wy)}" stroke="{GRID}" stroke-width="1"/>')
        g.append(f'<line x1="{fmt(cx)}" y1="{fmt(wy - 100)}" x2="{fmt(cx)}" y2="{fmt(wy + 100)}" stroke="{GRID}" stroke-width="1"/>')
        circle = [(cx + scale_w * math.cos(s), wy - scale_w * math.sin(s)) for s in [2 * math.pi * k / 120 for k in range(121)]]
        g.append(polyline(circle, stroke=GRID, stroke_width="1", stroke_dasharray="3 3"))
        chosen, other = [], []
        for s in ts:
            x, y = a - b * s, b + a * s
            w = hilbert2(x, b * y) * principal_sqrt(complex(x, y))
            chosen.append((cx + scale_w * w.real, wy - scale_w * w.imag))
            other.append((cx - scale_w * w.real, wy + scale_w * w.imag))
        g.append(polyline(other, stroke=MUTED, stroke_width="1.4", stroke_dasharray="4 4"))
        g.append(polyline(chosen, stroke=INK, stroke_width="2.6"))
        g.append("</g>")
        parts += g
        lift = cmath.exp(0.5j * alpha)
        parts.append(f'<circle cx="{fmt(cx + scale_w * lift.real)}" cy="{fmt(wy - scale_w * lift.imag)}" r="3.4" fill="{INK}"/>')
        for value, name in [(1j, "i"), (-1j, "−i")]:
            parts.append(text(cx + 7, wy - scale_w * value.imag + (13 if value.imag < 0 else -5), name, 11, "start", MUTED, italic=True))
    y_legend = top + 14 + 2 * z_h + gap + 30
    parts.append(f'<line x1="18" y1="{y_legend - 4}" x2="42" y2="{y_legend - 4}" stroke="{INK}" stroke-width="2.6"/>')
    parts.append(text(48, y_legend, "the branch σ chosen by R_X: the integrand of R_X Φ is f(σ)", 12, "start"))
    parts.append(f'<line x1="18" y1="{y_legend + 16}" x2="42" y2="{y_legend + 16}" stroke="{MUTED}" stroke-width="1.4" stroke-dasharray="4 4"/>')
    parts.append(text(48, y_legend + 20, "the other branch, −σ", 12, "start"))
    parts.append(f'<line x1="400" y1="{y_legend - 4}" x2="424" y2="{y_legend - 4}" stroke="{GREEN}" stroke-width="2.4"/>')
    parts.append(text(430, y_legend, "σ = √z (principal root)", 12, "start"))
    parts.append(f'<line x1="400" y1="{y_legend + 16}" x2="424" y2="{y_legend + 16}" stroke="{BLUE}" stroke-width="2.4"/>')
    parts.append(text(430, y_legend + 20, "σ = −√z;   shaded: x < 0, y < 0", 12, "start"))
    height = y_legend + 34
    return svg(width, height, "\n".join(parts), "Lines in the punctured plane and the branch of their preimage chosen by the line integral R_X")


def main() -> None:
    check_model()
    check_lines()
    (HERE / "double-cover.svg").write_text(figure_double_cover())
    (HERE / "lines.svg").write_text(figure_lines())
    print("Checked the model against the paper's definitions; wrote double-cover.svg and lines.svg")


if __name__ == "__main__":
    main()
