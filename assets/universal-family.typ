#import "../template.typ": *
#import "@preview/cetz:0.4.1": canvas, draw

// Schematic pullback square: the frames indicate total spaces, while
// the ellipses stand for a few selected fibres rather than literal curves.
#let universal-family-pullback() = {
  set text(size: 10pt, fill: ink)
  canvas({
    import draw: *
    let highlight = ink
    let arrow-style = (end: ">", length: 0.18, width: 0.14)

    for offset in (0, 8) {
      rect((offset, 3.25), (offset + 4.8, 5.45),
        radius: .18, fill: mist, stroke: rule-c + .6pt)
      line((offset, .75), (offset + 4.8, .75), stroke: blue + 1pt)
      for dx in (.9, 2.4, 3.9) {
        let col = if dx == 2.4 { highlight } else { muted.lighten(28%) }
        line((offset + dx, 3.5), (offset + dx, .85),
          stroke: (paint: col, thickness: .6pt, dash: "dashed"))
        circle((offset + dx, 4.2), radius: (.3, .65),
          stroke: col + 1.1pt, fill: col.lighten(92%))
        circle((offset + dx, .75), radius: .055, fill: col, stroke: none)
      }
    }

    content((2.4, 6.25), text(fill: muted)[给定的族])
    content((10.4, 6.25), text(fill: muted)[万有族])
    content((2.4, 5.8), $Y=T times_M U$)
    content((10.4, 5.8), $U$)
    content((2.4, 5.1), text(fill: highlight)[$Y_(t_0)$])
    content((10.4, 5.1), text(fill: highlight)[$U_(m_0)$])

    line((5.1, 4.2), (7.7, 4.2), stroke: blue + .9pt, mark: arrow-style)
    content((6.4, 4.62), $tilde(g)$)
    line((5.1, .75), (7.7, .75), stroke: blue + .9pt, mark: arrow-style)
    content((6.4, 1.15), $g$)
    content((6.4, .25), text(size: 9pt, fill: muted)[分类态射])

    line((-.35, 3.1), (-.35, 1), stroke: blue + .9pt, mark: arrow-style)
    content((-.65, 2.05), $p$)
    line((13.15, 3.1), (13.15, 1), stroke: blue + .9pt, mark: arrow-style)
    content((13.5, 2.05), $pi$)
    content((.35, .25), $T$)
    content((12.45, .25), $M$)
    content((2.4, .25), text(fill: highlight)[$t_0$])
    content((10.4, .25), text(fill: highlight)[$m_0=g(t_0)$])
  })
}

// Real-point plots of x^2 = t^2 and x^2 = c. The quadratic Bezier
// parametrizes the parabola exactly; the marked fibres lie at t = +/-1, c = 1.
#let quadratic-family-pullback() = {
  set text(size: 10pt, fill: ink)
  canvas({
    import draw: *
    let highlight = ink
    let arrow-style = (end: ">", length: .18, width: .14)
    let guide = (paint: highlight.lighten(30%), thickness: .65pt, dash: "dashed")

    content((2.2, 6.25), $Y: x^2=t^2$)
    content((9.65, 6.25), $U: x^2=c$)

    // Coordinate axes of the total spaces.
    line((.4, 4), (4.1, 4), stroke: rule-c + .7pt, mark: arrow-style)
    line((2.2, 2.3), (2.2, 5.7), stroke: rule-c + .7pt, mark: arrow-style)
    line((7.7, 4), (11.55, 4), stroke: rule-c + .7pt, mark: arrow-style)
    line((8.3, 2.3), (8.3, 5.7), stroke: rule-c + .7pt, mark: arrow-style)
    content((4.12, 3.7), $t$)
    content((11.55, 3.7), $c$)
    content((2.2, 5.93), $x$)
    content((8.3, 5.93), $x$)

    for pos in (1.1, 3.3, 9.75) {
      line((pos, .8), (pos, 5.55), stroke: guide)
    }
    line((.66, 2.53), (3.74, 5.47), stroke: blue + 1.3pt)
    line((.66, 5.47), (3.74, 2.53), stroke: blue + 1.3pt)
    bezier((11.142, 2.53), (11.142, 5.47), (5.458, 4), stroke: blue + 1.3pt)

    for pos in (1.1, 3.3, 9.75) {
      for height in (2.95, 5.05) {
        circle((pos, height), radius: .065, fill: highlight, stroke: white + .4pt)
      }
    }
    circle((2.2, 4), radius: .07, fill: blue, stroke: none)
    circle((8.3, 4), radius: .07, fill: blue, stroke: none)

    line((4.55, 4), (7.2, 4), stroke: blue + .9pt, mark: arrow-style)
    content((5.875, 4.48), text(size: 9pt)[$(t,x) |-> (t^2,x)$])

    // Parameter lines and the classifying map.
    line((.4, .7), (4.1, .7), stroke: blue + .9pt, mark: arrow-style)
    line((7.7, .7), (11.55, .7), stroke: blue + .9pt, mark: arrow-style)
    for (pos, label) in ((1.1, $-1$), (2.2, $0$), (3.3, $1$), (8.3, $0$), (9.75, $1$)) {
      circle((pos, .7), radius: .055,
        fill: if pos in (2.2, 8.3) { blue } else { highlight }, stroke: none)
      content((pos, .32), label)
    }
    content((2.2, -.2), $T=bb(A)^1_k$)
    content((9.65, -.2), $M=bb(A)^1_k$)
    line((4.55, .7), (7.2, .7), stroke: blue + .9pt, mark: arrow-style)
    content((5.875, 1.13), $g:t |-> t^2$)
    line((.1, 2.25), (.1, .95), stroke: blue + .9pt, mark: arrow-style)
    content((-.2, 1.6), $p$)
    line((11.9, 2.25), (11.9, .95), stroke: blue + .9pt, mark: arrow-style)
    content((12.2, 1.6), $pi$)
  })
}
