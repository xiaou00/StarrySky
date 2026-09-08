#import "../template.typ": ink, blue, muted, mist
#import "@preview/cetz:0.4.1": canvas, draw

// Images of H_t(z, s) = (z, (1-t)s), drawn in the same projection.
// The cylinder is its lateral surface; the white upper ellipse is an opening.
#let cylinder-retraction() = {
  set text(size: 10pt, fill: ink)
  canvas({
    import draw: *
    let rx = 1.15
    let ry = .34
    let base = .95
    let arrow = (end: ">", length: .17, width: .13)
    let faint = (paint: muted.lighten(30%), thickness: .65pt, dash: "dashed")

    for (cx, height, time, label) in (
      (1.5, 2.3, $t=0$, $S^1 times [0,1]$),
      (6.0, 1.15, $t=1/2$, $S^1 times [0,1/2]$),
      (10.5, 0, $t=1$, $S^1 times {0}$),
    ) {
      content((cx, 4.0), time)

      // A faint outline records the original height in the middle panel.
      if height == 1.15 {
        circle((cx, base + 2.3), radius: (rx, ry), stroke: faint)
        for dx in (-rx, rx) {
          line((cx + dx, base + height), (cx + dx, base + 2.3), stroke: faint)
        }
      }

      if height > 0 {
        rect((cx - rx, base), (cx + rx, base + height), fill: mist, stroke: none)
        circle((cx, base), radius: (rx, ry), fill: mist, stroke: none)
        circle((cx, base + height), radius: (rx, ry),
          fill: white, stroke: muted + .85pt)
        for dx in (-rx, rx) {
          line((cx + dx, base), (cx + dx, base + height), stroke: muted + .85pt)
        }
        // Two selected vertical trajectories on the visible front half.
        for angle in (225deg, 315deg) {
          let px = cx + rx * calc.cos(angle)
          let py = base + ry * calc.sin(angle)
          line((px, py + height * .8), (px, py + .13),
            stroke: blue + .85pt, mark: arrow)
        }
      }

      // The retract stays pointwise fixed throughout the homotopy.
      circle((cx, base), radius: (rx, ry), stroke: blue + 1.5pt)
      circle((cx, base - ry), radius: .055, fill: blue, stroke: none)
      content((cx, .1), label)
    }

    for cx in (3.75, 8.25) {
      line((cx - .6, 2.0), (cx + .6, 2.0), stroke: blue + .9pt, mark: arrow)
    }
  })
}
