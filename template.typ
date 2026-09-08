// ─────────────────────────────────────────────
//  Ex Nihilo · 数学笔记模板
// ─────────────────────────────────────────────

#import "@preview/fletcher:0.5.8" as fletcher

// Palette drawn from the cover: midnight blue, cyan light, cool silver.
// Keep saturated cyan for ornaments; use darker blues for readable text.
#let ink       = rgb("#202D40")
#let midnight  = rgb("#101C30")
#let accent    = rgb("#00AFE3")
#let blue      = rgb("#21618D")
#let muted     = rgb("#6A7B8D")
#let rule-c    = rgb("#DCE5EE")
#let mist      = rgb("#F3F8FC")
#let c-thm     = rgb("#285C86")
#let c-def     = rgb("#14778C")
#let c-prop    = rgb("#376E98")
#let c-con     = rgb("#567389")
#let c-rem     = rgb("#718096")
#let table-tint = rgb("#F3F7FD")

// Shared blue-gray lines for mathematical diagrams.
#let book-diagram = fletcher.diagram.with(edge-stroke: .65pt + muted)

// Keep the header rule continuous across column gutters. The guard also
// makes this safe when an included chapter applies conf a second time.
#let _table-header-rule(it) = {
  let needs-rule(child) = child.func() == table.header and not (
    child.children.any(cell => cell.func() == table.hline)
  )
  if it.children.any(needs-rule) {
    let fields = it.fields()
    let children = fields.remove("children")
    table(..fields, ..children.map(child => {
      if needs-rule(child) {
        let header-fields = child.fields()
        let cells = header-fields.remove("children")
        table.header(..header-fields, ..cells, table.hline())
      } else { child }
    }))
  } else { it }
}

// Family names as exposed by Typst (including Chinese fallbacks).
#let source-han-serif = "Source Han Serif"
#let latin-serif = "Libertinus Serif"
#let cover-title-font = ("Noto Serif Display", source-han-serif)
#let ui-font = ("Fira Sans", "Source Han Sans")

// The cover's four-point star, drawn as a small vector ornament.
#let _star(size: 9pt, color: accent) = box(
  width: size, height: size, baseline: 15%,
  polygon(
    fill: color, stroke: none,
    (size / 2, 0pt), (size * .61, size * .39),
    (size, size / 2), (size * .61, size * .61),
    (size / 2, size), (size * .39, size * .61),
    (0pt, size / 2), (size * .39, size * .39),
  ),
)

#let _small-label(body, color: muted) = text(
  font: ui-font, size: 8pt, tracking: 1.4pt, fill: color, body,
)

#let _accent-rule() = grid(
  columns: (25pt, 1fr, 7pt), column-gutter: 5pt, align: horizon,
  line(length: 100%, stroke: 1.5pt + accent),
  line(length: 100%, stroke: .5pt + rule-c),
  _star(size: 7pt),
)

#let _folio() = context {
  align(right, [
    #_star(size: 6pt, color: accent.lighten(20%))
    #h(8pt)
    #text(font: ui-font, size: 8pt, fill: muted,
      counter(page).display("1"))
  ])
}

#let _env-counter(tag) = counter("env-" + tag)
#let _part-counter = counter("part")
#let _book-title = state("ex-nihilo-book-title", [])
#let _appendix-depth = state("ex-nihilo-appendix-depth", 0)

// Keep the native heading counter for links and nesting. Format its chapter
// component from the target chapter, so references work across appendix scopes.
#let _chapter-number(chapter, padded: false) = {
  let appendices = query(heading.where(level: 1)).filter(it =>
    it.numbering != none and _appendix-depth.at(it.location()) > 0)
    .map(it => counter(heading).at(it.location()).first())
  let preceding = appendices.filter(n => n <= chapter).len()
  if chapter in appendices {
    numbering("A", preceding)
  } else {
    numbering(if padded { "01" } else { "1" }, chapter - preceding)
  }
}

#let _heading-numbering(..numbers) = context {
  let values = numbers.pos()
  ( (_chapter-number(values.first()),) + values.slice(1).map(str) ).join(".")
}

// Place this wrapper at the end of the book. Included chapters can keep their
// own conf(easy: true); multiple wrappers continue A, B, C rather than restart.
// Usage: #appendix[#include "chapters/a001.typ"]
#let appendix(body) = {
  _appendix-depth.update(n => n + 1)
  body
  _appendix-depth.update(n => n - 1)
}

// A part sits above chapters but does not enter the chapter counter. The
// unnumbered heading supplies its bookmark and outline entry without advancing
// the heading counter.
#let part(body) = {
  _part-counter.step()
  heading(
    level: 1,
    numbering: none,
    outlined: true,
    bookmarked: true,
    body,
  )
}

// End matter uses an unnumbered chapter heading and native bibliography links.
// Usage: #references("references.bib"); cite works with @Qui67[I.1, Theorem 1].
#let references(sources, title: [参考文献]) = {
  [#heading(level: 1, numbering: none, title) <references>]
  set text(lang: "en")
  set par(justify: false)
  show link: it => if type(it.dest) == str and it.dest.ends-with(".pdf") and it.body != [PDF] {
    link(it.dest, [PDF])
  } else { it }
  bibliography(sources, title: none, style: "math-alphanumeric.csl")
}

// A compact filled 2-simplex, entirely drawn as a Fletcher diagram.
// Examples:
//   #simplex2($x_0$, $x_1$, $x_2$)
//   #simplex2($x_0$, $x_1$, $x_2$, ab: $f$, bc: $g$, ac: $g compose f$)
#let simplex2(a, b, c, ab: none, bc: none, ac: none) = book-diagram(
  spacing: 20pt,
  cell-size: 0pt,
  node-inset: 5pt,
  {
    fletcher.edge(
      (-0.18, 1.02), (1.18, 1.02),
      label: $#ac$, label-side: right, marks: "->",
    )
    fletcher.edge(
      (0.5, -0.18), (1.18, 1.02),
      label: $#bc$, label-side: left, marks: "->",
    )
    fletcher.edge(
      (-0.18, 1.02), (0.5, -0.18),
      label: $#ab$, label-side: left, marks: "->",
    )

    fletcher.node((-0.18, 1.02), $#a$)
    fletcher.node((1.18, 1.02), $#c$)
    fletcher.node((0.5, -0.18), $#b$)
    fletcher.node((0.5, 0.61), text(size: 10pt, "///"))
  },
)
#let simplex2hollow(a, b, c, ab: none, bc: none, ac: none) = book-diagram(
  spacing: 20pt,
  cell-size: 0pt,
  node-inset: 5pt,
  {
    fletcher.edge(
      (-0.18, 1.02), (1.18, 1.02),
      label: $#ac$, label-side: right, marks: "->",
    )
    fletcher.edge(
      (0.5, -0.18), (1.18, 1.02),
      label: $#bc$, label-side: left, marks: "->",
    )
    fletcher.edge(
      (-0.18, 1.02), (0.5, -0.18),
      label: $#ab$, label-side: left, marks: "->",
    )

    fletcher.node((-0.18, 1.02), $#a$)
    fletcher.node((1.18, 1.02), $#c$)
    fletcher.node((0.5, -0.18), $#b$)
  },
)

#let _cover-simplex() = {
  let crystal = blue
  let edge = 1.15pt + crystal
  let hidden-edge = (paint: crystal.lighten(28%), thickness: 0.8pt, dash: "dashed")
  let vertex = 3.2pt

  box(width: 132pt, height: 112pt, {
    // A centered equilateral silhouette with three subtly shaded faces.
    place(dx: 18pt, dy: 10pt, polygon(
      fill: crystal.transparentize(80%),
      stroke: none,
      (48pt, 0pt), (0pt, 82pt), (48pt, 58pt),
    ))
    place(dx: 66pt, dy: 10pt, polygon(
      fill: accent.transparentize(88%),
      stroke: none,
      (0pt, 0pt), (48pt, 82pt), (0pt, 58pt),
    ))
    place(dx: 18pt, dy: 68pt, polygon(
      fill: crystal.transparentize(75%),
      stroke: none,
      (48pt, 0pt), (0pt, 24pt), (96pt, 24pt),
    ))

    // The three outer sides stay solid; only the rear inner edge is dashed.
    place(dx: 18pt, dy: 92pt, line(end: (48pt, -24pt), stroke: hidden-edge))
    place(dx: 66pt, dy: 10pt, line(end: (-48pt, 82pt), stroke: edge))
    place(dx: 66pt, dy: 10pt, line(end: (48pt, 82pt), stroke: edge))
    place(dx: 66pt, dy: 10pt, line(end: (0pt, 58pt), stroke: edge))
    place(dx: 18pt, dy: 92pt, line(end: (96pt, 0pt), stroke: edge))
    place(dx: 66pt, dy: 68pt, line(end: (48pt, 24pt), stroke: edge))

    for point in ((66pt, 10pt), (18pt, 92pt), (66pt, 68pt), (114pt, 92pt)) {
      place(
        dx: point.at(0) - vertex,
        dy: point.at(1) - vertex,
        circle(radius: vertex, fill: white, stroke: 1.2pt + crystal),
      )
    }
  })
}

#let _reset-env-counters() = {
  for tag in ("theorem", "lemma", "corollary", "proposition", "definition", "axiom") {
    _env-counter(tag).update(0)
  }
}

#let _env-labels = (
  "env-theorem": "定理",
  "env-lemma": "引理",
  "env-corollary": "推论",
  "env-proposition": "命题",
  "env-definition": "定义",
  "env-axiom": "公理",
)

#let _book-ref(it) = {
  let el = it.element
  if el != none and el.func() == heading and it.form == "normal" and it.supplement == auto {
    let prefix = if el.level != 1 { [小节] }
      else if _appendix-depth.at(el.location()) > 0 { [附录] }
      else { [章节] }
    ref(it.target, supplement: prefix)
  } else if el != none and repr(el.func()) == "block" and repr(el.body.func()) == "align" {
    let inner = el.body.body
    if repr(inner.func()) == "sequence" and inner.children.len() > 0 {
      let first = inner.children.first()
      if repr(first.func()) == "counter-update" and first.has("key") and first.key in _env-labels {
        let hs = counter(heading).at(el.location())
        let chapter = hs.at(0, default: 1)
        let section = hs.at(1, default: 0)
        let n = counter(first.key).at(el.location()).first() + 1
        let number = _chapter-number(chapter) + "." + str(section) + "." + str(n)
        link(el.location(), _env-labels.at(first.key) + " " + number)
      } else {
        it
      }
    } else {
      it
    }
  } else {
    it
  }
}

// ── Page setup ───────────────────────────────
#let conf(
  title:    "",
  subtitle: "",
  author:   "",
  date:     "",
  cover-image: none,
  easy:     false,
  doc,
) = {
  if not easy {
    set document(title: title, author: author)
    _book-title.update(title)
  }

  set page(
    paper: "a4",
    margin: (x: 2.7cm, top: 2.6cm, bottom: 2.5cm),
    fill: white,
    header-ascent: 1.2em,
    footer-descent: 1.2em,
    header: context {
      // Included chapters may apply conf(easy: true): keep the book title.
      let book-title = if title == "" { _book-title.get() } else { title }
      let chapters = query(heading.where(level: 1)).filter(h =>
        (h.numbering != none or h.at("label", default: none) == <references>)
        and h.location().page() <= here().page())
      let chapter-title = if chapters.len() > 0 { chapters.last().body } else { [] }
      set text(font: (latin-serif, source-han-serif), size: 8pt, fill: muted)
      grid(
        columns: (1fr, 1fr), column-gutter: 12pt,
        align(left, book-title),
        align(right, chapter-title),
      )
      v(5pt)
      line(length: 100%, stroke: .45pt + rule-c)
    },
    footer: _folio(),
  )

  set text(font: (latin-serif, source-han-serif), size: 11pt, lang: "zh", fill: ink)
  show math.equation: set text(font: ("Libertinus Math", source-han-serif))
  set par(justify: true, leading: .72em, spacing: .9em)
  set list(indent: 1em, body-indent: .6em, marker: text(fill: blue, [•]))
  set enum(indent: 1em, body-indent: .6em)
  show link: set text(fill: blue)
  show ref: _book-ref
  set math.equation(numbering: none)
  set heading(numbering: _heading-numbering)

  // Striped tables: centered text, open columns, and one header rule.
  set table(
    stroke: none,
    inset: (x: 9pt, y: 7pt),
    column-gutter: 18pt,
    align: center + horizon,
    fill: (x, y) => if calc.even(y) { table-tint } else { none },
  )
  set table.hline(stroke: .65pt + muted)
  show table.cell.where(y: 0): set text(weight: "bold", fill: ink)
  show table: _table-header-rule
  show figure.caption: set text(size: 9pt, fill: muted)
  set figure(gap: .8em)
  show footnote.entry: set text(size: 8.5pt)
  set footnote.entry(separator: line(stroke: .5pt + rule-c, length: 25%))
  show raw: set text(font: "JetBrains Mono", size: .85em)
  show raw.where(block: true): set block(
    fill: mist, inset: 12pt, radius: 2pt, stroke: .4pt + rule-c,
  )

  show heading.where(level: 1): it => {
    if it.at("label", default: none) == <references> {
      pagebreak(weak: true)
      block(width: 100%, breakable: false, sticky: true, above: 14pt, below: 22pt, {
        _small-label("REFERENCES", color: blue)
        v(12pt)
        text(size: 24pt, weight: "semibold", fill: midnight, it.body)
        v(16pt)
        _accent-rule()
      })
    } else if it.numbering == none {
      let part-number = _part-counter.at(it.location()).first()
      page(header: none, footer: none, fill: none, {
        v(1fr)
        align(center, {
          _star(size: 20pt)
          v(24pt)
          _small-label([PART #numbering("I", part-number)], color: blue)
          v(12pt)
          text(size: 12pt, fill: muted,
            [第#numbering("一", part-number)部分])
          v(14pt)
          text(size: 28pt, weight: "semibold", fill: midnight, it.body)
          v(24pt)
          line(length: 38pt, stroke: 1pt + accent)
        })
        v(1.25fr)
      })
    } else {
      _reset-env-counters()
      pagebreak(weak: true)
      block(width: 100%, breakable: false, sticky: true, above: 14pt, below: 22pt, {
        _small-label({
          let chapter = counter(heading).at(it.location()).first()
          let prefix = if _appendix-depth.at(it.location()) > 0 { "APPENDIX " } else { "CHAPTER " }
          prefix + _chapter-number(chapter, padded: true)
        }, color: blue)
        v(12pt)
        text(size: 24pt, weight: "semibold", fill: midnight, it.body)
        v(16pt)
        _accent-rule()
      })
    }
  }
  show heading.where(level: 2): it => block(
    width: 100%, breakable: false, sticky: true, above: 20pt, below: 10pt,
    grid(
      columns: (auto, 1fr), column-gutter: 10pt, align: horizon,
      text(font: latin-serif, size: 12pt, fill: blue,
        counter(heading).display(_heading-numbering)),
      text(size: 15pt, weight: "semibold", fill: midnight, it.body),
    ),
  )
  show heading.where(level: 3): it => block(
    breakable: false, sticky: true, above: 14pt, below: 7pt,
    text(size: 12pt, weight: "semibold", fill: ink, [
      #text(fill: blue, counter(heading).display(_heading-numbering))
      #h(5pt)#it.body
    ]),
  )

  if not easy {
    // A light book-jacket composition with a centered, inset illustration.
    page(
      margin: (x: 2.4cm, top: 1.8cm, bottom: 1.8cm),
      fill: white, header: none, footer: none,
      background: if cover-image != none {
        align(center + horizon,
          image(cover-image, width: 75%, fit: "contain"))
      },
      {
        set text(fill: midnight)
        set par(leading: 0pt, spacing: 0pt)
        text(
          font: cover-title-font, size: 46pt,
          style: "italic", weight: "light", tracking: .1pt, title,
        )
        if subtitle != "" {
          v(10pt)
          text(size: 10pt, tracking: 1.8pt, fill: blue, subtitle)
        }
        v(13pt)
        line(length: 28pt, stroke: 1.2pt + accent)
        if cover-image == none {
          v(1fr)
          align(center, _cover-simplex())
        }
        v(1fr)
        grid(
          columns: (1fr, auto), align: bottom,
          text(size: 11pt, tracking: .8pt, author),
          _small-label(date, color: muted),
        )
      },
    )

    // Explicit page scope also handles a table of contents spanning many pages.
    page(header: none, footer: _folio(), {
      v(15pt)
      _small-label("CONTENTS", color: blue)
      v(12pt)
      text(size: 25pt, weight: "semibold", fill: midnight, "目录")
      v(16pt)
      _accent-rule()
      v(23pt)
      let outline-page(body) = text(
        font: ui-font, size: 9pt, weight: "regular", style: "normal", fill: muted,
        number-type: "lining", number-width: "tabular", body,
      )
      set outline.entry(fill: none)
      show outline.entry.where(level: 1): it => {
        let el = it.element
        if el.at("label", default: none) == <references> {
          block(width: 100%, above: 16pt, below: 10pt,
            link(el.location(), grid(
              columns: (1fr, auto), column-gutter: 10pt, align: horizon,
              text(size: 12pt, weight: "semibold", fill: midnight, el.body),
              outline-page(it.page()),
            )))
        } else if el.numbering == none {
          let part-number = _part-counter.at(el.location()).first()
          block(above: 24pt, below: 10pt, sticky: true,
            link(el.location(), text(size: 10pt, weight: "semibold", fill: blue, [
              #_star(size: 7pt)#h(7pt)第#numbering("一", part-number)部分 · #el.body
            ])))
        } else {
          block(width: 100%, above: 16pt, below: 10pt,
            link(el.location(), grid(
              columns: (28pt, 1fr, auto), column-gutter: 10pt, align: horizon,
              text(size: 18pt, fill: blue,
                _chapter-number(counter(heading).at(el.location()).first())),
              text(size: 12pt, weight: "semibold", fill: midnight, it.body()),
              outline-page(it.page()),
            )))
        }
      }
      show outline.entry.where(level: 2): it => {
        set text(size: 10pt, fill: muted)
        block(above: 6pt, below: 6pt,
          link(it.element.location(), it.indented(
            text(fill: blue, it.prefix()),
            [#it.body()#h(1fr)#box(outline-page(it.page()))],
            gap: 10pt)))
      }
      outline(title: none, indent: 38pt, depth: 2)
    })
  }

  doc
}

// ── Theorem environments ──────────────────────

#let _env(tag, label, color, title, body, numbering: true) = {
  let cnt = _env-counter(tag)
  let formal = tag in ("theorem", "lemma", "corollary", "proposition", "definition", "axiom")
  block(
    width: 100%, breakable: true,
    above: 12pt, below: 12pt,
    inset: (left: 12pt, right: 12pt, top: 10pt, bottom: 10pt),
    radius: (top-right: 2pt, bottom-right: 2pt),
    fill: if formal { color.lighten(96%) } else { none },
    stroke: (left: (if formal { 1.6pt } else { .7pt }) + color.lighten(12%)),
    // Preserve this wrapper/counter structure for labeled environment references.
    align(left, {
      if numbering { cnt.step() }
      context {
        let hs = counter(heading).get()
        let chapter = hs.at(0, default: 1)
        let section = hs.at(1, default: 0)
        let n = cnt.get().first()
        let number = _chapter-number(chapter) + "." + str(section) + "." + str(n)
        text(weight: "semibold", fill: color,
          label
          + if numbering { " " + number } else { "" }
          + if title != "" { "（" + title + "）" } else { "" }
          + ". "
        )
      }
      body
    }),
  )
}

#let theorem(body, title: "")    = _env("theorem",    "定理", c-thm, title, body)
#let lemma(body, title: "")      = _env("lemma",      "引理", c-thm, title, body)
#let proposition(body, title:"") = _env("proposition","命题", c-prop, title, body)
#let corollary(body, title: "")  = _env("corollary",  "推论", c-thm, title, body)
#let definition(body, title: "") = _env("definition", "定义", c-def, title, body)
#let axiom(body, title: "")      = _env("axiom",      "公理", c-def, title, body)
#let example(body, title: "")    = _env("example",    "例", c-con, title, body, numbering: false)
#let remark(body, title: "")     = _env("remark",     "注", c-rem, title, body, numbering: false)
#let question(body, title: "")   = _env("question",   "问题", c-def, title, body, numbering: false)

#let quote(body) = block(
  width: 100%, above: 15pt, below: 15pt,
  inset: (x: 16pt, y: 12pt), fill: mist, radius: 2pt,
  grid(
    columns: (18pt, 1fr), column-gutter: 5pt,
    text(font: latin-serif, size: 30pt, fill: accent.lighten(38%), "“"),
    text(fill: c-con, body),
  ),
)

#let _proof(label, body) = block(
  width: 100%, breakable: true, above: 7pt, below: 12pt,
  inset: (top: 2pt, bottom: 2pt),
  {
    text(weight: "semibold", size: 10pt, fill: muted, label + ". ")
    body
    h(1fr)
    box(square(size: 4.5pt, fill: none, stroke: .7pt + blue))
  },
)
#let proof(body) = _proof("证明", body)
#let proofsketch(body) = _proof("证明思路", body)
#let answer(body) = _proof("解答", body)

/* defines */

#let draw(path, width: 50%) = block(
  width: 100%,
  above: 1em,
  below: 1em,
  align(center, image(path, width: width)),
)

#let rightarrow = $stretch(->, size: #15pt)$
#let movebase(size, x) = text(baseline: size)[#x]
#let injlim = $display(limits(lim_(movebase(#(-1.9pt),rightarrow))))$
#let varinjlim(subscript) = $injlim_movebase(#(-2.8pt), subscript)$

#let leftarrow = $stretch(<-, size: #15pt)$
#let projlim = $display(limits(lim_(movebase(#(-1.9pt),leftarrow))))$
#let varprojlim(subscript) = $projlim_movebase(#(-2.8pt), subscript)$

#let neq(body) = math.equation(
  block: true,
  numbering: "(I)",
  body,
)

#let colim = $limits(op("colim"))$
#let Spec = $op("Spec")$
#let Frac = $op("Frac")$
#let Im = $op("im")$
#let Coeq = $op("coeq")$
#let res = $op("res")$
#let Eq = $op("Eq")$

#let act = $arrow.half.cw$
#let wedge = $or$
#let smash = $and$
#let coprod = $union.sq$
#let semidirect = $\u{22ca}$
#let pairarrow = $\u{21c9}$

#let GL = $"GL"$
#let SL = $"SL"$

#let et = "ét"
#let Ner = $"N"_bullet$
#let fib = $"fib"$
#let cofib = $"cofib"$
#let coker = $"coker"$
#let dg = $"dg"$

#let Hom = "Hom"
#let Map = "Map"
#let Cov = "Cov"
#let Desc = "Desc"
#let Mul = "Mul"
#let Der = "Der"
#let Aut = "Aut"
#let End = "End"
#let Lan = "Lan"
#let Ran = "Ran"
#let Pic = "Pic"
#let Ext = "Ext"
#let Tor = "Tor"
#let Nm = "Nm"
#let Gr = "Gr"
#let Hilb = "Hilb"
#let Quot = "Quot"
#let Assem = "Assem"
#let opp = "op"
#let pr = "pr"
#let ev = "ev"
#let Spf = "Spf"
#let CH = "CH"
#let yo = "よ"

#let Fun = $bold(sans("Fun"))$
#let BiFun = $bold(sans("BiFun"))$
#let Exc = $bold(sans("Exc"))$
#let Act = $bold(sans("Act"))$
#let Env = $bold(sans("Env"))$
#let Set = $bold(sans("Set"))$
#let Open = $bold(sans("Open"))$
#let PSh = $bold(sans("PSh"))$
#let Sh = $bold(sans("Sh"))$
#let LRep = $bold(sans("LRep"))$
#let Ab = $bold(sans("Ab"))$
#let Ring = $bold(sans("Ring"))$
#let CRing = $bold(sans("CRing"))$
#let Mod = $bold(sans("Mod"))$
#let QCoh = $bold(sans("QCoh"))$
#let Grp = $bold(sans("Grp"))$
#let Sch = $bold(sans("Sch"))$
#let Top = $bold(sans("Top"))$
#let LRS = $bold(sans("LRS"))$
#let Aff = $bold(sans("Aff"))$
#let Cat = $bold(sans("Cat"))$
#let Grpd = $bold(sans("Grpd"))$
#let Ani = $bold(sans("Ani"))$
#let St = $bold(sans("St"))$
#let PSt = $bold(sans("PSt"))$
#let sSet = $bold(sans("sSet"))$
#let CG = $bold(sans("CG"))$
#let QCat = $bold(sans("QCat"))$
#let Sp = $bold(sans("Sp"))$
#let Ch = $bold(sans("Ch"))$
#let dgCat = $bold(sans("dgCat"))$
#let Kcat = $bold(sans("K"))$
#let Dcat = $bold(sans("D"))$
#let Fin = $bold(sans("Fin"))$
#let Op = $bold(sans("Op"))$
#let POp = $bold(sans("POp"))$
#let Comm = $bold(sans("Comm"))$
#let Alg = $bold(sans("Alg"))$
#let CAlg = $bold(sans("CAlg"))$
#let Mon = $bold(sans("Mon"))$
#let CMon = $bold(sans("CMon"))$
#let AlgSp = $bold(sans("AlgSp"))$
#let DMSt = $bold(sans("DMSt"))$
#let ArtSt = $bold(sans("ArtSt"))$

#let cat(name) = $bold(sans(name))$

#let fork = $\u{22D4}$
#let lfork = math.attach(box(width: 0pt)[], t: $fork$)
#let odot = $\u{2299}$
#let wr = $\u{2240}$
