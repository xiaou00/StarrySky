#import "template.typ": *

#show: doc => conf(
  title: [
    Starry Sky
  ],
  subtitle: [
    代数几何深耕
  ],
  author: "xiaou0",
  date: "2026",
  cover-image: "cover.png",
  doc,
)

#part[高阶对象]

#include "chapters/c001.typ"

#include "chapters/c002.typ"

#include "chapters/c003.typ"

#include "chapters/c004.typ"

#include "chapters/c005.typ"

#include "chapters/c006.typ"

#part[代数 $K$-理论]

#include "chapters/c007.typ"

#include "chapters/c008.typ"

#include "chapters/c009.typ"

#part[附录]

#appendix[
  #include "chapters/a001.typ"

  #include "chapters/a002.typ"
]

#references("references.bib")

