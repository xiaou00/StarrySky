#import "template.typ": *

#show: doc => conf(
  title: [
    Starry Sky
  ],
  subtitle: [
    几何 / 拓扑 / 数论
  ],
  author: "xiaou0",
  date: "2026",
  cover-image: "cover.png",
  doc,
)

#part[高阶对象]

#include "chapters/c001.typ"

#include "chapters/c002.typ"

#references("references.bib")
