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

#references("references.bib")
