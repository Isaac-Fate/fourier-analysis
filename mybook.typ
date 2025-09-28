
// ------------------------------
// Imports
// ------------------------------

#import "@preview/theorion:0.3.3": (
  corollary, cosmos, definition, lemma, note-box, proposition, theorem, tip-box, warning-box,
)
#import "@preview/theorion:0.3.3": (
  example as theorion-example, exercise as theorion-exercise, proof as theorion-proof, solution as theorion-solution,
)
#import cosmos.fancy: *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/in-dexter:0.7.0": *

// Diagrams
#import "@preview/fletcher:0.5.7" as fletcher: diagram, edge, node

// ------------------------------
// Global variables
// ------------------------------

#let proof = thmproof("proof", "Proof").with(inset: (top: 0em, left: 0em, right: 0em))
#let solution = thmproof("solution", "Solution").with(inset: (top: 0em, left: 0em, right: 0em))
#let proof-sketch = thmproof("proof-sketch", "Proof Sketch").with(
  inset: (top: 0em, left: 0em, right: 0em),
)

#let example = thmplain("example", "Example").with(
  base_level: 1,
  inset: (top: 0em, left: 0em, right: 0em),
  numbering: "1.1",
)

#let exercise = thmplain("exercise", "Exercise").with(
  base_level: 1,
  inset: (top: 0em, left: 0em, right: 0em),
  numbering: "1.1",
)

// ------------------------------
// Template
// ------------------------------

#let mybook(doc) = {
  show: thmrules
  show: show-theorion

  set page(paper: "us-letter")
  set text(lang: "en")
  set par(
    first-line-indent: 1em,
    spacing: 0.65em,
    justify: true,
  )

  // Set the equation numbering
  set math.equation(
    numbering: n => {
      numbering("(1.1)", counter(heading).get().first(), n)
      // if you want change the number of number of displayed
      // section numbers, modify it this way:
      /*
      let count = counter(heading).get()
      let h1 = count.first()
      let h2 = count.at(1, default: 0)
      numbering("(1.1.1)", h1, h2, n)
      */
    },

    // Don't need supplement since not every mathematical formula is an equation
    supplement: none,
  )


  // Set the figure numbering
  set figure(numbering: n => {
    numbering("1.1", counter(heading).get().first(), n)
  })


  // Change the counters and numbering:
  set-inherited-levels(1)
  set-zero-fill(true)
  set-leading-zero(true)
  set-theorion-numbering("1.1")


  // Set the page layout
  show heading: it => {
    if it.level == 1 {
      // Reset the equation counter whenever a new chapter starts
      counter(math.equation).update(0)

      set text(size: 1.5em)
      let chapter_number = counter(heading).get().at(0)

      // // Start a new page if this is not the first level 1 heading
      // if page.numbering == "1" or chapter_number > 1 {
      //   pagebreak()
      // }
      pagebreak()

      if heading.numbering == "1.1" {
        set text(size: 1.6em)
        [$#math.bb(str(chapter_number))$]
        h(16pt)
      }

      it.body

      // Add vertical space below level 1 headings
      v(32pt)
    } else if it.level == 2 {
      // Add vertical space above level 2 headings
      v(16pt)

      it

      // Add vertical space below level 2 headings
      v(8pt)
    } else {
      it
    }
  }

  // Set the supplement to Chapter for level 1 headings
  show heading.where(level: 1, numbering: "1.1"): set heading(supplement: [Chapter])

  // Set the outline
  show outline.entry: it => {
    if it.level == 1 {
      // Add vertical space above level 1 headings
      v(4pt)
      it
    } else {
      it
    }
  }

  set image(width: 70%)

  doc
}
