#import "mybook.typ": *
#show: mybook.with()

#import "@preview/fauxreilly:0.1.1": orly

#orly(
  color: rgb("#85144b"),
  title: "Fourier Analysis",
  top-text: "",
  subtitle: "",
  pic: image("/assets/images/cover.png", width: 100%, height: 30em, fit: "cover"),
  signature: "Isaac Fei",
  publisher: none,
)



// Force next page for main content
#pagebreak()

// Reset the heading counter
#counter(heading).update(0)

// Reset the page counter
#counter(page).update(1)

// Apply Roman numerals for preliminary pages
// before switching to standard numbering for the main content
#set page(numbering: "i")

#set heading(numbering: none)


= Preface

This is a notebook for Stein's Fourier Analysis: An Introduction @steinFourierAnalysisIntroduction2003.




= Table of Contents

#outline(title: none)



// Set page numbering
#set page(numbering: "1")

// Reset page counter
#counter(page).update(1)

// Set heading
#set heading(numbering: "1.1")



/*
 * Main Content
 */

#include "/chapters/02-basic-properties-of-fourier-series.typ"
#include "/chapters/03-convergence-of-fourier-series.typ"


/*
 * Index
 */

#set heading(numbering: none)

= Index

#columns(2)[
  #make-index(title: none, outlined: true, use-page-counter: true)
]



/*
 * Bibliography
 */

#bibliography("/references.bib")
