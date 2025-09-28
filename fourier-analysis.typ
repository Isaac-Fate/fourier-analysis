#import "mybook.typ": *
#show: mybook.with()

// Reset the heading counter
#counter(heading).update(0)


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

#include "content/02-basic-properties-of-fourier-series.typ"
#include "content/03-convergence-of-fourier-series.typ"


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

#bibliography("fourier-analysis.bib")
