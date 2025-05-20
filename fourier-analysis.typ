
#import "@preview/theorion:0.3.3": (
  cosmos,
  theorem,
  proposition,
  lemma,
  corollary,
  definition,
  note-box,
  warning-box,
  tip-box,
)
#import "@preview/theorion:0.3.3": (
  proof as theorion-proof,
  solution as theorion-solution,
  example as theorion-example,
  exercise as theorion-exercise,
)
#import cosmos.fancy: *
// #import cosmos.rainbow: *
// #import cosmos.clouds: *
#import "@preview/ctheorems:1.1.3": *
#import "@preview/in-dexter:0.7.0": *

#show: thmrules

#let proof = thmproof("proof", "Proof").with(inset: (top: 0em, left: 0em, right: 0em))
#let solution = thmproof("solution", "Solution").with(inset: (top: 0em, left: 0em, right: 0em))

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


#show: show-theorion

#set page(paper: "us-letter")
#set text(lang: "en")
#set par(
  first-line-indent: 1em,
  spacing: 0.65em,
  justify: true,
)


// Set the equation numbering
#set math.equation(
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
)


// Set the figure numbering
#set figure(
  numbering: n => {
    numbering("1.1", counter(heading).get().first(), n)
  },
)


// Change the counters and numbering:
#set-inherited-levels(1)
#set-zero-fill(true)
#set-leading-zero(true)
#set-theorion-numbering("1.1")


// Set the page layout
#show heading: it => {
  if it.level == 1 {
    // Reset the equation counter whenever a new chapter starts
    counter(math.equation).update(0)

    set text(size: 1.5em)
    let chapter_number = counter(heading).get().at(0)

    // Start a new page if this is not the first level 1 heading
    if page.numbering == "1" or chapter_number > 1 {
      pagebreak()
    }

    if page.numbering == "1" {
      set text(size: 1.6em)
      [$#math.bb(str(chapter_number))$]
      h(16pt)
    }

    it.body

    // Add vertical space below level 1 headings
    v(32pt)
  } else if it.level == 2 {
    it

    // Add vertical space below level 2 headings
    v(16pt)
  } else {
    it
  }
}

// Set the supplement to Chapter for level 1 headings
#show heading.where(level: 1): set heading(supplement: [Chapter])

// Set the outline
#show outline.entry: it => {
  if it.level == 1 {
    // Add vertical space above level 1 headings
    v(4pt)

    if it.element.location().page-numbering() != "1" {
      // set it.indented(gap: 0em)
      link(
        it.element.location(),
        // Keep just the inner
        it.inner(),
      )
    } else {
      it
    }
  } else {
    it
  }
}



// Reset the heading counter
#counter(heading).update(0)

// Set heading
#set heading(numbering: "1")


// Apply Roman numerals for preliminary pages
// before switching to standard numbering for the main content
#set page(numbering: "i")



#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge


= Preface






= Table of Contents

#outline(title: none)

#counter(heading).update(0)

// Set page numbering
#set page(numbering: "1")

// Reset page counter
#counter(page).update(1)

// Set heading
#set heading(numbering: "1.1")



/*
 * Main Content
 */

= Basic Properties of Fourier Series


== Formulation of the Problems

#figure()[
  #diagram(
    let (a, b) = ((-1, 0.5), (-0.2, 0.5)),
    node(a, $[a, b]$),
    node(b),
    edge(a, b, "->", shift: 3pt, $phi$),
    edge(b, a, "->", shift: 3pt, label-side: left, $phi^(-1)$),

    node((1, 1), $phi(a)$, name: <endpoint1>),
    node((0, 0), $phi(b)$, name: <endpoint2>),
    edge(<endpoint1>, <endpoint2>, "*->-*", bend: -45deg, $A$),
  )
]



== Main Definitions

#definition[
  Let $f$ be an integrable function on $[a, b]$.
  The $n$-th *Fourier coefficient* #index[Fourier coefficient] of $f$ is defined as
  $
    hat(f)(n) := 1 / L integral_a^b f(x) e^(-2pi i n x \/ L) dif x, quad n in Z.
  $
  where $L = b - a$ is length of the interval $[a, b]$.

  The *Fourier series* #index[Fourier series] of $f$ is defined _formally_ by
  $
    sum_(n = oo)^(oo) hat(f)(n) e^(2pi i n x \/ L).
  $
]

For any integrable function $f$, we write
$
  f(x) tilde sum_(n=-oo)^(oo) hat(f)(n) e^(2pi i n x \/ L)
$
to indicate that the RHS is the Fourier series of $f$.
Nothing is said about its convergence.

For instance, if $f$ is defined on $[-pi, pi]$, then the length of interval is $L=2pi$ and hence the general formulas can be simplified to
$
  hat(f)(n) = 1 / (2pi) integral_(-pi)^(pi) f(theta) e^(-i n theta) dif theta
$
and
$
  f(theta) tilde sum_(n=-oo)^(oo) hat(f)(n) e^(i n theta).
$

Similarly, if $f$ is defiend on $[0, 2pi]$, the formulas are the same except that we integrate from $0$ to $2pi$ for the Fourier coefficients.

We may oftern consider the Fourier series of a function on the circle.
As discussed, we may think of it as a $2pi$-periodic function on $RR$.
First, pick any interval of length $2pi$,
and then we will obtain the similar formulas as the previosue examples.
Question: Is there any issue?
If we first compute the Fourier coefficient $hat(f)(n)$ on $[-pi, pi]$.
And then do the same on $[0, 2pi]$, obtaining coefficient $hat(f)^prime (n)$.
Are the two coefficients necessarily the same?
Fortunately, @ex:1 shows that indeed $hat(f)(n) = hat(f)^prime (n)$.
Therefore, the Fourier coefficients of functions on the circle are well defined.

As a last example,
sometimes we shall consider function $g$ defined on $[0, 1]$.
In this case, the length of the interval is $L=1$.
The $n$-th Fourier coefficients of $g$ is
$
  hat(g)(n) = integral_0^1 g(x) e^(-2pi i n x) dif x.
$

#exercise[
  Suppose $f$ is $2pi$-periodic and is integrable on any closed interval.
  Prove that if $a, b in RR$, then
  $
    integral_a^b f(x) dif x
    = integral_(a + 2pi)^(b + 2pi) f(x) dif x
    = integral_(a - 2pi)^(b - 2pi) f(x) dif x.
  $ <eq:1>
  Also prove that
  $
    integral_(-pi)^pi f(x + a) dif x
    = integral_(-pi)^pi f(x) dif x
    = integral_(-pi + a)^(pi + a) f(x) dif x.
  $ <eq:2>
] <ex:1>

#note-box[
  @eq:1 states that for any fixed interval [a,b], the integral of a 2π-periodic function remains invariant under a shift of the interval by 2π.

  @eq:2 generalizes this result: for any interval of length 2π, the integral preserves its value. Intuitively, if we slide a "window" of width 2π along the real line, the integral over this window remains constant.
]

#proof[
  We first prove @eq:1.
  Applying the change of variables $t = x - 2pi$, we obtain
  $
    integral_(a + 2pi)^(b + 2pi) f(x) dif x
    = integral_a^b f(t + 2pi) dif t
    = integral_a^b f(t) dif t
  $
  where the last equality follows from the $2pi$-periodicity of $f$.
  Similarly, substituting $t = x + 2pi$ yields
  $integral_(a - 2pi)^(b - 2pi) f(x) dif x = integral_a^b f(t) dif t$.

  Next, we prove @eq:2.
  Note that the equation
  $
    integral_(-pi)^pi f(x + a) dif x
    = integral_(-pi + a)^(pi + a) f(x) dif x
  $
  can be obtained easily by applying the change of variables $t = x + a$.
  Now, we want to show
  $
    integral_(-pi + a)^(pi + a) f(x) dif x
    = integral_(-pi)^pi f(x) dif x.
  $
  Breaking the integral $integral_(-pi + a)^(pi + a) f(x) dif x$ into two parts, we have
  $
    integral_(-pi + a)^(pi + a) f(x) dif x
    &= integral_(-pi + a)^pi f(x) dif x + integral_pi^(pi + a) f(x) dif x \
    &"Subtracting" 2pi "from both upper and lower limits of ther last term" \
    &"will preserve the integral, which is what we just proved." \
    &= integral_(-pi + a)^pi f(x) dif x + integral_(pi - 2pi)^(pi + a - 2pi) f(x) dif x \
    &= integral_(-pi + a)^pi f(x) dif x + integral_(-pi)^(-pi + a) f(x) dif x \
    &= integral_(-pi)^pi f(x) dif x
  $
  This completes the proof.
]




To study the convergence of Fourier series, we need to introduce the concept of *partial sums* #index[partial sum of Fourier series].
The $N$-th partial sum $S_N (f)$ of the Fourier series of a function $f$ is given by the sum of the terms whose indices range from $-N$ to $N$. That is,
$
  S_N (f)(x) := sum_(n=-N)^(N) hat(f)(n) e^(2pi i n x \/ L).
$
We say the Fourier series $sum_(n=-oo)^(oo) hat(f)(n) e^(2pi i n x \/ L)$
converges if the limit of $S_N (f) (x)$ exists (as a finite number) as $N -> oo$.

Fourier serires are part of a larger family called *trigonometric series* #index[trigonometric series], which has the form
$
  sum_(n=-oo)^oo c_n e^(2pi i n x \/ L), quad "where" c_n in CC.
$
If a trigonometric series only consists of finitely many terms,
then it is called a *trigonometric polynomial* #index[trigonometric polynomial].
The *degree* #index[degree of a trigonometric polynomial] of a trigonometric polynomial
is the largest value of $abs(n)$ for which $c_n != 0$.

#example[
  The trigonometric polynomial defined for $x in [-pi, pi]$ by
  $
    D_N (x) := sum_(n=-N)^(N) e^(i n x)
  $
  is called the *Direchlet kernel* #index[Direchlet kernel],
  which is of fundamental importance in the theory of Fourier analysis.

  A closed form of $D_N (x)$ is
  $
    D_N (x) = sin((N + 1 / 2) x) / sin(x / 2).
  $
  This can be derived by considering $omega = e^(i x)$ and splitting the sum
  $
    D_N (x) = sum_(n=0)^N omega^n + sum_(n=-N)^(-1) omega^n.
  $
  #tip-box[
    We have the folloing properties
    1. $omega^n + omega^(-n) = 2 cos(n x)$, and
    2. $omega^n - omega^(-n) = 2 i sin(n x)$ where $n in ZZ$.
  ]
]

== Uniqueness of Fourier Series


#lemma[
  Let $f$ be an integrable function on the circle.
  If $hat(f) (n) = 0$ for all $n in ZZ$,
  then we also have
  $
    integral_(-pi)^pi f(theta) T(theta) dif theta = 0
  $
  where $T(theta)$ is any trigonometric polynomial.
] <lem:1>

#proof[
  Let $T(theta)$ be an arbitray trigonometric polynomial.
  It can be written as $T(theta) = sum_(n=-N)^N c_n e^(-i n theta)$.
  (Well, whether the exponent is $i n theta$ or $-i n theta$ is inconsequential because we can always replace $n$ with $-n$ and relabel the summation indices accordingly.)

  Because $hat(f) (n) = 0$ for all $n in ZZ$, we have
  $
    integral_(-pi)^pi f(theta) e^(-i n theta) dif theta = 0 quad forall n in ZZ.
  $
  Multiplying both sides by $c_n$ and then summing over $n$ yields
  $
    sum_(n=-N)^N c_n integral_(-pi)^pi f(theta) e^(-i n theta) dif theta = 0.
  $
  We may moving $c_n$ inside the integral and then swapping the order of integration and summation to obtain
  $
    integral_(-pi)^pi f(theta) sum_(n=-N)^N c_n e^(-i n theta) dif theta = 0.
  $
  This is exactly $integral_(-pi)^pi f(theta) T(theta) dif theta = 0$.
]

#theorem[
  Suppose $f$ is an integrable fucntion on the circle
  with $hat(f) (n) = 0$ for all $n in ZZ$.
  Then $f(theta_0) = 0$ if $f$ is continuous at $theta_0$.
]

#proof[
  Without loss of generality, we may assume that $theta_0 = 0$ and restrict ourselves to the interva $[-pi, pi]$. (Why? Justify this with @ex:1.)
  We have
  $
    hat(f) (n) = integral_(-pi)^pi f(theta) e^(-i n theta) dif theta = 0 quad forall n in ZZ.
  $

  By @lem:1 we know that
  $
    integral_(-pi)^pi f(theta) T(theta) dif theta = 0
  $ <eq:3>
  for any trigonometric polynomial $T$.

  We shall prove this theorem by contradiction.
  Assume that $f$ is continuous at $theta_0 = 0$ but $f(0) != 0$.
  Without loss of generality, we may assume that $f(0) > 0$.
  Our goal is to construct a sequence of trigonometric polynomials ${T_k}_(k in NN^ast)$ such that
  $
    integral_(-pi)^pi f(theta) T_k (theta) dif theta > 0
  $
  for a large enough $k$, which would contradict @eq:3.


  Since $f(0) > 0$ and $f$ is continuous at $0$,
  $f$ must remain positive in some small neighborhood around $0$.
  In fact, we can say something stronger.
  There exists some neighborhood of $0$
  where $f$ is not just positive but actually bounded below by a fixed positive constant, say $f(0) \/ 2$.
  Mathematically, this means that there exists a sufficiently small $delta > 0$ such that
  $delta < pi \/ 2$ and
  $
    f(theta) > f(0) / 2 quad "whenever" |theta| < delta.
  $
  #note-box[
    The reason why we enforce $delta < pi \/ 2$ is related to the construction of $T_k (theta)$, which we will see shortly.
  ]

  We now have a positive lower bound for $f$ on $[-delta, delta]$, namely$f(0) \/ 2$.
  On the _tails_ $[-pi, -delta]$ and $[delta, pi]$, we lack precise control over $f$---though no control is an exaggeration.
  Since $f$ is integrable, it must be bounded.
  Let's assume $abs(f) <= A$ on $[-pi, pi]$ for some $A > 0$.

  For the construction of $T_k (theta)$, we want two things:
  1. In the middle interval $[-delta, delta]$,
  $f(theta) T_k (theta)$ remains postive, and its integral grows as $k$ increases.
  2. On the tails $[-pi, -delta]$ and $[delta, pi]$:
  $f(theta) T_k (theta)$ damps out, ensuring that even if even if
  $
    integral_(delta)^pi f(theta) T_k (theta) dif theta + integral_(-pi)^(-delta) f(theta) T_k (theta) dif theta < 0,
  $
  this negative contribution cannot outweigh the dominant positive term
  $
    integral_(-delta)^delta f(theta) T_k (theta) dif theta.
  $

  Here, we first reveal the simple construction.
  Let
  $
    T(theta) = epsilon + cos(theta) "and" T_k (theta) = T^k (theta)
  $
  where $epsilon$ satisfies that
  $
    0< epsilon < (2(1 - cos delta) ) / 3.
  $ <eq:4>
  One can verify that
  $
    abs(T(theta)) < 1 - epsilon / 2 quad "whenever" delta <= abs(theta) <= pi
  $ <eq:5>
  #note-box[
    Actually, the condition @eq:4 is specifically designed to ensure that @eq:5 holds.
    This is achieved by solving for $epsilon$ through the inequality:
    $
      abs(epsilon + cos theta) < 1 - epsilon / 2 quad forall theta in [delta, pi].
    $
  ]

  For a general sense of the behavior of $T_k (theta)$ looks refer to @fig:1 for an illustrative example.

  #figure(caption: [$T_k (theta)$ defined on $[-pi, pi]$ with $epsilon = 0.1$.])[
    #image("images/sequence-of-trigonometric-polynomials.png", width: 70%)
  ] <fig:1>


  Note that $T(theta)$ attains its maximum $epsilon + 1$ at $theta = 0$.
  Since it is continuous, there exists $0 < eta < delta$ such that
  $
    T(theta) > 1 + epsilon / 2 quad "whenever" abs(theta) < eta.
  $

  Therefore, we have:
  1. When $|theta| < eta$,
  $
    f(theta) T_k (theta) > f(0) / 2 (1 + epsilon / 2)^k.
  $
  The RHS tends to $oo$ as $k -> oo$.

  2. When $eta <= |theta| < delta$,
  $
    f(theta) T_k (theta) > 0.
  $

  3. When $delta <= |theta| <= pi$,
  $
    abs(f(theta) T_k (theta)) < A (1 - epsilon / 2)^k. quad ("Recall that" abs(f) <= A.)
  $
  The RHS tends to $0$ as $k -> oo$.

  Then, it is easy to find some large enough $k$ that
  $
    &integral_(-pi)^pi f(theta) T_k (theta) dif theta \
    = &integral_(-eta)^eta f(theta) T_k (theta) dif theta \
    &+ integral_(-delta)^(-eta) f(theta) T_k (theta) dif theta
    + integral_(eta)^(delta) f(theta) T_k (theta) dif theta \
    &+ integral_(-pi)^(-delta) f(theta) T_k (theta) dif theta
    + integral_(delta)^(pi) f(theta) T_k (theta) dif theta \
    >&0
  $
  This contradicts @eq:3, completing the proof.
]


= Index

#columns(2)[
  #make-index(title: none, outlined: true, use-page-counter: true)
]
