
#import "../mybook.typ": *
#show: mybook.with()


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
$ <eq:25>
If a trigonometric series only consists of finitely many terms,
then it is called a *trigonometric polynomial* #index[trigonometric polynomial].
The *degree* #index[degree of a trigonometric polynomial] of a trigonometric polynomial
is the largest value of $abs(n)$ for which $c_n != 0$.

#example[
  The trigonometric polynomial defined for $x in [-pi, pi]$ by
  $
    D_N (x) := sum_(n=-N)^(N) e^(i n x)
  $
  is called the *Dirichlet kernel* #index[Dirichlet kernel],
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

Weierstrass's M-test is a very helful test to examine whether a series is uniformly convergent.

#theorem(title: "Weierstrass's M-test")[
  Let $sum f_n (x)$ be a series of functions defined on $S subset.eq CC$.
  And let ${M_n}$ be a sequence of non-negative numbers such that
  $
    abs(f_n (x)) <= M_n quad forall x in S, forall n in NN^ast.
  $
  Then $sum f_n (x)$ converges absolutely and uniformly on $S$ if $sum M_n$ converges.
] <thm:4>

#example[
  The function $P_r (theta)$, called the *Poisson kernel* #index[Poisson kernel],
  is defined by
  $
    P_r (theta) = sum_(n=-oo)^oo r^(abs(n)) e^(i n theta), quad theta in [-pi, pi]
  $ <eq:33>
  where $r$ satisfies $0 <= r < 1$.
  Note that the series in @eq:33 converges absolutely and uniformly on $[-pi, pi]$.
  One can verify this using Weierstrass's M-test (@thm:4).

  The closed form of $P_r (theta)$ is
  $
    P_r (theta) = (1 - r^2) / (1 - 2 r cos(theta) + r^2).
  $
  In fact, letting $omega = r e^(i n theta)$, we can write
  $
    P_r (theta)
    = sum_(n=-oo)^oo r^(abs(n)) e^(i n theta)
    = sum_(n=0)^oo omega^n + sum_(n=1)^oo overline(omega)^n.
  $
  The RHS is just the sum of two geometirc series. We have
  $
    P_r (theta)
    = 1 / (1 - omega) + overline(omega) / (1 - overline(omega))
    = (1 - abs(omega)^2) / ((1 - omega)(1 - overline(omega)))
    = (1 - r^2) / (1 - 2 r cos(theta) + r^2).
  $
] <eg:1>

== Uniqueness of Fourier Series

If we assume that the Fourier series of a function $f$ converges to $f$ under certain conditions, a natural question arises: is $f$ uniquely determined by its Fourier coefficients? In other words, if $hat(f) (n) = hat(g) (n)$ for all $n in ZZ$, does it follow that $f = g$ (under appropriate conditions)?

To investigate this, consider the difference $h = f - g$. The problem then reduces to determining whether $h=0$ whenever its Fourier coefficients vanish, i.e., $hat(h) (n) = 0$ for all $n in ZZ$.

To better exploit the condition
$
  hat(f) (n) = 1 / (2pi) integral_(-pi)^pi f(theta) e^(-i n theta) dif theta = 0 quad forall n in ZZ,
$
we first show the following lemma.

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
  Suppose $f$ is an integrable complex-valued fucntion on the circle
  with $hat(f) (n) = 0$ for all $n in ZZ$.
  Then $f(theta_0) = 0$ if $f$ is continuous at $theta_0$.
] <thm:1>

#proof[
  It suffices to prove this theorem for real-value functions.
  Having proved that, we may write
  $
    f(theta) = u(theta) + i v(theta)
  $
  where
  $
    u(theta) = (f(theta) + overline(f(theta))) / 2
    quad "and" quad
    v(theta) = (f(theta) - overline(f(theta))) / 2
  $
  are real-valued functions, which immediately implies that this theorem also holds for complex-valued functions.

  Assume $f$ is real-valued.
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
    T(theta) = epsilon + cos theta "and" T_k (theta) = T^k (theta)
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
    #image("/assets/figures/sequence-of-trigonometric-polynomials.png", width: 70%)
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
    f(theta) T_k (theta) >= 0.
  $

  3. When $delta <= |theta| <= pi$,
  $
    abs(f(theta) T_k (theta)) < A (1 - epsilon / 2)^k. quad ("Recall that" abs(f) <= A.)
  $
  The RHS tends to $0$ as $k -> oo$.

  Then, it is easy to find some large enough $k$ that
  $
      & integral_(-pi)^pi f(theta) T_k (theta) dif theta \
    = & integral_(-eta)^eta f(theta) T_k (theta) dif theta \
      & + integral_(-delta)^(-eta) f(theta) T_k (theta) dif theta
        + integral_(eta)^(delta) f(theta) T_k (theta) dif theta \
      & + integral_(-pi)^(-delta) f(theta) T_k (theta) dif theta
        + integral_(delta)^(pi) f(theta) T_k (theta) dif theta \
    > & 0
  $
  This contradicts @eq:3, completing the proof.
]

#note-box[
  Constructing a sequence of functions like $T_k (theta)$ which peak at the origin, together with other nice properties is a common and useful technique of conducting proofs in the study of Fourier analysis.
]

#corollary[
  If $f$ is continuous on a circle
  and $hat(f) (n) = 0$ for all $n in ZZ$, then $f = 0$.
]

Therefore, we have a positive answer to the problem we raised in the beginning of this section.
If $f$ and $g$ are continuous functions on the circle and their Fourier coefficients are equal, $hat(f) (n) = hat(g) (n)$ for all $n in ZZ$, then these two functions are identical, $f = g$.

#corollary[
  Suppose that $f$ is continuous on a circle and
  that the Fourier series of $f$ is absolutely convergent,
  $sum_(n=-oo)^oo abs(hat(f) (n)) < oo$.
  Then, the Fourier series converges uniformly to $f$, i.e.,
  the sequence of functions ${S_N (f) (theta)}$
  converges uniformly to $f$ on $[-pi, pi]$.
] <cor:1>

#proof[
  Consider function $g$ defined by
  $
    g(theta) = sum_(n=-oo)^oo hat(f) (n) e^(i n theta).
  $ <eq:6>
  Note that the series on the RHS of @eq:6 converges absolutely since
  $
    abs(hat(f) (n) e^(i n theta))
    = abs(hat(f) (n)) abs(e^(i n theta))
    = abs(hat(f) (n)) dot 1
    = abs(hat(f) (n)).
  $

  Furthermore, we want to show that this series converges uniformly to $g$.
  Let $epsilon > 0$ be arbitray.
  Since $sum hat(f) (n)$ converges absolutely,
  there exists $N in NN^*$ such that
  $
    sum_(n=N)^oo abs(hat(f) (n)) + sum_(-oo)^(-N) abs(hat(f) (n)) < epsilon
  $
  It then follows that for all $M >= N$, we have
  $
    abs(sum_(n=M)^oo hat(f) (n) e^(i n theta) + sum_(n=-oo)^(-M) hat(f) (n) e^(i n theta))
    &<= sum_(n=M)^oo abs(hat(f) (n) e^(i n theta)) + sum_(-oo)^(-M) abs(hat(f) (n) e^(i n theta)) \
    &<= sum_(n=N)^oo abs(hat(f) (n) e^(i n theta)) + sum_(-oo)^(-N) abs(hat(f) (n) e^(i n theta)) \
    &<= sum_(n=N)^oo abs(hat(f) (n)) + sum_(-oo)^(-N) abs(hat(f) (n)) \
    &< epsilon
  $
  This proves that $sum_(n=-oo)^oo hat(f) (n) e^(i n theta)$ converges uniformly to $g$ on $[-pi, pi]$.

  Becauase each partial sum $S_N (g) (theta) = sum_(n=-N)^N hat(f) (n) e^(i n theta)$
  is a continuous fucntion and $S_N (g) (theta)$ converges uniformly to $g$ on $[-pi, pi]$ (already proved),
  function $g$ itself must also be continuous (uniform limit theorem).

  Now, we compute $g$'s Fourier coefficients.
  $
    hat(g) (n) & = 1 / (2pi) integral_(-pi)^pi g(theta) e^(-i n theta) dif theta \
               & = 1 / (2pi) integral_(-pi)^pi sum_(k=-oo)^oo hat(f) (k) e^(i k theta) e^(-i n theta) dif theta \
               & "We may interchange the order of integration and summation" \
               & "since the series converges uniformly." \
               & = 1 / (2pi) sum_(k=-oo)^oo integral_(-pi)^pi hat(f) (k) e^(i k theta) e^(-i n theta) dif theta \
               & = 1 / (2pi) sum_(k=-oo)^oo hat(f) (k) integral_(-pi)^pi e^(i (k-n) theta) dif theta \
  $ <eq:7>
  The value of the intergal $integral_(-pi)^pi e^(i (k-n) theta) dif theta$ is
  $
    integral_(-pi)^pi e^(i (k-n) theta) dif theta
    = cases(2pi "if" k = n, lr(1 / (i(k-n))e^(i (k-n) theta) |)_(-pi)^pi = 0 "if" k != n),
  $ <eq:8>
  In other words, it evaluates to $2pi$ only when $k=n$ and otherwise vanishes.

  Combining @eq:7 with @eq:8, we obtain
  $
    hat(g) (n) = 1 / (2pi) hat(f) (n) dot 2pi = hat(f) (n).
  $
  Therefore, by @thm:1, $f = g$, which means ${S_N (f) (theta)}$ converges uniformly to $f$ on $[-pi, pi]$.
]

The result of @cor:1 is elegant because it guarantees that the Fourier series of $f$ converges to $f$ uniformly in $theta$, provided the series itself is absolutely convergent.

However, a natural follow-up question arises: How can we verify the absolute convergence of the Fourier series? Ideally, we would prefer a condition that is directly imposed on $f$ rather than its Fourier coefficients.

This is precisely the focus of the following corollary.
Short answer: A sufficient condition is $f$ being twice continuously differentiable.

#corollary[
  Suppose $f$ is a twice continuously differentiable function on the circle, i.e., $f in C^2$.
  Then
  $
    hat(f) (n) = O(1 / abs(n)^2) quad "as" n -> oo.
  $
  In this case, the Fourier series converges _absolutely_ and uniformly to $f$.
]

#proof[
  The key step in this proof is the application of integration by parts.
  Since we are considering the regime where $abs(n)$ is large, we implicitly assume $n != 0$.
  The first application of integration by parts yields
  $
    2pi hat(f) (n) & = lr(f(theta) 1 / (-i n) e^(-i n theta) |)_(-pi)^pi
                     - integral_(-pi)^pi f'(theta) 1 / (-i n) e^(-i n theta) dif theta \
                   & = 1 / (i n) integral_(-pi)^pi f'(theta) e^(-i n theta) dif theta.
  $ <eq:9>

  Applying integration by parts again, we obtain
  $
    1 / (i n) integral_(-pi)^pi f'(theta) e^(-i n theta) dif theta
    &= lr(f'(theta) 1 / (n^2) e^(-i n theta) |)_(-pi)^pi
    -integral_(-pi)^pi f''(theta) 1 / (n^2) e^(-i n theta) dif theta\
    &= -1 / (n^2) integral_(-pi)^pi f''(theta) e^(-i n theta) dif theta.
  $

  Therefore, we have
  $
    2pi hat(f) (n)
    = -1 / (n^2) integral_(-pi)^pi f''(theta) e^(-i n theta) dif theta.
  $
  Take the modulus of both sides and we will have the following estimate:
  $
    2pi abs(hat(f) (n)) & = 1 / (abs(n)^2) abs(integral_(-pi)^pi f''(theta) e^(-i n theta) dif theta) \
                        & <= 1 / (abs(n)^2) integral_(-pi)^pi abs(f''(theta) e^(-i n theta)) dif theta \
                        & = 1 / (abs(n)^2) integral_(-pi)^pi abs(f''(theta)) dif theta \
                        & "Since" f'' "is continuous, so is" abs(f''), "and thus" \
                        & abs(f'') "attains its maximum" M "on" [-pi, pi]. \
                        & <= 1 / (abs(n)^2) 2pi M \
  $
  It then follows that
  $
    abs(hat(f) (n)) <= M / (abs(n)^2).
  $
  In the big $O$ notation, this means exactly that $abs(hat(f) (n)) = O(1 / abs(n)^2)$.

  Because the series $sum_(n=-oo)^oo 1 / (abs(n)^2)$ converges,
  the series $sum_(n=-oo)^oo abs(hat(f) (n))$ also converges by the comparison test.
  Then, by @cor:1, the Fourier series of $f$ converges uniformly to $f$ in $theta$.
]

#note-box[
  @eq:9 gives us a by-product that
  $
    i n hat(f) (n) = hat(f') (n).
  $
  We have already shown this for $n != 0$.
  The case where $n = 0$ can be proved easily by a simple calculation.
]



== Convolutions

#definition[
  Given two $2pi$-periodic integrable functions $f$ and $g$ on $RR$,
  their *convolution* #index[convolution] is defined by
  $
    (f * g) (x) = 1 / (2pi) integral_(-pi)^pi f(y) g(x - y) dif y, quad x in [-pi, pi].
  $ <eq:10>
]

Note that @eq:10 is well-defined for each $x$ since the product of two integrable functions
is also integrable.

The following are some basic properties of convolutions.

#proposition[
  Let $f$, $g$ and $h$ be $2pi$-periodic integrable functions on $RR$.
  Then we have:
  1. $f * (g + h) = f * g + f * h$.
  2. $(c f) * g = c (f * g) = f * (c g)$ for any $c in CC$.
  3. $f * g = g * f$.
  4. $(f * g) * h = f * (g * h)$.
  5. $f * g$ is continuous.
  6. $hat(f * g) (n) = hat(f) (n) hat(g) (n)$.
]

The first four statements outline key algebraic properties of convolutions: 1 and 2 express the linearity, which follows directly from the linearity of integration;
3 states the commutativity,
and 4 states the associativity.

Statement 5 says that the convolution $f * g$ is continuous
though $f$ and $g$ are merely integrable, which means that taking the convolution will produce a nicer and smoother function in some sense.

Finally, statement 6 shows that the $n$-th Fourier coefficient of the convolution $f * g$ is the product of the $n$-th Fourier coefficients of $f$ and $g$. Formally, applying the _hat_ operator over the convolution will split it into a product.

In the following, we only prove 3 and 4.
1 and 2 are immedate consequence of the linearity of integration and the commutativity of convolutions.
The proofs of statement 5 and 6 are more involved and will be given separately with a few preparations.

In the following, we will only prove statements 3 and 4.
Statements 1 and 2 follow immediately from the linearity of integration.
While the proofs of statements 5 and 6 require additional technical preparations and will be addressed separately.


#proof[

  *Proof of 3:*


  *Proof of 4:* We have
  $
    ((f * g) * h) (x) & = 1 / (2pi) integral_(-pi)^pi (f * g)(y) dot h(x-y) dif y \
                      & = 1 / (2pi) integral_(-pi)^pi (1 / (2pi) integral_(-pi)^pi f(u) g (y - u) dif u) h(x-y) dif y \
                      & = 1 / (2pi)^2 integral_(-pi)^pi integral_(-pi)^pi f(u) g (y - u) h(x-y) dif u dif y.
  $ <eq:11>
  Because the integrand is continuous throughout the rectange $[-pi, pi] times [-pi, pi]$,
  by a simple version of the first form of Fubini's theorem stated in @weirThomasCalculusEarly2014, we may switch the order of integration in @eq:11.
  We have
  $
    &&   & 1 / (2pi)^2 integral_(-pi)^pi integral_(-pi)^pi f(u) g (y - u) h(x-y) dif u dif y \
    && = & 1 / (2pi)^2 integral_(-pi)^pi integral_(-pi)^pi f(u) g (y - u) h(x-y) dif y dif u \
    && = & 1 / (2pi) integral_(-pi)^pi f(u) (1 / (2pi) integral_(-pi)^pi g (y - u) h(x-y) dif y) dif u. \
    &&   & "Substitute" y = v + u. \
    && = & 1 / (2pi) integral_(-pi)^(pi) f(u) (1 / (2pi) integral_(-pi-u)^(pi-u) g (v) h(x-u-v) dif v) dif u \
    && = & 1 / (2pi) integral_(-pi)^(pi) f(u) (1 / (2pi) integral_(-pi)^(pi) g (v) h(x-u-v) dif v) dif u \
    && = & 1 / (2pi) integral_(-pi)^(pi) f(u) dot (g * h) (x-u) dif u \
    && = & (f * (g * h)) (x).
  $
]

We begin by proving statement 5 for the special case of continuous functions.
Specifically, we will show that the convolution $f * g$ is continuous under the assumption that both $f$ and $g$ are continuous functions on the circle.

#proof[
  Since $f$ is integrable on the circle, it is bounded.
  Suppose that $abs(f) <= M$ for some $M > 0$.

  Let $epsilon > 0$ be given.
  Because $g$ is continuous on $[-pi, pi]$, it is uniformly continuous there.
  Thus we can find $delta > 0$ such that
  $
    abs(g(u) - g(v)) < epsilon / M quad "whenever" quad abs(u - v) < delta
  $
  for any $u, v in [-pi, pi]$.

  Now take any $x_1, x_2 in [-pi, pi]$ with $abs(x_1 - x_2) < delta$.
  We estimate:
  $
    abs((f * g)(x_1) - (f * g)(x_2)) & = 1 / (2pi) abs(integral_(-pi)^pi f(y) [g(x_1 - y) - g(x_2 - y)] dif y) \
                                     & <= 1 / (2pi) integral_(-pi)^pi abs(f(y)) abs(g(x_1 - y) - g(x_2 - y)) dif y \
                                     & <= M / (2pi) integral_(-pi)^pi abs(g(x_1 - y) - g(x_2 - y)) dif y \
                                     & < M / (2pi) dot (epsilon / M) dot 2pi \
                                     & = epsilon.
  $

  This shows that $f * g$ is uniformly continuous on $[-pi, pi]$.
]

To relax these continuity assumptions and consider the case where $f$ and $g$ are merely integrable, we require the following approximation lemma. This result allows us to approximate an integrable function with a sequence of continuous functions.

#lemma[
  Suppose that $f$ is an integrable function on the circle and is bounded by $M > 0$.
  Then there exists a sequence of continuous functions ${f_n}_(n=1)^oo$ such that
  $
    sup_(x in [-pi, pi]) abs(f_n (x)) <= M quad forall n in NN^ast
  $
  and
  $
    integral_(-pi)^pi abs(f(x) - f_n (x)) dif x -> 0 quad "as" n -> oo.
  $ <eq:15>
] <lem:2>

The proof of this lemma is omitted here to maintain focus on our primary objective.

In the following, we present the proof of statement 5 for the general case.


#proof[
  Suppose $abs(f) ≤ M_1$ and $abs(g) ≤ M_2$ for some constants $M_1, M_2 > 0$.
  Let ${f_n}_(n=1)^∞$ and ${g_n}_(n=1)^∞$ be sequences of functions given by @lem:2.

  Given $ε > 0$, there exist $N_1 in NN^*$ and $N_2 in NN^*$ such that
  $
    integral_(-pi)^pi abs(f(x) - f_n (x)) dif x & < epsilon / (2 M_2) quad "for" n >= N_1, quad "and" \
    integral_(-pi)^pi abs(g(x) - g_n (x)) dif x & < epsilon / (2 M_1) quad "for" n >= N_2.
  $

  We analyze the difference:
  $
    abs(f * g - f_n * g_n) & = abs(f * g - f * g_n + f * g_n - f_n * g_n). \
                           & "Apply the linearality, we have" \
                           & = abs(f * (g - g_n) + (f - f_n) * g_n) \
                           & <= abs(f * (g - g_n)) + abs((f - f_n) * g_n).
  $ <eq:12>

  We estimate each term separately. For $n ≥ N_2$:
  $
    abs(f * (g - g_n)) & = 1 / (2pi) abs(integral_(-pi)^pi f(y) [g(x-y) - g_n (x-y)] dif y) \
                       & <= 1 / (2pi) integral_(-pi)^pi abs(f(y)) abs(g(x-y) - g_n (x-y)) dif y \
                       & <= M_1 / (2pi) integral_(-pi)^pi abs(g(x-y) - g_n (x-y)) dif y \
                       & = M_1 / (2pi) integral_(-pi+x)^(pi+x) abs(g(u) - g_n (u)) dif u \
                       & = M_1 / (2pi) integral_(-pi)^(pi) abs(g(u) - g_n (u)) dif u \
                       & < M_1 / (2pi) dot epsilon / (2 M_1) dot 2pi \
                       & = epsilon / 2
  $ <eq:13>

  Applying a similar argument, one may show that
  $
    abs((f - f_n) * g_n) < epsilon / 2 quad "for" n >= N_1.
  $ <eq:14>

  Taking $N = max(N_1, N_2)$, we combine @eq:12, @eq:13, and @eq:14 to obtain:
  $
    abs(f * g - f_n * g_n) < epsilon quad "for" n >= N.
  $
  This establishes uniform convergence of ${f_n * g_n}_(n=1)^oo$ to $f*g$ on $[-π, π]$.
  Since each $f_n*g_n$ is continuous (as proved in the special case), the limit $f*g$ is consequently continuous.
]


Finally, we turn to the proof of statement 6.
As before, we first consider the case where both $f$ and $g$ are continuous.
The argument proceeds via interchanging integral signs and applying change of variables.

#proof[
  Assume $f$ and $g$ are both continuous on $[-pi, pi]$.
  We have
  $
    hat(f * g)(n)
    &= 1 / (2pi) integral_(-pi)^pi (1 / (2pi) integral_(-pi)^pi f(y) g(x-y) dif y) e^(-i n x) dif x \
    &= 1 / (2pi)^2 integral_(-pi)^pi integral_(-pi)^pi f(y) g(x-y) e^(-i n x) dif y dif x.\
    &"Since the integrand is continuous, we may interchange the order of integration:"\
    &= 1 / (2pi)^2 integral_(-pi)^pi integral_(-pi)^pi f(y) g(x-y) e^(-i n x) dif x dif y\
    &= 1 / (2pi)^2 integral_(-pi)^pi f(y) ( integral_(-pi)^pi g(x-y) e^(-i n x) dif x ) dif y.\
    &"Substitute" x = u + y:\
    &= 1 / (2pi)^2 integral_(-pi)^pi f(y) ( integral_(-pi-y)^(pi-y) g(u) e^(-i n u) e^(-i n y) dif u ) dif y.\
    &"Because the integrand of the inner integral is" 2pi"-periodic, we have:"\
    &= 1 / (2pi)^2 integral_(-pi)^pi f(y) ( integral_(-pi)^(pi) g(u) e^(-i n u) e^(-i n y) dif u ) dif y.\
    &= 1 / (2pi)^2 integral_(-pi)^pi f(y) e^(-i n y) ( integral_(-pi)^(pi) g(u) e^(-i n u) dif u ) dif y\
    &= (1 / (2pi) integral_(-pi)^pi f(y) e^(-i n y) dif y) dot (1 / (2pi) integral_(-pi)^(pi) g(u) e^(-i n u) dif u )\
    &= hat(f)(n) hat(g)(n).
  $
]

Now, we establish the general case of statement 6.

#proof[
  Recall in the general proof of statement 5, we have concluded that
  $f_k * g_k$ converges uniformly to $f * g$ on $[-pi, pi]$.
  (We use the $k$ as the index to avoid confusion with the symbol $n$ in statement 6.)

  We will first show that $hat(f_k * g_k)(n) -> hat(f * g)(n)$ as $k -> oo$.
  Let $epsilon > 0$ be arbitray.
  Since $f_k * g_k$ converges uniformly to $f * g$, there exists $N in NN^*$ such that
  $
    abs((f_k * g_k)(x) - (f * g)(x)) < epsilon quad forall k >= N med forall x in [-pi, pi].
  $
  For $k >= N$, we have
  $
    abs(hat(f_k * g_k)(n) - hat(f * g)(n))
    &= abs(1 / (2pi) integral_(-pi)^pi [(f_k * g_k)(x) - (f * g)(x)] e^(-i n x) dif x) \
    &<=1 / (2pi) integral_(-pi)^pi abs((f_k * g_k)(x) - (f * g)(x)) dif x \
    &<=1 / (2pi) dot epsilon dot 2pi \
    &= epsilon.
  $
  This shows that indeed $hat(f_k * g_k)(n) -> hat(f * g)(n)$ as $k -> oo$.


  Recall that $f_k$ and $g_k$ are both continuous.
  Therefore,
  $
    hat(f_k * g_k)(n) = hat(f_k)(n) hat(g_k)(n),
  $
  which we have already proved.

  Next, we want to show that $hat(f_k)(n) -> hat(f)(n)$ and $hat(g_k)(n) -> hat(g)(n)$ as $k -> oo$.
  Again, let $epsilon > 0$ be arbitray chosen.
  Using @eq:15 from @lem:2,
  there exists $N_1 in NN^*$ such that $abs(f_k(x) - f(x)) < epsilon$ whenever $k >= N_1$.
  Assuming $k >= N_1$, we have
  $
    abs(hat(f)_k (n) - hat(f) (n)) & = abs(1 / (2pi) integral_(-pi)^pi [f_k (x) - f (x)] e^(-i n x) dif x) \
                                   & <=1 / (2pi) integral_(-pi)^pi abs(f_k (x) - f (x)) dif x \
                                   & <1 / (2pi) dot epsilon dot 2pi \
                                   & = epsilon.
  $
  Therefore, indeed $hat(f_k)(n) -> hat(f)(n)$ as $k -> oo$.
  Applying a similar argument, one can show that $hat(g_k)(n) -> hat(g)(n)$ as $k -> oo$.

  In summary, now we have
  $
          lim_(k->oo) hat(f_k * g_k)(n) & = hat(f * g)(n), \
    lim_(k->oo) hat(f_k)(n) hat(g_k)(n) & = hat(f)(n) hat(g)(n), "and" \
                      hat(f_k * g_k)(n) & = hat(f_k)(n) hat(g_k)(n).
  $
  Because of the uniqueness of limits, it follows that
  $
    hat(f * g)(n) = hat(f)(n) hat(g)(n).
  $
]




== Good Kernels

#definition[
  A family of functions ${K_n}_(n=1)^oo$ on the circle is said to be a family of *good kernels* #index[good kernels] if it satisfies the folloing properties:
  + For all $n>= 1$, $ 1 / (2pi) integral_(-pi)^pi K_n (x) dif x = 1. $
  + There exists $M > 0$ such that for all $n>= 1$, we have $ integral_(-pi)^pi abs(K_n (x)) dif x <= M. $
  + For every $delta > 0$, $integral_(delta<=abs(x)<=pi) abs(K_n (x)) dif x -> 0 quad "as" n -> oo$.
] <def:1>

Property 1 states that the average value of $K_n$ over the circle is 1. Property 2 ensures that the integral of $abs(K_n)$ is bounded regardless of $n$, so $K_n$ remains controlled as $n$ increases. If $K_n >= 0$ for $n$, the property 2 is a consequence of property 1. Property 3 means that $K_n$ becomes increasingly concentrated at $0$ as $n -> oo$. Visually, as $n$ grows, the graph of $K_n$ becomes sharply peaked near $0$, while the tails diminish.
@fig:2 illustrates a typical characteristic of a family of good kernels.

#figure(
  caption: [A family of good kernels. This is actually a plot of Fejér kernels ${F_N (x)}$, which we will introduce later.],
)[
  #image("/assets/figures/fejer-kernels.png")
] <fig:2>

#theorem[
  Let ${K_n}_(n=1)^oo$ be a family of good kernels,
  and $f$ an integrable function on the circle.
  Then
  $
    lim_(n->oo) (f * K_n)(x) = f(x)
  $
  whenever $f$ is continuous at $x$.

  Moreover, if $f$ is continuous everywhere, then the sequence of functions ${f * K_n}_(n=1)^oo$
  converges uniformly to $f$ on the circle.
] <thm:2>

#proof[
  Suppose that $abs(f) <= M_1$ on the circle and that
  $
    integral_(-pi)^pi abs(K_n (x)) dif x <= M_2
  $
  for some $M_2 > 0$, which is the second property of good kernels.

  Let $epsilon > 0$ be arbitray.
  Let $x in [-pi, pi]$ be a point of continuity of $f$, we consider the difference:
  $
    abs((f*K_n)(x) - f(x)) & = 1 / (2pi) abs(integral_(-pi)^pi K_n (y) f(x-y) dif y - integral_(-pi)^pi f(x) dif y) \
                           & <= 1 / (2pi) integral_(-pi)^pi abs(K_n (y)) abs(f(x-y) - f(x)) dif y
  $ <eq:16>

  We would like to bound the RHS of the above inequality.
  The strategy is as follows:
  - When $|y|$ is small, we exploit the continuity of $f$ to ensure $|f(x-y) - f(x)|$ is sufficiently small, while the second property of good kernels controls $integral_(-pi)^pi |K_n (y)| dif y$.
  - When $|y|$ is large, the third property of good kernels bounds the integral.

  Since $f$ is continuous on the circle, it is continuous uniformly there.
  There exists $0 < delta < pi$ such that
  $
    abs(f(x) - f(t)) < (epsilon pi) / M_2 quad "whenever" quad abs(x - t) < delta.
  $ <eq:20>
  Considering $abs(y) < delta$, we have
  $
    1 / (2pi) integral_(-delta)^delta abs(K_n (y)) abs(f(x-y) - f(x)) dif y
    &< 1 / (2pi) dot (epsilon pi) / M_2 integral_(-delta)^delta abs(K_n (y)) dif y \
    &< 1 / (2pi) dot (epsilon pi) / M_2 dot M_2 \
    &= epsilon / 2.
  $ <eq:17>

  On the other hand, for $delta <= abs(y) <= pi$, applying $abs(f(x-y) - f(x)) <= 2M_1$, we have
  $
    1 / (2pi) integral_(delta<=abs(y)<=pi) abs(K_n (y)) abs(f(x-y) - f(x)) dif y
    &<= 1 / (2pi) dot 2 M_1 integral_(delta<=abs(y)<=pi) abs(K_n (y)) dif y.
  $ <eq:18>
  Becuase $integral_(delta<=abs(y)<=pi) abs(K_n (y)) dif y -> 0$ as $n -> oo$,
  there exists $N in NN^*$ such that
  $
    integral_(delta<=abs(y)<=pi) abs(K_n (y)) dif y < (epsilon pi) / (2M_1) quad forall n >= N.
  $
  Therefore, the RHS in @eq:18 can be further estimated as follows:
  $
    1 / (2pi) dot 2 M_1 integral_(delta<=abs(y)<=pi) abs(K_n (y)) dif y
    < 1 / (2pi) dot 2 M_1 dot (epsilon pi) / (2M_1)
    = epsilon / 2.
  $ <eq:19>

  Combining @eq:16, @eq:17, @eq:18 and @eq:19, we obtain that
  $
    abs((f*K_n)(x) - f(x)) < epsilon quad forall n >= N.
  $
  This shows that $(f*K_n)(x) -> f(x)$ as $n -> oo$.


  If $f$ is continuous on the circle, then it is uniformly continuous there.
  In this case, the choice of $delta$ in @eq:20 is independent of the choice of $x$.
  Folling the same argument as above, one can obtain that
  $
    abs((f*K_n)(x) - f(x)) < epsilon quad forall n >= N med forall x in [-pi, pi],
  $
  which means that ${f*K_n}$ converges uniformly to $f$ on the circle.
]

Recall that the partial sum of a Fourier series of $f$
can be written as the convolution of $f$ and the $n$-th Dirichlet kernel $D_N$:
$
  S_N (f)(x) = (f * D_N)(x).
$
It is natural to ask whether $D_N$ is a good kernel.
If this were true, then it would mean that every Fourier series of $f$
converges to $f(x)$ whenenver $f$ is continuous at $x$.
Unfortunately, this is not the case.

Recall
$
  D_N (x) = sum_(n=-N)^(N) e^(i n x).
$
An estimate of $D_N (x)$ shows that it violates the second property of good kernels.
More precisely, one can show that
$
  integral_(-pi)^pi abs(D_N (x)) dif x >= c log N quad "as" N -> oo.
$
However, it does satisfy the first property:
$
  1 / (2pi) integral_(-pi)^pi D_N (x) dif x = 1.
$
The fact that the integral of $|D_N (x)|$ is unbounded while $D_N$ still assigns unit mass on the circle is a result of cancellation.
@fig:3 illustrates the behavior of $D_N (x)$ for various values of $N$.
As you can see, $D_N (x)$ takes on positive and negative values and oscillates rapidly as $N$ increases.

#figure(caption: [Dirichlet kernels ${D_N (x)}$.])[
  #image("/assets/figures/dirichlet-kernels.png")
] <fig:3>



== Cesàro and Abel Summability: Application to Fourier Series

=== Cesàro Means and Summation

Consider summing up a collection of complex numbers.
If there are only finitely many numbers $c_0, c_1, ..., c_n$, the definition of sum is straightforward.
No matter how you conduct the steps of calculation, the result will always be the same as long as you include all the numbers.

Things become tricky when the number of items to sum is infinite: $c_0, c_1, c_2, ...$.
We developed the concept of series
$
  sum_(k=0)^oo c_k,
$
which is, roughly speaking, a _formal_ way of adding these terms together.
Nothing is said about whether it has a sum or not.
A common way to define the sum of a series is to consider the sequence of its partial sums ${s_n}$ given by
$
  s_n = sum_(k=0)^n c_k.
$
It is said that the series converges to $s$, or has sum $s$ if the sequence ${s_n}$ converges to $s$ as $n -> oo$.

Under this definition, the series
$
  sum_(k=0)^oo (-1)^k = 1 - 1 + 1 - 1 + 1 - 1 + dots.c
$
clearly does not have a well-defined sum since its sequence of partial sums oscillates between $0$ and $1$.

However, one may argue that the series has a value of $1\/2$, as it averages its two possible states ($0$ and $1$). This intuitive argument can be made rigorous through alternative summation definitions. Specifically, the Cesàro sum of this series is $1\/2$, a concept we will now examine.

#definition[
  Let ${s_n}_(n_0)^oo$ be the sequence of partial sums of the series $sum_(k=0)^oo c_k$.
  The $N$-th *Cesàro mean* #index[Cesàro mean] $sigma_N$ of ${s_n}$ is defined by
  $
    sigma_N = 1 / N sum_(n=0)^(N-1) s_n.
  $
  That is, the average of the first $N$ partial sums.
  $sigma_N$ is also refered to as the $N$-th *Cesàro sum* #index[Cesàro sum] of the series $sum_(k=0)^oo c_k$.

  If the sequence ${sigma_N}_(N=1)^oo$ converges to $sigma$ as $N -> oo$,
  then the series $sum_(k=0)^oo c_k$ is said to be *Cesàro summable* #index[Cesàro summable] to $sigma$.
]

$sigma$ is called the Cesàro _sum_ of the series. A natural question is whether this definition is consistent with the standard sum of a convergent series.
That is, if $sum_(k=0)^oo c_k$ converges to $s$ in the usual sense, is it also Cesàro summable to $s$?
The answer is yes.

#proposition[
  If series $sum_(k=0)^oo c_k$ converges to $s$,
  then it is Cesàro summable to $s$ as well.
]

#proof-sketch[
  $
    abs(sigma_N - s) & = && abs(1 / N (s_0 + dots.c s_(N-1)) - s) \
    & = && 1 / N abs((s_0 - s) + dots.c + (s_(N-1) - s)) \
    & <= && 1 / N (abs(s_0 - s) + dots.c + abs(s_(N-1) - s)) \
    & = && underbrace(1 / N (abs(s_0 - s) + dots.c + abs(s_(M-1) - s)), "Finte terms; Each absolute value is bounded; Goes to" 0 "as" N -> oo) \
    & && + underbrace(1 / N (abs(s_M - s) + dots.c + abs(s_(N-1) - s)), N-M "terms; Each absolute value can be estimated by a small number") \
  $
]

#proof[
  Let ${s_n}_(n=0)^oo$ be the sequence of partial sums of the series $sum_(k=0)^oo c_k$.
  Let $epsilon > 0$ be arbitray.
  Because ${s_n}$ converges to $s$, there exists $M in NN^*$ such that
  $
    abs(s_n - s) < epsilon quad forall n >= M.
  $
  Moreover, ${s_n}$ is bounded, say by $A > 0$, which further implies that
  $
    abs(s_n - s) <= A quad forall n in NN.
  $

  Consider the absolute difference:
  $
    abs(sigma_N - s) & = abs(1 / N (s_0 + dots.c s_(N-1)) - s) \
    & = 1 / N abs((s_0 - s) + dots.c + (s_(N-1) - s)) \
    & <= 1 / N (abs(s_0 - s) + dots.c + abs(s_(N-1) - s)) \
    & = 1 / N (abs(s_0 - s) + dots.c + abs(s_(M-1) - s)) + 1 / N (abs(s_M - s) + dots.c + abs(s_(N-1) - s)) \
    &< (M A)/ N + ((N - M) epsilon) / N \
    & = (M A)/ N + epsilon - (M epsilon)/ N.
  $
  In summary, we have obtained
  $
    abs(sigma_N - s) < (M A)/ N + epsilon - (M epsilon)/ N.
  $
  We can regard both sides as sequences in $N$.
  Taking the limit superior on both sides yields
  $
    limsup_(N->oo) abs(sigma_N - s) <= epsilon.
  $
  Recall that $epsilon > 0$ is arbitrarily chosen, which implies that
  $
    lim_(N->oo) abs(sigma_N - s) = limsup_(N->oo) abs(sigma_N - s) = 0.
  $
  #note-box[
    Yeah, using the limit superior technique elimiates a lot of $epsilon$-engineerings.
  ]
  This precisely means that the sequence ${sigma_N}_(N=1)^oo$ converges to $s$ as $N -> oo$.
]

#exercise[
  Show that the series
  $
    sum_(k=0)^oo (-1)^k
  $
  is Cesàro summable to $1\/2$.
]

=== Fejér's Theorem

Recall that the $N$-th partial sum of Fourier series is
$
  S_N (f) = f * D_N.
$
We have seen that, unfortunately, $S_N (f)$ does not converge to $f$ (at points of continuity) in general since $D_N$ is not a good kernel.
Now, we consider a _weaker_ summability of the Fourier series using the Cesàro sum and pounder the question if the Cesàro sum of the Fourier series converges to $f$.

We have seen that, unfortunately, the partial sums $S_N(f)$ do not generally converge to $f$ (even at points of continuity), because the Dirichlet kernel $D_N$ is not a good kernel.

We now consider a weaker notion of summability for Fourier series---specifically, Cesàro summability---and ask whether the Cesàro means of the Fourier series converge to $f$.

Taking the means of $S_N (f)$, we have

$
  sigma_N (f) = 1/N sum_(n=0)^(N-1) S_n (f) = f * underbrace(1/N sum_(n=0)^(N-1) D_n, "Regard this as a kernel").
$ <eq:24>
This introduces a new kernel $1/N sum_(n=0)^(N-1) D_n$ that is derived from $D_n$ by taking the Cesàro mean of the Dirichlet kernels.

This is called the *Fejér kernel* #index[Fejér kernel], and is denoted by
$
  F_N (x)
  = 1 / N sum_(n=0)^(N-1) D_n (x)
  = 1 / N sum_(n=0)^(N-1) (sin ((n+ 1\/2) x)) / (sin(x \/ 2)).
$ <eq:21>

The LHS of @eq:24, $sigma(f)$, is the Cesàro sum of the Fourier series and the RHS is the convolution of $f$ and the Fejér kernel $F_N$.
Fortunately, Fejér kernel is indeed a good kernel,
which means that the Fourier series of $f$ is Cesàro summable to $f$ (at points of continuity).

The closed-form expression for the N-th Fejér kernel is
$
  F_N (x)
  = 1 / N (sin^2 (N x \/ 2)) / (sin^2 (x \/ 2)).
$ <eq:22>

The key step is to evaluate the sum of sines
$
    & sum_(n=0)^(N-1) sin ((n+ 1\/2) x) \
  = & sin (x\/2) + sin (x\/2 + x) + sin (x\/2 + 2x) + dots.c + sin (x\/2 + (N-1) x).
$

To do so, we need to use the following trigonometric identities:
1. Product-to-sum indendity:
  $
    sin theta sin phi = 1/2 [cos (theta - phi) - cos (theta + phi)].
  $
2. Power-reduction formula:
  $
    sin^2 theta = 1/2 [1 - cos (2theta)].
  $

The trick is to multiply the original sum of sines by the term $sin x \/ 2$.
For a general term $sin (x\/2 + n x)$, we have
$
  2 sin (x\/2 + n x) sin (x \/ 2)
  = cos (n x) - cos ((n+1) x) .
$
Taking the sum over $n$, we obtain
$
    & 2 sum_(n=0)^(N-1) sin (x\/2 + n x) sin (x\/2) \
  = & cos 0 - cos x + cos (x) - cos (2x) + dots.c + cos ((N-1) x) - cos (N x) \
  = & 1 - cos (N x) \
    & "Apply the power-reduction formula" \
  = & 2 sin^2 (N x \/ 2) .
$
Therefore,
$
  sum_(n=0)^(N-1) sin (x\/2 + n x) = (sin^2 (N x \/ 2)) / (sin (x\/2)).
$ <eq:23>

This indeed brought back many memories from high school.

Substituting @eq:23 into @eq:21, we obtain @eq:22.

We have mentioned the Fejér kernel is a good kernel, which we will now verify

#proposition[
  The Fejér kernel
  $
    F_N (x) = 1 / N (sin^2 (N x \/ 2)) / (sin^2 (x \/ 2))
  $
  is a good kernel.
]

#proof[
  Let's verify the three properties of good kernels one by one.

  $F_N (x)$ assigns unit mass on the circle.
  We don't have to compute the integral directly using the closed-form expression of the Fejér kernel.
  Since
  $
    F_N (x) = 1/N sum_(n=0)^(N-1) D_n (x)
  $
  and we know that the Dirichlet kernel $D_n (x)$ assigns unit mass on the circle, we may immedately derive that
  $
    1/(2pi) integral_(-pi)^pi F_N (x) dif x & = 1/(2pi) integral_(-pi)^pi 1/N sum_(n=0)^(N-1) D_n (x) dif x \
                                            & = 1/N sum_(n=0)^(N-1) 1/(2pi) integral_(-pi)^pi D_n (x) dif x \
                                            & = 1/N sum_(n=0)^(N-1) 1 \
                                            & = 1
  $

  Showing the boundedness is also trivial.
  We observe from the closed form of $F_N (x)$ that itself is actually positive.
  Therefore,
  $
    integral_(-pi)^pi abs(F_N (x)) dif x
    = integral_(-pi)^pi F_N (x) dif x = 2pi.
  $

  Finally, we consider the integral $integral_(delta <= abs(x) <= pi) abs(F_N (x)) dif x$.
  We have the following estimate:
  $
    integral_(delta <= abs(x) <= pi) abs(F_N (x)) dif x
    &= integral_(delta <= abs(x) <= pi) 1 / N (sin^2 (N x \/ 2)) / (sin^2 (x \/ 2)) dif x \
    &<= 1 / N integral_(delta <= abs(x) <= pi) 1 / (sin^2 (x \/ 2)) dif x \
    &= 2 / N integral_(delta)^pi 1 / (sin^2 (x \/ 2)) dif x \
    &<= 2 / N integral_(delta)^pi 1 / (sin^2 (delta \/ 2)) dif x \
    &= (2(pi - delta)) / (N sin^2 (delta \/ 2)) \
    & -> 0 "as" N -> oo.
  $
]

Now that we have verified that ${F_N}$ is a family of good kernels, applying @thm:2, we immedately obtain the following nice theorem.

#theorem[
  If $f$ is integrable on the circle, then its Fourier series is Cesàro summable to $f$ at every point of continuity.

  Moreover, if $f$ is continuous on the circle, then its Fourier series is *uniformly Cesàro summable* to $f$.
] <thm:3>

#note-box[
  By saying a series of functions $sum_(n=0)^oo g_n (x)$ is *uniformly Cesàro summable* #index[Uniform Cesàro summability] to a fucntion $f(x)$ on a set $S$,
  we mean that the sequence of Cesàro sums ${sigma_N (x)}_(N=1)^oo$ of $sum_(n=0)^oo g_n (x)$ converges uniformly to $f(x)$ on $S$.
]

The following corollary is the same as @thm:1.
We satate it there again to provide the reader with another proof.

#corollary[
  If $f$ is integrable on the circle and $hat(f)(n) = 0$ for all $n in ZZ$, then $f(theta) = 0$ whenever $f$ is continuous at $theta$.
]

#proof[
  The $N$-th partial sum of the Fourier series is
  $
    s_N (theta) = sum_(n=-N)^N hat(f) (n) e^(i n theta) = 0.
  $
  This implies that every partial sum is zero.
  The $N$-th Cesàro sum is
  $
    sigma_N (theta) = 1 / N sum_(n=0)^(N-1) s_n (theta) = 0.
  $
  By @thm:3, we know that $sigma_N (theta) equiv 0$ converges to $f(theta)$ if $f$
  provided that $f$ is continuous at $theta$, which is exactly the statement of the corollary.
]

#corollary[
  Continuous functions on the circle can be uniformly approximated by trigonometric polynomials.
]

Review @eq:25 for the definitions trigonometric series and polynomials.

#proof[
  The key is to see that $N$-th Cesàro sum $sigma_N (theta)$ of the Fourier series of $f$ is indeed a trigonometric polynomial.
  We have
  $
    sigma_N (theta) = 1 / N sum_(n=0)^(N-1) s_n (theta)
    = 1 / N underbrace(sum_(n=0)^(N-1) sum_(k=-n)^n, "Finitely many") underbrace(hat(f) (k) e^(i k theta), "Matches the term defined in trigonometric series")
  $
]



=== Abel Means and Summation

Another method of summation is considered by Abel and actually predates Cesàro's method.

#definition[
  A series $sum_(k=0)^oo c_k$ is said to be *Abel summable* #index[Abel summable] to $s$ if the power series
  $
    A(r) = sum_(k=0)^oo c_k r^k
  $
  converges for all $0 <= r < 1$ and
  $
    lim_(r->1) A(r) = s.
  $
]

The quantities $A(r)$ are referred to as the *Abel means* #index[Abel means] of the series $sum_(k=0)^oo c_k$.
Again, we need to check that this new way of summation is compatible with the usual definition of sum.

#proposition[
  If the series $sum_(k=0)^oo c_k$ converges to $s$,
  then it is Abel summable to $s$ as well.
]

Moreover, Abel summability is actually more powerful than Cesàro summability in that a series is Abel summable to $s$ if it is Cesàro summable to $s$. (We will prove this in @prop:1.)
But the converse is not true.

#example[
  Consider the series
  $
    sum_(k=0)^oo c_k = sum_(k=0)^oo (-1)^k (k+1) = 1 - 2 + 3 - 4 + dots.c.
  $
  We have
  $
    A(r) = sum_(k=0)^oo (-1)^k (k+1) r^k.
  $
  Let $s_n$ be the $n$-th partial sum of the series $A(r)$. We wish to find a closed-form expression for $s_n$.
  #note-box[
    In fact, before studying the partial sums, we may already conclude that the series $A(r)$ converges (absolutely) for $0 <= r < 1$ by applying the ratio test or the root test.
  ]
  We have
  $
      s_n & = 1 - 2r + 3r^2 - 4r^3 + dots.c + (-1)^n (n+1) r^n \
    r s_n & = r - 2r^2 + 3r^3 - 4r^4 + dots.c + (-1)^(n-1) n r^n + (-1)^n (n+1) r^(n+1) .
  $
  Adding the two equations yields
  $
    (1+r) s_n &= underbrace(1 - r + r^2 - r^3 + dots.c + (-1)^n r^n, "Geometric sequence with common ratio " -r) + (-1)^n (n+1) r^(n+1) \
    &= (1 - (-r)^(n+1)) / (1+r) + (-1)^n (n+1) r^(n+1).
  $
  We have
  $
    s_n = (1 - (-r)^(n+1)) / (1+r)^2 +underbrace(((-1)^n (n+1) r^(n+1)) / (1+r), "Tends to" 0 "as" n -> oo).
  $
  Letting $n -> oo$, we see that ${s_n}$ converges to $1/(1+r)^2$.
  And $lim_(r -> 1) A(r) = 1/4$.
  Therefore, $sum_(k=0)^oo c_k$ is Abel summable to $1/4$.
  However, $sum_(k=0)^oo c_k$ is not Cesàro summable.
]

In the following content, we will prove that Cesàro summability implies Abel summability.


#lemma[
  Let $sum_(n=1)^oo c_n$ be a complex series and
  let ${s_n}$ be its sequence of partial sums.
  We have the following identity:
  $
    sum_(n=1)^N c_n r^n
    = (1-r) sum_(n=1)^N s_n r^n + s_N r^(N+1).
  $ <eq:26>
]

#proof[
  The key is to apply summation by parts.
  We have
  $
    sum_(n=1)^N c_n r^n & = sum_(n=1)^N (s_n - s_(n-1)) r^n \
                        & = r sum_(n=1)^N (s_n - s_(n-1)) r^(n-1) \
                        & "Apply summation by parts" \
                        & = r [(s_N r^N - s_0 r^0) - sum_(n=1)^N s_n (r^n - r^(n-1))] quad "We define" s_0 = 0 \
                        & = s_N r^(N+1) - sum_(n=1)^N s_n r^n (r - 1) \
                        & = s_N r^(N+1) + (1-r) sum_(n=1)^N s_n r^n.
  $
]


#lemma[
  Let $sum_(n=1)^oo c_n$ be a complex series.
  Let ${s_n}$ be the sequence of its partial sums and ${sigma_n}$ be the Cesàro sums.
  We have
  $
    sum_(n=1)^N c_n r^n
    = (1-r)^2 sum_(n=1)^N n sigma_n r^n + (1-r) N sigma_N r^(N+1) + s_N r^(N+1).
  $ <eq:27>
  Moreover, if $sum_(n=1)^n c_n$ is Cesàro summable to $sigma$
  and $0 < r < 1$,
  then the series $sum_(n=1)^oo c_n$ converges and
  $
    sum_(n=1)^oo c_n r^n
    = (1-r)^2 sum_(n=1)^oo n sigma_n r^n.
  $
] <lem:4>

#proof[
  Note that
  $
    s_n = n sigma_n - (n-1) sigma_(n-1).
  $
  #note-box[
    $c_n$ and $s_n$ satisfy the relation
    $
      c_n = s_n - s_(n-1).
    $
    And now we note that $s_n$ and $n sigma_n$ (regarded as a whole) satisfy exactly the same relation
    $
      s_n = n sigma_n - (n-1) sigma_(n-1).
    $
  ]
  By substituting
  $
    c_n <- s_n "and" s_n <- n sigma_n
  $
  in @eq:26, we can immedately obtain that
  $
    sum_(n=1)^N s_n r^n
    = (1-r) sum_(n=1)^N n sigma_n r^n + N sigma_N r^(N+1).
  $ <eq:28>
  Substituting @eq:28 into @eq:26 yields @eq:27.

  Now, suppose that $sum_(n=1)^oo c_n$ is Cesàro summable to $sigma$ and $0 < r < 1$.
  By definition, $sigma_n -> sigma$ as $n -> oo$.
  First, we show that the series $sum_(n=1)^oo n sigma_n r^n$ converges by applying the root test.
  We have
  $
    root(n, abs(n sigma_n r^n))
    = root(n, n) dot root(n, abs(sigma_n)) dot r
  $ <eq:29>
  If $sigma = 0$, then the limit of the RHS in @eq:29 is $0$.
  Otherwise, the limit is $r < 1$.
  In either case, we may conclude that
  $
    limsup_(n->oo) root(n, abs(n sigma_n r^n)) < 1,
  $
  which implies that the series $sum_(n=1)^oo n sigma_n r^n$ converges.

  Finally, we need to show that the term
  $
    (1-r) N sigma_N r^(N+1) + s_N r^(N+1)
  $
  vanishes as $N->oo$.
  It is clear that
  $
    lim_(N->oo) (1-r) N sigma_N r^(N+1) = 0.
  $
  since $sigma_N -> sigma$ and $N r^(N+1) -> 0$ as $N ->oo$.
  For the term $s_N r^(N+1)$, we can write it as
  $
    s_N r^(N+1) & = N sigma_N r^(N+1) - (N-1) sigma_(N-1) r^(N+1) \
                & = N (sigma_N - sigma_(N-1)) r^(N+1) + sigma_(N-1) r^(N+1).
  $
  We have
  $
    abs(s_N r^(N+1)) & <= N abs(sigma_N - sigma_(N-1)) r^(N+1) + abs(sigma_(N-1)) r^(N+1) \
    & <= underbrace((abs(sigma_N) + abs(sigma_(N-1))) N r^(N+1), -> 0) + underbrace(abs(sigma_(N-1)) r^(N+1), ->0).
  $
  This concludes the proof.
]


Now, let's consider a special case where the Cesàro sum is zero.
The extension to the general case will then be straightforward to obtain with only a few steps.
We will consider the series $sum_(n=1)^oo c_n$ where the index starts from $1$ instead of $0$ for ease of notation. This does not affect the generality of the argument.


#lemma[
  If the series $sum_(n=1)^oo c_n$ is Cesàro summable to $0$,
  then it is Abel summable to $0$ as well.
] <lem:3>

#proof[
  By @lem:4, we have that the Amel means $A(r) = sum_(n=1)^oo c_n r^n$---regarded as a series---conveges and
  $
    A(r) = sum_(n=1)^oo c_n r^n
    = (1-r)^2 sum_(n=1)^oo n sigma_n r^n.
  $

  Pick $epsilon > 0$.
  There exists $N in NN^*$ ($N > 1$) such that
  $
    abs(sigma_n) < epsilon quad forall n >= N.
  $
  We have
  $
    abs((1-r)^2 sum_(n=1)^oo n sigma_n r^n) & <= (1-r)^2 sum_(n=1)^oo n abs(sigma_n) r^n \
    & < (1-r)^2 underbrace(sum_(n=1)^(N-1) n abs(sigma_n) r^n, "Denoted as" M) + (1-r)^2 sum_(n=1)^oo n epsilon r^n \
    & = (1-r)^2 M + epsilon underbrace((1-r)^2 sum_(n=1)^oo n r^n, "Let's study this term").
  $ <eq:30>
  #note-box[
    Let $S_n = sum_(k=1)^n k r^k$.
    We have a closed form expression for $S_n$:
    $
      S_n = (r (1 - r^n)) / (1-r)^2 - (n r^(n+1)) / (1-r).
    $
    One may derive this by considering $S_n - r S_n$.
  ]
  Note that the series $sum_(n=1)^oo n r^n$ converges and
  $
    sum_(n=1)^oo n r^n = r / (1-r)^2.
  $
  Plugging this back to @eq:30, we obtain
  $
    abs((1-r)^2 sum_(n=1)^oo n sigma_n r^n) & < (1-r)^2 M + epsilon r.
  $
  Taking the limit superior on both sides as $r -> 1$ yields
  $
    limsup_(r->1) abs((1-r)^2 sum_(n=1)^oo n sigma_n r^n) <= epsilon.
  $ <eq:31>
  Since @eq:31 holds every $epsilon > 0$, we conclude that
  $
    lim_(r->1) (1-r)^2 sum_(n=1)^oo n sigma_n r^n = 0.
  $
  Therefore, $A(r) = 0$ as $r -> 1$, which implies that $sum_(n=1)^oo c_k$ is Abel summable to $0$.
]

#proposition[
  If the series $sum_(n=1)^oo c_n$ is Cesàro summable to $sigma$,
  then it is Abel summable to $sigma$ as well.
] <prop:1>

#proof[
  Construct a new series $sum_(k=0)^oo c'_k$, where $c'_0 = c_0 - sigma$ and $c'_k = c_k$ for $k >= 1$.
  We have $s'_n = s_n - sigma$
  where $s'_n$ and $s_n$ are the $n$-th partial sums of $sum_(k=0)^oo c'_k$ and $sum_(k=0)^oo c_k$, respectively.
  It then follows that
  $
    sigma'_n = (s'_0 + dots.c + s'_(n-1)) / n & = ((s_0 + dots.c + s_(n-1)) - n sigma) / n \
                                              & = (s_0 + dots.c + s_(n-1)) / n - sigma \
                                              & = sigma_n - sigma.
  $
  Since $sigma_n -> sigma$ as $n -> oo$, we have $sigma'_n -> 0$ as $n -> oo$,
  which implies that $sum_(k=0)^oo c'_k$ is Cesàro summable to $0$.

  We now look at the Abel means $A'(r)$ of $sum_(k=0)^oo c'_k$.
  By @lem:3, we know that $A'(r)$ converges and that $lim_(r->1) A'(r) = 0$.
  We have
  $
    A'(r) & = sum_(k=0)^oo c'_k r^k \
          & = c'_0 + underbrace(sum_(k=1)^oo c'_k r^k, "This series converges") \
          & = (c_0 - sigma) + sum_(k=1)^oo c_k r^k \
          & = underbrace(c_0 + sum_(k=1)^oo c_k r^k, "Implicitly implies that this series converges") - sigma \
          & = A(r) - sigma.
  $
  Therefore, the series $A(r)$ converges and $lim_(r->1) A(r) = lim_(r->1) (A'(r) + sigma) = sigma$.
  This concludes the proof.
]

In summary, we have shown that for a complex series $sum c_n$, we have the following implications:

#figure()[
  #diagram(
    let (a, b, c) = ((-1, 0), (0, 0), (1, 0)),
    node(a, "Convergent"),
    node(b, "Cesàro summable"),
    node(c, "Abel summable"),

    edge(a, b, "=>"),
    edge(b, c, "=>"),
  )
]

Moreover, the definition of _sums_ are consistent.
That is, if $sum c_n$ converges to sum $s$, it is also Cesàro summable to $s$.
And if it is Cesàro summable to $sigma$, then it is also Abel summable to $sigma$.


=== The Poisson Kernel and Dirichlet's Problem in the Unit Disk

To adapt the Abel summability to the context of Fourier series,
we define the Abel means of
the function $f(theta) ~ sum_(n=-oo)^oo hat(f)(n) e^(i n theta)$ by
$
  A_r (f) (theta) = sum_(n=-oo)^oo r^(abs(n)) hat(f)(n) e^(i n theta).
$ <eq:32>
The RHS of @eq:32 is exactly the Abel means of the Fourier series of $f$.
To see this, we write
$
  c_0 & = hat(f) (0) \
  c_n & = hat(f) (n) e^(i n theta) + hat(f) (-n) e^(-i n theta), quad n >= 1.
$
The Fourier series of $f$ is exactly $sum_(n=0)^oo c_n$.
Then it is clear that the Abel means of $sum_(n=0)^oo c_n$
is exactly $A_r (f) (theta)$ in @eq:32.

By applying the Weierstrass's M-test, @thm:4, we may conclude that
$A_r (f) (theta)$, regarded as a series of functions in $theta$,
converges absolutely and uniformly on $[-pi, pi]$.

#note-box[
  Since $f$ is integrable on the circle, it is necessarily bounded.
  Suppose that $abs(f(theta)) <= M$.
  We have
  $
    abs(hat(f) (n))
    = 1/(2pi) abs(integral_(-pi)^pi f(theta) e^(-i n theta) dif theta)
    <= 1/(2pi) integral_(-pi)^pi abs(f(theta)) dif theta
    <= 1/(2pi) integral_(-pi)^pi M dif theta = M.
  $
  Therefore, each function $g_n (theta) = r^(abs(n)) hat(f) (n) e^(i n theta)$ has the following bound:
  $
    abs(g_n (theta)) = r^(abs(n)) abs(hat(f) (n)) <= M r^(abs(n)) = M_n.
  $
  It is clear that the series $sum_(n=-oo)^oo M_n$ converges.
  Therefore, by the Weierstrass's M-test,
  the series of function $sum_(n=-oo)^oo g_n (theta)$ converges absolutely and uniformly on $[-pi, pi]$.
]


Just like Cesàro sums, we may express $A_r (f)$ as a convolution:
$
  A_r (f) = f * P_r
$
where $P_r$ is the Poisson kernel given by
$
  P_r (theta) = sum_(n=-oo)^oo r^(abs(n)) e^(i n theta),
$
which we have already seen in @eg:1.

In fact, we have
$
  A_r (f) (theta) & = sum_(n=-oo)^oo r^(abs(n)) hat(f)(n) e^(i n theta) \
  & =sum_(n=-oo)^oo r^(abs(n)) [1/(2pi) integral_(-pi)^pi f(x) e^(-i n x) dif x ]e^(i n theta) \
  & = 1/(2pi) sum_(n=-oo)^oo integral_(-pi)^pi underbrace(r^(abs(n)) f(x) e^(i n (theta - x)), "Absolute value" <= M r^(abs(n)) "where" M "is such that" abs(f) <= M) dif x
$

The Weierstrass's M-test implies that
the series of integrand functions, $sum_(n=-oo)^oo r^(abs(n)) f(x) e^(i n (theta - x))$, converges uniformly on $[-pi, pi]$.
Thus, we may interchange the summation and the integration to obtain

$
  A_r (f) (theta) & = 1/(2pi) integral_(-pi)^pi sum_(n=-oo)^oo r^(abs(n)) f(x) e^(i n (theta - x)) dif x \
  & = 1/(2pi) integral_(-pi)^pi f(x) sum_(n=-oo)^oo underbrace(r^(abs(n)) e^(i n (theta - x)), "Compare to the Poisson kernel's formula") dif x \
  & = 1/(2pi) integral_(-pi)^pi f(x) P_r (theta - x) dif x \
  & = (f * P_r) (theta).
$

#lemma[
  If $0 <= r < 1$, then
  $
    P_r (theta)
    = (1-r^2) / (1 - 2 r cos theta + r^2).
  $
  Moreover, Poisson kernel is a good kernel, as $r -> 1$ from below.
]

#note-box[
  Recall that we defined a family of kernels as a sequence of functions.
  The kernels ${K_n}$ are indexed by an integer.

  Here we extend this notion to a family of functions indexed
  by a continuous parameter $r$, ${P_r}_(0 <= r <1)$.
  And in the definition of good kernels (@def:1), we simply replace $n$ with $r$ in the last property.
  For example, in the case of Poisson kernels, the last property of being a family of good kernels becomes:
  - For every $delta > 0$, $integral_(delta<=abs(x)<=pi) abs(P_r (theta)) dif theta -> 0$ as $r -> 1$.
]
