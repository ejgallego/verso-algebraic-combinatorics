import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.Polynomials

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Polynomials" =>

:::group "polynomials_definition"
Polynomial power series and the polynomial ring inside formal power series.
:::

```tex
\section{Polynomials}

\subsection{Definition}
```

:::definition "def.fps.pol" (parent := "polynomials_definition") (lean := "FPS.IsPolynomial, FPS.polynomialSubalgebra")
*(a)* An FPS $`a\in K\left[\left[x\right]\right]` is said to be a
_polynomial_ if all but finitely many $`n\in\mathbb{N}` satisfy
$`\left[x^{n}\right]a=0`; in other words, if all but finitely many
coefficients of $`a` are $`0`.

*(b)* We let $`K\left[x\right]` be the set of all polynomial FPSs
$`a\in K\left[\left[x\right]\right]`. This set is a subring of
$`K\left[\left[x\right]\right]`, and is called the _univariate polynomial
ring_ over $`K`.
:::

```tex "def.fps.pol" (slot := statement)
\begin{definition}
\label{def.fps.pol}
\lean{FPS.IsPolynomial, FPS.polynomialSubalgebra}
\leantarget
\leanok
\textbf{(a)} An FPS $a\in K\left[  \left[  x\right]
\right]  $ is said to be a \emph{polynomial} if all but finitely many
$n\in\mathbb{N}$ satisfy $\left[  x^{n}\right]  a=0$ (that is, if all but
finitely many coefficients of $a$ are $0$). \medskip

\textbf{(b)} We let $K\left[  x\right]  $ be the set of all polynomials $a\in
K\left[  \left[  x\right]  \right]  $. This set $K\left[  x\right]  $ is a
subring of $K\left[  \left[  x\right]  \right]  $ (according to Theorem
\ref{thm.fps.pol.ring} below), and is called the \emph{univariate polynomial
ring} over $K$.
\end{definition}
```

:::lemma_ "lem.fps.pol.degree-bound" (parent := "polynomials_definition") (lean := "FPS.isPolynomial_iff_exists_degree_bound")
An FPS $`f\in K\left[\left[x\right]\right]` is a polynomial if and only if
there exists an $`N\in\mathbb{N}` such that $`\left[x^{n}\right]f=0` for all
$`n\geq N`.
:::

```tex "lem.fps.pol.degree-bound" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.degree-bound}
\lean{FPS.isPolynomial_iff_exists_degree_bound}
\leanhelper
\leanok
An FPS $f\in K\left[\left[x\right]\right]$ is a polynomial if and only if
there exists an $N\in\mathbb{N}$ such that $\left[x^{n}\right]f=0$ for all
$n\geq N$.
\end{lemma}
```

:::proof "lem.fps.pol.degree-bound"
$`\Longrightarrow`: If the set of indices of nonzero coefficients is finite,
then it is bounded above by some $`N`, so all coefficients beyond $`N`
vanish.

$`\Longleftarrow`: If all coefficients beyond $`N` vanish, then the set of
indices with nonzero coefficient is contained in
$`\{0,1,\ldots,N-1\}`, which is finite.
:::

```tex "lem.fps.pol.degree-bound" (slot := proof)
\begin{proof}
\leanok
$\Longrightarrow$: If the set of nonzero-coefficient indices is finite, it is
bounded above by some $N$, so all coefficients beyond $N$ vanish.

$\Longleftarrow$: If all coefficients beyond $N$ vanish, then the set of
nonzero-coefficient indices is contained in $\{0,1,\ldots,N-1\}$, which is
finite.
\end{proof}
```

:::lemma_ "lem.fps.pol.exists-polynomial" (parent := "polynomials_definition") (lean := "FPS.isPolynomial_iff_exists_polynomial")
An FPS $`f\in K\left[\left[x\right]\right]` is a polynomial in the sense above
if and only if $`f` equals the image of some element of $`K[x]` under the
canonical embedding
$`K[x]\hookrightarrow K\left[\left[x\right]\right]`.
:::

```tex "lem.fps.pol.exists-polynomial" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.exists-polynomial}
\lean{FPS.isPolynomial_iff_exists_polynomial}
\leanhelper
\leanok
An FPS $f\in K\left[\left[x\right]\right]$ is a polynomial (in the sense of
Definition~\ref{def.fps.pol}) if and only if $f$ equals the image of some
element of $K[x]$ under the canonical embedding $K[x]\hookrightarrow
K\left[\left[x\right]\right]$.
\end{lemma}
```

:::proof "lem.fps.pol.exists-polynomial"
$`\Longrightarrow`: Use the degree-bound characterization and truncate the FPS
at that bound.

$`\Longleftarrow`: The image of any polynomial has finite support, by the next
lemma.
:::

```tex "lem.fps.pol.exists-polynomial" (slot := proof)
\begin{proof}
\leanok
$\Longrightarrow$: Use the degree bound from
Lemma~\ref{lem.fps.pol.degree-bound} and truncation.

$\Longleftarrow$: The image of any polynomial has finite support
(Lemma~\ref{lem.fps.pol.of-polynomial}).
\end{proof}
```

:::lemma_ "lem.fps.pol.of-polynomial" (parent := "polynomials_definition") (lean := "FPS.isPolynomial_of_polynomial")
The image of any polynomial $`p\in K[X]` under the canonical embedding
$`K[X]\hookrightarrow K\left[\left[x\right]\right]` is a polynomial in the
FPS sense.
:::

```tex "lem.fps.pol.of-polynomial" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.of-polynomial}
\lean{FPS.isPolynomial_of_polynomial}
\leanhelper
\leanok
The image of any polynomial $p\in K[X]$ under the canonical embedding
$K[X]\hookrightarrow K\left[\left[x\right]\right]$ is a polynomial in the FPS
sense.
\end{lemma}
```

:::proof "lem.fps.pol.of-polynomial"
The indices of nonzero coefficients are contained in the support of $`p`, and
that support is finite.
:::

```tex "lem.fps.pol.of-polynomial" (slot := proof)
\begin{proof}
\leanok
The set of indices with nonzero coefficients is contained in the support of $p$,
which is a finite set.
\end{proof}
```

:::group "polynomials_conversion"
Converting between polynomial FPSs and actual polynomials.
:::

```tex
\subsubsection{Converting between polynomial FPSs and polynomials}
```

:::definition "def.fps.pol.toPolynomial" (parent := "polynomials_conversion") (lean := "FPS.toPolynomial")
Let $`f\in K\left[\left[x\right]\right]` be a polynomial FPS. We define
$`\operatorname{toPolynomial}(f)\in K[X]` as the truncation of $`f` at the
degree bound given by the previous lemma.
:::

```tex "def.fps.pol.toPolynomial" (slot := statement)
\begin{definition}
\label{def.fps.pol.toPolynomial}
\lean{FPS.toPolynomial}
\leanhelper
\leanok
Let $f\in K\left[\left[x\right]\right]$ be a polynomial FPS (in the sense of
Definition~\ref{def.fps.pol}). We define $\operatorname{toPolynomial}(f)\in K[X]$ as
the truncation of $f$ at the degree bound given by
Lemma~\ref{lem.fps.pol.degree-bound}.
\end{definition}
```

:::lemma_ "lem.fps.pol.coe-toPolynomial" (parent := "polynomials_conversion") (lean := "FPS.coe_toPolynomial")
Let $`f\in K\left[\left[x\right]\right]` be a polynomial FPS. Then the
coercion of $`\operatorname{toPolynomial}(f)` back into
$`K\left[\left[x\right]\right]` equals $`f`:
$$`\iota\bigl(\operatorname{toPolynomial}(f)\bigr) = f,`
where $`\iota\colon K[X]\hookrightarrow K\left[\left[x\right]\right]` is the
canonical embedding.
:::

```tex "lem.fps.pol.coe-toPolynomial" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.coe-toPolynomial}
\lean{FPS.coe_toPolynomial}
\leanhelper
\leanok
Let $f\in K\left[\left[x\right]\right]$ be a polynomial FPS. Then the
coercion of $\operatorname{toPolynomial}(f)$ back into
$K\left[\left[x\right]\right]$ equals $f$:
\[
\iota\bigl(\operatorname{toPolynomial}(f)\bigr) = f,
\]
where $\iota\colon K[X]\hookrightarrow K\left[\left[x\right]\right]$ is the
canonical embedding.
\end{lemma}
```

:::proof "lem.fps.pol.coe-toPolynomial"
By the degree bound, all coefficients of $`f` beyond the truncation point are
$`0`, so truncation and coercion recover every coefficient of $`f`.
:::

```tex "lem.fps.pol.coe-toPolynomial" (slot := proof)
\begin{proof}
By the degree bound, all coefficients of $f$ beyond the bound are zero, so
truncation and coercion recover every coefficient of $f$.
\end{proof}
```

:::lemma_ "lem.fps.pol.toPolynomial-coe" (parent := "polynomials_conversion") (lean := "FPS.toPolynomial_coe")
For any polynomial $`p\in K[X]`, we have
$`\operatorname{toPolynomial}(\iota(p))=p`, where $`\iota` is the canonical
embedding.
:::

```tex "lem.fps.pol.toPolynomial-coe" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.toPolynomial-coe}
\lean{FPS.toPolynomial_coe}
\leanhelper
\leanok
For any polynomial $p\in K[X]$, we have
$\operatorname{toPolynomial}(\iota(p))=p$, where $\iota$ is the canonical embedding.
\end{lemma}
```

:::proof "lem.fps.pol.toPolynomial-coe"
By the previous lemma, both sides have the same image under $`\iota`, and the
canonical embedding is injective.
:::

```tex "lem.fps.pol.toPolynomial-coe" (slot := proof)
\begin{proof}
\leanok
By Lemma~\ref{lem.fps.pol.coe-toPolynomial}, both sides have the same image
under $\iota$, and $\iota$ is injective.
\end{proof}
```

:::group "polynomials_subring"
Closure of polynomial FPSs under the ring and module operations.
:::

```tex
\subsection{Polynomials form a subring of power series}
```

:::lemma_ "lem.fps.pol.zero" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_zero")
The zero power series $`\underline{0}` is a polynomial.
:::

```tex "lem.fps.pol.zero" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.zero}
\lean{FPS.isPolynomial_zero}
\leanhelper
\leanok
The zero power series $\underline{0}$ is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.zero"
All coefficients of $`\underline{0}` are $`0`, so the set of indices of
nonzero coefficients is empty, hence finite.
:::

```tex "lem.fps.pol.zero" (slot := proof)
\begin{proof}
\leanok
All coefficients of $\underline{0}$ are $0$, so the set of nonzero-coefficient
indices is empty, hence finite.
\end{proof}
```

:::lemma_ "lem.fps.pol.one" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_one")
The unity $`\underline{1}` is a polynomial.
:::

```tex "lem.fps.pol.one" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.one}
\lean{FPS.isPolynomial_one}
\leanhelper
\leanok
The unity $\underline{1}$ is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.one"
The unity $`\underline{1}` equals the image of $`1\in K[X]` under the
canonical embedding.
:::

```tex "lem.fps.pol.one" (slot := proof)
\begin{proof}
\leanok
The unity $\underline{1}$ equals the image of $1\in K[X]$ under the canonical
embedding.
\end{proof}
```

:::lemma_ "lem.fps.pol.add" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_add")
The sum of two polynomial power series is a polynomial.
:::

```tex "lem.fps.pol.add" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.add}
\lean{FPS.isPolynomial_add}
\leanhelper
\leanok
The sum of two polynomial power series is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.add"
If $`f` and $`g` are polynomials, then the set of indices where $`f+g` has a
nonzero coefficient is contained in the union of the corresponding sets for
$`f` and $`g`. A finite union of finite sets is finite.
:::

```tex "lem.fps.pol.add" (slot := proof)
\begin{proof}
\leanok
If $f$ and $g$ are polynomials, then the set of indices where $(f+g)$ has a
nonzero coefficient is contained in the union of the corresponding sets for
$f$ and $g$. A finite union of finite sets is finite.
\end{proof}
```

:::lemma_ "lem.fps.pol.neg" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_neg")
The negation of a polynomial power series is a polynomial.
:::

```tex "lem.fps.pol.neg" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.neg}
\lean{FPS.isPolynomial_neg}
\leanhelper
\leanok
The negation of a polynomial power series is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.neg"
Negation does not change which coefficients are nonzero.
:::

```tex "lem.fps.pol.neg" (slot := proof)
\begin{proof}
\leanok
Negation does not change which coefficients are nonzero.
\end{proof}
```

:::lemma_ "lem.fps.pol.sub" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_sub")
The difference of two polynomial power series is a polynomial.
:::

```tex "lem.fps.pol.sub" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.sub}
\lean{FPS.isPolynomial_sub}
\leanhelper
\leanok
The difference of two polynomial power series is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.sub"
Write $`f-g=f+(-g)` and use the previous two closure lemmas.
:::

```tex "lem.fps.pol.sub" (slot := proof)
\begin{proof}
\leanok
Write $f-g=f+(-g)$ and apply Lemma~\ref{lem.fps.pol.add} and
Lemma~\ref{lem.fps.pol.neg}.
\end{proof}
```

:::lemma_ "lem.fps.pol.mul" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_mul")
The product of two polynomial power series is a polynomial.
:::

```tex "lem.fps.pol.mul" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.mul}
\lean{FPS.isPolynomial_mul}
\leanhelper
\leanok
The product of two polynomial power series is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.mul"
Let $`a,b\in K[x]`. Since $`a` is a polynomial, there exists a finite subset
$`I\subseteq\mathbb{N}` such that $`\left[x^{i}\right]a=0` for all
$`i\in\mathbb{N}\setminus I`. Similarly, there exists a finite subset
$`J\subseteq\mathbb{N}` such that $`\left[x^{j}\right]b=0` for all
$`j\in\mathbb{N}\setminus J`.

Let
$`S=\left\{ i+j \mid i\in I\text{ and }j\in J\right\}`. This set is finite.
For any $`n\in\mathbb{N}\setminus S`, we have
$$`\left[x^{n}\right](ab)
=\sum_{i=0}^{n}\left[x^{i}\right]a\cdot \left[x^{n-i}\right]b = 0,`
because for each $`i\in\{0,1,\ldots,n\}`, letting $`j=n-i`, we cannot have
both $`i\in I` and $`j\in J`; otherwise $`n=i+j` would belong to $`S`.
Hence every summand is $`0`.

Thus all but finitely many coefficients of $`ab` vanish, so $`ab\in K[x]`.
:::

```tex "lem.fps.pol.mul" (slot := proof)
\begin{proof}
\leanok
Let $a,b\in K\left[  x\right]  $. Since $a$ is a polynomial, there exists a finite
subset $I$ of $\mathbb{N}$ such that
$\left[  x^{i}\right]  a=0$ for all
$i\in\mathbb{N}\setminus I$.
Similarly, there exists a finite subset $J$ of
$\mathbb{N}$ such that
$\left[  x^{j}\right]  b=0$ for all
$j\in\mathbb{N}\setminus J$.

Let $S=\left\{
i+j\ \mid\ i\in I\text{ and }j\in J\right\}$. This set $S$
is again finite (since $I$ and $J$ are finite), and we have
\[
\left[  x^{n}\right]  \left(  ab\right)  =\sum_{i=0}^{n}\left[  x^{i}\right]
a\cdot\left[  x^{n-i}\right]  b=0\text{ for all }n\in\mathbb{N}\setminus S,
\]
because for each $i\in\left\{  0,1,\ldots,n\right\}$, letting $j=n-i$, we cannot have both
$i\in I$ and $j\in J$ (otherwise $n=i+j\in S$, contradicting
$n\notin S$), so at least one of $\left[  x^{i}\right]  a$ and
$\left[  x^{j}\right]  b$ is $0$, making each summand $0$.
Thus, all but finitely many
$n\in\mathbb{N}$ satisfy $\left[  x^{n}\right]  \left(  ab\right)  =0$, so $ab\in K\left[  x\right]  $.
\end{proof}
```

:::lemma_ "lem.fps.pol.smul" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_smul")
Scalar multiplication of a polynomial power series by an element of $`K` is a
polynomial.
:::

```tex "lem.fps.pol.smul" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.smul}
\lean{FPS.isPolynomial_smul}
\leanhelper
\leanok
Scalar multiplication of a polynomial power series by an element of $K$ is a
polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.smul"
If $`\left[x^{n}\right]f=0`, then
$`\left[x^{n}\right](cf)=c\cdot\left[x^{n}\right]f=0`. Thus the set of
indices of nonzero coefficients of $`cf` is contained in that of $`f`, which
is finite.
:::

```tex "lem.fps.pol.smul" (slot := proof)
\begin{proof}
\leanok
If $\left[x^{n}\right]f=0$, then $\left[x^{n}\right](cf)=c\cdot
\left[x^{n}\right]f=0$. So the nonzero-coefficient set of $cf$ is contained
in that of $f$, which is finite.
\end{proof}
```

:::theorem "thm.fps.pol.ring" (parent := "polynomials_subring") (lean := "FPS.polynomialSubalgebra, FPS.polynomialSubring, FPS.polynomialSubmodule")
The set $`K[x]` is a subring of $`K\left[\left[x\right]\right]`; that is, it
is closed under addition, subtraction, and multiplication, and it contains
$`\underline{0}` and $`\underline{1}`. It is also a $`K`-submodule of
$`K\left[\left[x\right]\right]`; that is, it is closed under addition and
scaling by elements of $`K`.
:::

```tex "thm.fps.pol.ring" (slot := statement)
\begin{theorem}
\label{thm.fps.pol.ring}
\lean{FPS.polynomialSubalgebra, FPS.polynomialSubring, FPS.polynomialSubmodule}
\leantarget
\leanok
The set $K\left[  x\right]  $ is a subring of
$K\left[  \left[  x\right]  \right]  $ (that is, it is closed under addition,
subtraction and multiplication, and contains the zero $\underline{0}$ and the
unity $\underline{1}$) and is a $K$-submodule of $K\left[  \left[  x\right]
\right]  $ (that is, it is closed under addition and scaling by elements of
$K$).
\end{theorem}
```

:::proof "thm.fps.pol.ring"
This is an immediate consequence of the preceding lemmas: polynomial FPSs
contain $`\underline{0}` and $`\underline{1}`, are closed under addition,
subtraction, and multiplication, and are also closed under scaling by
elements of $`K`.
:::

```tex "thm.fps.pol.ring" (slot := proof)
\begin{proof}
Follows from the preceding lemmas: $K[x]$ contains $\underline{0}$
(Lemma~\ref{lem.fps.pol.zero}) and $\underline{1}$
(Lemma~\ref{lem.fps.pol.one}), is closed under addition
(Lemma~\ref{lem.fps.pol.add}), multiplication (Lemma~\ref{lem.fps.pol.mul}),
and scalar multiplication (Lemma~\ref{lem.fps.pol.smul}).
\end{proof}
```

:::lemma_ "lem.fps.pol.X" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_X")
The polynomial $`x\in K\left[\left[x\right]\right]` is a polynomial.
:::

```tex "lem.fps.pol.X" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.X}
\lean{FPS.isPolynomial_X}
\leanhelper
\leanok
The polynomial $x\in K\left[\left[x\right]\right]$ is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.X"
The only nonzero coefficient of $`x` is the coefficient of $`x^1`, which is
$`1`. Thus the set of indices of nonzero coefficients is contained in
$`\{1\}`, which is finite.
:::

```tex "lem.fps.pol.X" (slot := proof)
\begin{proof}
\leanok
The only nonzero coefficient of $x$ is the coefficient of $x^1$, which is $1$.
Thus the set of nonzero-coefficient indices is contained in $\{1\}$, which is
finite.
\end{proof}
```

:::lemma_ "lem.fps.pol.C" (parent := "polynomials_subring") (lean := "FPS.isPolynomial_C")
For any $`c\in K`, the constant FPS $`\underline{c}` is a polynomial.
:::

```tex "lem.fps.pol.C" (slot := statement)
\begin{lemma}
\label{lem.fps.pol.C}
\lean{FPS.isPolynomial_C}
\leanhelper
\leanok
For any $c\in K$, the constant FPS $\underline{c}$ is a polynomial.
\end{lemma}
```

:::proof "lem.fps.pol.C"
The only possibly nonzero coefficient of $`\underline{c}` is the coefficient
of $`x^0`. Thus the set of indices of nonzero coefficients is contained in
$`\{0\}`, which is finite.
:::

```tex "lem.fps.pol.C" (slot := proof)
\begin{proof}
\leanok
The only possibly nonzero coefficient of $\underline{c}$ is the coefficient of
$x^0$. Thus the set of nonzero-coefficient indices is contained in $\{0\}$,
which is finite.
\end{proof}
```

:::group "polynomials_ring_reminders"
Ring and algebra reminders used before polynomial evaluation.
:::

```tex
\subsection{Reminders on rings and $K$-algebras}
```

:::definition "def.alg.ring" (parent := "polynomials_ring_reminders") (lean := "FPS.ring_add_assoc, FPS.ring_add_comm, FPS.ring_add_zero, FPS.ring_zero_add, FPS.ring_add_neg, FPS.ring_mul_assoc, FPS.ring_left_distrib, FPS.ring_right_distrib, FPS.ring_mul_one, FPS.ring_one_mul, FPS.ring_mul_zero, FPS.ring_zero_mul")
The notion of a _ring_, also known as a _noncommutative ring_, is defined in
exactly the same way as the notion of a commutative ring from the earlier
chapter, except that the commutativity-of-multiplication axiom is removed.
:::

```tex "def.alg.ring" (slot := statement)
\begin{definition}
\label{def.alg.ring}
\lean{FPS.ring_add_assoc, FPS.ring_add_comm, FPS.ring_add_zero, FPS.ring_zero_add, FPS.ring_add_neg, FPS.ring_mul_assoc, FPS.ring_left_distrib, FPS.ring_right_distrib, FPS.ring_mul_one, FPS.ring_one_mul, FPS.ring_mul_zero, FPS.ring_zero_mul}
\leantarget
\leanok
The notion of a \emph{ring} (also known as a \emph{noncommutative ring}) is
defined in the exact same way as we defined the notion of a commutative ring in
Definition~\ref{def.alg.commring}, except that the ``Commutativity of
multiplication'' axiom is removed.
\end{definition}
```

:::definition "def.alg.Kalg" (parent := "polynomials_ring_reminders") (lean := "FPS.kalg_add_comm, FPS.kalg_add_assoc, FPS.kalg_add_zero, FPS.kalg_mul_assoc, FPS.kalg_left_distrib, FPS.kalg_right_distrib, FPS.kalg_mul_one, FPS.kalg_one_mul, FPS.kalg_smul_assoc, FPS.kalg_smul_add, FPS.kalg_add_smul, FPS.kalg_one_smul, FPS.kalg_zero_smul, FPS.kalg_smul_zero, FPS.kalg_smul_mul_assoc, FPS.kalg_mul_smul_comm, FPS.kalg_smul_mul_eq_mul_smul")
A $`K`-algebra is a set $`A` equipped with four maps
$$`\begin{aligned}
\oplus &  :A\times A\rightarrow A,\\
\ominus &  :A\times A\rightarrow A,\\
\odot &  :A\times A\rightarrow A,\\
\rightharpoonup &  :K\times A\rightarrow A
\end{aligned}`$$
and two elements $`\overrightarrow{0}\in A` and $`\overrightarrow{1}\in A`
satisfying the following properties:

1. The set $`A`, equipped with the maps $`\oplus`, $`\ominus`, and $`\odot`
   and the two elements $`\overrightarrow{0}` and $`\overrightarrow{1}`, is a
   ring.
2. The set $`A`, equipped with the maps $`\oplus`, $`\ominus`, and
   $`\rightharpoonup` and the element $`\overrightarrow{0}`, is a $`K`-module.
3. We have
   $$`\lambda\rightharpoonup\left(a\odot b\right)
   =\left(\lambda\rightharpoonup a\right)\odot b
   =a\odot\left(\lambda\rightharpoonup b\right)`$$
   for all $`\lambda\in K` and $`a,b\in A`.

Thus, in a nutshell, a $`K`-algebra is a set $`A` that is simultaneously a
ring and a $`K`-module, with the property that the ring $`A` and the
$`K`-module $`A` have the same addition, the same subtraction, and the same
zero, and satisfy the compatibility property above.
:::

```tex "def.alg.Kalg" (slot := statement)
\begin{definition}
\label{def.alg.Kalg}
\lean{FPS.kalg_add_comm, FPS.kalg_add_assoc, FPS.kalg_add_zero, FPS.kalg_mul_assoc, FPS.kalg_left_distrib, FPS.kalg_right_distrib, FPS.kalg_mul_one, FPS.kalg_one_mul, FPS.kalg_smul_assoc, FPS.kalg_smul_add, FPS.kalg_add_smul, FPS.kalg_one_smul, FPS.kalg_zero_smul, FPS.kalg_smul_zero, FPS.kalg_smul_mul_assoc, FPS.kalg_mul_smul_comm, FPS.kalg_smul_mul_eq_mul_smul}
\leantarget
\leanok
A $K$\emph{-algebra} is a set $A$ equipped with four maps%
\begin{align*}
\oplus &  :A\times A\rightarrow A,\\
\ominus &  :A\times A\rightarrow A,\\
\odot &  :A\times A\rightarrow A,\\
\rightharpoonup &  :K\times A\rightarrow A
\end{align*}
and two elements $\overrightarrow{0}\in A$ and $\overrightarrow{1}\in A$
satisfying the following properties:

\begin{enumerate}
\item The set $A$, equipped with the maps $\oplus$, $\ominus$ and $\odot$ and
the two elements $\overrightarrow{0}$ and $\overrightarrow{1}$, is a
(noncommutative) ring.

\item The set $A$, equipped with the maps $\oplus$, $\ominus$ and
$\rightharpoonup$ and the element $\overrightarrow{0}$, is a $K$-module.

\item We have%
\begin{equation}
\lambda\rightharpoonup\left(  a\odot b\right)  =\left(  \lambda\rightharpoonup
a\right)  \odot b=a\odot\left(  \lambda\rightharpoonup b\right)
\label{eq.def.alg.Kalg.scaleinv}%
\end{equation}
for all $\lambda\in K$ and $a,b\in A$.
\end{enumerate}

(Thus, in a nutshell, a $K$-algebra is a set $A$ that is simultaneously a ring
and a $K$-module, with the property that the ring $A$ and the $K$-module $A$
have the same addition, the same subtraction and the same zero, and satisfy
the additional compatibility property (\ref{eq.def.alg.Kalg.scaleinv}).)
\end{definition}
```

:::group "polynomials_evaluation"
Polynomial evaluation as substitution into an algebra.
:::

```tex
\subsection{Evaluation aka substitution into polynomials}
```

:::definition "def.pol.subs" (parent := "polynomials_evaluation") (lean := "FPS.polyEval")
Let $`f\in K[x]` be a polynomial, let $`A` be any $`K`-algebra, and let
$`a\in A`. We define an element $`f[a]\in A` as follows.

Write $`f` in the form
$`f=\sum_{n\in\mathbb{N}} f_n x^n` with $`f_n\in K`; in other words,
$`f_n=\left[x^n\right]f` for each $`n\in\mathbb{N}`. Then set
$$`f[a] := \sum_{n\in\mathbb{N}} f_n a^n.`
This sum is essentially finite because $`f` is a polynomial.

The element $`f[a]` is also denoted by $`f\circ a` or $`f(a)`, and is called
the _value_ of $`f` at $`a`, or the _evaluation_ of $`f` at $`a`, or the
_result of substituting_ $`a` _for_ $`x` _in_ $`f`.
:::

```tex "def.pol.subs" (slot := statement)
\begin{definition}
\label{def.pol.subs}
\lean{FPS.polyEval}
\leantarget
\leanok
Let $f\in K\left[  x\right]  $ be a polynomial. Let $A$ be
any $K$-algebra. Let $a\in A$ be any element. We then define an element
$f\left[  a\right]  \in A$ as follows:

Write $f$ in the form $f=\sum_{n\in\mathbb{N}}f_{n}x^{n}$ with $f_{0}%
,f_{1},f_{2},\ldots\in K$. (That is, $f_{n}=\left[  x^{n}\right]  f$ for each
$n\in\mathbb{N}$.) Then, set%
\[
f\left[  a\right]  :=\sum_{n\in\mathbb{N}}f_{n}a^{n}.
\]
(This sum is essentially finite, since $f$ is a polynomial.)

The element $f\left[  a\right]  $ is also denoted by $f\circ a$ or by
$f\left(  a\right)  $, and is called the \emph{value} of $f$ at $a$ (or the
\emph{evaluation} of $f$ at $a$, or the \emph{result of substituting }$a$ for
$x$ in $f$).
\end{definition}
```

:::lemma_ "lem.pol.eval.def" (parent := "polynomials_evaluation") (lean := "FPS.eval_def")
The evaluation $`f[a]` can be computed as
$`f[a]=\sum_{n} f_n\cdot a^n`, where the sum ranges over all $`n` in the
support of $`f`.
:::

```tex "lem.pol.eval.def" (slot := statement)
\begin{lemma}
\label{lem.pol.eval.def}
\lean{FPS.eval_def}
\leanhelper
\leanok
The evaluation $f\left[a\right]$ can be computed as
$f\left[a\right]=\sum_{n}f_{n}\cdot a^{n}$,
where the sum ranges over all $n$ in the support of $f$.
\end{lemma}
```

:::proof "lem.pol.eval.def"
Immediate from the definition.
:::

```tex "lem.pol.eval.def" (slot := proof)
\begin{proof}
\leanok
Immediate from the definitions.
\end{proof}
```

:::lemma_ "lem.pol.eval.finsum" (parent := "polynomials_evaluation") (lean := "FPS.eval_eq_finsum")
The evaluation $`f[a]` equals
$`\sum_{n\in \operatorname{supp}(f)} f_n\cdot a^n`, making the finiteness of
the sum explicit.
:::

```tex "lem.pol.eval.finsum" (slot := statement)
\begin{lemma}
\label{lem.pol.eval.finsum}
\lean{FPS.eval_eq_finsum}
\leanhelper
\leanok
The evaluation $f\left[a\right]$ equals
$\sum_{n\in\operatorname{supp}(f)}f_{n}\cdot a^{n}$,
making the finiteness of the sum explicit.
\end{lemma}
```

:::proof "lem.pol.eval.finsum"
This follows from the definition by restricting the sum to the support.
:::

```tex "lem.pol.eval.finsum" (slot := proof)
\begin{proof}
\leanok
This follows from the definition by restricting the sum to the support.
\end{proof}
```

:::lemma_ "lem.pol.eval.sum-range" (parent := "polynomials_evaluation") (lean := "FPS.eval_eq_sum_range")
The evaluation $`f[a]` equals
$`\sum_{n=0}^{\deg f} f_n\cdot a^n`, where the sum is taken up to the degree
of $`f`.
:::

```tex "lem.pol.eval.sum-range" (slot := statement)
\begin{lemma}
\label{lem.pol.eval.sum-range}
\lean{FPS.eval_eq_sum_range}
\leanhelper
\leanok
The evaluation $f\left[a\right]$ equals
$\sum_{n=0}^{\deg f}f_{n}\cdot a^{n}$,
where the sum is taken up to the degree of $f$.
\end{lemma}
```

:::proof "lem.pol.eval.sum-range"
Since all coefficients beyond the degree of $`f` are $`0`, extending or
restricting the sum to this range does not change the result.
:::

```tex "lem.pol.eval.sum-range" (slot := proof)
\begin{proof}
\leanok
Since all coefficients beyond the degree of $f$ are zero, extending or
restricting the sum to this range does not change the result.
\end{proof}
```
