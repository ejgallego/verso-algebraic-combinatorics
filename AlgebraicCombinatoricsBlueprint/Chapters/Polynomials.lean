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
