import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.DividingFPS

open Verso.Genre
open Verso.Genre.Manual
open Informal
open AlgebraicCombinatorics

#doc (Manual) "Dividing FPSs" =>

:::group "dividing_fps_scope"
This source chapter begins by recalling inverses and fractions in commutative
rings. That repeated ring-theory material is already ported in
`CommutativeRings`, so this chapter resumes at the first new FPS-specific
subsection.
:::

```tex
\section{Dividing FPSs}

\subsection{Inverses in $K[[x]]$}
```

:::group "fps_invertibility"
Invertibility criteria for formal power series.
:::

:::theorem "prop.fps.invertible" (parent := "fps_invertibility") (lean := "AlgebraicCombinatorics.fps_invertible_iff_constantCoeff")
Let $`a\in K[[x]]`.
Then the FPS $`a` is invertible in $`K[[x]]` if and only if its constant term
$`\left[x^{0}\right]a` is invertible in $`K`.
:::

```tex "prop.fps.invertible" (slot := statement)
\begin{proposition}
\label{prop.fps.invertible}
\lean{AlgebraicCombinatorics.fps_invertible_iff_constantCoeff}
\leantarget
\leanok
Let $a\in K[[x]]$.
Then, the FPS $a$ is invertible in $K[[x]]$ if
and only if its constant term $[x^{0}]a$ is invertible in $K$.
\end{proposition}
```

:::proof "prop.fps.invertible"
$`\Longrightarrow`: If $`ab=1`, then
$`\left[x^0\right]a\cdot\left[x^0\right]b = \left[x^0\right](ab)=1`
by the constant-term product lemma.

$`\Longleftarrow`: If $`\left[x^0\right]a=a_0` is invertible, define a sequence
$`(b_0,b_1,b_2,\ldots)` recursively by
$`b_0 = a_0^{-1}` and
$`b_n = -a_0^{-1}\sum_{k=1}^n a_k b_{n-k}` for $`n \ge 1`.
Then $`ab = 1`.
:::

```tex "prop.fps.invertible" (slot := proof)
\begin{proof}
\leanok
$\Longrightarrow$: If $ab=1$, then $[x^0]a\cdot[x^0]b = [x^0](ab)=1$
(by Lemma~\ref{lem.fps.coeff.zero.mul}).

$\Longleftarrow$: If $[x^0]a = a_0$ is invertible, define a sequence
$(b_0, b_1, b_2, \ldots)$ recursively by
$b_0 = a_0^{-1}$ (Lemma~\ref{lem.fps.inv-coeff-zero}) and
$b_n = -a_0^{-1}\sum_{k=1}^n a_k b_{n-k}$ for $n \geq 1$
(Lemma~\ref{lem.fps.inv-coeff-succ}).
Then $ab = 1$.
\end{proof}
```

:::corollary "cor.fps.invertible.field" (parent := "fps_invertibility") (lean := "AlgebraicCombinatorics.fps_invertible_iff_constantCoeff_ne_zero")
Assume that $`K` is a field. Let $`a\in K[[x]]`.
Then the FPS $`a` is invertible in $`K[[x]]` if and only if
$`\left[x^{0}\right]a\neq0`.
:::

```tex "cor.fps.invertible.field" (slot := statement)
\begin{corollary}
\label{cor.fps.invertible.field}
\lean{AlgebraicCombinatorics.fps_invertible_iff_constantCoeff_ne_zero}
\leantarget
\leanok
Assume that $K$ is a field. Let $a\in K[[x]]$.
Then, the FPS $a$ is invertible in $K[[x]]$ if and only if $[x^{0}]a\neq0$.
\end{corollary}
```

:::proof "cor.fps.invertible.field"
An element of $`K` is invertible in $`K` if and only if it is nonzero, since
$`K` is a field. Hence the corollary follows from the proposition above.
:::

```tex "cor.fps.invertible.field" (slot := proof)
\begin{proof}
\leanok
An element of $K$ is invertible in $K$ if and only if it is nonzero (since $K$
is a field). Hence, Corollary~\ref{cor.fps.invertible.field} follows from
Proposition~\ref{prop.fps.invertible}.
\end{proof}
```

:::group "fps_inverse_coefficients"
Coefficient formulas for inverses of formal power series.
:::

```tex
\subsection{Coefficient formulas for inverses}
```

:::lemma_ "lem.fps.inv-coeff-zero" (parent := "fps_inverse_coefficients") (lean := "AlgebraicCombinatorics.fps_inv_coeff_zero")
Assume that $`K` is a field. Let $`f\in K[[x]]`. Then the constant term of
$`f^{-1}` equals the inverse of the constant term of $`f`:
$$`\left[x^{0}\right]f^{-1} = \left(\left[x^{0}\right]f\right)^{-1}.`
:::

```tex "lem.fps.inv-coeff-zero" (slot := statement)
\begin{lemma}
\label{lem.fps.inv-coeff-zero}
\lean{AlgebraicCombinatorics.fps_inv_coeff_zero}
\leanhelper
\leanok
Assume that $K$ is a field. Let $f\in K[[x]]$. Then the constant term of $f^{-1}$
equals the inverse of the constant term of $f$:
\[
\left[x^{0}\right]f^{-1} = \left(\left[x^{0}\right]f\right)^{-1}.
\]
\end{lemma}
```

:::proof "lem.fps.inv-coeff-zero"
Direct consequence of the definition of the inverse of an FPS.
:::

```tex "lem.fps.inv-coeff-zero" (slot := proof)
\begin{proof}
Direct consequence of the definition of the inverse of an FPS.
\end{proof}
```

:::lemma_ "lem.fps.inv-coeff-succ" (parent := "fps_inverse_coefficients") (lean := "AlgebraicCombinatorics.fps_inv_coeff_succ")
Assume that $`K` is a field. Let $`f\in K[[x]]`. For each $`n\in\mathbb{N}`,
$$`\left[x^{n+1}\right]f^{-1}
= -\left(\left[x^{0}\right]f\right)^{-1}\sum_{k=0}^{n}\left[x^{k+1}\right]f\cdot
\left[x^{n-k}\right]f^{-1}.`
This recurrence allows computing the coefficients of $`f^{-1}` one by one.
:::

```tex "lem.fps.inv-coeff-succ" (slot := statement)
\begin{lemma}
\label{lem.fps.inv-coeff-succ}
\lean{AlgebraicCombinatorics.fps_inv_coeff_succ}
\leanhelper
\leanok
Assume that $K$ is a field. Let $f\in K[[x]]$. For each $n\in\mathbb{N}$,
\[
\left[x^{n+1}\right]f^{-1}
= -\left(\left[x^{0}\right]f\right)^{-1}\sum_{k=0}^{n}\left[x^{k+1}\right]f\cdot
\left[x^{n-k}\right]f^{-1}.
\]
This recurrence allows computing the coefficients of $f^{-1}$ one by one.
\end{lemma}
```

:::proof "lem.fps.inv-coeff-succ"
This follows from the recurrence relation for the coefficients of $`f^{-1}`
obtained by expanding the equation $`f\cdot f^{-1}=1` and solving for
$`\left[x^{n+1}\right]f^{-1}`.
:::

```tex "lem.fps.inv-coeff-succ" (slot := proof)
\begin{proof}
Follows from the recurrence relation for the coefficients of $f^{-1}$ obtained
by expanding the equation $f\cdot f^{-1}=1$ and solving for $[x^{n+1}]f^{-1}$.
\end{proof}
```

:::lemma_ "lem.fps.isUnit-inv-eq-inv" (parent := "fps_inverse_coefficients") (lean := "AlgebraicCombinatorics.fps_isUnit_inv_eq_inv")
Assume that $`K` is a field. Let $`f\in K[[x]]` be an invertible FPS.
Then the inverse of $`f` obtained from the invertibility proof equals
$`f^{-1}`, the inverse as defined in the power series ring.
:::

```tex "lem.fps.isUnit-inv-eq-inv" (slot := statement)
\begin{lemma}
\label{lem.fps.isUnit-inv-eq-inv}
\lean{AlgebraicCombinatorics.fps_isUnit_inv_eq_inv}
\leanhelper
\leanok
Assume that $K$ is a field. Let $f\in K[[x]]$ be an invertible FPS.
Then the inverse of $f$ obtained from the invertibility proof equals
$f^{-1}$ (the inverse as defined in the power series ring).
\end{lemma}
```

:::proof "lem.fps.isUnit-inv-eq-inv"
Both satisfy $`f\cdot g = 1`, and inverses are unique.
:::

```tex "lem.fps.isUnit-inv-eq-inv" (slot := proof)
\begin{proof}
\leanok
Both satisfy $f\cdot g = 1$, and inverses are unique
(Theorem~\ref{thm.commring.inverse-uni}).
\end{proof}
```

:::lemma_ "lem.fps.inv-coeff-zero-isUnit" (parent := "fps_inverse_coefficients") (lean := "AlgebraicCombinatorics.fps_inv_coeff_zero_isUnit")
Assume that $`K` is a field. Let $`f\in K[[x]]` be an invertible FPS. Then
$$`\left[x^{0}\right]f^{-1} = \left(\left[x^{0}\right]f\right)^{-1}.`
:::

```tex "lem.fps.inv-coeff-zero-isUnit" (slot := statement)
\begin{lemma}
\label{lem.fps.inv-coeff-zero-isUnit}
\lean{AlgebraicCombinatorics.fps_inv_coeff_zero_isUnit}
\leanhelper
\leanok
Assume that $K$ is a field. Let $f\in K[[x]]$ be an invertible FPS. Then
\[
\left[x^{0}\right]f^{-1} = \left(\left[x^{0}\right]f\right)^{-1}.
\]
\end{lemma}
```

:::proof "lem.fps.inv-coeff-zero-isUnit"
By the previous lemma, the inverse obtained from the invertibility proof equals
$`f^{-1}`, so the result follows from the lemma on the constant term of the
inverse.
:::

```tex "lem.fps.inv-coeff-zero-isUnit" (slot := proof)
\begin{proof}
\leanok
By Lemma~\ref{lem.fps.isUnit-inv-eq-inv}, the inverse obtained from
the invertibility proof equals $f^{-1}$,
so the result follows from Lemma~\ref{lem.fps.inv-coeff-zero}.
\end{proof}
```

:::lemma_ "lem.fps.inv-coeff-succ-isUnit" (parent := "fps_inverse_coefficients") (lean := "AlgebraicCombinatorics.fps_inv_coeff_succ_isUnit")
Assume that $`K` is a field. Let $`f\in K[[x]]` be an invertible FPS. For
each $`n\in\mathbb{N}`,
$$`\left[x^{n+1}\right]f^{-1}
= -\left(\left[x^{0}\right]f\right)^{-1}\sum_{k=0}^{n}\left[x^{k+1}\right]f\cdot
\left[x^{n-k}\right]f^{-1}.`
:::

```tex "lem.fps.inv-coeff-succ-isUnit" (slot := statement)
\begin{lemma}
\label{lem.fps.inv-coeff-succ-isUnit}
\lean{AlgebraicCombinatorics.fps_inv_coeff_succ_isUnit}
\leanhelper
\leanok
Assume that $K$ is a field. Let $f\in K[[x]]$ be an invertible FPS. For each
$n\in\mathbb{N}$,
\[
\left[x^{n+1}\right]f^{-1}
= -\left(\left[x^{0}\right]f\right)^{-1}\sum_{k=0}^{n}\left[x^{k+1}\right]f\cdot
\left[x^{n-k}\right]f^{-1}.
\]
\end{lemma}
```

:::proof "lem.fps.inv-coeff-succ-isUnit"
By the previous lemma, the inverse obtained from the invertibility proof equals
$`f^{-1}`, so the result follows from the recurrence lemma for inverse
coefficients.
:::

```tex "lem.fps.inv-coeff-succ-isUnit" (slot := proof)
\begin{proof}
By Lemma~\ref{lem.fps.isUnit-inv-eq-inv}, the inverse obtained from
the invertibility proof equals $f^{-1}$,
so the result follows from Lemma~\ref{lem.fps.inv-coeff-succ}.
\end{proof}
```

:::group "fps_newton_binomial"
Newton's binomial formula and its negative-exponent variants.
:::

```tex
\subsection{Newton's binomial formula}
```

:::theorem "prop.fps.invertible.1+x" (parent := "fps_newton_binomial") (lean := "AlgebraicCombinatorics.fps_onePlusX_isUnit, AlgebraicCombinatorics.fps_onePlusX_inv")
The FPS $`1+x\in K[[x]]` is invertible, and its inverse is
$$`\left(1+x\right)^{-1}=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n}.`
:::

```tex "prop.fps.invertible.1+x" (slot := statement)
\begin{proposition}
\label{prop.fps.invertible.1+x}
\lean{AlgebraicCombinatorics.fps_onePlusX_isUnit, AlgebraicCombinatorics.fps_onePlusX_inv}
\leantarget
\leanok
The FPS $1+x\in K[[x]]$ is invertible, and its inverse is%
\[
\left(1+x\right)^{-1}=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n}.
\]
\end{proposition}
```

:::proof "prop.fps.invertible.1+x"
Direct computation:
$`(1+x)\cdot\sum_{n\geq 0}(-1)^n x^n = 1` by telescoping. All powers of
$`x` other than $`1` cancel out.
:::

```tex "prop.fps.invertible.1+x" (slot := proof)
\begin{proof}
\leanok
Direct computation: $(1+x)\cdot\sum_{n\geq 0}(-1)^n x^n = 1$ by telescoping
(all powers of $x$ other than $1$ cancel out).
\end{proof}
```

:::theorem "thm.fps.newton-binom" (parent := "fps_newton_binomial") (lean := "AlgebraicCombinatorics.fps_newtonBinomial_nat, AlgebraicCombinatorics.fps_newtonBinomial_neg")
For each $`n\in\mathbb{Z}`, we have
$$`\left(1+x\right)^{n}=\sum_{k\in\mathbb{N}}\dbinom{n}{k}x^{k}.`
:::

```tex "thm.fps.newton-binom" (slot := statement)
\begin{theorem}
\label{thm.fps.newton-binom}
\lean{AlgebraicCombinatorics.fps_newtonBinomial_nat, AlgebraicCombinatorics.fps_newtonBinomial_neg}
\leantarget
\leanok
For each $n\in\mathbb{Z}$, we have%
\[
\left(1+x\right)^{n}=\sum_{k\in\mathbb{N}}\dbinom{n}{k}x^{k}.
\]
\end{theorem}
```

:::proof "thm.fps.newton-binom"
For $`n\geq 0`, this is the standard binomial theorem: the sum
$`\sum_{k\in\mathbb{N}}\dbinom{n}{k}x^{k}` reduces to
$`\sum_{k=0}^{n}\dbinom{n}{k}x^{k}` since $`\dbinom{n}{k}=0` for $`k>n`.

For $`n<0`, we have $`-n\in\mathbb{N}`, so the corollary for negative natural
powers, applied to $`-n`, yields
$`\left(1+x\right)^{-(-n)} = \sum_{k\in\mathbb{N}}\dbinom{-(-n)}{k}x^k`,
which rewrites as
$`\left(1+x\right)^n = \sum_{k\in\mathbb{N}}\dbinom{n}{k}x^k`.
:::

```tex "thm.fps.newton-binom" (slot := proof)
\begin{proof}
\leanok
For $n\geq 0$, this is the standard binomial theorem (the sum
$\sum_{k\in\mathbb{N}}\dbinom{n}{k}x^{k}$ reduces to $\sum_{k=0}^{n}\dbinom{n}{k}x^{k}$
since $\dbinom{n}{k}=0$ for $k > n$ by Proposition~\ref{prop.binom.0}).

For $n<0$, we have $-n\in\mathbb{N}$, so Corollary~\ref{cor.fps.anti-newton-binom-2}
(applied to $-n$ instead of $n$) yields
$\left(1+x\right)^{-(-n)} = \sum_{k\in\mathbb{N}}\dbinom{-(-n)}{k}x^k$,
which rewrites as $\left(1+x\right)^n = \sum_{k\in\mathbb{N}}\dbinom{n}{k}x^k$.
\end{proof}
```

:::theorem "thm.binom.upneg-n" (parent := "fps_newton_binomial") (lean := "AlgebraicCombinatorics.binomUpperNegation, AlgebraicCombinatorics.binomUpperNegation_int")
Let $`n\in\mathbb{C}` and $`k\in\mathbb{Z}`. Then
$$`\dbinom{-n}{k}=\left(-1\right)^{k}\dbinom{k+n-1}{k}.`
:::

```tex "thm.binom.upneg-n" (slot := statement)
\begin{theorem}
\label{thm.binom.upneg-n}
\lean{AlgebraicCombinatorics.binomUpperNegation, AlgebraicCombinatorics.binomUpperNegation_int}
\leantarget
\leanok
Let $n\in\mathbb{C}$ and $k\in\mathbb{Z}$. Then,%
\[
\dbinom{-n}{k}=\left(-1\right)^{k}\dbinom{k+n-1}{k}.
\]
\end{theorem}
```

:::proof "thm.binom.upneg-n"
If $`k<0`, then both $`\dbinom{-n}{k}` and $`\dbinom{k+n-1}{k}` are $`0`.
For $`k\geq 0`, expand using the definition and observe that the numerators
differ by a factor of $`\left(-1\right)^{k}`.
:::

```tex "thm.binom.upneg-n" (slot := proof)
\begin{proof}
\leanok
If $k<0$, then both $\dbinom{-n}{k}$ and $\dbinom{k+n-1}{k}$ are $0$.
For $k\geq 0$, expand using the definition and
observe the numerators differ by a factor of $(-1)^k$.
\end{proof}
```

:::theorem "prop.fps.anti-newton-binom" (parent := "fps_newton_binomial") (lean := "AlgebraicCombinatorics.fps_onePlusX_pow_neg")
For each $`n\in\mathbb{N}`, we have
$$`\left(1+x\right)^{-n}=\sum_{k\in\mathbb{N}}\left(-1\right)^{k}\dbinom{n+k-1}{k}x^{k}.`
:::

```tex "prop.fps.anti-newton-binom" (slot := statement)
\begin{proposition}
\label{prop.fps.anti-newton-binom}
\lean{AlgebraicCombinatorics.fps_onePlusX_pow_neg}
\leantarget
\leanok
For each $n\in\mathbb{N}$, we have%
\[
\left(1+x\right)^{-n}=\sum_{k\in\mathbb{N}}\left(-1\right)^{k}%
\dbinom{n+k-1}{k}x^{k}.
\]
\end{proposition}
```

:::proof "prop.fps.anti-newton-binom"
By induction on $`n`.

_Induction base:_ $`\left(1+x\right)^{-0} = 1`, and
$`\sum_{k\in\mathbb{N}} (-1)^k \dbinom{0+k-1}{k} x^k = 1`
since $`\dbinom{k-1}{k} = 0` for all $`k > 0`.

_Induction step:_ Assume the formula holds for $`n = j`. We must prove it for
$`n = j+1`. We have
$`\left(1+x\right)^{-(j+1)} = \left(1+x\right)^{-j} \cdot \left(1+x\right)^{-1}`.
Using the induction hypothesis and multiplying by $`1+x`, it suffices to show
$$`\left(1+x\right)^{-j} = \left(\sum_{k\in\mathbb{N}} (-1)^k \dbinom{j+k}{k} x^k\right) \cdot \left(1+x\right).`
Expanding the right hand side, using Pascal's identity
$`\dbinom{j+k}{k} = \dbinom{j+k-1}{k-1} + \dbinom{j+k-1}{k}` and collecting
terms, the $`\dbinom{j+k-1}{k-1}` terms telescope, and we obtain
$`\sum_{k\in\mathbb{N}} (-1)^k \dbinom{j+k-1}{k} x^k = \left(1+x\right)^{-j}`
by the induction hypothesis.
:::

```tex "prop.fps.anti-newton-binom" (slot := proof)
\begin{proof}
By induction on $n$.

\textit{Induction base:} $\left(1+x\right)^{-0} = 1$, and
$\sum_{k\in\mathbb{N}} (-1)^k \dbinom{0+k-1}{k} x^k = 1$
since $\dbinom{k-1}{k} = 0$ for all $k > 0$ (by Proposition~\ref{prop.binom.0}).

\textit{Induction step:} Assume the formula holds for $n = j$. We must prove it for $n = j+1$.
We have $\left(1+x\right)^{-(j+1)} = \left(1+x\right)^{-j} \cdot \left(1+x\right)^{-1}$.
Using the induction hypothesis and multiplying by $1+x$, it suffices to show
\[
\left(1+x\right)^{-j} = \left(\sum_{k\in\mathbb{N}} (-1)^k \dbinom{j+k}{k} x^k\right) \cdot \left(1+x\right).
\]
Expanding the right hand side, using Pascal's identity
$\dbinom{j+k}{k} = \dbinom{j+k-1}{k-1} + \dbinom{j+k-1}{k}$
(Proposition~\ref{prop.binom.rec}), and collecting terms (the
$\dbinom{j+k-1}{k-1}$ terms telescope), we obtain
$\sum_{k\in\mathbb{N}} (-1)^k \dbinom{j+k-1}{k} x^k = \left(1+x\right)^{-j}$
by the induction hypothesis.
\end{proof}
```

:::corollary "cor.fps.anti-newton-binom-2" (parent := "fps_newton_binomial") (lean := "AlgebraicCombinatorics.fps_onePlusX_pow_neg'")
For each $`n\in\mathbb{N}`, we have
$$`\left(1+x\right)^{-n}=\sum_{k\in\mathbb{N}}\dbinom{-n}{k}x^{k}.`
:::

```tex "cor.fps.anti-newton-binom-2" (slot := statement)
\begin{corollary}
\label{cor.fps.anti-newton-binom-2}
\lean{AlgebraicCombinatorics.fps_onePlusX_pow_neg'}
\leantarget
\leanok
For each $n\in\mathbb{N}$, we have%
\[
\left(1+x\right)^{-n}=\sum_{k\in\mathbb{N}}\dbinom{-n}{k}x^{k}.
\]
\end{corollary}
```

:::proof "cor.fps.anti-newton-binom-2"
The previous proposition yields
$`\left(1+x\right)^{-n} = \sum_{k\in\mathbb{N}} (-1)^k \dbinom{n+k-1}{k} x^k`.
By the upper-negation theorem, we have
$`(-1)^k \dbinom{n+k-1}{k} = (-1)^k \dbinom{k+n-1}{k} = \dbinom{-n}{k}`.
:::

```tex "cor.fps.anti-newton-binom-2" (slot := proof)
\begin{proof}
\leanok
Proposition~\ref{prop.fps.anti-newton-binom} yields
$\left(1+x\right)^{-n} = \sum_{k\in\mathbb{N}} (-1)^k \dbinom{n+k-1}{k} x^k$.
By Theorem~\ref{thm.binom.upneg-n}, we have
$(-1)^k \dbinom{n+k-1}{k} = (-1)^k \dbinom{k+n-1}{k} = \dbinom{-n}{k}$.
\end{proof}
```

:::group "fps_div_by_x"
Division by the indeterminate x.
:::

```tex
\subsection{Dividing by $x$}
```

:::definition "def.fps.div-by-x" (parent := "fps_div_by_x") (lean := "AlgebraicCombinatorics.PowerSeries.divByX")
Let $`a=\left(a_{0},a_{1},a_{2},\ldots\right)` be an FPS whose constant term
$`a_{0}` is $`0`. Then $`\dfrac{a}{x}` is defined to be the FPS
$`\left(a_{1},a_{2},a_{3},\ldots\right)`.
:::

```tex "def.fps.div-by-x" (slot := statement)
\begin{definition}
\label{def.fps.div-by-x}
\lean{AlgebraicCombinatorics.PowerSeries.divByX}
\leantarget
\leanok
Let $a=\left(a_{0},a_{1},a_{2},\ldots\right)$ be
an FPS whose constant term $a_{0}$ is $0$. Then, $\dfrac{a}{x}$ is defined to
be the FPS $\left(a_{1},a_{2},a_{3},\ldots\right)$.
\end{definition}
```

:::lemma_ "lem.fps.coeff-divByX" (parent := "fps_div_by_x") (lean := "AlgebraicCombinatorics.PowerSeries.coeff_divByX")
Let $`a\in K[[x]]` with $`\left[x^0\right]a=0`. Then for each
$`n\in\mathbb{N}`,
$$`\left[x^{n}\right]\frac{a}{x} = \left[x^{n+1}\right]a.`
:::

```tex "lem.fps.coeff-divByX" (slot := statement)
\begin{lemma}
\label{lem.fps.coeff-divByX}
\lean{AlgebraicCombinatorics.PowerSeries.coeff_divByX}
\leanhelper
\leanok
Let $a\in K[[x]]$ with $[x^0]a=0$. Then for each $n\in\mathbb{N}$,
\[
\left[x^{n}\right]\frac{a}{x} = \left[x^{n+1}\right]a.
\]
\end{lemma}
```

:::proof "lem.fps.coeff-divByX"
By definition, $`\frac{a}{x}=(a_1,a_2,a_3,\ldots)`, so its $`n`-th
coefficient is $`a_{n+1}=[x^{n+1}]a`.
:::

```tex "lem.fps.coeff-divByX" (slot := proof)
\begin{proof}
\leanok
By definition, $\frac{a}{x}=(a_1,a_2,a_3,\ldots)$, so its $n$-th coefficient
is $a_{n+1}=[x^{n+1}]a$.
\end{proof}
```

:::theorem "prop.fps.div-by-x-inverts" (parent := "fps_div_by_x") (lean := "AlgebraicCombinatorics.fps_eq_X_mul_iff")
Let $`a,b\in K[[x]]` be two FPSs. Then $`a=xb` if and only if
$`\left[x^{0}\right]a=0` and $`b=\dfrac{a}{x}`.
:::

```tex "prop.fps.div-by-x-inverts" (slot := statement)
\begin{proposition}
\label{prop.fps.div-by-x-inverts}
\lean{AlgebraicCombinatorics.fps_eq_X_mul_iff}
\leantarget
\leanok
Let $a,b\in K[[x]]$ be two FPSs. Then, $a=xb$ if
and only if $\left[x^{0}\right]a=0$ and $b=\dfrac{a}{x}$.
\end{proposition}
```

:::proof "prop.fps.div-by-x-inverts"
This follows directly from the definitions.
:::

```tex "prop.fps.div-by-x-inverts" (slot := proof)
\begin{proof}
\leanok
Follows directly from the definitions.
\end{proof}
```

:::group "fps_div_by_x_helpers"
Helpers for division by x.
:::

```tex
\subsubsection{Helpers for division by $x$}
```

:::lemma_ "lem.fps.eq-X-mul-divByX" (parent := "fps_div_by_x_helpers") (lean := "AlgebraicCombinatorics.fps_eq_X_mul_divByX")
Let $`a\in K[[x]]` with $`\left[x^0\right]a=0`. Then
$`a = x\cdot\frac{a}{x}`.
:::

```tex "lem.fps.eq-X-mul-divByX" (slot := statement)
\begin{lemma}
\label{lem.fps.eq-X-mul-divByX}
\lean{AlgebraicCombinatorics.fps_eq_X_mul_divByX}
\leanhelper
\leanok
Let $a\in K[[x]]$ with $[x^0]a=0$. Then $a = x\cdot\frac{a}{x}$.
\end{lemma}
```

:::proof "lem.fps.eq-X-mul-divByX"
This follows from the previous proposition: setting $`b=\frac{a}{x}`, the
right-to-left direction gives $`a=xb`.
:::

```tex "lem.fps.eq-X-mul-divByX" (slot := proof)
\begin{proof}
\leanok
Follows from Proposition~\ref{prop.fps.div-by-x-inverts}: setting
$b=\frac{a}{x}$, the right-to-left direction gives $a=xb$.
\end{proof}
```

:::lemma_ "lem.fps.divByX-X-mul" (parent := "fps_div_by_x_helpers") (lean := "AlgebraicCombinatorics.fps_divByX_X_mul")
For any FPS $`b\in K[[x]]`, we have $`\frac{xb}{x}=b`.
:::

```tex "lem.fps.divByX-X-mul" (slot := statement)
\begin{lemma}
\label{lem.fps.divByX-X-mul}
\lean{AlgebraicCombinatorics.fps_divByX_X_mul}
\leanhelper
\leanok
For any FPS $b\in K[[x]]$, we have $\frac{xb}{x}=b$.
\end{lemma}
```

:::proof "lem.fps.divByX-X-mul"
For each $`n\in\mathbb{N}`,
$`[x^n]\frac{xb}{x}=[x^{n+1}](xb)=[x^n]b`,
by the coefficient formula for $`\frac{a}{x}` and the coefficient formula for
$`xb`.
:::

```tex "lem.fps.divByX-X-mul" (slot := proof)
\begin{proof}
\leanok
For each $n\in\mathbb{N}$, $[x^n]\frac{xb}{x}=[x^{n+1}](xb)=[x^n]b$
(by Lemma~\ref{lem.fps.coeff-divByX} and the coefficient formula for $xb$).
\end{proof}
```

:::group "fps_misc_lemmas"
Auxiliary coefficient lemmas about multiples of powers of the indeterminate.
:::

```tex
\subsection{A few lemmas}
```

:::lemma_ "lem.fps.g=xh" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_exists_X_mul_of_constantCoeff_zero")
Let $`a\in K[[x]]` be an FPS with $`\left[x^{0}\right]a=0`. Then there exists
an $`h\in K[[x]]` such that $`a=xh`.
:::

```tex "lem.fps.g=xh" (slot := statement)
\begin{lemma}
\label{lem.fps.g=xh}
\lean{AlgebraicCombinatorics.fps_exists_X_mul_of_constantCoeff_zero}
\leantarget
\leanok
Let $a\in K[[x]]$ be an FPS
with $\left[x^{0}\right]a=0$. Then, there exists an $h\in K[[x]]$ such that $a=xh$.
\end{lemma}
```

:::proof "lem.fps.g=xh"
The FPS $`\frac{a}{x}` is well-defined because the constant term of $`a` is
$`0`. Set $`h=\frac{a}{x}`. Then the lemma on reconstructing a series from its
quotient by $`x` gives $`a = x\cdot h`.
:::

```tex "lem.fps.g=xh" (slot := proof)
\begin{proof}
\leanok
The FPS $\dfrac{a}{x}$ is well-defined (since $a_0 = 0$).
Set $h = \dfrac{a}{x}$; then $a = x \cdot \dfrac{a}{x} = xh$
(by Lemma~\ref{lem.fps.eq-X-mul-divByX}).
\end{proof}
```

:::lemma_ "lem.fps.first-n-coeffs-of-xna" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_coeff_X_pow_mul_eq_zero")
Let $`k\in\mathbb{N}`. Let $`a\in K[[x]]` be any FPS. Then the first $`k`
coefficients of the FPS $`x^{k}a` are $`0`.
:::

```tex "lem.fps.first-n-coeffs-of-xna" (slot := statement)
\begin{lemma}
\label{lem.fps.first-n-coeffs-of-xna}
\lean{AlgebraicCombinatorics.fps_coeff_X_pow_mul_eq_zero}
\leantarget
\leanok
Let $k\in\mathbb{N}$. Let $a\in K[[x]]$ be any FPS. Then, the first $k$ coefficients of
the FPS $x^{k}a$ are $0$.
\end{lemma}
```

:::proof "lem.fps.first-n-coeffs-of-xna"
If $`m<k`, then
$$`\left[x^m\right](x^k a)
= \sum_{i=0}^{m} \left[x^i\right](x^k)\cdot \left[x^{m-i}\right]a.`
But $`\left[x^i\right](x^k)=0` for every $`i\le m<k`, so each summand is
$`0`.
:::

```tex "lem.fps.first-n-coeffs-of-xna" (slot := proof)
\begin{proof}
\leanok
For $m<k$, we have
$[x^m](x^k a) = \sum_{i=0}^{m} [x^i](x^k)\cdot [x^{m-i}]a = 0$
since $[x^i](x^k) = 0$ for all $i\leq m < k$.
\end{proof}
```

:::lemma_ "lem.fps.muls-of-xn" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_first_k_coeffs_zero_iff_X_pow_dvd")
Let $`k\in\mathbb{N}`. Let $`f\in K[[x]]` be any FPS. Then the first $`k`
coefficients of $`f` are $`0` if and only if $`f` is a multiple of $`x^k`.
:::

```tex "lem.fps.muls-of-xn" (slot := statement)
\begin{lemma}
\label{lem.fps.muls-of-xn}
\lean{AlgebraicCombinatorics.fps_first_k_coeffs_zero_iff_X_pow_dvd}
\leantarget
\leanok
Let $k\in\mathbb{N}$. Let $f\in K[[x]]$ be any FPS. Then, the first $k$ coefficients of
$f$ are $0$ if and only if $f$ is a multiple of $x^{k}$.
\end{lemma}
```

:::proof "lem.fps.muls-of-xn"
$`\Longleftarrow`: This is the previous lemma.

$`\Longrightarrow`: If the first $`k` coefficients of $`f` vanish, then
$`f = \sum_{n\ge k} f_n x^n = x^k \sum_{n\ge k} f_n x^{n-k}`, so $`f` is a
multiple of $`x^k`.
:::

```tex "lem.fps.muls-of-xn" (slot := proof)
\begin{proof}
\leanok
$\Longleftarrow$: By Lemma~\ref{lem.fps.first-n-coeffs-of-xna}.

$\Longrightarrow$: If $f_n = 0$ for each $n \in \{0, 1, \ldots, k-1\}$, then
$f = \sum_{n \geq k} f_n x^n = x^k \sum_{n \geq k} f_n x^{n-k}$.
\end{proof}
```

:::lemma_ "lem.fps.prod.irlv.fg" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_coeff_mul_eq_of_coeff_eq")
Let $`a,f,g\in K[[x]]` be three FPSs. Let $`n\in\mathbb{N}`. Assume that
$`\left[x^{m}\right]f=\left[x^{m}\right]g` for each
$`m\in\{0,1,\ldots,n\}`. Then
$`\left[x^{m}\right](af)=\left[x^{m}\right](ag)` for each
$`m\in\{0,1,\ldots,n\}`.
:::

```tex "lem.fps.prod.irlv.fg" (slot := statement)
\begin{lemma}
\label{lem.fps.prod.irlv.fg}
\lean{AlgebraicCombinatorics.fps_coeff_mul_eq_of_coeff_eq}
\leantarget
\leanok
Let $a,f,g\in K[[x]]$ be three FPSs. Let $n\in\mathbb{N}$. Assume that
$[x^{m}]f=[x^{m}]g$ for each $m\in\{0,1,\ldots,n\}$.
Then,
$[x^{m}](af)=[x^{m}](ag)$ for each $m\in\{0,1,\ldots,n\}$.
\end{lemma}
```

:::proof "lem.fps.prod.irlv.fg"
Fix $`m\in\{0,1,\ldots,n\}`. For each $`j\in\{0,1,\ldots,m\}`, we have
$`j\le m\le n`, hence $`\left[x^j\right]f=\left[x^j\right]g`. Expanding the
coefficient of a product therefore gives the same finite sum for
$`\left[x^m\right](af)` and $`\left[x^m\right](ag)`.
:::

```tex "lem.fps.prod.irlv.fg" (slot := proof)
\begin{proof}
\leanok
Let $m \in \{0,1,\ldots,n\}$. Each $j \in \{0,1,\ldots,m\}$ satisfies $j \leq m \leq n$
and thus $[x^j]f = [x^j]g$. Hence,
$[x^m](af) = \sum_{j=0}^m [x^{m-j}]a \cdot [x^j]f
= \sum_{j=0}^m [x^{m-j}]a \cdot [x^j]g = [x^m](ag)$.
\end{proof}
```

:::lemma_ "lem.fps.prod.irlv.mul" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_coeff_zero_of_multiple")
Let $`u,v\in K[[x]]` be two FPSs such that $`v` is a multiple of $`u`. Let
$`n\in\mathbb{N}`. Assume $`\left[x^{m}\right]u=0` for each
$`m\in\{0,1,\ldots,n\}`. Then $`\left[x^{m}\right]v=0` for each
$`m\in\{0,1,\ldots,n\}`.
:::

```tex "lem.fps.prod.irlv.mul" (slot := statement)
\begin{lemma}
\label{lem.fps.prod.irlv.mul}
\lean{AlgebraicCombinatorics.fps_coeff_zero_of_multiple}
\leantarget
\leanok
Let $u,v\in K[[x]]$ be two FPSs such that $v$ is a multiple of $u$. Let $n\in\mathbb{N}$. Assume
$[x^{m}]u=0$ for each $m\in\{0,1,\ldots,n\}$.
Then $[x^{m}]v=0$ for each $m\in\{0,1,\ldots,n\}$.
\end{lemma}
```

:::proof "lem.fps.prod.irlv.mul"
Write $`v=ua`. Since $`\left[x^m\right]u=0=\left[x^m\right]0` for each
$`m\le n`, the previous lemma applied to $`f=u` and $`g=0` yields
$`\left[x^m\right](au)=\left[x^m\right](a\cdot 0)=0`. Because $`v=ua=au`,
the same holds for $`v`.
:::

```tex "lem.fps.prod.irlv.mul" (slot := proof)
\begin{proof}
\leanok
Write $v=ua$. We have $[x^m]u = 0 = [x^m]0$ for each $m \in \{0,1,\ldots,n\}$.
Lemma~\ref{lem.fps.prod.irlv.fg} (applied to $f=u$ and $g=0$) yields
$[x^m](au) = [x^m](a \cdot 0) = 0$ for each $m \in \{0,1,\ldots,n\}$.
Since $v = ua = au$, we get $[x^m]v = 0$.
\end{proof}
```

:::lemma_ "lem.fps.prod.irlv.cong-mul" (parent := "fps_misc_lemmas") (lean := "AlgebraicCombinatorics.fps_coeff_mul_eq_of_both_coeff_eq")
Let $`a,b,c,d\in K[[x]]` be four FPSs. Let $`n\in\mathbb{N}`. Assume
$`\left[x^{m}\right]a=\left[x^{m}\right]b` and
$`\left[x^{m}\right]c=\left[x^{m}\right]d` for each
$`m\in\{0,1,\ldots,n\}`. Then
$`\left[x^{m}\right](ac)=\left[x^{m}\right](bd)` for each
$`m\in\{0,1,\ldots,n\}`.
:::

```tex "lem.fps.prod.irlv.cong-mul" (slot := statement)
\begin{lemma}
\label{lem.fps.prod.irlv.cong-mul}
\lean{AlgebraicCombinatorics.fps_coeff_mul_eq_of_both_coeff_eq}
\leantarget
\leanok
Let $a,b,c,d\in K[[x]]$ be four FPSs. Let $n\in\mathbb{N}$. Assume
$[x^{m}]a=[x^{m}]b$ and $[x^{m}]c=[x^{m}]d$ for each $m\in\{0,1,\ldots,n\}$.
Then $[x^{m}](ac)=[x^{m}](bd)$ for each $m\in\{0,1,\ldots,n\}$.
\end{lemma}
```

:::proof "lem.fps.prod.irlv.cong-mul"
The difference $`ac-bc=(a-b)c` is a multiple of $`a-b`, and the coefficients
of $`a-b` up to degree $`n` vanish. The previous lemma therefore gives
$`\left[x^m\right](ac)=\left[x^m\right](bc)` for $`m\le n`.

Applying the same argument to $`bc-bd=b(c-d)` shows
$`\left[x^m\right](bc)=\left[x^m\right](bd)` for $`m\le n`.

Combining the two equalities yields the claim.
:::

```tex "lem.fps.prod.irlv.cong-mul" (slot := proof)
\begin{proof}
\leanok
The FPS $ac - bc = (a-b)c$ is a multiple of $a-b$, and $[x^m](a-b) = 0$
for each $m \in \{0,1,\ldots,n\}$. By Lemma~\ref{lem.fps.prod.irlv.mul},
$[x^m](ac - bc) = 0$, so $[x^m](ac) = [x^m](bc)$.

Similarly, $bc - bd = b(c-d) = (c-d)b$ is a multiple of $c-d$, and
$[x^m](c-d) = 0$. By Lemma~\ref{lem.fps.prod.irlv.mul},
$[x^m](bc - bd) = 0$, so $[x^m](bc) = [x^m](bd)$.

Combining: $[x^m](ac) = [x^m](bc) = [x^m](bd)$.
\end{proof}
```
