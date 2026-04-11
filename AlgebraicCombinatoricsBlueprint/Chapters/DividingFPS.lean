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
