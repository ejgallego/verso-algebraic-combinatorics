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
