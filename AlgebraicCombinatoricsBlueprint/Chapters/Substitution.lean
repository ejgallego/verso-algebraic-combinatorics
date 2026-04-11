import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.Substitution

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Substitution and Evaluation of Power Series" =>

:::group "substitution_definition"
Defining composition of formal power series.
:::

```tex
\section{Substitution and evaluation of power series}

\subsection{Defining substitution}
```

:::definition "def.fps.subs" (parent := "substitution_definition") (lean := "AlgebraicCombinatorics.fps_comp, AlgebraicCombinatorics.fps_comp_coeff, AlgebraicCombinatorics.fps_comp_coeff_finite")
Let $`f` and $`g` be two FPSs in $`K[[x]]`. Assume that
$`\left[x^0\right]g = 0`; that is,
$`g = g_1 x + g_2 x^2 + g_3 x^3 + \cdots` for some coefficients in $`K`.

We then define an FPS $`f[g]\in K[[x]]` as follows.

Write $`f` in the form $`f = \sum_{n\in\mathbb{N}} f_n x^n` with
$`f_n = \left[x^n\right]f` for each $`n\in\mathbb{N}`. Then set
$$`f[g] := \sum_{n\in\mathbb{N}} f_n g^n.`
This sum is well-defined, as established below.

This FPS $`f[g]` is also denoted by $`f\circ g`, and is called the
_composition_ of $`f` with $`g`, or the result of _substituting_ $`g` for
$`x` in $`f`.

Equivalently, the $`n`-th coefficient of $`f[g]` is the finite sum
$$`\left[x^n\right](f[g]) = \sum_{d=0}^{n} f_d \cdot \left[x^n\right](g^d).`
:::

```tex "def.fps.subs" (slot := statement)
\begin{definition}
\label{def.fps.subs}
\lean{AlgebraicCombinatorics.fps_comp, AlgebraicCombinatorics.fps_comp_coeff, AlgebraicCombinatorics.fps_comp_coeff_finite}
\leantarget
\leanok
Let $f$ and $g$ be two FPSs in $K[[x]]$. Assume that $[x^0]g = 0$
(that is, $g = g_1 x + g_2 x^2 + g_3 x^3 + \cdots$ for some
$g_1, g_2, g_3, \ldots \in K$).

We then define an FPS $f[g] \in K[[x]]$ as follows:

Write $f$ in the form $f = \sum_{n \in \mathbb{N}} f_n x^n$ with
$f_0, f_1, f_2, \ldots \in K$. (That is, $f_n = [x^n]f$ for each
$n \in \mathbb{N}$.) Then, set
\[
f[g] := \sum_{n \in \mathbb{N}} f_n g^n.
\]
(This sum is well-defined, as we will see in Proposition
\ref{prop.fps.subs.wd} \textbf{(b)} below.)

This FPS $f[g]$ is also denoted by $f \circ g$, and is called the
\emph{composition} of $f$ with $g$, or the result of \emph{substituting}
$g$ for $x$ in $f$.

Equivalently, the $n$-th coefficient of $f[g]$ is the finite sum
\[
[x^n](f[g]) = \sum_{d=0}^{n} f_d \cdot [x^n](g^d).
\]
\end{definition}
```

:::lemma_ "lem.fps.subs.eq-subst" (parent := "substitution_definition") (lean := "AlgebraicCombinatorics.fps_comp_eq_subst")
The composition $`f[g]` defined above equals the standard substitution
operation on formal power series.
:::

```tex "lem.fps.subs.eq-subst" (slot := statement)
\begin{lemma}
\label{lem.fps.subs.eq-subst}
\lean{AlgebraicCombinatorics.fps_comp_eq_subst}
\leanhelper
\leanok
The composition $f[g]$ defined above equals the standard
substitution operation on formal power series.
\end{lemma}
```

:::proof "lem.fps.subs.eq-subst"
By definition.
:::

```tex "lem.fps.subs.eq-subst" (slot := proof)
\begin{proof}
\leanok
By definition.
\end{proof}
```

:::group "substitution_well_definedness"
Why the substitution series is well-defined.
:::

```tex
\subsection{Well-definedness of substitution}
```

:::theorem "prop.fps.subs.wd" (parent := "substitution_well_definedness") (lean := "AlgebraicCombinatorics.fps_subs_wd_firstCoeffs, AlgebraicCombinatorics.fps_subs_wd_summable, AlgebraicCombinatorics.fps_subs_wd_constCoeff")
Let $`f` and $`g` be two FPSs in $`K[[x]]`. Assume that
$`\left[x^0\right]g = 0`. Write $`f` in the form
$`f = \sum_{n\in\mathbb{N}} f_n x^n`. Then:

*(a)* For each $`n\in\mathbb{N}`, the first $`n` coefficients of the FPS
$`g^n` are $`0`.

*(b)* The sum $`\sum_{n\in\mathbb{N}} f_n g^n` is well-defined; that is, the
family $`(f_n g^n)_{n\in\mathbb{N}}` is summable.

*(c)* We have
$`\left[x^0\right]\left(\sum_{n\in\mathbb{N}} f_n g^n\right) = f_0`.
:::

```tex "prop.fps.subs.wd" (slot := statement)
\begin{proposition}
\label{prop.fps.subs.wd}
\lean{AlgebraicCombinatorics.fps_subs_wd_firstCoeffs, AlgebraicCombinatorics.fps_subs_wd_summable, AlgebraicCombinatorics.fps_subs_wd_constCoeff}
\leantarget
\leanok
Let $f$ and $g$ be two FPSs in $K[[x]]$. Assume that $[x^0]g = 0$.
Write $f$ in the form $f = \sum_{n \in \mathbb{N}} f_n x^n$ with
$f_0, f_1, f_2, \ldots \in K$. Then:

\textbf{(a)} For each $n \in \mathbb{N}$, the first $n$ coefficients of the
FPS $g^n$ are $0$.

\textbf{(b)} The sum $\sum_{n \in \mathbb{N}} f_n g^n$ is well-defined, i.e.,
the family $(f_n g^n)_{n \in \mathbb{N}}$ is summable.

\textbf{(c)} We have $[x^0](\sum_{n \in \mathbb{N}} f_n g^n) = f_0$.
\end{proposition}
```

:::proof "prop.fps.subs.wd"
*(a)* Since $`\left[x^0\right]g = 0`, the lemma $`g=xh` yields an FPS $`h`
with $`g = xh`. Hence $`g^n = x^n h^n`, and the lemma on the first
coefficients of $`x^n a` shows that the first $`n` coefficients of $`g^n`
vanish.

*(b)* By part *(a)*, whenever $`i>n`, the coefficient
$`\left[x^n\right](g^i)=0`. Therefore
$`\left[x^n\right](f_i g^i)=f_i\cdot 0 = 0` for all sufficiently large $`i`,
so the family $`(f_i g^i)` is summable.

*(c)* For each positive integer $`n`, part *(a)* gives
$`\left[x^0\right](g^n)=0`, hence
$`\left[x^0\right](f_n g^n)=0`. Therefore the constant coefficient of
$`\sum_{n\in\mathbb{N}} f_n g^n` comes only from the term $`f_0 g^0 = f_0`.
:::

```tex "prop.fps.subs.wd" (slot := proof)
\begin{proof}
\textbf{(a)} The FPS $g$ has constant term $[x^0]g = 0$. Hence, by
Lemma~\ref{lem.fps.g=xh} (applied to $a = g$), there exists an
$h \in K[[x]]$ such that $g = xh$. Now, let $n \in \mathbb{N}$. From
$g = xh$, we obtain $g^n = (xh)^n = x^n h^n$. However,
Lemma~\ref{lem.fps.first-n-coeffs-of-xna} (applied to $k = n$ and
$a = h^n$) yields that the first $n$ coefficients of $x^n h^n$ are $0$.
In other words, the first $n$ coefficients of $g^n$ are $0$.

\textbf{(b)} This follows from part \textbf{(a)}. We must prove that for each
$n \in \mathbb{N}$, all but finitely many $i \in \mathbb{N}$ satisfy
$[x^n](f_i g^i) = 0$. Fix $n \in \mathbb{N}$. Let $i \in \mathbb{N}$
satisfy $i > n$. Then $n < i$, and by part \textbf{(a)} (applied to $i$
instead of $n$), the first $i$ coefficients of $g^i$ are $0$. Since $n < i$,
the coefficient $[x^n](g^i) = 0$. Thus $[x^n](f_i g^i) = f_i \cdot 0 = 0$.

\textbf{(c)} Let $n$ be a positive integer. By part \textbf{(a)}, the first
$n$ coefficients of $g^n$ are $0$, so $[x^0](g^n) = 0$ and thus
$[x^0](f_n g^n) = 0$. Therefore,
\[
[x^0]\left(\sum_{n \in \mathbb{N}} f_n g^n\right)
= [x^0](f_0 \underbrace{g^0}_{= 1}) + \sum_{n > 0} \underbrace{[x^0](f_n g^n)}_{= 0}
= f_0.
\]
\end{proof}
```

:::lemma_ "lem.fps.subs.zero" (parent := "substitution_well_definedness") (lean := "AlgebraicCombinatorics.subst_zero")
Let $`g\in K[[x]]` with $`\left[x^0\right]g = 0`. Then $`0[g] = 0`.
:::

```tex "lem.fps.subs.zero" (slot := statement)
\begin{lemma}
\label{lem.fps.subs.zero}
\lean{AlgebraicCombinatorics.subst_zero}
\leanhelper
\leanok
Let $g \in K[[x]]$ with $[x^0]g = 0$. Then $0[g] = 0$.
\end{lemma}
```

:::proof "lem.fps.subs.zero"
Immediate from the definitions:
$`0[g] = \sum_{n\in\mathbb{N}} 0\cdot g^n = 0`.
:::

```tex "lem.fps.subs.zero" (slot := proof)
\begin{proof}
\leanok
Immediate from the definitions: $0[g] = \sum_{n \in \mathbb{N}} 0 \cdot g^n = 0$.
\end{proof}
```

:::lemma_ "lem.fps.subs.one" (parent := "substitution_well_definedness") (lean := "AlgebraicCombinatorics.subst_one")
Let $`g\in K[[x]]` with $`\left[x^0\right]g = 0`. Then
$`\underline{1}[g] = \underline{1}`.
:::

```tex "lem.fps.subs.one" (slot := statement)
\begin{lemma}
\label{lem.fps.subs.one}
\lean{AlgebraicCombinatorics.subst_one}
\leanhelper
\leanok
Let $g \in K[[x]]$ with $[x^0]g = 0$. Then $\underline{1}[g] = \underline{1}$.
\end{lemma}
```

:::proof "lem.fps.subs.one"
Immediate from the definitions:
$`\underline{1}[g] = 1\cdot g^0 + \sum_{n>0} 0\cdot g^n = 1`.
:::

```tex "lem.fps.subs.one" (slot := proof)
\begin{proof}
\leanok
Immediate from the definitions: $\underline{1}[g] = 1 \cdot g^0 + \sum_{n > 0} 0 \cdot g^n = 1$.
\end{proof}
```
