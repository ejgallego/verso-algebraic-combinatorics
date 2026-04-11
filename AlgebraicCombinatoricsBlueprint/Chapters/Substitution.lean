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

:::group "substitution_first_coeffs"
A helper lemma controlling the first coefficients after substitution.
:::

```tex
\subsection{Lemma for first $k$ coefficients}
```

:::lemma_ "lem.fps.fg-coeffs-0" (parent := "substitution_first_coeffs") (lean := "AlgebraicCombinatorics.fps_fg_coeffs_zero")
Let $`f,g\in K[[x]]` satisfy $`\left[x^0\right]g = 0`. Let
$`k\in\mathbb{N}` be such that the first $`k` coefficients of $`f` are $`0`.
Then the first $`k` coefficients of $`f\circ g` are $`0`.
:::

```tex "lem.fps.fg-coeffs-0" (slot := statement)
\begin{lemma}
\label{lem.fps.fg-coeffs-0}
\lean{AlgebraicCombinatorics.fps_fg_coeffs_zero}
\leantarget
\leanok
Let $f, g \in K[[x]]$ satisfy $[x^0]g = 0$. Let $k \in \mathbb{N}$ be such
that the first $k$ coefficients of $f$ are $0$. Then, the first $k$
coefficients of $f \circ g$ are $0$.
\end{lemma}
```

:::proof "lem.fps.fg-coeffs-0"
Since $`\left[x^0\right]g = 0`, the lemma $`g=xh` yields an
$`h\in K[[x]]` such that $`g = xh`.

Write $`f = (f_0,f_1,f_2,\ldots)`. The first $`k` coefficients of $`f` are
$`0`, so $`f_n = 0` for each $`n<k`. Hence
$$`f\circ g = \sum_{n\in\mathbb{N}} f_n g^n
= \sum_{\substack{n\in\mathbb{N};\\ n<k}} \underbrace{f_n}_{=0} g^n
+ \sum_{\substack{n\in\mathbb{N};\\ n\ge k}} f_n \underbrace{g^n}_{=x^n h^n}
= \sum_{\substack{n\in\mathbb{N};\\ n\ge k}} f_n x^n h^n.`$$

For any $`m<k`, each term with $`n\ge k` satisfies
$`\left[x^m\right](x^n h^n)=0`, since $`m<k\le n`. Therefore
$`\left[x^m\right](f\circ g)=0` for each $`m<k`.
:::

```tex "lem.fps.fg-coeffs-0" (slot := proof)
\begin{proof}
\leanok
We have $[x^0]g = 0$. Hence, by Lemma~\ref{lem.fps.g=xh} (applied to
$a = g$), there exists an $h \in K[[x]]$ such that $g = xh$.

Write $f = (f_0, f_1, f_2, \ldots)$. The first $k$ coefficients of $f$
are $0$, so $f_n = 0$ for each $n < k$. Now,
\[
f \circ g = \sum_{n \in \mathbb{N}} f_n g^n
= \sum_{\substack{n \in \mathbb{N}; \\ n < k}} \underbrace{f_n}_{= 0} g^n
+ \sum_{\substack{n \in \mathbb{N}; \\ n \geq k}} f_n \underbrace{g^n}_{= x^n h^n}
= \sum_{\substack{n \in \mathbb{N}; \\ n \geq k}} f_n x^n h^n.
\]
For any $m < k$, each term $f_n x^n h^n$ with $n \geq k$ satisfies
$[x^m](x^n h^n) = 0$ (since $m < k \leq n$). Thus $[x^m](f \circ g) = 0$
for each $m < k$.
\end{proof}
```

:::group "substitution_kronecker_delta"
Kronecker delta notation used in the substitution rules.
:::

```tex
\subsection{Kronecker delta notation}
```

:::definition "def.kron-delta" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta")
If $`i` and $`j` are any objects, then $`\delta_{i,j}` means the element
$$`\delta_{i,j} =
\begin{cases}
1, & \text{if } i = j; \\
0, & \text{if } i \neq j
\end{cases}`$$
of $`K`.
:::

```tex "def.kron-delta" (slot := statement)
\begin{definition}
\label{def.kron-delta}
\lean{AlgebraicCombinatorics.kroneckerDelta}
\leantarget
\leanok
If $i$ and $j$ are any objects, then $\delta_{i,j}$ means the element
\[
\delta_{i,j} =
\begin{cases}
1, & \text{if } i = j; \\
0, & \text{if } i \neq j
\end{cases}
\]
of $K$.
\end{definition}
```

:::lemma_ "lem.kron-delta.self" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_self")
$`\delta_{i,i} = 1`.
:::

```tex "lem.kron-delta.self" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.self}
\lean{AlgebraicCombinatorics.kroneckerDelta_self}
\leanhelper
\leanok
$\delta_{i,i} = 1$.
\end{lemma}
```

:::proof "lem.kron-delta.self"
Immediate from the definition.
:::

```tex "lem.kron-delta.self" (slot := proof)
\begin{proof}
\leanok
Immediate from the definition.
\end{proof}
```

:::lemma_ "lem.kron-delta.ne" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_ne")
If $`i\neq j`, then $`\delta_{i,j} = 0`.
:::

```tex "lem.kron-delta.ne" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.ne}
\lean{AlgebraicCombinatorics.kroneckerDelta_ne}
\leanhelper
\leanok
If $i \neq j$, then $\delta_{i,j} = 0$.
\end{lemma}
```

:::proof "lem.kron-delta.ne"
Immediate from the definition.
:::

```tex "lem.kron-delta.ne" (slot := proof)
\begin{proof}
\leanok
Immediate from the definition.
\end{proof}
```

:::lemma_ "lem.kron-delta.comm" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_comm")
$`\delta_{i,j} = \delta_{j,i}`.
:::

```tex "lem.kron-delta.comm" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.comm}
\lean{AlgebraicCombinatorics.kroneckerDelta_comm}
\leanhelper
\leanok
$\delta_{i,j} = \delta_{j,i}$.
\end{lemma}
```

:::proof "lem.kron-delta.comm"
Case split on whether $`i=j`.
:::

```tex "lem.kron-delta.comm" (slot := proof)
\begin{proof}
\leanok
Case split on whether $i = j$.
\end{proof}
```

:::lemma_ "lem.kron-delta.mul-left" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_mul_left")
$$`\delta_{i,j}\cdot a =
\begin{cases}
a, & \text{if } i = j, \\
0, & \text{if } i \neq j
\end{cases}`$$
:::

```tex "lem.kron-delta.mul-left" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.mul-left}
\lean{AlgebraicCombinatorics.kroneckerDelta_mul_left}
\leanhelper
\leanok
$\delta_{i,j} \cdot a = \begin{cases} a & \text{if } i = j, \\ 0 & \text{if } i \neq j. \end{cases}$
\end{lemma}
```

:::proof "lem.kron-delta.mul-left"
Case split on whether $`i=j`.
:::

```tex "lem.kron-delta.mul-left" (slot := proof)
\begin{proof}
\leanok
Case split on whether $i = j$.
\end{proof}
```

:::lemma_ "lem.kron-delta.mul-right" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_mul_right")
$$`a\cdot \delta_{i,j} =
\begin{cases}
a, & \text{if } i = j, \\
0, & \text{if } i \neq j
\end{cases}`$$
:::

```tex "lem.kron-delta.mul-right" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.mul-right}
\lean{AlgebraicCombinatorics.kroneckerDelta_mul_right}
\leanhelper
\leanok
$a \cdot \delta_{i,j} = \begin{cases} a & \text{if } i = j, \\ 0 & \text{if } i \neq j. \end{cases}$
\end{lemma}
```

:::proof "lem.kron-delta.mul-right"
Case split on whether $`i=j`.
:::

```tex "lem.kron-delta.mul-right" (slot := proof)
\begin{proof}
\leanok
Case split on whether $i = j$.
\end{proof}
```

:::lemma_ "lem.kron-delta.sum-left" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.sum_kroneckerDelta_left")
If $`\alpha` is a finite type, then
$`\sum_{i\in\alpha} \delta_{i,j} = 1`.
:::

```tex "lem.kron-delta.sum-left" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.sum-left}
\lean{AlgebraicCombinatorics.sum_kroneckerDelta_left}
\leanhelper
\leanok
If $\alpha$ is a finite type, then $\sum_{i \in \alpha} \delta_{i,j} = 1$.
\end{lemma}
```

:::proof "lem.kron-delta.sum-left"
All terms vanish except $`i=j`, which contributes $`1`.
:::

```tex "lem.kron-delta.sum-left" (slot := proof)
\begin{proof}
\leanok
All terms vanish except $i = j$, which contributes $1$.
\end{proof}
```

:::lemma_ "lem.kron-delta.sum-right" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.sum_kroneckerDelta_right")
If $`\alpha` is a finite type, then
$`\sum_{j\in\alpha} \delta_{i,j} = 1`.
:::

```tex "lem.kron-delta.sum-right" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.sum-right}
\lean{AlgebraicCombinatorics.sum_kroneckerDelta_right}
\leanhelper
\leanok
If $\alpha$ is a finite type, then $\sum_{j \in \alpha} \delta_{i,j} = 1$.
\end{lemma}
```

:::proof "lem.kron-delta.sum-right"
By symmetry, this reduces to the previous lemma.
:::

```tex "lem.kron-delta.sum-right" (slot := proof)
\begin{proof}
\leanok
By symmetry ($\delta_{i,j} = \delta_{j,i}$), this reduces to
Lemma~\ref{lem.kron-delta.sum-left}.
\end{proof}
```

:::lemma_ "lem.kron-delta.contraction" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.sum_kroneckerDelta_mul")
If $`\alpha` is a finite type, then
$`\sum_{i\in\alpha} \delta_{i,j}\cdot f(i) = f(j)`.
:::

```tex "lem.kron-delta.contraction" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.contraction}
\lean{AlgebraicCombinatorics.sum_kroneckerDelta_mul}
\leanhelper
\leanok
If $\alpha$ is a finite type, then
$\sum_{i \in \alpha} \delta_{i,j} \cdot f(i) = f(j)$.
\end{lemma}
```

:::proof "lem.kron-delta.contraction"
By the multiplication property,
$`\delta_{i,j}\cdot f(i)=0` for $`i\neq j` and equals $`f(j)` for $`i=j`.
Thus the sum collapses to the single term $`f(j)`.
:::

```tex "lem.kron-delta.contraction" (slot := proof)
\begin{proof}
\leanok
By the multiplication property, $\delta_{i,j} \cdot f(i) = 0$ for $i \neq j$
and $f(j)$ for $i = j$. The sum collapses to the single term $f(j)$.
\end{proof}
```

:::lemma_ "lem.kron-delta.contraction-right" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.sum_mul_kroneckerDelta")
If $`\alpha` is a finite type, then
$`\sum_{j\in\alpha} f(j)\cdot \delta_{i,j} = f(i)`.
:::

```tex "lem.kron-delta.contraction-right" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.contraction-right}
\lean{AlgebraicCombinatorics.sum_mul_kroneckerDelta}
\leanhelper
\leanok
If $\alpha$ is a finite type, then
$\sum_{j \in \alpha} f(j) \cdot \delta_{i,j} = f(i)$.
\end{lemma}
```

:::proof "lem.kron-delta.contraction-right"
Analogous to the previous lemma.
:::

```tex "lem.kron-delta.contraction-right" (slot := proof)
\begin{proof}
\leanok
Analogous to Lemma~\ref{lem.kron-delta.contraction}.
\end{proof}
```

:::lemma_ "lem.kron-delta.nat-eq" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_nat_eq")
For natural numbers $`n,m\in\mathbb{N}`, we have
$$`\delta_{n,m} =
\begin{cases}
1, & \text{if } n = m, \\
0, & \text{if } n \neq m
\end{cases}`$$
:::

```tex "lem.kron-delta.nat-eq" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.nat-eq}
\lean{AlgebraicCombinatorics.kroneckerDelta_nat_eq}
\leanhelper
\leanok
For natural numbers $n,m\in\mathbb{N}$, we have
$\delta_{n,m} = \begin{cases} 1 & \text{if } n = m, \\ 0 & \text{if } n \neq m. \end{cases}$
\end{lemma}
```

:::proof "lem.kron-delta.nat-eq"
Immediate specialization of the definition to natural numbers.
:::

```tex "lem.kron-delta.nat-eq" (slot := proof)
\begin{proof}
\leanok
This is an immediate specialization of the definition to natural numbers.
\end{proof}
```

:::lemma_ "lem.kron-delta.int-eq" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_int_eq")
For integers $`n,m\in\mathbb{Z}`, we have
$$`\delta_{n,m} =
\begin{cases}
1, & \text{if } n = m, \\
0, & \text{if } n \neq m
\end{cases}`$$
:::

```tex "lem.kron-delta.int-eq" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.int-eq}
\lean{AlgebraicCombinatorics.kroneckerDelta_int_eq}
\leanhelper
\leanok
For integers $n,m\in\mathbb{Z}$, we have
$\delta_{n,m} = \begin{cases} 1 & \text{if } n = m, \\ 0 & \text{if } n \neq m. \end{cases}$
\end{lemma}
```

:::proof "lem.kron-delta.int-eq"
Immediate specialization of the definition to integers.
:::

```tex "lem.kron-delta.int-eq" (slot := proof)
\begin{proof}
\leanok
This is an immediate specialization of the definition to integers.
\end{proof}
```

:::lemma_ "lem.kron-delta.eq-zero-iff" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_eq_zero_iff")
For a nontrivial ring $`K` and any $`i,j`, we have
$`\delta_{i,j} = 0` if and only if $`i\neq j`.
:::

```tex "lem.kron-delta.eq-zero-iff" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.eq-zero-iff}
\lean{AlgebraicCombinatorics.kroneckerDelta_eq_zero_iff}
\leanhelper
\leanok
For a nontrivial ring $K$ and any $i,j$, we have
$\delta_{i,j} = 0$ if and only if $i \neq j$.
\end{lemma}
```

:::proof "lem.kron-delta.eq-zero-iff"
If $`i\neq j`, then $`\delta_{i,j}=0` by definition. Conversely, if
$`i=j`, then $`\delta_{i,j}=1\neq 0` because $`K` is nontrivial.
:::

```tex "lem.kron-delta.eq-zero-iff" (slot := proof)
\begin{proof}
\leanok
If $i \neq j$, then $\delta_{i,j} = 0$ by definition.
Conversely, if $i = j$, then $\delta_{i,j} = 1 \neq 0$ (since $K$ is nontrivial).
\end{proof}
```

:::lemma_ "lem.kron-delta.eq-one-iff" (parent := "substitution_kronecker_delta") (lean := "AlgebraicCombinatorics.kroneckerDelta_eq_one_iff")
For a nontrivial ring $`K` and any $`i,j`, we have
$`\delta_{i,j} = 1` if and only if $`i=j`.
:::

```tex "lem.kron-delta.eq-one-iff" (slot := statement)
\begin{lemma}
\label{lem.kron-delta.eq-one-iff}
\lean{AlgebraicCombinatorics.kroneckerDelta_eq_one_iff}
\leanhelper
\leanok
For a nontrivial ring $K$ and any $i,j$, we have
$\delta_{i,j} = 1$ if and only if $i = j$.
\end{lemma}
```

:::proof "lem.kron-delta.eq-one-iff"
If $`i=j`, then $`\delta_{i,j}=1` by definition. Conversely, if
$`i\neq j`, then $`\delta_{i,j}=0\neq 1` because $`K` is nontrivial.
:::

```tex "lem.kron-delta.eq-one-iff" (slot := proof)
\begin{proof}
\leanok
If $i = j$, then $\delta_{i,j} = 1$ by definition.
Conversely, if $i \neq j$, then $\delta_{i,j} = 0 \neq 1$ (since $K$ is nontrivial).
\end{proof}
```
