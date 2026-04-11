import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.Derivatives

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Derivatives of FPSs" =>

Our definition of the derivative of an FPS copycats the familiar derivative
formula for power series in analysis.

```tex
\section{Derivatives of FPSs}

Our definition of the derivative of a FPS copycats the well-known formula for
the derivative of a power series in analysis:
```

:::group "derivatives_definition"
The definition of the derivative and its first basic examples.
:::

:::definition "def.fps.deriv" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.coeff_derivative_eq")
Let $`f\in K\left[\left[x\right]\right]` be an FPS. Then the _derivative_
$`f'` of $`f` is the FPS defined as follows: write
$`f=\sum_{n\in\mathbb{N}} f_n x^n` with coefficients in $`K`, and set
$$`f' := \sum_{n>0} n f_n x^{n-1}.`
:::

```tex "def.fps.deriv" (slot := statement)
\begin{definition}
\label{def.fps.deriv}
\lean{AlgebraicCombinatorics.FPS.coeff_derivative_eq}
\leantarget
\leanok
Let $f\in K\left[  \left[  x\right]  \right]  $ be an
FPS. Then, the \emph{derivative} $f^{\prime}$ of $f$ is an FPS defined as
follows: Write $f$ as $f=\sum_{n\in\mathbb{N}}f_{n}x^{n}$ (with $f_{0}%
,f_{1},f_{2},\ldots\in K$), and set%
\[
f^{\prime}:=\sum_{n>0}nf_{n}x^{n-1}.
\]
\end{definition}
```

:::lemma_ "lem.fps.deriv.mk" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_eq_mk")
Let $`f\in K\left[\left[x\right]\right]` be an FPS. Then $`f'` is the power
series with coefficient function
$`n \mapsto (n+1)\cdot f_{n+1}`.
:::

```tex "lem.fps.deriv.mk" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.mk}
\lean{AlgebraicCombinatorics.FPS.derivative_eq_mk}
\leanhelper
\leanok
Let $f\in K\left[  \left[  x\right]  \right]  $ be an FPS.
Then $f^{\prime}$ is the power series with coefficient function
$n \mapsto (n+1) \cdot f_{n+1}$.
\end{lemma}
```

:::proof "lem.fps.deriv.mk"
Immediate from the definition by reindexing $`n \mapsto n+1`.
:::

```tex "lem.fps.deriv.mk" (slot := proof)
\begin{proof}
\leanok
Immediate from the definition by reindexing $n \mapsto n+1$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.eq-derivativeFun" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_eq_derivativeFun")
The derivative operation $`f \mapsto f'` agrees with the standard derivative
operation on formal power series.
:::

```tex "lem.fps.deriv.eq-derivativeFun" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.eq-derivativeFun}
\lean{AlgebraicCombinatorics.FPS.derivative_eq_derivativeFun}
\leanhelper
\leanok
The derivative operation $f \mapsto f^{\prime}$ agrees with
the standard derivative operation on formal power series.
\end{lemma}
```

:::proof "lem.fps.deriv.eq-derivativeFun"
By definition.
:::

```tex "lem.fps.deriv.eq-derivativeFun" (slot := proof)
\begin{proof}
\leanok
By definition.
\end{proof}
```

:::lemma_ "lem.fps.deriv.coeff-formula" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_coeff_formula")
Let $`f\in K\left[\left[x\right]\right]` be an FPS. Then for each
$`n\in\mathbb{N}`, the $`n`-th coefficient of $`f'` is
$`(n+1)\cdot f_{n+1}`.
:::

```tex "lem.fps.deriv.coeff-formula" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.coeff-formula}
\lean{AlgebraicCombinatorics.FPS.derivative_coeff_formula}
\leanhelper
\leanok
Let $f\in K\left[  \left[  x\right]  \right]  $ be an FPS.
Then for each $n\in\mathbb{N}$, the $n$-th coefficient of $f^{\prime}$
is $(n+1) \cdot f_{n+1}$.
\end{lemma}
```

:::proof "lem.fps.deriv.coeff-formula"
Follows directly from the definition of the derivative.
:::

```tex "lem.fps.deriv.coeff-formula" (slot := proof)
\begin{proof}
\leanok
Follows directly from the definition of the derivative.
\end{proof}
```

:::lemma_ "lem.fps.deriv.zero" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_zero")
We have $`0' = 0`.
:::

```tex "lem.fps.deriv.zero" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.zero}
\lean{AlgebraicCombinatorics.FPS.derivative_zero}
\leanhelper
\leanok
We have $0^{\prime} = 0$.
\end{lemma}
```

:::proof "lem.fps.deriv.zero"
All coefficients of $`0` are $`0`, so the derivative is $`0`.
:::

```tex "lem.fps.deriv.zero" (slot := proof)
\begin{proof}
\leanok
All coefficients of $0$ are $0$, so the derivative is $0$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.one" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_one")
We have $`1' = 0`.
:::

```tex "lem.fps.deriv.one" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.one}
\lean{AlgebraicCombinatorics.FPS.derivative_one}
\leanhelper
\leanok
We have $1^{\prime} = 0$.
\end{lemma}
```

:::proof "lem.fps.deriv.one"
$`1` is constant, so $`1' = 0`.
:::

```tex "lem.fps.deriv.one" (slot := proof)
\begin{proof}
\leanok
$1$ is constant, so $1^{\prime} = 0$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.C" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_C")
For any $`c\in K`, we have $`(c)' = 0`, where $`c` is viewed as a constant
FPS.
:::

```tex "lem.fps.deriv.C" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.C}
\lean{AlgebraicCombinatorics.FPS.derivative_C}
\leanhelper
\leanok
For any $c\in K$, we have $(c)^{\prime} = 0$
(where $c$ is viewed as a constant FPS).
\end{lemma}
```

:::proof "lem.fps.deriv.C"
All coefficients of $`c` beyond the constant term are $`0`, so the derivative
is $`0`.
:::

```tex "lem.fps.deriv.C" (slot := proof)
\begin{proof}
\leanok
All coefficients of $c$ beyond the constant term are $0$, so the derivative is $0$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.X" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_X")
We have $`x' = 1`.
:::

```tex "lem.fps.deriv.X" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.X}
\lean{AlgebraicCombinatorics.FPS.derivative_X}
\leanhelper
\leanok
We have $x^{\prime} = 1$.
\end{lemma}
```

:::proof "lem.fps.deriv.X"
The $`0`-th coefficient of $`x'` is
$`(0+1)\cdot \left[x^1\right]x = 1`, and all higher coefficients are $`0`.
:::

```tex "lem.fps.deriv.X" (slot := proof)
\begin{proof}
\leanok
The $0$-th coefficient of $x^{\prime}$ is $(0+1) \cdot [x^1]x = 1$, and
all higher coefficients are $0$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.X-pow-succ" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_X_pow_succ")
For any $`n\in\mathbb{N}`, we have
$`\left(x^{n+1}\right)' = (n+1)\cdot x^n`.
:::

```tex "lem.fps.deriv.X-pow-succ" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.X-pow-succ}
\lean{AlgebraicCombinatorics.FPS.derivative_X_pow_succ}
\leanhelper
\leanok
For any $n\in\mathbb{N}$, we have
$\left(x^{n+1}\right)^{\prime} = (n+1) \cdot x^{n}$.
\end{lemma}
```

:::proof "lem.fps.deriv.X-pow-succ"
Direct coefficient comparison:
$`\left[x^m\right](x^{n+1})' = (m+1)\cdot \left[x^{m+1}\right](x^{n+1})`.
This is $`n+1` when $`m=n` and $`0` otherwise.
:::

```tex "lem.fps.deriv.X-pow-succ" (slot := proof)
\begin{proof}
\leanok
Direct coefficient comparison: $[x^m](x^{n+1})^{\prime} = (m+1) \cdot [x^{m+1}](x^{n+1})$.
This is $(n+1)$ if $m = n$ and $0$ otherwise.
\end{proof}
```

:::lemma_ "lem.fps.deriv.X-pow-pos" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_X_pow_of_pos")
For any $`n\in\mathbb{N}` with $`n>0`, we have
$`\left(x^n\right)' = n\cdot x^{n-1}`.
:::

```tex "lem.fps.deriv.X-pow-pos" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.X-pow-pos}
\lean{AlgebraicCombinatorics.FPS.derivative_X_pow_of_pos}
\leanhelper
\leanok
For any $n\in\mathbb{N}$ with $n > 0$, we have
$\left(x^{n}\right)^{\prime} = n \cdot x^{n-1}$.
\end{lemma}
```

:::proof "lem.fps.deriv.X-pow-pos"
Write $`n = m+1` and apply the previous lemma.
:::

```tex "lem.fps.deriv.X-pow-pos" (slot := proof)
\begin{proof}
\leanok
Write $n = m + 1$ and apply Lemma~\ref{lem.fps.deriv.X-pow-succ}.
\end{proof}
```

:::lemma_ "lem.fps.deriv.coe-polynomial" (parent := "derivatives_definition") (lean := "AlgebraicCombinatorics.FPS.derivative_coe_polynomial")
Let $`p` be a polynomial. Then the derivative of $`p` viewed as a power series
equals the polynomial derivative of $`p` viewed as a power series.
:::

```tex "lem.fps.deriv.coe-polynomial" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.coe-polynomial}
\lean{AlgebraicCombinatorics.FPS.derivative_coe_polynomial}
\leanhelper
\leanok
Let $p$ be a polynomial. Then the derivative of $p$ viewed as a power series
equals the polynomial derivative of $p$ viewed as a power series.
\end{lemma}
```

:::proof "lem.fps.deriv.coe-polynomial"
Both derivatives are defined by the same coefficient formula.
:::

```tex "lem.fps.deriv.coe-polynomial" (slot := proof)
\begin{proof}
\leanok
Both derivatives are defined by the same coefficient formula.
\end{proof}
```

:::group "derivative_rules"
The standard algebraic rules for differentiating formal power series.
:::

```tex
\subsection{Derivative rules}
```

:::theorem "thm.fps.deriv.rules" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_add, AlgebraicCombinatorics.FPS.derivative_sum, AlgebraicCombinatorics.FPS.derivative_summableFPSSum, AlgebraicCombinatorics.FPS.derivative_smul, AlgebraicCombinatorics.FPS.derivative_mul, AlgebraicCombinatorics.FPS.derivative_div, AlgebraicCombinatorics.FPS.derivative_pow', AlgebraicCombinatorics.FPS.derivative_comp, AlgebraicCombinatorics.FPS.derivative_eq_imp_diff_const")
The derivative satisfies the expected rules:

*(a)* $`\left(f+g\right)' = f' + g'` for any FPSs $`f,g`.

*(b)* If $`(f_i)_{i\in I}` is a summable family of FPSs, then
$`(f_i')_{i\in I}` is summable as well, and
$`\left(\sum_{i\in I} f_i\right)' = \sum_{i\in I} f_i'`.

*(c)* $`\left(cf\right)' = cf'` for any $`c\in K` and FPS $`f`.

*(d)* $`\left(fg\right)' = f'g + fg'` for any FPSs $`f,g`. This is the
Leibniz rule.

*(e)* If $`g` is invertible, then
$`\left(\dfrac{f}{g}\right)' = \dfrac{f'g-fg'}{g^2}`. This is the quotient
rule.

*(f)* $`\left(g^n\right)' = ng'g^{n-1}` for any FPS $`g` and any
$`n\in\mathbb{N}`; for $`n=0`, the right-hand side is understood as $`0`.

*(g)* We have
$`\left(f\circ g\right)' = \left(f'\circ g\right)\cdot g'` if $`f` is a
polynomial or if $`\left[x^0\right]g=0`. This is the chain rule.

*(h)* If $`K` is a $`\mathbb{Q}`-algebra and two FPSs $`f,g` satisfy
$`f' = g'`, then $`f-g` is constant.
:::

```tex "thm.fps.deriv.rules" (slot := statement)
\begin{theorem}
\label{thm.fps.deriv.rules}
\lean{AlgebraicCombinatorics.FPS.derivative_add, AlgebraicCombinatorics.FPS.derivative_sum, AlgebraicCombinatorics.FPS.derivative_summableFPSSum, AlgebraicCombinatorics.FPS.derivative_smul, AlgebraicCombinatorics.FPS.derivative_mul, AlgebraicCombinatorics.FPS.derivative_div, AlgebraicCombinatorics.FPS.derivative_pow', AlgebraicCombinatorics.FPS.derivative_comp, AlgebraicCombinatorics.FPS.derivative_eq_imp_diff_const}
\leantarget
\leanok

\textbf{(a)} We have $\left(  f+g\right)  ^{\prime
}=f^{\prime}+g^{\prime}$ for any $f,g\in K\left[  \left[  x\right]  \right]
$. \medskip

\textbf{(b)} If $\left(  f_{i}\right)  _{i\in I}$ is a summable family of
FPSs, then the family $\left(  f_{i}^{\prime}\right)  _{i\in I}$ is summable
as well, and we have%
\[
\left(  \sum_{i\in I}f_{i}\right)  ^{\prime}=\sum_{i\in I}f_{i}^{\prime}.
\]


\textbf{(c)} We have $\left(  cf\right)  ^{\prime}=cf^{\prime}$ for any $c\in
K$ and $f\in K\left[  \left[  x\right]  \right]  $. \medskip

\textbf{(d)} We have $\left(  fg\right)  ^{\prime}=f^{\prime}g+fg^{\prime}$
for any $f,g\in K\left[  \left[  x\right]  \right]  $. (This is known as the
\emph{Leibniz rule}.) \medskip

\textbf{(e)} If $f,g\in K\left[  \left[  x\right]  \right]  $ are two FPSs
such that $g$ is invertible, then%
\[
\left(  \dfrac{f}{g}\right)  ^{\prime}=\dfrac{f^{\prime}g-fg^{\prime}}{g^{2}%
}.
\]
(This is known as the \emph{quotient rule}.) \medskip

\textbf{(f)} If $g\in K\left[  \left[  x\right]  \right]  $ is an FPS, then
$\left(  g^{n}\right)  ^{\prime}=ng^{\prime}g^{n-1}$ for any $n\in\mathbb{N}$
(where the expression $ng^{\prime}g^{n-1}$ is to be understood as $0$ if
$n=0$). \medskip

\textbf{(g)} Given two FPSs $f,g\in K\left[  \left[  x\right]  \right]  $, we
have
\[
\left(  f\circ g\right)  ^{\prime}=\left(  f^{\prime}\circ g\right)  \cdot
g^{\prime}%
\]
if $f$ is a polynomial or if $\left[  x^{0}\right]  g=0$. (This is known as
the \emph{chain rule}.) \medskip

\textbf{(h)} If $K$ is a $\mathbb{Q}$-algebra, and if two FPSs $f,g\in
K\left[  \left[  x\right]  \right]  $ satisfy $f^{\prime}=g^{\prime}$, then
$f-g$ is constant.
\end{theorem}
```

:::proof "thm.fps.deriv.rules"
This combines parts *(a)* through *(h)*, proved individually below.
:::

```tex "thm.fps.deriv.rules" (slot := proof)
\begin{proof}
This combines parts \textbf{(a)} through \textbf{(h)}, proved individually below.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.a" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_add")
We have $`\left(f+g\right)' = f' + g'` for any FPSs $`f,g`.
:::

```tex "lem.fps.deriv.rules.a" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(a)}]
\label{lem.fps.deriv.rules.a}
\lean{AlgebraicCombinatorics.FPS.derivative_add}
\leanhelper
\leanok
We have $\left(  f+g\right)  ^{\prime}=f^{\prime}+g^{\prime}$
for any $f,g\in K\left[  \left[  x\right]  \right]$.
\end{lemma}
```

:::proof "lem.fps.deriv.rules.a"
This is part of the cited exercise on differentiating formal power series.
:::

```tex "lem.fps.deriv.rules.a" (slot := proof)
\begin{proof}
\leanok
This is part of \cite[Exercise 5 \textbf{(b)}]{19s-mt3s} (specifically, it is
Statement 1 in \cite[solution to Exercise 5 \textbf{(b)}]{19s-mt3s}).
\end{proof}
```

:::lemma_ "lem.fps.deriv.neg" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_neg")
We have $`(-f)' = -f'` for any FPS $`f`, where $`K` is a commutative ring.
:::

```tex "lem.fps.deriv.neg" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.neg}
\lean{AlgebraicCombinatorics.FPS.derivative_neg}
\leanhelper
\leanok
We have $(-f)^{\prime} = -f^{\prime}$
for any $f\in K\left[  \left[  x\right]  \right]$ (where $K$ is a commutative ring).
\end{lemma}
```

:::proof "lem.fps.deriv.neg"
The derivative is an additive map, so it preserves negation.
:::

```tex "lem.fps.deriv.neg" (slot := proof)
\begin{proof}
\leanok
The derivative is an additive map, so it preserves negation.
\end{proof}
```

:::lemma_ "lem.fps.deriv.sub" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_sub")
We have $`\left(f-g\right)' = f' - g'` for any FPSs $`f,g`, where $`K` is a
commutative ring.
:::

```tex "lem.fps.deriv.sub" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.sub}
\lean{AlgebraicCombinatorics.FPS.derivative_sub}
\leanhelper
\leanok
We have $(f - g)^{\prime} = f^{\prime} - g^{\prime}$
for any $f,g\in K\left[  \left[  x\right]  \right]$ (where $K$ is a commutative ring).
\end{lemma}
```

:::proof "lem.fps.deriv.sub"
The derivative is an additive map, so it preserves subtraction.
:::

```tex "lem.fps.deriv.sub" (slot := proof)
\begin{proof}
\leanok
The derivative is an additive map, so it preserves subtraction.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.b.finite" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_sum")
Let $`I` be a finite index set and $`(f_i)_{i\in I}` a family of FPSs. Then
$`\left(\sum_{i\in I} f_i\right)' = \sum_{i\in I} f_i'`.
:::

```tex "lem.fps.deriv.rules.b.finite" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(b)}, finite version]
\label{lem.fps.deriv.rules.b.finite}
\lean{AlgebraicCombinatorics.FPS.derivative_sum}
\leanhelper
\leanok
Let $I$ be a finite index set and $(f_i)_{i\in I}$ a family of FPSs.
Then
$\left(\sum_{i\in I} f_i\right)^{\prime} = \sum_{i\in I} f_i^{\prime}$.
\end{lemma}
```

:::proof "lem.fps.deriv.rules.b.finite"
Follows from additivity by induction on $`|I|`.
:::

```tex "lem.fps.deriv.rules.b.finite" (slot := proof)
\begin{proof}
\leanok
Follows from additivity (part \textbf{(a)}) by induction on $|I|$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.summable-preserved" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.summableFPS_derivative")
If $`(f_i)_{i\in I}` is a summable family of FPSs, then
$`(f_i')_{i\in I}` is also summable.
:::

```tex "lem.fps.deriv.summable-preserved" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.summable-preserved}
\lean{AlgebraicCombinatorics.FPS.summableFPS_derivative}
\leanhelper
\leanok
If $(f_i)_{i\in I}$ is a summable family of FPSs, then
$(f_i^{\prime})_{i\in I}$ is also summable.
\end{lemma}
```

:::proof "lem.fps.deriv.summable-preserved"
For each coefficient index $`n`, the set of $`i` with
$`\left[x^n\right]f_i' \neq 0` is a subset of the set of $`i` with
$`\left[x^{n+1}\right]f_i \neq 0`, which is finite by summability of
$`(f_i)`.
:::

```tex "lem.fps.deriv.summable-preserved" (slot := proof)
\begin{proof}
\leanok
For each coefficient index $n$, the set of $i$ with $[x^n]f_i^{\prime} \neq 0$
is a subset of the set of $i$ with $[x^{n+1}]f_i \neq 0$, which is finite
by summability of $(f_i)$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.b.infinite" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_summableFPSSum")
If $`(f_i)_{i\in I}` is a summable family of FPSs, then the family
$`(f_i')_{i\in I}` is summable as well, and
$`\left(\sum_{i\in I} f_i\right)' = \sum_{i\in I} f_i'`.
:::

```tex "lem.fps.deriv.rules.b.infinite" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(b)}, infinite version]
\label{lem.fps.deriv.rules.b.infinite}
\lean{AlgebraicCombinatorics.FPS.derivative_summableFPSSum}
\leanhelper
\leanok
If $\left(  f_{i}\right)  _{i\in I}$ is a summable family of
FPSs, then the family $\left(  f_{i}^{\prime}\right)  _{i\in I}$ is summable
as well, and we have%
\[
\left(  \sum_{i\in I}f_{i}\right)  ^{\prime}=\sum_{i\in I}f_{i}^{\prime}.
\]
\end{lemma}
```

:::proof "lem.fps.deriv.rules.b.infinite"
This is the natural generalization of part *(a)* to potentially infinite sums.
For each $`n`,
$`\left[x^n\right]\left(\sum_{i\in I}f_i\right)'`
equals
$`\left(\sum_{i\in I}\left[x^{n+1}\right]f_i\right) \cdot (n+1)`, which is
the same as
$`\sum_{i\in I} \left[x^{n+1}\right]f_i \cdot (n+1)
= \sum_{i\in I} \left[x^n\right] f_i^{\prime}`.
The interchange of summation and multiplication by $`n+1` is justified because
the sum has finite support.
:::

```tex "lem.fps.deriv.rules.b.infinite" (slot := proof)
\begin{proof}
This is the natural generalization of Theorem
\ref{thm.fps.deriv.rules} \textbf{(a)} to (potentially) infinite sums. The
proof works coefficient-by-coefficient: for each $n$,
\begin{align*}
[x^n]\left(\sum_{i\in I}f_i\right)^{\prime}
&= \left(\sum_{i\in I}[x^{n+1}]f_i\right) \cdot (n+1) \\
&= \sum_{i\in I} [x^{n+1}]f_i \cdot (n+1)
= \sum_{i\in I} [x^n] f_i^{\prime},
\end{align*}
where the interchange of summation and multiplication by $(n+1)$ is justified
because the sum has finite support.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.c" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_smul")
We have $`\left(cf\right)' = cf'` for any $`c\in K` and FPS $`f`.
:::

```tex "lem.fps.deriv.rules.c" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(c)}]
\label{lem.fps.deriv.rules.c}
\lean{AlgebraicCombinatorics.FPS.derivative_smul}
\leanhelper
\leanok
We have $\left(  cf\right)  ^{\prime}=cf^{\prime}$ for any $c\in
K$ and $f\in K\left[  \left[  x\right]  \right]  $.
\end{lemma}
```

:::proof "lem.fps.deriv.rules.c"
This is another standard exercise on formal power series differentiation.
:::

```tex "lem.fps.deriv.rules.c" (slot := proof)
\begin{proof}
\leanok
This is part of \cite[Exercise 5 \textbf{(b)}]{19s-mt3s}
(specifically, it is Statement 3 in \cite[solution to Exercise 5 \textbf{(b)}%
]{19s-mt3s}).
\end{proof}
```

:::lemma_ "lem.fps.deriv.C-mul" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_C_mul")
We have $`\left(C(c)\cdot f\right)' = C(c)\cdot f'` for any $`c\in K` and
FPS $`f`, where $`C(c)` denotes the constant power series with value $`c`.
:::

```tex "lem.fps.deriv.C-mul" (slot := statement)
\begin{lemma}
\label{lem.fps.deriv.C-mul}
\lean{AlgebraicCombinatorics.FPS.derivative_C_mul}
\leanhelper
\leanok
We have $(C(c) \cdot f)^{\prime} = C(c) \cdot f^{\prime}$ for any $c\in K$
and $f\in K\left[  \left[  x\right]  \right]$, where $C(c)$ denotes the
constant power series with value $c$.
\end{lemma}
```

:::proof "lem.fps.deriv.C-mul"
This follows from the scalar-multiplication rule, since
$`C(c)\cdot f = c\cdot f` in the power series ring.
:::

```tex "lem.fps.deriv.C-mul" (slot := proof)
\begin{proof}
\leanok
This follows from the scalar multiplication rule (Lemma~\ref{lem.fps.deriv.rules.c}),
since $C(c) \cdot f = c \cdot f$ in the power series ring.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.d" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_mul")
We have $`\left(fg\right)' = f'g + fg'` for any FPSs $`f,g`. This is the
Leibniz rule.
:::

```tex "lem.fps.deriv.rules.d" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(d)}]
\label{lem.fps.deriv.rules.d}
\lean{AlgebraicCombinatorics.FPS.derivative_mul}
\leanhelper
\leanok
We have $\left(  fg\right)  ^{\prime}=f^{\prime}g+fg^{\prime}$
for any $f,g\in K\left[  \left[  x\right]  \right]  $. (This is known as the
\emph{Leibniz rule}.)
\end{lemma}
```

:::proof "lem.fps.deriv.rules.d"
This is Exercise 5 (c) in `19s-mt3s` and Proposition 0.2 (c) in `logexp`.
:::

```tex "lem.fps.deriv.rules.d" (slot := proof)
\begin{proof}
\leanok
This is \cite[Exercise 5 \textbf{(c)}]{19s-mt3s} and
\cite[Proposition 0.2 \textbf{(c)}]{logexp}.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.e" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_div")
If $`f,g\in K\left[\left[x\right]\right]` are two FPSs such that $`g` is
invertible, then
$`\left(\dfrac{f}{g}\right)' = \dfrac{f'g-fg'}{g^2}`. This is the quotient
rule.
:::

```tex "lem.fps.deriv.rules.e" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(e)}]
\label{lem.fps.deriv.rules.e}
\lean{AlgebraicCombinatorics.FPS.derivative_div}
\leanhelper
\leanok
If $f,g\in K\left[  \left[  x\right]  \right]  $ are two FPSs
such that $g$ is invertible, then%
\[
\left(  \dfrac{f}{g}\right)  ^{\prime}=\dfrac{f^{\prime}g-fg^{\prime}}{g^{2}%
}.
\]
(This is known as the \emph{quotient rule}.)
\end{lemma}
```

:::proof "lem.fps.deriv.rules.e"
Apply the product rule to $`\dfrac{f}{g}\cdot g = f`. This gives
$`f' = \left(\dfrac{f}{g}\right)'\cdot g + \dfrac{f}{g}\cdot g'`. Solving for
$`\left(\dfrac{f}{g}\right)'` yields the stated formula.
:::

```tex "lem.fps.deriv.rules.e" (slot := proof)
\begin{proof}
Let $f,g\in K\left[  \left[  x\right]  \right]  $ be two FPSs
such that $g$ is invertible. Then, Theorem \ref{thm.fps.deriv.rules}
\textbf{(d)} (applied to $\dfrac{f}{g}$ instead of $f$) yields $\left(
\dfrac{f}{g}\cdot g\right)  ^{\prime}=\left(  \dfrac{f}{g}\right)  ^{\prime
}\cdot g+\dfrac{f}{g}\cdot g^{\prime}$. In view of $\dfrac{f}{g}\cdot g=f$,
this rewrites as $f^{\prime}=\left(  \dfrac{f}{g}\right)  ^{\prime}\cdot
g+\dfrac{f}{g}\cdot g^{\prime}$. Solving this for $\left(  \dfrac{f}%
{g}\right)  ^{\prime}$, we find $\left(  \dfrac{f}{g}\right)  ^{\prime}%
=\dfrac{f^{\prime}g-fg^{\prime}}{g^{2}}$.
\end{proof}
```

:::lemma_ "lem.fps.deriv.rules.f" (parent := "derivative_rules") (lean := "AlgebraicCombinatorics.FPS.derivative_pow'")
If $`g\in K\left[\left[x\right]\right]` is an FPS, then
$`\left(g^n\right)' = ng'g^{n-1}` for any $`n\in\mathbb{N}`, where the
expression on the right is understood as $`0` if $`n=0`.
:::

```tex "lem.fps.deriv.rules.f" (slot := statement)
\begin{lemma}[Theorem~\ref{thm.fps.deriv.rules} \textbf{(f)}]
\label{lem.fps.deriv.rules.f}
\lean{AlgebraicCombinatorics.FPS.derivative_pow'}
\leanhelper
\leanok
If $g\in K\left[  \left[  x\right]  \right]  $ is an FPS, then
$\left(  g^{n}\right)  ^{\prime}=ng^{\prime}g^{n-1}$ for any $n\in\mathbb{N}$
(where the expression $ng^{\prime}g^{n-1}$ is to be understood as $0$ if
$n=0$).
\end{lemma}
```

:::proof "lem.fps.deriv.rules.f"
Induct on $`n`, using the Leibniz rule in the induction step and the fact that
$`1' = 0` in the base case.
:::

```tex "lem.fps.deriv.rules.f" (slot := proof)
\begin{proof}
\leanok
This follows by induction on $n$, using part \textbf{(d)} (in the
induction step) and $1^{\prime}=0$ (in the induction base).
\end{proof}
```
