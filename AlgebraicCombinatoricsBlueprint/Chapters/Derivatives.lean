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
