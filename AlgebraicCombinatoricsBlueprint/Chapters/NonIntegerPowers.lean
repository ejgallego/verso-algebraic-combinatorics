import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.NonIntegerPowers

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Non-Integer Powers" =>

:::group "non_integer_powers_definition"
Power series with constant term one, and the first logarithmic constructions on
them.
:::

```tex
\section{Non-integer powers}

\subsection{Definition}
```

:::definition "def.fps.HasConstantTermOne" (parent := "non_integer_powers_definition") (lean := "AlgebraicCombinatorics.FPS.HasConstantTermOne")
An FPS $`f\in K[[x]]` has _constant term one_ if $`\left[x^0\right]f=1`.
We write $`f\in K[[x]]_1` for this condition.
:::

```tex "def.fps.HasConstantTermOne" (slot := statement)
\begin{definition}
\label{def.fps.HasConstantTermOne}
\lean{AlgebraicCombinatorics.FPS.HasConstantTermOne}
\leanhelper
\leanok
An FPS $f\in K[[x]]$ has \emph{constant term one} if $[x^0]f=1$.
We write $f\in K[[x]]_1$ for this condition.
\end{definition}
```

:::lemma_ "lem.fps.hasConstantTermOne-mul" (parent := "non_integer_powers_definition") (lean := "AlgebraicCombinatorics.FPS.hasConstantTermOne_mul")
If $`f,g\in K[[x]]_1`, then $`fg\in K[[x]]_1`.
:::

```tex "lem.fps.hasConstantTermOne-mul" (slot := statement)
\begin{lemma}
\label{lem.fps.hasConstantTermOne-mul}
\lean{AlgebraicCombinatorics.FPS.hasConstantTermOne_mul}
\leanhelper
\leanok
If $f,g\in K[[x]]_1$, then $fg\in K[[x]]_1$.
\end{lemma}
```

:::proof "lem.fps.hasConstantTermOne-mul"
$`\left[x^0\right](fg)=\left(\left[x^0\right]f\right)\left(\left[x^0\right]g\right)=1\cdot1=1`.
:::

```tex "lem.fps.hasConstantTermOne-mul" (slot := proof)
\begin{proof}
\leanok
$[x^0](fg) = ([x^0]f)([x^0]g) = 1\cdot 1 = 1$.
\end{proof}
```

:::lemma_ "lem.fps.hasConstantTermOne-one-add-X" (parent := "non_integer_powers_definition") (lean := "AlgebraicCombinatorics.FPS.hasConstantTermOne_one_add_X")
$`1+x\in K[[x]]_1`.
:::

```tex "lem.fps.hasConstantTermOne-one-add-X" (slot := statement)
\begin{lemma}
\label{lem.fps.hasConstantTermOne-one-add-X}
\lean{AlgebraicCombinatorics.FPS.hasConstantTermOne_one_add_X}
\leanhelper
\leanok
$1+x\in K[[x]]_1$.
\end{lemma}
```

:::proof "lem.fps.hasConstantTermOne-one-add-X"
$`\left[x^0\right](1+x)=1`.
:::

```tex "lem.fps.hasConstantTermOne-one-add-X" (slot := proof)
\begin{proof}
\leanok
$[x^0](1+x) = 1$.
\end{proof}
```

:::group "non_integer_powers_log_map"
The logarithm map on series with constant term one.
:::

```tex
\subsubsection{The Log map}
```

:::definition "def.fps.logSeries" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.logSeries")
The _logarithm series_, or $`\overline{\log}`, is the FPS
$$`\overline{\log} := \sum_{n\geq 1} \frac{(-1)^{n-1}}{n} x^n
= x - \frac{x^2}{2} + \frac{x^3}{3} - \cdots
\in K[[x]].`
Its constant term is $`0`.
:::

```tex "def.fps.logSeries" (slot := statement)
\begin{definition}
\label{def.fps.logSeries}
\lean{AlgebraicCombinatorics.FPS.logSeries}
\leanhelper
\leanok
The \emph{logarithm series} (or $\overline{\log}$) is the FPS
\[
\overline{\log} := \sum_{n\geq 1} \frac{(-1)^{n-1}}{n} x^n
= x - \frac{x^2}{2} + \frac{x^3}{3} - \cdots
\in K[[x]].
\]
Its constant term is~$0$.
\end{definition}
```

:::lemma_ "lem.fps.constantCoeff-logSeries" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.constantCoeff_logSeries")
$`\left[x^0\right]\overline{\log}=0`.
:::

```tex "lem.fps.constantCoeff-logSeries" (slot := statement)
\begin{lemma}
\label{lem.fps.constantCoeff-logSeries}
\lean{AlgebraicCombinatorics.FPS.constantCoeff_logSeries}
\leanhelper
\leanok
$[x^0]\overline{\log} = 0$.
\end{lemma}
```

:::proof "lem.fps.constantCoeff-logSeries"
Immediate from the definition.
:::

```tex "lem.fps.constantCoeff-logSeries" (slot := proof)
\begin{proof}
\leanok
Immediate from the definition.
\end{proof}
```

:::definition "def.fps.fpsLog" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.fpsLog")
For $`f\in K[[x]]_1`, define
$$`\operatorname{Log}(f) := \overline{\log}\circ (f-1).`
Since $`f` has constant term $`1`, the FPS $`f-1` has constant term $`0`, so
this substitution is well-defined.
:::

```tex "def.fps.fpsLog" (slot := statement)
\begin{definition}
\label{def.fps.fpsLog}
\lean{AlgebraicCombinatorics.FPS.fpsLog}
\leanhelper
\leanok
For $f\in K[[x]]_1$, we define
\[
\operatorname{Log}(f) := \overline{\log} \circ (f-1).
\]
Since $f$ has constant term~$1$, the FPS $f-1$ has constant term~$0$,
so the substitution is well-defined.
\end{definition}
```

:::lemma_ "lem.fps.fpsLog-one" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.fpsLog_one")
$`\operatorname{Log}(1)=0`.
:::

```tex "lem.fps.fpsLog-one" (slot := statement)
\begin{lemma}
\label{lem.fps.fpsLog-one}
\lean{AlgebraicCombinatorics.FPS.fpsLog_one}
\leanhelper
\leanok
$\operatorname{Log}(1) = 0$.
\end{lemma}
```

:::proof "lem.fps.fpsLog-one"
$`\operatorname{Log}(1)=\overline{\log}\circ(1-1)=\overline{\log}\circ 0=0`,
since every term in the substitution sum is zero.
:::

```tex "lem.fps.fpsLog-one" (slot := proof)
\begin{proof}
\leanok
$\operatorname{Log}(1) = \overline{\log}\circ (1-1) = \overline{\log}\circ 0 = 0$,
since every term in the substitution sum is zero.
\end{proof}
```

:::lemma_ "lem.fps.constantCoeff-fpsLog" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.constantCoeff_fpsLog")
For $`f\in K[[x]]_1`, we have
$`\left[x^0\right]\operatorname{Log}(f)=0`.
:::

```tex "lem.fps.constantCoeff-fpsLog" (slot := statement)
\begin{lemma}
\label{lem.fps.constantCoeff-fpsLog}
\lean{AlgebraicCombinatorics.FPS.constantCoeff_fpsLog}
\leanhelper
\leanok
For $f\in K[[x]]_1$, we have $[x^0]\operatorname{Log}(f)=0$.
\end{lemma}
```

:::proof "lem.fps.constantCoeff-fpsLog"
The constant term of a substitution $`g\circ h` where both
$`\left[x^0\right]g=0` and $`\left[x^0\right]h=0` is again $`0`.
:::

```tex "lem.fps.constantCoeff-fpsLog" (slot := proof)
\begin{proof}
\leanok
The constant term of a substitution $g\circ h$ where both $[x^0]g=0$ and $[x^0]h=0$
is~$0$.
\end{proof}
```

:::theorem "thm.fps.fpsLog-mul" (parent := "non_integer_powers_log_map") (lean := "AlgebraicCombinatorics.FPS.fpsLog_mul")
For $`f,g\in K[[x]]_1`,
$$`\operatorname{Log}(fg)=\operatorname{Log}(f)+\operatorname{Log}(g).`
:::

```tex "thm.fps.fpsLog-mul" (slot := statement)
\begin{theorem}
\label{thm.fps.fpsLog-mul}
\lean{AlgebraicCombinatorics.FPS.fpsLog_mul}
\leanhelper
\leanok
For $f,g\in K[[x]]_1$,
\[
\operatorname{Log}(fg) = \operatorname{Log}(f) + \operatorname{Log}(g).
\]
\end{theorem}
```

:::proof "thm.fps.fpsLog-mul"
Let
$`h=\operatorname{Log}(fg)-\operatorname{Log}(f)-\operatorname{Log}(g)`.
Using the derivative characterization
$`\left(\dfrac{d}{dx}\right)\operatorname{Log}(f)=\left(\dfrac{d}{dx}\overline{\log}\right)\circ(f-1)\cdot f'`
together with the key identity
$`\left(\dfrac{d}{dx}\overline{\log}\right)\circ(f-1)\cdot f=1`, the Leibniz
rule for $`(fg)'` shows that $`h'=0`.
Also
$`\left[x^0\right]h=0-0-0=0`.
By uniqueness from constant term and derivative, $`h=0`, which is exactly the
claim.
:::

```tex "thm.fps.fpsLog-mul" (slot := proof)
\begin{proof}
\leanok
Let $h = \operatorname{Log}(fg) - \operatorname{Log}(f) - \operatorname{Log}(g)$.
We show $h'=0$ and $[x^0]h = 0$ using the derivative characterization:
$(d/dx)\operatorname{Log}(f) = (d/dx \overline{\log})\circ(f-1)\cdot f'$,
and the key identity $(d/dx\,\overline{\log})\circ(f-1)\cdot f = 1$
(since $d/dx\,\overline{\log} = 1/(1+x)$ and substituting $f-1$ gives $1/f$).
The Leibniz rule for $(fg)'$ then shows $h'=0$.
Since $[x^0]h = 0-0-0 = 0$ and $h'=0$, uniqueness gives $h=0$.
\end{proof}
```
