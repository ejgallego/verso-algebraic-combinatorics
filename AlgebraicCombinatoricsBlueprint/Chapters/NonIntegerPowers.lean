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

:::group "non_integer_powers_exp_map"
The exponential map on series with constant term zero.
:::

```tex
\subsubsection{The Exp map}
```

:::definition "def.fps.fpsExp" (parent := "non_integer_powers_exp_map") (lean := "AlgebraicCombinatorics.FPS.fpsExp")
For $`g\in K[[x]]_0`, define
$$`\operatorname{Exp}(g) := \exp\circ g
= \left(\sum_{n\in\mathbb{N}} \frac{x^n}{n!}\right)\circ g.`
Since $`g` has constant term $`0`, the substitution is well-defined.
:::

```tex "def.fps.fpsExp" (slot := statement)
\begin{definition}
\label{def.fps.fpsExp}
\lean{AlgebraicCombinatorics.FPS.fpsExp}
\leanhelper
\leanok
For $g\in K[[x]]_0$ (FPS with constant term~$0$), we define
\[
\operatorname{Exp}(g) := \exp\circ\, g
= \left(\sum_{n\in\mathbb{N}} \frac{x^n}{n!}\right)\circ g.
\]
Since $g$ has constant term~$0$, the substitution is well-defined.
\end{definition}
```

:::lemma_ "lem.fps.fpsExp-zero" (parent := "non_integer_powers_exp_map") (lean := "AlgebraicCombinatorics.FPS.fpsExp_zero")
$`\operatorname{Exp}(0)=1`.
:::

```tex "lem.fps.fpsExp-zero" (slot := statement)
\begin{lemma}
\label{lem.fps.fpsExp-zero}
\lean{AlgebraicCombinatorics.FPS.fpsExp_zero}
\leanhelper
\leanok
$\operatorname{Exp}(0)=1$.
\end{lemma}
```

:::proof "lem.fps.fpsExp-zero"
Only the $`m=0` term in the substitution sum is nonzero, so the value is
$`1`.
:::

```tex "lem.fps.fpsExp-zero" (slot := proof)
\begin{proof}
\leanok
Only the $m=0$ term in the substitution sum is nonzero, giving~$1$.
\end{proof}
```

:::lemma_ "lem.fps.hasConstantTermOne-fpsExp" (parent := "non_integer_powers_exp_map") (lean := "AlgebraicCombinatorics.FPS.hasConstantTermOne_fpsExp")
For $`g\in K[[x]]_0`, we have
$`\operatorname{Exp}(g)\in K[[x]]_1`.
:::

```tex "lem.fps.hasConstantTermOne-fpsExp" (slot := statement)
\begin{lemma}
\label{lem.fps.hasConstantTermOne-fpsExp}
\lean{AlgebraicCombinatorics.FPS.hasConstantTermOne_fpsExp}
\leanhelper
\leanok
For $g\in K[[x]]_0$, we have $\operatorname{Exp}(g)\in K[[x]]_1$.
\end{lemma}
```

:::proof "lem.fps.hasConstantTermOne-fpsExp"
The constant term of $`\operatorname{Exp}(g)=\exp\circ g` is
$`\left[x^0\right]\exp = 1/0! = 1`, since all higher powers of $`g`
contribute $`0` to the constant term.
:::

```tex "lem.fps.hasConstantTermOne-fpsExp" (slot := proof)
\begin{proof}
\leanok
The constant term of $\operatorname{Exp}(g) = \exp\circ g$ is $[x^0]\exp = 1/0! = 1$,
since all higher powers of $g$ contribute~$0$ to the constant term.
\end{proof}
```

:::theorem "thm.fps.fpsExp-add" (parent := "non_integer_powers_exp_map") (lean := "AlgebraicCombinatorics.FPS.fpsExp_add")
For $`u,v\in K[[x]]_0`, we have
$$`\operatorname{Exp}(u+v)=\operatorname{Exp}(u)\cdot\operatorname{Exp}(v).`
:::

```tex "thm.fps.fpsExp-add" (slot := statement)
\begin{theorem}
\label{thm.fps.fpsExp-add}
\lean{AlgebraicCombinatorics.FPS.fpsExp_add}
\leanhelper
\leanok
For $u,v\in K[[x]]_0$,
\[
\operatorname{Exp}(u+v) = \operatorname{Exp}(u)\cdot\operatorname{Exp}(v).
\]
\end{theorem}
```

:::proof "thm.fps.fpsExp-add"
This is the multiplicativity of the exponential map for formal power series.
:::

```tex "thm.fps.fpsExp-add" (slot := proof)
\begin{proof}
\leanok
Follows from the multiplicativity of the exponential map, established
in Mathlib's Exp/Log theory for formal power series.
\end{proof}
```

:::group "non_integer_powers_power_definition"
Defining non-integer powers using `Exp` and `Log`.
:::

```tex
\subsubsection{The power definition}
```

:::definition "def.fps.power-c" (parent := "non_integer_powers_power_definition") (lean := "AlgebraicCombinatorics.FPS.fpsPow")
Assume that $`K` is a commutative $`\mathbb{Q}`-algebra.
Let $`f\in K\left[\left[x\right]\right]_1` and $`c\in K`.
Define an FPS
$$`f^c := \operatorname{Exp}\left(c\operatorname{Log}f\right)
\in K\left[\left[x\right]\right]_1.`
:::

```tex "def.fps.power-c" (slot := statement)
\begin{definition}
\label{def.fps.power-c}
\lean{AlgebraicCombinatorics.FPS.fpsPow}
\leantarget
\leanok
Assume that $K$ is a commutative $\mathbb{Q}$-algebra.
Let $f\in K\left[  \left[  x\right]  \right]  _{1}$ and $c\in K$. Then, we
define an FPS%
\[
f^{c}:=\operatorname{Exp}\left(  c\operatorname{Log}f\right)  \in K\left[
\left[  x\right]  \right]  _{1}.
\]
\end{definition}
```

:::lemma_ "lem.fps.fpsPow-zero" (parent := "non_integer_powers_power_definition") (lean := "AlgebraicCombinatorics.FPS.fpsPow_zero")
For any $`f\in K[[x]]`, we have $`f^0 = 1`.
:::

```tex "lem.fps.fpsPow-zero" (slot := statement)
\begin{lemma}
\label{lem.fps.fpsPow-zero}
\lean{AlgebraicCombinatorics.FPS.fpsPow_zero}
\leanhelper
\leanok
For any $f\in K[[x]]$, we have $f^0 = 1$.
\end{lemma}
```

:::proof "lem.fps.fpsPow-zero"
$`f^0=\operatorname{Exp}(0\cdot\operatorname{Log}f)=\operatorname{Exp}(0)=1`.
:::

```tex "lem.fps.fpsPow-zero" (slot := proof)
\begin{proof}
\leanok
$f^0 = \operatorname{Exp}(0\cdot\operatorname{Log}f) = \operatorname{Exp}(0) = 1$.
\end{proof}
```

:::lemma_ "lem.fps.hasConstantTermOne-fpsPow" (parent := "non_integer_powers_power_definition") (lean := "AlgebraicCombinatorics.FPS.hasConstantTermOne_fpsPow")
For $`f\in K[[x]]_1` and $`c\in K`, we have
$`f^c\in K[[x]]_1`.
:::

```tex "lem.fps.hasConstantTermOne-fpsPow" (slot := statement)
\begin{lemma}
\label{lem.fps.hasConstantTermOne-fpsPow}
\lean{AlgebraicCombinatorics.FPS.hasConstantTermOne_fpsPow}
\leanhelper
\leanok
For $f\in K[[x]]_1$ and $c\in K$, we have $f^c\in K[[x]]_1$.
\end{lemma}
```

:::proof "lem.fps.hasConstantTermOne-fpsPow"
Since $`\left[x^0\right]\operatorname{Log}f = 0`, we have
$`\left[x^0\right](c\operatorname{Log}f)=0`, so
$`\operatorname{Exp}(c\operatorname{Log}f)\in K[[x]]_1`.
:::

```tex "lem.fps.hasConstantTermOne-fpsPow" (slot := proof)
\begin{proof}
\leanok
Since $[x^0]\operatorname{Log}f = 0$, we have $[x^0](c\operatorname{Log}f) = 0$,
so $\operatorname{Exp}(c\operatorname{Log}f)\in K[[x]]_1$.
\end{proof}
```

:::lemma_ "lem.fps.fpsPow-one" (parent := "non_integer_powers_power_definition") (lean := "AlgebraicCombinatorics.FPS.fpsPow_one")
For $`f\in K[[x]]_1`, we have $`f^1 = f`.
:::

```tex "lem.fps.fpsPow-one" (slot := statement)
\begin{lemma}
\label{lem.fps.fpsPow-one}
\lean{AlgebraicCombinatorics.FPS.fpsPow_one}
\leanhelper
\leanok
For $f\in K[[x]]_1$, we have $f^1 = f$.
\end{lemma}
```

:::proof "lem.fps.fpsPow-one"
$`f^1=\operatorname{Exp}(1\cdot\operatorname{Log}f)=\operatorname{Exp}(\operatorname{Log}f)=f`,
using that $`\operatorname{Exp}\circ\operatorname{Log}` is the identity on
$`K[[x]]_1`.
:::

```tex "lem.fps.fpsPow-one" (slot := proof)
\begin{proof}
\leanok
$f^1 = \operatorname{Exp}(1\cdot\operatorname{Log}f) = \operatorname{Exp}(\operatorname{Log}f) = f$,
using the inverse property $\operatorname{Exp}\circ\operatorname{Log} = \operatorname{id}$
on $K[[x]]_1$.
The formal proof bridges the local definitions of $\operatorname{Log}$ and $\operatorname{Exp}$
to Mathlib's Exp/Log framework
(via Lemmas~\ref{lem.fps.fpsLog-eq-Log-val} and~\ref{lem.fps.fpsExp-eq-Exp-val})
and then applies the inverse property.
\end{proof}
```

:::group "non_integer_powers_rules"
Basic exponent rules for the formal power-series power.
:::

```tex
\subsection{Rules of exponents}
```

:::theorem "thm.fps.power-c.rules" (parent := "non_integer_powers_rules") (lean := "AlgebraicCombinatorics.FPS.fpsPow_add, AlgebraicCombinatorics.FPS.fpsPow_mul, AlgebraicCombinatorics.FPS.fpsPow_pow")
Assume that $`K` is a commutative $`\mathbb{Q}`-algebra. For any
$`a,b\in K` and
$`f,g\in K\left[\left[x\right]\right]_1`, we have
$$`f^{a+b}=f^a f^b,\qquad (fg)^a=f^a g^a,\qquad \left(f^a\right)^b=f^{ab}.`
:::

```tex "thm.fps.power-c.rules" (slot := statement)
\begin{theorem}
\label{thm.fps.power-c.rules}
\lean{AlgebraicCombinatorics.FPS.fpsPow_add, AlgebraicCombinatorics.FPS.fpsPow_mul, AlgebraicCombinatorics.FPS.fpsPow_pow}
\leantarget
\leanok
Assume that $K$ is a commutative $\mathbb{Q}%
$-algebra. For any $a,b\in K$ and $f,g\in K\left[  \left[  x\right]  \right]
_{1}$, we have
\[
f^{a+b}=f^{a}f^{b},\ \ \ \ \ \ \ \ \ \ \left(  fg\right)  ^{a}=f^{a}%
g^{a},\ \ \ \ \ \ \ \ \ \ \left(  f^{a}\right)  ^{b}=f^{ab}.
\]
\end{theorem}
```

:::proof "thm.fps.power-c.rules"
_First rule:_
$`f^{a+b}=\operatorname{Exp}((a+b)\operatorname{Log}f)
=\operatorname{Exp}(a\operatorname{Log}f+b\operatorname{Log}f)
=\operatorname{Exp}(a\operatorname{Log}f)\operatorname{Exp}(b\operatorname{Log}f)
=f^a f^b`.

_Second rule:_
$`(fg)^a=\operatorname{Exp}(a\operatorname{Log}(fg))
=\operatorname{Exp}(a(\operatorname{Log}f+\operatorname{Log}g))
=\operatorname{Exp}(a\operatorname{Log}f+a\operatorname{Log}g)
=f^a g^a`.

_Third rule:_
$`(f^a)^b=\operatorname{Exp}(b\operatorname{Log}(f^a))
=\operatorname{Exp}(b\operatorname{Log}(\operatorname{Exp}(a\operatorname{Log}f)))
=\operatorname{Exp}(b\cdot a\operatorname{Log}f)
=\operatorname{Exp}((ab)\operatorname{Log}f)=f^{ab}`.
:::

```tex "thm.fps.power-c.rules" (slot := proof)
\begin{proof}
\textbf{First rule ($f^{a+b}=f^af^b$):}
\begin{align*}
f^{a+b} &= \operatorname{Exp}((a+b)\operatorname{Log}f) \\
&= \operatorname{Exp}(a\operatorname{Log}f + b\operatorname{Log}f) \\
&= \operatorname{Exp}(a\operatorname{Log}f)\cdot\operatorname{Exp}(b\operatorname{Log}f)
\quad\text{(by }\operatorname{Exp}(x+y)=\operatorname{Exp}(x)\operatorname{Exp}(y)\text{)} \\
&= f^a \cdot f^b.
\end{align*}

\textbf{Second rule ($(fg)^a = f^a g^a$):}
\begin{align*}
(fg)^a &= \operatorname{Exp}(a\operatorname{Log}(fg)) \\
&= \operatorname{Exp}(a(\operatorname{Log}f + \operatorname{Log}g))
\quad\text{(by }\operatorname{Log}(fg)=\operatorname{Log}f+\operatorname{Log}g\text{)} \\
&= \operatorname{Exp}(a\operatorname{Log}f + a\operatorname{Log}g) \\
&= \operatorname{Exp}(a\operatorname{Log}f)\cdot\operatorname{Exp}(a\operatorname{Log}g)
= f^a\cdot g^a.
\end{align*}

\textbf{Third rule ($(f^a)^b = f^{ab}$):}
\begin{align*}
(f^a)^b &= \operatorname{Exp}(b\operatorname{Log}(f^a)) \\
&= \operatorname{Exp}(b\operatorname{Log}(\operatorname{Exp}(a\operatorname{Log}f))) \\
&= \operatorname{Exp}(b\cdot a\operatorname{Log}f)
\quad\text{(by }\operatorname{Log}\circ\operatorname{Exp} = \operatorname{id}\text{)} \\
&= \operatorname{Exp}((ab)\operatorname{Log}f) = f^{ab}.
\end{align*}
\end{proof}
```

:::lemma_ "lem.fps.fpsPow-nat" (parent := "non_integer_powers_rules") (lean := "AlgebraicCombinatorics.FPS.fpsPow_nat")
For $`f\in K[[x]]_1` and $`n\in\mathbb{N}`, we have
$`f^n = \underbrace{f\cdot f\cdots f}_{n\text{ times}}`.
That is, the definition of $`f^c` is consistent with the standard power when
$`c\in\mathbb{N}`.
:::

```tex "lem.fps.fpsPow-nat" (slot := statement)
\begin{lemma}
\label{lem.fps.fpsPow-nat}
\lean{AlgebraicCombinatorics.FPS.fpsPow_nat}
\leanhelper
\leanok
For $f\in K[[x]]_1$ and $n\in\mathbb{N}$, we have
$f^n = \underbrace{f\cdot f\cdots f}_{n\text{ times}}$.
That is, our definition of $f^c$ is consistent with the standard power when $c\in\mathbb{N}$.
\end{lemma}
```

:::proof "lem.fps.fpsPow-nat"
Induct on $`n`.
For the base case, $`f^0=1` by the zero-power lemma.
For the induction step,
$`f^{n+1}=f^n\cdot f^1=f^n\cdot f` by the first exponent rule and the
one-power lemma.
:::

```tex "lem.fps.fpsPow-nat" (slot := proof)
\begin{proof}
\leanok
By induction on $n$:
the base case $n=0$ gives $f^0=1$ (by Lemma~\ref{lem.fps.fpsPow-zero}),
and the inductive step uses $f^{n+1} = f^n\cdot f^1 = f^n\cdot f$
(by the first rule of exponents and Lemma~\ref{lem.fps.fpsPow-one}).
\end{proof}
```
