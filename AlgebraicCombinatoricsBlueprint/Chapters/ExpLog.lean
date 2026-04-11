import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.ExpLog

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Exponentials and Logarithms" =>

:::group "exp_log_convention"
The standing hypothesis for the exponential and logarithm constructions.
:::

Throughout this section, unless otherwise stated, we assume that $`K` is not
just a commutative ring, but actually a commutative $`\mathbb{Q}`-algebra.

```tex
\section{Exponentials and logarithms}

\begin{convention}
\label{conv.fps.exp.K-Q-alg}Throughout this section (unless otherwise stated), we assume
that $K$ is not just a commutative ring, but actually a commutative
$\mathbb{Q}$-algebra.
\end{convention}
```

:::group "exp_log_definitions"
The basic exponential and logarithmic power series.
:::

```tex
\subsection{Definitions}
```

:::definition "def.fps.exp-log" (parent := "exp_log_definitions") (lean := "PowerSeries.logbar, PowerSeries.expbar")
Define three FPS $`\exp`, $`\overline{\log}` and $`\overline{\exp}` in
$`K\left[\left[x\right]\right]` by
$$`\exp :=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n},
\qquad
\overline{\log} :=\sum_{n\geq1}\dfrac{\left(-1\right)^{n-1}}{n}x^{n},
\qquad
\overline{\exp} :=\exp-1=\sum_{n\geq1}\dfrac{1}{n!}x^{n}.`

The last equality sign follows from
$`\exp=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}
=\underbrace{\dfrac{1}{0!}}_{=1}\underbrace{x^{0}}_{=1}
+\sum_{n\geq1}\dfrac{1}{n!}x^{n}
=1+\sum_{n\geq1}\dfrac{1}{n!}x^{n}`.
:::

```tex "def.fps.exp-log" (slot := statement)
\begin{definition}
\label{def.fps.exp-log}
\lean{PowerSeries.logbar, PowerSeries.expbar}
\leantarget
\leanok
Define three FPS $\exp$, $\overline{\log}$ and
$\overline{\exp}$ in $K\left[\left[x\right]\right]$ by
\begin{align*}
\exp &  :=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n},\\
\overline{\log}  &  :=\sum_{n\geq1}\dfrac{\left(-1\right)^{n-1}}{n}x^{n},\\
\overline{\exp}  &  :=\exp-1=\sum_{n\geq1}\dfrac{1}{n!}x^{n}.
\end{align*}

(The last equality sign here follows from $\exp=\sum_{n\in\mathbb{N}}\dfrac
{1}{n!}x^{n}=\underbrace{\dfrac{1}{0!}}_{=1}\underbrace{x^{0}}_{=1}
+\sum_{n\geq1}\dfrac{1}{n!}x^{n}=1+\sum_{n\geq1}\dfrac{1}{n!}x^{n}$.)
\end{definition}
```

:::group "exp_log_derivative_helpers"
Helper series and derivative identities.
:::

```tex
\subsection{Helpers for derivative computations}
```

:::lemma_ "lem.fps.invOnePlusX" (parent := "exp_log_derivative_helpers") (lean := "PowerSeries.invOnePlusX")
Define the FPS
$$`\iota := \sum_{n \in \mathbb{N}} (-1)^n x^n.`
This is the geometric series for $`(1+x)^{-1}`; indeed,
$`\iota \cdot (1+x) = 1`.
:::

```tex "lem.fps.invOnePlusX" (slot := statement)
\begin{lemma}[The series $(1+x)^{-1}$]
\label{lem.fps.invOnePlusX}
\lean{PowerSeries.invOnePlusX}
\leanhelper
\leanok
Define the FPS
\[
\iota := \sum_{n \in \mathbb{N}} (-1)^n x^n.
\]
This is the geometric series for $(1+x)^{-1}$; indeed, $\iota \cdot (1+x) = 1$.
\end{lemma}
```

:::proof "lem.fps.invOnePlusX"
Direct verification: the product is computed coefficient-wise and shown to
equal $`1`.
:::

```tex "lem.fps.invOnePlusX" (slot := proof)
\begin{proof}
Direct verification: the product is computed coefficient-wise and shown to equal~$1$.
\end{proof}
```

:::lemma_ "lem.fps.derivative-logbar" (parent := "exp_log_derivative_helpers") (lean := "PowerSeries.derivative_logbar")
We have $`\overline{\log}' = \iota = (1+x)^{-1}`.
:::

```tex "lem.fps.derivative-logbar" (slot := statement)
\begin{lemma}[Derivative of $\overline{\log}$]
\label{lem.fps.derivative-logbar}
\lean{PowerSeries.derivative_logbar}
\leanhelper
\leanok
We have $\overline{\log}' = \iota = (1+x)^{-1}$.
\end{lemma}
```

:::proof "lem.fps.derivative-logbar"
By computing the derivative of
$`\overline{\log} = \sum_{n \ge 1} \frac{(-1)^{n-1}}{n} x^n` term-by-term:
$`\overline{\log}' = \sum_{n \ge 1} (-1)^{n-1} x^{n-1}
= \sum_{n \ge 0} (-1)^n x^n = \iota`.
:::

```tex "lem.fps.derivative-logbar" (slot := proof)
\begin{proof}
\leanok
By computing the derivative of $\overline{\log} = \sum_{n \ge 1} \frac{(-1)^{n-1}}{n} x^n$
term-by-term:
$\overline{\log}' = \sum_{n \ge 1} (-1)^{n-1} x^{n-1} = \sum_{n \ge 0} (-1)^n x^n = \iota$.
\end{proof}
```

:::lemma_ "lem.fps.derivative-expbar" (parent := "exp_log_derivative_helpers") (lean := "PowerSeries.derivative_expbar")
We have $`\overline{\exp}' = \exp`.
:::

```tex "lem.fps.derivative-expbar" (slot := statement)
\begin{lemma}[Derivative of $\overline{\exp}$]
\label{lem.fps.derivative-expbar}
\lean{PowerSeries.derivative_expbar}
\leanhelper
\leanok
We have $\overline{\exp}' = \exp$.
\end{lemma}
```

:::proof "lem.fps.derivative-expbar"
Since $`\overline{\exp} = \exp - 1`, we have
$`\overline{\exp}' = \exp' - 0 = \exp' = \exp`,
where the last equality is the standard fact $`\exp' = \exp`.
:::

```tex "lem.fps.derivative-expbar" (slot := proof)
\begin{proof}
\leanok
Since $\overline{\exp} = \exp - 1$, we have $\overline{\exp}' = \exp' - 0 = \exp' = \exp$,
where the last equality is the standard fact $\exp' = \exp$.
\end{proof}
```

:::lemma_ "lem.fps.invOnePlusX-subst" (parent := "exp_log_derivative_helpers") (lean := "PowerSeries.invOnePlusX_subst_eq_inv")
Let $`g \in K\llbracket x \rrbracket` with $`[x^0]g = 0`.
Then $`\iota \circ g = (1+g)^{-1}`.
:::

```tex "lem.fps.invOnePlusX-subst" (slot := statement)
\begin{lemma}[Substitution of $(1+x)^{-1}$]
\label{lem.fps.invOnePlusX-subst}
\lean{PowerSeries.invOnePlusX_subst_eq_inv}
\leanhelper
\leanok
Let $g \in K\llbracket x \rrbracket$ with $[x^0]g = 0$.
Then $\iota \circ g = (1+g)^{-1}$.
\end{lemma}
```

:::proof "lem.fps.invOnePlusX-subst"
We have
$`(\iota \circ g) \cdot (1 + g)
= (\iota \cdot (1+x)) \circ g = 1 \circ g = 1`.
Since $`[x^0](1+g) \ne 0`, this gives
$`\iota \circ g = (1+g)^{-1}`.
:::

```tex "lem.fps.invOnePlusX-subst" (slot := proof)
\begin{proof}
\leanok
We have $(\iota \circ g) \cdot (1 + g)
= (\iota \cdot (1+x)) \circ g = 1 \circ g = 1$.
Since $[x^0](1+g) \ne 0$, this gives $\iota \circ g = (1+g)^{-1}$.
\end{proof}
```
