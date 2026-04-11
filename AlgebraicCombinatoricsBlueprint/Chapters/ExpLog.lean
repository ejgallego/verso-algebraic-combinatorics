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

:::group "exp_log_inverse_derivatives"
Derivative identities underlying the inverse relationship between exp and log.
:::

```tex
\subsection{The exponential and the logarithm are inverse}
```

:::theorem "prop.fps.exp-log-der" (parent := "exp_log_inverse_derivatives") (lean := "PowerSeries.derivative_exp_comp, PowerSeries.derivative_expbar_comp, PowerSeries.derivative_logbar_comp")
Let $`g\in K\left[\left[x\right]\right]` with $`\left[x^{0}\right]g=0`.
Then:

*(a)* We have
$$`\left(\overline{\exp}\circ g\right)^{\prime}
=\left(\exp\circ g\right)^{\prime}
=\left(\exp\circ g\right)\cdot g^{\prime}.`

*(b)* We have
$$`\left(\overline{\log}\circ g\right)^{\prime}
=\left(1+g\right)^{-1}\cdot g^{\prime}.`
:::

```tex "prop.fps.exp-log-der" (slot := statement)
\begin{proposition}
\label{prop.fps.exp-log-der}
\lean{PowerSeries.derivative_exp_comp, PowerSeries.derivative_expbar_comp, PowerSeries.derivative_logbar_comp}
\leantarget
\leanok
Let $g\in K\left[\left[x\right]\right]$
with $\left[x^{0}\right]g=0$. Then: \medskip

\textbf{(a)} We have
\[
\left(\overline{\exp}\circ g\right)^{\prime}=\left(\exp\circ g\right)
^{\prime}=\left(\exp\circ g\right)\cdot g^{\prime}.
\]

\textbf{(b)} We have
\[
\left(\overline{\log}\circ g\right)^{\prime}=\left(1+g\right)
^{-1}\cdot g^{\prime}.
\]
\end{proposition}
```

:::proof "prop.fps.exp-log-der"
*(a)* Let us first show that
$`\overline{\exp}^{\prime}=\exp^{\prime}=\exp`.
Indeed, $`\overline{\exp}=\exp-1`, so that $`\exp=\overline{\exp}+1` and
therefore
$$`\exp^{\prime}
=\left(\overline{\exp}+1\right)^{\prime}
=\overline{\exp}^{\prime}+\underbrace{1^{\prime}}_{=0}
=\overline{\exp}^{\prime}.`
Next, since
$`\exp=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}`, the definition of a
derivative yields
$$`\exp^{\prime}
=\sum_{n\geq1}\underbrace{n\cdot\dfrac{1}{n!}}_{=\dfrac{1}{\left(n-1\right)!}}x^{n-1}
=\sum_{n\geq1}\dfrac{1}{\left(n-1\right)!}x^{n-1}
=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}
=\exp,`
where we have substituted $`n` for $`n-1` in the sum.
Comparing these equalities, we find
$`\overline{\exp}^{\prime}=\exp`.

Now we can apply the chain rule to $`f=\overline{\exp}`, since
$`\left[x^{0}\right]g=0`, and thus obtain
$$`\left(\overline{\exp}\circ g\right)^{\prime}
=\left(\underbrace{\overline{\exp}^{\prime}}_{=\exp}\circ g\right)\cdot g^{\prime}
=\left(\exp\circ g\right)\cdot g^{\prime}.`
The same computation, but with $`\overline{\exp}` replaced by $`\exp`,
yields
$`\left(\exp\circ g\right)^{\prime}=\left(\exp\circ g\right)\cdot g^{\prime}`.
Combining these formulas proves part *(a)*.

*(b)* We have
$`\overline{\log}=\sum_{n\geq1}\dfrac{\left(-1\right)^{n-1}}{n}x^{n}`.
Thus
$$`\overline{\log}^{\prime}
=\left(\sum_{n\geq1}\dfrac{\left(-1\right)^{n-1}}{n}x^{n}\right)^{\prime}
=\sum_{n\geq1}\underbrace{\dfrac{\left(-1\right)^{n-1}}{n}n}_{=\left(-1\right)^{n-1}}
\underbrace{x^{\prime}}_{=1}x^{n-1}
=\sum_{n\geq1}\left(-1\right)^{n-1}x^{n-1}
=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n},`
where we have substituted $`n` for $`n-1` in the sum.
On the other hand,
$`\left(1+x\right)^{-1}=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n}`.
Comparing these two equalities, we find
$`\overline{\log}^{\prime}=\left(1+x\right)^{-1}`.

Now we can apply the chain rule to $`f=\overline{\log}`, again using
$`\left[x^{0}\right]g=0`, and thus obtain
$$`\left(\overline{\log}\circ g\right)^{\prime}
=\left(\underbrace{\overline{\log}^{\prime}}_{=\left(1+x\right)^{-1}}\circ g\right)\cdot g^{\prime}
=\left(\left(1+x\right)^{-1}\circ g\right)\cdot g^{\prime}.`
However, $`\left(1+x\right)^{-1}\circ g=\left(1+g\right)^{-1}`. Indeed,
$`\dfrac{1}{1+x}\circ g=\dfrac{1\circ g}{\left(1+x\right)\circ g}` since the
FPS $`1+x` is invertible, while $`1\circ g=\underline{1}` and
$`\left(1+x\right)\circ g=1+g`.
Hence
$$`\left(\overline{\log}\circ g\right)^{\prime}
=\left(1+g\right)^{-1}\cdot g^{\prime},`
which proves part *(b)*.
:::

```tex "prop.fps.exp-log-der" (slot := proof)
\begin{proof}
\textbf{(a)} Let us first
show that $\overline{\exp}^{\prime}=\exp^{\prime}=\exp$. Indeed,
$\overline{\exp}=\exp-1$, so that $\exp=\overline{\exp}+1$ and therefore
\begin{align}
\exp^{\prime} &  =\left(\overline{\exp}+1\right)^{\prime}=\overline{\exp
}^{\prime}+\underbrace{1^{\prime}}_{=0}
=\overline{\exp}^{\prime}.
\end{align}
Next, we recall that $\exp=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}$. Hence,
the definition of a derivative yields
\begin{align}
\exp^{\prime} &  =\sum_{n\geq1}\underbrace{n\cdot\dfrac{1}{n!}}%
_{\substack{=\dfrac{1}{\left(n-1\right)!}\\\text{(since }n!=n\cdot\left(
n-1\right)!\text{)}}}x^{n-1}=\sum_{n\geq1}\dfrac{1}{\left(n-1\right)
!}x^{n-1}=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}\nonumber\\
& \qquad\qquad\left(\text{here, we have
substituted }n\text{ for }n-1\text{ in the sum}\right) \nonumber\\
&  =\exp.
\end{align}
Comparing this with the previous equality, we find
\begin{equation}
\overline{\exp}^{\prime}=\exp.
\end{equation}

Now, we can apply the chain rule to $f=\overline{\exp}$
(since $\left[x^{0}\right]g=0$), and
thus obtain
\[
\left(\overline{\exp}\circ g\right)^{\prime}=\left(\underbrace{\overline
{\exp}^{\prime}}_{=\exp}\circ\,g\right)\cdot g^{\prime}=\left(\exp\circ
g\right)\cdot g^{\prime}.
\]
The same computation (but with $\overline{\exp}$ replaced by $\exp$) yields
$\left(\exp\circ g\right)^{\prime}=\left(\exp\circ g\right)\cdot
g^{\prime}$. Combining these two formulas, we obtain $\left(\overline{\exp
}\circ g\right)^{\prime}=\left(\exp\circ g\right)^{\prime}=\left(
\exp\circ g\right)\cdot g^{\prime}$. This proves part \textbf{(a)}.

\textbf{(b)} We have $\overline{\log}=\sum_{n\geq1}\dfrac{\left(-1\right)
^{n-1}}{n}x^{n}$. Thus,
\begin{align*}
\overline{\log}^{\prime} &  =\left(\sum_{n\geq1}\dfrac{\left(-1\right)
^{n-1}}{n}x^{n}\right)^{\prime}
=\sum_{n\geq1}\underbrace{\dfrac{\left(-1\right)^{n-1}}{n}n}_{=\left(
-1\right)^{n-1}}\underbrace{x^{\prime}}_{=1}x^{n-1}=\sum_{n\geq1}\left(
-1\right)^{n-1}x^{n-1}=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n}
\end{align*}
(here, we have substituted $n$ for $n-1$ in the sum). On the other hand,
$\left(1+x\right)^{-1}
=\sum_{n\in\mathbb{N}}\left(-1\right)^{n}x^{n}$. Comparing these two
equalities, we find
\begin{equation}
\overline{\log}^{\prime}=\left(1+x\right)^{-1}.
\end{equation}

Now, we can apply the chain rule to $f=\overline{\log}$ (since $\left[x^{0}\right]g=0$), and
thus obtain
\begin{equation}
\left(\overline{\log}\circ g\right)^{\prime}=\left(\underbrace{\overline
{\log}^{\prime}}_{=\left(1+x\right)^{-1}}\circ\,g\right)\cdot g^{\prime
}=\left(\left(1+x\right)^{-1}\circ g\right)\cdot g^{\prime}.
\end{equation}

However, we claim that $\left(1+x\right)^{-1}\circ g=\left(1+g\right)
^{-1}$. Indeed, $\dfrac{1}{1+x}\circ g=\dfrac{1\circ
g}{\left(1+x\right)\circ g}$ (since the FPS $1+x$ is invertible), and
$1\circ\,g=\underline{1}$ and
$\left(1+x\right)\circ g=1+g$,
so $\left(1+x\right)^{-1}\circ g=\left(1+g\right)^{-1}$. Hence, this
becomes
\[
\left(\overline{\log}\circ g\right)^{\prime}=\left(1+g\right)^{-1}\cdot
g^{\prime}.
\]
This proves part \textbf{(b)}.
\end{proof}
```
