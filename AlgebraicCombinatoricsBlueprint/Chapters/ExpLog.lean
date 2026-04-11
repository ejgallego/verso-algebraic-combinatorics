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

:::group "exp_log_inverse_helpers"
Auxiliary uniqueness and substitution lemmas for the inverse theorem.
:::

```tex
\subsection{Helpers for Theorem~\ref{thm.fps.exp-log-inv}}
```

:::lemma_ "lem.fps.ode-uniqueness-mul-inv" (parent := "exp_log_inverse_helpers") (lean := "PowerSeries.eq_of_derivative_eq_mul_of_inv")
Let $`h_1,h_2,g \in K\llbracket x \rrbracket`.
If $`h_1' = (1+h_1)\cdot g` and $`h_2' = (1+h_2)\cdot g` and
$`[x^0]h_1 = [x^0]h_2`, then $`h_1 = h_2`.
:::

```tex "lem.fps.ode-uniqueness-mul-inv" (slot := statement)
\begin{lemma}[ODE uniqueness: $h' = (1+h) \cdot g$]
\label{lem.fps.ode-uniqueness-mul-inv}
\lean{PowerSeries.eq_of_derivative_eq_mul_of_inv}
\leanhelper
\leanok
Let $h_1, h_2, g \in K\llbracket x \rrbracket$.
If $h_1' = (1 + h_1) \cdot g$ and $h_2' = (1 + h_2) \cdot g$
and $[x^0] h_1 = [x^0] h_2$, then $h_1 = h_2$.
\end{lemma}
```

:::proof "lem.fps.ode-uniqueness-mul-inv"
Use strong induction on the coefficient index. The base case uses the equality
of constant terms. For the inductive step, the differential equation relates
$`\left[x^{n+1}\right]h\cdot (n+1)` to a convolution depending only on lower
coefficients; by induction, these lower coefficients agree for $`h_1` and
$`h_2`, and then the $`\mathbb{Q}`-algebra structure lets us cancel $`n+1`.
:::

```tex "lem.fps.ode-uniqueness-mul-inv" (slot := proof)
\begin{proof}
By strong induction on the coefficient index.
The base case uses the matching constant terms.
For the inductive step, the ODE relates $[x^{n+1}] h \cdot (n+1)$ to a
convolution involving only lower coefficients; by the induction hypothesis,
these coincide for $h_1$ and $h_2$, and one cancels $n+1$ using the
$\mathbb{Q}$-algebra structure.
\end{proof}
```

:::lemma_ "lem.fps.ode-uniqueness-one" (parent := "exp_log_inverse_helpers") (lean := "PowerSeries.eq_of_derivative_eq_one")
Let $`h_1,h_2 \in K\llbracket x \rrbracket`.
If $`h_1' = 1` and $`h_2' = 1` and $`[x^0]h_1 = [x^0]h_2`, then
$`h_1 = h_2`.
:::

```tex "lem.fps.ode-uniqueness-one" (slot := statement)
\begin{lemma}[ODE uniqueness: $h' = 1$]
\label{lem.fps.ode-uniqueness-one}
\lean{PowerSeries.eq_of_derivative_eq_one}
\leanhelper
\leanok
Let $h_1, h_2 \in K\llbracket x \rrbracket$.
If $h_1' = 1$ and $h_2' = 1$ and $[x^0] h_1 = [x^0] h_2$,
then $h_1 = h_2$.
\end{lemma}
```

:::proof "lem.fps.ode-uniqueness-one"
As in the previous lemma: use strong induction on the coefficient index and
cancel $`n+1` at each step.
:::

```tex "lem.fps.ode-uniqueness-one" (slot := proof)
\begin{proof}
As in Lemma~\ref{lem.fps.ode-uniqueness-mul-inv}, by strong induction on
the coefficient index, cancelling $n+1$ at each step.
\end{proof}
```

:::lemma_ "lem.fps.invOnePlusX-subst-expbar-mul-exp" (parent := "exp_log_inverse_helpers") (lean := "PowerSeries.invOnePlusX_subst_expbar_mul_exp")
We have $`(\iota \circ \overline{\exp}) \cdot \exp = 1`.
:::

```tex "lem.fps.invOnePlusX-subst-expbar-mul-exp" (slot := statement)
\begin{lemma}[$\iota \circ \overline{\exp}$ times $\exp$]
\label{lem.fps.invOnePlusX-subst-expbar-mul-exp}
\lean{PowerSeries.invOnePlusX_subst_expbar_mul_exp}
\leanhelper
\leanok
We have $(\iota \circ \overline{\exp}) \cdot \exp = 1$.
\end{lemma}
```

:::proof "lem.fps.invOnePlusX-subst-expbar-mul-exp"
Substitute $`\overline{\exp}` into the identity
$`\iota \cdot (1+x) = 1`, observing that
$`(1+x)\circ \overline{\exp} = 1 + \overline{\exp} = \exp`.
:::

```tex "lem.fps.invOnePlusX-subst-expbar-mul-exp" (slot := proof)
\begin{proof}
We substitute $\overline{\exp}$ into the identity
$\iota \cdot (1 + x) = 1$, noting that
$(1 + x) \circ \overline{\exp} = 1 + \overline{\exp} = \exp$.
\end{proof}
```

:::lemma_ "lem.fps.compos-cst-term-0" (parent := "exp_log_inverse_helpers") (lean := "PowerSeries.constantCoeff_subst_of_constantCoeff_zero")
Let $`f,g\in K\left[\left[x\right]\right]` be two FPSs with
$`\left[x^0\right]g=0`. Then
$`\left[x^0\right](f\circ g)=\left[x^0\right]f`.
:::

```tex "lem.fps.compos-cst-term-0" (slot := statement)
\begin{lemma}
\label{lem.fps.compos-cst-term-0}
\lean{PowerSeries.constantCoeff_subst_of_constantCoeff_zero}
\leantarget
\leanok
Let $f,g\in K\left[\left[x\right]
\right]$ be two FPSs with $\left[x^{0}\right]g=0$. Then, $\left[
x^{0}\right]\left(f\circ g\right)=\left[x^{0}\right]f$.
\end{lemma}
```

:::proof "lem.fps.compos-cst-term-0"
Write $`f=\sum_{n\in\mathbb{N}} f_n x^n`, so
$`f_0=\left[x^0\right]f`. Since
$`f[g]=\sum_{n\in\mathbb{N}} f_n g^n`, the constant-term computation from
substitution gives
$`\left[x^0\right]\left(\sum_{n\in\mathbb{N}} f_n g^n\right)=f_0`. Rewriting
this in terms of $`f\circ g` yields the claim.
:::

```tex "lem.fps.compos-cst-term-0" (slot := proof)
\begin{proof}
\leanok
Write $f$ in the form
$f=\sum_{n\in\mathbb{N}}f_{n}x^{n}$ with $f_{0},f_{1},f_{2},\ldots\in K$.
Thus, $f_{0}=\left[x^{0}\right]f$. Now, $f\left[g\right]=\sum_{n\in\mathbb{N}}f_{n}g^{n}$. However,
$\left[x^{0}\right]
\left(\sum_{n\in\mathbb{N}}f_{n}g^{n}\right)=f_{0}=\left[x^{0}\right]
f$. In view of $f\circ g=f\left[g\right]=\sum_{n\in\mathbb{N}}f_{n}g^{n}$,
we can rewrite this as $\left[x^{0}\right]\left(f\circ g\right)
=\left[x^{0}\right]f$.
\end{proof}
```

:::theorem "thm.fps.exp-log-inv" (parent := "exp_log_inverse_helpers") (lean := "PowerSeries.expbar_comp_logbar, PowerSeries.logbar_comp_expbar")
We have
$$`\overline{\exp}\circ\overline{\log}=x
\qquad\text{and}\qquad
\overline{\log}\circ\overline{\exp}=x.`
:::

```tex "thm.fps.exp-log-inv" (slot := statement)
\begin{theorem}
\label{thm.fps.exp-log-inv}
\lean{PowerSeries.expbar_comp_logbar, PowerSeries.logbar_comp_expbar}
\leantarget
\leanok
We have
\[
\overline{\exp}\circ\overline{\log}=x\ \ \ \ \ \ \ \ \ \ \text{and}%
\ \ \ \ \ \ \ \ \ \ \overline{\log}\circ\overline{\exp}=x.
\]
\end{theorem}
```

:::proof "thm.fps.exp-log-inv"
First prove
$`\overline{\log}\circ\overline{\exp}=x`. The idea is to show that
$`\overline{\log}\circ\overline{\exp}` and $`x` have the same constant term,
namely $`0`, and the same derivative, namely $`1`. Over a
$`\mathbb{Q}`-algebra, a power series is determined by its constant term and
its derivative, so equality follows.

Indeed, $`\left[x^0\right]\overline{\exp}=0`, so the constant-term lemma gives
$`\left[x^0\right]\left(\overline{\log}\circ\overline{\exp}\right)=0`.
Also, the derivative proposition applied to $`g=\overline{\exp}` shows
$`\left(\overline{\log}\circ\overline{\exp}\right)' = 1 = x'`, because
$`1+\overline{\exp}=\exp` and $`\overline{\exp}'=\exp`.
Hence
$`\overline{\log}\circ\overline{\exp}=x`.

For the other identity, first show that
$`\exp\circ\overline{\log}=1+x`. Apply the quotient rule to
$`\dfrac{\exp\circ\overline{\log}}{1+x}`. Using the chain rule together with
$`\overline{\log}'=(1+x)^{-1}`, its derivative simplifies to $`0`, so the
quotient is constant. Comparing constant terms shows this constant is $`1`,
hence $`\exp\circ\overline{\log}=1+x`.

Finally, since $`\overline{\exp}=\exp-1`, we obtain
$`\overline{\exp}\circ\overline{\log}
=\left(\exp\circ\overline{\log}\right)+\left(\underline{-1}\circ\overline{\log}\right)
=(1+x)+(-1)=x`.
:::

```tex "thm.fps.exp-log-inv" (slot := proof)
\begin{proof}
Let us first prove that
$\overline{\log}\circ\overline{\exp}=x$.

The idea of this proof is to show that $\overline{\log}\circ
\overline{\exp}$ and $x$ are two FPSs with the same constant term (namely,
$0$) and with the same derivative. Once this is proved, they must be equal
(since a FPS is determined by its constant term and its derivative over a $\mathbb{Q}$-algebra).

We have $\left[x^{0}\right]\overline{\exp}=0$
(since $\overline{\exp}=\sum_{n\geq1}\dfrac{1}{n!}x^{n}$). Hence, Lemma
\ref{lem.fps.compos-cst-term-0} (applied to $f=\overline{\log}$ and
$g=\overline{\exp}$) yields $\left[x^{0}\right]\left(\overline{\log
}\circ\overline{\exp}\right)=\left[x^{0}\right]\overline{\log}=0$ (since
$\overline{\log}=\sum_{n\geq1}\dfrac{\left(-1\right)^{n-1}}{n}x^{n}$).
Now,
\[
\left[x^{0}\right]\left(\overline{\log}\circ\overline{\exp}-x\right)
=\underbrace{\left[x^{0}\right]\left(\overline{\log}\circ\overline{\exp
}\right)}_{=0}-\underbrace{\left[x^{0}\right]x}_{=0}=0.
\]
However, $\overline{\exp}=\exp-1$ and thus $1+\overline{\exp}=\exp$. Now,
Proposition \ref{prop.fps.exp-log-der} \textbf{(b)} (applied to $g=\overline
{\exp}$) yields
\[
\left(\overline{\log}\circ\overline{\exp}\right)^{\prime}=\left(
\underbrace{1+\overline{\exp}}_{=\exp}\right)^{-1}\cdot\underbrace{\overline
{\exp}^{\prime}}_{=\exp}=\exp^{-1}\cdot\exp=1=x^{\prime}.
\]
Hence,
$\overline{\log}\circ\overline{\exp}-x$ is constant (since its derivative is $0$). Since its constant
term is $0$, this constant must be $0$. Thus, $\overline{\log
}\circ\overline{\exp}=x$.

Now it remains to prove that $\overline{\exp}\circ\overline{\log}=x$.

We shall first show
that $\exp\circ\overline{\log}=1+x$.

To wit: The FPS $1+x$ is invertible. Applying the quotient rule
to $f=\exp\circ\,\overline{\log}$ and
$g=1+x$, we obtain
\[
\left(\dfrac{\exp\circ\,\overline{\log}}{1+x}\right)^{\prime}
=\dfrac{\left(\exp\circ\,\overline{\log}\right)^{\prime}\cdot\left(
1+x\right)-\left(\exp\circ\,\overline{\log}\right)\cdot\left(
1+x\right)^{\prime}}{\left(1+x\right)^{2}}.
\]
In view of
\[
\left(\exp\circ\,\overline{\log}\right)^{\prime}
=\left(\exp\circ\,\overline{\log}\right)\cdot\underbrace{\overline{\log}^{\prime}
}_{=\left(1+x\right)^{-1}}
=\left(\exp\circ\,\overline{\log}\right)\cdot\left(1+x\right)^{-1}
\]
and $\left(1+x\right)^{\prime}=1$, we can rewrite this as
\begin{align*}
\left(\dfrac{\exp\circ\,\overline{\log}}{1+x}\right)^{\prime}
=\dfrac{\left(\exp\circ\,\overline{\log}\right)-\left(\exp
\circ\,\overline{\log}\right)}{\left(1+x\right)^{2}}=0=0^{\prime}.
\end{align*}
Thus,
$\dfrac{\exp\circ\,\overline{\log}}{1+x}$ is constant, say equal to $\underline{a}$ for some $a\in K$.
Then $\exp\circ\,\overline{\log}=a\left(1+x\right)$, so
$\left[x^{0}\right]\left(\exp\circ\,\overline{\log}\right)=a$.
However, it is easy to see that $\left[x^{0}\right]\left(\exp
\circ\,\overline{\log}\right)=1$
(using Lemma \ref{lem.fps.compos-cst-term-0}).
Comparing, we find $a=1$. Thus, $\exp\circ\,\overline{\log}=1+x$.

Now, $\overline{\exp}=\exp-1=\exp+\,\underline{-1}$. Hence,
\begin{align*}
\overline{\exp}\circ\overline{\log}
=\underbrace{\exp\circ\,\overline{\log}}_{=1+x}+\underbrace{\underline{-1}
\circ\overline{\log}}_{=\underline{-1}}
=1+x+\underline{-1}=x.
\end{align*}
This completes the proof.
\end{proof}
```

:::group "exp_log_maps"
The `Exp` and `Log` maps between series with constant term `0` and `1`.
:::

```tex
\subsection{The exponential and the logarithm of an FPS}
```

:::definition "def.fps.Exp-Log-maps" (parent := "exp_log_maps") (lean := "PowerSeries.PowerSeries₀, PowerSeries.PowerSeries₁, PowerSeries.Exp, PowerSeries.Log")
*(a)* Let $`K\left[\left[x\right]\right]_0` denote the set of all FPSs
$`f\in K\left[\left[x\right]\right]` with $`\left[x^0\right]f=0`.

*(b)* Let $`K\left[\left[x\right]\right]_1` denote the set of all FPSs
$`f\in K\left[\left[x\right]\right]` with $`\left[x^0\right]f=1`.

*(c)* Define two maps
$`\operatorname{Exp}:K\left[\left[x\right]\right]_0\to K\left[\left[x\right]\right]_1`,
$`g\mapsto \exp\circ g`,
and
$`\operatorname{Log}:K\left[\left[x\right]\right]_1\to K\left[\left[x\right]\right]_0`,
$`f\mapsto \overline{\log}\circ (f-1)`.
These are well-defined by the following lemma.
:::

```tex "def.fps.Exp-Log-maps" (slot := statement)
\begin{definition}
\label{def.fps.Exp-Log-maps}
\lean{PowerSeries.PowerSeries₀, PowerSeries.PowerSeries₁, PowerSeries.Exp, PowerSeries.Log}
\leantarget
\leanok
\textbf{(a)} We let $K\left[\left[x\right]
\right]_{0}$ denote the set of all FPSs $f\in K\left[\left[x\right]
\right]$ with $\left[x^{0}\right]f=0$. \medskip

\textbf{(b)} We let $K\left[\left[x\right]\right]_{1}$ denote the set
of all FPSs $f\in K\left[\left[x\right]\right]$ with $\left[
x^{0}\right]f=1$. \medskip

\textbf{(c)} We define two maps
\begin{align*}
\operatorname{Exp}:K\left[\left[x\right]\right]_{0} &  \rightarrow
K\left[\left[x\right]\right]_{1},\\
g &  \mapsto\exp\circ g
\end{align*}
and
\begin{align*}
\operatorname{Log}:K\left[\left[x\right]\right]_{1} &  \rightarrow
K\left[\left[x\right]\right]_{0},\\
f &  \mapsto\overline{\log}\circ\left(f-1\right).
\end{align*}
(These two maps are well-defined according to parts \textbf{(c)} and
\textbf{(d)} of Lemma \ref{lem.fps.Exp-Log-maps-wd} below.)
\end{definition}
```

:::lemma_ "lem.fps.Exp-Log-maps-wd" (parent := "exp_log_maps") (lean := "PowerSeries.PowerSeries₀.subst_mem, PowerSeries.PowerSeries₁.subst_mem, PowerSeries.exp_subst_mem_PowerSeries₁, PowerSeries.logbar_subst_sub_one_mem_PowerSeries₀")
*(a)* For any $`f,g\in K\left[\left[x\right]\right]_0`, we have
$`f\circ g\in K\left[\left[x\right]\right]_0`.

*(b)* For any $`f\in K\left[\left[x\right]\right]_1` and
$`g\in K\left[\left[x\right]\right]_0`, we have
$`f\circ g\in K\left[\left[x\right]\right]_1`.

*(c)* For any $`g\in K\left[\left[x\right]\right]_0`, we have
$`\exp\circ g\in K\left[\left[x\right]\right]_1`.

*(d)* For any $`f\in K\left[\left[x\right]\right]_1`, we have
$`f-1\in K\left[\left[x\right]\right]_0` and
$`\overline{\log}\circ (f-1)\in K\left[\left[x\right]\right]_0`.
:::

```tex "lem.fps.Exp-Log-maps-wd" (slot := statement)
\begin{lemma}
\label{lem.fps.Exp-Log-maps-wd}
\lean{PowerSeries.PowerSeries₀.subst_mem, PowerSeries.PowerSeries₁.subst_mem, PowerSeries.exp_subst_mem_PowerSeries₁, PowerSeries.logbar_subst_sub_one_mem_PowerSeries₀}
\leantarget
\leanok
\textbf{(a)} For any $f,g\in K\left[\left[
x\right]\right]_{0}$, we have $f\circ g\in K\left[\left[x\right]
\right]_{0}$. \medskip

\textbf{(b)} For any $f\in K\left[\left[x\right]\right]_{1}$ and $g\in
K\left[\left[x\right]\right]_{0}$, we have $f\circ g\in K\left[
\left[x\right]\right]_{1}$. \medskip

\textbf{(c)} For any $g\in K\left[\left[x\right]\right]_{0}$, we have
$\exp\circ g\in K\left[\left[x\right]\right]_{1}$. \medskip

\textbf{(d)} For any $f\in K\left[\left[x\right]\right]_{1}$, we have
$f-1\in K\left[\left[x\right]\right]_{0}$ and $\overline{\log}
\circ\left(f-1\right)\in K\left[\left[x\right]\right]_{0}$.
\end{lemma}
```

:::proof "lem.fps.Exp-Log-maps-wd"
*(a)* If $`f,g\in K\left[\left[x\right]\right]_0`, then
$`\left[x^0\right]f=0` and $`\left[x^0\right]g=0`. The constant-term
composition lemma gives
$`\left[x^0\right](f\circ g)=\left[x^0\right]f=0`, so
$`f\circ g\in K\left[\left[x\right]\right]_0`.

*(b)* The same argument shows that if $`\left[x^0\right]f=1` and
$`\left[x^0\right]g=0`, then
$`\left[x^0\right](f\circ g)=\left[x^0\right]f=1`, so
$`f\circ g\in K\left[\left[x\right]\right]_1`.

*(c)* Since
$`\exp=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^n`, we have $`\left[x^0\right]\exp=1`,
so $`\exp\in K\left[\left[x\right]\right]_1`. Part *(b)* then gives
$`\exp\circ g\in K\left[\left[x\right]\right]_1`.

*(d)* If $`f\in K\left[\left[x\right]\right]_1`, then
$`\left[x^0\right](f-1)=\left[x^0\right]f-\left[x^0\right]1=1-1=0`, so
$`f-1\in K\left[\left[x\right]\right]_0`. Also,
$`\left[x^0\right]\overline{\log}=0`, so
$`\overline{\log}\in K\left[\left[x\right]\right]_0`. Applying part *(a)* to
$`\overline{\log}` and $`f-1` yields
$`\overline{\log}\circ (f-1)\in K\left[\left[x\right]\right]_0`.
:::

```tex "lem.fps.Exp-Log-maps-wd" (slot := proof)
\begin{proof}
\textbf{(a)} Let $f,g\in
K\left[\left[x\right]\right]_{0}$. Then $\left[
x^{0}\right]f=0$ and $\left[x^{0}\right]g=0$. Hence, Lemma
\ref{lem.fps.compos-cst-term-0} yields $\left[x^{0}\right]\left(f\circ
g\right)=\left[x^{0}\right]f=0$. In other words, $f\circ g\in K\left[
\left[x\right]\right]_{0}$.

\textbf{(b)} This is analogous to the proof of part \textbf{(a)}.

\textbf{(c)} Let $g\in K\left[\left[x\right]\right]_{0}$. From
$\exp=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}x^{n}$, we obtain $\left[
x^{0}\right]\exp=1$, so that $\exp\in K\left[\left[
x\right]\right]_{1}$. Hence, part
\textbf{(b)} (applied to $f=\exp$) yields $\exp\circ g\in K\left[\left[
x\right]\right]_{1}$.

\textbf{(d)} Let $f\in K\left[\left[x\right]\right]_{1}$. Thus,
$\left[x^{0}\right]f=1$. Now,
$\left[x^{0}\right]\left(f-1\right)=\left[x^{0}\right]
f-\left[x^{0}\right]1=1-1=0$, so that $f-1\in
K\left[\left[x\right]\right]_{0}$. Furthermore, $\left[x^{0}\right]
\overline{\log}=0$ and thus $\overline{\log}\in K\left[\left[
x\right]\right]_{0}$. Hence, part
\textbf{(a)} (applied to $\overline{\log}$ and $f-1$ instead of $f$ and $g$)
yields $\overline{\log}\circ\left(f-1\right)\in K\left[\left[x\right]
\right]_{0}$.
\end{proof}
```

:::lemma_ "lem.fps.Exp-Log-maps-inv" (parent := "exp_log_maps") (lean := "PowerSeries.Log_Exp, PowerSeries.Exp_Log, PowerSeries.Exp_Log_inverse")
The maps $`\operatorname{Exp}` and $`\operatorname{Log}` are mutually inverse
bijections between
$`K\left[\left[x\right]\right]_0` and $`K\left[\left[x\right]\right]_1`.
:::

```tex "lem.fps.Exp-Log-maps-inv" (slot := statement)
\begin{lemma}
\label{lem.fps.Exp-Log-maps-inv}
\lean{PowerSeries.Log_Exp, PowerSeries.Exp_Log, PowerSeries.Exp_Log_inverse}
\leantarget
\leanok
The maps $\operatorname{Exp}$ and
$\operatorname{Log}$ are mutually inverse bijections between $K\left[
\left[x\right]\right]_{0}$ and $K\left[\left[x\right]\right]_{1}$.
\end{lemma}
```

:::proof "lem.fps.Exp-Log-maps-inv"
First observe that every $`g\in K\left[\left[x\right]\right]_0` satisfies
$`\exp\circ g = \overline{\exp}\circ g + 1`, since
$`\exp=\overline{\exp}+\underline{1}` and $`\underline{1}\circ g=\underline{1}`.

Now let $`f\in K\left[\left[x\right]\right]_1`. Then
$`f-1\in K\left[\left[x\right]\right]_0` by the previous lemma. Using
associativity of composition together with
$`\overline{\exp}\circ\overline{\log}=x`, we obtain
$`\overline{\exp}\circ\left(\overline{\log}\circ (f-1)\right)=f-1`.
Adding $`1` and using the observation above shows
$`\left(\operatorname{Exp}\circ\operatorname{Log}\right)(f)=f`.

The same idea, using
$`\overline{\log}\circ\overline{\exp}=x`, shows that
$`\operatorname{Log}\circ\operatorname{Exp}=\operatorname{id}`.
Hence the two maps are mutually inverse bijections.
:::

```tex "lem.fps.Exp-Log-maps-inv" (slot := proof)
\begin{proof}
\leanok
First, we make a simple
auxiliary observation: Each $g\in K\left[\left[x\right]\right]_{0}$
satisfies
\begin{equation}
\exp\circ g=\overline{\exp}\circ g+1.
\end{equation}

[\textit{Proof of this auxiliary observation:} Recall that $\overline{\exp}=\exp-1$, so
that $\exp=\overline{\exp}+\underline{1}$. Hence,
$\exp\circ g=\left(\overline{\exp}+\underline{1}\right)\circ g=\overline
{\exp}\circ g+\underline{1}\circ g$. But
$\underline{1}\circ g=\underline{1}=1$. Hence, $\exp\circ g=\overline{\exp
}\circ g+1$.]

Now, let us show that $\operatorname{Exp}\circ\operatorname{Log}
=\operatorname{id}$. Indeed, we fix some $f\in K\left[\left[x\right]
\right]_{1}$. Then, $f-1\in K\left[\left[x\right]\right]_{0}$ (by
Lemma \ref{lem.fps.Exp-Log-maps-wd} \textbf{(d)}). By associativity of composition and Theorem \ref{thm.fps.exp-log-inv}, we get
\[
\overline{\exp}\circ\left(\overline{\log}\circ\left(f-1\right)\right)
=\underbrace{\left(\overline{\exp}\circ\overline{\log}\right)
}_{=x}\circ\left(f-1\right)=x\circ\left(f-1\right)
=f-1.
\]
Hence
\begin{align*}
\left(\operatorname{Exp}\circ\operatorname{Log}\right)\left(f\right)
&  =\exp\circ\left(\operatorname{Log}f\right) \\
&  =\overline{\exp}\circ\underbrace{\left(\operatorname{Log}f\right)
}_{=\overline{\log}\circ\left(f-1\right)}+\,1
\end{align*}
(by the auxiliary observation above), so
\begin{align*}
\left(\operatorname{Exp}\circ\operatorname{Log}\right)\left(f\right)
&  =\underbrace{\overline{\exp}\circ\left(\overline{\log}\circ\left(
f-1\right)\right)}_{=f-1}+\,1
=\left(f-1\right)+1=f.
\end{align*}

Using a similar argument (with $\overline{\log}\circ\overline{\exp}=x$ from Theorem \ref{thm.fps.exp-log-inv}), we can show that $\operatorname{Log}\circ
\operatorname{Exp}=\operatorname{id}$.
Combining, $\operatorname{Exp}$ and
$\operatorname{Log}$ are mutually inverse bijections.
\end{proof}
```

:::group "exp_log_group_helpers"
Auxiliary lemmas used to put group structures on the `Exp` and `Log` domains.
:::

```tex
\subsection{Helpers for the group structure}
```

:::lemma_ "lem.fps.sub-one-mem-PS0" (parent := "exp_log_group_helpers") (lean := "PowerSeries.sub_one_mem_PowerSeries₀")
If $`f \in K\llbracket x \rrbracket_1`, that is, if $`[x^0]f = 1`, then
$`f - 1 \in K\llbracket x \rrbracket_0`, that is, $`[x^0](f-1) = 0`.
:::

```tex "lem.fps.sub-one-mem-PS0" (slot := statement)
\begin{lemma}[$f - 1 \in K\llbracket x \rrbracket_0$ when $f \in K\llbracket x \rrbracket_1$]
\label{lem.fps.sub-one-mem-PS0}
\lean{PowerSeries.sub_one_mem_PowerSeries₀}
\leanhelper
\leanok
If $f \in K\llbracket x \rrbracket_1$ (i.e., $[x^0]f = 1$),
then $f - 1 \in K\llbracket x \rrbracket_0$ (i.e., $[x^0](f-1) = 0$).
\end{lemma}
```

:::proof "lem.fps.sub-one-mem-PS0"
$`\left[x^0\right](f-1)=\left[x^0\right]f-1=1-1=0`.
:::

```tex "lem.fps.sub-one-mem-PS0" (slot := proof)
\begin{proof}
\leanok
$[x^0](f - 1) = [x^0]f - 1 = 1 - 1 = 0$.
\end{proof}
```

:::lemma_ "lem.fps.ode-uniqueness-mul-self" (parent := "exp_log_group_helpers") (lean := "PowerSeries.eq_of_derivative_eq_mul_self")
Let $`h_1,h_2,g \in K\llbracket x \rrbracket`.
If $`h_1' = h_1 \cdot g` and $`h_2' = h_2 \cdot g` and
$`[x^0]h_1 = [x^0]h_2`, then $`h_1 = h_2`.
:::

```tex "lem.fps.ode-uniqueness-mul-self" (slot := statement)
\begin{lemma}[ODE uniqueness: $h' = h \cdot g$]
\label{lem.fps.ode-uniqueness-mul-self}
\lean{PowerSeries.eq_of_derivative_eq_mul_self}
\leanhelper
\leanok
Let $h_1, h_2, g \in K\llbracket x \rrbracket$.
If $h_1' = h_1 \cdot g$ and $h_2' = h_2 \cdot g$
and $[x^0] h_1 = [x^0] h_2$, then $h_1 = h_2$.
\end{lemma}
```

:::proof "lem.fps.ode-uniqueness-mul-self"
Use strong induction on the coefficient index. The differential equation gives
$`\left[x^{n+1}\right]h \cdot (n+1) = \left[x^n\right](h\cdot g)`, and the
right-hand side only depends on coefficients of $`h` of index at most $`n`.
By induction these lower coefficients agree for $`h_1` and $`h_2`, and then
the $`\mathbb{Q}`-algebra structure lets us cancel $`n+1`.
:::

```tex "lem.fps.ode-uniqueness-mul-self" (slot := proof)
\begin{proof}
By strong induction on the coefficient index. The ODE gives
$[x^{n+1}] h \cdot (n+1) = [x^n](h \cdot g)$; the right side is a
convolution involving only coefficients of $h$ of index $\le n$,
which agree by induction hypothesis. Cancelling $n+1$ uses the
$\mathbb{Q}$-algebra structure.
\end{proof}
```

:::lemma_ "lem.fps.Exp-zero-Log-one" (parent := "exp_log_group_helpers") (lean := "PowerSeries.Exp_zero, PowerSeries.Log_one")
The map $`\operatorname{Exp}` sends
$`0 \in K\llbracket x \rrbracket_0` to
$`1 \in K\llbracket x \rrbracket_1`, and
$`\operatorname{Log}` sends $`1` to $`0`.
:::

```tex "lem.fps.Exp-zero-Log-one" (slot := statement)
\begin{lemma}[$\operatorname{Exp}(0) = 1$ and $\operatorname{Log}(1) = 0$]
\label{lem.fps.Exp-zero-Log-one}
\lean{PowerSeries.Exp_zero, PowerSeries.Log_one}
\leanhelper
\leanok
The map $\operatorname{Exp}$ sends $0 \in K\llbracket x \rrbracket_0$
to $1 \in K\llbracket x \rrbracket_1$, and $\operatorname{Log}$
sends $1$ to $0$.
\end{lemma}
```

:::proof "lem.fps.Exp-zero-Log-one"
$`\operatorname{Exp}(0)=\exp\circ 0 = 1`, because substituting $`0` picks out
the constant term of $`\exp`, which is $`1`.
Likewise,
$`\operatorname{Log}(1)=\overline{\log}\circ (1-1)=\overline{\log}\circ 0=0`,
because the constant term of $`\overline{\log}` is $`0`.
:::

```tex "lem.fps.Exp-zero-Log-one" (slot := proof)
\begin{proof}
\leanok
$\operatorname{Exp}(0) = \exp \circ 0 = 1$ (since $[x^0]\exp = 1$ and
substituting $0$ picks out the constant term).
$\operatorname{Log}(1) = \overline{\log} \circ (1 - 1) = \overline{\log} \circ 0 = 0$
(since $[x^0]\overline{\log} = 0$).
\end{proof}
```

:::group "exp_log_group_structure"
How `Exp` turns addition into multiplication, and `Log` does the reverse.
:::

```tex
\subsection{Addition to multiplication}
```

:::lemma_ "lem.fps.Exp-Log-additive" (parent := "exp_log_group_structure") (lean := "PowerSeries.Exp_add, PowerSeries.Log_mul")
*(a)* For any
$`f,g\in K\left[\left[x\right]\right]_0`, we have
$$`\operatorname{Exp}(f+g)=\operatorname{Exp}f\cdot \operatorname{Exp}g.`

*(b)* For any
$`f,g\in K\left[\left[x\right]\right]_1`, we have
$$`\operatorname{Log}(fg)=\operatorname{Log}f+\operatorname{Log}g.`
:::

```tex "lem.fps.Exp-Log-additive" (slot := statement)
\begin{lemma}
\label{lem.fps.Exp-Log-additive}
\lean{PowerSeries.Exp_add, PowerSeries.Log_mul}
\leantarget
\leanok
\textbf{(a)} For any $f,g\in K\left[\left[
x\right]\right]_{0}$, we have
\[
\operatorname{Exp}\left(f+g\right)=\operatorname{Exp}f\cdot
\operatorname{Exp}g.
\]

\textbf{(b)} For any $f,g\in K\left[\left[x\right]\right]_{1}$, we
have
\[
\operatorname{Log}\left(fg\right)=\operatorname{Log}
f+\operatorname{Log}g.
\]
\end{lemma}
```

:::proof "lem.fps.Exp-Log-additive"
*(a)* For $`f,g\in K\left[\left[x\right]\right]_0`, the formal series
definitions give
$`\operatorname{Exp}f=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}f^n`,
$`\operatorname{Exp}g=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}g^n`,
and
$`\operatorname{Exp}(f+g)=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}(f+g)^n`.
Expanding with the binomial formula and rearranging gives exactly the product
$`\operatorname{Exp}f\cdot \operatorname{Exp}g`.

*(b)* This follows from part *(a)* because $`\operatorname{Log}` is inverse to
$`\operatorname{Exp}`. Setting
$`u=\operatorname{Log}f` and $`v=\operatorname{Log}g`, part *(a)* yields
$`\operatorname{Exp}(u+v)=\operatorname{Exp}u\cdot\operatorname{Exp}v`; then
apply $`\operatorname{Log}` to both sides.
:::

```tex "lem.fps.Exp-Log-additive" (slot := proof)
\begin{proof}
\textbf{(a)} Let $f,g\in K\left[\left[x\right]\right]_{0}$. Thus, $\left[
x^{0}\right]f=0$ and $\left[x^{0}\right]g=0$. By the definition of $\operatorname{Exp}$, we have
\[
\operatorname{Exp}f=\exp\circ f=\sum_{n\in\mathbb{N}
}\dfrac{1}{n!}f^{n}.
\]
Similarly, $\operatorname{Exp}g=\sum_{n\in\mathbb{N}}\dfrac{1}{n!}g^{n}$
and
$\operatorname{Exp}\left(f+g\right)=\sum_{n\in\mathbb{N}}\dfrac{1}
{n!}\left(f+g\right)^{n}$.

Now, the latter equality becomes
\begin{align*}
\operatorname{Exp}\left(f+g\right) &  =\sum_{n\in\mathbb{N}}\dfrac{1}
{n!}\sum\limits_{k=0}
^{n}\dbinom{n}{k}f^{k}g^{n-k}
=\sum_{k\in\mathbb{N}}\ \ \sum\limits_{\ell
\in\mathbb{N}}\dfrac{1}{k!\ell!}f^{k}g^{\ell}.
\end{align*}
Comparing this with
$\operatorname{Exp}f\cdot\operatorname{Exp}g
=\sum_{k\in\mathbb{N}}\ \ \sum_{\ell\in
\mathbb{N}}\dfrac{1}{k!\ell!}f^{k}g^{\ell}$,
we obtain $\operatorname{Exp}\left(f+g\right)=\operatorname{Exp}
f\cdot\operatorname{Exp}g$.

(In the Lean formalization, this is proved via ODE uniqueness:
both sides satisfy the ODE $h^{\prime} = h \cdot (f^{\prime} + g^{\prime})$ with the same initial condition.)

\textbf{(b)} This follows from part \textbf{(a)}, since we know that
$\operatorname{Log}$ is inverse to $\operatorname{Exp}$. Setting
$u=\operatorname{Log}f$ and $v=\operatorname{Log}g$, part \textbf{(a)}
gives $\operatorname{Exp}\left(u+v\right)=\operatorname{Exp}u\cdot\operatorname{Exp}v$,
and applying $\operatorname{Log}$ (using Lemma \ref{lem.fps.Exp-Log-maps-inv}) yields
$\operatorname{Log}\left(fg\right)=\operatorname{Log}f+\operatorname{Log}g$.
\end{proof}
```

:::theorem "prop.fps.Exp-Log-groups" (parent := "exp_log_group_structure") (lean := "PowerSeries.PowerSeries₀.addSubgroup, PowerSeries.PowerSeries₁.subgroup")
*(a)* The subset
$`K\left[\left[x\right]\right]_0` of $`K\left[\left[x\right]\right]` is closed
under addition and subtraction and contains $`0`, so it forms a group
$`\left(K\left[\left[x\right]\right]_0,+,0\right)`.

*(b)* The subset
$`K\left[\left[x\right]\right]_1` of $`K\left[\left[x\right]\right]` is closed
under multiplication and division and contains $`1`, so it forms a group
$`\left(K\left[\left[x\right]\right]_1,\cdot,1\right)`.
:::

```tex "prop.fps.Exp-Log-groups" (slot := statement)
\begin{proposition}
\label{prop.fps.Exp-Log-groups}
\lean{PowerSeries.PowerSeries₀.addSubgroup, PowerSeries.PowerSeries₁.subgroup}
\leantarget
\leanok
\textbf{(a)} The subset $K\left[\left[
x\right]\right]_{0}$ of $K\left[\left[x\right]\right]$ is closed
under addition and subtraction and contains $0$, and thus forms a group
$\left(K\left[\left[x\right]\right]_{0},+,0\right)$. \medskip

\textbf{(b)} The subset $K\left[\left[x\right]\right]_{1}$ of
$K\left[\left[x\right]\right]$ is closed under multiplication and
division and contains $1$, and thus forms a group $\left(K\left[\left[
x\right]\right]_{1},\cdot,1\right)$.
\end{proposition}
```

:::proof "prop.fps.Exp-Log-groups"
*(a)* The zero series belongs to
$`K\left[\left[x\right]\right]_0`, and if
$`f,g\in K\left[\left[x\right]\right]_0`, then the constant term of both
$`f+g` and $`f-g` is again $`0`.

*(b)* Any element of
$`K\left[\left[x\right]\right]_1` is invertible because its constant term is
$`1`. The set is closed under multiplication because constant terms multiply,
and it is closed under division because inverses stay in the same set.
:::

```tex "prop.fps.Exp-Log-groups" (slot := proof)
\begin{proof}
\textbf{(a)} It is clear
that the set $K\left[\left[x\right]\right]_{0}$ contains the FPS $0$
(since $\left[x^{0}\right]0=0$). If $f,g\in K\left[\left[x\right]\right]_{0}$, then
$\left[x^{0}\right]f=0$ and $\left[x^{0}\right]g=0$, and therefore
$f+g\in K\left[\left[x\right]\right]_{0}$ (since
$\left[x^{0}\right]\left(
f+g\right)=0+0=0$) and $f-g\in K\left[\left[x\right]\right]
_{0}$ (by a similar argument).

\textbf{(b)} Any $a\in K\left[\left[
x\right]\right]_{1}$ is invertible
in $K\left[\left[x\right]\right]$ (since $\left[x^{0}\right]a=1$ is invertible in $K$).
Next, $K\left[\left[x\right]\right]_{1}$ is closed under
multiplication: if $f,g\in K\left[\left[x\right]\right]_{1}$,
then $\left[x^{0}\right]f=1$ and $\left[x^{0}\right]g=1$, and
therefore $\left[x^{0}\right]\left(
fg\right)=1\cdot 1=1$.
Similarly, $K\left[\left[x\right]\right]_{1}$ is closed
under division.
\end{proof}
```

:::theorem "thm.fps.Exp-Log-group-iso" (parent := "exp_log_group_structure") (lean := "PowerSeries.Exp_Log_groupIso")
The maps
$$`\operatorname{Exp}:\left(K\left[\left[x\right]\right]_{0},+,0\right)
\rightarrow\left(K\left[\left[x\right]\right]_{1},\cdot,1\right)`
and
$$`\operatorname{Log}:\left(K\left[\left[x\right]\right]_{1},\cdot,1\right)
\rightarrow\left(K\left[\left[x\right]\right]_{0},+,0\right)`
are mutually inverse group isomorphisms.
:::

```tex "thm.fps.Exp-Log-group-iso" (slot := statement)
\begin{theorem}
\label{thm.fps.Exp-Log-group-iso}
\lean{PowerSeries.Exp_Log_groupIso}
\leantarget
\leanok
The maps
\[
\operatorname{Exp}:\left(K\left[\left[x\right]\right]_{0}
,+,0\right)\rightarrow\left(K\left[\left[x\right]\right]_{1}
,\cdot,1\right)
\]
and
\[
\operatorname{Log}:\left(K\left[\left[x\right]\right]_{1}
,\cdot,1\right)\rightarrow\left(K\left[\left[x\right]\right]
_{0},+,0\right)
\]
are mutually inverse group isomorphisms.
\end{theorem}
```

:::proof "thm.fps.Exp-Log-group-iso"
The additive/multiplicative compatibility lemma shows that the two maps are
group homomorphisms, and the inverse-map lemma shows that they are mutually
inverse. Therefore they are mutually inverse group isomorphisms.
:::

```tex "thm.fps.Exp-Log-group-iso" (slot := proof)
\begin{proof}
Lemma
\ref{lem.fps.Exp-Log-additive} yields that these two maps are group
homomorphisms. Lemma \ref{lem.fps.Exp-Log-maps-inv}
shows that they are mutually inverse. Combining these results, we conclude
that these two maps are mutually inverse group isomorphisms.
\end{proof}
```

:::group "exp_log_loder"
The logarithmic derivative and its first basic identities.
:::

```tex
\subsection{The logarithmic derivative}
```

:::definition "def.fps.loder.1" (parent := "exp_log_loder") (lean := "PowerSeries.loder")
In this definition, we do _not_ use the standing
$`\mathbb{Q}`-algebra convention, so $`K` can be an arbitrary commutative
ring. Set
$`K\left[\left[x\right]\right]_1=\left\{f\in K\left[\left[x\right]\right]\mid \left[x^0\right]f=1\right\}`.

For any FPS $`f\in K\left[\left[x\right]\right]_1`, define the
_logarithmic derivative_ $`\operatorname{loder}f\in K\left[\left[x\right]\right]`
to be the FPS
$`\dfrac{f'}{f}`. This is well-defined because such an $`f` is invertible.
:::

```tex "def.fps.loder.1" (slot := statement)
\begin{definition}
\label{def.fps.loder.1}
\lean{PowerSeries.loder}
\leantarget
\leanok
In this definition, we do \textbf{not} use Convention
\ref{conv.fps.exp.K-Q-alg}; thus, $K$ can be an arbitrary commutative ring.
However, we set $K\left[\left[x\right]\right]_{1}=\left\{f\in
K\left[\left[x\right]\right]\ \mid\ \left[x^{0}\right]f=1\right\}
$.

For any FPS $f\in K\left[\left[x\right]\right]_{1}$, we define the
\emph{logarithmic derivative} $\operatorname{loder}f\in K\left[\left[
x\right]\right]$ to be the FPS $\dfrac{f^{\prime}}{f}$. (This is
well-defined, since $f$ is easily seen to be invertible.)
\end{definition}
```

:::lemma_ "lem.fps.isUnit-constantCoeff-one" (parent := "exp_log_loder") (lean := "PowerSeries.isUnit_of_constantCoeff_eq_one, PowerSeries.isUnit_iff_constantCoeff_isUnit, PowerSeries.mul_inv_cancel_of_constantCoeff_eq_one, PowerSeries.inv_mul_cancel_of_constantCoeff_eq_one, PowerSeries.constantCoeff_inv_of_constantCoeff_eq_one")
If $`\left[x^0\right]f = 1`, then $`f` is a unit in
$`K\llbracket x \rrbracket`; that is,
$`f\cdot f^{-1}=1` and $`f^{-1}\cdot f=1`.
Moreover, $`\left[x^0\right](f^{-1})=1`.
More generally, $`f` is a unit if and only if $`\left[x^0\right]f` is a unit
in $`K`.
:::

```tex "lem.fps.isUnit-constantCoeff-one" (slot := statement)
\begin{lemma}[Invertibility of FPS with constant term $1$]
\label{lem.fps.isUnit-constantCoeff-one}
\lean{PowerSeries.isUnit_of_constantCoeff_eq_one, PowerSeries.isUnit_iff_constantCoeff_isUnit, PowerSeries.mul_inv_cancel_of_constantCoeff_eq_one, PowerSeries.inv_mul_cancel_of_constantCoeff_eq_one, PowerSeries.constantCoeff_inv_of_constantCoeff_eq_one}
\leanhelper
\leanok
If $[x^0]f = 1$, then $f$ is a unit in $K\llbracket x \rrbracket$, i.e.,
$f \cdot f^{-1} = 1$ and $f^{-1} \cdot f = 1$.
Moreover, $[x^0](f^{-1}) = 1$.
More generally, $f$ is a unit iff $[x^0]f$ is a unit in $K$.
\end{lemma}
```

:::proof "lem.fps.isUnit-constantCoeff-one"
Since $`\left[x^0\right]f` is a unit, the invertibility criterion for power
series gives that $`f` is invertible. The constant coefficient of $`f^{-1}` is
then the inverse of $`\left[x^0\right]f = 1`, so it is again $`1`.
:::

```tex "lem.fps.isUnit-constantCoeff-one" (slot := proof)
\begin{proof}
\leanok
Since $[x^0]f$ is a unit, the invertibility criterion for power series
gives the result (a power series is invertible if and only if its constant coefficient is invertible).
The constant coefficient of $f^{-1}$ is the inverse of $[x^0]f = 1$.
\end{proof}
```

:::lemma_ "lem.fps.loder-one" (parent := "exp_log_loder") (lean := "PowerSeries.loder_one")
$`\operatorname{loder}(1) = 0`.
:::

```tex "lem.fps.loder-one" (slot := statement)
\begin{lemma}[$\operatorname{loder}(1) = 0$]
\label{lem.fps.loder-one}
\lean{PowerSeries.loder_one}
\leanhelper
\leanok
$\operatorname{loder}(1) = 0$.
\end{lemma}
```

:::proof "lem.fps.loder-one"
$`1' = 0`, so
$`\operatorname{loder}(1) = 0\cdot 1^{-1} = 0`.
:::

```tex "lem.fps.loder-one" (slot := proof)
\begin{proof}
\leanok
$1' = 0$, so $\operatorname{loder}(1) = 0 \cdot 1^{-1} = 0$.
\end{proof}
```

:::theorem "prop.fps.loder.log" (parent := "exp_log_loder") (lean := "PowerSeries.loder_eq_derivative_Log")
Let $`K` be a commutative $`\mathbb{Q}`-algebra. Let
$`f\in K\left[\left[x\right]\right]_1` be an FPS. Then
$`\operatorname{loder}f = \left(\operatorname{Log}f\right)'`.
:::

```tex "prop.fps.loder.log" (slot := statement)
\begin{proposition}
\label{prop.fps.loder.log}
\lean{PowerSeries.loder_eq_derivative_Log}
\leantarget
\leanok
Let $K$ be a commutative $\mathbb{Q}$-algebra. Let
$f\in K\left[\left[x\right]\right]_{1}$ be an FPS. Then,
$\operatorname{loder}f=\left(\operatorname{Log}f\right)^{\prime}$.
\end{proposition}
```

:::proof "prop.fps.loder.log"
By definition,
$`\operatorname{Log}f=\overline{\log}\circ (f-1)`.
Since $`f\in K\left[\left[x\right]\right]_1`, we have
$`\left[x^0\right](f-1)=0`, so
`prop.fps.exp-log-der` part *(b)* applies and gives
$`\left(\operatorname{Log}f\right)' = f^{-1}\cdot (f-1)'`.
But $`(f-1)' = f'`, hence
$`\left(\operatorname{Log}f\right)' = \dfrac{f'}{f} = \operatorname{loder}f`.
:::

```tex "prop.fps.loder.log" (slot := proof)
\begin{proof}
\leanok
The definition of
$\operatorname{Log}$ yields $\operatorname{Log}f=\overline{\log}\circ\left(
f-1\right)$.

From $f\in K\left[\left[x\right]\right]_{1}$, we obtain $\left[
x^{0}\right]f=1$. Now, $\left[x^{0}\right]
\left(f-1\right)=\left[x^{0}\right]f-\left[x^{0}\right]1=0$. Hence, Proposition
\ref{prop.fps.exp-log-der} \textbf{(b)} (applied to $g=f-1$) yields
\[
\left(\overline{\log}\circ\left(f-1\right)\right)^{\prime}=\left(
\underbrace{1+\left(f-1\right)}_{=f}\right)^{-1}\cdot\left(f-1\right)
^{\prime}=f^{-1}\cdot\left(f-1\right)^{\prime}=\dfrac{\left(f-1\right)
^{\prime}}{f}.
\]
In view of $\operatorname{Log}f=\overline{\log}\circ\left(f-1\right)$, we
can rewrite this as
$\left(\operatorname{Log}f\right)^{\prime}=\dfrac{\left(f-1\right)
^{\prime}}{f}$.

Since $\left(f-1\right)^{\prime}=f^{\prime}$, we can rewrite
this further as $\left(\operatorname{Log}f\right)^{\prime}=\dfrac
{f^{\prime}}{f}=\operatorname{loder}f$.
\end{proof}
```
