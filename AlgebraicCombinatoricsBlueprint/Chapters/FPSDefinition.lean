import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPSDefinition

open Verso.Genre
open Verso.Genre.Manual
open Informal
open AlgebraicCombinatorics

#doc (Manual) "Formal Power Series: Definition and Basic Properties" =>

:::group "fps_definition_convention"
The standing convention on the base commutative ring.
:::

Fix a commutative ring $`K`. For example, $`K` can be $`\mathbb{Z}` or
$`\mathbb{Q}` or $`\mathbb{C}`.

```tex
\section{Formal power series: definition and basic properties}

\subsection{Convention}

Fix a commutative ring $K$. (For example, $K$ can be $\mathbb{Z}$ or
$\mathbb{Q}$ or $\mathbb{C}$.)
```

:::group "fps_definition_basic"
The definition of formal power series, their basic operations, and coefficient
notation.
:::

```tex
\subsection{The definition of formal power series}
```

:::definition "def.fps.fps" (parent := "fps_definition_basic") (lean := "AlgebraicCombinatorics.FPS.fpsEquivSeq")
A _formal power series_, or short, _FPS_, in $`1` indeterminate over $`K`
means a sequence
$`\left(a_{0},a_{1},a_{2},\ldots\right) = \left(a_{n}\right)_{n\in\mathbb{N}} \in K^{\mathbb{N}}`
of elements of $`K`.
:::

```tex "def.fps.fps" (slot := statement)
\begin{definition}
\label{def.fps.fps}
\lean{AlgebraicCombinatorics.FPS.fpsEquivSeq}
\leantarget
\leanok
A \emph{formal power series} (or, short, \emph{FPS}) in $1$
indeterminate over $K$ means a sequence $\left(a_{0},a_{1},a_{2}%
,\ldots\right) = \left(a_{n}\right)_{n\in\mathbb{N}} \in K^{\mathbb{N}}$ of
elements of $K$.
\end{definition}
```

:::definition "def.fps.ops" (parent := "fps_definition_basic") (lean := "AlgebraicCombinatorics.FPS.coeff_add_fps, AlgebraicCombinatorics.FPS.coeff_sub_fps, AlgebraicCombinatorics.FPS.coeff_smul_fps, AlgebraicCombinatorics.FPS.coeff_mul_fps, AlgebraicCombinatorics.FPS.coeff_C_fps")
*(a)* The _sum_ of two FPSs
$`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)` and
$`\mathbf{b}=\left(b_{0},b_{1},b_{2},\ldots\right)` is defined to be the FPS
$$`\left(a_{0}+b_{0},\ \ a_{1}+b_{1},\ \ a_{2}+b_{2},\ \ \ldots\right).`
It is denoted by $`\mathbf{a}+\mathbf{b}`.

*(b)* The _difference_ of two FPSs
$`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)` and
$`\mathbf{b}=\left(b_{0},b_{1},b_{2},\ldots\right)` is defined to be the FPS
$$`\left(a_{0}-b_{0},\ \ a_{1}-b_{1},\ \ a_{2}-b_{2},\ \ \ldots\right).`
It is denoted by $`\mathbf{a}-\mathbf{b}`.

*(c)* If $`\lambda\in K` and if
$`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)` is an FPS, then we define
an FPS
$$`\lambda\mathbf{a}:=\left(\lambda a_{0},\lambda a_{1},\lambda a_{2},\ldots\right).`

*(d)* The _product_ of two FPSs
$`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)` and
$`\mathbf{b}=\left(b_{0},b_{1},b_{2},\ldots\right)` is defined to be the FPS
$`\left(c_{0},c_{1},c_{2},\ldots\right)`, where
$$`c_{n} =\sum_{i=0}^{n}a_{i}b_{n-i}
=\sum_{\substack{\left(i,j\right)\in\mathbb{N}^{2};\\i+j=n}}a_{i}b_{j}
=a_{0}b_{n}+a_{1}b_{n-1}+a_{2}b_{n-2}+\cdots+a_{n}b_{0}`
for each $`n\in\mathbb{N}`.
This product is denoted by $`\mathbf{a}\cdot\mathbf{b}` or just by
$`\mathbf{ab}`.

*(e)* For each $`a\in K`, we define $`\underline{a}` to be the FPS
$`\left(a,0,0,0,\ldots\right)`. An FPS of the form $`\underline{a}` for some
$`a\in K`, that is, an FPS
$`\left(a_{0},a_{1},a_{2},\ldots\right)` satisfying
$`a_{1}=a_{2}=a_{3}=\cdots=0`, is said to be _constant_.

*(f)* The set of all FPSs in $`1` indeterminate over $`K` is denoted
$`K\left[\left[x\right]\right]`.
:::

```tex "def.fps.ops" (slot := statement)
\begin{definition}
\label{def.fps.ops}
\lean{AlgebraicCombinatorics.FPS.coeff_add_fps, AlgebraicCombinatorics.FPS.coeff_sub_fps, AlgebraicCombinatorics.FPS.coeff_smul_fps, AlgebraicCombinatorics.FPS.coeff_mul_fps, AlgebraicCombinatorics.FPS.coeff_C_fps}
\leantarget
\leanok
\textbf{(a)} The \emph{sum} of two FPSs $\mathbf{a}=\left(
a_{0},a_{1},a_{2},\ldots\right)$ and $\mathbf{b}=\left(b_{0},b_{1}%
,b_{2},\ldots\right)$ is defined to be the FPS%
\[
\left(a_{0}+b_{0},\ \ a_{1}+b_{1},\ \ a_{2}+b_{2},\ \ \ldots\right).
\]
It is denoted by $\mathbf{a}+\mathbf{b}$. \medskip

\textbf{(b)} The \emph{difference} of two FPSs $\mathbf{a}=\left(a_{0}%
,a_{1},a_{2},\ldots\right)$ and $\mathbf{b}=\left(b_{0},b_{1},b_{2}%
,\ldots\right)$ is defined to be the FPS%
\[
\left(a_{0}-b_{0},\ \ a_{1}-b_{1},\ \ a_{2}-b_{2},\ \ \ldots\right).
\]
It is denoted by $\mathbf{a}-\mathbf{b}$. \medskip

\textbf{(c)} If $\lambda\in K$ and if $\mathbf{a}=\left(a_{0},a_{1}%
,a_{2},\ldots\right)$ is an FPS, then we define an FPS
\[
\lambda\mathbf{a}:=\left(\lambda a_{0},\lambda a_{1},\lambda a_{2}%
,\ldots\right).
\]

\textbf{(d)} The \emph{product} of two FPSs $\mathbf{a}=\left(a_{0}%
,a_{1},a_{2},\ldots\right)$ and $\mathbf{b}=\left(b_{0},b_{1},b_{2}%
,\ldots\right)$ is defined to be the FPS $\left(c_{0},c_{1},c_{2}%
,\ldots\right)$, where
\begin{align*}
c_{n} & =\sum_{i=0}^{n}a_{i}b_{n-i}=\sum_{\substack{\left(i,j\right)
\in\mathbb{N}^{2};\\i+j=n}}a_{i}b_{j}\\
& =a_{0}b_{n}+a_{1}b_{n-1}+a_{2}b_{n-2}+\cdots+a_{n}b_{0}%
\ \ \ \ \ \ \ \ \ \ \text{for each }n\in\mathbb{N}.
\end{align*}
This product is denoted by $\mathbf{a}\cdot\mathbf{b}$ or just by
$\mathbf{ab}$. \medskip

\textbf{(e)} For each $a\in K$, we define $\underline{a}$ to be the FPS
$\left(a,0,0,0,\ldots\right)$. An FPS of the form $\underline{a}$ for some
$a\in K$ (that is, an FPS $\left(a_{0},a_{1},a_{2},\ldots\right)$
satisfying $a_{1}=a_{2}=a_{3}=\cdots=0$) is said to be \emph{constant}.
\medskip

\textbf{(f)} The set of all FPSs (in $1$ indeterminate over $K$) is denoted
$K\left[\left[x\right]\right]$.
\end{definition}
```

:::definition "def.fps.coeff" (parent := "fps_definition_basic") (lean := "AlgebraicCombinatorics.FPS.fps_coeff_mk")
If $`n\in\mathbb{N}`, and if
$`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right) \in K\left[\left[x\right]\right]`
is an FPS, then we define an element
$`\left[x^{n}\right]\mathbf{a}\in K` by
$$`\left[x^{n}\right]\mathbf{a}:=a_{n}.`
This is called the _coefficient of_ $`x^{n}` _in_ $`\mathbf{a}`, or the
$`n`-th coefficient of $`\mathbf{a}`, or the $`x^{n}`-coefficient of
$`\mathbf{a}`.
:::

```tex "def.fps.coeff" (slot := statement)
\begin{definition}
\label{def.fps.coeff}
\lean{AlgebraicCombinatorics.FPS.fps_coeff_mk}
\leantarget
\leanok
If $n\in\mathbb{N}$, and if $\mathbf{a}=\left(
a_{0},a_{1},a_{2},\ldots\right) \in K\left[\left[x\right]\right]$ is
an FPS, then we define an element $\left[x^{n}\right]\mathbf{a}\in K$ by
\[
\left[x^{n}\right]\mathbf{a}:=a_{n}.
\]
This is called the \emph{coefficient of }$x^{n}$\emph{ in }$\mathbf{a}$, or
the $n$\emph{-th coefficient} of $\mathbf{a}$, or the $x^{n}$%
\emph{-coefficient} of $\mathbf{a}$.
\end{definition}
```
