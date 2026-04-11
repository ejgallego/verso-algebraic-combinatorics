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

:::group "fps_ring_structure"
The ring and module structure on formal power series.
:::

:::theorem "thm.fps.ring" (parent := "fps_ring_structure") (lean := "AlgebraicCombinatorics.FPS.smul_mul_fps, AlgebraicCombinatorics.FPS.smul_eq_C_mul_fps")
*(a)* The set $`K\left[\left[x\right]\right]` is a commutative ring, with its
operations $`+`, $`-`, and $`\cdot` defined above. Its zero and its unity are
the FPSs
$`\underline{0}=\left(0,0,0,\ldots\right)` and
$`\underline{1}=\left(1,0,0,0,\ldots\right)`. Concretely, this means that:

1. _Commutativity of addition:_ We have
   $`\mathbf{a}+\mathbf{b}=\mathbf{b}+\mathbf{a}` for all
   $`\mathbf{a},\mathbf{b}\in K\left[\left[x\right]\right]`.
2. _Associativity of addition:_ We have
   $`\mathbf{a}+\left(\mathbf{b}+\mathbf{c}\right)
   =\left(\mathbf{a}+\mathbf{b}\right)+\mathbf{c}` for all
   $`\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]`.
3. _Neutrality of zero:_ We have
   $`\mathbf{a}+\underline{0}=\underline{0}+\mathbf{a}=\mathbf{a}` for all
   $`\mathbf{a}\in K\left[\left[x\right]\right]`.
4. _Subtraction undoes addition:_ Let
   $`\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]`. We
   have $`\mathbf{a}+\mathbf{b}=\mathbf{c}` if and only if
   $`\mathbf{a}=\mathbf{c}-\mathbf{b}`.
5. _Commutativity of multiplication:_ We have
   $`\mathbf{ab}=\mathbf{ba}` for all
   $`\mathbf{a},\mathbf{b}\in K\left[\left[x\right]\right]`.
6. _Associativity of multiplication:_ We have
   $`\mathbf{a}\left(\mathbf{bc}\right)=\left(\mathbf{ab}\right)\mathbf{c}`
   for all
   $`\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]`.
7. _Distributivity:_ We have
   $$`\mathbf{a}\left(\mathbf{b}+\mathbf{c}\right)=\mathbf{ab}+\mathbf{ac}
   \qquad \text{and} \qquad
   \left(\mathbf{a}+\mathbf{b}\right)\mathbf{c}=\mathbf{ac}+\mathbf{bc}`
   for all
   $`\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]`.
8. _Neutrality of one:_ We have
   $`\mathbf{a}\cdot\underline{1}=\underline{1}\cdot\mathbf{a}=\mathbf{a}` for
   all $`\mathbf{a}\in K\left[\left[x\right]\right]`.
9. _Annihilation:_ We have
   $`\mathbf{a}\cdot\underline{0}=\underline{0}\cdot\mathbf{a}=\underline{0}`
   for all $`\mathbf{a}\in K\left[\left[x\right]\right]`.

*(b)* Furthermore, $`K\left[\left[x\right]\right]` is a $`K`-module, with its
scaling being the map that sends each
$`\left(\lambda,\mathbf{a}\right) \in K\times K\left[\left[x\right]\right]`
to the FPS $`\lambda\mathbf{a}` defined above. Its zero vector is
$`\underline{0}`. Concretely, this means that:

10. _Associativity of scaling:_ We have
    $`\lambda\left(\mu\mathbf{a}\right)=\left(\lambda\mu\right)\mathbf{a}` for
    all $`\lambda,\mu\in K` and
    $`\mathbf{a}\in K\left[\left[x\right]\right]`.
11. _Left distributivity:_ We have
    $`\lambda\left(\mathbf{a}+\mathbf{b}\right)=\lambda\mathbf{a}+\lambda\mathbf{b}`
    for all $`\lambda\in K` and
    $`\mathbf{a},\mathbf{b}\in K\left[\left[x\right]\right]`.
12. _Right distributivity:_ We have
    $`\left(\lambda+\mu\right)\mathbf{a}=\lambda\mathbf{a}+\mu\mathbf{a}` for
    all $`\lambda,\mu\in K` and
    $`\mathbf{a}\in K\left[\left[x\right]\right]`.
13. _Neutrality of one:_ We have $`1\mathbf{a}=\mathbf{a}` for all
    $`\mathbf{a}\in K\left[\left[x\right]\right]`.
14. _Left annihilation:_ We have $`0\mathbf{a}=\underline{0}` for all
    $`\mathbf{a}\in K\left[\left[x\right]\right]`.
15. _Right annihilation:_ We have
    $`\lambda\underline{0}=\underline{0}` for all $`\lambda\in K`.

*(c)* We have
$`\lambda\left(\mathbf{a}\cdot\mathbf{b}\right)
=\left(\lambda\mathbf{a}\right)\cdot\mathbf{b}
=\mathbf{a}\cdot\left(\lambda\mathbf{b}\right)` for all
$`\lambda\in K` and
$`\mathbf{a},\mathbf{b}\in K\left[\left[x\right]\right]`.

*(d)* Finally, we have
$`\lambda\mathbf{a}=\underline{\lambda}\cdot\mathbf{a}` for all
$`\lambda\in K` and
$`\mathbf{a}\in K\left[\left[x\right]\right]`.
:::

```tex "thm.fps.ring" (slot := statement)
\begin{theorem}
\label{thm.fps.ring}
\lean{AlgebraicCombinatorics.FPS.smul_mul_fps, AlgebraicCombinatorics.FPS.smul_eq_C_mul_fps}
\leantarget
\leanok
\textbf{(a)} The set $K\left[\left[x\right]\right]$
is a commutative ring (with its operations $+$, $-$ and $\cdot$ defined in
Definition \ref{def.fps.ops}). Its zero and its unity are the FPSs
$\underline{0}=\left(0,0,0,\ldots\right)$ and $\underline{1}=\left(
1,0,0,0,\ldots\right)$. This means, concretely, that the following facts hold:

\begin{enumerate}
\item \emph{Commutativity of addition:} We have $\mathbf{a}+\mathbf{b}%
=\mathbf{b}+\mathbf{a}$ for all $\mathbf{a},\mathbf{b}\in K\left[\left[
x\right]\right]$.

\item \emph{Associativity of addition:} We have $\mathbf{a}+\left(
\mathbf{b}+\mathbf{c}\right) =\left(\mathbf{a}+\mathbf{b}\right)
+\mathbf{c}$ for all $\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[
x\right]\right]$.

\item \emph{Neutrality of zero:} We have $\mathbf{a}+\underline{0}%
=\underline{0}+\mathbf{a}=\mathbf{a}$ for all $\mathbf{a}\in K\left[\left[
x\right]\right]$.

\item \emph{Subtraction undoes addition:} Let $\mathbf{a},\mathbf{b}%
,\mathbf{c}\in K\left[\left[x\right]\right]$. We have $\mathbf{a}%
+\mathbf{b}=\mathbf{c}$ if and only if $\mathbf{a}=\mathbf{c}-\mathbf{b}$.

\item \emph{Commutativity of multiplication:} We have $\mathbf{ab}%
=\mathbf{ba}$ for all $\mathbf{a},\mathbf{b}\in K\left[\left[x\right]
\right]$.

\item \emph{Associativity of multiplication:} We have $\mathbf{a}\left(
\mathbf{bc}\right) =\left(\mathbf{ab}\right)\mathbf{c}$ for all
$\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]$.

\item \emph{Distributivity:} We have%
\[
\mathbf{a}\left(\mathbf{b}+\mathbf{c}\right) =\mathbf{ab}+\mathbf{ac}%
\ \ \ \ \ \ \ \ \ \ \text{and}\ \ \ \ \ \ \ \ \ \ \left(\mathbf{a}%
+\mathbf{b}\right)\mathbf{c}=\mathbf{ac}+\mathbf{bc}%
\]
for all $\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]
\right]$.

\item \emph{Neutrality of one:} We have $\mathbf{a}\cdot\underline{1}%
=\underline{1}\cdot\mathbf{a}=\mathbf{a}$ for all $\mathbf{a}\in K\left[
\left[x\right]\right]$.

\item \emph{Annihilation:} We have $\mathbf{a}\cdot\underline{0}%
=\underline{0}\cdot\mathbf{a}=\underline{0}$ for all $\mathbf{a}\in K\left[
\left[x\right]\right]$.
\end{enumerate}

\textbf{(b)} Furthermore, $K\left[\left[x\right]\right]$ is a
$K$-module (with its scaling being the map that sends each $\left(
\lambda,\mathbf{a}\right) \in K\times K\left[\left[x\right]\right]$
to the FPS $\lambda\mathbf{a}$ defined in Definition \ref{def.fps.ops}
\textbf{(c)}). Its zero vector is $\underline{0}$. Concretely, this means that:

\begin{enumerate}
\item[10.] \emph{Associativity of scaling:} We have $\lambda\left(
\mu\mathbf{a}\right)  =\left(  \lambda\mu\right)  \mathbf{a}$ for all
$\lambda,\mu\in K$ and $\mathbf{a}\in K\left[\left[x\right]\right]$.

\item[11.] \emph{Left distributivity:} We have $\lambda\left(  \mathbf{a}%
+\mathbf{b}\right)  =\lambda\mathbf{a}+\lambda\mathbf{b}$ for all $\lambda\in
K$ and $\mathbf{a},\mathbf{b}\in K\left[\left[x\right]\right]$.

\item[12.] \emph{Right distributivity:} We have $\left(  \lambda+\mu\right)
\mathbf{a}=\lambda\mathbf{a}+\mu\mathbf{a}$ for all $\lambda,\mu\in K$ and
$\mathbf{a}\in K\left[\left[x\right]\right]$.

\item[13.] \emph{Neutrality of one:} We have $1\mathbf{a}=\mathbf{a}$ for all
$\mathbf{a}\in K\left[\left[x\right]\right]$.

\item[14.] \emph{Left annihilation:} We have $0\mathbf{a}=\underline{0}$ for
all $\mathbf{a}\in K\left[\left[x\right]\right]$.

\item[15.] \emph{Right annihilation:} We have $\lambda\underline{0}%
=\underline{0}$ for all $\lambda\in K$.
\end{enumerate}

\textbf{(c)} We have $\lambda\left(\mathbf{a}\cdot\mathbf{b}\right)
=\left(\lambda\mathbf{a}\right)\cdot\mathbf{b}=\mathbf{a}\cdot\left(
\lambda\mathbf{b}\right)$ for all $\lambda\in K$ and $\mathbf{a}%
,\mathbf{b}\in K\left[\left[x\right]\right]$. \medskip

\textbf{(d)} Finally, we have $\lambda\mathbf{a}=\underline{\lambda}%
\cdot\mathbf{a}$ for all $\lambda\in K$ and $\mathbf{a}\in K\left[\left[
x\right]\right]$.
\end{theorem}
```

:::proof "thm.fps.ring"
Most parts of the theorem are straightforward to verify. Let us check the
associativity of multiplication.

Let $`\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]`.
We must prove that
$`\mathbf{a}\left(\mathbf{bc}\right) = \left(\mathbf{ab}\right)\mathbf{c}`.
Let $`n\in\mathbb{N}`. Consider the two equalities
$$`\left[x^{n}\right]\left(\left(\mathbf{ab}\right)\mathbf{c}\right)
=\sum_{j=0}^{n}\underbrace{\left[x^{n-j}\right]\left(\mathbf{ab}\right)}_{=\sum_{i=0}^{n-j}\left[x^{i}\right]\mathbf{a}\cdot\left[x^{n-j-i}\right]\mathbf{b}}\cdot\left[x^{j}\right]\mathbf{c}
=\sum_{j=0}^{n}\ \ \sum_{i=0}^{n-j}\left[x^{i}\right]\mathbf{a}\cdot\left[x^{n-j-i}\right]\mathbf{b}\cdot\left[x^{j}\right]\mathbf{c}`
and
$$`\left[x^{n}\right]\left(\mathbf{a}\left(\mathbf{bc}\right)\right)
=\sum_{i=0}^{n}\left[x^{i}\right]\mathbf{a}\cdot\underbrace{\left[x^{n-i}\right]\left(\mathbf{bc}\right)}_{=\sum_{j=0}^{n-i}\left[x^{n-i-j}\right]\mathbf{b}\cdot\left[x^{j}\right]\mathbf{c}}
=\sum_{i=0}^{n}\ \ \sum_{j=0}^{n-i}\left[x^{i}\right]\mathbf{a}\cdot\left[x^{n-i-j}\right]\mathbf{b}\cdot\left[x^{j}\right]\mathbf{c}.`

The right hand sides are equal since
$$`\sum_{j=0}^{n}\ \ \sum_{i=0}^{n-j}
=\sum_{\substack{\left(i,j\right)\in\mathbb{N}^{2};\\i+j\leq n}}
=\sum_{i=0}^{n}\ \ \sum_{j=0}^{n-i}`
and $`n-j-i=n-i-j`.
Thus
$`\left[x^{n}\right]\left(\left(\mathbf{ab}\right)\mathbf{c}\right)
=\left[x^{n}\right]\left(\mathbf{a}\left(\mathbf{bc}\right)\right)` for each
$`n\in\mathbb{N}`, which entails
$`\left(\mathbf{ab}\right)\mathbf{c}=\mathbf{a}\left(\mathbf{bc}\right)`.

The remaining claims of the theorem follow by similar, and easier,
coefficient-wise verifications. In the Lean formalization, the commutative ring
and module structures are provided by Mathlib's existing instances on power
series.
:::

```tex "thm.fps.ring" (slot := proof)
\begin{proof}
Most parts of Theorem \ref{thm.fps.ring}
are straightforward to verify. Let us check the associativity of multiplication.

Let $\mathbf{a},\mathbf{b},\mathbf{c}\in K\left[\left[x\right]\right]$.
We must prove that $\mathbf{a}\left(\mathbf{bc}\right) = \left(
\mathbf{ab}\right)\mathbf{c}$. Let $n\in\mathbb{N}$. Consider the two
equalities
\begin{align*}
\left[x^{n}\right]\left(\left(\mathbf{ab}\right)\mathbf{c}\right)
& =\sum_{j=0}^{n}\underbrace{\left[x^{n-j}\right]\left(\mathbf{ab}%
\right)}_{=\sum_{i=0}^{n-j}\left[x^{i}\right]\mathbf{a}%
\cdot\left[x^{n-j-i}\right]\mathbf{b}}\cdot\left[x^{j}\right]\mathbf{c}\\
& =\sum_{j=0}^{n}\ \ \sum_{i=0}^{n-j}\left[x^{i}\right]\mathbf{a}%
\cdot\left[x^{n-j-i}\right]\mathbf{b}\cdot\left[x^{j}\right]\mathbf{c}%
\end{align*}
and
\begin{align*}
\left[x^{n}\right]\left(\mathbf{a}\left(\mathbf{bc}\right)\right)
& =\sum_{i=0}^{n}\left[x^{i}\right]\mathbf{a}\cdot\underbrace{\left[
x^{n-i}\right]\left(\mathbf{bc}\right)}_{=\sum_{j=0}%
^{n-i}\left[x^{n-i-j}\right]\mathbf{b}\cdot\left[x^{j}\right]
\mathbf{c}}\\
& =\sum_{i=0}^{n}\ \ \sum_{j=0}^{n-i}\left[x^{i}\right]\mathbf{a}%
\cdot\left[x^{n-i-j}\right]\mathbf{b}\cdot\left[x^{j}\right]
\mathbf{c}.
\end{align*}
The right hand sides are equal since
\[
\sum_{j=0}^{n}\ \ \sum_{i=0}^{n-j}=\sum_{\substack{\left(i,j\right)
\in\mathbb{N}^{2};\\i+j\leq n}}=\sum_{i=0}^{n}\ \ \sum_{j=0}^{n-i}
\]
and $n-j-i=n-i-j$. Thus $\left[x^{n}\right]\left(\left(\mathbf{ab}\right)\mathbf{c}\right)
=\left[x^{n}\right]\left(\mathbf{a}\left(\mathbf{bc}\right)\right)$
for each $n\in\mathbb{N}$, which entails $\left(\mathbf{ab}\right)
\mathbf{c}=\mathbf{a}\left(\mathbf{bc}\right)$.

The remaining claims of Theorem \ref{thm.fps.ring} follow by similar
(and easier) coefficient-wise verifications.
In the Lean formalization, the commutative ring and module structures are
provided by Mathlib's existing instances on power series.
\end{proof}
```
