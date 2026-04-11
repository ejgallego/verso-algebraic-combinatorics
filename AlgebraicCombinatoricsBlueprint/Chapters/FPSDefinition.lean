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

:::lemma_ "lem.fps.coeff_mul_range" (parent := "fps_ring_structure") (lean := "AlgebraicCombinatorics.FPS.coeff_mul_fps'")
The product formula can be written as a sum over a range:
$$`\left[x^{n}\right]\left(\mathbf{ab}\right)
= \sum_{i=0}^{n}\left[x^{i}\right]\mathbf{a}\cdot\left[x^{n-i}\right]\mathbf{b}.`
:::

```tex "lem.fps.coeff_mul_range" (slot := statement)
\begin{lemma}
\label{lem.fps.coeff_mul_range}
\lean{AlgebraicCombinatorics.FPS.coeff_mul_fps'}
\leanhelper
\leanok
The product formula can be written as a sum over a range:
\[
\left[x^{n}\right]\left(\mathbf{ab}\right)
= \sum_{i=0}^{n}\left[x^{i}\right]\mathbf{a}\cdot\left[x^{n-i}\right]\mathbf{b}.
\]
\end{lemma}
```

:::proof "lem.fps.coeff_mul_range"
This rewrites the antidiagonal sum from the product definition as a range sum
using the bijection $`(i, n-i) \leftrightarrow i \in \{0, \ldots, n\}`.
:::

```tex "lem.fps.coeff_mul_range" (slot := proof)
\begin{proof}
This rewrites the antidiagonal sum from Definition~\ref{def.fps.ops}
as a range sum using the bijection $(i, n-i) \leftrightarrow i \in \{0, \ldots, n\}$.
\end{proof}
```

:::group "fps_summable_families"
Essentially finite sums and summable families of formal power series.
:::

```tex
\subsection{Essentially finite sums and summable families}
```

:::definition "def.infsum.essfin" (parent := "fps_summable_families") (lean := "AlgebraicCombinatorics.FPS.EssentiallyFinite")
*(a)* A family $`\left(a_{i}\right)_{i\in I}\in K^{I}` of elements of
$`K` is said to be _essentially finite_ if all but finitely many
$`i\in I` satisfy $`a_{i}=0`, in other words, if the set
$`\left\{i\in I\mid a_{i}\neq0\right\}` is finite.

*(b)* Let $`\left(a_{i}\right)_{i\in I}\in K^{I}` be an essentially finite
family of elements of $`K`. Then the infinite sum $`\sum_{i\in I}a_{i}` is
defined to equal the finite sum
$`\sum_{\substack{i\in I;\\a_{i}\neq0}}a_{i}`. Such an infinite sum is said
to be _essentially finite_.
:::

```tex "def.infsum.essfin" (slot := statement)
\begin{definition}
\label{def.infsum.essfin}
\lean{AlgebraicCombinatorics.FPS.EssentiallyFinite}
\leantarget
\leanok
\textbf{(a)} A family $\left(a_{i}\right)_{i\in I}\in K^{I}$
of elements of $K$ is said to be \emph{essentially finite} if all
but finitely many $i\in I$ satisfy $a_{i}=0$ (in other words, if the set
$\left\{i\in I\ \mid\ a_{i}\neq0\right\}$ is finite). \medskip

\textbf{(b)} Let $\left(a_{i}\right)_{i\in I}\in K^{I}$ be an essentially
finite family of elements of $K$. Then, the infinite sum $\sum_{i\in I}a_{i}$
is defined to equal the finite sum $\sum_{\substack{i\in I;\\a_{i}\neq0}}a_{i}$.
Such an infinite sum is said to be \emph{essentially finite}.
\end{definition}
```

:::definition "def.fps.summable" (parent := "fps_summable_families") (lean := "AlgebraicCombinatorics.FPS.SummableFPS, AlgebraicCombinatorics.FPS.summableFPSSum")
A possibly infinite family $`\left(\mathbf{a}_{i}\right)_{i\in I}` of FPSs is
said to be _summable_, or _entrywise essentially finite_, if
$$`\text{for each }n\in\mathbb{N}\text{, all but finitely many }i\in I\text{ satisfy }\left[x^{n}\right]\mathbf{a}_{i}=0.`
In this case, the sum $`\sum_{i\in I}\mathbf{a}_{i}` is defined to be the FPS
with
$$`\left[x^{n}\right]\left(\sum_{i\in I}\mathbf{a}_{i}\right)
=\underbrace{\sum_{i\in I}\left[x^{n}\right]\mathbf{a}_{i}}_{\substack{\text{an essentially}\\\text{finite sum}}}
\qquad \text{for all }n\in\mathbb{N}.`
:::

```tex "def.fps.summable" (slot := statement)
\begin{definition}
\label{def.fps.summable}
\lean{AlgebraicCombinatorics.FPS.SummableFPS, AlgebraicCombinatorics.FPS.summableFPSSum}
\leantarget
\leanok
A (possibly infinite) family $\left(\mathbf{a}_{i}\right)_{i\in I}$
of FPSs is said to be \emph{summable} (or \emph{entrywise essentially finite})
if
\[
\text{for each }n\in\mathbb{N}\text{, all but finitely many }i\in I\text{
satisfy }\left[x^{n}\right]\mathbf{a}_{i}=0.
\]
In this case, the sum $\sum_{i\in I}\mathbf{a}_{i}$ is defined to be the FPS
with
\[
\left[x^{n}\right]\left(\sum_{i\in I}\mathbf{a}_{i}\right)
=\underbrace{\sum_{i\in I}\left[x^{n}\right]\mathbf{a}_{i}}%
_{\substack{\text{an essentially}\\\text{finite sum}}}
\ \ \ \ \ \ \ \ \ \ \text{for all }n\in\mathbb{N}\text{.}
\]
\end{definition}
```

:::theorem "prop.fps.summable.sub" (parent := "fps_summable_families") (lean := "AlgebraicCombinatorics.FPS.summableFPS_subfamily")
Let $`\left(\mathbf{a}_{i}\right)_{i\in I}` be a summable family of FPSs.
Then any subfamily of $`\left(\mathbf{a}_{i}\right)_{i\in I}` is summable as
well.
:::

```tex "prop.fps.summable.sub" (slot := statement)
\begin{proposition}
\label{prop.fps.summable.sub}
\lean{AlgebraicCombinatorics.FPS.summableFPS_subfamily}
\leantarget
\leanok
Let $\left(\mathbf{a}_{i}\right)_{i\in I}$ be
a summable family of FPSs. Then, any subfamily of $\left(\mathbf{a}%
_{i}\right)_{i\in I}$ is summable as well.
\end{proposition}
```

:::proof "prop.fps.summable.sub"
Let $`J` be a subset of $`I`. We must prove that the subfamily
$`\left(\mathbf{a}_{i}\right)_{i\in J}` is summable.

Let $`n\in\mathbb{N}`. Then all but finitely many $`i\in I` satisfy
$`\left[x^{n}\right]\mathbf{a}_{i}=0`, since
$`\left(\mathbf{a}_{i}\right)_{i\in I}` is summable. Hence all but finitely
many $`i\in J` satisfy $`\left[x^{n}\right]\mathbf{a}_{i}=0`, since $`J` is a
subset of $`I`. Since we have proved this for each $`n\in\mathbb{N}`, we
conclude that the family $`\left(\mathbf{a}_{i}\right)_{i\in J}` is summable.
:::

```tex "prop.fps.summable.sub" (slot := proof)
\begin{proof}
\leanok
Let $J$ be a subset of $I$.
We must prove that the subfamily $\left(\mathbf{a}_{i}\right)_{i\in J}$ is summable.

Let $n\in\mathbb{N}$. Then, all but finitely many $i\in I$ satisfy $\left[
x^{n}\right]\mathbf{a}_{i}=0$ (since the family $\left(\mathbf{a}%
_{i}\right)_{i\in I}$ is summable). Hence, all but finitely many $i\in J$
satisfy $\left[x^{n}\right]\mathbf{a}_{i}=0$ (since $J$ is a subset of
$I$). Since we have proved this for each $n\in\mathbb{N}$, we thus conclude
that the family $\left(\mathbf{a}_{i}\right)_{i\in J}$ is summable.
\end{proof}
```

:::theorem "prop.fps.summable-sums-rule" (parent := "fps_summable_families") (lean := "AlgebraicCombinatorics.FPS.summableFPS_fubini")
Sums of summable families of FPSs satisfy the usual rules for sums, such as
the breaking-apart rule
$`\sum_{i\in S}a_{s}=\sum_{i\in X}a_{s}+\sum_{i\in Y}a_{s}` when a set
$`S` is the union of two disjoint sets $`X` and $`Y`.
Again, the only caveat is about interchange of summation signs: the equality
$$`\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}
=\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}`
holds when the family
$`\left(\mathbf{a}_{i,j}\right)_{\left(i,j\right)\in I\times J}` is summable,
that is, when for each $`n\in\mathbb{N}`, all but finitely many pairs
$`\left(i,j\right)\in I\times J` satisfy
$`\left[x^{n}\right]\mathbf{a}_{i,j}=0`; it does not generally hold if we
merely assume that the sums
$`\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}` and
$`\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}` are summable.
:::

```tex "prop.fps.summable-sums-rule" (slot := statement)
\begin{proposition}
\label{prop.fps.summable-sums-rule}
\lean{AlgebraicCombinatorics.FPS.summableFPS_fubini}
\leantarget
\leanok
Sums of summable families of FPSs satisfy
the usual rules for sums (such as the breaking-apart rule $\sum_{i\in S}%
a_{s}=\sum_{i\in X}a_{s}+\sum_{i\in Y}a_{s}$ when a set $S$ is the union of
two disjoint sets $X$ and $Y$). See \cite[Proposition 7.2.11]{19s} for
details. Again, the only \textbf{caveat} is about interchange
of summation signs: The equality
\[
\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}=\sum_{j\in J}\ \ \sum_{i\in
I}\mathbf{a}_{i,j}
\]
holds when the family $\left(\mathbf{a}_{i,j}\right)_{\left(i,j\right)
\in I\times J}$ is summable (i.e., when for each $n\in\mathbb{N}$, all but
finitely many \textbf{pairs} $\left(i,j\right) \in I\times J$ satisfy
$\left[x^{n}\right]\mathbf{a}_{i,j}=0$); it does not generally hold if we
merely assume that the sums $\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}$
and $\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}$ are summable.
\end{proposition}
```

:::proof "prop.fps.summable-sums-rule"
The proof is tedious, because there are many rules to check, but fairly
straightforward: always focus on a single coefficient, and then reduce the
infinite sums to finite sums. For example, consider the discrete Fubini rule,
which says that
$$`\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}
=\sum_{\left(i,j\right)\in I\times J}\mathbf{a}_{i,j}
=\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}`
whenever $`\left(\mathbf{a}_{i,j}\right)_{\left(i,j\right)\in I\times J}` is
a summable family of FPSs.

To prove this rule, fix such a summable family. It is easy to see that the
families $`\left(\mathbf{a}_{i,j}\right)_{j\in J}` for all $`i\in I` are
summable as well, as are the families
$`\left(\mathbf{a}_{i,j}\right)_{i\in I}` for all $`j\in J`, and the families
$`\left(\sum_{j\in J}\mathbf{a}_{i,j}\right)_{i\in I}` and
$`\left(\sum_{i\in I}\mathbf{a}_{i,j}\right)_{j\in J}`.

To verify the Fubini identity, it suffices to check that
$$`\left[x^{n}\right]\left(\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}\right)
=\left[x^{n}\right]\left(\sum_{\left(i,j\right)\in I\times J}\mathbf{a}_{i,j}\right)
=\left[x^{n}\right]\left(\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}\right)`
for each $`n\in\mathbb{N}`.

Fix $`n\in\mathbb{N}`. Then
$`\left[x^{n}\right]\left(\mathbf{a}_{i,j}\right)=0` for all but finitely many
$`\left(i,j\right)\in I\times J`, since the family is summable. Thus the set
of all pairs $`\left(i,j\right)\in I\times J` satisfying
$`\left[x^{n}\right]\left(\mathbf{a}_{i,j}\right)\neq0` is finite. Hence the
set $`I^{\prime}` of first entries and the set $`J^{\prime}` of second entries
of all these pairs are also finite. The three sums reduce to finite sums over
$`I^{\prime}\times J^{\prime}`, which are equal by the usual Fubini rule for
finite sums.
:::

```tex "prop.fps.summable-sums-rule" (slot := proof)
\begin{proof}
The proof is tedious
(as there are many rules to check), but fairly straightforward (the idea is
always to focus on a single coefficient, and then to reduce the infinite sums
to finite sums). For example, consider the discrete Fubini
rule, which says that
\[
\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}_{i,j}=\sum_{\left(i,j\right) \in
I\times J}\mathbf{a}_{i,j}=\sum_{j\in J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}
\]
whenever $\left(\mathbf{a}_{i,j}\right)_{\left(i,j\right) \in I\times
J}$ is a summable family of FPSs. In order to prove this rule, we fix a
summable family $\left(\mathbf{a}_{i,j}\right)_{\left(i,j\right) \in
I\times J}$ of FPSs. It is easy to see that the families $\left(
\mathbf{a}_{i,j}\right)_{j\in J}$ for all $i\in I$ are summable as well, as
are the families $\left(\mathbf{a}_{i,j}\right)_{i\in I}$ for all $j\in
J$, and the families $\left(\sum_{j\in J}\mathbf{a}_{i,j}\right)_{i\in I}$
and $\left(\sum_{i\in I}\mathbf{a}_{i,j}\right)_{j\in J}$.

To verify the Fubini identity, it suffices to check that
\[
\left[x^{n}\right]\left(\sum_{i\in I}\ \ \sum_{j\in J}\mathbf{a}%
_{i,j}\right) = \left[x^{n}\right]\left(\sum_{\left(i,j\right) \in
I\times J}\mathbf{a}_{i,j}\right) = \left[x^{n}\right]\left(\sum_{j\in
J}\ \ \sum_{i\in I}\mathbf{a}_{i,j}\right)
\]
for each $n\in\mathbb{N}$. Fix $n\in\mathbb{N}$; then, we have $\left[
x^{n}\right]\left(\mathbf{a}_{i,j}\right) =0$ for all but finitely many
$\left(i,j\right) \in I\times J$ (since the family $\left(\mathbf{a}%
_{i,j}\right)_{\left(i,j\right) \in I\times J}$ is summable). That is,
the set of all pairs $\left(i,j\right) \in I\times J$ satisfying $\left[
x^{n}\right]\left(\mathbf{a}_{i,j}\right) \neq0$ is finite. Hence, the
set $I^{\prime}$ of the first entries and the set $J^{\prime}$ of the second entries
of all these pairs are also finite. The three sums reduce to finite sums over
$I^{\prime}\times J^{\prime}$, which are equal by the usual Fubini rule for finite sums.
See \cite[proof of Proposition 7.2.11]{19s} for more details.
\end{proof}
```


:::group "fps_x_powers"
The indeterminate x and its powers.
:::

```tex
\subsection{The indeterminate $x$ and powers}
```

:::definition "def.fps.x" (parent := "fps_x_powers") (lean := "AlgebraicCombinatorics.FPS.X_coeff_one, AlgebraicCombinatorics.FPS.X_coeff_ne_one")
Let $`x` denote the FPS $`\left(0,1,0,0,0,\ldots\right)`.
In other words, let $`x` denote the FPS with
$`\left[x^{1}\right]x=1` and $`\left[x^{i}\right]x=0` for all $`i\neq1`.
:::

```tex "def.fps.x" (slot := statement)
\begin{definition}
\label{def.fps.x}
\lean{AlgebraicCombinatorics.FPS.X_coeff_one, AlgebraicCombinatorics.FPS.X_coeff_ne_one}
\leantarget
\leanok
Let $x$ denote the FPS $\left(0,1,0,0,0,\ldots\right)$.
In other words, let $x$ denote the FPS with $\left[x^{1}\right]x=1$ and
$\left[x^{i}\right]x=0$ for all $i\neq1$.
\end{definition}
```

:::lemma_ "lem.fps.xa" (parent := "fps_x_powers") (lean := "AlgebraicCombinatorics.FPS.X_mul_shift, AlgebraicCombinatorics.FPS.X_mul_coeff_zero, AlgebraicCombinatorics.FPS.coeff_X_mul")
Let $`\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)` be an FPS.
Then
$`x\cdot\mathbf{a}=\left(0,a_{0},a_{1},a_{2},\ldots\right)`.
:::

```tex "lem.fps.xa" (slot := statement)
\begin{lemma}
\label{lem.fps.xa}
\lean{AlgebraicCombinatorics.FPS.X_mul_shift, AlgebraicCombinatorics.FPS.X_mul_coeff_zero, AlgebraicCombinatorics.FPS.coeff_X_mul}
\leantarget
\leanok
Let $\mathbf{a}=\left(a_{0},a_{1},a_{2},\ldots\right)$
be an FPS. Then, $x\cdot\mathbf{a}=\left(0,a_{0},a_{1},a_{2},\ldots\right)$.
\end{lemma}
```

:::proof "lem.fps.xa"
If $`n` is a positive integer, then
$$`\left[x^{n}\right]\left(x\cdot\mathbf{a}\right)
=\sum_{i=0}^{n}\left[x^{i}\right]x\cdot a_{n-i}
=\underbrace{\left[x^{0}\right]x}_{=0}\cdot a_{n}
+\underbrace{\left[x^{1}\right]x}_{=1}\cdot a_{n-1}
+\sum_{i=2}^{n}\underbrace{\left[x^{i}\right]x}_{=0}\cdot a_{n-i}
=a_{n-1}.`

A similar argument for $`n=0` yields
$`\left[x^{0}\right]\left(x\cdot\mathbf{a}\right)=0`.
Thus, for each $`n\in\mathbb{N}`,
$$`\left[x^{n}\right]\left(x\cdot\mathbf{a}\right)=
\begin{cases}
a_{n-1}, & \text{if }n>0;\\
0, & \text{if }n=0.
\end{cases}`
In other words,
$`x\cdot\mathbf{a}=\left(0,a_{0},a_{1},a_{2},\ldots\right)`.
:::

```tex "lem.fps.xa" (slot := proof)
\begin{proof}
\leanok
If $n$ is a positive integer, then
\begin{align*}
\left[x^{n}\right]\left(x\cdot\mathbf{a}\right) & =\sum_{i=0}%
^{n}\left[x^{i}\right]x\cdot a_{n-i}\\
& =\underbrace{\left[x^{0}\right]x}_{=0}\cdot\,a_{n-0}+\underbrace{\left[x^{1}\right]x}%
_{=1}\cdot\,a_{n-1}+\sum_{i=2}^{n}\underbrace{\left[x^{i}\right]
x}_{\substack{=0\\\text{(since }i\geq2>1\text{)}}}\cdot\,a_{n-i}\\
& =a_{n-1}.
\end{align*}
A similar argument for $n=0$ yields $\left[x^{0}\right]\left(x\cdot\mathbf{a}\right)=0$.
Thus, for each $n\in\mathbb{N}$,
\[
\left[x^{n}\right]\left(x\cdot\mathbf{a}\right) =
\begin{cases}
a_{n-1}, & \text{if }n>0;\\
0, & \text{if }n=0.
\end{cases}
\]
In other words, $x\cdot\mathbf{a}=\left(0,a_{0},a_{1},a_{2},\ldots\right)$.
\end{proof}
```

:::theorem "prop.fps.xk" (parent := "fps_x_powers") (lean := "AlgebraicCombinatorics.FPS.X_pow_coeff")
We have
$$`x^{k}=\left(\underbrace{0,0,\ldots,0}_{k\text{ times}},1,0,0,0,\ldots\right)
\qquad\text{for each }k\in\mathbb{N}.`
:::

```tex "prop.fps.xk" (slot := statement)
\begin{proposition}
\label{prop.fps.xk}
\lean{AlgebraicCombinatorics.FPS.X_pow_coeff}
\leantarget
\leanok
We have
\[
x^{k}=\left(\underbrace{0,0,\ldots,0}_{k\text{ times}},1,0,0,0,\ldots
\right) \ \ \ \ \ \ \ \ \ \ \text{for each }k\in\mathbb{N}.
\]
\end{proposition}
```

:::proof "prop.fps.xk"
We induct on $`k`.

_Induction base:_ We have
$`x^{0}=\underline{1}=\left(1,0,0,0,0,\ldots\right)
=\left(\underbrace{0,0,\ldots,0}_{0\text{ times}},1,0,0,0,\ldots\right)`.

_Induction step:_ Let $`m\in\mathbb{N}` and assume the proposition holds for
$`k=m`. Then
$`x^{m}=\left(\underbrace{0,0,\ldots,0}_{m\text{ times}},1,0,0,0,\ldots\right)`.
Applying the previous lemma to $`\mathbf{a}=x^{m}` yields
$$`x\cdot x^{m}
=\left(0,\underbrace{0,0,\ldots,0}_{m\text{ times}},1,0,0,0,\ldots\right)
=\left(\underbrace{0,0,\ldots,0}_{m+1\text{ times}},1,0,0,0,\ldots\right).`
Since $`x\cdot x^{m}=x^{m+1}`, this completes the induction step.
:::

```tex "prop.fps.xk" (slot := proof)
\begin{proof}
We induct on $k$.

\textit{Induction base:} We have $x^{0}=\underline{1}=\left(1,0,0,0,0,\ldots
\right) = \left(\underbrace{0,0,\ldots,0}_{0\text{ times}},1,0,0,0,\ldots
\right)$.

\textit{Induction step:} Let $m\in\mathbb{N}$. Assume that Proposition
\ref{prop.fps.xk} holds for $k=m$. We have $x^{m}=\left(\underbrace{0,0,\ldots,0}_{m\text{ times}%
},1,0,0,0,\ldots\right)$. Thus, Lemma \ref{lem.fps.xa} (applied to $\mathbf{a}=x^{m}$) yields
\[
x\cdot x^{m}=\left(0,\underbrace{0,0,\ldots,0}_{m\text{ times}%
},1,0,0,0,\ldots\right) = \left(\underbrace{0,0,\ldots,0}_{m+1\text{ times}%
},1,0,0,0,\ldots\right).
\]
Since $x\cdot x^{m}=x^{m+1}$, this completes the induction step.
\end{proof}
```

:::corollary "cor.fps.sumakxk" (parent := "fps_x_powers") (lean := "AlgebraicCombinatorics.FPS.fps_eq_tsum_coeff, AlgebraicCombinatorics.FPS.summableFPS_monomial_family")
Any FPS
$`\left(a_{0},a_{1},a_{2},\ldots\right)\in K\left[\left[x\right]\right]`
satisfies
$$`\left(a_{0},a_{1},a_{2},\ldots\right)
= a_{0}+a_{1}x+a_{2}x^{2}+a_{3}x^{3}+\cdots
= \sum_{n\in\mathbb{N}}a_{n}x^{n}.`
In particular, the right hand side is well-defined, that is, the family
$`\left(a_{n}x^{n}\right)_{n\in\mathbb{N}}` is summable.
:::

```tex "cor.fps.sumakxk" (slot := statement)
\begin{corollary}
\label{cor.fps.sumakxk}
\lean{AlgebraicCombinatorics.FPS.fps_eq_tsum_coeff, AlgebraicCombinatorics.FPS.summableFPS_monomial_family}
\leantarget
\leanok
Any FPS $\left(a_{0},a_{1},a_{2},\ldots\right) \in
K\left[\left[x\right]\right]$ satisfies
\[
\left(a_{0},a_{1},a_{2},\ldots\right) = a_{0}+a_{1}x+a_{2}x^{2}+a_{3}%
x^{3}+\cdots = \sum_{n\in\mathbb{N}}a_{n}x^{n}.
\]
In particular, the right hand side here is well-defined, i.e., the family
$\left(a_{n}x^{n}\right)_{n\in\mathbb{N}}$ is summable.
\end{corollary}
```

:::proof "cor.fps.sumakxk"
By the previous proposition, we have
$$`a_{0}+a_{1}x+a_{2}x^{2}+a_{3}x^{3}+\cdots
= a_{0}\left(1,0,0,0,\ldots\right)
+ a_{1}\left(0,1,0,0,\ldots\right)
+ a_{2}\left(0,0,1,0,\ldots\right)
+ a_{3}\left(0,0,0,1,\ldots\right)+\cdots`
and hence
$$`= \left(a_{0},0,0,0,\ldots\right)
+ \left(0,a_{1},0,0,\ldots\right)
+ \left(0,0,a_{2},0,\ldots\right)
+ \left(0,0,0,a_{3},\ldots\right)+\cdots
=\left(a_{0},a_{1},a_{2},a_{3},\ldots\right).`
:::

```tex "cor.fps.sumakxk" (slot := proof)
\begin{proof}
By Proposition \ref{prop.fps.xk}, we have
\begin{align*}
& a_{0}+a_{1}x+a_{2}x^{2}+a_{3}x^{3}+\cdots\\
& =\ \ \ \ a_{0}\left(1,0,0,0,\ldots\right) \\
& \ \ \ \ +a_{1}\left(0,1,0,0,\ldots\right) \\
& \ \ \ \ +a_{2}\left(0,0,1,0,\ldots\right) \\
& \ \ \ \ +a_{3}\left(0,0,0,1,\ldots\right) \\
& \ \ \ \ +\cdots\\
& =\ \ \ \ \left(a_{0},0,0,0,\ldots\right) \\
& \ \ \ \ +\left(0,a_{1},0,0,\ldots\right) \\
& \ \ \ \ +\left(0,0,a_{2},0,\ldots\right) \\
& \ \ \ \ +\left(0,0,0,a_{3},\ldots\right) \\
& \ \ \ \ +\cdots\\
& =\left(a_{0},a_{1},a_{2},a_{3},\ldots\right).
\end{align*}
\end{proof}
```

:::group "fps_helper_lemmas"
Helper lemmas from the formalization.
:::

```tex
\subsection{Helper lemmas from the formalization}
```

:::lemma_ "lem.fps.summable.add" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.summableFPS_add")
If $`\left(\mathbf{a}_{i}\right)_{i\in I}` and
$`\left(\mathbf{b}_{i}\right)_{i\in I}` are summable families of FPSs, then
so is $`\left(\mathbf{a}_{i}+\mathbf{b}_{i}\right)_{i\in I}`.
:::

```tex "lem.fps.summable.add" (slot := statement)
\begin{lemma}
\label{lem.fps.summable.add}
\lean{AlgebraicCombinatorics.FPS.summableFPS_add}
\leanhelper
\leanok
If $\left(\mathbf{a}_{i}\right)_{i\in I}$ and $\left(\mathbf{b}_{i}\right)_{i\in I}$
are summable families of FPSs, then so is $\left(\mathbf{a}_{i}+\mathbf{b}_{i}\right)_{i\in I}$.
\end{lemma}
```

:::proof "lem.fps.summable.add"
For each $`n\in\mathbb{N}`,
$`\{i \mid \left[x^{n}\right](\mathbf{a}_{i}+\mathbf{b}_{i})\neq 0\}
\subseteq \{i \mid \left[x^{n}\right]\mathbf{a}_{i}\neq 0\} \cup
\{i \mid \left[x^{n}\right]\mathbf{b}_{i}\neq 0\}`, and the union of two
finite sets is finite.
:::

```tex "lem.fps.summable.add" (slot := proof)
\begin{proof}
\leanok
For each $n\in\mathbb{N}$,
$\{i \mid \left[x^{n}\right](\mathbf{a}_{i}+\mathbf{b}_{i})\neq 0\}
\subseteq \{i \mid \left[x^{n}\right]\mathbf{a}_{i}\neq 0\} \cup
\{i \mid \left[x^{n}\right]\mathbf{b}_{i}\neq 0\}$, and the union of two
finite sets is finite.
\end{proof}
```

:::lemma_ "lem.fps.summable.neg" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.summableFPS_neg")
If $`\left(\mathbf{a}_{i}\right)_{i\in I}` is a summable family of FPSs, then
so is $`\left(-\mathbf{a}_{i}\right)_{i\in I}`.
:::

```tex "lem.fps.summable.neg" (slot := statement)
\begin{lemma}
\label{lem.fps.summable.neg}
\lean{AlgebraicCombinatorics.FPS.summableFPS_neg}
\leanhelper
\leanok
If $\left(\mathbf{a}_{i}\right)_{i\in I}$ is a summable family of FPSs,
then so is $\left(-\mathbf{a}_{i}\right)_{i\in I}$.
\end{lemma}
```

:::proof "lem.fps.summable.neg"
For each $`n`,
$`\left[x^{n}\right](-\mathbf{a}_{i})=-\left[x^{n}\right]\mathbf{a}_{i}`, so
$`\{i \mid \left[x^{n}\right](-\mathbf{a}_{i})\neq 0\}
= \{i \mid \left[x^{n}\right]\mathbf{a}_{i}\neq 0\}`.
:::

```tex "lem.fps.summable.neg" (slot := proof)
\begin{proof}
\leanok
For each $n$, $\left[x^{n}\right](-\mathbf{a}_{i})=-\left[x^{n}\right]\mathbf{a}_{i}$,
so $\{i \mid \left[x^{n}\right](-\mathbf{a}_{i})\neq 0\} = \{i \mid \left[x^{n}\right]\mathbf{a}_{i}\neq 0\}$.
\end{proof}
```

:::lemma_ "lem.fps.essfin.add" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essentiallyFinite_add")
The sum of two essentially finite families is essentially finite.
:::

```tex "lem.fps.essfin.add" (slot := statement)
\begin{lemma}
\label{lem.fps.essfin.add}
\lean{AlgebraicCombinatorics.FPS.essentiallyFinite_add}
\leanhelper
\leanok
The sum of two essentially finite families is essentially finite.
\end{lemma}
```

:::proof "lem.fps.essfin.add"
$`\{i \mid a_{i}+b_{i}\neq 0\}\subseteq \{i \mid a_{i}\neq 0\}\cup\{i \mid b_{i}\neq 0\}`,
and the union of two finite sets is finite.
:::

```tex "lem.fps.essfin.add" (slot := proof)
\begin{proof}
\leanok
$\{i \mid a_{i}+b_{i}\neq 0\}\subseteq \{i \mid a_{i}\neq 0\}\cup\{i \mid b_{i}\neq 0\}$,
and the union of two finite sets is finite.
\end{proof}
```

:::lemma_ "lem.fps.essfin.neg" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essentiallyFinite_neg")
The negation of an essentially finite family is essentially finite.
:::

```tex "lem.fps.essfin.neg" (slot := statement)
\begin{lemma}
\label{lem.fps.essfin.neg}
\lean{AlgebraicCombinatorics.FPS.essentiallyFinite_neg}
\leanhelper
\leanok
The negation of an essentially finite family is essentially finite.
\end{lemma}
```

:::proof "lem.fps.essfin.neg"
$`\{i \mid -a_{i}\neq 0\}=\{i \mid a_{i}\neq 0\}`.
:::

```tex "lem.fps.essfin.neg" (slot := proof)
\begin{proof}
\leanok
$\{i \mid -a_{i}\neq 0\}=\{i \mid a_{i}\neq 0\}$.
\end{proof}
```

:::lemma_ "lem.fps.essfin.sub" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essentiallyFinite_sub")
The difference of two essentially finite families is essentially finite.
:::

```tex "lem.fps.essfin.sub" (slot := statement)
\begin{lemma}
\label{lem.fps.essfin.sub}
\lean{AlgebraicCombinatorics.FPS.essentiallyFinite_sub}
\leanhelper
\leanok
The difference of two essentially finite families is essentially finite.
\end{lemma}
```

:::proof "lem.fps.essfin.sub"
Write $`a_i - b_i = a_i + (-b_i)` and apply the previous essentially finite
addition and negation lemmas.
:::

```tex "lem.fps.essfin.sub" (slot := proof)
\begin{proof}
\leanok
Write $a_i - b_i = a_i + (-b_i)$ and apply
Lemma~\ref{lem.fps.essfin.add} and Lemma~\ref{lem.fps.essfin.neg}.
\end{proof}
```

:::definition "def.fps.essFinSum" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essFinSum")
For an essentially finite family $`(a_i)_{i\in I}`, the _essentially finite
sum_ $`\sum_{i\in I} a_i` is defined as $`\sum_{i\in S} a_i` where
$`S = \{i\in I \mid a_i \neq 0\}`.
:::

```tex "def.fps.essFinSum" (slot := statement)
\begin{definition}
\label{def.fps.essFinSum}
\lean{AlgebraicCombinatorics.FPS.essFinSum}
\leanhelper
\leanok
For an essentially finite family $(a_i)_{i\in I}$, the \emph{essentially finite sum}
$\sum_{i\in I} a_i$ is defined as $\sum_{i\in S} a_i$ where $S = \{i\in I \mid a_i \neq 0\}$.
\end{definition}
```

:::lemma_ "lem.fps.essFinSum.add" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essFinSum_add")
The essentially finite sum distributes over addition: if
$`(a_i)_{i\in I}` and $`(b_i)_{i\in I}` are essentially finite families, then
$`\sum_{i\in I}(a_i + b_i) = \sum_{i\in I} a_i + \sum_{i\in I} b_i`.
:::

```tex "lem.fps.essFinSum.add" (slot := statement)
\begin{lemma}
\label{lem.fps.essFinSum.add}
\lean{AlgebraicCombinatorics.FPS.essFinSum_add}
\leanhelper
\leanok
The essentially finite sum distributes over addition:
if $(a_i)_{i\in I}$ and $(b_i)_{i\in I}$ are essentially finite families,
then $\sum_{i\in I}(a_i + b_i) = \sum_{i\in I} a_i + \sum_{i\in I} b_i$.
\end{lemma}
```

:::proof "lem.fps.essFinSum.add"
All three sums can be computed over the finite set
$`S = \{i \mid a_i\neq 0\}\cup\{i \mid b_i\neq 0\}`, so this reduces to the
finite sum identity
$`\sum_{i\in S}(a_i+b_i)=\sum_{i\in S}a_i+\sum_{i\in S}b_i`.
:::

```tex "lem.fps.essFinSum.add" (slot := proof)
\begin{proof}
\leanok
All three sums can be computed over the finite set
$S = \{i \mid a_i\neq 0\}\cup\{i \mid b_i\neq 0\}$,
so this reduces to the finite sum identity $\sum_{i\in S}(a_i+b_i)=\sum_{i\in S}a_i+\sum_{i\in S}b_i$.
\end{proof}
```

:::lemma_ "lem.fps.essFinSum.smul" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.essFinSum_smul")
For a scalar $`c\in K` and an essentially finite family
$`(a_i)_{i\in I}`,
$`\sum_{i\in I} c\, a_i = c\cdot\sum_{i\in I} a_i`.
:::

```tex "lem.fps.essFinSum.smul" (slot := statement)
\begin{lemma}
\label{lem.fps.essFinSum.smul}
\lean{AlgebraicCombinatorics.FPS.essFinSum_smul}
\leanhelper
\leanok
For a scalar $c\in K$ and an essentially finite family $(a_i)_{i\in I}$,
$\sum_{i\in I} c\, a_i = c\cdot\sum_{i\in I} a_i$.
\end{lemma}
```

:::proof "lem.fps.essFinSum.smul"
The support of $`(c\,a_i)` is contained in the support of $`(a_i)`, so this
reduces to the finite identity
$`\sum_{i\in S}c\,a_i = c\sum_{i\in S}a_i`.
:::

```tex "lem.fps.essFinSum.smul" (slot := proof)
\begin{proof}
\leanok
The support of $(c\,a_i)$ is contained in the support of $(a_i)$,
so this reduces to the finite identity $\sum_{i\in S}c\,a_i = c\sum_{i\in S}a_i$.
\end{proof}
```

:::lemma_ "lem.fps.summable.sub" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.summableFPS_sub")
If $`\left(\mathbf{a}_{i}\right)_{i\in I}` and
$`\left(\mathbf{b}_{i}\right)_{i\in I}` are summable families of FPSs, then so
is $`\left(\mathbf{a}_{i}-\mathbf{b}_{i}\right)_{i\in I}`.
:::

```tex "lem.fps.summable.sub" (slot := statement)
\begin{lemma}
\label{lem.fps.summable.sub}
\lean{AlgebraicCombinatorics.FPS.summableFPS_sub}
\leanhelper
\leanok
If $\left(\mathbf{a}_{i}\right)_{i\in I}$ and $\left(\mathbf{b}_{i}\right)_{i\in I}$
are summable families of FPSs, then so is $\left(\mathbf{a}_{i}-\mathbf{b}_{i}\right)_{i\in I}$.
\end{lemma}
```

:::proof "lem.fps.summable.sub"
Write $`\mathbf{a}_i - \mathbf{b}_i = \mathbf{a}_i + (-\mathbf{b}_i)` and
apply the previous summable-add and summable-neg lemmas.
:::

```tex "lem.fps.summable.sub" (slot := proof)
\begin{proof}
\leanok
Write $\mathbf{a}_i - \mathbf{b}_i = \mathbf{a}_i + (-\mathbf{b}_i)$
and apply Lemma~\ref{lem.fps.summable.add} and Lemma~\ref{lem.fps.summable.neg}.
\end{proof}
```

:::lemma_ "lem.fps.summable.of_essfin" (parent := "fps_helper_lemmas") (lean := "AlgebraicCombinatorics.FPS.summableFPS_of_essentiallyFinite")
If $`(\mathbf{a}_i)_{i\in I}` is a family of FPSs such that
$`\{i \mid \mathbf{a}_i \neq 0\}` is finite, then the family is summable.
:::

```tex "lem.fps.summable.of_essfin" (slot := statement)
\begin{lemma}
\label{lem.fps.summable.of_essfin}
\lean{AlgebraicCombinatorics.FPS.summableFPS_of_essentiallyFinite}
\leanhelper
\leanok
If $(\mathbf{a}_i)_{i\in I}$ is a family of FPSs such that
$\{i \mid \mathbf{a}_i \neq 0\}$ is finite, then the family is summable.
\end{lemma}
```

:::proof "lem.fps.summable.of_essfin"
For each $`n`,
$`\{i \mid [x^n]\mathbf{a}_i \neq 0\} \subseteq \{i \mid \mathbf{a}_i \neq 0\}`,
which is finite by hypothesis.
:::

```tex "lem.fps.summable.of_essfin" (slot := proof)
\begin{proof}
\leanok
For each $n$, $\{i \mid [x^n]\mathbf{a}_i \neq 0\} \subseteq \{i \mid \mathbf{a}_i \neq 0\}$,
which is finite by hypothesis.
\end{proof}
```

:::group "fps_generating_functions"
Generating functions of sequences.
:::

```tex
\subsection{Generating functions}
```

:::definition "def.fps.gf" (parent := "fps_generating_functions") (lean := "AlgebraicCombinatorics.FPS.generatingFunction")
The ordinary generating function of a sequence
$`(a_0, a_1, a_2, \ldots)` is the FPS
$`(a_0, a_1, a_2, \ldots) = \sum_{n\geq 0} a_n x^n`.
:::

```tex "def.fps.gf" (slot := statement)
\begin{definition}
\label{def.fps.gf}
\lean{AlgebraicCombinatorics.FPS.generatingFunction}
\leanhelper
\leanok
The \emph{(ordinary) generating function} of a sequence $(a_0, a_1, a_2, \ldots)$
is the FPS $(a_0, a_1, a_2, \ldots) = \sum_{n\geq 0} a_n x^n$.
\end{definition}
```

:::lemma_ "lem.fps.gf.coeff" (parent := "fps_generating_functions") (lean := "AlgebraicCombinatorics.FPS.generatingFunction_coeff")
The $`n`-th coefficient of the generating function of a sequence
$`(a_n)` is $`a_n`.
:::

```tex "lem.fps.gf.coeff" (slot := statement)
\begin{lemma}
\label{lem.fps.gf.coeff}
\lean{AlgebraicCombinatorics.FPS.generatingFunction_coeff}
\leanhelper
\leanok
The $n$-th coefficient of the generating function of a sequence $(a_n)$ is $a_n$.
\end{lemma}
```

:::proof "lem.fps.gf.coeff"
Immediate from the definitions.
:::

```tex "lem.fps.gf.coeff" (slot := proof)
\begin{proof}
\leanok
Immediate from the definitions.
\end{proof}
```

:::group "fps_vandermonde"
The Chu--Vandermonde identity.
:::

```tex
\subsection{The Chu--Vandermonde identity}
```

:::theorem "prop.binom.vandermonde.NN" (parent := "fps_vandermonde") (lean := "AlgebraicCombinatorics.FPS.vandermonde_nat")
Let $`a,b\in\mathbb{N}`, and let $`n\in\mathbb{N}`. Then
$$`\binom{a+b}{n}=\sum_{k=0}^{n}\binom{a}{k}\binom{b}{n-k}.`
:::

```tex "prop.binom.vandermonde.NN" (slot := statement)
\begin{proposition}
\label{prop.binom.vandermonde.NN}
\lean{AlgebraicCombinatorics.FPS.vandermonde_nat}
\leantarget
\leanok
Let $a,b\in\mathbb{N}$, and let
$n\in\mathbb{N}$. Then,
\[
\binom{a+b}{n}=\sum_{k=0}^{n}\binom{a}{k}\binom{b}{n-k}.
\]
\end{proposition}
```

:::proof "prop.binom.vandermonde.NN"
Multiply out the identity
$`\left(1+x\right)^{a+b}=\left(1+x\right)^{a}\left(1+x\right)^{b}` using the
binomial formula and compare the coefficient of $`x^{n}` on both sides.
The left side gives $`\binom{a+b}{n}`, and the right side gives
$`\sum_{k=0}^{n}\binom{a}{k}\binom{b}{n-k}` by the product formula for FPSs.
:::

```tex "prop.binom.vandermonde.NN" (slot := proof)
\begin{proof}
Multiply out the identity $\left(1+x\right)^{a+b}=\left(1+x\right)^{a}\left(1+x\right)^{b}$
using the binomial formula and compare the coefficient of $x^{n}$ on both sides.
The left side gives $\binom{a+b}{n}$, and the right side gives
$\sum_{k=0}^{n}\binom{a}{k}\binom{b}{n-k}$ by the product formula for FPSs.
\end{proof}
```
