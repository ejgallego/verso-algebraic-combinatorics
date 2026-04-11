import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.CommutativeRings

open Verso.Genre
open Verso.Genre.Manual
open Informal
open AlgebraicCombinatorics

#doc (Manual) "Commutative Rings and Modules" =>

:::group "commutative_rings_definition"
The reminder on commutative rings and the basic notation used in later FPS
sections.
:::

```tex
\section{Commutative rings and modules}

\subsection{Reminder: Commutative rings}
```

:::definition "def.alg.commring" (parent := "commutative_rings_definition") (lean := "AlgebraicCombinatorics.FPS.commRing_add_comm, AlgebraicCombinatorics.FPS.commRing_add_assoc, AlgebraicCombinatorics.FPS.commRing_add_zero, AlgebraicCombinatorics.FPS.commRing_sub_iff_add, AlgebraicCombinatorics.FPS.commRing_mul_comm, AlgebraicCombinatorics.FPS.commRing_mul_assoc, AlgebraicCombinatorics.FPS.commRing_left_distrib, AlgebraicCombinatorics.FPS.commRing_mul_one, AlgebraicCombinatorics.FPS.commRing_mul_zero")
A _commutative ring_ means a set $`K` equipped with three maps
$`\oplus : K\times K\rightarrow K`, $`\ominus : K\times K\rightarrow K`, and
$`\odot : K\times K\rightarrow K`, and two elements $`\mathbf{0}\in K` and
$`\mathbf{1}\in K` satisfying the following axioms:

1. _Commutativity of addition:_ We have $`a\oplus b=b\oplus a` for all $`a,b\in K`.
2. _Associativity of addition:_ We have $`a\oplus\left(b\oplus c\right)=\left(a\oplus b\right)\oplus c` for all $`a,b,c\in K`.
3. _Neutrality of zero:_ We have $`a\oplus\mathbf{0}=\mathbf{0}\oplus a=a` for all $`a\in K`.
4. _Subtraction undoes addition:_ Let $`a,b,c\in K`. We have $`a\oplus b=c` if and only if $`a=c\ominus b`.
5. _Commutativity of multiplication:_ We have $`a\odot b=b\odot a` for all $`a,b\in K`.
6. _Associativity of multiplication:_ We have $`a\odot\left(b\odot c\right)=\left(a\odot b\right)\odot c` for all $`a,b,c\in K`.
7. _Distributivity:_ We have $`a\odot\left(b\oplus c\right)=\left(a\odot b\right)\oplus\left(a\odot c\right)` and $`\left(a\oplus b\right)\odot c=\left(a\odot c\right)\oplus\left(b\odot c\right)` for all $`a,b,c\in K`.
8. _Neutrality of one:_ We have $`a\odot\mathbf{1}=\mathbf{1}\odot a=a` for all $`a\in K`.
9. _Annihilation:_ We have $`a\odot\mathbf{0}=\mathbf{0}\odot a=\mathbf{0}` for all $`a\in K`.

The operations $`\oplus`, $`\ominus` and $`\odot` are called the _addition_,
the _subtraction_ and the _multiplication_ of the ring $`K`.
When confusion is unlikely, we will denote these three operations by
$`+`, $`-` and $`\cdot`, respectively, and we will abbreviate
$`a\odot b=a\cdot b` by $`ab`.

The elements $`\mathbf{0}` and $`\mathbf{1}` are called the _zero_ and the
_unity_ or the _one_ of the ring $`K`. We will simply call these elements
$`0` and $`1` when confusion with the corresponding numbers is unlikely.

We will use _PEMDAS conventions_ for the three operations $`\oplus`,
$`\ominus` and $`\odot`. These imply that $`\odot` has higher precedence than
$`\oplus` and $`\ominus`, while $`\oplus` and $`\ominus` are left-associative.
:::

```tex "def.alg.commring" (slot := statement)
\begin{definition}
\label{def.alg.commring}
\lean{AlgebraicCombinatorics.FPS.commRing_add_comm, AlgebraicCombinatorics.FPS.commRing_add_assoc, AlgebraicCombinatorics.FPS.commRing_add_zero, AlgebraicCombinatorics.FPS.commRing_sub_iff_add, AlgebraicCombinatorics.FPS.commRing_mul_comm, AlgebraicCombinatorics.FPS.commRing_mul_assoc, AlgebraicCombinatorics.FPS.commRing_left_distrib, AlgebraicCombinatorics.FPS.commRing_mul_one, AlgebraicCombinatorics.FPS.commRing_mul_zero}
\leantarget
\leanok
A \emph{commutative ring} means a set $K$ equipped
with three maps%
\begin{align*}
\oplus &  :K\times K\rightarrow K,\\
\ominus &  :K\times K\rightarrow K,\\
\odot &  :K\times K\rightarrow K
\end{align*}
and two elements $\mathbf{0}\in K$ and $\mathbf{1}\in K$ satisfying the
following axioms:

\begin{enumerate}
\item \emph{Commutativity of addition:} We have $a\oplus b=b\oplus a$ for all
$a,b\in K$.

\item \emph{Associativity of addition:} We have $a\oplus\left(  b\oplus
c\right)  =\left(  a\oplus b\right)  \oplus c$ for all $a,b,c\in K$.

\item \emph{Neutrality of zero:} We have $a\oplus\mathbf{0}=\mathbf{0}\oplus
a=a$ for all $a\in K$.

\item \emph{Subtraction undoes addition:} Let $a,b,c\in K$. We have $a\oplus
b=c$ if and only if $a=c\ominus b$.

\item \emph{Commutativity of multiplication:} We have $a\odot b=b\odot a$ for
all $a,b\in K$.

\item \emph{Associativity of multiplication:} We have $a\odot\left(  b\odot
c\right)  =\left(  a\odot b\right)  \odot c$ for all $a,b,c\in K$.

\item \emph{Distributivity:} We have%
\[
a\odot\left(  b\oplus c\right)  =\left(  a\odot b\right)  \oplus\left(  a\odot
c\right)  \ \ \ \ \ \ \ \ \ \ \text{and}\ \ \ \ \ \ \ \ \ \ \left(  a\oplus
b\right)  \odot c=\left(  a\odot c\right)  \oplus\left(  b\odot c\right)
\]
for all $a,b,c\in K$.

\item \emph{Neutrality of one:} We have $a\odot\mathbf{1}=\mathbf{1}\odot a=a$
for all $a\in K$.

\item \emph{Annihilation:} We have $a\odot\mathbf{0}=\mathbf{0}\odot
a=\mathbf{0}$ for all $a\in K$.
\end{enumerate}

The operations $\oplus$, $\ominus$ and $\odot$ are called the \emph{addition},
the \emph{subtraction} and the \emph{multiplication} of the ring $K$.
When confusion is unlikely,
we will denote these three operations $\oplus$, $\ominus$ and $\odot$ by $+$,
$-$ and $\cdot$, respectively, and we will abbreviate $a\odot b=a\cdot b$ by
$ab$.

The elements $\mathbf{0}$ and $\mathbf{1}$ are called the \emph{zero} and the
\emph{unity} (or the \emph{one}) of the ring $K$.
We will simply call these elements $0$ and $1$ when confusion with the
corresponding numbers is unlikely.

We will use \emph{PEMDAS conventions} for the three operations $\oplus$,
$\ominus$ and $\odot$. These imply that the operation $\odot$ has higher
precedence than $\oplus$ and $\ominus$, while the operations $\oplus$ and
$\ominus$ are left-associative.
\end{definition}
```

:::group "commutative_rings_standard_rules"
Standard rules in commutative rings.
:::

```tex
\subsection{Standard rules in commutative rings}
```

:::lemma_ "lem.commring.neg-add" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.neg_add_distrib")
Let $`K` be a commutative ring. For any $`a,b\in K`, we have
$`-\left(  a+b\right)  =\left(  -a\right)  +\left(  -b\right)`.
:::

```tex "lem.commring.neg-add" (slot := statement)
\begin{lemma}
\label{lem.commring.neg-add}
\lean{AlgebraicCombinatorics.FPS.neg_add_distrib}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a,b\in K$, we have
$-\left(  a+b\right)  =\left(  -a\right)  +\left(  -b\right)$.
\end{lemma}
```

:::proof "lem.commring.neg-add"
Standard ring theory.
:::

```tex "lem.commring.neg-add" (slot := proof)
\begin{proof}
\leanok
Standard ring theory.
\end{proof}
```

:::lemma_ "lem.commring.neg-neg" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.neg_neg_eq")
Let $`K` be a commutative ring. For any $`a\in K`, we have
$`-\left(  -a\right)  =a`.
:::

```tex "lem.commring.neg-neg" (slot := statement)
\begin{lemma}
\label{lem.commring.neg-neg}
\lean{AlgebraicCombinatorics.FPS.neg_neg_eq}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a\in K$, we have
$-\left(  -a\right)  =a$.
\end{lemma}
```

:::proof "lem.commring.neg-neg"
Standard ring theory.
:::

```tex "lem.commring.neg-neg" (slot := proof)
\begin{proof}
\leanok
Standard ring theory.
\end{proof}
```

:::lemma_ "lem.commring.add-zsmul" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.add_zsmul_distrib")
Let $`K` be a commutative ring. For any $`a\in K` and
$`n,m\in\mathbb{Z}`, we have
$`\left(  n+m\right)  a=na+ma`.
:::

```tex "lem.commring.add-zsmul" (slot := statement)
\begin{lemma}
\label{lem.commring.add-zsmul}
\lean{AlgebraicCombinatorics.FPS.add_zsmul_distrib}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a\in K$ and $n,m\in\mathbb{Z}$, we have
$\left(  n+m\right)  a=na+ma$.
\end{lemma}
```

:::proof "lem.commring.add-zsmul"
Standard ring theory.
:::

```tex "lem.commring.add-zsmul" (slot := proof)
\begin{proof}
\leanok
Standard ring theory.
\end{proof}
```

:::lemma_ "lem.commring.mul-zsmul" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.mul_zsmul_assoc")
Let $`K` be a commutative ring. For any $`a\in K` and
$`n,m\in\mathbb{Z}`, we have
$`\left(  nm\right)  a=n\left(  ma\right)`.
:::

```tex "lem.commring.mul-zsmul" (slot := statement)
\begin{lemma}
\label{lem.commring.mul-zsmul}
\lean{AlgebraicCombinatorics.FPS.mul_zsmul_assoc}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a\in K$ and $n,m\in\mathbb{Z}$, we have
$\left(  nm\right)  a=n\left(  ma\right)$.
\end{lemma}
```

:::proof "lem.commring.mul-zsmul"
Standard ring theory.
:::

```tex "lem.commring.mul-zsmul" (slot := proof)
\begin{proof}
\leanok
Standard ring theory.
\end{proof}
```

:::lemma_ "lem.commring.mul-sub" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.mul_sub_distrib")
Let $`K` be a commutative ring. For any $`a,b,c\in K`, we have
$`a\left(  b-c\right)  =\left(  ab\right)  -\left(  ac\right)`.
:::

```tex "lem.commring.mul-sub" (slot := statement)
\begin{lemma}
\label{lem.commring.mul-sub}
\lean{AlgebraicCombinatorics.FPS.mul_sub_distrib}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a,b,c\in K$, we have
$a\left(  b-c\right)  =\left(  ab\right)  -\left(  ac\right)$.
\end{lemma}
```

:::proof "lem.commring.mul-sub"
Standard ring theory.
:::

```tex "lem.commring.mul-sub" (slot := proof)
\begin{proof}
\leanok
Standard ring theory.
\end{proof}
```

:::lemma_ "lem.commring.mul-pow" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.mul_pow_eq")
Let $`K` be a commutative ring. For any $`a,b\in K` and
$`n\in\mathbb{N}`, we have
$`\left(  ab\right)  ^{n}=a^{n}b^{n}`.
:::

```tex "lem.commring.mul-pow" (slot := statement)
\begin{lemma}
\label{lem.commring.mul-pow}
\lean{AlgebraicCombinatorics.FPS.mul_pow_eq}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a,b\in K$ and $n\in\mathbb{N}$, we have
$\left(  ab\right)  ^{n}=a^{n}b^{n}$.
\end{lemma}
```

:::proof "lem.commring.mul-pow"
Standard ring theory (induction on $`n`).
:::

```tex "lem.commring.mul-pow" (slot := proof)
\begin{proof}
\leanok
Standard ring theory (induction on $n$).
\end{proof}
```

:::lemma_ "lem.commring.pow-add" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.pow_add_eq")
Let $`K` be a commutative ring. For any $`a\in K` and
$`n,m\in\mathbb{N}`, we have
$`a^{n+m}=a^{n}a^{m}`.
:::

```tex "lem.commring.pow-add" (slot := statement)
\begin{lemma}
\label{lem.commring.pow-add}
\lean{AlgebraicCombinatorics.FPS.pow_add_eq}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a\in K$ and $n,m\in\mathbb{N}$, we have
$a^{n+m}=a^{n}a^{m}$.
\end{lemma}
```

:::proof "lem.commring.pow-add"
Standard ring theory (induction on $`m`).
:::

```tex "lem.commring.pow-add" (slot := proof)
\begin{proof}
\leanok
Standard ring theory (induction on $m$).
\end{proof}
```

:::lemma_ "lem.commring.pow-mul" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.pow_mul_eq")
Let $`K` be a commutative ring. For any $`a\in K` and
$`n,m\in\mathbb{N}`, we have
$`a^{nm}=\left(  a^{n}\right)  ^{m}`.
:::

```tex "lem.commring.pow-mul" (slot := statement)
\begin{lemma}
\label{lem.commring.pow-mul}
\lean{AlgebraicCombinatorics.FPS.pow_mul_eq}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a\in K$ and $n,m\in\mathbb{N}$, we have
$a^{nm}=\left(  a^{n}\right)  ^{m}$.
\end{lemma}
```

:::proof "lem.commring.pow-mul"
Standard ring theory (induction on $`m`).
:::

```tex "lem.commring.pow-mul" (slot := proof)
\begin{proof}
\leanok
Standard ring theory (induction on $m$).
\end{proof}
```

:::theorem "thm.commring.binomial" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.binomial_theorem")
*Binomial Theorem.* Let $`K` be a commutative ring. For any $`a,b\in K` and
$`n\in\mathbb{N}`,
$$`(a+b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}.`
:::

```tex "thm.commring.binomial" (slot := statement)
\begin{theorem}
\label{thm.commring.binomial}
\lean{AlgebraicCombinatorics.FPS.binomial_theorem}
\leanhelper
\leanok
\textbf{(Binomial Theorem.)}
Let $K$ be a commutative ring. For any $a,b\in K$ and $n\in\mathbb{N}$,
\[
(a+b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}.
\]
\end{theorem}
```

:::proof "thm.commring.binomial"
Standard; this is the binomial theorem from Mathlib.
:::

```tex "thm.commring.binomial" (slot := proof)
\begin{proof}
Standard; this is the binomial theorem from Mathlib.
\end{proof}
```

:::lemma_ "lem.commring.binomial-sub" (parent := "commutative_rings_standard_rules") (lean := "AlgebraicCombinatorics.FPS.binomial_theorem_sub")
Let $`K` be a commutative ring. For any $`a,b\in K` and $`n\in\mathbb{N}`,
$$`(a-b)^n = \sum_{m=0}^{n} (-1)^{m+n} \cdot a^m \cdot b^{n-m} \cdot \binom{n}{m}.`
:::

```tex "lem.commring.binomial-sub" (slot := statement)
\begin{lemma}
\label{lem.commring.binomial-sub}
\lean{AlgebraicCombinatorics.FPS.binomial_theorem_sub}
\leanhelper
\leanok
Let $K$ be a commutative ring. For any $a,b\in K$ and $n\in\mathbb{N}$,
\[
(a-b)^n = \sum_{m=0}^{n} (-1)^{m+n} \cdot a^m \cdot b^{n-m} \cdot \binom{n}{m}.
\]
\end{lemma}
```

:::proof "lem.commring.binomial-sub"
Write $`a - b = a + (-b)` and apply the binomial theorem.
:::

```tex "lem.commring.binomial-sub" (slot := proof)
\begin{proof}
\leanok
Write $a - b = a + (-b)$ and apply Theorem~\ref{thm.commring.binomial}.
\end{proof}
```

:::group "commutative_rings_finite_sums_products"
Finite sums and products in commutative rings.
:::

```tex
\subsection{Finite sums and products}
```

:::lemma_ "lem.commring.sum-disjoint" (parent := "commutative_rings_finite_sums_products") (lean := "AlgebraicCombinatorics.FPS.sum_disjoint_union")
Let $`K` be a commutative ring. Let $`S` be a finite type, and let
$`X, Y` be disjoint finite subsets of $`S`. For any family
$`(a_s)_{s \in S}` of elements of $`K`, we have
$`\sum_{s\in X\cup Y}a_{s}=\sum_{s\in X}a_{s}+\sum_{s\in Y}a_{s}`.
:::

```tex "lem.commring.sum-disjoint" (slot := statement)
\begin{lemma}
\label{lem.commring.sum-disjoint}
\lean{AlgebraicCombinatorics.FPS.sum_disjoint_union}
\leanhelper
\leanok
Let $K$ be a commutative ring. Let $S$ be a finite type, and let
$X, Y$ be disjoint finite subsets of $S$. For any family $(a_s)_{s \in S}$
of elements of $K$, we have
$\sum_{s\in X\cup Y}a_{s}=\sum_{s\in X}a_{s}+\sum_{s\in Y}a_{s}$.
\end{lemma}
```

:::proof "lem.commring.sum-disjoint"
Standard.
:::

```tex "lem.commring.sum-disjoint" (slot := proof)
\begin{proof}
\leanok
Standard.
\end{proof}
```

:::lemma_ "lem.commring.sum-add" (parent := "commutative_rings_finite_sums_products") (lean := "AlgebraicCombinatorics.FPS.sum_add_distrib'")
Let $`K` be a commutative ring. Let $`T` be a finite set and
$`(a_s)_{s\in T}`, $`(b_s)_{s\in T}` be two families of elements of $`K`.
Then
$`\sum_{s\in T}\left(  a_{s}+b_{s}\right)  =\sum_{s\in T}a_{s}+\sum_{s\in T}b_{s}`.
:::

```tex "lem.commring.sum-add" (slot := statement)
\begin{lemma}
\label{lem.commring.sum-add}
\lean{AlgebraicCombinatorics.FPS.sum_add_distrib'}
\leanhelper
\leanok
Let $K$ be a commutative ring. Let $T$ be a finite set and $(a_s)_{s\in T}$, $(b_s)_{s\in T}$
be two families of elements of $K$. Then
$\sum_{s\in T}\left(  a_{s}+b_{s}\right)  =\sum_{s\in T}a_{s}+\sum_{s\in T}b_{s}$.
\end{lemma}
```

:::proof "lem.commring.sum-add"
Standard.
:::

```tex "lem.commring.sum-add" (slot := proof)
\begin{proof}
\leanok
Standard.
\end{proof}
```

:::lemma_ "lem.commring.sum-empty" (parent := "commutative_rings_finite_sums_products") (lean := "AlgebraicCombinatorics.FPS.sum_empty")
Let $`K` be a commutative ring. If $`S=\varnothing`, then
$`\sum_{s\in S}a_{s}=0`.
:::

```tex "lem.commring.sum-empty" (slot := statement)
\begin{lemma}
\label{lem.commring.sum-empty}
\lean{AlgebraicCombinatorics.FPS.sum_empty}
\leanhelper
\leanok
Let $K$ be a commutative ring. If $S=\varnothing$, then $\sum_{s\in S}a_{s}=0$.
\end{lemma}
```

:::proof "lem.commring.sum-empty"
By definition.
:::

```tex "lem.commring.sum-empty" (slot := proof)
\begin{proof}
\leanok
By definition.
\end{proof}
```

:::lemma_ "lem.commring.prod-empty" (parent := "commutative_rings_finite_sums_products") (lean := "AlgebraicCombinatorics.FPS.prod_empty")
Let $`K` be a commutative ring. If $`S=\varnothing`, then
$`\prod_{s\in S}a_{s}=1`.
:::

```tex "lem.commring.prod-empty" (slot := statement)
\begin{lemma}
\label{lem.commring.prod-empty}
\lean{AlgebraicCombinatorics.FPS.prod_empty}
\leanhelper
\leanok
Let $K$ be a commutative ring. If $S=\varnothing$, then $\prod_{s\in S}a_{s}=1$.
\end{lemma}
```

:::proof "lem.commring.prod-empty"
By definition.
:::

```tex "lem.commring.prod-empty" (slot := proof)
\begin{proof}
\leanok
By definition.
\end{proof}
```

:::group "commutative_rings_modules"
The definition of a K-module.
:::

```tex
\subsection{$K$-modules}
```

:::definition "def.alg.module" (parent := "commutative_rings_modules") (lean := "AlgebraicCombinatorics.FPS.module_add_comm, AlgebraicCombinatorics.FPS.module_add_assoc, AlgebraicCombinatorics.FPS.module_add_zero, AlgebraicCombinatorics.FPS.module_sub_iff_add, AlgebraicCombinatorics.FPS.module_smul_assoc, AlgebraicCombinatorics.FPS.module_smul_add, AlgebraicCombinatorics.FPS.module_add_smul, AlgebraicCombinatorics.FPS.module_one_smul, AlgebraicCombinatorics.FPS.module_zero_smul, AlgebraicCombinatorics.FPS.module_smul_zero")
Let $`K` be a commutative ring.

A $`K`-module means a set $`M` equipped with three maps
$$`\oplus : M\times M\rightarrow M, \qquad
\ominus : M\times M\rightarrow M, \qquad
\rightharpoonup : K\times M\rightarrow M`
and an element $`\overrightarrow{0}\in M` satisfying the following axioms:

1. _Commutativity of addition:_ We have $`a\oplus b=b\oplus a` for all
   $`a,b\in M`.
2. _Associativity of addition:_ We have
   $`a\oplus\left(  b\oplus c\right)  =\left(  a\oplus b\right)  \oplus c`
   for all $`a,b,c\in M`.
3. _Neutrality of zero:_ We have
   $`a\oplus\overrightarrow{0}=\overrightarrow{0}\oplus a=a` for all
   $`a\in M`.
4. _Subtraction undoes addition:_ Let $`a,b,c\in M`. We have
   $`a\oplus b=c` if and only if $`a=c\ominus b`.
5. _Associativity of scaling:_ We have
   $`u\rightharpoonup\left( v\rightharpoonup a\right)
   =\left( uv\right)\rightharpoonup a` for all $`u,v\in K` and $`a\in M`.
6. _Left distributivity:_ We have
   $`u\rightharpoonup\left(  a\oplus b\right)
   =\left(  u\rightharpoonup a\right)  \oplus\left(  u\rightharpoonup b\right)`
   for all $`u\in K` and $`a,b\in M`.
7. _Right distributivity:_ We have
   $`\left(  u+v\right)\rightharpoonup a
   =\left(  u\rightharpoonup a\right)  \oplus\left(  v\rightharpoonup a\right)`
   for all $`u,v\in K` and $`a\in M`.
8. _Neutrality of one:_ We have $`1\rightharpoonup a=a` for all $`a\in M`.
9. _Left annihilation:_ We have
   $`0\rightharpoonup a=\overrightarrow{0}` for all $`a\in M`.
10. _Right annihilation:_ We have
   $`u\rightharpoonup\overrightarrow{0}=\overrightarrow{0}` for all
   $`u\in K`.

The operations $`\oplus`, $`\ominus` and $`\rightharpoonup` are called the
_addition_, the _subtraction_ and the _scaling_, or the
$`K`-action, of the $`K`-module $`M`. When confusion is unlikely, we will
denote these three operations by $`+`, $`-` and $`\cdot`, respectively, and we
will abbreviate $`a\rightharpoonup b=a\cdot b` by $`ab`.

The element $`\overrightarrow{0}` is called the _zero_ or the _zero vector_ of
the $`K`-module $`M`. We will usually just call it $`0`.

When $`M` is a $`K`-module, the elements of $`M` are called _vectors_, while
the elements of $`K` are called _scalars_.

We will use _PEMDAS conventions_ for the three operations $`\oplus`,
$`\ominus` and $`\rightharpoonup`, with $`\rightharpoonup` having higher
precedence than $`\oplus` and $`\ominus`.
:::

```tex "def.alg.module" (slot := statement)
\begin{definition}
\label{def.alg.module}
\lean{AlgebraicCombinatorics.FPS.module_add_comm, AlgebraicCombinatorics.FPS.module_add_assoc, AlgebraicCombinatorics.FPS.module_add_zero, AlgebraicCombinatorics.FPS.module_sub_iff_add, AlgebraicCombinatorics.FPS.module_smul_assoc, AlgebraicCombinatorics.FPS.module_smul_add, AlgebraicCombinatorics.FPS.module_add_smul, AlgebraicCombinatorics.FPS.module_one_smul, AlgebraicCombinatorics.FPS.module_zero_smul, AlgebraicCombinatorics.FPS.module_smul_zero}
\leantarget
\leanok
Let $K$ be a commutative ring.

A $K$\emph{-module} means a set $M$ equipped with three maps
\begin{align*}
\oplus &  :M\times M\rightarrow M,\\
\ominus &  :M\times M\rightarrow M,\\
\rightharpoonup &  :K\times M\rightarrow M
\end{align*}
(notice that the third map has domain $K\times M$, not $M\times M$) and an
element $\overrightarrow{0}\in M$ satisfying the following axioms:

\begin{enumerate}
\item \emph{Commutativity of addition:} We have $a\oplus b=b\oplus a$ for all
$a,b\in M$.

\item \emph{Associativity of addition:} We have $a\oplus\left(  b\oplus
c\right)  =\left(  a\oplus b\right)  \oplus c$ for all $a,b,c\in M$.

\item \emph{Neutrality of zero:} We have $a\oplus\overrightarrow{0}%
=\overrightarrow{0}\oplus a=a$ for all $a\in M$.

\item \emph{Subtraction undoes addition:} Let $a,b,c\in M$. We have $a\oplus
b=c$ if and only if $a=c\ominus b$.

\item \emph{Associativity of scaling:} We have $u\rightharpoonup\left(
v\rightharpoonup a\right)  =\left(  uv\right)  \rightharpoonup a$ for all
$u,v\in K$ and $a\in M$.

\item \emph{Left distributivity:} We have $u\rightharpoonup\left(  a\oplus
b\right)  =\left(  u\rightharpoonup a\right)  \oplus\left(  u\rightharpoonup
b\right)  $ for all $u\in K$ and $a,b\in M$.

\item \emph{Right distributivity:} We have $\left(  u+v\right)
\rightharpoonup a=\left(  u\rightharpoonup a\right)  \oplus\left(
v\rightharpoonup a\right)  $ for all $u,v\in K$ and $a\in M$.

\item \emph{Neutrality of one:} We have $1\rightharpoonup a=a$ for all $a\in
M$.

\item \emph{Left annihilation:} We have $0\rightharpoonup a=\overrightarrow{0}%
$ for all $a\in M$.

\item \emph{Right annihilation:} We have $u\rightharpoonup\overrightarrow{0}%
=\overrightarrow{0}$ for all $u\in K$.
\end{enumerate}

The operations $\oplus$, $\ominus$ and $\rightharpoonup$ are called the
\emph{addition}, the \emph{subtraction} and the \emph{scaling} (or the
$K$\emph{-action}) of the $K$-module $M$. When confusion is unlikely, we will
denote these three operations $\oplus$, $\ominus$ and $\rightharpoonup$ by
$+$, $-$ and $\cdot$, respectively, and we will abbreviate $a\rightharpoonup
b=a\cdot b$ by $ab$.

The element $\overrightarrow{0}$ is called the \emph{zero} (or the \emph{zero
vector}) of the $K$-module $M$. We will usually just call it $0$.

When $M$ is a $K$-module, the elements of $M$ are called \emph{vectors}, while
the elements of $K$ are called \emph{scalars}.

We will use \emph{PEMDAS conventions} for the three operations $\oplus$,
$\ominus$ and $\rightharpoonup$, with the operation $\rightharpoonup$ having
higher precedence than $\oplus$ and $\ominus$.
\end{definition}
```

:::group "module_additive_inverses"
Additive inverses in modules.
:::

```tex
\subsection{Additive inverses in modules}
```

:::lemma_ "lem.module.neg-one-smul" (parent := "module_additive_inverses") (lean := "AlgebraicCombinatorics.FPS.module_neg_eq_neg_one_smul")
Let $`K` be a commutative ring and $`M` a $`K`-module. For any $`a\in M`, the
additive inverse of $`a` can be constructed as $`(-1)\cdot a`, that is,
$`-a = (-1)\cdot a`.
:::

```tex "lem.module.neg-one-smul" (slot := statement)
\begin{lemma}
\label{lem.module.neg-one-smul}
\lean{AlgebraicCombinatorics.FPS.module_neg_eq_neg_one_smul}
\leanhelper
\leanok
Let $K$ be a commutative ring and $M$ a $K$-module. For any $a\in M$,
the additive inverse of $a$ can be constructed as $(-1)\cdot a$, i.e.,
$-a = (-1)\cdot a$.
\end{lemma}
```

:::proof "lem.module.neg-one-smul"
Standard module theory.
:::

```tex "lem.module.neg-one-smul" (slot := proof)
\begin{proof}
\leanok
Standard module theory.
\end{proof}
```

:::lemma_ "lem.module.sub-eq-add-neg" (parent := "module_additive_inverses") (lean := "AlgebraicCombinatorics.FPS.module_sub_eq_add_neg")
Let $`K` be a commutative ring and $`M` a $`K`-module. For any
$`a,b\in M`, we have $`a - b = a + (-b)`.
:::

```tex "lem.module.sub-eq-add-neg" (slot := statement)
\begin{lemma}
\label{lem.module.sub-eq-add-neg}
\lean{AlgebraicCombinatorics.FPS.module_sub_eq_add_neg}
\leanhelper
\leanok
Let $K$ be a commutative ring and $M$ a $K$-module. For any $a,b\in M$,
we have $a - b = a + (-b)$.
\end{lemma}
```

:::proof "lem.module.sub-eq-add-neg"
Standard module theory.
:::

```tex "lem.module.sub-eq-add-neg" (slot := proof)
\begin{proof}
\leanok
Standard module theory.
\end{proof}
```

:::lemma_ "lem.module.sub-eq-add-neg-one-smul" (parent := "module_additive_inverses") (lean := "AlgebraicCombinatorics.FPS.module_sub_eq_add_neg_one_smul")
Let $`K` be a commutative ring and $`M` a $`K`-module. For any
$`a,b\in M`, we have $`a - b = a + (-1)\cdot b`.
:::

```tex "lem.module.sub-eq-add-neg-one-smul" (slot := statement)
\begin{lemma}
\label{lem.module.sub-eq-add-neg-one-smul}
\lean{AlgebraicCombinatorics.FPS.module_sub_eq_add_neg_one_smul}
\leanhelper
\leanok
Let $K$ be a commutative ring and $M$ a $K$-module. For any $a,b\in M$,
we have $a - b = a + (-1)\cdot b$.
\end{lemma}
```

:::proof "lem.module.sub-eq-add-neg-one-smul"
Combine the fact that $`-b = (-1)\cdot b` with $`a - b = a + (-b)`.
:::

```tex "lem.module.sub-eq-add-neg-one-smul" (slot := proof)
\begin{proof}
\leanok
Combine the fact that $-b = (-1)\cdot b$ with $a - b = a + (-b)$.
\end{proof}
```

:::lemma_ "lem.module.neg-add" (parent := "module_additive_inverses") (lean := "AlgebraicCombinatorics.FPS.module_neg_add")
Let $`K` be a commutative ring and $`M` a $`K`-module. For any
$`a,b\in M`, we have $`-(a+b) = (-a) + (-b)`.
:::

```tex "lem.module.neg-add" (slot := statement)
\begin{lemma}
\label{lem.module.neg-add}
\lean{AlgebraicCombinatorics.FPS.module_neg_add}
\leanhelper
\leanok
Let $K$ be a commutative ring and $M$ a $K$-module. For any $a,b\in M$,
we have $-(a+b) = (-a) + (-b)$.
\end{lemma}
```

:::proof "lem.module.neg-add"
Standard module theory.
:::

```tex "lem.module.neg-add" (slot := proof)
\begin{proof}
\leanok
Standard module theory.
\end{proof}
```

:::lemma_ "lem.module.neg-neg" (parent := "module_additive_inverses") (lean := "AlgebraicCombinatorics.FPS.module_neg_neg")
Let $`K` be a commutative ring and $`M` a $`K`-module. For any
$`a\in M`, we have $`-(-a) = a`.
:::

```tex "lem.module.neg-neg" (slot := statement)
\begin{lemma}
\label{lem.module.neg-neg}
\lean{AlgebraicCombinatorics.FPS.module_neg_neg}
\leanhelper
\leanok
Let $K$ be a commutative ring and $M$ a $K$-module. For any $a\in M$,
we have $-(-a) = a$.
\end{lemma}
```

:::proof "lem.module.neg-neg"
Standard module theory.
:::

```tex "lem.module.neg-neg" (slot := proof)
\begin{proof}
\leanok
Standard module theory.
\end{proof}
```


:::group "commutative_rings_inverses"
Inverses and invertible elements in commutative rings.
:::

```tex
\subsection{Inverses in commutative rings}
```

:::definition "def.commring.inverse" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.IsInverse")
Let $`L` be a commutative ring and $`a, b \in L`.

*(a)* We say that $`b` is an _inverse_, or _multiplicative inverse_, of
$`a` if $`a \cdot b = 1`.

*(b)* We say that $`a` is _invertible_ in $`L`, or a _unit_ of $`L`, if
$`a` has an inverse.
:::

```tex "def.commring.inverse" (slot := statement)
\begin{definition}
\label{def.commring.inverse}
\lean{AlgebraicCombinatorics.FPS.IsInverse}
\leanhelper
\leanok
Let $L$ be a commutative ring and $a, b \in L$.

\textbf{(a)} We say that $b$ is an \emph{inverse} (or \emph{multiplicative inverse})
of $a$ if $a \cdot b = 1$.

\textbf{(b)} We say that $a$ is \emph{invertible} in $L$ (or a \emph{unit} of $L$)
if $a$ has an inverse.
\end{definition}
```

:::lemma_ "lem.commring.inverse-uni" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.isInverse_unique")
Let $`L` be a commutative ring. If $`b` and $`c` are both inverses of $`a`,
then $`b = c`. In other words, the inverse of an element, if it exists, is
unique.
:::

```tex "lem.commring.inverse-uni" (slot := statement)
\begin{lemma}
\label{lem.commring.inverse-uni}
\lean{AlgebraicCombinatorics.FPS.isInverse_unique}
\leanhelper
\leanok
Let $L$ be a commutative ring. If $b$ and $c$ are both inverses of $a$,
then $b = c$. In other words, the inverse of an element (if it exists) is unique.
\end{lemma}
```

:::proof "lem.commring.inverse-uni"
We have
$`b = b \cdot 1 = b \cdot (a \cdot c) = (b \cdot a) \cdot c = 1 \cdot c = c`.
:::

```tex "lem.commring.inverse-uni" (slot := proof)
\begin{proof}
\leanok
We have $b = b \cdot 1 = b \cdot (a \cdot c) = (b \cdot a) \cdot c = 1 \cdot c = c$.
\end{proof}
```

:::definition "def.commring.invertible" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.IsInvertible")
An element $`a \in L` is _invertible_ if there exists $`b \in L` such that
$`a \cdot b = 1`.
:::

```tex "def.commring.invertible" (slot := statement)
\begin{definition}
\label{def.commring.invertible}
\lean{AlgebraicCombinatorics.FPS.IsInvertible}
\leanhelper
\leanok
An element $a \in L$ is \emph{invertible} if there exists $b \in L$ such that
$a \cdot b = 1$.
\end{definition}
```

:::lemma_ "lem.commring.invertible-iff-isUnit" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.isInvertible_iff_isUnit")
The definition of invertibility from the inverse definition is equivalent to
the definition of a unit in Mathlib.
:::

```tex "lem.commring.invertible-iff-isUnit" (slot := statement)
\begin{lemma}
\label{lem.commring.invertible-iff-isUnit}
\lean{AlgebraicCombinatorics.FPS.isInvertible_iff_isUnit}
\leanhelper
\leanok
The definition of invertibility from Definition~\ref{def.commring.inverse} is equivalent
to the definition of a unit in Mathlib.
\end{lemma}
```

:::proof "lem.commring.invertible-iff-isUnit"
Both express the existence of a multiplicative inverse; the equivalence is
immediate from the definitions.
:::

```tex "lem.commring.invertible-iff-isUnit" (slot := proof)
\begin{proof}
\leanok
Both express the existence of a multiplicative inverse; the equivalence is
immediate from the definitions.
\end{proof}
```

:::lemma_ "lem.commring.invertible-mul" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.isInvertible_mul")
If $`a` and $`b` are invertible in $`L`, then $`a \cdot b` is invertible.
:::

```tex "lem.commring.invertible-mul" (slot := statement)
\begin{lemma}
\label{lem.commring.invertible-mul}
\lean{AlgebraicCombinatorics.FPS.isInvertible_mul}
\leanhelper
\leanok
If $a$ and $b$ are invertible in $L$, then $a \cdot b$ is invertible.
\end{lemma}
```

:::proof "lem.commring.invertible-mul"
Convert to the equivalent notion of a unit and use the fact that the product
of two units is a unit.
:::

```tex "lem.commring.invertible-mul" (slot := proof)
\begin{proof}
\leanok
Convert to the equivalent notion of a unit and use the fact that the product
of two units is a unit.
\end{proof}
```

:::lemma_ "lem.commring.field-isUnit" (parent := "commutative_rings_inverses") (lean := "AlgebraicCombinatorics.FPS.field_isUnit_iff")
In a field $`F`, an element $`a` is invertible if and only if $`a \neq 0`.
:::

```tex "lem.commring.field-isUnit" (slot := statement)
\begin{lemma}
\label{lem.commring.field-isUnit}
\lean{AlgebraicCombinatorics.FPS.field_isUnit_iff}
\leanhelper
\leanok
In a field $F$, an element $a$ is invertible if and only if $a \neq 0$.
\end{lemma}
```

:::proof "lem.commring.field-isUnit"
Every nonzero element of a field has a multiplicative inverse.
:::

```tex "lem.commring.field-isUnit" (slot := proof)
\begin{proof}
\leanok
Every nonzero element of a field has a multiplicative inverse.
\end{proof}
```

:::group "commutative_rings_fractions"
Fractions and integer powers.
:::

```tex
\subsection{Fractions and integer powers}
```

:::definition "def.commring.fraction" (parent := "commutative_rings_fractions") (lean := "AlgebraicCombinatorics.FPS.fraction")
For an invertible element $`a` and any $`b \in L`, the _fraction_ $`b/a` is
defined as $`b \cdot a^{-1}`.
:::

```tex "def.commring.fraction" (slot := statement)
\begin{definition}
\label{def.commring.fraction}
\lean{AlgebraicCombinatorics.FPS.fraction}
\leanhelper
\leanok
For an invertible element $a$ and any $b \in L$,
the \emph{fraction} $b/a$ is defined as $b \cdot a^{-1}$.
\end{definition}
```

:::lemma_ "lem.commring.fraction-eq-iff" (parent := "commutative_rings_fractions") (lean := "AlgebraicCombinatorics.FPS.fraction_eq_iff")
For an invertible element $`a` and elements $`b, c \in L`, we have
$`b / a = c` if and only if $`b = c \cdot a`.
:::

```tex "lem.commring.fraction-eq-iff" (slot := statement)
\begin{lemma}
\label{lem.commring.fraction-eq-iff}
\lean{AlgebraicCombinatorics.FPS.fraction_eq_iff}
\leanhelper
\leanok
For an invertible element $a$ and elements $b, c \in L$, we have $b / a = c$ if and only if
$b = c \cdot a$.
\end{lemma}
```

:::proof "lem.commring.fraction-eq-iff"
Multiply both sides by $`a`, or by $`a^{-1}`, and use
$`a \cdot a^{-1} = 1`.
:::

```tex "lem.commring.fraction-eq-iff" (slot := proof)
\begin{proof}
\leanok
Multiply both sides by $a$ (or $a^{-1}$) and use $a \cdot a^{-1} = 1$.
\end{proof}
```

:::lemma_ "lem.commring.unit-zpow-neg" (parent := "commutative_rings_fractions") (lean := "AlgebraicCombinatorics.FPS.unit_zpow_neg")
For an invertible element $`a` and a natural number $`n`, we have
$`a^{-n} = (a^{-1})^n`.
This defines negative integer powers.
:::

```tex "lem.commring.unit-zpow-neg" (slot := statement)
\begin{lemma}
\label{lem.commring.unit-zpow-neg}
\lean{AlgebraicCombinatorics.FPS.unit_zpow_neg}
\leanhelper
\leanok
For an invertible element $a$ and a natural number $n$, we have $a^{-n} = (a^{-1})^n$.
This defines negative integer powers.
\end{lemma}
```

:::proof "lem.commring.unit-zpow-neg"
By the definition of integer powers on units.
:::

```tex "lem.commring.unit-zpow-neg" (slot := proof)
\begin{proof}
\leanok
By the definition of integer powers on units.
\end{proof}
```

:::lemma_ "lem.commring.unit-zpow-add" (parent := "commutative_rings_fractions") (lean := "AlgebraicCombinatorics.FPS.unit_zpow_add")
For an invertible element $`a` and integers $`m, n \in \mathbb{Z}`, we have
$`a^{m+n} = a^m \cdot a^n`.
:::

```tex "lem.commring.unit-zpow-add" (slot := statement)
\begin{lemma}
\label{lem.commring.unit-zpow-add}
\lean{AlgebraicCombinatorics.FPS.unit_zpow_add}
\leanhelper
\leanok
For an invertible element $a$ and integers $m, n \in \mathbb{Z}$, we have
$a^{m+n} = a^m \cdot a^n$.
\end{lemma}
```

:::proof "lem.commring.unit-zpow-add"
Standard property of integer powers.
:::

```tex "lem.commring.unit-zpow-add" (slot := proof)
\begin{proof}
\leanok
Standard property of integer powers.
\end{proof}
```
