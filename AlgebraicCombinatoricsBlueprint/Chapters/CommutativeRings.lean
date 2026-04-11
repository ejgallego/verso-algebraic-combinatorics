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
