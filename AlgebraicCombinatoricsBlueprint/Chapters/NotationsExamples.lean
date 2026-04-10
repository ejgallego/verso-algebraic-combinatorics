import Verso
import VersoManual
import VersoBlueprint
import AlgebraicCombinatorics.FPS.NotationsExamples

open Verso.Genre
open Verso.Genre.Manual
open Informal
open AlgebraicCombinatorics

#doc (Manual) "Notations and Elementary Facts" =>

:::group "notational_conventions"
Basic notation and elementary counting principles used later in the chapter.
:::

We will use the following notations and conventions:
- The symbol $`\mathbb{N}` will denote the set $`\{0,1,2,3,\ldots\}` of
  nonnegative integers.
- The size, that is, cardinality, of a set $`A` will be denoted by $`|A|`.

```tex
\section{Notations and elementary facts}

We will use the following notations and conventions:

\begin{itemize}
\item The symbol $\mathbb{N}$ will denote the set $\left\{  0,1,2,3,\ldots
\right\}  $ of nonnegative integers.

\item The size (i.e., cardinality) of a set $A$ will be denoted by $\left\vert
A\right\vert $.
\end{itemize}
```

We will need some basics from enumerative combinatorics:
- *Addition principle (sum rule):* If $`A` and $`B` are two disjoint sets,
  then $`|A \cup B| = |A| + |B|`.
- *Multiplication principle (product rule):* If $`A` and $`B` are any two
  sets, then $`|A \times B| = |A| \cdot |B|`.
- *Bijection principle:* There is a bijection between two sets $`X` and
  $`Y` if and only if $`|X| = |Y|`.
- A set with $`n` elements has $`2^n` subsets, and has $`\dbinom{n}{k}`
  size-$`k` subsets for any $`k \in \mathbb{R}`.
- A set with $`n` elements has $`n!` permutations.

```tex
We will need some basics from enumerative combinatorics:

\begin{itemize}
\item \textbf{Addition principle (sum rule):} If $A$ and $B$ are two disjoint
sets, then $\left\vert A\cup B\right\vert =\left\vert A\right\vert +\left\vert
B\right\vert $.

\item \textbf{Multiplication principle (product rule):} If $A$ and $B$ are any
two sets, then $\left\vert A\times B\right\vert =\left\vert A\right\vert
\cdot\left\vert B\right\vert $.

\item \textbf{Bijection principle:} There is a bijection between two sets $X$ and $Y$ if
and only if $\left\vert X\right\vert =\left\vert Y\right\vert $.

\item A set with $n$ elements has $2^{n}$ subsets, and has $\dbinom{n}{k}$
size-$k$ subsets for any $k\in\mathbb{R}$.

\item A set with $n$ elements has $n!$ permutations.
\end{itemize}
```

:::group "binomial_coefficients"
The opening binomial-coefficient definitions and identities.
:::

```tex
\subsection{Binomial coefficients}
```

:::definition "def.binom.binom" (parent := "binomial_coefficients") (lean := "FPS.binom_def_formula")
For any numbers $`n` and $`k`, we set
$$`\dbinom{n}{k} =
\begin{cases}
\dfrac{n(n-1)(n-2)\cdots(n-k+1)}{k!}, & \text{if } k \in \mathbb{N};\\
0, & \text{else.}
\end{cases}`
Note that "numbers" is to be understood fairly liberally here. In particular,
$`n` can be any integer, rational, real, or complex number, or more generally
any element in a $`\mathbb{Q}`-algebra, whereas $`k` can be anything, although
the only nonzero values of $`\dbinom{n}{k}` are achieved for
$`k \in \mathbb{N}` by the above definition.
:::

```tex "def.binom.binom" (slot := statement)
\begin{definition}
\label{def.binom.binom}
\lean{FPS.binom_def_formula}
\leantarget
\leanok
For any numbers $n$ and $k$, we set%
\begin{equation}
\dbinom{n}{k}=%
\begin{cases}
\dfrac{n\left(  n-1\right)  \left(  n-2\right)  \cdots\left(  n-k+1\right)
}{k!}, & \text{if }k\in\mathbb{N};\\
0, & \text{else.}%
\end{cases}
\label{eq.def.binom.binom.eq}%
\end{equation}
Note that ``numbers'' is to be understood
fairly liberally here. In particular, $n$ can be any integer, rational, real
or complex number (or, more generally, any element in a $\mathbb{Q}$-algebra),
whereas $k$ can be anything (although the only nonzero values of $\dbinom
{n}{k}$ will be achieved for $k\in\mathbb{N}$, by the above definition).
\end{definition}
```

:::lemma_ "lem.binom.neg_one" (parent := "binomial_coefficients") (lean := "FPS.binom_neg_one")
For any $`k \in \mathbb{N}`, we have $`\dbinom{-1}{k} = (-1)^k`.
:::

```tex "lem.binom.neg_one" (slot := statement)
\begin{lemma}
\label{lem.binom.neg_one}
\lean{FPS.binom_neg_one}
\leanhelper
\leanok
For any $k\in\mathbb{N}$, we have
$\dbinom{-1}{k} = (-1)^k$.
\end{lemma}
```

:::proof "lem.binom.neg_one"
We have
$$`\dbinom{-1}{k}
= \dfrac{(-1)(-1-1)(-1-2)\cdots(-1-k+1)}{k!}
= \dfrac{(-1)(-2)(-3)\cdots(-k)}{k!}
= \dfrac{(-1)^k k!}{k!}
= (-1)^k.`
:::

```tex "lem.binom.neg_one" (slot := proof)
\begin{proof}
\leanok
We have
\begin{align*}
\dbinom{-1}{k}  &  =\dfrac{\left(  -1\right)  \left(  -1-1\right)  \left(
-1-2\right)  \cdots\left(  -1-k+1\right)  }{k!}\\
&  =\dfrac{\left(  -1\right)  \left(  -2\right)  \left(  -3\right)
\cdots\left(  -k\right)  }{k!}=\dfrac{\left(  -1\right)  ^{k}k!}{k!}=\left(
-1\right)  ^{k}.
\end{align*}
\end{proof}
```

If $`n, k \in \mathbb{N}` and $`n \ge k`, then
$$`\dbinom{n}{k} = \dfrac{n!}{k!(n-k)!}.`
But this formula only applies to the case when $`n, k \in \mathbb{N}` and
$`n \ge k`. The above definition is more general than it.

```tex
If $n,k\in\mathbb{N}$ and $n\geq k$, then
\begin{equation}
\dbinom{n}{k}=\dfrac{n!}{k!\left(  n-k\right)  !}. \label{eq.binom.fac-form}%
\end{equation}
But this formula only applies to the case when $n,k\in\mathbb{N}$ and $n\geq
k$. The above definition is more general than it.
```

:::lemma_ "lem.binom.fac-form" (parent := "binomial_coefficients") (lean := "FPS.binom_factorial_formula")
For $`n, k \in \mathbb{N}` with $`k \le n`, we have
$`\dbinom{n}{k} = \dfrac{n!}{k!(n-k)!}`.
:::

```tex "lem.binom.fac-form" (slot := statement)
\begin{lemma}
\label{lem.binom.fac-form}
\lean{FPS.binom_factorial_formula}
\leanhelper
\leanok
For $n,k\in\mathbb{N}$ with $k \leq n$, we have
$\dbinom{n}{k}=\dfrac{n!}{k!\left(  n-k\right)  !}$.
\end{lemma}
```

:::proof "lem.binom.fac-form"
This follows directly from the definition by cancellation.
:::

```tex "lem.binom.fac-form" (slot := proof)
\begin{proof}
\leanok
This follows directly from the definition by cancellation.
\end{proof}
```

:::lemma_ "lem.binom.2n-choose-n" (parent := "binomial_coefficients") (lean := "FPS.binom_two_n_n_eq")
Let $`n \in \mathbb{N}`. Then
$$`\dbinom{2n}{n} =
\dfrac{1 \cdot 3 \cdot 5 \cdot \cdots \cdot (2n-1)}{n!} \cdot 2^n.`
:::

```tex "lem.binom.2n-choose-n" (slot := statement)
\begin{lemma}
\label{lem.binom.2n-choose-n}
\lean{FPS.binom_two_n_n_eq}
\leanhelper
\leanok
Let $n\in\mathbb{N}$. Then, $\dbinom{2n}{n}=\dfrac{1\cdot3\cdot5\cdot\cdots\cdot\left(  2n-1\right)  }{n!}\cdot2^{n}$.
\end{lemma}
```

:::proof "lem.binom.2n-choose-n"
We have
$$`(2n)!
= 1 \cdot 2 \cdot \cdots \cdot (2n)
= \left(1 \cdot 3 \cdot 5 \cdot \cdots \cdot (2n-1)\right)
\cdot \left(2 \cdot 4 \cdot 6 \cdot \cdots \cdot (2n)\right)
= \left(1 \cdot 3 \cdot 5 \cdot \cdots \cdot (2n-1)\right) \cdot 2^n n!.`

Now the factorial formula yields
$$`\dbinom{2n}{n}
= \dfrac{(2n)!}{n!n!}
= \dfrac{\left(1 \cdot 3 \cdot 5 \cdot \cdots \cdot (2n-1)\right) \cdot 2^n n!}{n! \cdot n!}
= \dfrac{1 \cdot 3 \cdot 5 \cdot \cdots \cdot (2n-1)}{n!} \cdot 2^n.`
:::

```tex "lem.binom.2n-choose-n" (slot := proof)
\begin{proof}
\leanok
We have%
\begin{align*}
\left(  2n\right)  !  &  =1\cdot2\cdot\cdots\cdot\left(  2n\right) \\
&  =\left(  1\cdot3\cdot5\cdot\cdots\cdot\left(  2n-1\right)  \right)
\cdot\underbrace{\left(  2\cdot4\cdot6\cdot\cdots\cdot\left(  2n\right)
\right)  }_{=2^{n}\left(  1\cdot2\cdot
\cdots\cdot n\right)  }\\
&  =\left(  1\cdot3\cdot5\cdot\cdots\cdot\left(  2n-1\right)  \right)
\cdot2^{n}\underbrace{\left(  1\cdot2\cdot\cdots\cdot n\right)  }_{=n!}\\
&  =\left(  1\cdot3\cdot5\cdot\cdots\cdot\left(  2n-1\right)  \right)
\cdot2^{n}n!.
\end{align*}
Now, (\ref{eq.binom.fac-form}) yields%
\begin{align*}
\dbinom{2n}{n}  &  =\dfrac{\left(  2n\right)  !}{n!n!}=\dfrac{\left(  1\cdot3\cdot5\cdot
\cdots\cdot\left(  2n-1\right)  \right)  \cdot2^{n}n!}{n!\cdot n!}\\
&  =\dfrac{1\cdot3\cdot5\cdot\cdots\cdot\left(  2n-1\right)  }{n!}\cdot2^{n}.
\end{align*}
\end{proof}
```

:::theorem "prop.binom.rec" (parent := "binomial_coefficients") (lean := "FPS.pascal_identity_ring")
We have
$$`\dbinom{m}{n} = \dbinom{m-1}{n-1} + \dbinom{m-1}{n}`
for any numbers $`m` and $`n`.
:::

```tex "prop.binom.rec" (slot := statement)
\begin{proposition}
[\emph{Pascal's identity}, aka \emph{recurrence of the binomial coefficients}]
\label{prop.binom.rec}
\lean{FPS.pascal_identity_ring}
\leantarget
\leanok
We have%
\begin{equation}
\dbinom{m}{n}=\dbinom{m-1}{n-1}+\dbinom{m-1}{n} \label{eq.binom.rec.m}%
\end{equation}
for any numbers $m$ and $n$.
\end{proposition}
```

:::proof "prop.binom.rec"
This follows from the identity
$`\dbinom{r+1}{k+1} = \dbinom{r}{k} + \dbinom{r}{k+1}`, the successor form
of Pascal's identity, by substituting $`r = m - 1` and $`k = n - 1`.
:::

```tex "prop.binom.rec" (slot := proof)
\begin{proof}
\leanok
This follows from the identity
$\dbinom{r+1}{k+1} = \dbinom{r}{k} + \dbinom{r}{k+1}$
(the successor form of Pascal's identity)
by substituting $r = m - 1$ and $k = n - 1$.
\end{proof}
```

:::lemma_ "lem.binom.pascal_nat" (parent := "binomial_coefficients") (lean := "FPS.pascal_identity")
For natural numbers $`m, n` with $`m > 0` and $`n > 0`, we have
$`\dbinom{m}{n} = \dbinom{m-1}{n-1} + \dbinom{m-1}{n}`.
:::

```tex "lem.binom.pascal_nat" (slot := statement)
\begin{lemma}
\label{lem.binom.pascal_nat}
\lean{FPS.pascal_identity}
\leanhelper
\leanok
For natural numbers $m, n$ with $m > 0$ and $n > 0$, we have
$\dbinom{m}{n}=\dbinom{m-1}{n-1}+\dbinom{m-1}{n}$.
\end{lemma}
```

:::proof "lem.binom.pascal_nat"
This is the natural-number specialization of Pascal's identity.
:::

```tex "lem.binom.pascal_nat" (slot := proof)
\begin{proof}
\leanok
This is the natural number specialization of Proposition~\ref{prop.binom.rec}.
\end{proof}
```

:::lemma_ "lem.binom.pascal_succ" (parent := "binomial_coefficients") (lean := "FPS.pascal_identity_succ")
For any element $`r` in a binomial ring and $`k \in \mathbb{N}`,
$`\dbinom{r+1}{k+1} = \dbinom{r}{k} + \dbinom{r}{k+1}`.
:::

```tex "lem.binom.pascal_succ" (slot := statement)
\begin{lemma}
\label{lem.binom.pascal_succ}
\lean{FPS.pascal_identity_succ}
\leanhelper
\leanok
For any element $r$ in a binomial ring and $k \in \mathbb{N}$,
$\dbinom{r+1}{k+1} = \dbinom{r}{k} + \dbinom{r}{k+1}$.
\end{lemma}
```

:::proof "lem.binom.pascal_succ"
This is the successor form of Pascal's identity, which is a standard result in
Mathlib.
:::

```tex "lem.binom.pascal_succ" (slot := proof)
\begin{proof}
\leanok
This is the successor form of Pascal's identity,
which is a standard result in Mathlib.
\end{proof}
```

:::theorem "prop.binom.0" (parent := "binomial_coefficients") (lean := "FPS.binom_zero_of_lt")
Let $`m, n \in \mathbb{N}` satisfy $`m < n`. Then
$`\dbinom{m}{n} = 0`.
:::

```tex "prop.binom.0" (slot := statement)
\begin{proposition}
\label{prop.binom.0}
\lean{FPS.binom_zero_of_lt}
\leantarget
\leanok
Let $m,n\in\mathbb{N}$ satisfy $m<n$. Then, $\dbinom{m}{n}=0$.
\end{proposition}
```

:::proof "prop.binom.0"
If $`m < n`, then in the product
$`m(m-1)(m-2)\cdots(m-n+1)` in the numerator of $`\dbinom{m}{n}`, one of the
factors is $`m-m = 0`. Hence the entire product is $`0`, and so
$`\dbinom{m}{n} = 0`.

Note that this really requires $`m \in \mathbb{N}`. For example,
$`1.5 < 2` but $`\dbinom{1.5}{2} = 0.375 \neq 0`.
:::

```tex "prop.binom.0" (slot := proof)
\begin{proof}
\leanok
If $m < n$, then in the product $m(m-1)(m-2)\cdots(m-n+1)$ in the numerator of $\dbinom{m}{n}$,
one of the factors is $m - m = 0$ (since $m - n + 1 \leq 0 \leq m$ when $m < n$ and $m \in \mathbb{N}$).
Hence the entire product is $0$, and so $\dbinom{m}{n} = 0$.

Note that this really requires $m\in\mathbb{N}$. For
example, $1.5<2$ but $\dbinom{1.5}{2}=0.375\neq0$.
\end{proof}
```

:::theorem "thm.binom.sym" (parent := "binomial_coefficients") (lean := "FPS.binom_symm")
Let $`n \in \mathbb{N}` and $`k \in \mathbb{R}`. Then
$$`\dbinom{n}{k} = \dbinom{n}{n-k}.`
:::

```tex "thm.binom.sym" (slot := statement)
\begin{theorem}
[\emph{Symmetry of the binomial coefficients}]
\label{thm.binom.sym}
\lean{FPS.binom_symm}
\leantarget
\leanok
Let $n\in\mathbb{N}$ and $k\in\mathbb{R}$. Then,%
\[
\dbinom{n}{k}=\dbinom{n}{n-k}.
\]
\end{theorem}
```

:::proof "thm.binom.sym"
For $`k \notin \{0, 1, \ldots, n\}`, both sides are $`0`. If $`k < 0` or
$`k > n`, then both $`\dbinom{n}{k} = 0` and $`\dbinom{n}{n-k} = 0` by the
previous proposition or by the definition.

For $`k \in \{0, 1, \ldots, n\}`, we use the factorial formula:
$$`\dbinom{n}{k}
= \dfrac{n!}{k!(n-k)!}
= \dfrac{n!}{(n-k)!k!}
= \dbinom{n}{n-k}.`

Note the requirement $`n \in \mathbb{N}`. This statement would fail for
$`n = -1` and $`k = 0`, since $`\dbinom{-1}{0} = 1` but
$`\dbinom{-1}{-1} = 0`.
:::

```tex "thm.binom.sym" (slot := proof)
\begin{proof}
\leanok
For $k \notin \{0, 1, \ldots, n\}$, both sides are $0$
(if $k < 0$ or $k > n$, then both $\dbinom{n}{k} = 0$ and $\dbinom{n}{n-k} = 0$
by Proposition~\ref{prop.binom.0} or by the definition).
For $k \in \{0, 1, \ldots, n\}$, we use the factorial formula (\ref{eq.binom.fac-form}):
\[
\dbinom{n}{k} = \frac{n!}{k!(n-k)!} = \frac{n!}{(n-k)!k!} = \dbinom{n}{n-k}.
\]

Note the $n\in\mathbb{N}$ requirement. Theorem~\ref{thm.binom.sym} would fail for $n=-1$ and $k=0$,
since $\dbinom{-1}{0} = 1$ but $\dbinom{-1}{-1} = 0$.
\end{proof}
```

:::lemma_ "lem.binom.symm_add" (parent := "binomial_coefficients") (lean := "FPS.binom_symm_add")
For any $`a, b \in \mathbb{N}`, we have
$`\dbinom{a+b}{a} = \dbinom{a+b}{b}`.
:::

```tex "lem.binom.symm_add" (slot := statement)
\begin{lemma}
\label{lem.binom.symm_add}
\lean{FPS.binom_symm_add}
\leanhelper
\leanok
For any $a, b \in \mathbb{N}$, we have $\dbinom{a+b}{a} = \dbinom{a+b}{b}$.
\end{lemma}
```

:::proof "lem.binom.symm_add"
This follows from the symmetry theorem since $`(a+b) - a = b`.
:::

```tex "lem.binom.symm_add" (slot := proof)
\begin{proof}
\leanok
This follows from Theorem~\ref{thm.binom.sym} since $(a+b) - a = b$.
\end{proof}
```

:::lemma_ "lem.binom.symm_ring" (parent := "binomial_coefficients") (lean := "FPS.binom_symm_ring")
For any binomial ring $`R`, natural numbers $`n, k` with $`k \le n`,
$`\dbinom{n}{k} = \dbinom{n}{n-k}` where $`n` is viewed as an element of
$`R`.
:::

```tex "lem.binom.symm_ring" (slot := statement)
\begin{lemma}
\label{lem.binom.symm_ring}
\lean{FPS.binom_symm_ring}
\leanhelper
\leanok
For any binomial ring $R$, natural numbers $n, k$ with $k \leq n$,
$\dbinom{n}{k} = \dbinom{n}{n-k}$
where $n$ is viewed as an element of $R$.
\end{lemma}
```

:::proof "lem.binom.symm_ring"
This follows from the natural-number symmetry and the fact that the
generalized binomial coefficient agrees with the natural-number binomial
coefficient on natural numbers.
:::

```tex "lem.binom.symm_ring" (slot := proof)
\begin{proof}
\leanok
This follows from the natural-number symmetry (Theorem~\ref{thm.binom.sym})
and the fact that the generalized binomial coefficient agrees with the
natural-number binomial coefficient on natural numbers (Lemma~\ref{lem.binom.natCast}).
\end{proof}
```

:::lemma_ "lem.binom.zero_right" (parent := "binomial_coefficients") (lean := "FPS.binom_zero_right")
For any $`r`, we have $`\dbinom{r}{0} = 1`.
:::

```tex "lem.binom.zero_right" (slot := statement)
\begin{lemma}
\label{lem.binom.zero_right}
\lean{FPS.binom_zero_right}
\leanhelper
\leanok
For any $r$, we have $\dbinom{r}{0} = 1$.
\end{lemma}
```

:::proof "lem.binom.zero_right"
The empty product in the numerator of $`\dbinom{r}{0}` equals $`1`, and
$`0! = 1`.
:::

```tex "lem.binom.zero_right" (slot := proof)
\begin{proof}
\leanok
The empty product in the numerator of $\dbinom{r}{0}$ equals $1$, and $0! = 1$.
\end{proof}
```

:::lemma_ "lem.binom.one_right" (parent := "binomial_coefficients") (lean := "FPS.binom_one_right")
For any $`r`, we have $`\dbinom{r}{1} = r`.
:::

```tex "lem.binom.one_right" (slot := statement)
\begin{lemma}
\label{lem.binom.one_right}
\lean{FPS.binom_one_right}
\leanhelper
\leanok
For any $r$, we have $\dbinom{r}{1} = r$.
\end{lemma}
```

:::proof "lem.binom.one_right"
We have $`\dbinom{r}{1} = \frac{r}{1!} = r`.
:::

```tex "lem.binom.one_right" (slot := proof)
\begin{proof}
\leanok
We have $\dbinom{r}{1} = \frac{r}{1!} = r$.
\end{proof}
```

:::lemma_ "lem.binom.zero_left_pos" (parent := "binomial_coefficients") (lean := "FPS.binom_zero_left_pos")
For $`k > 0`, we have $`\dbinom{0}{k} = 0`.
:::

```tex "lem.binom.zero_left_pos" (slot := statement)
\begin{lemma}
\label{lem.binom.zero_left_pos}
\lean{FPS.binom_zero_left_pos}
\leanhelper
\leanok
For $k > 0$, we have $\dbinom{0}{k} = 0$.
\end{lemma}
```

:::proof "lem.binom.zero_left_pos"
The numerator of $`\dbinom{0}{k}` contains the factor $`0`.
:::

```tex "lem.binom.zero_left_pos" (slot := proof)
\begin{proof}
\leanok
The numerator of $\dbinom{0}{k}$ contains the factor $0$.
\end{proof}
```

:::lemma_ "lem.binom.factorial_smul" (parent := "binomial_coefficients") (lean := "FPS.binom_factorial_smul")
For any element $`r` in a binomial ring and $`n \in \mathbb{N}`,
$$`n! \cdot \dbinom{r}{n} = r(r-1)(r-2)\cdots(r-n+1).`
:::

```tex "lem.binom.factorial_smul" (slot := statement)
\begin{lemma}
\label{lem.binom.factorial_smul}
\lean{FPS.binom_factorial_smul}
\leanhelper
\leanok
For any element $r$ in a binomial ring and $n \in \mathbb{N}$,
$n! \cdot \dbinom{r}{n} = r(r-1)(r-2)\cdots(r-n+1)$.
\end{lemma}
```

:::proof "lem.binom.factorial_smul"
This is the defining property of generalized binomial coefficients in a
binomial ring, expressed using the descending Pochhammer symbol.
:::

```tex "lem.binom.factorial_smul" (slot := proof)
\begin{proof}
\leanok
This is the defining property of generalized binomial coefficients in a binomial ring,
expressed using the descending Pochhammer symbol.
\end{proof}
```

:::lemma_ "lem.binom.natCast" (parent := "binomial_coefficients") (lean := "FPS.binom_natCast")
For natural numbers $`n, k`, the generalized binomial coefficient
$`\dbinom{n}{k}`, computed in any binomial ring, agrees with the
natural-number binomial coefficient $`\dbinom{n}{k}` as computed from the
defining formula for binomial coefficients.
:::

```tex "lem.binom.natCast" (slot := statement)
\begin{lemma}
\label{lem.binom.natCast}
\lean{FPS.binom_natCast}
\leanhelper
\leanok
For natural numbers $n, k$, the generalized binomial coefficient $\dbinom{n}{k}$
(computed in any binomial ring) agrees with the natural-number binomial coefficient
$\dbinom{n}{k}$ as computed from Definition~\ref{def.binom.binom}.
\end{lemma}
```

:::proof "lem.binom.natCast"
This follows from the fact that the generalized binomial coefficient agrees
with the natural-number binomial coefficient when $`n` and $`k` are natural
numbers.
:::

```tex "lem.binom.natCast" (slot := proof)
\begin{proof}
\leanok
This follows from the fact that the generalized binomial coefficient
agrees with the natural-number binomial coefficient when $n$ and $k$ are natural numbers.
\end{proof}
```

:::group "binom_helpers_two_n_choose_n"
Helper lemmas for the odd-factor product appearing in the central binomial
coefficient formula.
:::

```tex
\subsection{Helpers for Lemma~\ref{lem.binom.2n-choose-n}}
```

:::lemma_ "lem.binom.prod_odd_eq_doubleFactorial" (parent := "binom_helpers_two_n_choose_n") (lean := "FPS.prod_odd_eq_doubleFactorial")
For any $`n \in \mathbb{N}`,
$$`\prod_{i=0}^{n-1}(2i+1) = (2n-1)!!`
That is, the product of odd numbers
$`1 \cdot 3 \cdot 5 \cdots (2n-1)` equals the double factorial
$`(2n-1)!!`.
:::

```tex "lem.binom.prod_odd_eq_doubleFactorial" (slot := statement)
\begin{lemma}
\label{lem.binom.prod_odd_eq_doubleFactorial}
\lean{FPS.prod_odd_eq_doubleFactorial}
\leanhelper
\leanok
For any $n\in\mathbb{N}$, $\prod_{i=0}^{n-1}(2i+1) = (2n-1)!!$.
That is, the product of odd numbers $1\cdot 3\cdot 5\cdots(2n-1)$ equals the double factorial $(2n-1)!!$.
\end{lemma}
```

:::proof "lem.binom.prod_odd_eq_doubleFactorial"
By induction on $`n`, using the double factorial recurrence
$`(2m+3)!! = (2m+3)\cdot(2m+1)!!`.
:::

```tex "lem.binom.prod_odd_eq_doubleFactorial" (slot := proof)
\begin{proof}
\leanok
By induction on $n$, using the double factorial recurrence $(2m+3)!! = (2m+3)\cdot(2m+1)!!$.
\end{proof}
```

:::lemma_ "lem.binom.factorial_dvd_prod_odd_mul_pow" (parent := "binom_helpers_two_n_choose_n") (lean := "FPS.factorial_dvd_prod_odd_mul_pow")
For any $`n \in \mathbb{N}`,
$`n!` divides $`\left(\prod_{i=0}^{n-1}(2i+1)\right)\cdot 2^n`.
:::

```tex "lem.binom.factorial_dvd_prod_odd_mul_pow" (slot := statement)
\begin{lemma}
\label{lem.binom.factorial_dvd_prod_odd_mul_pow}
\lean{FPS.factorial_dvd_prod_odd_mul_pow}
\leanhelper
\leanok
For any $n\in\mathbb{N}$, $n!$ divides $\left(\prod_{i=0}^{n-1}(2i+1)\right)\cdot 2^n$.
\end{lemma}
```

:::proof "lem.binom.factorial_dvd_prod_odd_mul_pow"
This uses the factorization
$`(2n)! = 2^n \cdot n! \cdot (2n-1)!!` together with the divisibility
$`n!\cdot n! \mid (2n)!`.
:::

```tex "lem.binom.factorial_dvd_prod_odd_mul_pow" (slot := proof)
\begin{proof}
\leanok
Uses the factorization $(2n)! = 2^n \cdot n! \cdot (2n-1)!!$ together with the
divisibility $n!\cdot n! \mid (2n)!$.
\end{proof}
```

:::group "fibonacci_sequence"
The Fibonacci example and its generating-function formulas.
:::

```tex
\subsection{The Fibonacci sequence (Example 1)}
```

:::definition "def.fib.fibonacci" (parent := "fibonacci_sequence") (lean := "FPS.fibonacci")
The Fibonacci sequence $`(f_0, f_1, f_2, \ldots)` is defined by
$`f_0 = 0`, $`f_1 = 1`, and $`f_n = f_{n-1} + f_{n-2}` for $`n \ge 2`.
:::

```tex "def.fib.fibonacci" (slot := statement)
\begin{definition}
\label{def.fib.fibonacci}
\lean{FPS.fibonacci}
\leanhelper
\leanok
The \emph{Fibonacci sequence} $(f_0, f_1, f_2, \ldots)$ is defined by
$f_0 = 0$, $f_1 = 1$, and $f_n = f_{n-1} + f_{n-2}$ for $n \geq 2$.
\end{definition}
```

:::definition "def.fib.golden_ratio_plus" (parent := "fibonacci_sequence") (lean := "FPS.goldenRatioPlus")
The golden ratio is $`\phi_+ = \frac{1+\sqrt{5}}{2}`.
:::

```tex "def.fib.golden_ratio_plus" (slot := statement)
\begin{definition}
\label{def.fib.golden_ratio_plus}
\lean{FPS.goldenRatioPlus}
\leanhelper
\leanok
The \emph{golden ratio} $\phi_+ = \frac{1+\sqrt{5}}{2}$.
\end{definition}
```

:::definition "def.fib.golden_ratio_minus" (parent := "fibonacci_sequence") (lean := "FPS.goldenRatioMinus")
The conjugate golden ratio is $`\phi_- = \frac{1-\sqrt{5}}{2}`.
:::

```tex "def.fib.golden_ratio_minus" (slot := statement)
\begin{definition}
\label{def.fib.golden_ratio_minus}
\lean{FPS.goldenRatioMinus}
\leanhelper
\leanok
The \emph{conjugate golden ratio} $\phi_- = \frac{1-\sqrt{5}}{2}$.
\end{definition}
```

:::theorem "thm.fib.gf" (parent := "fibonacci_sequence") (lean := "FPS.fibonacci_gf")
The generating function of the Fibonacci sequence is
$$`F(x) = \sum_{n \geq 0} f_n x^n = \frac{x}{1-x-x^2}.`
:::

```tex "thm.fib.gf" (slot := statement)
\begin{theorem}
\label{thm.fib.gf}
\lean{FPS.fibonacci_gf}
\leanhelper
\leanok
The generating function of the Fibonacci sequence is
\[
F(x) = \sum_{n\geq 0} f_n x^n = \frac{x}{1-x-x^2}.
\]
\end{theorem}
```

:::proof "thm.fib.gf"
Let $`D = 1 - x - x^2`. We verify $`F \cdot D = x` by checking that for each
$`n`, $`[x^n](F \cdot D) = f_n - f_{n-1} - f_{n-2} = 0` for $`n \ge 2`,
$`[x^1](F \cdot D) = 1`, and $`[x^0](F \cdot D) = 0`.
Then $`F = x \cdot D^{-1}` since the constant term of $`D` is nonzero.
:::

```tex "thm.fib.gf" (slot := proof)
\begin{proof}
\leanok
Let $D = 1 - x - x^2$. We verify $F \cdot D = x$ by checking that for each $n$,
$[x^n](F\cdot D) = f_n - f_{n-1} - f_{n-2} = 0$ for $n \geq 2$,
$[x^1](F\cdot D) = 1$, and $[x^0](F\cdot D) = 0$.
Then $F = x \cdot D^{-1}$ since the constant term of $D$ is nonzero.
\end{proof}
```

:::theorem "thm.fib.binet" (parent := "fibonacci_sequence") (lean := "FPS.fibonacci_binet")
For any $`n \in \mathbb{N}`,
$$`f_n = \frac{\phi_+^n - \phi_-^n}{\sqrt{5}}.`
:::

```tex "thm.fib.binet" (slot := statement)
\begin{theorem}[Binet's formula]
\label{thm.fib.binet}
\lean{FPS.fibonacci_binet}
\leanhelper
\leanok
For any $n\in\mathbb{N}$,
\[
f_n = \frac{\phi_+^n - \phi_-^n}{\sqrt{5}}.
\]
\end{theorem}
```

:::proof "thm.fib.binet"
This follows from Binet's formula as established in Mathlib.
:::

```tex "thm.fib.binet" (slot := proof)
\begin{proof}
\leanok
This follows from Binet's formula as established in Mathlib.
\end{proof}
```

:::group "catalan_example"
Dyck words, Catalan numbers, and their generating function.
:::

```tex
\subsection{Dyck words and Catalan numbers (Example 2)}
```

:::definition "def.catalan.dyck" (parent := "catalan_example") (lean := "FPS.isDyckWord")
A _Dyck word_ of length $`2n` is a list of $`0`s and $`1`s with equal numbers
of each, such that every prefix has at least as many $`1`s as $`0`s.
:::

```tex "def.catalan.dyck" (slot := statement)
\begin{definition}
\label{def.catalan.dyck}
\lean{FPS.isDyckWord}
\leanhelper
\leanok
A \emph{Dyck word} of length $2n$ is a list of $0$s and $1$s
with equal numbers of each, such that every prefix has at least as many $1$s as $0$s.
\end{definition}
```

:::definition "def.catalan.catalan" (parent := "catalan_example") (lean := "FPS.catalan")
The $`n`-th _Catalan number_ is
$`c_n = \frac{1}{n+1}\dbinom{2n}{n}`.
:::

```tex "def.catalan.catalan" (slot := statement)
\begin{definition}
\label{def.catalan.catalan}
\lean{FPS.catalan}
\leanhelper
\leanok
The $n$-th \emph{Catalan number} is $c_n = \frac{1}{n+1}\dbinom{2n}{n}$.
\end{definition}
```

:::theorem "thm.catalan.recurrence" (parent := "catalan_example") (lean := "FPS.catalan_recurrence")
For $`n \ge 1`, the Catalan numbers satisfy the recurrence
$$`c_n = \sum_{k=0}^{n-1} c_k \, c_{n-1-k}.`
:::

```tex "thm.catalan.recurrence" (slot := statement)
\begin{theorem}
\label{thm.catalan.recurrence}
\lean{FPS.catalan_recurrence}
\leanhelper
\leanok
For $n \geq 1$, the Catalan numbers satisfy the recurrence
\[
c_n = \sum_{k=0}^{n-1} c_k \, c_{n-1-k}.
\]
\end{theorem}
```

:::proof "thm.catalan.recurrence"
This follows from Mathlib's Catalan number recurrence, converting between
Mathlib's recursive definition and the explicit formula.
:::

```tex "thm.catalan.recurrence" (slot := proof)
\begin{proof}
\leanok
Follows from Mathlib's Catalan number recurrence, converting between
Mathlib's recursive definition and the explicit formula.
\end{proof}
```

:::lemma_ "lem.catalan.explicit" (parent := "catalan_example") (lean := "FPS.catalan_explicit")
The explicit formula for Catalan numbers is
$`c_n = \frac{1}{n+1}\dbinom{2n}{n}`.
:::

```tex "lem.catalan.explicit" (slot := statement)
\begin{lemma}
\label{lem.catalan.explicit}
\lean{FPS.catalan_explicit}
\leanhelper
\leanok
The explicit formula for Catalan numbers:
$c_n = \frac{1}{n+1}\dbinom{2n}{n}$.
\end{lemma}
```

:::proof "lem.catalan.explicit"
This is immediate from the definition of $`c_n`.
:::

```tex "lem.catalan.explicit" (slot := proof)
\begin{proof}
\leanok
This is immediate from the definition of $c_n$.
\end{proof}
```

:::lemma_ "lem.catalan.as_diff" (parent := "catalan_example") (lean := "FPS.catalan_as_diff")
For $`n \ge 1`,
$`c_n = \dbinom{2n}{n} - \dbinom{2n}{n-1}`.
:::

```tex "lem.catalan.as_diff" (slot := statement)
\begin{lemma}
\label{lem.catalan.as_diff}
\lean{FPS.catalan_as_diff}
\leanhelper
\leanok
For $n \geq 1$,
$c_n = \dbinom{2n}{n} - \dbinom{2n}{n-1}$.
\end{lemma}
```

:::proof "lem.catalan.as_diff"
This uses the identity
$`\dbinom{2n}{n-1}\cdot(n+1) = \dbinom{2n}{n}\cdot n`, coming from the
recurrence for binomial coefficients, together with the divisibility
$`(n+1) \mid \dbinom{2n}{n}`.
:::

```tex "lem.catalan.as_diff" (slot := proof)
\begin{proof}
\leanok
Uses the identity $\dbinom{2n}{n-1}\cdot(n+1) = \dbinom{2n}{n}\cdot n$
(from the recurrence for binomial coefficients) and the divisibility $(n+1) \mid \dbinom{2n}{n}$.
\end{proof}
```

:::theorem "thm.catalan.gf_equation" (parent := "catalan_example") (lean := "FPS.catalan_gf_equation")
The generating function $`C(x) = \sum_{n\geq 0} c_n x^n` satisfies the
functional equation
$`C(x) = 1 + x\, C(x)^2`.
:::

```tex "thm.catalan.gf_equation" (slot := statement)
\begin{theorem}
\label{thm.catalan.gf_equation}
\lean{FPS.catalan_gf_equation}
\leanhelper
\leanok
The generating function $C(x) = \sum_{n\geq 0} c_n x^n$ satisfies the functional equation
$C(x) = 1 + x\, C(x)^2$.
\end{theorem}
```

:::proof "thm.catalan.gf_equation"
This follows from Mathlib's identity
$`C(x)^2 \cdot x + 1 = C(x)` for the Catalan generating function, after
showing that $`C(x)` equals the image of Mathlib's Catalan series under the
natural map.
:::

```tex "thm.catalan.gf_equation" (slot := proof)
\begin{proof}
\leanok
Follows from Mathlib's identity $C(x)^2 \cdot x + 1 = C(x)$ for the Catalan generating function,
after showing that $C(x)$ equals the image of Mathlib's Catalan series under the natural map.
\end{proof}
```

:::group "catalan_gf_helpers"
Helper lemmas for the explicit Catalan generating function.
:::

```tex
\subsubsection{Helpers for the Catalan generating function}
```

:::lemma_ "lem.catalan.choose_half_recurrence" (parent := "catalan_gf_helpers") (lean := "FPS.choose_half_recurrence")
For $`n \in \mathbb{N}`,
$`(n+1)\dbinom{1/2}{n+1} = \left(\frac{1}{2}-n\right)\dbinom{1/2}{n}`.
:::

```tex "lem.catalan.choose_half_recurrence" (slot := statement)
\begin{lemma}
\label{lem.catalan.choose_half_recurrence}
\lean{FPS.choose_half_recurrence}
\leanhelper
\leanok
For $n\in\mathbb{N}$,
$(n+1)\dbinom{1/2}{n+1} = \left(\frac{1}{2}-n\right)\dbinom{1/2}{n}$.
\end{lemma}
```

:::proof "lem.catalan.choose_half_recurrence"
This follows from the descending Pochhammer recurrence applied to
$`\dbinom{1/2}{n}`.
:::

```tex "lem.catalan.choose_half_recurrence" (slot := proof)
\begin{proof}
\leanok
Follows from the descending Pochhammer recurrence
applied to $\dbinom{1/2}{n}$.
\end{proof}
```

:::lemma_ "lem.catalan.A_eq_neg_two_centralBinom" (parent := "catalan_gf_helpers") (lean := "FPS.A_eq_neg_two_centralBinom")
For $`n \in \mathbb{N}`,
$`\dbinom{1/2}{n+1}\cdot(-4)^{n+1}\cdot(n+1) = -2\cdot\dbinom{2n}{n}`.
:::

```tex "lem.catalan.A_eq_neg_two_centralBinom" (slot := statement)
\begin{lemma}
\label{lem.catalan.A_eq_neg_two_centralBinom}
\lean{FPS.A_eq_neg_two_centralBinom}
\leanhelper
\leanok
For $n\in\mathbb{N}$,
$\dbinom{1/2}{n+1}\cdot(-4)^{n+1}\cdot(n+1) = -2\cdot\dbinom{2n}{n}$.
\end{lemma}
```

:::proof "lem.catalan.A_eq_neg_two_centralBinom"
By induction on $`n`, using the previous recurrence lemma and the central
binomial coefficient recurrence
$`(n+1)\dbinom{2(n+1)}{n+1} = 2(2n+1)\dbinom{2n}{n}`.
:::

```tex "lem.catalan.A_eq_neg_two_centralBinom" (slot := proof)
\begin{proof}
\leanok
By induction on $n$, using Lemma~\ref{lem.catalan.choose_half_recurrence}
and the central binomial coefficient recurrence $(n+1)\dbinom{2(n+1)}{n+1} = 2(2n+1)\dbinom{2n}{n}$.
\end{proof}
```

:::lemma_ "lem.catalan.choose_half_neg4_pow" (parent := "catalan_gf_helpers") (lean := "FPS.choose_half_neg4_pow_eq")
For $`n \in \mathbb{N}`,
$`\dbinom{1/2}{n+1}\cdot(-4)^{n+1} = -2\, c_n`.
:::

```tex "lem.catalan.choose_half_neg4_pow" (slot := statement)
\begin{lemma}
\label{lem.catalan.choose_half_neg4_pow}
\lean{FPS.choose_half_neg4_pow_eq}
\leanhelper
\leanok
For $n\in\mathbb{N}$,
$\dbinom{1/2}{n+1}\cdot(-4)^{n+1} = -2\, c_n$.
\end{lemma}
```

:::proof "lem.catalan.choose_half_neg4_pow"
This follows from the previous lemma by dividing both sides by $`(n+1)`, using
$`(n+1)\mid\dbinom{2n}{n}` and
$`c_n = \dbinom{2n}{n}/(n+1)`.
:::

```tex "lem.catalan.choose_half_neg4_pow" (slot := proof)
\begin{proof}
\leanok
Follows from Lemma~\ref{lem.catalan.A_eq_neg_two_centralBinom} by dividing both sides by $(n+1)$,
using $(n+1)\mid\dbinom{2n}{n}$ and $c_n = \dbinom{2n}{n}/(n+1)$.
\end{proof}
```

:::theorem "thm.catalan.gf_explicit" (parent := "catalan_gf_helpers") (lean := "FPS.catalan_gf_explicit")
The generating function of the Catalan numbers satisfies
$$`2x\,C(x) = 1 - \sqrt{1-4x},`
where $`\sqrt{1-4x} = \sum_{n\geq 0}\dbinom{1/2}{n}(-4)^n x^n` is the
binomial series.
:::

```tex "thm.catalan.gf_explicit" (slot := statement)
\begin{theorem}
\label{thm.catalan.gf_explicit}
\lean{FPS.catalan_gf_explicit}
\leanhelper
\leanok
The generating function of the Catalan numbers satisfies
\[
2x\,C(x) = 1 - \sqrt{1-4x},
\]
where $\sqrt{1-4x} = \sum_{n\geq 0}\dbinom{1/2}{n}(-4)^n x^n$ is the binomial series.
\end{theorem}
```

:::proof "thm.catalan.gf_explicit"
We check coefficient by coefficient. For $`n=0`, both sides give $`0`.
For $`n \ge 1`, the $`n`-th coefficient of the left side is $`2c_{n-1}`,
and the $`n`-th coefficient of $`1 - \sqrt{1-4x}` is
$`-\dbinom{1/2}{n}(-4)^n`, which equals $`2c_{n-1}` by the previous helper
lemma.
:::

```tex "thm.catalan.gf_explicit" (slot := proof)
\begin{proof}
\leanok
We check coefficient by coefficient. For $n=0$, both sides give $0$.
For $n \geq 1$, the $n$-th coefficient of the left side is $2c_{n-1}$,
and the $n$-th coefficient of $1 - \sqrt{1-4x}$ is $-\dbinom{1/2}{n}(-4)^n$,
which equals $2c_{n-1}$ by Lemma~\ref{lem.catalan.choose_half_neg4_pow}.
\end{proof}
```
