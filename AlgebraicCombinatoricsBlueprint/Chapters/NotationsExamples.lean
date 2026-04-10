import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Notations and Elementary Facts" =>

:::group "notational_conventions"
Starter direct-port chapter for
`algebraic-combinatorics/blueprint/src/chapter_notations.tex`.
:::

:::group "binomial_coefficients"
The source chapter continues with a binomial-coefficients subsection whose
labeled statements are formalized in the upstream `AlgebraicCombinatorics.FPS`
namespace.
:::

The legacy blueprint opens with basic notational conventions and a short list
of elementary counting principles.

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

The same source file then begins the binomial-coefficient material that will
anchor the first LT pass for this repository.

```tex
\subsection{Binomial coefficients}

\begin{definition}
\label{def.binom.binom}
\lean{FPS.binom_def_formula}
\leantarget
\leanok
...
\end{definition}
```

The first labeled results in this source section are `FPS.binom_def_formula`,
`FPS.binom_neg_one`, `FPS.binom_factorial_formula`, `FPS.binom_two_n_n_eq`,
`FPS.pascal_identity_ring`, `FPS.binom_zero_of_lt`, and `FPS.binom_symm`.
