import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "TeX To Verso Porting Status" =>

:::group "porting_status"
Current harness status for the Algebraic Combinatorics Verso port.
:::

:::definition "tex_source_of_truth" (parent := "porting_status")
The TeX source of truth for the prose structure lives in
`algebraic-combinatorics/blueprint/src/chapter_*.tex`, with chapter order in
`algebraic-combinatorics/blueprint/src/content.tex`.
:::

:::definition "porting_status_workflow" (parent := "porting_status")
The shared harness lives under `tools/verso-harness`. Direct-port chapters
should be moved toward LT, then checked with the harness audit stack rather
than maintained as free-form prose.
:::

:::definition "porting_status_snapshot" (parent := "porting_status")
The current scaffold creates one direct-port chapter starter,
`NotationsExamples`, sourced from `chapter_notations.tex`. The remaining source
chapters are still pending first-pass Verso transcription.
:::
