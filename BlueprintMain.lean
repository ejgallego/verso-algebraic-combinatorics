import VersoManual
import VersoBlueprint.PreviewManifest
import AlgebraicCombinatoricsBlueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc AlgebraicCombinatoricsBlueprint)
    args
    (extensionImpls := by exact extension_impls%)
