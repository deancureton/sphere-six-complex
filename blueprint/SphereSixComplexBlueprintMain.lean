import VersoBlueprint.PreviewManifest
import VersoManual
import SphereSixComplexBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc SphereSixComplexBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
