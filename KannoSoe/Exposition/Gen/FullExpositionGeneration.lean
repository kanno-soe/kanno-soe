import KannoSoe.Exposition.Gen.ExpositionLib

namespace KannoSoe.Exposition.Gen.FullExpositionGeneration

def outputRoot : String := ".lake/exposition-full"

def copyStaticDocs : IO Unit := do
  IO.FS.createDirAll (outputRoot ++ "/Exposition")
  for ref in KannoSoe.Exposition.registry do
    match ref.provenance with
    | .source =>
        let content <- IO.FS.readFile ref.output
        IO.FS.writeFile (KannoSoe.Exposition.outputPath outputRoot ref.output) content
    | .generated _ => pure ()

def checkNonempty (ref : KannoSoe.Exposition.DocRef) : IO Unit := do
  let path := KannoSoe.Exposition.outputPath outputRoot ref.output
  let content <- IO.FS.readFile path
  if content.isEmpty then
    throw (IO.userError s!"exposition file is empty: {path}")

def run : IO Unit := do
  copyStaticDocs
  KannoSoe.Exposition.writeDocs outputRoot
  for ref in KannoSoe.Exposition.registry do
    checkNonempty ref

end KannoSoe.Exposition.Gen.FullExpositionGeneration

def main : IO Unit := do
  KannoSoe.Exposition.Gen.FullExpositionGeneration.run
