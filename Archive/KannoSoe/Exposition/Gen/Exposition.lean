import KannoSoe.Exposition.Gen.ExpositionLib

def main (args : List String) : IO Unit := do
  match KannoSoe.Exposition.parseArgs args with
  | .error msg => throw (IO.userError msg)
  | .ok opts =>
      if opts.check then
        KannoSoe.Exposition.checkDocs opts.outputRoot
      else
        KannoSoe.Exposition.writeDocs opts.outputRoot
