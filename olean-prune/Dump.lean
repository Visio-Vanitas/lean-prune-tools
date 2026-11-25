import Lean
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

def deps (c : ConstantInfo) : NameSet := Id.run do
  let mut s : NameSet := {}
  for n in c.type.getUsedConstants do s := s.insert n
  match c with
  | .defnInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .thmInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .opaqueInfo v => for n in v.value.getUsedConstants do s := s.insert n
  | .inductInfo v => for n in v.ctors do s := s.insert n
  | .ctorInfo v => s := s.insert v.induct
  | .recInfo v => for r in v.rules do for n in r.rhs.getUsedConstants do s := s.insert n
  | _ => pure ()
  return s

/-- usage:
  names OUT LIST      LIST lines: `module<TAB>pathstem`; prints `module<TAB>kind<TAB>name` from public .olean
  deps OUT NAMES LIST prints `module<TAB>kind<TAB>name<TAB>deps...` from full data, deps filtered to NAMES -/
unsafe def main (args : List String) : IO Unit := do
  match args with
  | ["names", out, list] =>
    let h ← IO.FS.Handle.mk out .write
    for line in (← IO.FS.lines list) do
      match line.splitOn "\t" with
      | [m, p] =>
        try
          let (md, region) ← readModuleData (p ++ ".olean")
          for c in md.constants do h.putStrLn s!"{m}\t{kindOf c}\t{c.name}"
          region.free
        catch e => IO.eprintln s!"ERR {m}: {e}"
      | _ => pure ()
  | ["deps", out, namesFile, list] =>
    let mut known : NameSet := {}
    for l in (← IO.FS.lines namesFile) do known := known.insert l.toName
    let h ← IO.FS.Handle.mk out .write
    for line in (← IO.FS.lines list) do
      match line.splitOn "\t" with
      | [m, p] =>
        try
          let full : System.FilePath := p ++ ".olean.private"
          let parts : Array System.FilePath := #[p ++ ".olean", p ++ ".olean.server", full]
          let ok ← do pure ((← full.pathExists) && (← full.metadata).byteSize > 0)
          let res ← readModuleDataParts (if ok then parts else #[p ++ ".olean"])
          if let some (md, _) := res.back? then
            let tag := if ok then "full" else "public"
            for c in md.constants do
              let ds := (deps c).toList.filter (fun n => (known.contains n || isPrivateName n) && n != c.name)
              h.putStrLn s!"{m}\t{tag}\t{kindOf c}\t{c.name}\t{" ".intercalate (ds.map toString)}"
          for (_, region) in res.reverse do
            region.free
          pure ()
        catch e => IO.eprintln s!"ERR {m}: {e}"
      | _ => pure ()
  | _ => IO.eprintln "bad usage"
