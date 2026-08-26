import Solution

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut worklist : Array Name := #[`sphere_six_admits_complex_structure, `mathoverflow_1973]
  let mut checked : Std.HashSet Name := {}
  let mut axioms : Std.HashSet Name := {}
  while !worklist.isEmpty do
    let target := worklist.back!
    worklist := worklist.pop
    if checked.contains target then
      continue
    let some info := env.find? target
      | throwError "constant not found: {target}"
    let mut references : Array Name := #[info.name]
    for name in info.type.getUsedConstants do
      references := references.push name
    if let some value := info.value? (allowOpaque := true) then
      for name in value.getUsedConstants do
        references := references.push name
    match info with
    | .inductInfo data =>
        references := references ++ data.ctors ++ data.all
    | .ctorInfo data =>
        references := references.push data.induct
    | .recInfo data =>
        for rule in data.rules do
          references := references.push rule.ctor
          for name in rule.rhs.getUsedConstants do
            references := references.push name
    | _ => pure ()
    for name in references do
      let some dependency := env.find? name
        | throwError "dependency not found: {name}"
      if let .axiomInfo axiomInfo := dependency then
        axioms := axioms.insert axiomInfo.name
      if !checked.contains name then
        worklist := worklist.push name
    checked := checked.insert target
  for name in axioms.toArray.qsort Name.lt do
    logInfo m!"{name}"
