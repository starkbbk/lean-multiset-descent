import Descent
import Lean.Util.CollectAxioms

/-!
Run with `lake env lean Audit.lean`. Every declaration in the project namespace
is checked, including definitions that contain certificate proof fields.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Descent).isPrefixOf name then
      declarations := declarations + 1
      match info with
      | .axiomInfo _ => throwError "Project-defined axiom rejected: {name}"
      | .thmInfo _ =>
        theorems := theorems + 1
        logInfo m!"THEOREM {name}"
      | _ => pure ()
      let axioms ← collectAxioms name
      let unexpected := axioms.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected proof dependency in {name}: {unexpected}"
  unless theorems ≥ 50 do
    throwError "Expected at least 50 project theorems, found {theorems}"
  logInfo m!"AUDIT PASS: {theorems} theorem declarations (including generated helpers); {declarations} declarations checked."
  logInfo "Allowed foundational axioms: propext, Classical.choice, Quot.sound."
