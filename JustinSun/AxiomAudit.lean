import Lean

/-!
# Axiom audit

`#audit_axioms Pfx` collects every declaration whose name starts with `Pfx`, computes the axioms
each depends on, and fails (with an error) if any declaration uses an axiom other than `propext`,
`Classical.choice` and `Quot.sound` (in particular `sorryAx` or `Lean.ofReduceBool`).
-/

open Lean Elab Command

syntax (name := auditAxioms) "#audit_axioms " ident : command

@[command_elab auditAxioms] def elabAuditAxioms : CommandElab := fun stx => do
  let pfx := stx[1].getId
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (n, _) in env.constants.map₁.toList ++ env.constants.map₂.toList do
    if pfx.isPrefixOf n && !n.isInternal then
      count := count + 1
      let axs ← liftCoreM (collectAxioms n)
      let extra := axs.filter (fun a => !(allowed.contains a))
      if !extra.isEmpty then bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"audit {pfx}: {count} declarations, axioms within [propext, Classical.choice, Quot.sound]"
  else
    throwError m!"audit {pfx}: {bad.size} of {count} declarations use other axioms: {bad.toList}"

syntax (name := requireStandardAxioms) "#require_standard_axioms " ident : command

/-- `#require_standard_axioms d` fails unless declaration `d` depends only on `propext`,
`Classical.choice` and `Quot.sound`. -/
@[command_elab requireStandardAxioms] def elabRequireStandardAxioms : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let axs ← liftCoreM (collectAxioms n)
  let extra := axs.filter (fun a => !(allowed.contains a))
  if extra.isEmpty then
    logInfo m!"{n}: axioms {axs.toList} (standard only)"
  else
    throwError m!"{n} uses non-standard axioms: {extra.toList}"
