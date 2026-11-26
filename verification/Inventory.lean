import ManuscriptProofs
import Lean.Util.CollectAxioms

open Lean Elab Command

/- Inventory by owning module, including private declarations and automatically
generated constants. The audit itself exports no mathematical declarations. -/
run_cmd do
  let env ← getEnv
  let owned := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some idx =>
      let mod := env.header.moduleNames[idx.toNat]!
      if (`ManuscriptProofs).isPrefixOf mod then acc.push (mod, name) else acc
  let sorted := owned.qsort fun a b => if a.1 == b.1 then a.2.lt b.2 else a.1.lt b.1
  if sorted.isEmpty then throwError "no project declarations found"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (mod, name) in sorted do
    let ci ← getConstInfo name
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let deps ← collectAxioms name
    let unexpected := deps.filter fun a => !allowed.contains a
    if kind == "axiom" || kind == "opaque" || ci.isUnsafe || !unexpected.isEmpty then
      throwError "unexpected declaration or dependency: {mod} {name} {kind} unsafe={ci.isUnsafe} partial={ci.isPartial} {deps}"
    if ci.isPartial then
      unless kind == "definition" && name.getString! == "_unsafe_rec" do
        throwError "unexpected partial definition: {mod} {name}"
      liftIO <| IO.println s!"RUNTIME\t{mod}\t{name}\tgenerated partial recursion backend"
    let axes := String.intercalate "," (deps.toList.map toString)
    liftIO <| IO.println s!"DECL\t{mod}\t{name}\t{kind}\t{axes}"
  liftIO <| IO.println s!"COUNT\t{sorted.size}"
