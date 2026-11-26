import ManuscriptProofs
import Lean.Replay
import Lean.Util.FoldConsts

open Lean Elab Command

/- Independent of the axiom-summary extension. Traverse the actual types and
proof terms, complete each mutual-inductive block, and replay the resulting
closed set in an empty kernel environment. No declaration is added to a paper. -/
run_cmd do
  let env ← getEnv
  let allLocal := env.constants.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | none => acc
    | some i => if (`ManuscriptProofs).isPrefixOf env.header.moduleNames[i.toNat]!
                then acc.push name else acc
  let mut roots : Array Name := #[]
  let mut runtime : Array Name := #[]
  for n in allLocal do
    let ci ← getConstInfo n
    if ci.isPartial then
      unless n.getString! == "_unsafe_rec" do throwError "unexpected partial root {n}"
      runtime := runtime.push n
    else
      roots := roots.push n
  if roots.isEmpty then throwError "empty root set"
  let mut pending := roots.toList
  let mut closure : Std.HashMap Name ConstantInfo := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if closure.contains n then continue
    let some ci := env.find? n | throwError "missing dependency {n}"
    closure := closure.insert n ci
    if ci.isUnsafe || ci.isPartial then
      throwError "unsafe or partial declaration in mathematical closure: {n}"
    match ci with
    | .axiomInfo _ => axioms := axioms.insert n
    | .inductInfo v => pending := v.all ++ pending
    | _ => pure ()
    pending := ci.getUsedConstantsAsSet.toList ++ pending
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for n in axioms.toList do
    unless allowed.contains n do throwError "unexpected raw dependency: {n}"
  for n in runtime do
    if closure.contains n then throwError "a logical root used the partial runtime helper {n}"
  liftIO <| IO.println s!"Local object declarations: {allLocal.size}; total logical roots: {roots.size}; generated partial runtime helpers excluded and unreachable: {runtime.size}"
  liftIO <| IO.println s!"Actual transitive mathematical constants: {closure.size}"
  liftIO <| IO.println s!"Axioms reached in proof terms: {axioms.toList}"
  let empty ← liftIO <| mkEmptyEnvironment
  let verified ← liftIO <| empty.toKernelEnv.replay closure
  for (n, _) in closure.toList do
    unless (verified.find? n).isSome do throwError "declaration absent after kernel replay: {n}"
  liftIO <| IO.println "PASS: complete mathematical dependency closure replayed into the empty Lean kernel environment."
