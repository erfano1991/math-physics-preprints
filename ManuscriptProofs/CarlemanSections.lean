import Mathlib.Analysis.ODE.ExistUnique

open Set

namespace ManuscriptProofs.Carleman

/-- Once the Taylor section and the truncated solution satisfy the same
finite linear system, they agree on every forward interval. -/
theorem finite_section_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) {f g : ℝ → E} {T : ℝ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (df : ∀ t ∈ Ico 0 T, HasDerivWithinAt f (A (f t)) (Ici t) t)
    (dg : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (A (g t)) (Ici t) t)
    (hzero : f 0 = g 0) : EqOn f g (Icc 0 T) :=
  ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ) (v := fun _ x => A x)
    (fun _ _ => A.lipschitzWith.lipschitzOnWith) hf df (fun _ _ => mem_univ _)
    hg dg (fun _ _ => mem_univ _) hzero

end ManuscriptProofs.Carleman
