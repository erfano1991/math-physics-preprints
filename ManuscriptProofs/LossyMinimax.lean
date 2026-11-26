import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Set

namespace ManuscriptProofs.LossyQubit

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

private def payoff (v : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ i, p i * v i
  map_add' p q := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r p := by simp [Finset.mul_sum, mul_assoc]

/-- If every probability weighting has a generating direction with payoff
at least c, a single mixture of at most N+1 generating payoff vectors attains
at least c in every coordinate. K is the compact hull used in the paper. -/
theorem finite_menu_minimax (S : Set (ι → ℝ)) (hs : S.Nonempty)
    (hk : IsCompact (convexHull ℝ S)) (c : ℝ)
    (h : ∀ p ∈ stdSimplex ℝ ι, ∃ v ∈ S, c ≤ ∑ i, p i*v i) :
    ∃ t : Finset (ι → ℝ), (t : Set (ι → ℝ)) ⊆ S ∧ t.card ≤ Fintype.card ι+1 ∧
      ∃ v ∈ convexHull ℝ (t : Set (ι → ℝ)), ∀ i, c ≤ v i := by
  classical
  let X := stdSimplex ℝ ι
  let Y := convexHull ℝ S
  let f := fun p v : ι → ℝ => ∑ i, p i*v i
  have hX : X.Nonempty := ⟨_,single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩
  have hY : Y.Nonempty := hs.mono (subset_convexHull ℝ S)
  have hcx := convex_stdSimplex ℝ ι
  have hcy := convex_convexHull ℝ S
  have hc₁ (v : ι → ℝ) : Continuous (fun p => f p v) := by dsimp [f]; fun_prop
  have hc₂ (p : ι → ℝ) : Continuous (f p) := by dsimp [f]; fun_prop
  have hsym (p v : ι → ℝ) : f p v = payoff p v := by simp [f, payoff, mul_comm]
  obtain ⟨p,hp,v,hv,hvopt⟩ := Sion.exists_isSaddlePointOn (f := f) hX hcx
    (isCompact_stdSimplex ℝ ι) (fun v _ => (hc₁ v).continuousOn.lowerSemicontinuousOn)
    (fun v _ => ((payoff v).convexOn hcx).quasiconvexOn) hcy hY hk
    (fun p _ => (hc₂ p).continuousOn.upperSemicontinuousOn)
    (fun p _ => by simpa only [hsym] using ((payoff p).concaveOn hcy).quasiconcaveOn)
  obtain ⟨u,hu,hcu⟩ := h p hp
  have hcoord (i : ι) : c ≤ v i := by
    have hi := hvopt _ (single_mem_stdSimplex ℝ i) u (subset_convexHull ℝ S hu)
    exact hcu.trans (by simpa [f, Pi.single_apply, ite_mul] using hi)
  let t := Caratheodory.minCardFinsetOfMemConvexHull hv
  have hind := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hv
  have hdim := (hind.card_le_finrank_succ).trans
    (Nat.add_le_add_right (Submodule.finrank_le (vectorSpan ℝ (range ((↑) : t → (ι → ℝ))))) 1)
  refine ⟨t,Caratheodory.minCardFinsetOfMemConvexHull_subseteq hv, ?_, v,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hv, hcoord⟩
  simpa [t, Module.finrank_pi] using hdim

end ManuscriptProofs.LossyQubit
