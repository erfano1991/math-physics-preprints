import ManuscriptProofs.ExclusionFrames
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

open Set Metric

namespace ManuscriptProofs.PureExclusion

/-- The actual unit vectors in a nonzero complex space form a connected
fiber, including the complex line that occurs at the last step. -/
theorem complex_unit_sphere_connected (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : 0 < Module.finrank ℂ E) :
    IsConnected (Metric.sphere (0:E) 1) := by
  let := NormedSpace.restrictScalars ℝ ℂ E
  apply isConnected_sphere _ (0:E) zero_le_one
  apply Module.one_lt_rank_of_one_lt_finrank
  have hdim := Module.finrank_mul_finrank ℝ ℂ E
  rw [Complex.finrank_real_complex] at hdim
  omega

/-- The extension of a compact connected frame family by the unit sphere
of its allowed subspace is connected even when the dimension of that
subspace varies. Closed incidence is the only continuity condition. -/
theorem connected_unit_extensions {B E : Type*} [TopologicalSpace B] [T2Space B]
    [CompactSpace B] [ConnectedSpace B] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (V : B → Submodule ℂ E)
    (hdim : ∀ b, 0 < Module.finrank ℂ (V b))
    (hclosed : IsClosed {p : B × Metric.sphere (0:E) 1 | p.2.val ∈ V p.1}) :
    IsConnected (Set.univ : Set {p : B × Metric.sphere (0:E) 1 // p.2.val ∈ V p.1}) := by
  let X := {p : B × Metric.sphere (0:E) 1 // p.2.val ∈ V p.1}
  let : CompactSpace X := isCompact_iff_compactSpace.mp hclosed.isCompact
  let π : X → B := fun x => x.val.1
  apply connected_of_frame_fibers π (continuous_fst.comp continuous_subtype_val)
  intro b
  let T := Metric.sphere (0 : V b) 1
  have hT : IsConnected T := complex_unit_sphere_connected (V b) (hdim b)
  let inc (v : T) : X :=
    ⟨(b, ⟨v.val.val, by
      have hv := v.property
      change dist v.val 0 = 1 at hv
      rw [dist_zero_right] at hv
      exact (dist_zero_right (v.val.val)).trans hv⟩), v.val.property⟩
  have hinc : Continuous inc := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  have img : Set.range inc = π ⁻¹' {b} := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      rfl
    · rcases x with ⟨⟨b',v⟩,hv⟩
      intro he
      change b'=b at he
      subst b'
      exact ⟨⟨⟨v.val,hv⟩, by simp [T]⟩, rfl⟩
  rw [← img]
  let : ConnectedSpace T := Subtype.connectedSpace hT
  exact isConnected_range hinc

/-- The incidence and dimension conditions in the frame induction follow
from the actual continuous constraint vectors. Dependence among those
vectors can increase the fiber dimension and does not disconnect it. -/
theorem connected_orthogonal_extensions {B E ι : Type*} [TopologicalSpace B] [T2Space B]
    [CompactSpace B] [ConnectedSpace B] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Fintype ι] (v : ι → B → E) (hv : ∀ i, Continuous (v i))
    (hcard : Fintype.card ι < Module.finrank ℂ E) :
    let V := fun b => (Submodule.span ℂ (range (fun i => v i b)))ᗮ
    IsConnected (Set.univ : Set {p : B × Metric.sphere (0:E) 1 // p.2.val ∈ V p.1}) := by
  classical
  let K := fun b => Submodule.span ℂ (range (fun i => v i b))
  apply connected_unit_extensions (fun b => (K b)ᗮ)
  · intro b
    have hc : Module.finrank ℂ (K b) ≤ Fintype.card ι := finrank_range_le_card (fun i => v i b)
    have hd := (K b).finrank_add_finrank_orthogonal
    omega
  · have hmem (b : B) (x : E) : x ∈ (K b)ᗮ ↔ ∀ i, inner ℂ (v i b) x = 0 := by
      constructor
      · intro h i
        exact h _ (Submodule.subset_span ⟨i,rfl⟩)
      · intro h y hy
        have hle : K b ≤ (ℂ ∙ x)ᗮ := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,rfl⟩
          exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_eq_zero_symm.mp (h i))
        exact inner_eq_zero_symm.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (hle hy))
    have hset : {p : B × Metric.sphere (0:E) 1 | p.2.val ∈ (K p.1)ᗮ} =
        ⋂ i, {p : B × Metric.sphere (0:E) 1 | inner ℂ (v i p.1) p.2.val = 0} := by
      ext p
      simp [hmem]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_eq
      (((hv i).comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)) continuous_const

end ManuscriptProofs.PureExclusion
