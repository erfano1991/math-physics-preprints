import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

open scoped BigOperators ComplexOrder MatrixOrder

namespace ManuscriptProofs.Quantum

abbrev Operator (d : Type*) := Matrix d d ℂ

/-- A finite positive-operator-valued measure, acting on complex matrices. -/
structure POVM (d Ω : Type*) [Fintype d] [DecidableEq d] [Fintype Ω] where
  effect : Ω → Operator d
  pos (o : Ω) : (effect o).PosSemidef
  sum_eq_one : ∑ o, effect o = 1

variable {d Ω Λ : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Fintype Λ]

/-- The effect of a finite event. -/
def POVM.event (M : POVM d Ω) (s : Finset Ω) : Operator d := ∑ o ∈ s, M.effect o

theorem POVM.event_pos (M : POVM d Ω) (s : Finset Ω) : (M.event s).PosSemidef :=
  Matrix.posSemidef_sum s (fun i _ => M.pos i)

theorem POVM.event_mono (M : POVM d Ω) {s t : Finset Ω} (h : s ⊆ t) :
    M.event s ≤ M.event t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ =>
    Matrix.nonneg_iff_posSemidef.mpr (M.pos i)

@[simp] theorem POVM.event_univ (M : POVM d Ω) : M.event Finset.univ = 1 :=
  M.sum_eq_one

theorem POVM.effect_le_event (M : POVM d Ω) {s : Finset Ω} {o : Ω} (ho : o ∈ s) :
    M.effect o ≤ M.event s := by
  classical
  simpa [event] using M.event_mono (Finset.singleton_subset_iff.mpr ho)

/-- Classical relabeling groups the original effects by their output. -/
noncomputable def POVM.postprocess (M : POVM d Ω) (f : Ω → Λ) : POVM d Λ := by
  classical
  exact {
    effect l := M.event (Finset.univ.filter (fun o => f o = l))
    pos _ := M.event_pos _
    sum_eq_one := by
      rw [← M.sum_eq_one]
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) M.effect }

@[simp] theorem POVM.postprocess_effect [DecidableEq Λ] (M : POVM d Ω)
    (f : Ω → Λ) (l : Λ) :
    (M.postprocess f).effect l = M.event (Finset.univ.filter (fun o => f o = l)) := by
  change M.event _ = M.event _
  refine congrArg M.event ?_
  ext o
  simp

/-- A joint POVM is one whose coordinate marginals are the specified POVMs. -/
def Compatible {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] (M : (i : ι) → POVM d (A i)) : Prop :=
  ∃ G : POVM d ((i : ι) → A i),
    ∀ i a, (G.postprocess (fun z => z i)).effect a = (M i).effect a

/-- A single parent with deterministic response maps gives a joint POVM. -/
theorem compatible_of_parent {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ i, Fintype (A i)] {M : (i : ι) → POVM d (A i)}
    (G : POVM d Ω) (f : (i : ι) → Ω → A i)
    (h : ∀ i a, (G.postprocess (f i)).effect a = (M i).effect a) : Compatible M := by
  classical
  refine ⟨G.postprocess (fun o i => f i o), fun i a => ?_⟩
  rw [← h i a]
  simp only [POVM.postprocess, POVM.event]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun o j => f j o)
    (s := Finset.univ.filter fun o => f i o = a)
    (t := Finset.univ.filter fun z => z i = a) _ G.effect]
  · apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun e => ⟨(congrFun e i).trans (Finset.mem_filter.mp hz).2, e⟩, fun e => e.2⟩
  · intro o ho
    simpa using ho

end ManuscriptProofs.Quantum
