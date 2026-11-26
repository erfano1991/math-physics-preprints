import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FieldSimp

namespace ManuscriptProofs.PureExclusion

/-- One step in the constrained-frame tower: a continuous surjection
from a compact frame space to a connected Hausdorff base with connected fibers. -/
theorem connected_of_frame_fibers {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] (f : X → Y) (hf : Continuous f)
    (h : ∀ y, IsConnected (f ⁻¹' {y})) : IsConnected (Set.univ : Set X) := by
  have hsur : Function.Surjective f := fun y => (h y).nonempty
  have hq := hf.isClosedMap.isQuotientMap hf hsur
  simpa using hq.isCoinducing.isConnected_preimage_of_isClosed h isClosed_univ isConnected_univ

/-- The final intermediate value and complex phase in the independent-state
case. The equality includes both terms vanishing. -/
theorem exclusion_phase_on_connected_family {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (a b : X → ℂ) (ha : Continuous a) (hb : Continuous b)
    (x y : X) (hx : ‖a x‖ ≤ ‖b x‖) (hy : ‖b y‖ ≤ ‖a y‖) :
    ∃ u : X, ∃ z : ℂ, ‖z‖ = 1 ∧ a u + z * b u = 0 := by
  obtain ⟨u, hu⟩ := intermediate_value_univ₂ ha.norm hb.norm hx hy
  by_cases h : b u = 0
  · have h' : a u = 0 := norm_eq_zero.mp (by simpa [h] using hu)
    exact ⟨u, 1, norm_one, by simp [h, h']⟩
  · refine ⟨u, -a u / b u, ?_, ?_⟩
    · rw [norm_div, norm_neg, hu, div_self (norm_ne_zero_iff.mpr h)]
    · rw [div_mul_cancel₀ _ h, add_neg_cancel]

end ManuscriptProofs.PureExclusion
