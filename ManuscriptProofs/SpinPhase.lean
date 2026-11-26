import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith

open Set Filter Topology

namespace ManuscriptProofs.SpinWigner

/-- The lifted logarithm is given locally by a single smooth branch of log
near 1. This supplies the phase in the spin proof without any global choice
of a principal argument. -/
theorem continuous_log_with_local_formula {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (f : X → ℂ)
    (hf : Continuous f) (hn : ∀ x, f x ≠ 0) (x₀ : X) :
    ∃ g : X → ℂ, Continuous g ∧ (∀ x, Complex.exp (g x) = f x) ∧
      ∀ x, ∀ᶠ y in 𝓝 x, g y = g x + Complex.log (f y / f x) := by
  obtain ⟨g, ⟨_, he⟩, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨f,hf⟩ : C(X,ℂ)) (a₀ := x₀) (Complex.exp_log (hn x₀)) (fun x => hn x)
  have hex x : Complex.exp (g x) = f x := congrFun he x
  refine ⟨g, g.continuous, hex, ?_⟩
  intro x
  have hc : Continuous (fun y => (g y - g x).im) :=
    Complex.continuous_im.comp (g.continuous.sub continuous_const)
  have hh : ∀ᶠ y in 𝓝 x, (g y-g x).im ∈ Ioo (-Real.pi) Real.pi := by
    apply hc.continuousAt.eventually_mem (isOpen_Ioo.mem_nhds ?_)
    simp [Real.pi_pos]
  filter_upwards [hh] with y hy
  rw [← hex y, ← hex x, ← Complex.exp_sub, Complex.log_exp hy.1 hy.2.le]
  abel

end ManuscriptProofs.SpinWigner
