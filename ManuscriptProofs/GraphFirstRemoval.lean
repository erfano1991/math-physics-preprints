import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ManuscriptProofs.GraphCollector

open MeasureTheory

/-- Conditioning on an exponential first removal produces this convolution;
its derivative is the backward equation at every nonnegative time. The
continuous source can be extended to negative times arbitrarily. -/
theorem first_removal_backward (q : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    let F := fun u : ℝ => ∫ s in 0..u, Real.exp (-q*(u-s)) * g s
    HasDerivAt F (g t - q * F t) t := by
  let h := fun s : ℝ => Real.exp (q*s) * g s
  have hh : Continuous h := ((continuous_const.mul continuous_id).rexp).mul hg
  have hI := intervalIntegral.integral_hasDerivAt_right (hh.intervalIntegrable 0 t)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuousAt
  have he := (((hasDerivAt_id t).const_mul (-q)).exp)
  have hF (u : ℝ) : (∫ s in 0..u, Real.exp (-q*(u-s)) * g s) =
      Real.exp (-q*u) * ∫ s in 0..u, h s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [h]
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
  dsimp only
  simp_rw [hF]
  apply (he.mul hI).congr_deriv
  simp only [h, id_eq, mul_one, neg_mul]
  have hcancel : Real.exp (-(q*t)) * Real.exp (q*t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  linear_combination (g t) * hcancel

end ManuscriptProofs.GraphCollector
