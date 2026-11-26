import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith

open MeasureTheory Set

namespace ManuscriptProofs.SpinWigner

/-- The overlap step for spin Wigner functions. The two inputs are Wigner
densities for a state and a rotation of it. The orthogonal rotation gives
zero overlap, the spherical harmonic identity theorem gives density of
the nonzero set, and rotations are homeomorphisms. -/
theorem negative_open_set_of_zero_overlap {S : Type*} [TopologicalSpace S] [Nonempty S]
    [MeasurableSpace S] (μ : Measure S) [μ.IsOpenPosMeasure]
    (w : S → ℝ) (g : S ≃ₜ S) (hw : Continuous w)
    (hdense : Dense (Function.support w))
    (hi : Integrable (fun x => w x * w (g x)) μ)
    (hoverlap : (∫ x, w x * w (g x) ∂μ) = 0) :
    ∃ U : Set S, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, w x < 0 := by
  suffices hex : ∃ x, w x < 0 by
    obtain ⟨x, hx⟩ := hex
    exact ⟨{x | w x < 0}, isOpen_lt hw continuous_const, ⟨x, hx⟩, fun _ hx => hx⟩
  by_contra! hnonneg
  have hopen : IsOpen (Function.support w) := by
    convert isOpen_lt (f := fun _ : S => (0 : ℝ)) continuous_const hw using 1
    ext x
    change w x ≠ 0 ↔ 0 < w x
    exact ⟨fun h => lt_of_le_of_ne (hnonneg x) h.symm, ne_of_gt⟩
  have hd' : Dense (g ⁻¹' Function.support w) :=
    hdense.preimage g.isOpenMap
  obtain ⟨x, hgx, hx⟩ := hdense.inter_open_nonempty _
    (hopen.preimage g.continuous) hd'.nonempty
  let f : S → ℝ := fun x => w x * w (g x)
  have hf : Continuous f := hw.mul (hw.comp g.continuous)
  have hn : ∀ x, 0 ≤ f x := fun x => mul_nonneg (hnonneg x) (hnonneg (g x))
  have hne : (Function.support f).Nonempty := by
    exact ⟨x, mul_ne_zero hx hgx⟩
  have ho : IsOpen (Function.support f) := by
    convert isOpen_lt (f := fun _ : S => (0 : ℝ)) continuous_const hf using 1
    ext x
    change f x ≠ 0 ↔ 0 < f x
    exact ⟨fun h => lt_of_le_of_ne (hn x) h.symm, ne_of_gt⟩
  have hpos := (integral_pos_iff_support_of_nonneg hn hi).mpr (ho.measure_pos μ hne)
  exact (ne_of_gt hpos) hoverlap

private theorem negPart_mul_le (a b M : ℝ) (hM : 0 ≤ M) (ha : a ≤ M) (hb : b ≤ M) :
    max (-(a * b)) 0 ≤ M * (max (-a) 0 + max (-b) 0) := by
  by_cases ha₀ : 0 ≤ a <;> by_cases hb₀ : 0 ≤ b
  · rw [max_eq_right (neg_nonpos.mpr (mul_nonneg ha₀ hb₀))]
    positivity
  · have hbn : b ≤ 0 := le_of_not_ge hb₀
    rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos ha₀ hbn)),
      max_eq_right (neg_nonpos.mpr ha₀), max_eq_left (neg_nonneg.mpr hbn), zero_add, ← mul_neg]
    exact mul_le_mul_of_nonneg_right ha (neg_nonneg.mpr hbn)
  · have han : a ≤ 0 := le_of_not_ge ha₀
    rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg han hb₀)),
      max_eq_left (neg_nonneg.mpr han), max_eq_right (neg_nonpos.mpr hb₀), add_zero, ← neg_mul]
    rw [mul_comm (-a) b]
    exact mul_le_mul_of_nonneg_right hb (neg_nonneg.mpr han)
  · rw [max_eq_right (neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos
      (le_of_not_ge ha₀) (le_of_not_ge hb₀)))]
    positivity

/-- The negative-volume estimate from a zero signed overlap. Measure
preservation makes the two negative-part integrals equal. -/
theorem abs_overlap_le_negative_volume {S : Type*} [MeasurableSpace S] (μ : Measure S)
    (w : S → ℝ) (g : S ≃ᵐ S) (hg : MeasurePreserving g μ μ)
    (M : ℝ) (hM : 0 ≤ M) (hwM : ∀ x, w x ≤ M)
    (hw : Integrable w μ) (hi : Integrable (fun x => w x * w (g x)) μ)
    (hzero : (∫ x, w x * w (g x) ∂μ) = 0) :
    (∫ x, |w x * w (g x)| ∂μ) ≤ 4 * M * ∫ x, max (-w x) 0 ∂μ := by
  have hp : Integrable (fun x => max (-w x) 0) μ := by
    simpa only [Real.coe_toNNReal', Pi.neg_apply] using hw.neg.real_toNNReal
  have hp' : Integrable (fun x => max (-w (g x)) 0) μ := hg.integrable_comp_of_integrable hp
  have hprod : Integrable (fun x => max (-(w x * w (g x))) 0) μ := by
    simpa only [Real.coe_toNNReal', Pi.neg_apply] using hi.neg.real_toNNReal
  have h : (∫ x, max (-(w x * w (g x))) 0 ∂μ) ≤
      ∫ x, M * (max (-w x) 0 + max (-w (g x)) 0) ∂μ :=
    integral_mono hprod ((hp.add hp').const_mul M) fun x =>
      negPart_mul_le (w x) (w (g x)) M hM (hwM x) (hwM (g x))
  rw [integral_const_mul, integral_add hp hp', hg.integral_comp' (fun x => max (-w x) 0)] at h
  rw [integral_abs_eq_two_mul_integral_negPart_add_integral hi, hzero, add_zero]
  simp only [NegPart.negPart]
  nlinarith

end ManuscriptProofs.SpinWigner
