import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ManuscriptProofs.Optical

open scoped InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Apply Cauchy--Schwarz to the two vectors in the both-no-click
parent summand after inserting the coherent-state matrix elements. -/
theorem fixed_separation_necessity (x y : E) (s t₁ t₂ : ℝ) (hs : 0 < s)
    (hxy : ‖inner ℂ x y‖ = Real.exp (-s / 2))
    (hx : ‖x‖ = Real.exp (-t₂*s/2)) (hy : ‖y‖ = Real.exp (-t₁*s/2)) :
    t₁ + t₂ ≤ 1 := by
  have h := norm_inner_le_norm (𝕜 := ℂ) x y
  rw [hxy, hx, hy, ← Real.exp_add, Real.exp_le_exp] at h
  by_contra! hh
  nlinarith [mul_pos hs (sub_pos.mpr hh)]

/-- Under saturation, retaining any subcollection of the parent outcomes
multiplies the cross matrix element by a real number between zero and one.
Here T is the coordinate projection (the statement allows any contraction). -/
theorem saturation_subcollection (x y : E) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ‖inner ℂ x y‖ = ‖x‖ * ‖y‖) (T : E →ₗ[ℂ] F) (hT : ‖T x‖ ≤ ‖x‖) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ inner ℂ (T x) (T y) = (r : ℂ) * inner ℂ x y := by
  obtain ⟨c, _, rfl⟩ := (norm_inner_eq_norm_iff (𝕜 := ℂ) hx hy).mp h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖T x‖^2 / ‖x‖^2, by positivity, ?_, ?_⟩
  · exact (div_le_one (sq_pos_of_pos hn)).2 (sq_le_sq' (by linarith [norm_nonneg (T x)]) hT)
  · rw [map_smul, inner_smul_right, inner_smul_right, inner_self_eq_norm_sq_to_K,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_pow]
    have hne : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
    change c * (‖T x‖ : ℂ)^2 =
      ((‖T x‖ : ℂ)^2 / (‖x‖ : ℂ)^2) * (c * (‖x‖ : ℂ)^2)
    field_simp

end ManuscriptProofs.Optical
