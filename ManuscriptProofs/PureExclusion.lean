import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ManuscriptProofs.PureExclusion

/-- The exact equivalence of the qutrit square-root spectral inequality
and the purity inequality. Zero eigenvalues are included. -/
theorem qutrit_sqrt_triangle_iff_purity (a b c : ℝ) (h₁ : c ≤ b) (h₂ : b ≤ a) (h₃ : 0 ≤ c)
    (htrace : a + b + c = 1) :
    Real.sqrt a ≤ Real.sqrt b + Real.sqrt c ↔ a ^ 2 + b ^ 2 + c ^ 2 ≤ 1 / 2 := by
  have hb : 0 ≤ b := h₃.trans h₁
  have ha : 0 ≤ a := hb.trans h₂
  let x := Real.sqrt a
  let y := Real.sqrt b
  let z := Real.sqrt c
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have hxy : y ≤ x := Real.sqrt_le_sqrt h₂
  have hyz : z ≤ y := Real.sqrt_le_sqrt h₁
  have ha' : x ^ 2 = a := Real.sq_sqrt ha
  have hb' : y ^ 2 = b := Real.sq_sqrt hb
  have hc' : z ^ 2 = c := Real.sq_sqrt h₃
  have hheron :
      (x + y + z) * (x + y - z) * (x - y + z) * (-x + y + z) =
        1 - 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    calc
      _ = (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 - 2 * ((x ^ 2) ^ 2 + (y ^ 2) ^ 2 + (z ^ 2) ^ 2) := by ring
      _ = _ := by rw [ha', hb', hc', htrace]; ring
  change x ≤ y + z ↔ _
  constructor
  · intro h
    have hpos := mul_nonneg
      (mul_nonneg (mul_nonneg (show 0 ≤ x + y + z by linarith)
          (show 0 ≤ x + y - z by linarith)) (show 0 ≤ x - y + z by linarith))
      (show 0 ≤ -x + y + z by linarith)
    rw [hheron] at hpos
    linarith
  · intro h
    by_contra! hn
    have hprod := mul_neg_of_pos_of_neg
      (mul_pos (mul_pos (show 0 < x + y + z by linarith)
        (show 0 < x + y - z by linarith)) (show 0 < x - y + z by linarith))
      (show -x + y + z < 0 by linarith)
    rw [hheron] at hprod
    linarith

/-- The weighted Cauchy–Schwarz step for the negative eigenspace of the
dual variable. It allows zero eigenvalues in the mixture. -/
theorem weighted_spectral_sum_bound {ι : Type*} (J : Finset ι) (eigen t : ι → ℝ)
    (heigen : ∀ j ∈ J, 0 ≤ eigen j) (ht : ∀ j ∈ J, 0 < t j) :
    (∑ j ∈ J, Real.sqrt (eigen j)) ^ 2 ≤
      (∑ j ∈ J, t j) * (∑ j ∈ J, eigen j / t j) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul J
    (fun j hj => (ht j hj).le) (fun j hj => div_nonneg (heigen j hj) (ht j hj).le)
  intro j hj
  rw [Real.sq_sqrt (heigen j hj), mul_comm (t j), div_mul_cancel₀ _ (ht j hj).ne']

/-- The sharp scalar upper bound in the spectral exclusion formula,
given the trace inequality from dual feasibility and rearrangement. -/
theorem spectral_dual_upper_bound (a T L S : ℝ) (hT : 0 < T) (hTa : T < a)
    (hL : 0 ≤ L) (hS : 0 ≤ S) (htrace : 1 ≤ L / a - S ^ 2 / T) :
    S < Real.sqrt L ∧ a - T ≤ (Real.sqrt L - S) ^ 2 := by
  have ha : 0 < a := hT.trans hTa
  have hq : S ^ 2 / T < L / a := by linarith
  have hq' : S ^ 2 / a < L / a :=
    (div_le_div_of_nonneg_left (sq_nonneg S) hT hTa.le).trans_lt hq
  have hs : S ^ 2 < L := (div_lt_div_iff_of_pos_right ha).mp hq'
  have hr : S < Real.sqrt L := by
    apply (sq_lt_sq₀ hS (Real.sqrt_nonneg L)).mp
    rwa [Real.sq_sqrt hL]
  refine ⟨hr, ?_⟩
  have hprod : a - T ≤ (a - T) * (L / a - S ^ 2 / T) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTa.le) (sub_nonneg.mpr htrace)]
  let b := Real.sqrt L
  have hb : b ^ 2 = L := Real.sq_sqrt hL
  have he : (b - S) ^ 2 - (a - T) * (b ^ 2 / a - S ^ 2 / T) =
      (T * b - a * S) ^ 2 / (a * T) := by
    field_simp [ha.ne', hT.ne']
    ring
  rw [hb] at he
  have hx := div_nonneg (sq_nonneg (T * b - a * S)) (mul_nonneg ha.le hT.le)
  exact hprod.trans (sub_nonneg.mp (he.symm ▸ hx))

/-- The top square root is counted once in the trace square root. -/
theorem top_excess_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (eigen : ι → ℝ) (top : ι) :
    2 * Real.sqrt (eigen top) - (∑ i, Real.sqrt (eigen i)) =
      Real.sqrt (eigen top) - ∑ i ∈ Finset.univ.erase top, Real.sqrt (eigen i) := by
  rw [← Finset.sum_erase_add Finset.univ (fun i => Real.sqrt (eigen i)) (Finset.mem_univ top)]
  ring

/-- Positive spectral excess makes the distinguished eigenvalue strictly larger
than every other eigenvalue, with eigenvalues indexed by multiplicity. -/
theorem strict_top_of_positive_excess {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eigen : ι → ℝ) (top : ι)
    (hexcess : 0 < 2 * Real.sqrt (eigen top) - ∑ j, Real.sqrt (eigen j))
    {i : ι} (hi : i ≠ top) : eigen i < eigen top := by
  rw [top_excess_eq] at hexcess
  have hterm : Real.sqrt (eigen i) ≤ ∑ j ∈ Finset.univ.erase top, Real.sqrt (eigen j) :=
    Finset.single_le_sum (fun j _ => Real.sqrt_nonneg (eigen j))
      (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact lt_of_not_ge fun h => (not_le_of_gt (hterm.trans_lt (sub_pos.mp hexcess)))
    (Real.sqrt_le_sqrt h)

/-- Trace normalization of the spectral witness in an eigenbasis.
The diagonal entries are those of δ(2P - I)R⁻¹ᐟ². -/
theorem spectral_witness_trace_normalization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (eigen : ι → ℝ) (top : ι) (hpos : ∀ i, 0 < eigen i)
    (hexcess : 0 < 2 * Real.sqrt (eigen top) - ∑ i, Real.sqrt (eigen i)) :
    let δ := 2 * Real.sqrt (eigen top) - ∑ i, Real.sqrt (eigen i)
    let k (i : ι) := δ * (if i = top then 1 else -1) / Real.sqrt (eigen i)
    (∑ i, k i * eigen i) = δ ^ 2 ∧ (∑ i, (k i)⁻¹) = 1 := by
  let r (i : ι) := Real.sqrt (eigen i)
  let σ (i : ι) : ℝ := if i = top then 1 else -1
  let δ := 2 * r top - ∑ i, r i
  let k (i : ι) := δ * σ i / r i
  change (∑ i, k i * eigen i) = δ ^ 2 ∧ (∑ i, (k i)⁻¹) = 1
  have hδ : δ ≠ 0 := ne_of_gt hexcess
  have hr (i : ι) : r i ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hpos i))
  have hs : (∑ i, σ i * r i) = δ := by
    calc
      _ = (∑ i ∈ Finset.univ.erase top, σ i * r i) + σ top * r top :=
        (Finset.sum_erase_add Finset.univ (fun i => σ i * r i) (Finset.mem_univ top)).symm
      _ = (∑ i ∈ Finset.univ.erase top, -r i) + r top := by
        rw [show σ top * r top = r top by simp [σ]]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp [σ, (Finset.mem_erase.mp hi).1]
      _ = δ := by
        rw [Finset.sum_neg_distrib]
        change _ = 2 * Real.sqrt (eigen top) - ∑ i, Real.sqrt (eigen i)
        rw [top_excess_eq]
        ring
  have hpair (i : ι) : k i * eigen i = δ * (σ i * r i) := by
    have hi : (r i) ^ 2 = eigen i := Real.sq_sqrt (hpos i).le
    rw [← hi]
    dsimp [k]
    field_simp [hr i]
  have hinv (i : ι) : (k i)⁻¹ = δ⁻¹ * (σ i * r i) := by
    dsimp [k]
    rw [inv_div]
    by_cases hi : i = top <;> simp [σ, hi, div_eq_mul_inv, mul_comm]
  constructor
  · simp only [hpair, ← Finset.mul_sum, hs, pow_two]
  · simp only [hinv, ← Finset.mul_sum, hs, inv_mul_cancel₀ hδ]

end ManuscriptProofs.PureExclusion
