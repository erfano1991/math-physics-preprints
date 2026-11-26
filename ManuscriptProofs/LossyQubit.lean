import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open scoped BigOperators RealInnerProductSpace

namespace ManuscriptProofs.LossyQubit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The axis with its reported sign. -/
def signed (s : Bool) (x : E) : E := if s then x else -x

/-- Data for a branch of a classical sign record. Click coefficients
refer to the two rank-one outcome projectors. -/
structure Branch (E : Type*) where
  weight : ℝ
  bloch : E
  a : ℝ
  b : ℝ
  s : Bool
  t : Bool

/-- The two-setting model in Bloch coordinates.
The three norm inequalities are positivity of the branch effect
and its two differences with the corresponding click effects. -/
def Feasible (x y : E) (η₁ η₂ : ℝ) : Prop :=
  ∃ (n : ℕ) (B : Fin n → Branch E),
    (∀ j, ‖(B j).bloch‖ ≤ (B j).weight ∧
      0 ≤ (B j).a ∧ 0 ≤ (B j).b ∧
      ‖(B j).bloch - (B j).a • signed (B j).s x‖ ≤ (B j).weight - (B j).a ∧
      ‖(B j).bloch - (B j).b • signed (B j).t y‖ ≤ (B j).weight - (B j).b) ∧
    (∑ j, (B j).weight) = 2 ∧ (∑ j, (B j).bloch) = 0 ∧
    (∀ s : Bool, (∑ j, if (B j).s = s then (B j).a else 0) = η₁) ∧
    (∀ t : Bool, (∑ j, if (B j).t = t then (B j).b else 0) = η₂)

private theorem unsigned_distance_le {x y : E} (hxy : 0 ≤ ⟪x, y⟫)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (s t : Bool) :
    ‖a • x - b • y‖ ≤ ‖a • signed s x - b • signed t y‖ := by
  have hadd : ‖a • x - b • y‖ ≤ ‖a • x + b • y‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sub_sq_real, norm_add_sq_real]
    rw [real_inner_smul_left, real_inner_smul_right]
    nlinarith [mul_nonneg ha (mul_nonneg hb hxy)]
  cases s <;> cases t
  · simp only [signed, Bool.false_eq_true, ite_false, smul_neg, neg_sub_neg]
    exact (norm_sub_rev _ _).le
  · simp only [signed, Bool.false_eq_true, ite_false, ite_true, smul_neg]
    rw [show -(a • x) - b • y = -(a • x + b • y) by abel, norm_neg]
    exact hadd
  · simpa [signed, sub_neg_eq_add] using hadd
  · simp [signed]

private theorem common_point {x y : E} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h : ‖x - y‖ ≤ r + s) :
    ∃ v : E, ‖v - x‖ ≤ r ∧ ‖v - y‖ ≤ s := by
  by_cases hd : r + s = 0
  · have hxy : x = y := by
      apply sub_eq_zero.mp
      exact norm_eq_zero.mp (le_antisymm (hd ▸ h) (norm_nonneg _))
    exact ⟨x, by simpa using hr, by simpa [hxy] using hs⟩
  · have hp : 0 < r + s := lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm hd)
    let a := r / (r + s)
    have h₀ : 0 ≤ a := div_nonneg hr hp.le
    have h₁ : 0 ≤ 1 - a := by
      have : a ≤ 1 := (div_le_iff₀ hp).2 (by linarith)
      linarith
    let v := x + a • (y - x)
    refine ⟨v, ?_, ?_⟩
    · have he : v - x = a • (y - x) := by dsimp [v]; abel
      have hscale : a * (r + s) = r := div_mul_cancel₀ r hp.ne'
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg h₀, norm_sub_rev]
      exact (mul_le_mul_of_nonneg_left h h₀).trans_eq hscale
    · have he : v - y = (1 - a) • (x - y) := by dsimp [v]; module
      have hscale : (1 - a) * (r + s) = s := by dsimp [a]; field_simp; ring
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg h₁]
      exact (mul_le_mul_of_nonneg_left h h₁).trans_eq hscale

private theorem sum_two_signs {n : ℕ} (sign : Fin n → Bool) (weight : Fin n → ℝ) (η : ℝ)
    (h : ∀ s : Bool, (∑ j, if sign j = s then weight j else 0) = η) :
    (∑ j, weight j) = 2 * η := by
  have h' := congrArg₂ (· + ·) (h false) (h true)
  rw [← Finset.sum_add_distrib] at h'
  have he : (fun j => (if sign j = false then weight j else 0) +
      if sign j = true then weight j else 0) = weight := by
    funext j
    cases sign j <;> simp
  rw [he] at h'
  linarith

/-- The full unequal-efficiency region, including efficiency zero and one. -/
theorem two_setting_iff (x y : E) (hx : ‖x‖ = 1) (_hy : ‖y‖ = 1)
    (hxy : 0 ≤ ⟪x, y⟫) (η₁ η₂ : ℝ) (he₁ : η₁ ∈ Set.Icc 0 1)
    (he₂ : η₂ ∈ Set.Icc 0 1) :
    Feasible x y η₁ η₂ ↔ ‖η₁ • x - η₂ • y‖ ≤ 2 - η₁ - η₂ := by
  constructor
  · rintro ⟨n, B, hB, hw, _, ha, hb⟩
    have has := sum_two_signs (fun j => (B j).s) (fun j => (B j).a) η₁ ha
    have hbs := sum_two_signs (fun j => (B j).t) (fun j => (B j).b) η₂ hb
    have hdist (j : Fin n) :
        ‖(B j).a • x - (B j).b • y‖ ≤ 2 * (B j).weight - (B j).a - (B j).b := by
      obtain ⟨_, hj₁, hj₂, hj₃, hj₄⟩ := hB j
      apply (unsigned_distance_le hxy hj₁ hj₂ _ _).trans
      have hle : ‖(B j).a • signed (B j).s x - (B j).b • signed (B j).t y‖ ≤
          ‖(B j).bloch - (B j).a • signed (B j).s x‖ +
          ‖(B j).bloch - (B j).b • signed (B j).t y‖ := by
        rw [norm_sub_rev (B j : Branch E).bloch ((B j).a • signed (B j).s x)]
        calc
          _ = ‖((B j).a • signed (B j).s x - (B j).bloch) +
              ((B j).bloch - (B j).b • signed (B j).t y)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have hsum := (norm_sum_le Finset.univ (fun j => (B j).a • x - (B j).b • y)).trans
      (Finset.sum_le_sum fun j _ => hdist j)
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.sum_smul, has, hbs,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, has, hbs] at hsum
    rw [mul_smul, mul_smul, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsum
    linarith
  · intro h
    obtain ⟨v, hv₁, hv₂⟩ := common_point (x := η₁ • x) (y := η₂ • y)
      (r := 1 - η₁) (s := 1 - η₂) (sub_nonneg.mpr he₁.2) (sub_nonneg.mpr he₂.2)
      (by linarith)
    have hv : ‖v‖ ≤ 1 := by
      have htri := norm_add_le (v - η₁ • x) (η₁ • x)
      rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg he₁.1, hx, mul_one] at htri
      linarith
    let B : Fin 2 → Branch E := fun j =>
      if j = 0 then ⟨1, v, η₁, η₂, true, true⟩ else ⟨1, -v, η₁, η₂, false, false⟩
    refine ⟨2, B, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      fin_cases j
      · simp [B, signed, hv, he₁.1, he₂.1, hv₁, hv₂]
      · have hn₁ : ‖-v - η₁ • -x‖ ≤ 1 - η₁ := by
          rw [smul_neg, neg_sub_neg, norm_sub_rev]
          exact hv₁
        have hn₂ : ‖-v - η₂ • -y‖ ≤ 1 - η₂ := by
          rw [smul_neg, neg_sub_neg, norm_sub_rev]
          exact hv₂
        simpa [B, signed] using (show ‖-v‖ ≤ 1 ∧ 0 ≤ η₁ ∧ 0 ≤ η₂ ∧
          ‖-v - η₁ • -x‖ ≤ 1 - η₁ ∧ ‖-v - η₂ • -y‖ ≤ 1 - η₂ from
            ⟨by simpa using hv, he₁.1, he₂.1, hn₁, hn₂⟩)
    · norm_num [B, Fin.sum_univ_two]
    · simp [B, Fin.sum_univ_two]
    · intro s
      cases s <;> simp [B, Fin.sum_univ_two]
    · intro t
      cases t <;> simp [B, Fin.sum_univ_two]


/-- The exact click-capacity calculation for a normalized Bloch branch and
a fixed signed unit axis. The manuscript chooses the sign that maximizes
the inner product. -/
theorem branch_capacity_iff (m n : E) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (r a : ℝ) (hr : 0 ≤ r) (hr' : r < 1) (ha : 0 ≤ a) :
    ‖r • m - a • n‖ ≤ 1 - a ↔
      a ≤ (1 - r ^ 2) / (2 * (1 - r * ⟪m, n⟫)) := by
  have hi : ⟪m, n⟫ ≤ 1 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) m n
    rw [hm, hn, mul_one, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hp : 0 < 2 * (1 - r * ⟪m, n⟫) := by
    have h := mul_le_mul_of_nonneg_left hi hr
    nlinarith
  have hbound : (1 - r ^ 2) / (2 * (1 - r * ⟪m, n⟫)) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [sq_nonneg (1-r), mul_nonneg hr (sub_nonneg.mpr hi)]
  have hs :
      ‖r • m - a • n‖ ^ 2 = r ^ 2 - 2 * r * a * ⟪m, n⟫ + a ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, hm, hn, mul_one, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg ha,
      real_inner_smul_left, real_inner_smul_right]
    ring
  constructor
  · intro h
    have hnonneg : 0 ≤ 1 - a := (norm_nonneg _).trans h
    have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr h
    rw [hs] at hsq
    apply (le_div_iff₀ hp).mpr
    nlinarith
  · intro h
    have hnonneg : 0 ≤ 1 - a := sub_nonneg.mpr (h.trans hbound)
    apply (sq_le_sq₀ (norm_nonneg _) hnonneg).mp
    rw [hs]
    have h' := (le_div_iff₀ hp).mp h
    nlinarith


/-- Rank-one branch capacity. Positive click weight is possible precisely
on the same oriented ray, and its coefficient is at most one. -/
theorem rank_one_branch_capacity_iff (m n : E) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    ‖m - a • n‖ ≤ 1 - a ↔ a = 0 ∨ n = m ∧ a ≤ 1 := by
  by_cases haz : a = 0
  · simp [haz, hm]
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hip : ⟪m, n⟫ ≤ 1 := by
    have ht := norm_inner_le_norm (𝕜 := ℝ) m n
    rw [hm, hn, mul_one, Real.norm_eq_abs] at ht
    exact (le_abs_self _).trans ht
  constructor
  · intro h
    have hbound : a ≤ 1 := by linarith [((norm_nonneg _).trans h : 0 ≤ 1 - a)]
    have hs := (sq_le_sq₀ (norm_nonneg _) (sub_nonneg.mpr hbound)).mpr h
    rw [norm_sub_sq_real, hm, norm_smul, hn, mul_one,
      Real.norm_eq_abs, abs_of_nonneg ha, real_inner_smul_right] at hs
    have hmul : a * 1 ≤ a * ⟪m, n⟫ := by nlinarith
    have hge : 1 ≤ ⟪m, n⟫ := (mul_le_mul_iff_right₀ hapos).mp hmul
    have he : ⟪m, n⟫ = 1 := le_antisymm hip hge
    have hz : ‖m - n‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hm, hn, he]; norm_num
    have hz' : ‖m - n‖ = 0 := by nlinarith
    have hmn : m = n := sub_eq_zero.mp (norm_eq_zero.mp hz')
    exact Or.inr ⟨hmn.symm, hbound⟩
  · rintro (h | ⟨haxis, hbound⟩)
    · simp [h, hm]
    · rw [haxis, show m - a • m = (1 - a) • m by
        rw [sub_smul, one_smul], norm_smul, hm, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hbound)]

/-- Optimizing the reported sign gives the endpoint capacity
one on the same unoriented axis and zero otherwise. -/
theorem rank_one_branch_signed_iff (m n : E) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (∃ s : Bool, ‖m - a • signed s n‖ ≤ 1 - a) ↔
      a = 0 ∨ (n = m ∨ n = -m) ∧ a ≤ 1 := by
  constructor
  · rintro ⟨s, h⟩
    have hsn : ‖signed s n‖ = 1 := by cases s <;> simp [signed, hn]
    rcases (rank_one_branch_capacity_iff m (signed s n) hm hsn a ha).mp h with hz | ⟨hs, hle⟩
    · exact Or.inl hz
    · refine Or.inr ⟨?_, hle⟩
      cases s
      · have hneg : -n = m := by simpa [signed] using hs
        exact Or.inr (neg_eq_iff_eq_neg.mp hneg)
      · exact Or.inl (by simpa [signed] using hs)
  · rintro (rfl | ⟨hs, hle⟩)
    · exact ⟨true, by simp [hm]⟩
    · rcases hs with he | he
      · refine ⟨true, ?_⟩
        simpa [signed] using (rank_one_branch_capacity_iff m n hm hn a ha).mpr
          (Or.inr ⟨he, hle⟩)
      · refine ⟨false, ?_⟩
        simpa [signed] using (rank_one_branch_capacity_iff m (-n) hm (by simpa using hn) a ha).mpr
          (Or.inr ⟨by rw [he, neg_neg], hle⟩)

end ManuscriptProofs.LossyQubit
