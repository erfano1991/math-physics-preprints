import ManuscriptProofs.Carleman

open scoped BigOperators

namespace ManuscriptProofs.Carleman

/-- Reciprocals exceeding this value are marked at level j. -/
noncomputable def dyadicThreshold (ν : ℝ) (j : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ ((j : ℝ) * ν)

theorem dyadicThreshold_eq (ν : ℝ) (j : ℕ) :
    dyadicThreshold ν j = 2 * ((2 ^ j : ℕ) : ℝ) ^ ν := by
  unfold dyadicThreshold
  rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_cast

theorem dyadicThreshold_mono {ν : ℝ} (hν : 0 ≤ ν) : Monotone (dyadicThreshold ν) := by
  intro i j hij
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hν)

private theorem scalar_le_threshold_at_count (ν : ℝ) (hν : 0 ≤ ν) (J : ℕ) (x : ℝ)
    (hcut : x ≤ dyadicThreshold ν J) :
    x ≤ dyadicThreshold ν ((Finset.range J).filter (fun j => dyadicThreshold ν j < x)).card := by
  classical
  let S := (Finset.range J).filter (fun j => dyadicThreshold ν j < x)
  have hs : S.card ≤ J := by
    simpa [S] using (Finset.card_filter_le (s := Finset.range J)
      (p := fun j => dyadicThreshold ν j < x))
  by_contra! hc
  have hlt : S.card < J := by
    by_contra! he
    have heq : S.card = J := le_antisymm hs he
    exact (not_lt_of_ge hcut) (heq ▸ hc)
  have hin : Finset.range (S.card + 1) ⊆ S := by
    intro j hj
    have hj' : j ≤ S.card := by
      have := Finset.mem_range.mp hj
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt hj' hlt),
       (dyadicThreshold_mono hν hj').trans_lt hc⟩
  have hbad := Finset.card_le_card hin
  simp only [Finset.card_range] at hbad
  omega

private theorem half_geometric_sum_le (J : ℕ) :
    (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j) ≤ 2 := by
  have h := geom_sum_mul_neg (1 / 2 : ℝ) J
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) J]

private theorem card_filter_cast {α : Type*} (T : Finset α) (p : α → Prop) [DecidablePred p] :
    ((T.filter p).card : ℝ) = ∑ a ∈ T, if p a then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp

/-- The full inverse-divisor product estimate from dyadic counts.
The proof sums the level contributions before exponentiating. -/
theorem inverse_divisor_product_of_dyadic_counts {ι : Type*} (S : Finset ι)
    (x : ι → ℝ) (hx : ∀ i ∈ S, 0 ≤ x i) (ν : ℝ) (hν : 0 ≤ ν) (J : ℕ)
    (hcut : ∀ i ∈ S, x i ≤ dyadicThreshold ν J)
    (hcount : ∀ j ∈ Finset.range J,
      ((S.filter (fun i => dyadicThreshold ν j < x i)).card : ℝ) ≤
        (2 * (S.card : ℝ)) * (1 / 2 : ℝ) ^ j) :
    (∏ i ∈ S, x i) ≤ (2 : ℝ) ^ ((1 + 4 * ν) * (S.card : ℝ)) := by
  classical
  let count (i : ι) := ((Finset.range J).filter (fun j => dyadicThreshold ν j < x i)).card
  have hsum : (∑ i ∈ S, (count i : ℝ)) ≤ 4 * (S.card : ℝ) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ Finset.range J, if dyadicThreshold ν j < x i then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact card_filter_cast (Finset.range J) (fun j => dyadicThreshold ν j < x i)
      _ = ∑ j ∈ Finset.range J, ((S.filter (fun i => dyadicThreshold ν j < x i)).card : ℝ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ =>
          (card_filter_cast S (fun i => dyadicThreshold ν j < x i)).symm
      _ ≤ ∑ j ∈ Finset.range J, (2 * (S.card : ℝ)) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum hcount
      _ = (2 * (S.card : ℝ)) * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * (S.card : ℝ) := by
        have h := mul_le_mul_of_nonneg_left (half_geometric_sum_le J)
          (show 0 ≤ 2 * (S.card : ℝ) by positivity)
        linarith
  have hpoint (i : ι) (hi : i ∈ S) :
      x i ≤ (2 : ℝ) ^ (1 + (count i : ℝ) * ν) := by
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    exact scalar_le_threshold_at_count ν hν J (x i) (hcut i hi)
  calc
    _ ≤ ∏ i ∈ S, (2 : ℝ) ^ (1 + (count i : ℝ) * ν) := Finset.prod_le_prod hx hpoint
    _ = (2 : ℝ) ^ (∑ i ∈ S, (1 + (count i : ℝ) * ν)) :=
      (Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_mul]
      nlinarith [mul_le_mul_of_nonneg_right hsum hν]

end ManuscriptProofs.Carleman
