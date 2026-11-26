import ManuscriptProofs.Quantum.POVM
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace ManuscriptProofs.Quantum

private theorem annihilates_of_le {d : Type*} [Fintype d] {A B : Operator d}
    (hA : A.PosSemidef) (h : A ≤ B) {x : d → ℂ} (hx : B *ᵥ x = 0) :
    A *ᵥ x = 0 := by
  apply (hA.dotProduct_mulVec_zero_iff x).mp
  have h₀ := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  rw [Matrix.sub_mulVec, hx, zero_sub, dotProduct_neg] at h₀
  exact le_antisymm (neg_nonneg.mp h₀) (hA.dotProduct_mulVec_nonneg x)

section Merged

variable {d J ι : Type*} [Fintype d] [DecidableEq d]
  [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]

/-- A measurement reports a retained label or a single residual outcome.
The common alphabet is padded by zero effects for the labels it does not retain. -/
noncomputable def merged (P : J → Operator d) (hP : ∀ j, (P j).PosSemidef)
    (S : Finset J) (hS : (∑ j ∈ S, P j) ≤ 1) : POVM d (Option J) where
  effect
    | none => 1 - ∑ j ∈ S, P j
    | some j => if j ∈ S then P j else 0
  pos o := by
    cases o with
    | none => exact Matrix.le_iff.mp hS
    | some j =>
        change (if j ∈ S then P j else 0).PosSemidef
        by_cases hj : j ∈ S
        · simpa [hj] using hP j
        · simpa [hj] using (Matrix.PosSemidef.zero : (0 : Operator d).PosSemidef)
  sum_eq_one := by
    rw [Fintype.sum_option]
    change (1 - ∑ j ∈ S, P j) + (∑ j, if j ∈ S then P j else 0) = 1
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    abel

omit [DecidableEq J] in
private theorem eq_effect_of_eq_some {A B : POVM d (Option J)}
    (h : ∀ j, A.effect (some j) = B.effect (some j)) (o : Option J) :
    A.effect o = B.effect o := by
  cases o with
  | some j => exact h j
  | none =>
      have hA := A.sum_eq_one
      have hB := B.sum_eq_one
      rw [Fintype.sum_option] at hA hB
      simp only [h] at hA
      exact add_right_cancel (hA.trans hB.symm)

/-- The union criterion for reported effects with pairwise disjoint positive
lower bounds. The alphabet, marginals and parent use positive complex matrices. -/
theorem merged_compatible_iff (P : J → Operator d) (hP : ∀ j, (P j).PosSemidef)
    (hex : ∀ j k, j ≠ k → ∀ H : Operator d, H.PosSemidef → H ≤ P j → H ≤ P k → H = 0)
    (A : ι → Finset J) (hA : ∀ i, (∑ j ∈ A i, P j) ≤ 1) :
    Compatible (fun i => merged P hP (A i) (hA i)) ↔
      (∑ j ∈ Finset.univ.biUnion A, P j) ≤ 1 := by
  classical
  set U := Finset.univ.biUnion A
  have hU (j : J) : j ∈ U ↔ ∃ i, j ∈ A i := by simp [U]
  constructor
  · rintro ⟨G, hG⟩
    choose chooseCoord hcoord using fun j : U => (hU j).mp j.property
    let B (j : U) : Finset (ι → Option J) :=
      Finset.univ.filter (fun z => z (chooseCoord j) = some (j : J))
    have hB (j : U) : G.event (B j) = P j := by
      simpa [B, POVM.postprocess, merged, hcoord j] using hG (chooseCoord j) (some (j : J))
    have hsingle (z : ι → Option J) (hz : G.effect z ≠ 0) :
        ∀ j k : U, z ∈ B j → z ∈ B k → j = k := by
      intro j k hj hk
      by_contra hne
      apply hz
      apply hex j k (fun h => hne (Subtype.ext h)) (G.effect z) (G.pos z)
      · simpa [hB j] using G.effect_le_event hj
      · simpa [hB k] using G.effect_le_event hk
    calc
      (∑ j ∈ U, P j) = ∑ j : U, P j :=
        (Finset.sum_attach U P).symm
      _ = ∑ j : U, G.event (B j) := by simp only [hB]
      _ = ∑ j : U, ∑ z : ι → Option J, if z ∈ B j then G.effect z else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.sum_filter]
        congr 1
        ext z
        simp
      _ = ∑ z : ι → Option J, ∑ j : U, if z ∈ B j then G.effect z else 0 :=
        Finset.sum_comm
      _ ≤ ∑ z, G.effect z := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : G.effect z = 0
        · simp [hz]
        by_cases h : ∃ j : U, z ∈ B j
        · obtain ⟨j, hj⟩ := h
          rw [Finset.sum_eq_single j]
          · simp [hj]
          · intro k _ hk
            simp [show z ∉ B k from fun hzk => hk (hsingle z hz k j hzk hj)]
          · simp
        · have hz' : ∀ j : U, z ∉ B j := fun j h' => h ⟨j, h'⟩
          simpa [hz'] using Matrix.nonneg_iff_posSemidef.mpr (G.pos z)
      _ = 1 := G.sum_eq_one
  · intro h
    let G := merged P hP U h
    let f (i : ι) (o : Option J) : Option J :=
      o.bind (fun j => if j ∈ A i then some j else none)
    refine compatible_of_parent G f (fun i o => eq_effect_of_eq_some (fun j => ?_) o)
    have hf (z : Option J) (j : J) : f i z = some j ↔ z = some j ∧ j ∈ A i := by
      cases z with
      | none => simp [f]
      | some k =>
          by_cases e : k = j
          · subst k
            by_cases hk : j ∈ A i <;> simp [f, hk]
          · by_cases hk : k ∈ A i <;> simp [f, hk, e]
    rw [POVM.postprocess_effect]
    by_cases hj : j ∈ A i
    · have hu : j ∈ U := (hU j).mpr ⟨i, hj⟩
      have hfilter : Finset.univ.filter (fun z => f i z = some j) = {some j} := by
        ext z
        simp [hf, hj]
      simp [hfilter, POVM.event, G, merged, hj, hu]
    · have hfilter : Finset.univ.filter (fun z => f i z = some j) = ∅ := by
        ext z
        simp [hf, hj]
      simp [hfilter, POVM.event, merged, hj]

end Merged

section ExplicitRays

private def ray (t : ℝ) : Fin 2 → ℂ := ![1, (t : ℂ)]
private def perpendicular (t : ℝ) : Fin 2 → ℂ := ![-(t : ℂ), 1]

/-- The rank-one projector onto the rational ray through \((1,t)\) when
\`t\` is rational. -/
noncomputable def rayProjection (t : ℝ) : Operator (Fin 2) :=
  (1 / (1 + t ^ 2) : ℝ) • Matrix.vecMulVec (ray t) (star (ray t))

private noncomputable def perpendicularProjection (t : ℝ) : Operator (Fin 2) :=
  (1 / (1 + t ^ 2) : ℝ) • Matrix.vecMulVec (perpendicular t) (star (perpendicular t))

theorem rayProjection_pos (t : ℝ) : (rayProjection t).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (ray t)).smul (by positivity)

private theorem rayProjection_add_complement (t : ℝ) :
    rayProjection t + perpendicularProjection t = 1 := by
  have h : (1 + (t : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (show (1 + t ^ 2) ≠ 0 by positivity)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rayProjection, perpendicularProjection, ray, perpendicular, Matrix.vecMulVec,
      Complex.real_smul, Complex.ofReal_add, Complex.ofReal_pow] <;>
    field_simp [h]; ring

theorem rayProjection_le_one (t : ℝ) : rayProjection t ≤ 1 := by
  apply Matrix.le_iff.mpr
  rw [← rayProjection_add_complement t, add_sub_cancel_left]
  exact (Matrix.posSemidef_vecMulVec_self_star (perpendicular t)).smul (by positivity)

private theorem rayProjection_perpendicular (t : ℝ) :
    rayProjection t *ᵥ perpendicular t = 0 := by
  have h : star (ray t) ⬝ᵥ perpendicular t = 0 := by
    simp [ray, perpendicular, dotProduct, Fin.sum_univ_two]
  rw [rayProjection, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, h]
  simp

theorem distinct_ray_lower_bound {s t c : ℝ} (hst : s ≠ t)
    {H : Operator (Fin 2)} (hH : H.PosSemidef)
    (hs : H ≤ c • rayProjection s) (ht : H ≤ c • rayProjection t) : H = 0 := by
  have hz (u : ℝ) (h : H ≤ c • rayProjection u) : H *ᵥ perpendicular u = 0 := by
    apply annihilates_of_le hH h
    rw [Matrix.smul_mulVec, rayProjection_perpendicular, smul_zero]
  ext i j
  have hs₁ := congrFun (hz s hs) i
  have ht₁ := congrFun (hz t ht) i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, perpendicular] at hs₁ ht₁
  have hp : H i 0 * ((s : ℂ) - (t : ℂ)) = 0 := by linear_combination ht₁ - hs₁
  have hzero : H i 0 = 0 := (mul_eq_zero.mp hp).resolve_right
    (sub_ne_zero.mpr (Complex.ofReal_injective.ne hst))
  have hzero' : H i 1 = 0 := by simpa [hzero] using hs₁
  fin_cases j
  · exact hzero
  · exact hzero'

end ExplicitRays

section Facets

/-- The common weight of the merged realization. -/
noncomputable def facetWeight (r : ℕ) : ℝ := 1 / ((r : ℝ) - 1)

/-- Rational slopes, with finite labels starting at one in the manuscript. -/
noncomputable def facetSlope (r : ℕ) (j : Fin r) : ℝ :=
  ((j.val : ℝ) + 1) / (r : ℝ)^2

/-- Label effect in the merged qubit construction. -/
noncomputable def facetEffect (r : ℕ) (j : Fin r) : Operator (Fin 2) :=
  facetWeight r • rayProjection (facetSlope r j)

theorem facetEffect_rational (r : ℕ) (j : Fin r) (i k : Fin 2) :
    ∃ q : ℚ, ((q : ℝ) : ℂ) = facetEffect r j i k := by
  let w : ℚ := 1 / ((r : ℚ) - 1)
  let s : ℚ := ((j.val : ℚ) + 1) / (r : ℚ) ^ 2
  let x : Fin 2 → ℚ := ![1, s]
  have hw : (w : ℝ) = facetWeight r := by simp [w, facetWeight]
  have hs : (s : ℝ) = facetSlope r j := by simp [s, facetSlope]
  refine ⟨w * (1 / (1 + s ^ 2)) * x i * x k, ?_⟩
  fin_cases i <;> fin_cases k <;>
    simp [facetEffect, rayProjection, ray, Matrix.vecMulVec, Complex.real_smul, x, hw, hs,
      Complex.ofReal_mul, mul_assoc]

theorem facetEffect_pos {r : ℕ} (hr : 2 ≤ r) (j : Fin r) :
    (facetEffect r j).PosSemidef := by
  apply (rayProjection_pos _).smul
  unfold facetWeight
  apply one_div_nonneg.mpr
  have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  linarith

theorem facetEffect_disjoint {r : ℕ} (hr : 2 ≤ r) (j k : Fin r) (hjk : j ≠ k)
    (H : Operator (Fin 2)) (hH : H.PosSemidef)
    (hj : H ≤ facetEffect r j) (hk : H ≤ facetEffect r k) : H = 0 := by
  apply distinct_ray_lower_bound (c := facetWeight r) _ hH hj hk
  intro he
  have hpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  simp only [facetSlope] at he
  have hval : ((j.val : ℝ) + 1) = (k.val : ℝ) + 1 :=
    (div_left_inj' (pow_ne_zero _ hpos.ne')).mp he
  have hv : (j.val : ℝ) = k.val := by linarith
  exact hjk (Fin.ext (by exact_mod_cast hv))

private theorem facetEffect_le_weight {r : ℕ} (hr : 2 ≤ r) (j : Fin r) :
    facetEffect r j ≤ facetWeight r • (1 : Operator (Fin 2)) := by
  apply Matrix.le_iff.mpr
  rw [facetEffect, ← smul_sub]
  have hw : 0 ≤ facetWeight r := by
    unfold facetWeight
    apply one_div_nonneg.mpr
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  exact (Matrix.le_iff.mp (rayProjection_le_one _)).smul hw

private theorem card_lt_of_not_univ {r : ℕ} {U : Finset (Fin r)} (hU : U ≠ Finset.univ) :
    U.card < r := by
  simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ _, hU⟩)

theorem facetEffect_sum_le_one_of_missing {r : ℕ} (hr : 2 ≤ r)
    (U : Finset (Fin r)) (hU : U ≠ Finset.univ) :
    (∑ j ∈ U, facetEffect r j) ≤ 1 := by
  have hc := card_lt_of_not_univ hU
  have hcast : (U.card : ℝ) + 1 ≤ r := by exact_mod_cast (Nat.succ_le_of_lt hc)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  refine (Finset.sum_le_sum (fun j _ => facetEffect_le_weight hr j)).trans ?_
  rw [← Finset.sum_smul]
  have hsum : (∑ _j ∈ U, facetWeight r) ≤ 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul, facetWeight]
    rw [mul_one_div]
    exact (div_le_iff₀ (by linarith : (0 : ℝ) < r - 1)).mpr (by linarith)
  apply Matrix.le_iff.mpr
  have he : (1 : Operator (Fin 2)) - (∑ _j ∈ U, facetWeight r) • 1 =
      (1 - ∑ _j ∈ U, facetWeight r) • (1 : Operator (Fin 2)) := by
    rw [sub_smul, one_smul]
  rw [he]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.mpr hsum)

private theorem facetEffect_entry (r : ℕ) (j : Fin r) :
    (facetEffect r j 0 0).re = facetWeight r / (1 + facetSlope r j ^ 2) := by
  have he :
      Matrix.vecMulVec (ray (facetSlope r j)) (star (ray (facetSlope r j))) 0 0 = 1 := by
    simp [ray, Matrix.vecMulVec]
  rw [facetEffect, Matrix.smul_apply, rayProjection, Matrix.smul_apply, he]
  simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one, mul_one_div]

theorem facetEffect_sum_not_le_one {r : ℕ} (hr : 2 ≤ r) :
    ¬ (∑ j : Fin r, facetEffect r j) ≤ 1 := by
  intro h
  have hre := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp h).diag_nonneg (i := (0 : Fin 2)))).1
  have hus : (∑ j : Fin r, (facetEffect r j 0 0).re) ≤ 1 := by
    apply sub_nonneg.mp
    simpa [Matrix.sub_apply, Complex.sub_re, Matrix.sum_apply, Complex.re_sum] using hre
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : (0 : ℝ) < r := by linarith
  have hm : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hj (j : Fin r) : (1 : ℝ) / r < (facetEffect r j 0 0).re := by
    have hcast : (j.val : ℝ) + 1 ≤ r := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    have hl : 0 ≤ facetSlope r j := by unfold facetSlope; positivity
    have ht : facetSlope r j ≤ 1 / (r : ℝ) := by
      unfold facetSlope
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (r : ℝ)^2)).mpr
      calc
        _ ≤ (r : ℝ) := hcast
        _ = (1 / (r : ℝ)) * (r : ℝ)^2 := by field_simp [hpos.ne']
    have hsq : facetSlope r j ^ 2 ≤ (1 / (r : ℝ))^2 := (sq_le_sq₀ hl (by positivity)).mpr ht
    have hp : ((r : ℝ) - 1) * facetSlope r j ^ 2 < 1 := by
      refine (mul_le_mul_of_nonneg_left hsq hm.le).trans_lt ?_
      field_simp
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    rw [facetEffect_entry, facetWeight, div_div]
    apply (one_div_lt_one_div_of_lt (by positivity))
    nlinarith
  have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin r)))
    (f := fun _ => (1 : ℝ) / r) (g := fun j => (facetEffect r j 0 0).re)
    (fun j _ => (hj j).le) ⟨⟨0, by omega⟩, Finset.mem_univ _, hj _⟩
  have hones : (∑ _j : Fin r, (1 : ℝ) / r) = 1 := by
    simp [nsmul_eq_mul, hpos.ne']
  rw [hones] at hsum
  exact (not_lt_of_ge hus) hsum

section

variable {V : Type*} [DecidableEq V] {r : ℕ}

/-- Labels of the facets that do not contain the vertex. -/
def omittedFacets (F : Fin r → Finset V) (v : V) : Finset (Fin r) :=
  Finset.univ.filter (fun j => v ∉ F j)

private theorem omittedFacets_ne_univ (F : Fin r → Finset V) (v : V)
    (hv : ∃ j, v ∈ F j) : omittedFacets F v ≠ Finset.univ := by
  obtain ⟨j, hj⟩ := hv
  intro h
  have hmem : j ∈ omittedFacets F v := h.symm ▸ Finset.mem_univ j
  exact (Finset.mem_filter.mp hmem).2 hj

/-- The merged POVM at a vertex in the rational-ray realization. -/
noncomputable def facetMeasurement (F : Fin r → Finset V) (hr : 2 ≤ r)
    (hcover : ∀ v, ∃ j, v ∈ F j) (v : V) : POVM (Fin 2) (Option (Fin r)) :=
  merged (facetEffect r) (facetEffect_pos hr) (omittedFacets F v)
    (facetEffect_sum_le_one_of_missing hr _ (omittedFacets_ne_univ F v (hcover v)))

/-- Every matrix entry of every outcome, including the residual, is rational. -/
theorem facetMeasurement_rational (F : Fin r → Finset V) (hr : 2 ≤ r)
    (hcover : ∀ v, ∃ j, v ∈ F j) (v : V) (o : Option (Fin r)) (i k : Fin 2) :
    ∃ q : ℚ, ((q : ℝ) : ℂ) = (facetMeasurement F hr hcover v).effect o i k := by
  classical
  cases o with
  | some j =>
      change ∃ q : ℚ, ((q : ℝ) : ℂ) =
        (if j ∈ omittedFacets F v then facetEffect r j else 0) i k
      by_cases h : j ∈ omittedFacets F v
      · rw [ite_eq_left h]; exact facetEffect_rational r j i k
      · rw [ite_eq_right h]; exact ⟨0, by simp⟩
  | none =>
      choose q hq using fun j : Fin r => facetEffect_rational r j i k
      let S := omittedFacets F v
      have hs : ((∑ j ∈ S, q j : ℚ) : ℝ) = ∑ j ∈ S, (q j : ℝ) :=
        map_sum (Rat.castHom ℝ) (fun j => q j) S
      refine ⟨(if i = k then 1 else 0) - ∑ j ∈ S, q j, ?_⟩
      change _ = ((1 : Operator (Fin 2)) - ∑ j ∈ S, facetEffect r j) i k
      simp only [Rat.cast_sub, hs, Complex.ofReal_sub, Complex.ofReal_sum,
        Matrix.sub_apply, Matrix.sum_apply, hq, Matrix.one_apply]
      split <;> simp

/-- The merged realization of a finite complex given by its covering facets.
All effects, positivity, and joint marginals are expressed as actual
two-by-two complex matrices. -/
theorem facetMeasurement_compatible_iff (F : Fin r → Finset V) (hr : 2 ≤ r)
    (hcover : ∀ v, ∃ j, v ∈ F j) (S : Finset V) :
    Compatible (fun v : S => facetMeasurement F hr hcover v) ↔ ∃ j, S ⊆ F j := by
  classical
  let A : S → Finset (Fin r) := fun v => omittedFacets F v
  let U := Finset.univ.biUnion A
  change Compatible (fun v : S => merged (facetEffect r) (facetEffect_pos hr)
    (A v) _) ↔ _
  rw [merged_compatible_iff (facetEffect r) (facetEffect_pos hr) (facetEffect_disjoint hr)]
  have hmem (j : Fin r) : j ∈ U ↔ ∃ v ∈ S, v ∉ F j := by simp [U, A, omittedFacets]
  change (∑ j ∈ U, facetEffect r j) ≤ 1 ↔ _
  constructor
  · intro h
    have hU : U ≠ Finset.univ := fun e => facetEffect_sum_not_le_one hr (e ▸ h)
    obtain ⟨j, hj⟩ : ∃ j, j ∉ U := by
      by_contra! hn
      exact hU (Finset.eq_univ_iff_forall.mpr hn)
    exact ⟨j, fun v hv => by by_contra hbad; exact hj ((hmem j).mpr ⟨v, hv, hbad⟩)⟩
  · rintro ⟨j, hj⟩
    apply facetEffect_sum_le_one_of_missing hr U
    intro e
    obtain ⟨v, hvs, hv⟩ := (hmem j).mp (e.symm ▸ Finset.mem_univ j)
    exact hv (hj hvs)

/-- The manuscript's outcome bound, measured by the number of nonzero
effects in the common padded alphabet. -/
theorem facetMeasurement_outcome_bound (F : Fin r → Finset V) (hr : 2 ≤ r)
    (hcover : ∀ v, ∃ j, v ∈ F j) (v : V) :
    ((Finset.univ : Finset (Option (Fin r))).filter
      (fun o => (facetMeasurement F hr hcover v).effect o ≠ 0)).card ≤ r := by
  classical
  let U := omittedFacets F v
  calc
    _ ≤ (insert none (U.image some)).card := by
      apply Finset.card_le_card
      intro o ho
      cases o with
      | none => simp
      | some j =>
          have hj : j ∈ U := by
            by_contra h
            simpa [facetMeasurement, merged, U, h] using (Finset.mem_filter.mp ho).2
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hj)
    _ = U.card + 1 := by
      rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective (Fin r))]
    _ ≤ r := card_lt_of_not_univ (omittedFacets_ne_univ F v (hcover v))

end

end Facets

section SimplicialComplex

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The maximal faces of a family of subsets of a finite vertex set. -/
def Facet (K : Finset V → Prop) :=
  {F : Finset V // K F ∧ ∀ G : Finset V, K G → F ⊆ G → G = F}

private theorem exists_facet_above (K : Finset V → Prop) (S : Finset V) (hS : K S) :
    ∃ F : Facet K, S ⊆ F.val := by
  classical
  let B := Finset.univ.filter (fun T : Finset V => K T ∧ S ⊆ T)
  have hB : B.Nonempty := ⟨S, by simp [B, hS]⟩
  obtain ⟨F, hF, hmax⟩ := Finset.exists_max_image B Finset.card hB
  have hF' : K F ∧ S ⊆ F := by simpa [B] using hF
  refine ⟨⟨F, hF'.1, ?_⟩, hF'.2⟩
  intro G hG hFG
  have hBG : G ∈ B := by simp [B, hG, hF'.2.trans hFG]
  have hc : G.card ≤ F.card := hmax G hBG
  exact (Finset.eq_of_subset_of_card_le hFG hc).symm

/-- Every finite abstract simplicial complex is the exact family of
compatible subfamilies of a family of qubit POVMs. The common alphabet is
finite. The preceding theorem bounds nonzero outcomes by the facet count
when there are at least two facets. -/
theorem finite_simplicial_complex_on_qubit (K : Finset V → Prop)
    (hempty : K ∅) (hvertex : ∀ v : V, K {v})
    (hdown : ∀ ⦃S T : Finset V⦄, S ⊆ T → K T → K S) :
    ∃ (r : ℕ) (M : V → POVM (Fin 2) (Option (Fin r))),
      ∀ S : Finset V, Compatible (fun v : S => M v) ↔ K S := by
  classical
  let _ : Fintype (Facet K) := by unfold Facet; infer_instance
  let n := Fintype.card (Facet K)
  let e : Facet K ≃ Fin n := Fintype.equivFin _
  let r := max 2 n
  have hr : 2 ≤ r := le_max_left _ _
  obtain ⟨F₀, _⟩ := exists_facet_above K ∅ hempty
  let lift (i : Fin r) : Facet K := if h : i.val < n then e.symm ⟨i.val, h⟩ else F₀
  have hsurj : Function.Surjective lift := by
    intro F
    refine ⟨⟨(e F).val, lt_of_lt_of_le (e F).isLt (le_max_right _ _)⟩, ?_⟩
    simp [lift, (e F).isLt]
  let F (i : Fin r) := (lift i).val
  have hcover (v : V) : ∃ j, v ∈ F j := by
    obtain ⟨G, hG⟩ := exists_facet_above K {v} (hvertex v)
    obtain ⟨j, rfl⟩ := hsurj G
    exact ⟨j, hG (Finset.mem_singleton_self v)⟩
  refine ⟨r, facetMeasurement F hr hcover, fun S => ?_⟩
  rw [facetMeasurement_compatible_iff F hr hcover]
  constructor
  · rintro ⟨j, hj⟩
    exact hdown hj (lift j).property.1
  · intro hS
    obtain ⟨G, hG⟩ := exists_facet_above K S hS
    obtain ⟨j, rfl⟩ := hsurj G
    exact ⟨j, hG⟩

end SimplicialComplex

end ManuscriptProofs.Quantum
