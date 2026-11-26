import ManuscriptProofs.Quantum.ListActivation
import ManuscriptProofs.Quantum.ListSupportExpansion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

namespace ManuscriptProofs.Quantum

private theorem kronecker_sum_right {d e I : Type*} [Fintype I]
    (A : Operator d) (B : I → Operator e) :
    A ⊗ₖ (∑ i, B i) = ∑ i, A ⊗ₖ B i :=
  map_sum (Matrix.kroneckerBilinear (R := ℂ) A) B Finset.univ

private theorem kronecker_sum_left {d e I : Type*} [Fintype I]
    (A : I → Operator d) (B : Operator e) :
    (∑ i, A i) ⊗ₖ B = ∑ i, A i ⊗ₖ B :=
  map_sum ((Matrix.kroneckerBilinear (R := ℂ)).flip B) A Finset.univ

private theorem sum_grouped_products {d e I Ω : Type*} [DecidableEq e] [Fintype I] [Fintype Ω]
    (L : I → Operator d) (X : I → Ω → Operator e) (hX : ∀ i, (∑ o, X i o) = 1) :
    (∑ o, ∑ i, L i ⊗ₖ X i o) = (∑ i, L i) ⊗ₖ (1 : Operator e) := by
  rw [Finset.sum_comm]
  simp_rw [← kronecker_sum_right, hX]
  exact (kronecker_sum_left L 1).symm

variable {d ι Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

/-- A positive support-complement projection has kernel equal to the range
of the preparation. -/
private theorem support_complement (ρ : Operator d) (hρ : ρ.PosSemidef) :
    ∃ K : Operator d, K.PosSemidef ∧ K * ρ = 0 ∧ ρ * K = 0 ∧
      ∀ x : d → ℂ, K *ᵥ x = 0 ↔ ∃ y, ρ *ᵥ y = x := by
  obtain ⟨K, Q, hK, hKK, hzero, _, hright, _⟩ := hermitian_range_inverse ρ hρ.isHermitian
  have hleft : K * ρ = 0 := by
    have h := congrArg Matrix.conjTranspose hzero
    simpa only [Matrix.conjTranspose_mul, hK.eq, hρ.isHermitian.eq, Matrix.conjTranspose_zero] using h
  have hp := Matrix.posSemidef_conjTranspose_mul_self K
  rw [hK.eq, hKK] at hp
  refine ⟨K, hp, hleft, hzero, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    refine ⟨Q *ᵥ x, ?_⟩
    rw [Matrix.mulVec_mulVec, hright, Matrix.sub_mulVec, Matrix.one_mulVec, hx, sub_zero]
  · rintro ⟨y, rfl⟩
    rw [Matrix.mulVec_mulVec, hleft, Matrix.zero_mulVec]

private def Fits (lists : Ω → Set ι) (A B : Finset ι) : Prop :=
  ∃ o, (∀ i ∈ A, i ∈ lists o) ∧ (∀ i ∈ B, i ∈ lists o)

private def GroupedExpansion (ρ : ι → Operator d) (lists : Ω → Set ι)
    (A B : Finset ι) (n : ℕ) : Prop :=
  ∃ X : Ω → Operator (Copies d n),
    (∑ o, X o) = 1 ∧
      (∀ o i, i ∈ A → i ∉ lists o → tensorPower (ρ i) n * X o = 0) ∧
      (∀ o i, i ∈ B → i ∉ lists o → X o * tensorPower (ρ i) n = 0)

private theorem grouped_of_fit (ρ : ι → Operator d) (lists : Ω → Set ι)
    (A B : Finset ι) (n : ℕ) (hfit : Fits lists A B) : GroupedExpansion ρ lists A B n := by
  classical
  obtain ⟨o, hA, hB⟩ := hfit
  refine ⟨fun j => if j = o then 1 else 0, by simp, ?_, ?_⟩
  · intro j i hi hx
    have hne : j ≠ o := fun eq => hx (eq.symm ▸ hA i hi)
    simp [hne]
  · intro j i hi hx
    have hne : j ≠ o := fun eq => hx (eq.symm ▸ hB i hi)
    simp [hne]

private theorem grouped_expansion_aux [DecidableEq ι] [Nonempty Ω]
    (ρ : ι → Operator d) (lists : Ω → Set ι) (K : ι → Operator d)
    (hK : ∀ i, (K i).PosSemidef) (hleft : ∀ i, ρ i * K i = 0) (hright : ∀ i, K i * ρ i = 0)
    (horth : ∀ A B : Finset ι, ¬ Fits lists A B →
      ∀ x y : d → ℂ, (∀ i ∈ A, K i *ᵥ x = 0) → (∀ j ∈ B, K j *ᵥ y = 0) →
        star x ⬝ᵥ y = 0) :
    ∀ (n : ℕ) (A B : Finset ι), A.card + B.card ≤ n → GroupedExpansion ρ lists A B n := by
  intro n
  induction n with
  | zero =>
      intro A B hbudget
      have hA : A = ∅ := Finset.card_eq_zero.mp (by omega)
      have hB : B = ∅ := Finset.card_eq_zero.mp (by omega)
      obtain ⟨o⟩ := ‹Nonempty Ω›
      exact grouped_of_fit ρ lists A B 0 ⟨o, by simp [hA], by simp [hB]⟩
  | succ n ih =>
      intro A B hbudget
      by_cases hfit : Fits lists A B
      · exact grouped_of_fit ρ lists A B (n + 1) hfit
      obtain ⟨P_A, _, Q_A, Q_B, _, _, _, hI, _, _⟩ :=
        orthogonal_support_expansion K hK A B (horth A B hfit)
      let L (i : ι) := K i * Q_A
      let R (j : ι) := P_A * Q_B * K j
      have hLA (i : A) : GroupedExpansion ρ lists (A.erase i) B n := by
        have hd := Finset.card_erase_of_mem i.prop
        have hp := Finset.card_pos.mpr ⟨i.val, i.prop⟩
        exact ih _ _ (by omega)
      have hRB (j : B) : GroupedExpansion ρ lists A (B.erase j) n := by
        have hd := Finset.card_erase_of_mem j.prop
        have hp := Finset.card_pos.mpr ⟨j.val, j.prop⟩
        exact ih _ _ (by omega)
      unfold GroupedExpansion at hLA hRB
      choose XA hsumA hleftA hrightA using hLA
      choose XB hsumB hleftB hrightB using hRB
      let X (o : Ω) : Operator (Copies d (n + 1)) :=
        (∑ i : A, L i ⊗ₖ XA i o) + ∑ j : B, R j ⊗ₖ XB j o
      have hnorm : (∑ o, X o) = 1 := by
        have hweights : (∑ i : A, L i) + (∑ j : B, R j) = 1 := by
          rw [Finset.sum_coe_sort A L, Finset.sum_coe_sort B R]
          exact hI.symm
        change (∑ o, ((∑ i : A, L i ⊗ₖ XA i o) + ∑ j : B, R j ⊗ₖ XB j o)) = _
        rw [Finset.sum_add_distrib, sum_grouped_products _ _ hsumA, sum_grouped_products _ _ hsumB,
          ← Matrix.add_kronecker, hweights, Matrix.one_kronecker_one]
      refine ⟨X, hnorm, ?_, ?_⟩
      · intro o i hi ho
        have hL (j : A) : (ρ i * L j) ⊗ₖ (tensorPower (ρ i) n * XA j o) = 0 := by
          by_cases hji : i = j.val
          · rw [hji, show ρ j * L j = 0 by dsimp [L]; rw [← Matrix.mul_assoc, hleft, zero_mul],
              Matrix.zero_kronecker]
          · rw [hleftA j o i (Finset.mem_erase.mpr ⟨hji, hi⟩) ho, Matrix.kronecker_zero]
        have hR (j : B) : (ρ i * R j) ⊗ₖ (tensorPower (ρ i) n * XB j o) = 0 := by
          rw [hleftB j o i hi ho, Matrix.kronecker_zero]
        change (ρ i ⊗ₖ tensorPower (ρ i) n) *
          ((∑ j : A, L j ⊗ₖ XA j o) + ∑ j : B, R j ⊗ₖ XB j o) = 0
        simp only [Matrix.mul_add, Matrix.mul_sum, ← Matrix.mul_kronecker_mul, hL, hR,
          Finset.sum_const_zero, add_zero]
      · intro o i hi ho
        have hL (j : A) : (L j * ρ i) ⊗ₖ (XA j o * tensorPower (ρ i) n) = 0 := by
          rw [hrightA j o i hi ho, Matrix.kronecker_zero]
        have hR (j : B) : (R j * ρ i) ⊗ₖ (XB j o * tensorPower (ρ i) n) = 0 := by
          by_cases hji : i = j.val
          · rw [hji, show R j * ρ j = 0 by dsimp [R]; rw [Matrix.mul_assoc, hright, mul_zero],
              Matrix.zero_kronecker]
          · rw [hrightB j o i (Finset.mem_erase.mpr ⟨hji, hi⟩) ho, Matrix.kronecker_zero]
        change ((∑ j : A, L j ⊗ₖ XA j o) + ∑ j : B, R j ⊗ₖ XB j o) *
          (ρ i ⊗ₖ tensorPower (ρ i) n) = 0
        simp only [Matrix.add_mul, Matrix.sum_mul, ← Matrix.mul_kronecker_mul, hL, hR,
          Finset.sum_const_zero, add_zero]

/-- The tensor expansion from the nonorthogonal-pair condition.
Terms are grouped by allowed list, with annihilation on both sides for
every omitted label. -/
theorem list_tensor_expansion [Fintype ι] [Nonempty Ω]
    (ρ : ι → Operator d) (hρ : ∀ i, (ρ i).PosSemidef) (lists : Ω → Set ι)
    (hpair : ∀ x y : d → ℂ, star x ⬝ᵥ y ≠ 0 →
      ∃ o, ∀ i, ((∃ v, ρ i *ᵥ v = x) ∨ (∃ w, ρ i *ᵥ w = y)) → i ∈ lists o)
    (n : ℕ) (hn : 2 * Fintype.card ι ≤ n) :
    ∃ X : Ω → Operator (Copies d n), (∑ o, X o) = 1 ∧
      ∀ o i, i ∉ lists o →
        tensorPower (ρ i) n * X o = 0 ∧ X o * tensorPower (ρ i) n = 0 := by
  classical
  choose K hK hright hleft hRange using fun i => support_complement (ρ i) (hρ i)
  have horth (A B : Finset ι) (hnfit : ¬ Fits lists A B)
      (x y : d → ℂ) (hx : ∀ i ∈ A, K i *ᵥ x = 0) (hy : ∀ i ∈ B, K i *ᵥ y = 0) :
      star x ⬝ᵥ y = 0 := by
    by_contra hne
    obtain ⟨o, ho⟩ := hpair x y hne
    exact hnfit ⟨o, fun i hi => ho i (Or.inl ((hRange i x).mp (hx i hi))),
      fun i hi => ho i (Or.inr ((hRange i y).mp (hy i hi)))⟩
  obtain ⟨X, hX, hA, hB⟩ :=
    grouped_expansion_aux ρ lists K hK hleft hright horth n Finset.univ Finset.univ
      (by simpa only [Finset.card_univ, two_mul] using hn)
  exact ⟨X, hX, fun o i hi =>
    ⟨hA o i (Finset.mem_univ i) hi, hB o i (Finset.mem_univ i) hi⟩⟩

private theorem parts_annihilate (A S : Operator d) (hA : IsSelfAdjoint A) (hS : A * S = 0) :
    A⁺ * S = 0 ∧ A⁻ * S = 0 := by
  have he : A⁺ * S = A⁻ * S := by
    apply sub_eq_zero.mp
    rw [← Matrix.sub_mul, CFC.posPart_sub_negPart A hA, hS]
  have hpos : (A⁺).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg A)
  have hz : (A⁺ * A⁺) * S = 0 := by
    rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, CFC.posPart_mul_negPart, zero_mul]
  have hp : A⁺ * S = 0 := (Matrix.conjTranspose_mul_self_mul_eq_zero A⁺ S).mp
    (by rw [hpos.isHermitian.eq, hz])
  exact ⟨hp, he.symm.trans hp⟩

/-- The nonorthogonal-pair condition yields the signed admissible identity
decomposition consumed by the activation theorem. -/
theorem signed_decomposition_of_list_condition [Fintype ι] [Nonempty Ω]
    (ρ : ι → Operator d) (hρ : ∀ i, (ρ i).PosSemidef) (lists : Ω → Set ι)
    (hpair : ∀ x y : d → ℂ, star x ⬝ᵥ y ≠ 0 →
      ∃ o, ∀ i, ((∃ v, ρ i *ᵥ v = x) ∨ (∃ w, ρ i *ᵥ w = y)) → i ∈ lists o)
    (n : ℕ) (hn : 2 * Fintype.card ι ≤ n) :
    ∃ B D : Ω → Operator (Copies d n),
      (∀ o, (B o).PosSemidef) ∧ (∀ o, (D o).PosSemidef) ∧
      (∑ o, B o) - (∑ o, D o) = 1 ∧
      ∀ o i, i ∉ lists o →
        (B o * tensorPower (ρ i) n).trace = 0 ∧ (D o * tensorPower (ρ i) n).trace = 0 := by
  obtain ⟨X, hX, hzero⟩ := list_tensor_expansion ρ hρ lists hpair n hn
  let H (o : Ω) := (1 / 2 : ℝ) • (X o + (X o)ᴴ)
  have hH (o : Ω) : IsSelfAdjoint (H o) := by
    change (H o)ᴴ = H o
    simp [H, Matrix.conjTranspose_add, add_comm]
  have hnorm : (∑ o, H o) = 1 := by
    change (∑ o, (1 / 2 : ℝ) • (X o + (X o)ᴴ)) = _
    rw [← Finset.smul_sum, Finset.sum_add_distrib, ← Matrix.conjTranspose_sum, hX,
      Matrix.conjTranspose_one, ← two_smul ℝ (1 : Operator (Copies d n)), smul_smul,
      show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  refine ⟨fun o => (H o)⁺, fun o => (H o)⁻,
    fun o => Matrix.nonneg_iff_posSemidef.mp (CFC.posPart_nonneg _),
    fun o => Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg _), ?_, ?_⟩
  · rw [← Finset.sum_sub_distrib]
    simpa only [CFC.posPart_sub_negPart _ (hH _)] using hnorm
  · intro o i hi
    let S := tensorPower (ρ i) n
    have hS : S.PosSemidef := tensorFactors_pos (fun _ => ρ i) (fun _ => hρ i)
    obtain ⟨hl, hr⟩ := hzero o i hi
    have hb : (X o)ᴴ * S = 0 := by
      simpa only [Matrix.conjTranspose_mul, hS.isHermitian.eq, Matrix.conjTranspose_zero] using
        congrArg Matrix.conjTranspose (show S * X o = 0 from hl)
    have hz : H o * S = 0 := by
      dsimp [H]
      rw [smul_mul_assoc, Matrix.add_mul, show X o * S = 0 from hr, hb, add_zero, smul_zero]
    obtain ⟨hp, hm⟩ := parts_annihilate (H o) S (hH o) hz
    change ((H o)⁺ * S).trace = 0 ∧ ((H o)⁻ * S).trace = 0
    simp only [hp, hm, Matrix.trace_zero, and_self]

open scoped Matrix.Norms.L2Operator in
/-- The pair criterion yields a zero-error measurement on finitely many
blocks, each containing twice the number of labels in copies. -/
theorem zero_error_on_blocks_of_list_condition [Fintype ι] [Nonempty Ω]
    (ρ : ι → Operator d) (hρ : ∀ i, (ρ i).PosSemidef) (lists : Ω → Set ι)
    (hpair : ∀ x y : d → ℂ, star x ⬝ᵥ y ≠ 0 →
      ∃ o, ∀ i, ((∃ v, ρ i *ᵥ v = x) ∨ (∃ w, ρ i *ᵥ w = y)) → i ∈ lists o) :
    ∃ m : ℕ, 0 < m ∧ ZeroError (fun i => tensorPower (ρ i) (2 * Fintype.card ι)) lists m := by
  let b := 2 * Fintype.card ι
  obtain ⟨B, D, hB, hD, hId, hzero⟩ := signed_decomposition_of_list_condition ρ hρ lists hpair b le_rfl
  let S := ∑ o, D o
  have hp : S.PosSemidef := Matrix.posSemidef_sum _ fun o _ => hD o
  let c : ℝ := ‖S‖ + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound : S ≤ c • (1 : Operator (Copies d b)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (CStarAlgebra.norm_le_iff_le_algebraMap S hc.le hp.nonneg).mp (by dsimp [c]; linarith)
  obtain ⟨m, hm⟩ := exists_nat_ge (1 + c)
  have hmp : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  exact ⟨m, hmp, activate_signed_decomposition (fun i => tensorPower (ρ i) b) lists
    B D hB hD hId hzero c hc hbound m hm⟩

end ManuscriptProofs.Quantum
