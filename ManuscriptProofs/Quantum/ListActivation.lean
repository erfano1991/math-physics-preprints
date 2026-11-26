import ManuscriptProofs.Quantum.FiniteCopyLists
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

namespace ManuscriptProofs.Quantum

variable {d Ω ι : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

/-- The local index at a tensor slot. -/
def copyCoordinate : (n : ℕ) → Copies d n → Fin n → d
  | 0, _, i => i.elim0
  | n + 1, (a, b), i => Fin.cases a (copyCoordinate n b) i

omit [Fintype d] [DecidableEq d] in
theorem tensorFactors_entry {n : ℕ} (F : Fin n → Operator d) (u v : Copies d n) :
    tensorFactors F u v = ∏ j, F j (copyCoordinate n u j) (copyCoordinate n v j) := by
  induction n with
  | zero => cases u; cases v; simp [tensorFactors]
  | succ n ih =>
      rcases u with ⟨u₀, u⟩
      rcases v with ⟨v₀, v⟩
      rw [tensorFactors, Matrix.kronecker_apply, Fin.prod_univ_succ]
      simp only [copyCoordinate, Fin.cases_zero, Fin.cases_succ]
      rw [ih]

omit [Fintype d] in
@[simp] theorem tensorPower_one (n : ℕ) :
    tensorPower (1 : Operator d) n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (1 : Operator d) ⊗ₖ tensorPower (1 : Operator d) n = 1
      rw [ih, Matrix.one_kronecker_one]

omit [Fintype d] [DecidableEq d] in
private theorem tensor_update_entry {n : ℕ} (F : Fin n → Operator d)
    (j : Fin n) (B : Operator d) (u v : Copies d n) :
    tensorFactors (Function.update F j B) u v =
      (∏ i ∈ Finset.univ.erase j, F i (copyCoordinate n u i) (copyCoordinate n v i)) *
        B (copyCoordinate n u j) (copyCoordinate n v j) := by
  rw [tensorFactors_entry, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

omit [Fintype d] [DecidableEq d] in
private theorem tensor_update_sum {n : ℕ} (F : Fin n → Operator d)
    (j : Fin n) (B : Ω → Operator d) :
    (∑ o, tensorFactors (Function.update F j (B o))) =
      tensorFactors (Function.update F j (∑ o, B o)) := by
  ext u v
  simp only [Matrix.sum_apply, tensor_update_entry, Finset.mul_sum]

omit [Fintype d] [DecidableEq d] in
private theorem tensor_update_add_smul {n : ℕ} (F : Fin n → Operator d)
    (j : Fin n) (B C : Operator d) (c : ℝ) :
    tensorFactors (Function.update F j (B + c • C)) =
      tensorFactors (Function.update F j B) + c • tensorFactors (Function.update F j C) := by
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, tensor_update_entry, mul_add, mul_smul_comm]

private noncomputable def tensorWord {n : ℕ} (A R : Operator d) (S : Finset (Fin n)) :
    Fin n → Operator d :=
  fun i => if i ∈ S then A else R

omit [Fintype d] [DecidableEq d] in
private theorem sum_tensor_words (A R : Operator d) (n : ℕ) :
    (∑ S : Finset (Fin n), tensorFactors (tensorWord A R S)) = tensorPower (A + R) n := by
  classical
  ext u v
  simp only [Matrix.sum_apply, tensorPower, tensorFactors_entry, Matrix.add_apply]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.prod_mul_prod_compl S]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp [tensorWord, hi]
  · exact Finset.prod_congr rfl fun i hi => by simp [tensorWord, Finset.mem_compl.mp hi]

/-- In a nonempty word, designate one admissible factor. In singleton words
that factor also receives its share of the all-residual term. -/
noncomputable def activatedPiece {n : ℕ} (A R : Operator d)
    (E C : Ω → Operator d) (S : Finset (Fin n)) (o : Ω) : Operator (Copies d n) :=
  if hs : S.Nonempty then
    tensorFactors (Function.update (tensorWord A R S) (S.min' hs)
      (if S.card = 1 then C o else E o))
  else 0

omit [DecidableEq d] [Fintype Ω] in
private theorem activatedPiece_pos {n : ℕ} (A R : Operator d) (E C : Ω → Operator d)
    (hA : A.PosSemidef) (hR : R.PosSemidef)
    (hE : ∀ o, (E o).PosSemidef) (hC : ∀ o, (C o).PosSemidef)
    (S : Finset (Fin n)) (o : Ω) :
    (activatedPiece A R E C S o).PosSemidef := by
  by_cases hs : S.Nonempty
  · simp only [activatedPiece, hs, dite_true]
    apply tensorFactors_pos
    intro j
    by_cases hj : j = S.min' hs
    · subst j
      simp only [Function.update_self]
      split
      · exact hC o
      · exact hE o
    · rw [Function.update_of_ne hj]
      unfold tensorWord
      split
      · exact hA
      · exact hR
  · simp only [activatedPiece, hs, dite_false]
    exact Matrix.PosSemidef.zero

omit [Fintype d] [DecidableEq d] in
private theorem sum_activated_at_word {n : ℕ} (A R : Operator d) (E C : Ω → Operator d)
    (hE : (∑ o, E o) = A) (hC : (∑ o, C o) = A + ((n : ℝ)⁻¹) • R)
    (S : Finset (Fin n)) :
    (∑ o, activatedPiece A R E C S o) =
      (if S.Nonempty then tensorFactors (tensorWord A R S) else 0) +
        (if S.card = 1 then ((n : ℝ)⁻¹) • tensorPower R n else 0) := by
  by_cases hs : S.Nonempty
  · let j := S.min' hs
    have hj : j ∈ S := S.min'_mem hs
    have hsame : Function.update (tensorWord A R S) j A = tensorWord A R S := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [tensorWord, hj]
      · exact Function.update_of_ne hij _ _
    by_cases hcard : S.card = 1
    · simp only [activatedPiece, hs, dite_true, hcard, ite_true]
      rw [tensor_update_sum, hC, tensor_update_add_smul, hsame]
      have hsingle : S = {j} := by
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
        have e : j = i := by simpa [hi] using hj
        simpa [e] using hi
      have hrepl : Function.update (tensorWord A R S) j R = fun _ => R := by
        funext i
        by_cases hij : i = j
        · subst i
          simp
        · simp [tensorWord, hsingle, hij]
      rw [hrepl]
      rfl
    · simp only [activatedPiece, hs, dite_true, hcard, ite_true, ite_false, add_zero]
      rw [tensor_update_sum, hE, hsame]
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst S
    simp [activatedPiece]

omit [Fintype d] [DecidableEq d] in
private theorem sum_nonempty_words (A R : Operator d) (n : ℕ) :
    (∑ S : Finset (Fin n), if S.Nonempty then tensorFactors (tensorWord A R S) else 0) =
      tensorPower (A + R) n - tensorPower R n := by
  classical
  have hS (S : Finset (Fin n)) :
      (if S.Nonempty then tensorFactors (tensorWord A R S) else 0) =
        tensorFactors (tensorWord A R S) - if S = ∅ then tensorPower R n else 0 := by
    by_cases h : S = ∅
    · subst S
      have hword : tensorWord A R (∅ : Finset (Fin n)) = fun _ => R := by
        funext i
        simp [tensorWord]
      simp [hword, tensorPower]
    · have hn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
      simp [h, hn]
  simp_rw [hS, Finset.sum_sub_distrib, Fintype.sum_ite_eq', sum_tensor_words]

omit [Fintype d] [DecidableEq d] in
private theorem sum_singletons {n : ℕ} (X : Operator (Copies d n)) :
    (∑ S : Finset (Fin n), if S.card = 1 then X else 0) = (n : ℝ) • X := by
  classical
  rw [← Finset.sum_filter]
  have h : (Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = 1) =
      Finset.univ.image (fun j : Fin n => ({j} : Finset (Fin n))) := by
    ext S
    simp [Finset.card_eq_one, eq_comm]
  rw [h, Finset.sum_const, Finset.card_image_of_injective _ (fun _ _ h => Finset.singleton_inj.mp h),
    Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]

omit [Fintype d] in
theorem activation_normalization {n : ℕ} (hn : 0 < n) (A R : Operator d)
    (E C : Ω → Operator d) (hAR : A + R = 1)
    (hE : (∑ o, E o) = A) (hC : (∑ o, C o) = A + ((n : ℝ)⁻¹) • R) :
    (∑ o, ∑ S : Finset (Fin n), activatedPiece A R E C S o) = 1 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [sum_activated_at_word A R E C hE hC]
  rw [Finset.sum_add_distrib, sum_nonempty_words, sum_singletons, hAR, tensorPower_one, smul_smul]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [mul_inv_cancel₀ hne, one_smul, sub_add_cancel]

/-- The activated product measurement has zero Born probability for each
omitted label. The input dimension may already be that of a block of copies. -/
theorem zero_error_from_activated_factors (ρ : ι → Operator d) (lists : Ω → Set ι)
    {n : ℕ} (hn : 0 < n) (A R : Operator d) (E C : Ω → Operator d)
    (hA : A.PosSemidef) (hR : R.PosSemidef) (hAR : A + R = 1)
    (hE : ∀ o, (E o).PosSemidef) (hC : ∀ o, (C o).PosSemidef)
    (hEs : (∑ o, E o) = A) (hCs : (∑ o, C o) = A + ((n : ℝ)⁻¹) • R)
    (h0 : ∀ o i, i ∉ lists o → (E o * ρ i).trace = 0 ∧ (C o * ρ i).trace = 0) :
    ZeroError ρ lists n := by
  classical
  refine ⟨⟨fun o => ∑ S : Finset (Fin n), activatedPiece A R E C S o,
    fun o => Matrix.posSemidef_sum _ fun S _ => activatedPiece_pos A R E C hA hR hE hC S o,
    activation_normalization hn A R E C hAR hEs hCs⟩, ?_⟩
  intro o i hi
  simp only [Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro S _
  by_cases hs : S.Nonempty
  · simp only [activatedPiece, hs, dite_true, tensorPower, ← tensorFactors_mul, trace_tensorFactors]
    apply Finset.prod_eq_zero (Finset.mem_univ (S.min' hs))
    simp only [Function.update_self]
    split
    · exact (h0 o i hi).2
    · exact (h0 o i hi).1
  · simp [activatedPiece, hs]

/-- Activation from an exact positive-minus-positive decomposition of the
identity. The scalar c dominates the entire negative part in Loewner order. -/
theorem activate_signed_decomposition (ρ : ι → Operator d) (lists : Ω → Set ι)
    (B D : Ω → Operator d) (hB : ∀ o, (B o).PosSemidef) (hD : ∀ o, (D o).PosSemidef)
    (hid : (∑ o, B o) - (∑ o, D o) = 1)
    (h0 : ∀ o i, i ∉ lists o → (B o * ρ i).trace = 0 ∧ (D o * ρ i).trace = 0)
    (c : ℝ) (hc : 0 < c) (hbound : (∑ o, D o) ≤ c • (1 : Operator d))
    (n : ℕ) (hn : 1 + c ≤ (n : ℝ)) :
    ZeroError ρ lists n := by
  let t := (n : ℝ)
  have ht : 0 < t := by dsimp [t]; linarith
  have hn' : 0 < n := by exact_mod_cast (show (0 : ℝ) < (n : ℝ) from ht)
  let E (o : Ω) := c⁻¹ • D o
  let A := c⁻¹ • ∑ o, D o
  let R : Operator d := 1 - A
  let β := (t - 1 - c) / (c * t)
  let C (o : Ω) := t⁻¹ • B o + β • D o
  have hβ : 0 ≤ β := div_nonneg (by dsimp [t]; linarith) (mul_nonneg hc.le ht.le)
  have hA : A.PosSemidef := (Matrix.posSemidef_sum _ (fun o _ => hD o)).smul (inv_nonneg.mpr hc.le)
  have hR : R.PosSemidef := by
    have h := (Matrix.le_iff.mp hbound).smul (inv_nonneg.mpr hc.le)
    simpa [R, A, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne'] using h
  have hBs : (∑ o, B o) = 1 + ∑ o, D o := sub_eq_iff_eq_add.mp hid
  refine zero_error_from_activated_factors ρ lists hn' A R E C hA hR
    (by dsimp [R]; abel)
    (fun o => (hD o).smul (inv_nonneg.mpr hc.le))
    (fun o => ((hB o).smul (inv_nonneg.mpr ht.le)).add ((hD o).smul hβ))
    ?_ ?_ ?_
  · simp [A, E, Finset.smul_sum]
  · have hcoeff : t⁻¹ + β = c⁻¹ - t⁻¹ * c⁻¹ := by
      dsimp [β]
      field_simp [ht.ne', hc.ne']
      ring
    simp only [C, Finset.sum_add_distrib, ← Finset.smul_sum, hBs, smul_add]
    change t⁻¹ • (1 : Operator d) + t⁻¹ • (∑ o, D o) + β • (∑ o, D o) =
      A + t⁻¹ • R
    rw [add_assoc, ← add_smul, hcoeff]
    dsimp [A, R]
    simp only [sub_smul, smul_sub, smul_smul]
    abel
  · intro o i hi
    obtain ⟨hb, hd⟩ := h0 o i hi
    simp [E, C, add_mul, Matrix.trace_add, Matrix.trace_smul, hb, hd]

end ManuscriptProofs.Quantum
