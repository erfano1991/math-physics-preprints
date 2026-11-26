import ManuscriptProofs.Quantum.POVM
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

namespace ManuscriptProofs.Quantum

section Hyperplane

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

/-- The system matrix unit acting as identity on the environment. -/
def liftedUnit (i j : d) : Operator (d × e) :=
  (Matrix.of (fun a b => if a = i ∧ b = j then 1 else 0) : Operator d) ⊗ₖ
    (1 : Operator e)

private theorem liftedUnit_mul {c : Type*} (V : Matrix (d × e) c ℂ) (i j : d)
    (a : d) (t : e) (b : c) :
    (liftedUnit (e := e) i j * V) (a, t) b = if a = i then V (j, t) b else 0 := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, liftedUnit, Matrix.kronecker_apply,
    Matrix.of_apply, Matrix.one_apply]
  by_cases h : a = i
  · simp [h, Finset.sum_ite_eq', Finset.sum_ite_eq]
  · simp [h]

/-- Matrix-unit tests for exact noiseless transmission in finite Stinespring
coordinates. They are the entrywise form of \(V^*(E_{ij}\otimes I)V=E_{ij}\). -/
theorem unit_tests_of_exact_compression
    (V : Matrix (d × e) d ℂ)
    (hV : ∀ i j, Vᴴ * liftedUnit i j * V =
      (Matrix.of fun a b => if a = i ∧ b = j then 1 else 0 : Operator d)) :
    ∀ i j a b, (∑ t : e, star (V (i, t) a) * V (j, t) b) =
      if a = i ∧ b = j then 1 else 0 := by
  intro i j a b
  have h := congrArg (fun X : Operator d => X a b) (hV i j)
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type] at h
  simp only [Matrix.conjTranspose_apply, liftedUnit_mul, mul_ite, mul_zero, Matrix.of_apply] at h
  rw [Finset.sum_comm] at h
  simpa [Finset.sum_ite_eq', Finset.sum_ite_eq] using h

omit [Fintype d] [DecidableEq e] in
/-- If a rectangular matrix satisfies the exact compression identity for
every system matrix unit, then it is entrywise a product embedding. -/
theorem product_embedding_of_unit_tests
    [Nonempty d]
    (V : Matrix (d × e) d ℂ)
    (hV : ∀ i j a b, (∑ t : e, star (V (i, t) a) * V (j, t) b) =
      if a = i ∧ b = j then 1 else 0) :
    ∃ h : e → ℂ, star h ⬝ᵥ h = 1 ∧
      ∀ a b t, V (a, t) b = if a = b then h t else 0 := by
  have hzero (a b : d) (h : a ≠ b) (t : e) : V (a, t) b = 0 := by
    have hw : star (fun t : e => V (a, t) b) ⬝ᵥ (fun t => V (a, t) b) = 0 := by
      simpa [dotProduct, Ne.symm h] using hV a a b b
    exact congrFun (dotProduct_star_self_eq_zero.mp hw) t
  inhabit d
  let h : e → ℂ := fun t => V (default, t) default
  have hsame (a : d) : (fun t : e => V (a, t) a) = h := by
    let q : e → ℂ := fun t => V (a, t) a
    have hqq : (∑ t : e, star (q t) * q t) = 1 := by simpa [q] using hV a a a a
    have hhh : (∑ t : e, star (h t) * h t) = 1 := by
      simpa [h] using hV default default default default
    have hqh : (∑ t : e, star (q t) * h t) = 1 := by
      simpa [q, h] using hV a default a default
    have hhq : (∑ t : e, star (h t) * q t) = 1 := by
      simpa [q, h] using hV default a default a
    apply sub_eq_zero.mp
    apply dotProduct_star_self_eq_zero.mp
    change star (q - h) ⬝ᵥ (q - h) = 0
    simp only [dotProduct, Pi.star_apply, Pi.sub_apply, star_sub, sub_mul, mul_sub,
      Finset.sum_sub_distrib, hqq, hhh, hqh, hhq, sub_self]
  refine ⟨h, ?_, fun a b t => ?_⟩
  · simpa [h, dotProduct] using hV default default default default
  · by_cases hab : a = b
    · subst b
      simpa using congrFun (hsame a) t
    · simp [hab, hzero a b hab t]

/-- The maximally entangled hyperplane supports no full noiseless code.
The defining linear equation is the inner product with the unnormalized
maximally entangled vector. -/
theorem no_full_code_in_maximally_entangled_hyperplane
    [Nonempty d] (V : Matrix (d × d) d ℂ)
    (hperp : ∀ b, (∑ a, V (a, a) b) = 0)
    (hV : ∀ i j, Vᴴ * liftedUnit i j * V =
      (Matrix.of fun a b => if a = i ∧ b = j then 1 else 0 : Operator d)) : False := by
  obtain ⟨h, hnorm, hv⟩ :=
    product_embedding_of_unit_tests V (unit_tests_of_exact_compression V hV)
  have hzero (b : d) : h b = 0 := by
    simpa [hv, Finset.sum_ite_eq', Finset.sum_ite_eq] using hperp b
  have : h = 0 := funext hzero
  simp [this] at hnorm

omit [DecidableEq d] in
/-- The same hyperplane contains the product vectors for any subspace
annihilated by the indicated environment functional. -/
theorem product_vector_in_maximally_entangled_hyperplane
    (F : Submodule ℂ (d → ℂ)) (h : d → ℂ)
    (hF : ∀ x ∈ F, x ⬝ᵥ h = 0) :
    ∀ x ∈ F, (∑ a, (fun ij : d × d => x ij.1 * h ij.2) (a, a)) = 0 :=
  fun x hx => hF x hx

/-- Each proper subspace admits a nonzero environment vector for a product
embedding into the maximally entangled hyperplane. -/
theorem proper_subspace_has_product_copy
    (F : Submodule ℂ (d → ℂ)) (hF : F ≠ ⊤) :
    ∃ h : d → ℂ, h ≠ 0 ∧ ∀ x ∈ F, (∑ a, x a * h a) = 0 := by
  classical
  obtain ⟨f, hf, hker⟩ := F.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hF)
  let h : d → ℂ := fun a => f (Pi.single a 1)
  have hpair (x : d → ℂ) : (∑ a, x a * h a) = f x := by
    calc
      _ = f (∑ a, x a • (Pi.single a (1 : ℂ) : d → ℂ)) := by
        simp [h, map_sum, map_smul, smul_eq_mul]
      _ = f x := by
        congr 1
        ext a
        classical
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, Finset.sum_ite_eq]
  refine ⟨h, ?_, fun x hx => (hpair x).trans (LinearMap.mem_ker.mp (hker hx))⟩
  intro he
  apply hf
  apply LinearMap.ext
  intro x
  change f x = 0
  rw [← hpair x, he]
  simp

end Hyperplane

section Averaging

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [AddCommGroup E] [Module ℝ E]

/-- Algebraic rigidity of the uniform averaging equations in the three-setting
construction. At most one index (the odd-dimensional block) may be omitted. -/
theorem uniform_block_rigidity (H : ι → E) (c : ℝ) (hc : c ≠ 0)
    (K : Finset ι) (hK : ∀ i j, i ∉ K → j ∉ K → i = j)
    (havg : ∀ i ∈ K, H i = (1 - (Fintype.card ι : ℝ) * c) • H i + c • ∑ j, H j) :
    ∃ h : E, ∀ i, H i = h := by
  classical
  let n : ℝ := Fintype.card ι
  have hn : n ≠ 0 := by
    dsimp [n]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  let h : E := n⁻¹ • ∑ j, H j
  have hk (i : ι) (hi : i ∈ K) : H i = h := by
    have he : (n * c) • H i = c • ∑ j, H j := by
      have hl := havg i hi
      change H i = (1 - n * c) • H i + c • ∑ j, H j at hl
      rw [sub_smul, one_smul] at hl
      have := congrArg (fun z : E => z - H i + (n * c) • H i) hl
      simpa only [sub_self, zero_add] using show
        H i - H i + (n * c) • H i = c • ∑ j, H j from
          this.trans (by abel)
    have he' := congrArg (fun z : E => (n * c)⁻¹ • z) he
    have hmul : (n * c)⁻¹ * c = n⁻¹ := by field_simp [hn, hc]
    simpa only [h, smul_smul, inv_mul_cancel₀ (mul_ne_zero hn hc), one_smul, hmul] using he'
  refine ⟨h, fun i => ?_⟩
  by_cases hi : i ∈ K
  · exact hk i hi
  have hh : ∑ j, (H j - h) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ]
    change (∑ j, H j) - n • h = 0
    simp [h, smul_smul, mul_inv_cancel₀ hn]
  rw [Finset.sum_eq_single i] at hh
  · exact sub_eq_zero.mp hh
  · intro j _ hji
    rw [hk j (by by_contra hj; exact hji (hK j i hj hi)), sub_self]
  · simp

end Averaging

end ManuscriptProofs.Quantum
