import ManuscriptProofs.PureExclusion
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators Matrix ComplexConjugate

namespace ManuscriptProofs.PureExclusion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
private theorem sqrt_row (w eigen : ι → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hs : ∑ j, w j = 1) (hl : ∀ j, 0 ≤ eigen j) :
    ∑ j, w j * Real.sqrt (eigen j) ≤ Real.sqrt (∑ j, w j * eigen j) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun j => w j * Real.sqrt (eigen j)) (f := w) (g := fun j => w j * eigen j)
    (fun j _ => hw j) (fun j _ => mul_nonneg (hw j) (hl j)) (fun j _ => by
      rw [mul_pow, Real.sq_sqrt (hl j)]; exact le_of_eq (by ring))
  rw [hs, one_mul] at h
  exact (Real.le_sqrt_of_sq_le h)

/-- The overlap matrix of two eigenbases can mix all the eigenvalues.
Rowwise Cauchy–Schwarz accounts for this mixing before estimating the
negative part of the inverse dual. -/
theorem trace_bound_of_overlaps (W : ι → ι → ℝ) (eigen t : ι → ℝ) (p k : ι) (a : ℝ)
    (hW : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = 1) (hl : ∀ j, 0 ≤ eigen j)
    (hmax : ∀ j, eigen j ≤ eigen k) (ha : 0 < a)
    (ht : ∀ i ∈ Finset.univ.erase p, 0 < t i)
    (hT : 0 < ∑ i ∈ Finset.univ.erase p, t i) :
    let d := fun i => ∑ j, W i j * eigen j
    d p/a - (∑ i ∈ Finset.univ.erase p, d i/t i) ≤
      eigen k/a - (∑ j ∈ Finset.univ.erase k, Real.sqrt (eigen j))^2 /
        (∑ i ∈ Finset.univ.erase p, t i) := by
  classical
  let d := fun i => ∑ j, W i j * eigen j
  change d p / a - _ ≤ _
  have hd i : 0 ≤ d i := Finset.sum_nonneg (fun j _ => mul_nonneg (hW i j) (hl j))
  have htop : d p ≤ eigen k := calc
    d p ≤ ∑ j, W p j * eigen k := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hmax j) (hW p j)
    _ = eigen k := by rw [← Finset.sum_mul, hrow, one_mul]
  have hsum : ∑ j, Real.sqrt (eigen j) ≤ ∑ i, Real.sqrt (d i) := calc
    _ = ∑ j, (∑ i, W i j) * Real.sqrt (eigen j) := by simp [hcol]
    _ = ∑ i, ∑ j, W i j * Real.sqrt (eigen j) := by simp only [Finset.sum_mul]; rw [Finset.sum_comm]
    _ ≤ _ := Finset.sum_le_sum (fun i _ => sqrt_row (W i) eigen (hW i) (hrow i) hl)
  have hrest : ∑ j ∈ Finset.univ.erase k, Real.sqrt (eigen j) ≤
      ∑ i ∈ Finset.univ.erase p, Real.sqrt (d i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k),
        ← Finset.sum_erase_add _ (fun i => Real.sqrt (d i)) (Finset.mem_univ p)] at hsum
    linarith [Real.sqrt_le_sqrt htop]
  have hn : 0 ≤ ∑ j ∈ Finset.univ.erase k, Real.sqrt (eigen j) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hsq := sq_le_sq' (by linarith) hrest
  have hcs := weighted_spectral_sum_bound (Finset.univ.erase p) d t (fun j _ => hd j) ht
  have hneg : (∑ j ∈ Finset.univ.erase k, Real.sqrt (eigen j))^2 /
      (∑ i ∈ Finset.univ.erase p, t i) ≤ ∑ i ∈ Finset.univ.erase p, d i/t i := by
    apply (div_le_iff₀ hT).2
    rw [mul_comm]
    exact hsq.trans hcs
  exact sub_le_sub (div_le_div_of_nonneg_right htop ha.le) hneg

private theorem unitaries_rows (U : Matrix.unitaryGroup ι ℂ) (i : ι) :
    ∑ j, Complex.normSq (U.val i j) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp U.property) i) i
  apply Complex.ofReal_injective
  push_cast
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self, mul_comm] using h

private theorem unitaries_cols (U : Matrix.unitaryGroup ι ℂ) (j : ι) :
    ∑ i, Complex.normSq (U.val i j) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp U.property) j) j
  apply Complex.ofReal_injective
  push_cast
  simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Complex.normSq_eq_conj_mul_self] using h

private theorem diagonal_in_basis (U : Matrix.unitaryGroup ι ℂ) (eigen : ι → ℝ) (i : ι) :
    (U.val * Matrix.diagonal (fun j => (eigen j : ℂ)) * U.valᴴ) i i =
      ((∑ j, Complex.normSq (U.val i j) * eigen j : ℝ) : ℂ) := by
  rw [Matrix.mul_apply]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self]
  change U.val i j * ↑(eigen j) * conj (U.val i j) = conj (U.val i j) * U.val i j * ↑(eigen j)
  ring

/-- The trace inequality in the eigenbasis of the inverse dual, for a genuine
complex unitary change of eigenbasis of the positive mixture. No ordering of
the negative eigenvalues or optimal choice of a permutation is assumed. -/
theorem unitary_trace_inverse_bound (U : Matrix.unitaryGroup ι ℂ) (eigen t : ι → ℝ)
    (p k : ι) (a : ℝ) (hl : ∀ j, 0 ≤ eigen j) (hmax : ∀ j, eigen j ≤ eigen k)
    (ha : 0 < a) (ht : ∀ i ∈ Finset.univ.erase p, 0 < t i)
    (hT : 0 < ∑ i ∈ Finset.univ.erase p, t i) :
    let R := U.val * Matrix.diagonal (fun j => (eigen j : ℂ)) * U.valᴴ
    let invY := Matrix.diagonal (fun i => ((if i = p then 1/a else -(1/t i) : ℝ) : ℂ))
    (invY * R).trace.re ≤ eigen k/a -
      (∑ j ∈ Finset.univ.erase k, Real.sqrt (eigen j))^2 / (∑ i ∈ Finset.univ.erase p, t i) := by
  let W := fun i j => Complex.normSq (U.val i j)
  let d := fun i => ∑ j, W i j * eigen j
  have hb := trace_bound_of_overlaps W eigen t p k a (fun i j => Complex.normSq_nonneg _)
    (unitaries_rows U) (unitaries_cols U) hl hmax ha ht hT
  change d p/a - _ ≤ _ at hb
  apply le_trans (le_of_eq ?_) hb
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, diagonal_in_basis,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  change (∑ i, (if i = p then 1/a else -(1/t i)) * d i) = _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p)]
  simp only [↓reduceIte]
  have hneg : (∑ i ∈ Finset.univ.erase p, (if i = p then 1/a else -(1/t i)) * d i) =
      -(∑ i ∈ Finset.univ.erase p, d i/t i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [(Finset.mem_erase.mp hi).1, div_eq_mul_inv, mul_comm]
  rw [hneg]
  ring

end ManuscriptProofs.PureExclusion
