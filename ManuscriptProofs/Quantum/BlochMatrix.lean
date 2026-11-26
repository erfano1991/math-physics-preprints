import ManuscriptProofs.LossyQubit
import ManuscriptProofs.Quantum.POVM
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace ManuscriptProofs.Quantum

abbrev BlochVector := EuclideanSpace ℝ (Fin 3)

/-- The traceless Hermitian matrix with Pauli coefficients v. -/
noncomputable def pauliDot (v : BlochVector) : Operator (Fin 2) :=
  !![(v 2 : ℂ), (v 0 : ℂ) - (v 1 : ℂ) * Complex.I;
    (v 0 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 2 : ℂ)]

private theorem pauliDot_hermitian (v : BlochVector) : (pauliDot v)ᴴ = pauliDot v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliDot, Matrix.conjTranspose_apply, sub_eq_add_neg]

private theorem pauliDot_square (v : BlochVector) :
    pauliDot v * pauliDot v = (‖v‖ ^ 2 : ℝ) • (1 : Operator (Fin 2)) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauliDot, Matrix.mul_apply, Fin.sum_univ_two, pow_two,
      Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

private noncomputable def shiftedPauli (w : ℝ) (v : BlochVector) : Operator (Fin 2) :=
  w • (1 : Operator (Fin 2)) + pauliDot v

private theorem shiftedPauli_hermitian (w : ℝ) (v : BlochVector) :
    (shiftedPauli w v)ᴴ = shiftedPauli w v := by
  simp [shiftedPauli, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, pauliDot_hermitian]

private theorem shiftedPauli_trace_re (w : ℝ) (v : BlochVector) :
    (shiftedPauli w v).trace.re = 2 * w := by
  simp [shiftedPauli, pauliDot, Matrix.trace, Fin.sum_univ_two, Complex.real_smul]
  ring

private theorem shiftedPauli_det_re (w : ℝ) (v : BlochVector) :
    (shiftedPauli w v).det.re = w ^ 2 - ‖v‖ ^ 2 := by
  simp [shiftedPauli, pauliDot, Matrix.det_fin_two, Complex.real_smul, Complex.mul_re,
    Complex.mul_im, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring

private theorem shiftedPauli_pos_iff (w : ℝ) (v : BlochVector) :
    (shiftedPauli w v).PosSemidef ↔ ‖v‖ ≤ w := by
  constructor
  · intro h
    have ht := (Complex.nonneg_iff.mp h.trace_nonneg).1
    have hd := (Complex.nonneg_iff.mp h.det_nonneg).1
    rw [shiftedPauli_trace_re] at ht
    rw [shiftedPauli_det_re] at hd
    exact (sq_le_sq₀ (norm_nonneg v) (by linarith)).mp (by linarith)
  · intro hw
    have hbase : (shiftedPauli ‖v‖ v).PosSemidef := by
      by_cases hv : v = 0
      · subst v
        have hz : shiftedPauli 0 0 = 0 := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [shiftedPauli, pauliDot]
        rw [norm_zero, hz]
        exact Matrix.PosSemidef.zero
      · have hp : 0 < 2 * ‖v‖ := by positivity
        have hsq : shiftedPauli ‖v‖ v * shiftedPauli ‖v‖ v =
            (2 * ‖v‖) • shiftedPauli ‖v‖ v := by
          simp only [shiftedPauli, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul,
            mul_one, smul_smul, pauliDot_square, smul_add]
          module
        have hB := Matrix.posSemidef_conjTranspose_mul_self (shiftedPauli ‖v‖ v)
        rw [shiftedPauli_hermitian, hsq] at hB
        simpa only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul] using
          hB.smul (inv_nonneg.mpr hp.le)
    have hscalar := (Matrix.PosSemidef.one (n := Fin 2) (R := ℂ)).smul (sub_nonneg.mpr hw)
    have he : shiftedPauli w v =
        (w - ‖v‖) • (1 : Operator (Fin 2)) + shiftedPauli ‖v‖ v := by
      unfold shiftedPauli
      rw [← add_assoc, ← add_smul, sub_add_cancel]
    rw [he]
    exact hscalar.add hbase

/-- The qubit effect with trace weight w and Bloch vector v. -/
noncomputable def blochEffect (w : ℝ) (v : BlochVector) : Operator (Fin 2) :=
  (1 / 2 : ℝ) • shiftedPauli w v

theorem blochEffect_pos_iff (w : ℝ) (v : BlochVector) :
    (blochEffect w v).PosSemidef ↔ ‖v‖ ≤ w := by
  constructor
  · intro h
    apply (shiftedPauli_pos_iff w v).mp
    have e : (2 : ℝ) • blochEffect w v = shiftedPauli w v := by
      rw [blochEffect, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
    rw [← e]
    exact h.smul (by norm_num : (0 : ℝ) ≤ 2)
  · intro h
    exact ((shiftedPauli_pos_iff w v).mpr h).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- Subtracting a click effect is subtraction of its trace weight and
its scaled Bloch vector. -/
theorem blochEffect_sub_scaled (w a : ℝ) (v n : BlochVector) :
    blochEffect w v - a • blochEffect 1 n = blochEffect (w - a) (v - a • n) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochEffect, shiftedPauli, pauliDot, PiLp.sub_apply, PiLp.smul_apply,
      Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring

theorem blochEffect_residual_pos_iff (w a : ℝ) (v n : BlochVector) :
    (blochEffect w v - a • blochEffect 1 n).PosSemidef ↔ ‖v - a • n‖ ≤ w - a := by
  rw [blochEffect_sub_scaled, blochEffect_pos_iff]

/-- Every Hermitian two-by-two matrix has Bloch coordinates. -/
theorem exists_blochEffect (M : Operator (Fin 2)) (hM : Mᴴ = M) :
    ∃ w : ℝ, ∃ v : BlochVector, M = blochEffect w v := by
  let w : ℝ := (M 0 0).re + (M 1 1).re
  let v : BlochVector := WithLp.toLp 2
    ![2 * (M 0 1).re, -2 * (M 0 1).im, (M 0 0).re - (M 1 1).re]
  have he (i j : Fin 2) : star (M i j) = M j i :=
    congrArg (fun A : Operator (Fin 2) => A j i) hM
  have hdiag (i : Fin 2) : (M i i).im = 0 := by
    have hi := congrArg Complex.im (he i i)
    simp only [Complex.star_def, Complex.conj_im] at hi
    linarith
  have hreal : (M 1 0).re = (M 0 1).re := by simpa using (congrArg Complex.re (he 0 1)).symm
  have him : (M 1 0).im = -(M 0 1).im := by
    simpa only [Complex.star_def, Complex.conj_im] using (congrArg Complex.im (he 0 1)).symm
  refine ⟨w, v, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [blochEffect, shiftedPauli, pauliDot, w, v, Complex.real_smul,
      Complex.mul_re, Complex.mul_im, hdiag, hreal, him] <;> ring

/-- The exact rank-one branch capacity as a matrix positivity test. -/
theorem rank_one_click_residual_iff (m n : BlochVector) (hm : ‖m‖ = 1) (hn : ‖n‖ = 1)
    (a : ℝ) (ha : 0 ≤ a) :
    (∃ s : Bool, (blochEffect 1 m - a • blochEffect 1 (LossyQubit.signed s n)).PosSemidef) ↔
      a = 0 ∨ (n = m ∨ n = -m) ∧ a ≤ 1 := by
  simp only [blochEffect_residual_pos_iff]
  exact LossyQubit.rank_one_branch_signed_iff m n hm hn a ha

end ManuscriptProofs.Quantum
