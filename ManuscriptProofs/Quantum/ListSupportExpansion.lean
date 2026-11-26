import ManuscriptProofs.Quantum.FiniteCopyLists
import Mathlib.Analysis.Matrix.Spectrum

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace ManuscriptProofs.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A Hermitian matrix has a kernel projection and an inverse on its range,
extended by zero on its kernel. -/
theorem hermitian_range_inverse (T : Operator d) (hT : T.IsHermitian) :
    ∃ P Q : Operator d, P.IsHermitian ∧ P * P = P ∧
      T * P = 0 ∧ Q * P = 0 ∧ T * Q = 1 - P ∧ Q * T = 1 - P := by
  classical
  let U := Unitary.conjStarAlgAut ℂ (Operator d) hT.eigenvectorUnitary
  let e (i : d) : ℂ := hT.eigenvalues i
  let z (i : d) : ℂ := if e i = 0 then 1 else 0
  let q (i : d) : ℂ := (e i)⁻¹
  let P := U (Matrix.diagonal z)
  let Q := U (Matrix.diagonal q)
  have hspec : T = U (Matrix.diagonal e) := hT.spectral_theorem
  have hself : IsSelfAdjoint (Matrix.diagonal z) := Matrix.isHermitian_diagonal_iff.mpr fun i => by
    dsimp [z]
    split <;> simp [isSelfAdjoint_iff]
  have hPP : Matrix.diagonal z * Matrix.diagonal z = Matrix.diagonal z := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : e i = 0 <;> simp [z, hi]
  have hTP : Matrix.diagonal e * Matrix.diagonal z = 0 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext i
    by_cases hi : e i = 0 <;> simp [z, hi]
  have hQP : Matrix.diagonal q * Matrix.diagonal z = 0 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_zero]
    congr 1
    funext i
    by_cases hi : e i = 0 <;> simp [q, z, hi]
  have hTQ : Matrix.diagonal e * Matrix.diagonal q = 1 - Matrix.diagonal z := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_sub]
    congr 1
    funext i
    by_cases hi : e i = 0 <;> simp [q, z, hi]
  have hQT : Matrix.diagonal q * Matrix.diagonal e = 1 - Matrix.diagonal z := by
    simpa only [Matrix.diagonal_mul_diagonal, mul_comm (q _) (e _)] using hTQ
  refine ⟨P, Q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsSelfAdjoint P
    exact hself.map U
  · change U (Matrix.diagonal z) * U (Matrix.diagonal z) = _
    rw [← map_mul, hPP]
  · calc
      T * P = U (Matrix.diagonal e * Matrix.diagonal z) := by
        rw [map_mul]
        exact congrArg (· * P) hspec
      _ = 0 := by rw [hTP, map_zero]
  · change U (Matrix.diagonal q) * U (Matrix.diagonal z) = _
    rw [← map_mul, hQP, map_zero]
  · calc
      T * Q = U (Matrix.diagonal e * Matrix.diagonal q) := by
        rw [map_mul]
        exact congrArg (· * Q) hspec
      _ = 1 - P := by rw [hTQ, map_sub, map_one]
  · calc
      Q * T = U (Matrix.diagonal q * Matrix.diagonal e) := by
        rw [map_mul]
        exact congrArg (Q * ·) hspec
      _ = 1 - P := by rw [hQT, map_sub, map_one]

omit [DecidableEq d] in
/-- The kernel of a sum of positive effects is their common kernel.
The empty sum gives the entire vector space. -/
theorem posSemidef_sum_kernel {ι : Type*} (K : ι → Operator d)
    (hK : ∀ i, (K i).PosSemidef) (S : Finset ι) (x : d → ℂ) :
    (∑ i ∈ S, K i) *ᵥ x = 0 ↔ ∀ i ∈ S, K i *ᵥ x = 0 := by
  constructor
  · intro h i hi
    have hs : (∑ j ∈ S, star x ⬝ᵥ (K j *ᵥ x)) = 0 := by
      simpa only [Matrix.sum_mulVec, dotProduct_sum, dotProduct_zero] using
        congrArg (fun y => star x ⬝ᵥ y) h
    exact ((hK i).dotProduct_mulVec_zero_iff x).mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hK j).dotProduct_mulVec_nonneg x)).mp hs i hi)
  · intro h
    rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero h

/-- The one-factor identity in the finite-copy sufficiency proof.
Orthogonality of the two common kernels gives the split of the identity.
The two families remove labels on the left and on the right respectively. -/
theorem orthogonal_support_expansion {ι : Type*} (K : ι → Operator d)
    (hK : ∀ i, (K i).PosSemidef) (A B : Finset ι)
    (hAB : ∀ x y : d → ℂ, (∀ i ∈ A, K i *ᵥ x = 0) →
      (∀ j ∈ B, K j *ᵥ y = 0) → star x ⬝ᵥ y = 0) :
    ∃ P_A P_B Q_A Q_B : Operator d,
      (∑ i ∈ A, K i) * Q_A = 1 - P_A ∧
      Q_B * (∑ j ∈ B, K j) = 1 - P_B ∧ P_A * P_B = 0 ∧
      (1 : Operator d) = (∑ i ∈ A, K i * Q_A) + (∑ j ∈ B, P_A * Q_B * K j) ∧
      (∀ i ∈ A, ∀ x y : d → ℂ, K i *ᵥ x = 0 →
        star x ⬝ᵥ ((K i * Q_A) *ᵥ y) = 0) ∧
      (∀ j ∈ B, ∀ x : d → ℂ, K j *ᵥ x = 0 → (P_A * Q_B * K j) *ᵥ x = 0) := by
  let T_A : Operator d := ∑ i ∈ A, K i
  let T_B : Operator d := ∑ j ∈ B, K j
  have hA : T_A.IsHermitian := (Matrix.posSemidef_sum A (fun i _ => hK i)).isHermitian
  have hB : T_B.IsHermitian := (Matrix.posSemidef_sum B (fun i _ => hK i)).isHermitian
  obtain ⟨P_A, Q_A, hPA, _, hTAPA, _, hAinv, _⟩ := hermitian_range_inverse T_A hA
  obtain ⟨P_B, Q_B, _, _, hTBPB, _, _, hBinv⟩ := hermitian_range_inverse T_B hB
  have hAK (x : d → ℂ) : ∀ i ∈ A, K i *ᵥ (P_A *ᵥ x) = 0 := by
    apply (posSemidef_sum_kernel K hK A _).mp
    change T_A *ᵥ (P_A *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hTAPA, Matrix.zero_mulVec]
  have hBK (x : d → ℂ) : ∀ j ∈ B, K j *ᵥ (P_B *ᵥ x) = 0 := by
    apply (posSemidef_sum_kernel K hK B _).mp
    change T_B *ᵥ (P_B *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hTBPB, Matrix.zero_mulVec]
  have hOrth : P_A * P_B = 0 := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
    let v := P_B *ᵥ x
    have h := hAB (P_A *ᵥ (P_A *ᵥ v)) v (hAK (P_A *ᵥ v)) (hBK x)
    rw [Matrix.star_mulVec, hPA.eq, ← Matrix.dotProduct_mulVec] at h
    exact dotProduct_star_self_eq_zero.mp h
  refine ⟨P_A, P_B, Q_A, Q_B, hAinv, hBinv, hOrth, ?_, ?_, ?_⟩
  · calc
      (1 : Operator d) = (1 - P_A) + P_A * (1 - P_B) := by
        rw [mul_sub, mul_one, hOrth, sub_zero, sub_add_cancel]
      _ = _ := by
        rw [← hAinv, ← hBinv, ← Matrix.mul_assoc]
        simp only [T_A, T_B, Matrix.sum_mul, Matrix.mul_sum]
  · intro i _ x y hx
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← (hK i).isHermitian.eq,
      ← Matrix.star_mulVec, hx, star_zero, zero_dotProduct]
  · intro j _ x hx
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

end ManuscriptProofs.Quantum
