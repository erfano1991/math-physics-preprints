import ManuscriptProofs.Quantum.ThreeSettingParent

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace ManuscriptProofs.Quantum

/-- The two support projections have a zero mixed block of the lifted
constant, whether or not their sum is the identity. -/
theorem opposite_slacks_zero_mixed_block {e : Type*} [Fintype e]
    (P Q Z W L : Operator e) (hP : P.IsHermitian) (hZ : Z.IsHermitian)
    (hZP : Z * P = 0) (hWQ : W * Q = 0) (hL : Z + W = (2 : ℝ) • L) :
    P * L * Q = 0 := by
  have hPZ : P * Z = 0 := by
    simpa only [Matrix.conjTranspose_mul, hP.eq, hZ.eq, Matrix.conjTranspose_zero] using
      congrArg Matrix.conjTranspose hZP
  have hm : P * (Z + W) * Q = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, hPZ, zero_mul, zero_add, Matrix.mul_assoc, hWQ, mul_zero]
  rw [hL, mul_smul_comm, smul_mul_assoc] at hm
  exact (smul_eq_zero.mp hm).resolve_left (by norm_num)

/-- A system vector tensored with the identity map on the environment. -/
def environmentEmbedding {s e : Type*} [DecidableEq e] (u : s → ℂ) : Matrix (s × e) e ℂ :=
  Matrix.of fun a x => if a.2 = x then u a.1 else 0

/-- The operator with diagonal system blocks and no mixed system entries. -/
def diagonalEnvironmentBlocks {s e : Type*} [DecidableEq s] (H : s → Operator e) :
    Operator (s × e) :=
  Matrix.of fun a b => if a.1 = b.1 then H a.1 a.2 b.2 else 0

variable {s e : Type*} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

private theorem diagonal_blocks_mul_embedding (H : s → Operator e) (v : s → ℂ)
    (a : s) (x y : e) :
    ((diagonalEnvironmentBlocks H * environmentEmbedding v : Matrix (s × e) e ℂ)
      (a, x) y) = H a x y * v a := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, diagonalEnvironmentBlocks, environmentEmbedding,
    Matrix.of_apply]
  simp [ite_mul, mul_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- Mixed environment matrix of two system vectors in a block-diagonal
operator. Each coefficient is the actual conjugate product. -/
theorem diagonal_environment_mixed_block (H : s → Operator e) (u v : s → ℂ) :
    (environmentEmbedding u)ᴴ * diagonalEnvironmentBlocks H * environmentEmbedding v =
      ∑ a, (star (u a) * v a) • H a := by
  ext x y
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, diagonal_blocks_mul_embedding]
  simp only [environmentEmbedding, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- The third opposite pair gives the weighted average in the construction.
The vectors are g - 2f and 2g + f before division by √5. -/
theorem third_pair_environment_average (H : s → Operator e) (K : Operator e) (g : s → ℂ)
    (hcross :
      (environmentEmbedding (e := e) (Sum.elim g (fun _ : Unit => (-2 : ℂ))))ᴴ *
        diagonalEnvironmentBlocks (Sum.elim H (fun _ : Unit => K)) *
          environmentEmbedding (e := e) (Sum.elim (fun a => 2 * g a) (fun _ : Unit => (1 : ℂ))) = 0) :
    K = ∑ a, (star (g a) * g a) • H a := by
  rw [diagonal_environment_mixed_block, Fintype.sum_sum_type] at hcross
  have hstar : star (-2 : ℂ) = -2 := by norm_num
  have h : (∑ a, (star (g a) * (2 * g a)) • H a) + (-2 : ℂ) • K = 0 := by
    simpa [hstar] using hcross
  have hcoef (a : s) : (star (g a) * (2 * g a)) • H a =
      (2 : ℂ) • ((star (g a) * g a) • H a) := by
    rw [smul_smul]
    congr 1
    ring
  simp_rw [hcoef] at h
  rw [← Finset.smul_sum, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h
  exact (sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left (by norm_num))).symm

end ManuscriptProofs.Quantum
