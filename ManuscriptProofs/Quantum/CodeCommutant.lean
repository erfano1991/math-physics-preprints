import ManuscriptProofs.Quantum.ThreeSettingRigidity
import ManuscriptProofs.Quantum.NoiselessCode

open scoped BigOperators Matrix Kronecker

namespace ManuscriptProofs.Quantum

/-- The positive plane parameters used for B distinguish the paired
anticommutator eigenspaces and give a nonzero flip on every such plane. -/
theorem paired_plane_parameters {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) (hv : v < 1) :
    2*u/(1+u^2) < 2*v/(1+v^2) ∧ 0 < (1-u^2)/(1+u^2) := by
  have hv0 := hu.trans huv.le
  have huv1 : u*v < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (huv.trans hv).le hv0) (by simpa using hv)
  constructor
  · apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_pos (sub_pos.mpr huv) (sub_pos.mpr huv1)]
  · apply div_pos _ (by positivity)
    nlinarith [mul_pos (sub_pos.mpr (huv.trans hv)) (show 0 < 1+u by linarith)]

/-- Squared absolute entry of I + (z-1) vv*, z=(399+40i)/401,
v the flat unit vector. The entry is written in real and imaginary parts. -/
theorem flat_mixer_weight (n : ℝ) (hn : n ≠ 0) (same : Bool) :
    Complex.normSq ⟨(if same then 1 else 0) - 2/(401*n), 40/(401*n)⟩ =
      (if same then 1 - (n-1)*(4/(401*n^2)) else 4/(401*n^2)) := by
  cases same <;> simp [Complex.normSq_apply] <;> field_simp <;> ring

variable {s e : Type*} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]

omit [Fintype s] [Fintype e] in
private theorem lift_diagonal (z : s → ℂ) :
    (Matrix.diagonal z ⊗ₖ (1 : Operator e)) =
      Matrix.diagonal (fun p : s × e => z p.1) := by
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j <;> by_cases k : x=y <;>
    simp [h, k]

private theorem comm_diag_entry (L : Operator (s × e)) (z : s → ℂ)
    (h : Commute L (Matrix.diagonal z ⊗ₖ (1 : Operator e)))
    (i j : s) (x y : e) :
    L (i,x) (j,y) * (z j - z i) = 0 := by
  rw [lift_diagonal] at h
  have hh := congrFun (congrFun h.eq (i,x)) (j,y)
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hh
  linear_combination hh

/-- The two lifted commutators give actual environment blocks. The separation
condition says that the sign and the anticommutator eigenvalue together
distinguish system basis vectors, including the possible unpaired line. -/
theorem blocks_of_two_commutators (L : Operator (s × e)) (B : Operator s) (z : s → ℂ)
    (hz : Commute L (Matrix.diagonal z ⊗ₖ (1 : Operator e)))
    (hb : Commute L (B ⊗ₖ (1 : Operator e)))
    (hoff : ∀ i j, i ≠ j → (z i + z j)*B i j = 0)
    (hsep : ∀ i j, z i = z j → 2*z i*B i i = 2*z j*B j j → i=j) :
    ∃ H : s → Operator e, L = diagonalEnvironmentBlocks H ∧
      ∀ i j, B i j ≠ 0 → H i = H j := by
  let q := fun i => 2*z i*B i i
  have hanti : Matrix.diagonal z * B + B * Matrix.diagonal z = Matrix.diagonal q := by
    ext i j
    simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_apply]
    split_ifs with h
    · subst j; dsimp [q]; ring
    · linear_combination hoff i j h
  have hq : Commute L (Matrix.diagonal q ⊗ₖ (1 : Operator e)) := by
    have h := (hz.mul_right hb).add_right (hb.mul_right hz)
    simpa only [← Matrix.mul_kronecker_mul, mul_one, ← Matrix.add_kronecker, hanti] using h
  let H : s → Operator e := fun i x y => L (i,x) (i,y)
  have hblock : L = diagonalEnvironmentBlocks H := by
    ext ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp [diagonalEnvironmentBlocks, H]
    · simp [diagonalEnvironmentBlocks, h]
      by_contra hn
      have hz' := (mul_eq_zero.mp (comm_diag_entry L z hz i j x y)).resolve_left hn
      have hq' := (mul_eq_zero.mp (comm_diag_entry L q hq i j x y)).resolve_left hn
      exact h (hsep i j (sub_eq_zero.mp hz').symm (sub_eq_zero.mp hq').symm)
  refine ⟨H, hblock, ?_⟩
  intro i j hij
  ext x y
  have h := congrFun (congrFun hb.eq (i,x)) (j,y)
  rw [hblock] at h
  simp [Matrix.mul_apply, Fintype.sum_prod_type, diagonalEnvironmentBlocks,
    Matrix.one_apply, mul_ite, ite_mul, Finset.sum_ite_eq'] at h
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show (H i x y - H j x y) * B i j = 0 by linear_combination h)).resolve_right hij

/-- Combining the commutators with the third-pair averaging equations yields
I ⊗ H on the entire system, with at most one missing averaging equation.
Each system index is either its representative or is connected to it by B. -/
theorem three_setting_product_rigidity {κ : Type*} [Fintype κ] [Nonempty κ]
    (L : Operator (s × e)) (B : Operator s) (z : s → ℂ)
    (hz : Commute L (Matrix.diagonal z ⊗ₖ (1 : Operator e)))
    (hb : Commute L (B ⊗ₖ (1 : Operator e)))
    (hoff : ∀ i j, i ≠ j → (z i + z j)*B i j = 0)
    (hsep : ∀ i j, z i = z j → 2*z i*B i i = 2*z j*B j j → i=j)
    (key : s → κ) (rep : κ → s)
    (hedge : ∀ i, i=rep (key i) ∨ B i (rep (key i)) ≠ 0)
    (K : Finset κ) (hK : ∀ i j, i ∉ K → j ∉ K → i=j)
    (c : ℝ) (hc : c ≠ 0)
    (havg : ∀ i ∈ K, ∀ x y : e,
      L (rep i,x) (rep i,y) =
        (1-(Fintype.card κ : ℝ)*c) • L (rep i,x) (rep i,y) +
          c • ∑ j, L (rep j,x) (rep j,y)) :
    ∃ H : Operator e, L = (1 : Operator s) ⊗ₖ H := by
  obtain ⟨T,hL,hlink⟩ := blocks_of_two_commutators L B z hz hb hoff hsep
  have hav : ∀ i ∈ K, T (rep i) =
      (1-(Fintype.card κ : ℝ)*c) • T (rep i) + c • ∑ j, T (rep j) := by
    intro i hi
    ext x y
    simpa [hL, diagonalEnvironmentBlocks, Matrix.sum_apply] using havg i hi x y
  obtain ⟨H,hH⟩ := uniform_block_rigidity (fun i => T (rep i)) c hc K hK hav
  have hall (i : s) : T i = H := by
    rcases hedge i with h | h
    · exact (congrArg T h).trans (hH _)
    · exact (hlink _ _ h).trans (hH _)
  refine ⟨H, ?_⟩
  rw [hL]
  ext ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j <;> simp [diagonalEnvironmentBlocks, h, hall]

end ManuscriptProofs.Quantum
