import ManuscriptProofs.Quantum.POVM
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic.Ring

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

namespace ManuscriptProofs.Quantum

universe u

variable {d : Type*} [Fintype d]

/-- Zero trace pairing of two positive effects forces their product to vanish. -/
theorem psd_trace_pair [DecidableEq d] (A B : Operator d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace ∧ ((A * B).trace = 0 → A * B = 0) := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [hX, hY]
  change 0 ≤ ((Xᴴ * X) * (Yᴴ * Y)).trace ∧
    (((Xᴴ * X) * (Yᴴ * Y)).trace = 0 → (Xᴴ * X) * (Yᴴ * Y) = 0)
  have heq : ((X * Yᴴ)ᴴ * (X * Yᴴ)).trace = ((Xᴴ * X) * (Yᴴ * Y)).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc Y, Matrix.trace_mul_comm Y]
    simp only [Matrix.mul_assoc]
  refine ⟨heq ▸ (Matrix.posSemidef_conjTranspose_mul_self (X * Yᴴ)).trace_nonneg, fun h => ?_⟩
  have h0 : X * Yᴴ = 0 :=
    Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (heq.trans h)
  calc
    (Xᴴ * X) * (Yᴴ * Y) = Xᴴ * (X * Yᴴ) * Y := by simp only [Matrix.mul_assoc]
    _ = 0 := by simp [h0]

/-- Computational basis for repeated copies; the zero-copy basis is a singleton. -/
abbrev Copies (d : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => d × Copies d n

instance copyFintype (n : ℕ) : Fintype (Copies d n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd d (Copies d n) _ ih

instance copyDecidableEq [DecidableEq d] (n : ℕ) : DecidableEq (Copies d n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq PUnit)
  | succ n ih => exact @instDecidableEqProd d (Copies d n) _ ih

/-- Kronecker product of a finite ordered family of operators. -/
def tensorFactors : {n : ℕ} → (Fin n → Operator d) → Operator (Copies d n)
  | 0, _ => 1
  | n + 1, A => A 0 ⊗ₖ tensorFactors (fun i : Fin n => A i.succ)

/-- The tensor power of a single matrix. -/
def tensorPower (A : Operator d) (n : ℕ) : Operator (Copies d n) :=
  tensorFactors (fun _ : Fin n => A)

/-- Repeated pure vector in the same computational basis. -/
def vectorPower (x : d → ℂ) : (n : ℕ) → Copies d n → ℂ
  | 0, _ => 1
  | n + 1, (i, j) => x i * vectorPower x n j

theorem tensorFactors_pos {n : ℕ} (A : Fin n → Operator d) (hA : ∀ j, (A j).PosSemidef) :
    (tensorFactors A).PosSemidef := by
  induction n with
  | zero => exact Matrix.PosSemidef.one
  | succ n ih =>
      exact (hA 0).kronecker (ih (fun i => A i.succ) (fun i => hA i.succ))

theorem tensorFactors_mul {n : ℕ} (A B : Fin n → Operator d) :
    tensorFactors (fun i => A i * B i) = tensorFactors A * tensorFactors B := by
  induction n with
  | zero => simp [tensorFactors]
  | succ n ih =>
      simp only [tensorFactors]
      rw [ih, Matrix.mul_kronecker_mul]

theorem trace_tensorFactors {n : ℕ} (A : Fin n → Operator d) :
    (tensorFactors A).trace = ∏ j, (A j).trace := by
  induction n with
  | zero => simp [tensorFactors, Matrix.trace_one, Copies]
  | succ n ih =>
      change (A 0 ⊗ₖ tensorFactors (fun i : Fin n => A i.succ)).trace = _
      rw [Matrix.trace_kronecker, ih, Fin.prod_univ_succ]

theorem tensorPower_mulVec (A : Operator d) (x : d → ℂ) (n : ℕ) :
    tensorPower A n *ᵥ vectorPower x n = vectorPower (A *ᵥ x) n := by
  induction n with
  | zero => simp [tensorPower, tensorFactors, vectorPower]
  | succ n ih =>
      ext z
      rcases z with ⟨a, b⟩
      change ((A ⊗ₖ tensorPower A n) *ᵥ vectorPower x (n + 1)) (a, b) =
        (A *ᵥ x) a * vectorPower (A *ᵥ x) n b
      -- Expand the product-index sum into the two independent sums.
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
      simp only [Matrix.kronecker_apply, vectorPower]
      have hx := congrFun ih b
      change (∑ j, tensorPower A n b j * vectorPower x n j) =
        vectorPower (A *ᵥ x) n b at hx
      rw [← hx, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring

theorem inner_vectorPower (x y : d → ℂ) (n : ℕ) :
    star (vectorPower x n) ⬝ᵥ vectorPower y n = (star x ⬝ᵥ y) ^ n := by
  induction n with
  | zero => simp [dotProduct, vectorPower, Copies, Pi.star_apply]
  | succ n ih =>
      change (∑ k : d × Copies d n,
        star (x k.1 * vectorPower x n k.2) * (y k.1 * vectorPower y n k.2)) =
        (star x ⬝ᵥ y) ^ (n + 1)
      rw [Fintype.sum_prod_type, pow_succ', ← ih, dotProduct, dotProduct, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by simp only [star_mul, Pi.star_apply]; ring

variable [DecidableEq d]

/-- A zero-error POVM for the indicated allowed lists, measured on repeated
density operators. The hypothesis is the actual zero Born probability. -/
def ZeroError {ι Ω : Type*} [Fintype Ω] (ρ : ι → Operator d) (lists : Ω → Set ι) (n : ℕ) :
    Prop :=
  ∃ M : POVM (Copies d n) Ω,
    ∀ o i, i ∉ lists o → (M.effect o * tensorPower (ρ i) n).trace = 0

/-- Necessity of the nonorthogonal-pair condition in the allowed-list theorem. -/
theorem lists_necessary {ι Ω : Type*} [Fintype Ω] (ρ : ι → Operator d)
    (hρ : ∀ i, (ρ i).PosSemidef) (lists : Ω → Set ι) (n : ℕ) (hz : ZeroError ρ lists n)
    (x y : d → ℂ) (hxy : star x ⬝ᵥ y ≠ 0) :
    ∃ o, ∀ i, ((∃ v, ρ i *ᵥ v = x) ∨ (∃ w, ρ i *ᵥ w = y)) → i ∈ lists o := by
  classical
  obtain ⟨M, hM⟩ := hz
  have hann (o : Ω) (i : ι) (hi : i ∉ lists o) (v : d → ℂ) :
      M.effect o *ᵥ vectorPower (ρ i *ᵥ v) n = 0 := by
    rw [← tensorPower_mulVec, Matrix.mulVec_mulVec]
    have hp : (tensorPower (ρ i) n).PosSemidef :=
      tensorFactors_pos (fun _ : Fin n => ρ i) (fun _ => hρ i)
    rw [(psd_trace_pair _ _ (M.pos o) hp).2 (hM o i hi), Matrix.zero_mulVec]
  have hnonzero : ∃ o, star (vectorPower x n) ⬝ᵥ M.effect o *ᵥ vectorPower y n ≠ 0 := by
    by_contra! h
    have hs : (∑ o, star (vectorPower x n) ⬝ᵥ M.effect o *ᵥ vectorPower y n) = 0 :=
      Finset.sum_eq_zero (fun o _ => h o)
    apply pow_ne_zero n hxy
    calc
      _ = star (vectorPower x n) ⬝ᵥ vectorPower y n := (inner_vectorPower x y n).symm
      _ = star (vectorPower x n) ⬝ᵥ ((∑ o, M.effect o) *ᵥ vectorPower y n) := by
        rw [M.sum_eq_one, Matrix.one_mulVec]
      _ = 0 := by rw [Matrix.sum_mulVec, dotProduct_sum, hs]
  obtain ⟨o, ho⟩ := hnonzero
  refine ⟨o, fun i hx => ?_⟩
  by_contra hi
  apply ho
  rcases hx with ⟨v, hv⟩ | ⟨w, hw⟩
  · have he : M.effect o *ᵥ vectorPower x n = 0 := hv ▸ hann o i hi v
    rw [Matrix.dotProduct_mulVec, ← (M.pos o).isHermitian.eq,
      ← Matrix.star_mulVec, he, star_zero, zero_dotProduct]
  · rw [← hw, hann o i hi w, dotProduct_zero]

/-- The separable obstruction from one trace witness. Each effect is a finite
sum of positive product operators, and every local factor that vanishes in
Born pairing on the excluded state is annihilated by the witness. -/
theorem no_separable_exclusion_of_witness {ι : Type*} [Fintype ι]
    (ρ : ι → Operator d) (hρ : ∀ i, (ρ i).PosSemidef)
    (W : Operator d) (hW : W.trace ≠ 0)
    (hkill : ∀ i (A : Operator d), A.PosSemidef → (A * ρ i).trace = 0 → (A * W).trace = 0)
    (n : ℕ) (M : POVM (Copies d n) ι)
    (hzero : ∀ i, (M.effect i * tensorPower (ρ i) n).trace = 0)
    (hsep : ∀ i, ∃ (m : ℕ) (A : Fin m → Fin n → Operator d),
      (∀ r j, (A r j).PosSemidef) ∧ M.effect i = ∑ r, tensorFactors (A r)) : False := by
  classical
  have hp (i : ι) : (M.effect i * tensorPower W n).trace = 0 := by
    obtain ⟨m, A, hA, hm⟩ := hsep i
    have hz := hzero i
    rw [hm, Matrix.sum_mul, Matrix.trace_sum] at hz ⊢
    simp_rw [tensorPower, ← tensorFactors_mul, trace_tensorFactors] at hz ⊢
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun r : Fin m => ∏ j, (A r j * ρ i).trace)
      (fun r _ => Finset.prod_nonneg (fun j _ => (psd_trace_pair _ _ (hA r j) (hρ i)).1))).mp hz
    apply Finset.sum_eq_zero
    intro r hr
    obtain ⟨j, hj, hjz⟩ := Finset.prod_eq_zero_iff.mp (hterm r hr)
    exact Finset.prod_eq_zero hj (hkill i (A r j) (hA r j) hjz)
  have hw := Finset.sum_eq_zero (s := (Finset.univ : Finset ι)) (fun i _ => hp i)
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, M.sum_eq_one, one_mul, tensorPower,
    trace_tensorFactors, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hw
  exact (pow_ne_zero n hW) hw

end ManuscriptProofs.Quantum
