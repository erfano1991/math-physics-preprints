import ManuscriptProofs.Quantum.FiniteCopyLists
import ManuscriptProofs.Quantum.NoiselessCode

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker

namespace ManuscriptProofs.Quantum

section Dilation

variable {D K : Type*} [Fintype D] [Fintype K] [DecidableEq D] [DecidableEq K]

/-- Compression along a Stinespring isometry in coordinates. -/
def compress (V : Matrix K D ℂ) (G : Operator K) : Operator D :=
  Vᴴ * G * V

/-- The adjoint of compression in the trace pairing. -/
def liftToDilation (V : Matrix K D ℂ) (Z : Operator D) : Operator K :=
  V * Z * Vᴴ

omit [DecidableEq D] [DecidableEq K] in
theorem trace_lift_pair (V : Matrix K D ℂ) (Z : Operator D) (G : Operator K) :
    (liftToDilation V Z * G).trace = (Z * compress V G).trace := by
  calc
    _ = (V * (Z * (Vᴴ * G))).trace := by simp only [liftToDilation, Matrix.mul_assoc]
    _ = ((Z * (Vᴴ * G)) * V).trace := Matrix.trace_mul_comm _ _
    _ = _ := by simp only [compress, Matrix.mul_assoc]

omit [DecidableEq D] in
/-- Complementary slackness on the compressed parent survives lifting to
the full dilation. The proof uses the rectangular trace identity and
the exact zero-pairing result for positive matrices. -/
theorem lift_annihilates_of_compressed_slack (V : Matrix K D ℂ) (Z : Operator D) (G : Operator K)
    (hZ : Z.PosSemidef) (hG : G.PosSemidef) (hslack : Z * compress V G = 0) :
    (liftToDilation V Z).PosSemidef ∧ liftToDilation V Z * G = 0 := by
  have hL : (liftToDilation V Z).PosSemidef := hZ.mul_mul_conjTranspose_same V
  refine ⟨hL, (psd_trace_pair _ _ hL hG).2 ?_⟩
  rw [trace_lift_pair, hslack, Matrix.trace_zero]

omit [DecidableEq K] in
/-- The lifted matrix is supported in the isometry range on both sides
and compresses back to the original matrix. -/
theorem lift_compress_support (V : Matrix K D ℂ) (hV : Vᴴ * V = 1) (H : Operator D) :
    compress V (liftToDilation V H) = H ∧
      (V * Vᴴ) * liftToDilation V H = liftToDilation V H ∧
      liftToDilation V H * (V * Vᴴ) = liftToDilation V H := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (Vᴴ * V) * H * (Vᴴ * V) := by
        simp only [compress, liftToDilation, Matrix.mul_assoc]
      _ = _ := by simp [hV]
  · calc
      _ = V * (Vᴴ * V) * H * Vᴴ := by simp only [liftToDilation, Matrix.mul_assoc]
      _ = _ := by simp [hV, liftToDilation]
  · calc
      _ = V * H * (Vᴴ * V) * Vᴴ := by simp only [liftToDilation, Matrix.mul_assoc]
      _ = _ := by simp [hV, liftToDilation]

omit [DecidableEq K] in
theorem lift_ne_zero_of_isometry (V : Matrix K D ℂ) (hV : Vᴴ * V = 1)
    {H : Operator D} (hH : H ≠ 0) : liftToDilation V H ≠ 0 := by
  intro h
  have e := (lift_compress_support V hV H).1
  simp [h, compress] at e
  exact hH e.symm

omit [Fintype K] [DecidableEq D] [DecidableEq K] in
theorem lift_add (V : Matrix K D ℂ) (A B : Operator D) :
    liftToDilation V (A + B) = liftToDilation V A + liftToDilation V B := by
  simp [liftToDilation, Matrix.mul_add, Matrix.add_mul]

/-- A family of opposite dual slacks lifts to positive annihilators with
the common opposite sum, supported in the dilation range. -/
theorem lift_opposite_slack_family {S : Type*} (V : Matrix K D ℂ) (hV : Vᴴ * V = 1)
    (H : Operator D) (hH : H.PosSemidef) (hne : H ≠ 0)
    (opp : S → S) (Z : S → Operator D) (G : S → Operator K)
    (hZ : ∀ s, (Z s).PosSemidef) (hG : ∀ s, (G s).PosSemidef)
    (hzero : ∀ s, Z s * compress V (G s) = 0) (hsum : ∀ s, Z s + Z (opp s) = H + H) :
    let L := liftToDilation V H
    L.PosSemidef ∧ L ≠ 0 ∧ (V * Vᴴ) * L = L ∧
      ∀ s, (liftToDilation V (Z s)).PosSemidef ∧ liftToDilation V (Z s) * G s = 0 ∧
        liftToDilation V (Z s) + liftToDilation V (Z (opp s)) = L + L := by
  dsimp only
  refine ⟨hH.mul_mul_conjTranspose_same V, lift_ne_zero_of_isometry V hV hne,
    (lift_compress_support V hV H).2.1, fun s => ?_⟩
  obtain ⟨hz, hk⟩ := lift_annihilates_of_compressed_slack V (Z s) (G s) (hZ s) (hG s) (hzero s)
  exact ⟨hz, hk, by rw [← lift_add, hsum, lift_add]⟩

end Dilation

section ProductCode

variable {d e D : Type*}
  [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e] [Fintype D] [DecidableEq D]

/-- Send a system basis vector to its product with an environment vector. -/
def productEncoding (h : e → ℂ) : Matrix (d × e) d ℂ :=
  Matrix.of fun a b => if a.1 = b then h a.2 else 0

private theorem kronecker_mul_productEncoding (h : e → ℂ) (X : Operator d)
    (a : d) (t : e) (b : d) :
    ((X ⊗ₖ (1 : Operator e)) * productEncoding (d := d) h : Matrix (d × e) d ℂ)
      (a, t) b = X a b * h t := by
  simp only [Matrix.mul_apply, productEncoding, Matrix.kronecker_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.one_apply]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- Exact preservation of every system matrix on a product encoding
with a normalized environment vector. -/
theorem product_encoding_exact (h : e → ℂ) (hh : star h ⬝ᵥ h = 1) (X : Operator d) :
    (productEncoding h)ᴴ * (X ⊗ₖ (1 : Operator e)) * productEncoding h = X := by
  ext a b
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.conjTranspose_apply, kronecker_mul_productEncoding]
  simp only [productEncoding, Matrix.of_apply, apply_ite star, star_zero, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [show ∀ t, star (h t) * (X a b * h t) = X a b * (star (h t) * h t) from
    fun _ => by ring]
  rw [← Finset.mul_sum]
  change X a b * (star h ⬝ᵥ h) = X a b
  rw [hh, mul_one]

/-- If the dilation range contains a normalized product code, its
pullback along the isometry implements an exact noiseless encoding. -/
theorem noiseless_code_of_product_range (V : Matrix (d × e) D ℂ) (hV : Vᴴ * V = 1)
    (h : e → ℂ) (hh : star h ⬝ᵥ h = 1)
    (hfixed : (V * Vᴴ) * productEncoding h = productEncoding h) :
    ∃ J : Matrix D d ℂ, Jᴴ * J = 1 ∧
      ∀ X : Operator d, Jᴴ * compress V (X ⊗ₖ (1 : Operator e)) * J = X := by
  let J := Vᴴ * (productEncoding h : Matrix (d × e) d ℂ)
  have hJ : V * J = productEncoding h := by
    change V * (Vᴴ * productEncoding h) = _
    rw [← Matrix.mul_assoc, hfixed]
  have hX (X : Operator d) :
      Jᴴ * compress V (X ⊗ₖ (1 : Operator e)) * J = X := by
    calc
      _ = (V * J)ᴴ * (X ⊗ₖ (1 : Operator e)) * (V * J) := by
        simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hJ]; exact product_encoding_exact h hh X
  refine ⟨J, ?_, hX⟩
  have hi := hX 1
  rw [Matrix.one_kronecker_one] at hi
  simpa [compress, hV] using hi

private theorem productEncoding_column (H : Operator e) (j : e) (c : ℂ) :
    ((1 : Operator d) ⊗ₖ H) * productEncoding (d := d) (fun i => if i = j then c else 0) =
      productEncoding (fun i => c * H i j) := by
  ext a b
  rcases a with ⟨a,t⟩
  simp only [Matrix.mul_apply, Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply,
    productEncoding, Matrix.of_apply]
  by_cases he : a = b
  · subst b
    simp [mul_ite, Finset.sum_ite_eq', mul_comm]
  · simp [he, mul_ite, ite_mul, Finset.sum_ite_eq']

/-- A nonzero lifted constant of the form I ⊗ H contains a normalized
product range and therefore yields an exact noiseless code. -/
theorem noiseless_code_of_lift_factorization
    (V : Matrix (d × e) D ℂ) (hV : Vᴴ * V = 1) (L : Operator D) (H : Operator e)
    (hH : H ≠ 0) (hfactor : liftToDilation V L = (1 : Operator d) ⊗ₖ H) :
    ∃ J : Matrix D d ℂ, Jᴴ * J = 1 ∧
      ∀ X : Operator d, Jᴴ * compress V (X ⊗ₖ (1 : Operator e)) * J = X := by
  have hex : ∃ j : e, (fun i => H i j) ≠ 0 := by
    by_contra! h
    apply hH
    ext i j
    exact congrFun (h j) i
  obtain ⟨j, hz⟩ := hex
  let z : e → ℂ := fun i => H i j
  let q : ℝ := (star z ⬝ᵥ z).re
  have hq : 0 < q := (Complex.pos_iff.mp (Matrix.dotProduct_star_self_pos_iff.mpr hz)).1
  have hqReal : star z ⬝ᵥ z = (q : ℂ) :=
    Complex.eq_re_of_ofReal_le (dotProduct_star_self_nonneg z)
  let r := (Real.sqrt q)⁻¹
  let h (i : e) := (r : ℂ) * z i
  have hr : r * r * q = 1 := by
    have hs := Real.sq_sqrt hq.le
    have hne := (Real.sqrt_pos.2 hq).ne'
    dsimp [r]
    field_simp
    simpa [pow_two] using hs.symm
  have hh : star h ⬝ᵥ h = 1 := by
    calc
      _ = (r : ℂ) * (r : ℂ) * (star z ⬝ᵥ z) := by
        simp only [h, dotProduct, Pi.star_apply, star_mul, Complex.star_def,
          Complex.conj_ofReal, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [hqReal]; exact_mod_cast hr
  have hproj := (lift_compress_support V hV L).2.1
  rw [hfactor] at hproj
  have hfixed : (V * Vᴴ) * productEncoding h = productEncoding h := by
    have he := productEncoding_column (d := d) H j (r : ℂ)
    change _ = productEncoding h at he
    rw [← he, ← Matrix.mul_assoc, hproj]
  exact noiseless_code_of_product_range V hV h hh hfixed

end ProductCode

end ManuscriptProofs.Quantum
