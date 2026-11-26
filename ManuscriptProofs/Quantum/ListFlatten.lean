import ManuscriptProofs.Quantum.ListTensorExpansion

open scoped BigOperators ComplexOrder Matrix MatrixOrder Kronecker
namespace ManuscriptProofs.Quantum

universe u
variable {d : Type u}

/-- Concatenate two recursively indexed computational bases. The second
length is the left summand so recursion on the first length is definitional. -/
def appendBasis (k : ℕ) : (b : ℕ) → Copies d b × Copies d k ≃ Copies d (k+b)
  | 0 => Equiv.punitProd _
  | b+1 => (Equiv.prodAssoc d (Copies d b) (Copies d k)).trans
      ((Equiv.refl d).prodCongr (appendBasis k b))

private theorem tensor_append (A : Operator d) (k b : ℕ)
    (u v : Copies d b) (x y : Copies d k) :
    tensorPower A (k+b) (appendBasis (d := d) k b (u,x)) (appendBasis (d := d) k b (v,y)) =
      tensorPower A b u v * tensorPower A k x y := by
  induction b with
  | zero => cases u; cases v; simp [appendBasis, tensorPower, tensorFactors]
  | succ b ih =>
      rcases u with ⟨i,u⟩
      rcases v with ⟨j,v⟩
      change A i j * tensorPower A (k+b) (appendBasis (d := d) k b (u,x)) (appendBasis (d := d) k b (v,y)) =
        (A i j * tensorPower A b u v) * tensorPower A k x y
      rw [ih, mul_assoc]

private def slots (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => slots b m + b

private theorem slots_eq (b m : ℕ) : slots b m = b*m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [slots, Nat.mul_succ, ih]

private def flattenBasis (b : ℕ) : (m : ℕ) → Copies (Copies d b) m ≃ Copies d (slots b m)
  | 0 => Equiv.refl _
  | m+1 => ((Equiv.refl (Copies d b)).prodCongr (flattenBasis b m)).trans (appendBasis _ b)

private theorem tensor_flatten (A : Operator d) (b m : ℕ) (u v : Copies (Copies d b) m) :
    tensorPower A (slots b m) (flattenBasis (d := d) b m u) (flattenBasis (d := d) b m v) =
    tensorPower (tensorPower A b) m u v := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a,x⟩
      rcases v with ⟨c,y⟩
      change tensorPower A (slots b m + b)
        (appendBasis (d := d) (slots b m) b (a,flattenBasis (d := d) b m x)) (appendBasis (d := d) (slots b m) b (c,flattenBasis (d := d) b m y)) =
        tensorPower A b a c * tensorPower (tensorPower A b) m x y
      rw [tensor_append, ih]

/-- Relabel the effects of a block measurement without changing a single
Born probability. Both sides use the paper's ordinary copy and POVM definitions. -/
theorem zero_error_flatten {ι Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]
    (ρ : ι → Operator d) (lists : Ω → Set ι) (b m : ℕ)
    (h : ZeroError (fun i => tensorPower (ρ i) b) lists m) :
    ZeroError ρ lists (b*m) := by
  rw [← slots_eq]
  obtain ⟨M, hM⟩ := h
  let e := (flattenBasis (d := d) b m).symm
  let N : POVM (Copies d (slots b m)) Ω := {
    effect := fun o => (M.effect o).submatrix e e
    pos := fun o => (M.pos o).submatrix _
    sum_eq_one := by
      ext x y
      have hm := congrFun (congrFun M.sum_eq_one (e x)) (e y)
      simpa [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply] using hm }
  refine ⟨N, fun o i hi => ?_⟩
  have hpow : tensorPower (ρ i) (slots b m) =
      (tensorPower (tensorPower (ρ i) b) m).submatrix e e := by
    ext x y
    simpa [e] using tensor_flatten (ρ i) b m (e x) (e y)
  change ((M.effect o).submatrix e e * tensorPower (ρ i) (slots b m)).trace = 0
  rw [hpow, Matrix.submatrix_mul_equiv]
  exact (e.sum_comp (fun x => (M.effect o * tensorPower (tensorPower (ρ i) b) m) x x)).trans
    (hM o i hi)

/-- The finite-copy list characterization, in both directions on a single
ordinary tensor power, for nonempty finite input and output alphabets. -/
theorem finite_copy_lists_iff {ι Ω : Type*} [Fintype d] [DecidableEq d]
    [Fintype ι] [Nonempty ι] [Fintype Ω] [Nonempty Ω]
    (ρ : ι → Operator d) (hρ : ∀ i, (ρ i).PosSemidef) (lists : Ω → Set ι) :
    (∃ n : ℕ, 0 < n ∧ ZeroError ρ lists n) ↔
      ∀ x y : d → ℂ, star x ⬝ᵥ y ≠ 0 →
        ∃ o, ∀ i, ((∃ v, ρ i *ᵥ v = x) ∨ (∃ w, ρ i *ᵥ w = y)) → i ∈ lists o := by
  constructor
  · rintro ⟨n, _, hn⟩
    exact lists_necessary ρ hρ lists n hn
  · intro hc
    obtain ⟨m, hm, hM⟩ := zero_error_on_blocks_of_list_condition ρ hρ lists hc
    exact ⟨_, Nat.mul_pos (Nat.mul_pos (by decide : 0 < 2) Fintype.card_pos) hm,
      zero_error_flatten ρ lists _ m hM⟩

end ManuscriptProofs.Quantum
