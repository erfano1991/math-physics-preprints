import ManuscriptProofs.Quantum.POVM
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

open scoped BigOperators Matrix ComplexOrder MatrixOrder

namespace ManuscriptProofs.Quantum

/-- Gershgorin on the actual selected Gram matrix. Indexing by selected
labels makes different occurrences of the same parent coordinate harmless. -/
theorem selected_gram_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (μ ev : ℝ) (hd : ∀ i, G i i = 1)
    (ho : ∀ i j, i ≠ j → ‖G i j‖ ≤ μ)
    (he : Module.End.HasEigenvalue G.toLin' (ev : ℂ)) :
    ev ≤ 1 + (Fintype.card ι - 1 : ℕ)*μ := by
  obtain ⟨i,hi⟩ := eigenvalue_mem_ball he
  rw [Metric.mem_closedBall, dist_eq_norm, hd] at hi
  have hsum : (∑ j ∈ Finset.univ.erase i, ‖G i j‖) ≤
      (Fintype.card ι - 1 : ℕ)*μ := calc
    _ ≤ ∑ _ ∈ Finset.univ.erase i, μ := Finset.sum_le_sum fun j hj => ho i j (Finset.mem_erase.mp hj).1.symm
    _ = _ := by simp [Finset.card_erase_of_mem, nsmul_eq_mul]
  have hreal : ev-1 ≤ ‖(ev:ℂ)-1‖ := by
    simpa using Complex.re_le_norm ((ev:ℂ)-1)
  linarith

private theorem positive_trace_pair {d : Type*} [Fintype d] [DecidableEq d]
    {X G : Operator d} (hx : 0 ≤ X) (hg : G.PosSemidef) : 0 ≤ (X*G).trace.re := by
  obtain ⟨B,hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hg.nonneg
  rw [hB, Matrix.star_eq_conjTranspose]
  have hcyc : (X*(Bᴴ*B)).trace = (B*X*Bᴴ).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (X*Bᴴ) B, ← Matrix.mul_assoc]
  rw [hcyc]
  exact (Matrix.nonneg_iff_posSemidef.mp hx |>.mul_mul_conjTranspose_same B).trace_nonneg.1

/-- Transfer the Gram bound from Aᴴ A to the positive matrix A Aᴴ. The
rectangular characteristic-polynomial identity handles unequal dimensions. -/
theorem selected_frame_bound {d ι : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype ι] [DecidableEq ι] (A : Matrix d ι ℂ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hd : ∀ i, (Aᴴ*A) i i = 1) (ho : ∀ i j, i ≠ j → ‖(Aᴴ*A) i j‖ ≤ μ) :
    A*Aᴴ ≤ (1 + (Fintype.card ι - 1 : ℕ)*μ) • (1 : Operator d) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply le_algebraMap_of_spectrum_le
  · intro r hr
    by_cases hz : r = 0
    · subst r; positivity
    have hr' : (r : ℂ) ∈ spectrum ℂ (A*Aᴴ) := (spectrum.algebraMap_mem_iff ℂ).mpr hr
    have hr₁ := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hr'
    have hpoly := congrArg (Polynomial.eval (r:ℂ)) (Matrix.charpoly_mul_comm' A Aᴴ)
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, hr₁.eq_zero, mul_zero] at hpoly
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
    have hr₂ := (mul_eq_zero.mp hpoly.symm).resolve_left (pow_ne_zero _ hn)
    apply selected_gram_bound (Aᴴ*A) μ r hd ho
    rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr hr₂
  · exact (Matrix.posSemidef_self_mul_conjTranspose A).isHermitian

/-- A retained positive qubit effect has a strictly positive normalized
trace, as required by the perturbation parent. -/
theorem retained_trace_pos {E : Operator (Fin 2)} (h : E.PosSemidef) (hn : E ≠ 0) :
    0 < E.trace.re/2 := by
  have hne : E.trace ≠ 0 := fun he => hn (h.trace_eq_zero_iff.mp he)
  have hp : 0 < E.trace := lt_of_le_of_ne h.trace_nonneg hne.symm
  exact div_pos hp.1 (by norm_num)

/-- Sum the selected marginal events against the normalized qubit trace.
No disjointness is assumed of the events: each atom uses precisely the
witnesses of the events it reports. -/
theorem parent_string_witness {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq Ω]
    (G : POVM (Fin 2) Ω) (W : ι → Operator (Fin 2)) (events : ι → Finset Ω) (δ : ℝ)
    (h : ∀ o, (∑ i, if o ∈ events i then W i else 0) ≤ δ • (1 : Operator (Fin 2))) :
    (∑ i, (W i * G.event (events i)).trace.re)/2 ≤ δ := by
  classical
  let T := fun o => ∑ i, if o ∈ events i then W i else 0
  have atom (o : Ω) : (T o * G.effect o).trace.re ≤
      ((δ • (1 : Operator (Fin 2))) * G.effect o).trace.re := by
    have hp := positive_trace_pair (sub_nonneg.mpr (h o)) (G.pos o)
    simpa only [sub_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using hp
  have expand (i : ι) : (W i * G.event (events i)).trace.re =
      ∑ o, ((if o ∈ events i then W i else 0) * G.effect o).trace.re := by
    simp [POVM.event, Matrix.mul_sum, Matrix.trace_sum, ite_mul,
      apply_ite, Finset.sum_ite_mem]
  have regroup : ∑ i, (W i * G.event (events i)).trace.re =
      ∑ o, (T o * G.effect o).trace.re := by
    simp_rw [expand]
    rw [Finset.sum_comm]
    simp [T, Matrix.sum_mul, Matrix.trace_sum]
  rw [regroup]
  have bound := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => atom o)
  have normalization : (∑ o, ((δ • (1 : Operator (Fin 2))) * G.effect o).trace.re) = 2*δ := by
    simp only [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum, G.sum_eq_one, mul_one,
      Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
    simp [Complex.real_smul, mul_comm]
  rw [normalization] at bound
  linarith

end ManuscriptProofs.Quantum
