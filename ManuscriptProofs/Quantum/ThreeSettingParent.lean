import ManuscriptProofs.Quantum.POVM
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace ManuscriptProofs.Quantum

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
private theorem psd_of_square_twice {Q : Operator d} (hQ : Qᴴ = Q)
    (h : Q * Q = (2 : ℝ) • Q) : Q.PosSemidef := by
  have hp := (Matrix.posSemidef_conjTranspose_mul_self Q).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hQ, h, smul_smul] at hp
  norm_num at hp
  exact hp

private theorem one_add_involution_pos {A : Operator d} (hA : Aᴴ = A)
    (hA₂ : A * A = 1) : (1 + A).PosSemidef := by
  apply psd_of_square_twice (by simp [hA])
  calc
    _ = 1 + A + A + A * A := by noncomm_ring
    _ = _ := by rw [hA₂]; module

private theorem one_sub_involution_pos {A : Operator d} (hA : Aᴴ = A)
    (hA₂ : A * A = 1) : (1 - A).PosSemidef := by
  simpa [sub_eq_add_neg] using
    one_add_involution_pos (A := -A) (by simp [hA]) (by simpa using hA₂)

private theorem square_sub_tripotent_pos {C : Operator d} (hC : Cᴴ = C)
    (hC₃ : C * C * C = C) : (C * C - C).PosSemidef := by
  apply psd_of_square_twice (by simp [Matrix.conjTranspose_mul, hC])
  have hc : C * (C * C) = C := by simpa [Matrix.mul_assoc] using hC₃
  have hcc : (C * C) * (C * C) = C * C := by rw [← Matrix.mul_assoc, hC₃]
  calc
    _ = (C * C) * (C * C) - C * C * C - C * (C * C) + C * C := by noncomm_ring
    _ = _ := by rw [hcc, hC₃, hc]; module

private theorem one_add_mul_comm {A P : Operator d} (hAP : Commute A P) :
    Commute (1 + A) (1 + P) := by
  show (1 + A) * (1 + P) = (1 + P) * (1 + A)
  calc
    _ = 1 + A + P + A * P := by noncomm_ring
    _ = 1 + A + P + P * A := by rw [hAP.eq]
    _ = _ := by noncomm_ring

private theorem one_sub_mul_comm {A P : Operator d} (hAP : Commute A P) :
    Commute (1 - A) (1 + P) := by
  simpa [sub_eq_add_neg] using one_add_mul_comm (A := -A) (P := P) hAP.neg_left

/-- The six supported effects of the three binary measurements.
The two unused sign outcomes can be assigned zero effects. -/
noncomputable def sixEffects (A B C P : Operator d) (s : Fin 3 × Fin 2) : Operator d :=
  (1 / 6 : ℝ) •
    (![if s.2 = 1 then (1 + P) * (1 - A) else (1 + P) * (1 + A),
      if s.2 = 1 then 1 - B else 1 + B,
      if s.2 = 1 then 1 - P - C else 1 - P + C] : Fin 3 → Operator d) s.1

theorem sixEffects_sum (A B C P : Operator d) : ∑ s, sixEffects A B C P s = 1 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  simp [sixEffects, Fin.sum_univ_two, Matrix.mul_add, Matrix.mul_sub]
  module

/-- The explicit six effects form a POVM under the algebraic conditions
on the involutions and the third contraction. -/
noncomputable def sixEffectParent (A B C P : Operator d)
    (hA : Aᴴ = A) (hA₂ : A * A = 1)
    (hB : Bᴴ = B) (hB₂ : B * B = 1)
    (hC : Cᴴ = C) (hC₃ : C * C * C = C)
    (hP : P.PosSemidef) (hPC : P = 1 - C * C) (hAP : Commute A P) :
    POVM d (Fin 3 × Fin 2) where
  effect := sixEffects A B C P
  sum_eq_one := sixEffects_sum A B C P
  pos s := by
    rcases s with ⟨i, b⟩
    have hP' := Matrix.PosSemidef.one.add hP
    have aMinus := one_sub_involution_pos hA hA₂
    have aPlus := one_add_involution_pos hA hA₂
    have bMinus := one_sub_involution_pos hB hB₂
    have bPlus := one_add_involution_pos hB hB₂
    have eP : 1 - P = C * C := by rw [hPC]; abel
    have cMinus : (1 - P - C).PosSemidef := by rw [eP]; exact square_sub_tripotent_pos hC hC₃
    have cPlus : (1 - P + C).PosSemidef := by
      rw [eP]
      simpa using square_sub_tripotent_pos (C := -C) (by simp [hC]) (by simpa using hC₃)
    have aEffectMinus : ((1 + P) * (1 - A)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (Commute.mul_nonneg hP'.nonneg aMinus.nonneg (one_sub_mul_comm hAP).symm)
    have aEffectPlus : ((1 + P) * (1 + A)).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp
        (Commute.mul_nonneg hP'.nonneg aPlus.nonneg (one_add_mul_comm hAP).symm)
    have hw : (0 : ℝ) ≤ 1 / 6 := by norm_num
    fin_cases i <;> fin_cases b <;>
      first
      | exact aEffectPlus.smul hw
      | exact aEffectMinus.smul hw
      | exact bPlus.smul hw
      | exact bMinus.smul hw
      | exact cPlus.smul hw
      | exact cMinus.smul hw

/-- For each of the six supported effects, the matching dual slack has
zero product with it. This is the exact source complementarity identity. -/
theorem sixEffects_annihilation (A B C P : Operator d)
    (hA₂ : A * A = 1) (hB₂ : B * B = 1) (hC₃ : C * C * C = C)
    (hPC : P = 1 - C * C) (hAP : Commute A P) :
    ∀ s : Fin 3 × Fin 2,
      (if s.2 = 1 then 1 + (![A, B, C] : Fin 3 → Operator d) s.1
        else 1 - (![A, B, C] : Fin 3 → Operator d) s.1) *
        sixEffects A B C P s = 0 := by
  have killPlus {X : Operator d} (hx : X * X = 1) : (1 + X) * (1 - X) = 0 := by
    calc
      _ = 1 - X * X := by noncomm_ring
      _ = _ := by rw [hx, sub_self]
  have killMinus {X : Operator d} (hx : X * X = 1) : (1 - X) * (1 + X) = 0 := by
    calc
      _ = 1 - X * X := by noncomm_ring
      _ = _ := by rw [hx, sub_self]
  have hc : C * (C * C) = C := by simpa [Matrix.mul_assoc] using hC₃
  have hpc : 1 - P = C * C := by rw [hPC]; abel
  have hcPlus : (1 + C) * (1 - P - C) = 0 := by
    rw [hpc]
    calc
      _ = C * (C * C) - C := by noncomm_ring
      _ = _ := by rw [hc, sub_self]
  have hcMinus : (1 - C) * (1 - P + C) = 0 := by
    rw [hpc]
    calc
      _ = C - C * (C * C) := by noncomm_ring
      _ = _ := by rw [hc, sub_self]
  have haPlus : (1 + A) * ((1 + P) * (1 - A)) = 0 := by
    rw [← Matrix.mul_assoc, (one_add_mul_comm hAP).eq, Matrix.mul_assoc, killPlus hA₂, mul_zero]
  have haMinus : (1 - A) * ((1 + P) * (1 + A)) = 0 := by
    rw [← Matrix.mul_assoc, (one_sub_mul_comm hAP).eq, Matrix.mul_assoc, killMinus hA₂, mul_zero]
  rintro ⟨i, b⟩
  fin_cases i <;> fin_cases b
  · change (1 - A) * ((1 / 6 : ℝ) • ((1 + P) * (1 + A))) = 0
    rw [mul_smul_comm, haMinus, smul_zero]
  · change (1 + A) * ((1 / 6 : ℝ) • ((1 + P) * (1 - A))) = 0
    rw [mul_smul_comm, haPlus, smul_zero]
  · change (1 - B) * ((1 / 6 : ℝ) • (1 + B)) = 0
    rw [mul_smul_comm, killMinus hB₂, smul_zero]
  · change (1 + B) * ((1 / 6 : ℝ) • (1 - B)) = 0
    rw [mul_smul_comm, killPlus hB₂, smul_zero]
  · change (1 - C) * ((1 / 6 : ℝ) • (1 - P + C)) = 0
    rw [mul_smul_comm, hcMinus, smul_zero]
  · change (1 + C) * ((1 / 6 : ℝ) • (1 - P - C)) = 0
    rw [mul_smul_comm, hcPlus, smul_zero]

end ManuscriptProofs.Quantum
