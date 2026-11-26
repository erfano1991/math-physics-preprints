import ManuscriptProofs.Quantum.POVM
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

open scoped BigOperators MatrixOrder ComplexOrder ComplexConjugate
open ManuscriptProofs.Quantum

namespace ManuscriptProofs.Optical

noncomputable def coherentOverlap (u v : ℂ) : ℂ :=
  Complex.exp (conj u*v - ((Complex.normSq u + Complex.normSq v : ℝ) : ℂ)/2)

/-- After cancellation of the environment overlap of the loss isometry,
the remaining three coherent overlaps give the cross ratio exactly. -/
theorem coherent_cross_ratio (a b c : ℂ) :
    coherentOverlap a c * coherentOverlap c b / coherentOverlap a b =
      Complex.exp (-(conj a-conj c)*(b-c)) := by
  unfold coherentOverlap
  rw [← Complex.exp_add, ← Complex.exp_sub]
  congr 1
  push_cast
  rw [Complex.normSq_eq_conj_mul_self (z := c)]
  ring

variable {d k : Type*} [Fintype d] [DecidableEq d] [Fintype k]

private noncomputable def arm (w : ℝ) (Q : Operator d) (b : Bool) : Operator d :=
  (w/2) • (if b then 1+Q else 1-Q)

/-- Normalize the signed directions and randomize over their binary parents. -/
noncomputable def cutoffParent (w : k → ℝ) (Q : k → Operator d)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hp : ∀ i, 0 ≤ (1 : Operator d) + Q i) (hm : ∀ i, 0 ≤ (1 : Operator d) - Q i) :
    POVM d (k × Bool) where
  effect o := arm (w o.1) (Q o.1) o.2
  pos o := by
    obtain ⟨i,b⟩ := o
    cases b
    · exact (Matrix.nonneg_iff_posSemidef.mp (hm i)).smul (div_nonneg (hw i) (by norm_num : (0:ℝ) ≤ 2))
    · exact (Matrix.nonneg_iff_posSemidef.mp (hp i)).smul (div_nonneg (hw i) (by norm_num : (0:ℝ) ≤ 2))
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [arm, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    calc
      _ = ∑ i, w i • (1 : Operator d) := by apply Finset.sum_congr rfl; intro i _; module
      _ = _ := by rw [← Finset.sum_smul, hs, one_smul]

/-- The classical response is stochastic and gives exactly the cosine/sine
family in the cutoff proof. The effects do not depend on the choice of t. -/
theorem cutoff_response (w : k → ℝ) (Q : k → Operator d)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (hp : ∀ i, 0 ≤ (1 : Operator d) + Q i) (hm : ∀ i, 0 ≤ (1 : Operator d) - Q i)
    (p S : ℝ) (hS : 0 ≤ S) (hl : S ≤ p) (hu : S ≤ 1-p)
    (t : k → ℝ) (ht : ∀ i, |t i| ≤ 1) :
    let M := cutoffParent w Q hw hs hp hm
    let prob := fun o : k × Bool => if o.2 then p+S*t o.1 else p-S*t o.1
    (∀ o, 0 ≤ prob o ∧ prob o ≤ 1) ∧
    (∑ o, prob o • M.effect o) =
      p • (1 : Operator d) + S • ∑ i, (w i*t i) • Q i := by
  constructor
  · rintro ⟨i,b⟩
    obtain ⟨lo,hi⟩ := abs_le.mp (ht i)
    have A := mul_le_mul_of_nonneg_left lo hS
    have B := mul_le_mul_of_nonneg_left hi hS
    cases b <;> simp <;> constructor <;> linarith
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, cutoffParent, arm,
      Bool.false_eq_true, ite_false, ite_true]
    calc
      _ = ∑ i, ((p*w i) • (1 : Operator d) + S • ((w i*t i) • Q i)) := by
        apply Finset.sum_congr rfl
        intro i _
        module
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul,
                      ← Finset.mul_sum, hs, mul_one]

/-- The numerical constant 36 in the necessary photon cutoff, including
y=0 and the full interval of radii up to 1. -/
theorem cutoff_radius_bound {r y : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hy : 0 ≤ y) (hy' : y ≤ r^2/36) :
    y + 2*(Real.exp (2*r*Real.sqrt y)-1) ≤ min 1 (Real.exp (r^2)-1) := by
  have hs : Real.sqrt y ≤ r/6 := (Real.sqrt_le_iff).2 ⟨by positivity, by nlinarith⟩
  have harg : 2*r*Real.sqrt y ≤ r^2/3 := by nlinarith [mul_le_mul_of_nonneg_left hs hr]
  have hr2 : r^2 ≤ 1 := by nlinarith [mul_nonneg hr (sub_nonneg.mpr hr1)]
  have hcube : (Real.exp (1/3))^3 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp (1/3) ≤ 13/9 := by
    by_contra! hh
    have hx := pow_lt_pow_left₀ hh (by norm_num : (0:ℝ) ≤ 13/9) (by decide : 3 ≠ 0)
    nlinarith [Real.exp_one_lt_three, hcube]
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1/3:ℝ))
    (sub_nonneg.mpr hr2) (sq_nonneg r) (by ring : 1-r^2+r^2=1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hconv
  have hb : Real.exp (r^2/3) ≤ 1-r^2+r^2*(13/9) := by
    calc
      _ ≤ 1-r^2+r^2*Real.exp (1/3) := by simpa only [div_eq_mul_inv, one_mul] using hconv
      _ ≤ _ := by gcongr
  have hfinal : y + 2*(Real.exp (2*r*Real.sqrt y)-1) ≤ r^2 := by
    linarith [Real.exp_le_exp.mpr harg, sq_nonneg r]
  exact le_min (hfinal.trans hr2) (hfinal.trans (by linarith [Real.add_one_le_exp (r^2)]))

end ManuscriptProofs.Optical
