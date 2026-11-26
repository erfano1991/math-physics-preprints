import ManuscriptProofs.GraphCollector
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators
open Set Filter

namespace ManuscriptProofs.GraphCollector

/-- The mass of a Poisson count at an integer. The series definition is also
defined for real arguments, so the tails can be differentiated directly. -/
noncomputable def poissonMass (x : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-x) * x ^ k / (k.factorial : ℝ)

noncomputable def poissonTail (x : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, poissonMass x (k + j)

noncomputable def poissonRatio (x : ℝ) (k : ℕ) : ℝ :=
  poissonTail x (k - 1) / poissonTail x k

private theorem mass_hasSum (x : ℝ) : HasSum (poissonMass x) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp x).mul_left (Real.exp (-x))
  have hx : Real.exp (-x) * NormedSpace.exp x = 1 := by
    rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hx] at h
  rw [show poissonMass x = (fun i : ℕ => Real.exp (-x) * (x ^ i / (i.factorial : ℝ))) from
    funext fun i => mul_div_assoc _ _ _]
  exact h

private theorem mass_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < poissonMass x k :=
  div_pos (mul_pos (Real.exp_pos _) (pow_pos hx _)) (by exact_mod_cast k.factorial_pos)

private theorem summable_tail (x : ℝ) (k : ℕ) : Summable (fun j => poissonMass x (k + j)) := by
  simpa [Nat.add_comm] using (summable_nat_add_iff k).2 (mass_hasSum x).summable

theorem poisson_tail_zero (x : ℝ) : poissonTail x 0 = 1 := by
  simpa [poissonTail] using (mass_hasSum x).tsum_eq

theorem poisson_tail_succ (x : ℝ) (k : ℕ) :
    poissonTail x k = poissonMass x k + poissonTail x (k + 1) := by
  have hindex (j : ℕ) : k + (j + 1) = k + 1 + j := by omega
  have hs : Summable (fun j : ℕ => poissonMass x (k + (j + 1))) :=
    (summable_tail x (k + 1)).congr fun j => congrArg (poissonMass x) (hindex j).symm
  calc
    poissonTail x k =
        poissonMass x (k + 0) + ∑' j : ℕ, poissonMass x (k + (j + 1)) :=
      tsum_eq_zero_add' hs
    _ = _ := by
      rw [Nat.add_zero, poissonTail]
      congr 1
      apply tsum_congr
      intro j
      rw [hindex]

theorem poisson_tail_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < poissonTail x k := by
  have h : 0 ≤ poissonTail x (k + 1) := by
    unfold poissonTail
    exact tsum_nonneg (g := fun j : ℕ => poissonMass x (k + 1 + j))
      (fun j => (mass_pos hx (k + 1 + j)).le)
  rw [poisson_tail_succ x k]
  exact add_pos_of_pos_of_nonneg (mass_pos hx k) h

private theorem mass_succ (x : ℝ) (k : ℕ) :
    poissonMass x (k + 1) = x * poissonMass x k / ((k : ℝ) + 1) := by
  simp only [poissonMass, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp [hk]

theorem hasDerivAt_poisson_tail_succ (x : ℝ) :
    ∀ k : ℕ, HasDerivAt (fun t => poissonTail t (k + 1)) (poissonMass x k) x := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa only [mul_neg, mul_one] using (hasDerivAt_neg x).exp
  have hm₀ : HasDerivAt (fun t => poissonMass t 0) (-poissonMass x 0) x := by
    simpa [poissonMass] using he
  have hm (k : ℕ) :
      HasDerivAt (fun t => poissonMass t (k + 1))
        (poissonMass x k - poissonMass x (k + 1)) x := by
    have h := he.mul (((hasDerivAt_id x).pow (k + 1)).div_const ((k + 1).factorial : ℝ))
    simp only [id_eq, Pi.pow_apply, mul_one, Nat.add_one_sub_one] at h
    change HasDerivAt (fun t : ℝ => Real.exp (-t) * (t ^ (k + 1) / ((k + 1).factorial : ℝ)))
      ((-Real.exp (-x)) * (x ^ (k + 1) / ((k + 1).factorial : ℝ)) +
        Real.exp (-x) * ((((k + 1 : ℕ) : ℝ) * x ^ k) / ((k + 1).factorial : ℝ))) x at h
    have hval :
        (-Real.exp (-x)) * (x ^ (k + 1) / ((k + 1).factorial : ℝ)) +
          Real.exp (-x) * ((((k + 1 : ℕ) : ℝ) * x ^ k) / ((k + 1).factorial : ℝ)) =
        poissonMass x k - poissonMass x (k + 1) := by
      have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      simp only [poissonMass, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
      field_simp [hk]
      ring
    rw [hval] at h
    rw [show (fun t => poissonMass t (k + 1)) =
      (fun t : ℝ => Real.exp (-t) * (t ^ (k + 1) / ((k + 1).factorial : ℝ))) from
      funext fun t => mul_div_assoc _ _ _]
    exact h
  intro k
  induction k with
  | zero =>
      rw [show (fun t => poissonTail t (0 + 1)) = fun t => 1 - poissonMass t 0 from by
        funext t
        have ht := poisson_tail_succ t 0
        rw [poisson_tail_zero] at ht
        linarith]
      have h := (hasDerivAt_const x (1 : ℝ)).sub hm₀
      change HasDerivAt (fun t => 1 - poissonMass t 0) (0 - -poissonMass x 0) x at h
      simpa only [zero_sub, neg_neg] using h
  | succ k ih =>
      rw [show (fun t => poissonTail t (k + 1 + 1)) =
          (fun t => poissonTail t (k + 1) - poissonMass t (k + 1)) from by
        funext t
        linarith [poisson_tail_succ t (k + 1)]]
      convert ih.sub (hm k) using 1 <;> first | rfl | ring

theorem poisson_ratio_pos {x : ℝ} (hx : 0 < x) (k : ℕ) :
    0 < poissonRatio x k :=
  div_pos (poisson_tail_pos hx _) (poisson_tail_pos hx _)

private theorem ratio_succ_formula (x : ℝ) (hx : 0 < x) (k : ℕ) :
    poissonRatio x (k + 1) = 1 + (poissonTail x (k + 1) / poissonMass x k)⁻¹ := by
  simp only [poissonRatio, Nat.add_sub_cancel]
  rw [poisson_tail_succ x k, add_div, div_self (poisson_tail_pos hx _).ne',
    inv_div, add_comm]

private theorem strict_tail_mass_ratio {x : ℝ} (hx : 0 < x) (k : ℕ) :
    poissonTail x (k + 1 + 1) / poissonMass x (k + 1) <
      poissonTail x (k + 1) / poissonMass x k := by
  let f (n j : ℕ) := poissonMass x (n + 1 + j) / poissonMass x n
  have hs (n : ℕ) : Summable (f n) := (summable_tail x (n + 1)).div_const _
  have ht (n : ℕ) :
      (∑' j, f n j) = poissonTail x (n + 1) / poissonMass x n := by
    simp [f, poissonTail, tsum_div_const]
  have hf (j : ℕ) : f (k + 1) j < f k j := by
    have hterm :
        f (k + 1) j = f k j * (((k : ℝ) + 1) / ((k : ℝ) + 2 + j)) := by
      unfold f
      rw [show k + 1 + 1 + j = (k + 1 + j) + 1 by omega,
        mass_succ x (k + 1 + j), mass_succ x k]
      push_cast
      field_simp [(mass_pos hx k).ne', hx.ne']; ring
    rw [hterm]
    have hpos : 0 < f k j := div_pos (mass_pos hx _) (mass_pos hx _)
    have hratio : ((k : ℝ) + 1) / ((k : ℝ) + 2 + j) < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < (k : ℝ) + 2 + j)).2
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    simpa using mul_lt_mul_of_pos_left hratio hpos
  rw [← ht (k + 1), ← ht k]
  exact Summable.tsum_lt_tsum (fun j => (hf j).le) (hf 0) (hs _) (hs _)

/-- The first Poisson ratio used by the graph comparison is strictly increasing. -/
theorem poisson_ratio_strictMonoOn {x : ℝ} (hx : 0 < x) :
    StrictMonoOn (poissonRatio x) (Ioi 0) := by
  have hstep (k : ℕ) : poissonRatio x (k + 1) < poissonRatio x (k + 1 + 1) := by
    rw [ratio_succ_formula x hx, ratio_succ_formula x hx]
    exact add_lt_add_right
      ((inv_lt_inv₀ (div_pos (poisson_tail_pos hx _) (mass_pos hx _))
        (div_pos (poisson_tail_pos hx _) (mass_pos hx _))).2 (strict_tail_mass_ratio hx k)) _
  have h := strictMono_nat_of_lt_succ (f := fun k => poissonRatio x (k + 1)) hstep
  intro a ha b hb hab
  cases a with
  | zero => simp at ha
  | succ a =>
      cases b with
      | zero => simp at hb
      | succ b => exact h (Nat.lt_of_succ_lt_succ hab)

private noncomputable def scaledTerm (x : ℝ) (k j : ℕ) : ℝ :=
  (k.factorial : ℝ) * poissonMass x (k + j)

private noncomputable def scaledTail (x : ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * poissonTail x k

private theorem sum_scaledTerm (x : ℝ) (k : ℕ) : HasSum (scaledTerm x k) (scaledTail x k) :=
  (summable_tail x k).hasSum.mul_left _

private theorem scaled_pos {x : ℝ} (hx : 0 < x) (k : ℕ) : 0 < scaledTail x k :=
  mul_pos (by exact_mod_cast k.factorial_pos) (poisson_tail_pos hx k)

private theorem scaledTerm_pos {x : ℝ} (hx : 0 < x) (k j : ℕ) :
    0 < scaledTerm x k j :=
  mul_pos (by exact_mod_cast k.factorial_pos) (mass_pos hx _)

private theorem scaledTerm_step (x : ℝ) (k j : ℕ) :
    scaledTerm x (k + 1) j =
      scaledTerm x k j * (x * ((k : ℝ) + 1) / ((k : ℝ) + j + 1)) := by
  unfold scaledTerm
  rw [show k + 1 + j = (k + j) + 1 by omega, mass_succ, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

private theorem term_logConvex {x : ℝ} (hx : 0 < x) (k j : ℕ) :
    scaledTerm x (k + 1) j ^ 2 ≤ scaledTerm x k j * scaledTerm x (k + 2) j := by
  have hcompare :
      x * ((k : ℝ) + 1) / ((k : ℝ) + j + 1) ≤
        x * ((k : ℝ) + 2) / ((k : ℝ) + j + 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < (k : ℝ) + j + 1)
      (by positivity : 0 < (k : ℝ) + j + 2)).2
    nlinarith [mul_nonneg hx.le (Nat.cast_nonneg (α := ℝ) j)]
  calc
    _ = (scaledTerm x k j * scaledTerm x (k + 1) j) *
        (x * ((k : ℝ) + 1) / ((k : ℝ) + j + 1)) := by
      nth_rw 1 [pow_two, scaledTerm_step x k j]
      ring
    _ ≤ (scaledTerm x k j * scaledTerm x (k + 1) j) *
        (x * ((k : ℝ) + 2) / ((k : ℝ) + j + 2)) :=
      mul_le_mul_of_nonneg_left hcompare (mul_nonneg (scaledTerm_pos hx _ _).le (scaledTerm_pos hx _ _).le)
    _ = _ := by
      rw [show k + 2 = (k + 1) + 1 by omega, scaledTerm_step x (k + 1) j]
      push_cast
      ring

private theorem scaled_tail_logConvex {x : ℝ} (hx : 0 < x) (k : ℕ) :
    scaledTail x (k + 1) ^ 2 ≤ scaledTail x k * scaledTail x (k + 2) := by
  apply le_of_tendsto_of_tendsto ((sum_scaledTerm x (k + 1)).tendsto_sum_nat.pow 2)
    ((sum_scaledTerm x k).tendsto_sum_nat.mul (sum_scaledTerm x (k + 2)).tendsto_sum_nat)
  exact Filter.Eventually.of_forall fun n =>
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range n)
      (fun j _ => (scaledTerm_pos hx k j).le) (fun j _ => (scaledTerm_pos hx (k + 2) j).le)
      (fun j _ => term_logConvex hx k j)

private theorem ratio_div_eq_scaled (x : ℝ) (k : ℕ) :
    poissonRatio x (k + 1) / ((k + 1 : ℕ) : ℝ) =
      scaledTail x k / scaledTail x (k + 1) := by
  simp only [poissonRatio, Nat.add_sub_cancel, scaledTail, Nat.factorial_succ, Nat.cast_mul]
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  by_cases h : poissonTail x (k + 1) = 0
  · simp [h]
  field_simp [hk, h]

/-- The second Poisson ratio used by the graph comparison is antitone after
division by its integer index. The proof uses log-convexity of the scaled
Poisson tail, proved from its series by finite Cauchy–Schwarz and a limit. -/
theorem poisson_ratio_div_antitoneOn {x : ℝ} (hx : 0 < x) :
    AntitoneOn (fun k : ℕ => poissonRatio x k / (k : ℝ)) (Ioi 0) := by
  have hstep (k : ℕ) : scaledTail x (k + 1) / scaledTail x (k + 2) ≤
      scaledTail x k / scaledTail x (k + 1) := by
    apply (div_le_div_iff₀ (scaled_pos hx _) (scaled_pos hx _)).2
    simpa only [pow_two] using scaled_tail_logConvex hx k
  have hmono := antitone_nat_of_succ_le (f := fun k => scaledTail x k / scaledTail x (k + 1)) hstep
  intro a ha b hb hab
  cases a with
  | zero => simp at ha
  | succ a =>
      cases b with
      | zero => simp at hb
      | succ b =>
          simp only [ratio_div_eq_scaled]
          exact hmono (Nat.le_of_succ_le_succ hab)

open scoped BigOperators in
/-- The generator comparison specialized to the actual Poisson series. -/
theorem poisson_ratio_generator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (hd : 0 < d)
    (hreg : ∀ v, G.degree v = d) (U : Finset V) {x : ℝ} (hx : 0 < x) :
    (∑ v, if 0 < uncoveredNeighbors G U v then poissonRatio x (uncoveredNeighbors G U v) - 1 else 0) ≤
      ∑ u ∈ U, (∑ v ∈ G.neighborFinset u, 1 / (uncoveredNeighbors G U v : ℝ)) *
        ((∏ v ∈ G.neighborFinset u, poissonRatio x (uncoveredNeighbors G U v) ^ (d : ℝ)⁻¹) - 1) :=
  ratio_generator G d hd hreg U (poissonRatio x) (fun k _ => poisson_ratio_pos hx k)
    (poisson_ratio_strictMonoOn hx) (poisson_ratio_div_antitoneOn hx)

end ManuscriptProofs.GraphCollector
