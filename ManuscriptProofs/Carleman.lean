import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ManuscriptProofs.Carleman

/-- Each internal vertex can carry a mark. The two children are ordered. -/
inductive Tree where
  | leaf
  | fork (marked : Bool) (left right : Tree)

def Tree.leaves : Tree → ℕ
  | .leaf => 1
  | .fork _ l r => l.leaves + r.leaves

def Tree.marks : Tree → ℕ
  | .leaf => 0
  | .fork b l r => l.marks + r.marks + if b then 1 else 0

/-- The number of marked vertices with no marked strict ancestor. -/
def Tree.outerMarks : Tree → ℕ
  | .leaf => 0
  | .fork true _ _ => 1
  | .fork false l r => l.outerMarks + r.outerMarks

/-- Leaves lying below one of the outermost marks. -/
def Tree.covered : Tree → ℕ
  | .leaf => 0
  | .fork true l r => l.leaves + r.leaves
  | .fork false l r => l.covered + r.covered

/-- Local conditions implied by small-divisor separation on an ancestor chain.
For a marked vertex with just one outermost marked descendant, the second
condition measures the leaves outside that descendant's subtree. -/
def Tree.Separated (b : ℕ) : Tree → Prop
  | .leaf => True
  | .fork false l r => l.Separated b ∧ r.Separated b
  | .fork true l r =>
      l.Separated b ∧ r.Separated b ∧
      b + 1 ≤ l.leaves + r.leaves ∧
      (l.outerMarks + r.outerMarks = 1 →
        b + 1 + l.covered + r.covered ≤ l.leaves + r.leaves)

theorem Tree.leaves_pos (t : Tree) : 0 < t.leaves := by
  induction t with
  | leaf => decide
  | fork flag l r hl hr => simp only [Tree.leaves]; omega

/-- The marks are bounded by the number of internal vertices, including at
the coarsest dyadic level. -/
theorem Tree.marks_le_internal_vertices (t : Tree) : t.marks ≤ t.leaves - 1 := by
  induction t with
  | leaf => exact Nat.zero_le _
  | fork flag l r hl hr =>
      have hlp := l.leaves_pos
      have hrp := r.leaves_pos
      cases flag <;> simp only [Tree.leaves, Tree.marks, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem Tree.covered_le_leaves (t : Tree) : t.covered ≤ t.leaves := by
  induction t with
  | leaf => decide
  | fork flag l r hl hr =>
      cases flag <;> simp only [Tree.covered, Tree.leaves] <;> omega

theorem Tree.outerMarks_eq_zero (t : Tree) (h : t.outerMarks = 0) :
    t.marks = 0 ∧ t.covered = 0 := by
  induction t with
  | leaf => exact ⟨rfl, rfl⟩
  | fork flag l r hl hr =>
      cases flag with
      | false =>
          simp only [Tree.outerMarks] at h
          obtain ⟨hl₁, hl₂⟩ := hl (by omega)
          obtain ⟨hr₁, hr₂⟩ := hr (by omega)
          simp [Tree.marks, Tree.covered, hl₁, hl₂, hr₁, hr₂]
      | true => simp [Tree.outerMarks] at h

theorem Tree.mark_budget {b : ℕ} {t : Tree} (ht : t.Separated b) :
    (t.marks + t.outerMarks) * (b + 1) ≤ 2 * t.covered := by
  induction t with
  | leaf => simp [Tree.marks, Tree.outerMarks, Tree.covered]
  | fork flag l r hl hr =>
      cases flag with
      | false =>
          have h₁ := hl ht.1
          have h₂ := hr ht.2
          simp only [Tree.marks, Tree.outerMarks, Tree.covered, Bool.false_eq_true,
            ite_false, add_zero, Nat.add_mul] at *
          omega
      | true =>
          obtain ⟨h₁, h₂, hsize, hsingle⟩ := ht
          have h₃ := hl h₁
          have h₄ := hr h₂
          have hlc := l.covered_le_leaves
          have hrc := r.covered_le_leaves
          by_cases h0 : l.outerMarks + r.outerMarks = 0
          · obtain ⟨hlm, _⟩ := l.outerMarks_eq_zero (by omega)
            obtain ⟨hrm, _⟩ := r.outerMarks_eq_zero (by omega)
            simp only [Tree.marks, Tree.outerMarks, Tree.covered, ite_true, hlm, hrm,
              zero_add, Nat.add_mul]
            omega
          · by_cases h1 : l.outerMarks + r.outerMarks = 1
            · have hs := hsingle h1
              have ht₁ :
                  (l.marks + r.marks + 1) * (b + 1) ≤
                    2 * (l.covered + r.covered) := by
                calc
                  _ = ((l.marks + l.outerMarks) + (r.marks + r.outerMarks)) * (b + 1) :=
                    congrArg (fun x : ℕ => x * (b + 1)) (by omega)
                  _ ≤ _ := by rw [Nat.add_mul]; omega
              simp only [Tree.marks, Tree.outerMarks, Tree.covered, ite_true,
                Nat.add_mul] at *
              omega
            · have hsum :
                  (l.marks + r.marks + 1 + 1) * (b + 1) ≤
                    ((l.marks + l.outerMarks) + (r.marks + r.outerMarks)) * (b + 1) :=
                  Nat.mul_le_mul_right _ (by omega)
              simp only [Tree.marks, Tree.outerMarks, Tree.covered, ite_true,
                Nat.add_mul] at *
              omega

/-- Twice the number of leaves beyond the first pays for all marked vertices
at scale `b`. This is the counting estimate in the dyadic divisor argument. -/
theorem Tree.dyadic_mark_bound {b : ℕ} {t : Tree} (hb : 0 < b)
    (ht : t.Separated b) : b * t.marks ≤ 2 * (t.leaves - 1) := by
  have hbudget := Tree.mark_budget ht
  have hle := t.covered_le_leaves
  by_cases h : t.outerMarks = 0
  · simp [(t.outerMarks_eq_zero h).1]
  · have hle' := Nat.mul_le_mul_right (b + 1)
        (show t.marks + 1 ≤ t.marks + t.outerMarks by omega)
    have hl := t.leaves_pos
    have hpay : t.marks * b + 2 ≤ (t.marks + 1) * (b + 1) := by
      rw [Nat.add_mul, Nat.mul_add, one_mul, mul_one]
      omega
    rw [Nat.mul_comm b t.marks]
    omega

/-- The exact geometric-series first-coordinate error in the manuscript's example.
Here `z` is the ratio of the truncated series, equal to `2 * I` at time π. -/
theorem geometric_truncation_error (z : ℂ) (hz : z ≠ 1) (k : ℕ) :
    ‖-(∑ j ∈ Finset.range k, z ^ j) - (-(1 - z)⁻¹)‖ =
      ‖z‖ ^ k / ‖1 - z‖ := by
  have hz' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have heq : -(∑ j ∈ Finset.range k, z ^ j) - (-(1 - z)⁻¹) =
      z ^ k / (1 - z) := by
    apply (eq_div_iff hz').2
    calc
      _ = -(∑ j ∈ Finset.range k, z ^ j) * (1 - z) + 1 := by
        rw [sub_neg_eq_add, add_mul, inv_mul_cancel₀ hz']
      _ = _ := by rw [neg_mul, geom_sum_mul_neg]; ring
  rw [heq, norm_div, norm_pow]


section Divisors

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The divisor used by the homological equation at a labelled vertex. -/
def divisor (spectrum : d → ℂ) (α : d → ℕ) (i : d) : ℂ :=
  (∑ j, (α j : ℂ) * spectrum j) - spectrum i

/-- Subtracting an ancestor and descendant divisor gives another divisor,
with the descendant output relabeling its removed leaves. -/
theorem divisor_sub_eq (spectrum : d → ℂ) (α β : d → ℕ) (i j : d)
    (hβα : ∀ k, β k ≤ α k) :
    divisor spectrum α i - divisor spectrum β j =
      divisor spectrum (fun k => α k - β k + if k = j then 1 else 0) i := by
  classical
  have hc (k : d) :
      ((α k - β k + if k = j then 1 else 0 : ℕ) : ℂ) =
        (α k : ℂ) - (β k : ℂ) + if k = j then 1 else 0 := by
    rw [Nat.cast_add, Nat.cast_sub (hβα k)]
    split <;> simp_all
  unfold divisor
  simp_rw [hc, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp
  ring

/-- The gap for two marked vertices follows by applying the Diophantine
condition to their difference, rather than to either divisor alone. -/
theorem marked_ancestor_gap (spectrum : d → ℂ) (Δ ν : ℝ) (hΔ : 0 < Δ) (hν : 0 ≤ ν)
    (hdio : ∀ (α : d → ℕ) (i : d), 2 ≤ ∑ k, α k →
      Δ / (((∑ k, α k : ℕ) : ℝ) - 1) ^ ν ≤ ‖divisor spectrum α i‖)
    (α β : d → ℕ) (i j : d) (hβα : ∀ k, β k ≤ α k)
    (hsize : (∑ k, β k) < ∑ k, α k) (b : ℕ) (_hb : 0 < b)
    (ha : ‖divisor spectrum α i‖ < Δ / (2 * (b : ℝ) ^ ν))
    (hc : ‖divisor spectrum β j‖ < Δ / (2 * (b : ℝ) ^ ν)) :
    b < (∑ k, α k) - ∑ k, β k := by
  classical
  let γ : d → ℕ := fun k => α k - β k + if k = j then 1 else 0
  let gap := (∑ k, α k) - ∑ k, β k
  have hpos : 0 < gap := Nat.sub_pos_of_lt hsize
  have hsum : (∑ k, γ k) = gap + 1 := by
    simp only [γ, gap, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [Finset.sum_tsub_distrib Finset.univ (fun k _ => hβα k)]
  have hγ : 2 ≤ ∑ k, γ k := by rw [hsum]; omega
  have hgap := hdio γ i hγ
  rw [hsum, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    ← divisor_sub_eq spectrum α β i j hβα] at hgap
  by_contra! hn
  have hbase : (gap : ℝ) ≤ b := by exact_mod_cast hn
  have hrpow : (gap : ℝ) ^ ν ≤ (b : ℝ) ^ ν := Real.rpow_le_rpow (by positivity) hbase hν
  have hlow := div_le_div_of_nonneg_left hΔ.le
    (Real.rpow_pos_of_pos (by exact_mod_cast hpos) ν) hrpow
  have hhi : ‖divisor spectrum α i - divisor spectrum β j‖ < Δ / (b : ℝ) ^ ν := by
    apply (norm_sub_le _ _).trans_lt
    have hm := add_lt_add ha hc
    linarith [show Δ / (2 * (b : ℝ) ^ ν) + Δ / (2 * (b : ℝ) ^ ν) =
      Δ / (b : ℝ) ^ ν by rw [div_mul_eq_div_div]; ring]
  exact (not_lt_of_ge (hlow.trans hgap)) hhi

end Divisors

private theorem norm_one_sub_two_i : ‖(1 : ℂ) - 2 * Complex.I‖ = Real.sqrt 5 := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num

/-- Exact error of the first Carleman coordinate at \(t=\pi\) in the
triangular Riccati example. -/
theorem riccati_error_at_pi (k : ℕ) :
    ‖-(∑ j ∈ Finset.range k, (2 * Complex.I) ^ j) - (-(1 - 2 * Complex.I)⁻¹)‖ =
      (2 : ℝ) ^ k / Real.sqrt 5 := by
  have hne : (2 : ℂ) * Complex.I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  rw [geometric_truncation_error _ hne, norm_one_sub_two_i, norm_mul, Complex.norm_I, mul_one]
  norm_num

/-- The exact denominator stays away from zero when \(z=\exp(it)\). -/
theorem riccati_denominator_lower (z : ℂ) (hz : ‖z‖ = 1) :
    Real.sqrt 2 - 1 ≤ ‖1 - (z - 1) / Complex.I‖ := by
  have hi : (Complex.I)⁻¹ = -Complex.I := Complex.inv_I
  have he : (1 : ℂ) - (z - 1) / Complex.I = (1 - Complex.I) + Complex.I * z := by
    rw [div_eq_mul_inv, hi]
    ring
  have hn : ‖(1 : ℂ) - Complex.I‖ = Real.sqrt 2 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    norm_num
  have htri := norm_sub_le ((1 : ℂ) - Complex.I + Complex.I * z) (Complex.I * z)
  rw [add_sub_cancel_right, hn, norm_mul, Complex.norm_I, hz, one_mul] at htri
  rw [he]
  linarith

end ManuscriptProofs.Carleman
