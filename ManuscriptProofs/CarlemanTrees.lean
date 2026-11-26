import ManuscriptProofs.CarlemanProduct

open scoped BigOperators

namespace ManuscriptProofs.Carleman

/-- An ordered binary tree with a spectral label at every vertex. -/
inductive LabelledTree (d : Type*) where
  | leaf (i : d)
  | fork (i : d) (left right : LabelledTree d)

namespace LabelledTree

variable {d : Type*}

def rootLabel : LabelledTree d → d
  | .leaf i => i
  | .fork i _ _ => i

def leaves : LabelledTree d → ℕ
  | .leaf _ => 1
  | .fork _ l r => l.leaves + r.leaves

def leafCounts [DecidableEq d] : LabelledTree d → d → ℕ
  | .leaf i, j => if j = i then 1 else 0
  | .fork _ l r, j => l.leafCounts j + r.leafCounts j

/-- All internal vertices with multiplicity, represented by their subtrees. -/
def branches : LabelledTree d → List (LabelledTree d)
  | .leaf _ => []
  | .fork i l r => .fork i l r :: (l.branches ++ r.branches)

def marked (p : LabelledTree d → Bool) : LabelledTree d → Tree
  | .leaf _ => .leaf
  | .fork i l r => .fork (p (.fork i l r)) (l.marked p) (r.marked p)

theorem leaves_pos (t : LabelledTree d) : 0 < t.leaves := by
  induction t with
  | leaf => simp [leaves]
  | fork i l r hl hr => simp only [leaves]; omega

theorem branches_length (t : LabelledTree d) : t.branches.length = t.leaves - 1 := by
  induction t with
  | leaf => rfl
  | fork i l r hl hr =>
      simp only [branches, leaves, List.length_cons, List.length_append, hl, hr]
      have hp := l.leaves_pos
      have hq := r.leaves_pos
      omega

theorem sum_leafCounts [Fintype d] [DecidableEq d] (t : LabelledTree d) :
    (∑ i, t.leafCounts i) = t.leaves := by
  induction t with
  | leaf i => simp [leafCounts, leaves, Finset.sum_ite_eq']
  | fork i l r hl hr => simp [leafCounts, leaves, Finset.sum_add_distrib, hl, hr]

private theorem branch_leaves_bounds {t u : LabelledTree d} (hu : u ∈ t.branches) :
    2 ≤ u.leaves ∧ u.leaves ≤ t.leaves := by
  induction t with
  | leaf i => simp [branches] at hu
  | fork i l r hl hr =>
      simp only [branches, List.mem_cons, List.mem_append] at hu
      rcases hu with rfl | hu | hu
      · have h₁ := l.leaves_pos
        have h₂ := r.leaves_pos
        simp only [leaves]
        omega
      · have hp := hl hu
        simp only [leaves]
        omega
      · have hp := hr hu
        simp only [leaves]
        omega

private theorem branch_counts_le [DecidableEq d] {t u : LabelledTree d}
    (hu : u ∈ t.branches) (i : d) : u.leafCounts i ≤ t.leafCounts i := by
  induction t with
  | leaf => simp [branches] at hu
  | fork j l r hl hr =>
      simp only [branches, List.mem_cons, List.mem_append] at hu
      rcases hu with rfl | hu | hu
      · exact le_rfl
      · have h := hl hu
        simp only [leafCounts]
        omega
      · have h := hr hu
        simp only [leafCounts]
        omega

theorem marked_leaves (t : LabelledTree d) (p : LabelledTree d → Bool) :
    (t.marked p).leaves = t.leaves := by
  induction t with
  | leaf => rfl
  | fork i l r hl hr => simp [marked, Tree.leaves, leaves, hl, hr]

theorem count_marked (t : LabelledTree d) (p : LabelledTree d → Bool) :
    (t.marked p).marks = t.branches.countP p := by
  induction t with
  | leaf => rfl
  | fork i l r hl hr =>
      simp only [marked, Tree.marks, branches, List.countP_cons, List.countP_append, hl, hr]

private theorem unique_outer_branch (t : LabelledTree d) (p : LabelledTree d → Bool)
    (ht : (t.marked p).outerMarks = 1) :
    ∃ u ∈ t.branches, p u = true ∧ u.leaves = (t.marked p).covered := by
  induction t with
  | leaf => simp [marked, Tree.outerMarks] at ht
  | fork i l r hl hr =>
      cases hp : p (.fork i l r)
      case true =>
        refine ⟨.fork i l r, by simp [branches], hp, ?_⟩
        simp [marked, hp, Tree.covered, leaves, marked_leaves]
      case false =>
        simp only [marked, hp, Tree.outerMarks] at ht
        by_cases h0 : (r.marked p).outerMarks = 0
        · obtain ⟨u, hu, hpu, hul⟩ := hl (by omega)
          refine ⟨u, by simp [branches, hu], hpu, ?_⟩
          simp [marked, hp, Tree.covered, (Tree.outerMarks_eq_zero _ h0).2, hul]
        · have h0' : (l.marked p).outerMarks = 0 := by omega
          obtain ⟨u, hu, hpu, hul⟩ := hr (by omega)
          refine ⟨u, by simp [branches, hu], hpu, ?_⟩
          simp [marked, hp, Tree.covered, (Tree.outerMarks_eq_zero _ h0').2, hul]

/-- Local marking conditions imply exactly the separation predicate used by
the combinatorial count. A marked vertex with one outermost descendant
uses the actual leaf count of that descendant. -/
theorem separated_of_ancestor_marking (t : LabelledTree d) (p : LabelledTree d → Bool) (b : ℕ)
    (hsize : ∀ u : LabelledTree d, 2 ≤ u.leaves → p u = true → b < u.leaves)
    (hgap : ∀ (i : d) (l r u : LabelledTree d),
      u ∈ l.branches ∨ u ∈ r.branches →
      p (.fork i l r) = true → p u = true →
      b < (LabelledTree.fork i l r).leaves - u.leaves) :
    (t.marked p).Separated b := by
  induction t with
  | leaf => trivial
  | fork i l r hl hr =>
      cases hm : p (.fork i l r)
      case false => simpa [marked, hm, Tree.Separated] using And.intro hl hr
      case true =>
        simp only [marked, hm, Tree.Separated, marked_leaves]
        have hbig : 2 ≤ (LabelledTree.fork i l r).leaves := by
          have hleft := l.leaves_pos
          have hright := r.leaves_pos
          simp only [leaves]
          omega
        have hroot := hsize (.fork i l r) hbig hm
        simp only [leaves] at hroot
        refine ⟨hl, hr, by omega, fun hsingle => ?_⟩
        by_cases h0 : (r.marked p).outerMarks = 0
        · obtain ⟨u, hu, hpu, hul⟩ := unique_outer_branch l p (by omega)
          have hsep := hgap i l r u (Or.inl hu) hm hpu
          simp only [leaves] at hsep
          have hright := (Tree.outerMarks_eq_zero _ h0).2
          omega
        · have hzero : (l.marked p).outerMarks = 0 := by omega
          obtain ⟨u, hu, hpu, hur⟩ := unique_outer_branch r p (by omega)
          have hsep := hgap i l r u (Or.inr hu) hm hpu
          simp only [leaves] at hsep
          have hleft := (Tree.outerMarks_eq_zero _ hzero).2
          omega

section Spectrum

variable [Fintype d] [DecidableEq d]

/-- The norm of the spectral divisor at a subtree's root. -/
noncomputable def divisorNorm (spectrum : d → ℂ) (t : LabelledTree d) : ℝ :=
  ‖divisor spectrum t.leafCounts t.rootLabel‖

/-- The Diophantine condition for every multi-index of degree at least two. -/
def DiophantineGap (spectrum : d → ℂ) (Δ ν : ℝ) : Prop :=
  ∀ (α : d → ℕ) (i : d), 2 ≤ ∑ k, α k →
    Δ / (((∑ k, α k : ℕ) : ℝ) - 1) ^ ν ≤ ‖divisor spectrum α i‖

private theorem reciprocal_bound (spectrum : d → ℂ) (Δ ν : ℝ) (hΔ : 0 < Δ)
    (hD : DiophantineGap spectrum Δ ν) (u : LabelledTree d) (hu : 2 ≤ u.leaves) :
    0 < divisorNorm spectrum u ∧
      Δ / divisorNorm spectrum u ≤ ((u.leaves : ℝ) - 1) ^ ν := by
  have h := hD u.leafCounts u.rootLabel (by simpa [sum_leafCounts] using hu)
  rw [sum_leafCounts] at h
  have hup : (2 : ℝ) ≤ u.leaves := by exact_mod_cast hu
  have hp : 0 < ((u.leaves : ℝ) - 1) ^ ν := Real.rpow_pos_of_pos (by linarith) _
  have hnorm : 0 < divisorNorm spectrum u := (div_pos hΔ hp).trans_le h
  exact ⟨hnorm, (div_le_iff₀ hnorm).mpr (by
    simpa [mul_comm, divisorNorm] using (div_le_iff₀ hp).mp h)⟩

private theorem branch_filter_count {α : Type*} (l : List α) (p : α → Bool) :
    ((Finset.univ : Finset (Fin l.length)).filter (fun i => p (l.get i))).card =
      l.countP p := by
  classical
  rw [Finset.card_filter]
  induction l with
  | nil => simp
  | cons a l ih =>
      change (∑ i : Fin (l.length + 1), if p ((a :: l).get i) then (1 : ℕ) else 0) = _
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.countP_cons]
      change (if p a then 1 else 0) +
        (∑ i : Fin l.length, if p (l.get i) then (1 : ℕ) else 0) = _
      rw [ih, add_comm]

/-- The manuscript's inverse-divisor product bound for every actual
labelled tree. All level counts follow from the specified spectral gap. -/
theorem inverse_divisor_product (spectrum : d → ℂ) (Δ ν : ℝ) (hΔ : 0 < Δ) (hν : 0 ≤ ν)
    (hD : DiophantineGap spectrum Δ ν) (t : LabelledTree d) :
    (∏ i : Fin t.branches.length, Δ / divisorNorm spectrum (t.branches.get i)) ≤
      (2 : ℝ) ^ ((1 + 4 * ν) * ((t.leaves - 1 : ℕ) : ℝ)) := by
  classical
  let J := t.leaves
  let x (i : Fin t.branches.length) := Δ / divisorNorm spectrum (t.branches.get i)
  have hbranch (i : Fin t.branches.length) := branch_leaves_bounds (List.get_mem t.branches i)
  have h0 (i : Fin t.branches.length) : 0 ≤ x i := by
    exact div_nonneg hΔ.le (norm_nonneg _)
  have hcut (i : Fin t.branches.length) : x i ≤ dyadicThreshold ν J := by
    rw [dyadicThreshold_eq]
    have hlt : t.leaves ≤ 2 ^ J := t.leaves.lt_two_pow_self.le
    have hm : (t.branches.get i).leaves ≤ 2 ^ J := (hbranch i).2.trans hlt
    have hm' : ((t.branches.get i).leaves : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by exact_mod_cast hm
    have hf := (reciprocal_bound spectrum Δ ν hΔ hD _ (hbranch i).1).2
    have hpow := Real.rpow_le_rpow (show 0 ≤ ((t.branches.get i).leaves : ℝ) - 1 by
      have h := (hbranch i).1
      have h' : (2 : ℝ) ≤ (t.branches.get i).leaves := by exact_mod_cast h
      linarith) (show ((t.branches.get i).leaves : ℝ) - 1 ≤ ((2 ^ J : ℕ) : ℝ) by linarith) hν
    exact hf.trans (hpow.trans (le_mul_of_one_le_left (by positivity) (by norm_num)))
  have hc (j : ℕ) :
      (((Finset.univ : Finset (Fin t.branches.length)).filter
        (fun i => dyadicThreshold ν j < x i)).card : ℝ) ≤
        (2 * (t.branches.length : ℝ)) * (1 / 2 : ℝ) ^ j := by
    let b : ℕ := 2 ^ j
    have hb : 0 < b := by positivity
    let p : LabelledTree d → Bool := fun u => decide (dyadicThreshold ν j < Δ / divisorNorm spectrum u)
    have hmark (u : LabelledTree d) (hu : 2 ≤ u.leaves) (hpu : p u = true) :
        divisorNorm spectrum u < Δ / (2 * (b : ℝ) ^ ν) := by
      have hp : dyadicThreshold ν j < Δ / divisorNorm spectrum u := of_decide_eq_true hpu
      rw [dyadicThreshold_eq] at hp
      have hp' := (lt_div_iff₀ (reciprocal_bound spectrum Δ ν hΔ hD u hu).1).mp hp
      exact (lt_div_iff₀ (by positivity : 0 < 2 * (b : ℝ)^ν)).mpr (by simpa [b, mul_comm] using hp')
    have hsize (u : LabelledTree d) (hu : 2 ≤ u.leaves) (hpu : p u = true) : b < u.leaves := by
      have hm : dyadicThreshold ν j < Δ / divisorNorm spectrum u := of_decide_eq_true hpu
      rw [dyadicThreshold_eq] at hm
      by_contra! hb'
      have h₁ : (u.leaves : ℝ) ≤ b := by exact_mod_cast hb'
      have h₂ : (2 : ℝ) ≤ u.leaves := by exact_mod_cast hu
      have hp := Real.rpow_le_rpow (show 0 ≤ (u.leaves : ℝ) - 1 by linarith)
        (show (u.leaves : ℝ) - 1 ≤ b by linarith) hν
      have h := (reciprocal_bound spectrum Δ ν hΔ hD u hu).2.trans hp
      have hz : 0 ≤ (b : ℝ) ^ ν := by positivity
      change 2 * (b : ℝ)^ν < _ at hm
      linarith
    have hsep := separated_of_ancestor_marking t p b hsize ?_
    · have hh := Tree.dyadic_mark_bound hb hsep
      rw [marked_leaves, count_marked, ← branch_filter_count t.branches p, ← branches_length] at hh
      have hreal : (b : ℝ) *
          (((Finset.univ : Finset (Fin t.branches.length)).filter
            (fun i => p (t.branches.get i))).card : ℝ) ≤ 2 * (t.branches.length : ℝ) := by
        exact_mod_cast hh
      have hp : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
      have hz : (((Finset.univ : Finset (Fin t.branches.length)).filter
          (fun i => p (t.branches.get i))).card : ℝ) ≤ 2 * (t.branches.length : ℝ) / b :=
        (le_div_iff₀ hp).mpr (by rw [mul_comm]; exact hreal)
      have he : (1 / 2 : ℝ) ^ j = (b : ℝ)⁻¹ := by
        rw [one_div_pow, one_div]
        simp [b]
      rw [he, ← div_eq_mul_inv]
      simpa only [p, decide_eq_true_eq, x] using hz
    · intro k l r u hu hroot hpu
      have hu' : u ∈ (LabelledTree.fork k l r).branches := by simp [branches, hu]
      have hrootSize : 2 ≤ (LabelledTree.fork k l r).leaves := by
        have hl := l.leaves_pos
        have hr := r.leaves_pos
        simp only [leaves]
        omega
      have huSize := (branch_leaves_bounds hu').1
      have hlt : u.leaves < (LabelledTree.fork k l r).leaves := by
        rcases hu with hu | hu
        · have ht := (branch_leaves_bounds hu).2
          have hr := r.leaves_pos
          simp only [leaves]
          omega
        · have ht := (branch_leaves_bounds hu).2
          have hl := l.leaves_pos
          simp only [leaves]
          omega
      have h := marked_ancestor_gap spectrum Δ ν hΔ hν hD
        (LabelledTree.fork k l r).leafCounts u.leafCounts k u.rootLabel
        (branch_counts_le hu') (by simpa [sum_leafCounts] using hlt) b hb
        (hmark _ hrootSize hroot) (hmark _ huSize hpu)
      simpa [sum_leafCounts] using h
  have h := inverse_divisor_product_of_dyadic_counts Finset.univ x
    (fun i _ => h0 i) ν hν J (fun i _ => hcut i) (by simpa using fun j _ => hc j)
  simpa [x, branches_length] using h

end Spectrum

end LabelledTree
end ManuscriptProofs.Carleman
