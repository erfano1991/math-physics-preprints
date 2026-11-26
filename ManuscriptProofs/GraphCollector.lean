import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

open scoped BigOperators
open Set

namespace ManuscriptProofs.GraphCollector

section Graph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Every vertex lies on one side of a closed complete bipartite block
with exactly `d` vertices on each side. -/
def HasBalancedBlocks (d : ℕ) : Prop :=
  ∀ x : V, ∃ A B : Finset V,
    x ∈ A ∧ Disjoint A B ∧ A.card = d ∧ B.card = d ∧
    (∀ a ∈ A, G.neighborFinset a = B) ∧ (∀ b ∈ B, G.neighborFinset b = A)

/-- The neighborhood equality arising in the strict-slack argument
characterizes disjoint unions of balanced complete bipartite blocks. -/
theorem hasBalancedBlocks_iff (d : ℕ) (hd : 0 < d)
    (hreg : ∀ x, G.degree x = d) :
    HasBalancedBlocks G d ↔
      ∀ u v x, G.Adj u x → G.Adj v x → G.neighborFinset u = G.neighborFinset v := by
  constructor
  · intro h u v x hux hvx
    obtain ⟨A, B, hu, _, _, _, hA, hB⟩ := h u
    have hx : x ∈ B := hA u hu ▸ (G.mem_neighborFinset u x).2 hux
    have hv : v ∈ A := hB x hx ▸ (G.mem_neighborFinset x v).2 hvx.symm
    exact (hA u hu).trans (hA v hv).symm
  · intro h u
    obtain ⟨v, huv⟩ := (G.degree_pos_iff_exists_adj u).mp (hreg u ▸ hd)
    let A := G.neighborFinset v
    let B := G.neighborFinset u
    have hA : ∀ a ∈ A, G.neighborFinset a = B := by
      intro a ha
      exact h a u v ((G.mem_neighborFinset v a).mp ha).symm huv
    have hB : ∀ b ∈ B, G.neighborFinset b = A := by
      intro b hb
      exact h b v u ((G.mem_neighborFinset u b).mp hb).symm huv.symm
    refine ⟨A, B, (G.mem_neighborFinset v u).2 huv.symm, ?_, hreg v, hreg u, hA, hB⟩
    rw [Finset.disjoint_left]
    intro a ha hb
    exact G.notMem_neighborFinset_self a (hA a ha ▸ hb)

end Graph

section RatioMean

variable {ι : Type*}

/-- The graph collector's ratio inequality after establishing the two
monotonicity properties of its Poisson-tail ratios. It includes strictness
when the neighborhood counts differ. -/
theorem ratio_mean (s : Finset ι) (hs : s.Nonempty) (k : ι → ℕ) (R : ℕ → ℝ)
    (hk : ∀ i ∈ s, 0 < k i) (hR : ∀ n > 0, 0 < R n)
    (hmono : StrictMonoOn R (Ioi 0))
    (hanti : AntitoneOn (fun n : ℕ => R n / n) (Ioi 0)) :
    (∑ i ∈ s, R (k i) / (k i : ℝ)) ≤
        (∑ i ∈ s, 1 / (k i : ℝ)) *
          (∏ i ∈ s, R (k i) ^ (s.card : ℝ)⁻¹) ∧
    ((∃ i ∈ s, ∃ j ∈ s, k i ≠ k j) →
      (∑ i ∈ s, R (k i) / (k i : ℝ)) <
        (∑ i ∈ s, 1 / (k i : ℝ)) *
          (∏ i ∈ s, R (k i) ^ (s.card : ℝ)⁻¹)) := by
  let n : ℝ := s.card
  have hn : 0 < n := by
    change (0 : ℝ) < (s.card : ℝ)
    exact_mod_cast hs.card_pos
  have hr (i : ι) (hi : i ∈ s) : 0 < R (k i) := hR _ (hk i hi)
  have hm : MonovaryOn (fun i => R (k i) / (k i : ℝ)) (fun i => (R (k i))⁻¹) (↑s : Set ι) := by
    intro i hi j hj hij
    have hji := (inv_lt_inv₀ (hr i hi) (hr j hj)).mp hij
    have hkj : k j ≤ k i := by
      by_contra! hlt
      exact (not_lt_of_ge (hmono (hk i hi) (hk j hj) hlt).le) hji
    exact hanti (hk j hj) (hk i hi) hkj
  have hC := hm.sum_mul_sum_le_card_mul_sum
  have hcancel (i : ι) (hi : i ∈ s) :
      R (k i) / (k i : ℝ) * (R (k i))⁻¹ = 1 / (k i : ℝ) := by
    rw [div_eq_mul_inv, mul_comm (R (k i)), mul_assoc, mul_inv_cancel₀ (hr i hi).ne',
      mul_one, one_div]
  have hprod : (∑ i ∈ s, R (k i) / (k i : ℝ) * (R (k i))⁻¹) =
      ∑ i ∈ s, 1 / (k i : ℝ) := Finset.sum_congr rfl hcancel
  rw [hprod] at hC
  let q : ℝ := ∑ i ∈ s, n⁻¹ / R (k i)
  let g : ℝ := ∏ i ∈ s, R (k i) ^ n⁻¹
  have hi : 0 < ∑ i ∈ s, (R (k i))⁻¹ :=
    Finset.sum_pos (fun i hi => inv_pos.mpr (hr i hi)) hs
  have hqeq : q = n⁻¹ * ∑ i ∈ s, (R (k i))⁻¹ := by simp [q, Finset.mul_sum, div_eq_mul_inv]
  have hq : 0 < q := by rw [hqeq]; exact mul_pos (inv_pos.mpr hn) hi
  have hgm : 0 < g := Finset.prod_pos fun i hi => Real.rpow_pos_of_pos (hr i hi) _
  have hweight : (∑ _i ∈ s, n⁻¹) = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hn.ne'
  have hHM : q⁻¹ ≤ g := Real.harm_mean_le_geom_mean_weighted s
    (fun _ => n⁻¹) (fun i => R (k i)) hs (fun _ _ => inv_pos.mpr hn) hweight hr
  have hbase : (∑ i ∈ s, R (k i) / (k i : ℝ)) ≤
      (∑ i ∈ s, 1 / (k i : ℝ)) * q⁻¹ := by
    calc
      _ ≤ (n * ∑ i ∈ s, 1 / (k i : ℝ)) / (∑ i ∈ s, (R (k i))⁻¹) :=
        (le_div_iff₀ hi).mpr hC
      _ = _ := by rw [hqeq]; field_simp [hn.ne', hi.ne']
  have hp : 0 < ∑ i ∈ s, 1 / (k i : ℝ) :=
    Finset.sum_pos (fun i hi => one_div_pos.mpr (by exact_mod_cast hk i hi)) hs
  refine ⟨hbase.trans (mul_le_mul_of_nonneg_left hHM hp.le), fun hne => ?_⟩
  have hstrict := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos s
    (fun _ => n⁻¹) (fun i => (R (k i))⁻¹)
    (fun _ _ => inv_pos.mpr hn) hweight (fun i hi => inv_nonneg.mpr (hr i hi).le)).mpr ?_
  · have hginv : g⁻¹ = ∏ i ∈ s, (R (k i))⁻¹ ^ n⁻¹ := by
      unfold g
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i hi => (Real.inv_rpow (hr i hi).le _).symm
    rw [← hginv] at hstrict
    have hstrict' : g⁻¹ < q := by simpa [q, div_eq_mul_inv] using hstrict
    have hqg : q⁻¹ < g := by
      simpa using (inv_lt_inv₀ hq (inv_pos.mpr hgm)).mpr hstrict'
    exact hbase.trans_lt (mul_lt_mul_of_pos_left hqg hp)
  · obtain ⟨i, hi, j, hj, hij⟩ := hne
    refine ⟨i, hi, j, hj, ?_⟩
    intro he
    apply hij
    apply hmono.injOn (hk i hi) (hk j hj)
    exact inv_injective he

end RatioMean

section Generator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of still-uncovered neighbors of a vertex. -/
def uncoveredNeighbors (U : Finset V) (v : V) : ℕ :=
  (G.neighborFinset v ∩ U).card

/-- Each active vertex is counted once for each of its uncovered neighbors. -/
theorem incidence_sum (U : Finset V) (f : V → ℝ) :
    (∑ u ∈ U, ∑ v ∈ G.neighborFinset u, f v) =
      ∑ v, (uncoveredNeighbors G U v : ℝ) * f v := by
  classical
  calc
    _ = ∑ u ∈ U, ∑ v, if G.Adj u v then f v else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [G.neighborFinset_eq_filter, Finset.sum_filter]
    _ = ∑ v, ∑ u ∈ U, if G.Adj v u then f v else 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => by
        by_cases huv : G.Adj u v
        · simp [huv, huv.symm]
        · have hvu : ¬ G.Adj v u := fun h => huv h.symm
          simp [huv, hvu]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.sum_filter]
      have he : U.filter (G.Adj v) = G.neighborFinset v ∩ U := by
        ext u
        simp [and_comm]
      simp [he, uncoveredNeighbors, nsmul_eq_mul]

/-- The normalized generator inequality for the product barrier. The
two monotonicity premises are the ratio estimates supplied by the manuscript's
Poisson-tail calculation. -/
theorem ratio_generator (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (U : Finset V) (R : ℕ → ℝ)
    (hR : ∀ k > 0, 0 < R k)
    (hmono : StrictMonoOn R (Ioi 0))
    (hanti : AntitoneOn (fun n : ℕ => R n / n) (Ioi 0)) :
    (∑ v, if 0 < uncoveredNeighbors G U v then R (uncoveredNeighbors G U v) - 1 else 0) ≤
      ∑ u ∈ U, (∑ v ∈ G.neighborFinset u, 1 / (uncoveredNeighbors G U v : ℝ)) *
        ((∏ v ∈ G.neighborFinset u, R (uncoveredNeighbors G U v) ^ (d : ℝ)⁻¹) - 1) := by
  classical
  let k := uncoveredNeighbors G U
  have hcount : (∑ v, if 0 < k v then R (k v) - 1 else 0) =
      ∑ u ∈ U, ∑ v ∈ G.neighborFinset u, (R (k v) - 1) / (k v : ℝ) := by
    rw [incidence_sum]
    apply Finset.sum_congr rfl
    intro v _
    change (if 0 < k v then R (k v) - 1 else 0) =
      (k v : ℝ) * ((R (k v) - 1) / (k v : ℝ))
    by_cases hp : 0 < k v
    · have hne : (k v : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [hp, ite_true]
      rw [div_eq_mul_inv, mul_comm (k v : ℝ), mul_assoc,
        inv_mul_cancel₀ hne, mul_one]
    · have hz : k v = 0 := by omega
      simp [hz]
  rw [hcount]
  apply Finset.sum_le_sum
  intro u hu
  have hne : (G.neighborFinset u).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hreg u]
    exact hd
  have hk (v : V) (hv : v ∈ G.neighborFinset u) : 0 < k v := by
    apply Finset.card_pos.mpr
    have hu' := (G.mem_neighborFinset v u).mpr ((G.mem_neighborFinset u v).mp hv).symm
    exact ⟨u, Finset.mem_inter.mpr ⟨hu', hu⟩⟩
  have h := (ratio_mean _ hne k R hk hR hmono hanti).1
  rw [G.card_neighborFinset_eq_degree, hreg u] at h
  simp_rw [sub_div, Finset.sum_sub_distrib, mul_sub, mul_one]
  exact sub_le_sub_right h _

end Generator

/-- The finite backward-equation comparison with a nonnegative slack.
This uses the derivative on positive times, so differentiation at zero
is unnecessary. -/
theorem comparison_of_backward_equation {V : Type*} [DecidableEq V]
    (D slack : Finset V → ℝ → ℝ) (rate : Finset V → V → ℝ) (exit : Finset V → ℝ)
    (hcont : ∀ U, ContinuousOn (D U) (Ici 0)) (hinit : ∀ U, D U 0 = 0)
    (hrate : ∀ U u, u ∈ U → 0 ≤ rate U u)
    (hslack : ∀ U t, 0 < t → 0 ≤ slack U t)
    (hderiv : ∀ U t, 0 < t →
      HasDerivAt (D U)
        ((∑ u ∈ U, rate U u * D (U.erase u) t) + slack U t - exit U * D U t) t) :
    ∀ U t, 0 ≤ t → 0 ≤ D U t := by
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
      let F : ℝ → ℝ := fun t => Real.exp (exit U * t) * D U t
      have hf : ContinuousOn F (Ici 0) :=
        ((continuous_const.mul continuous_id).rexp.continuousOn).mul (hcont U)
      have hf' (t : ℝ) (ht : 0 < t) :
          HasDerivAt F
            (Real.exp (exit U * t) *
              ((∑ u ∈ U, rate U u * D (U.erase u) t) + slack U t)) t := by
        convert (((hasDerivAt_id t).const_mul (exit U)).exp.mul (hderiv U t ht)) using 1 <;>
          try rfl
        try simp only [id_eq, mul_one]
        ring
      have hmono : MonotoneOn F (Ici 0) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hf
        · intro t ht
          rw [interior_Ici, mem_Ioi] at ht
          exact (hf' t ht).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [interior_Ici, mem_Ioi] at ht
          rw [(hf' t ht).deriv]
          apply mul_nonneg (Real.exp_pos _).le (add_nonneg _ (hslack U t ht))
          exact Finset.sum_nonneg fun u hu =>
            mul_nonneg (hrate U u hu) (ih (U.erase u) (Finset.erase_ssubset hu) t ht.le)
      intro t ht
      have hFt := hmono (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
      change Real.exp (exit U * 0) * D U 0 ≤ Real.exp (exit U * t) * D U t at hFt
      rw [hinit U, mul_zero] at hFt
      exact nonneg_of_mul_nonneg_right hFt (Real.exp_pos _)

end ManuscriptProofs.GraphCollector
