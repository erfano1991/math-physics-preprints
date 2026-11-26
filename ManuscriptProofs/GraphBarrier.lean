import ManuscriptProofs.GraphPoisson
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open scoped BigOperators
open Set

namespace ManuscriptProofs.GraphCollector

private theorem poissonTail_continuous (k : ℕ) : Continuous (fun x => poissonTail x k) := by
  cases k with
  | zero => simpa only [poisson_tail_zero] using (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
  | succ k => exact continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_poisson_tail_succ x k).continuousAt

private theorem poissonTail_zero_arg (k : ℕ) : poissonTail 0 (k + 1) = 0 := by
  have hm (j : ℕ) : poissonMass 0 (k + 1 + j) = 0 := by
    simp [poissonMass, zero_pow (by omega : k + 1 + j ≠ 0)]
  simp only [poissonTail, hm, tsum_zero]

private theorem poissonRatio_zero (x : ℝ) : poissonRatio x 0 = 1 := by
  simp [poissonRatio, poisson_tail_zero]

private theorem hasDerivAt_tail_ratio {x : ℝ} (hx : 0 < x) (k : ℕ) :
    HasDerivAt (fun s => poissonTail s k) ((poissonRatio x k - 1) * poissonTail x k) x := by
  cases k with
  | zero =>
      simpa only [poisson_tail_zero, poissonRatio_zero, sub_self, zero_mul] using
        hasDerivAt_const x (1 : ℝ)
  | succ k =>
      have he : (poissonRatio x (k + 1) - 1) * poissonTail x (k + 1) = poissonMass x k := by
        simp only [poissonRatio, Nat.add_sub_cancel, sub_mul, one_mul,
          div_mul_cancel₀ _ (poisson_tail_pos hx _).ne']
        linarith [poisson_tail_succ x k]
      rw [he]
      exact hasDerivAt_poisson_tail_succ x k

private theorem hasDerivAt_powered_tail (d : ℝ) (hd : 0 < d) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    HasDerivAt (fun s => poissonTail (d * s) k ^ d⁻¹)
      ((poissonRatio (d * t) k - 1) * poissonTail (d * t) k ^ d⁻¹) t := by
  have hx := mul_pos hd ht
  have hp := poisson_tail_pos hx k
  have h := ((hasDerivAt_tail_ratio hx k).comp t ((hasDerivAt_id t).const_mul d)).rpow_const
    (p := d⁻¹) (Or.inl hp.ne')
  have he : ((poissonRatio (d * t) k - 1) * poissonTail (d * t) k * (d * 1)) * d⁻¹ *
      poissonTail (d * t) k ^ (d⁻¹ - 1) =
      (poissonRatio (d * t) k - 1) * poissonTail (d * t) k ^ d⁻¹ := by
    rw [Real.rpow_sub_one hp.ne']
    field_simp [hd.ne', hp.ne']
  simp only [Function.comp_apply] at h
  rw [he] at h
  exact h

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The product of powered Poisson tails at the graph's uncovered counts. -/
noncomputable def poissonBarrier (d : ℕ) (U : Finset V) (t : ℝ) : ℝ :=
  ∏ v, poissonTail ((d : ℝ) * t) (uncoveredNeighbors G U v) ^ (d : ℝ)⁻¹

/-- The total rate at which a specified remaining vertex is removed. -/
noncomputable def coverageRate (U : Finset V) (u : V) : ℝ :=
  ∑ v ∈ G.neighborFinset u, 1 / (uncoveredNeighbors G U v : ℝ)

/-- The backward generator on functions of the uncovered vertex set. -/
noncomputable def coverageGenerator (F : Finset V → ℝ → ℝ) (U : Finset V) (t : ℝ) : ℝ :=
  ∑ u ∈ U, coverageRate G U u * (F (U.erase u) t - F U t)

theorem poissonBarrier_continuous (d : ℕ) (U : Finset V) : Continuous (poissonBarrier G d U) := by
  unfold poissonBarrier
  apply continuous_finsetProd
  intro v _
  apply ((poissonTail_continuous (uncoveredNeighbors G U v)).comp
    (continuous_const.mul continuous_id)).rpow_const
  exact fun _ => Or.inr (inv_nonneg.mpr (Nat.cast_nonneg d))

private theorem uncovered_pos_of_neighbor (U : Finset V) {u v : V} (hu : u ∈ U)
    (hv : v ∈ G.neighborFinset u) : 0 < uncoveredNeighbors G U v := by
  apply Finset.card_pos.mpr
  exact ⟨u, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr
    ((G.mem_neighborFinset u v).mp hv).symm, hu⟩⟩

theorem poissonBarrier_initial (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (U : Finset V) :
    poissonBarrier G d U 0 = if U = ∅ then 1 else 0 := by
  by_cases hU : U = ∅
  · subst U
    simp [poissonBarrier, uncoveredNeighbors, poisson_tail_zero]
  · obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    have hc : 0 < (G.neighborFinset u).card := by
      rw [G.card_neighborFinset_eq_degree, hreg u]
      exact hd
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hc
    have hpos := uncovered_pos_of_neighbor G U hu hv
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    simp only [hU, ite_false, poissonBarrier, mul_zero]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [hk, poissonTail_zero_arg, Real.zero_rpow]
    exact inv_ne_zero (by exact_mod_cast hd.ne')

/-- The time derivative of the barrier is its value times the sum of
active ratios minus one. -/
theorem hasDerivAt_poissonBarrier (d : ℕ) (hd : 0 < d) (U : Finset V) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (poissonBarrier G d U)
      (poissonBarrier G d U t * ∑ v, if 0 < uncoveredNeighbors G U v then
        poissonRatio ((d : ℝ) * t) (uncoveredNeighbors G U v) - 1 else 0) t := by
  classical
  let x : ℝ := (d : ℝ) * t
  let k := uncoveredNeighbors G U
  let p (v : V) := poissonTail x (k v) ^ (d : ℝ)⁻¹
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset V))
    fun v _ => hasDerivAt_powered_tail (d : ℝ) hd' ht (k v)
  have he (v : V) : (if 0 < k v then poissonRatio x (k v) - 1 else 0) =
      poissonRatio x (k v) - 1 := by
    by_cases hv : 0 < k v
    · simp [hv]
    · have hzero : k v = 0 := by omega
      simp [hzero, poissonRatio_zero]
  change HasDerivAt (poissonBarrier G d U)
    (poissonBarrier G d U t * ∑ v, if 0 < k v then poissonRatio x (k v) - 1 else 0) t
  have hcoeff : poissonBarrier G d U t * (∑ v, (poissonRatio x (k v) - 1)) =
      ∑ v, (∏ j ∈ Finset.univ.erase v, p j) * ((poissonRatio x (k v) - 1) * p v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    change (∏ j, p j) * (poissonRatio x (k v) - 1) =
      (∏ j ∈ Finset.univ.erase v, p j) * ((poissonRatio x (k v) - 1) * p v)
    rw [← Finset.prod_erase_mul _ _ hv]
    ring
  rw [show (∑ v, if 0 < k v then poissonRatio x (k v) - 1 else 0) =
    ∑ v, (poissonRatio x (k v) - 1) from Finset.sum_congr rfl fun v _ => he v, hcoeff]
  simpa only [smul_eq_mul, poissonBarrier, p, x] using! h

/-- Removing u multiplies the barrier by precisely the neighbor ratios. -/
theorem poissonBarrier_erase (d : ℕ) (hd : 0 < d) (U : Finset V) {u : V} (hu : u ∈ U)
    {t : ℝ} (ht : 0 < t) :
    poissonBarrier G d (U.erase u) t =
      poissonBarrier G d U t *
        ∏ v ∈ G.neighborFinset u, poissonRatio ((d : ℝ) * t) (uncoveredNeighbors G U v) ^ (d : ℝ)⁻¹ := by
  classical
  let x : ℝ := (d : ℝ) * t
  let r : ℝ := (d : ℝ)⁻¹
  let k := uncoveredNeighbors G U
  let Q (v : V) := poissonRatio x (k v) ^ r
  let P (v : V) := poissonTail x (k v) ^ r
  have hdx : 0 < (d : ℝ) := by exact_mod_cast hd
  have hx : 0 < x := mul_pos hdx ht
  have hfactor (v : V) :
      poissonTail x (uncoveredNeighbors G (U.erase u) v) ^ r =
        P v * if v ∈ G.neighborFinset u then Q v else 1 := by
    by_cases hv : v ∈ G.neighborFinset u
    · have hs : u ∈ G.neighborFinset v ∩ U :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v u).mpr
          ((G.mem_neighborFinset u v).mp hv).symm, hu⟩
      have hnew : uncoveredNeighbors G (U.erase u) v = k v - 1 := by
        exact (congrArg Finset.card (Finset.inter_erase _ _ _)).trans (Finset.card_erase_of_mem hs)
      have hratio : poissonTail x (k v - 1) = poissonTail x (k v) * poissonRatio x (k v) := by
        rw [mul_comm, poissonRatio, div_mul_cancel₀ _ (poisson_tail_pos hx _).ne']
      rw [ite_eq_left hv, hnew, hratio]
      exact Real.mul_rpow (poisson_tail_pos hx _).le (poisson_ratio_pos hx _).le
    · have hs : u ∉ G.neighborFinset v ∩ U := by
        intro h
        exact hv ((G.mem_neighborFinset u v).mpr
          ((G.mem_neighborFinset v u).mp (Finset.mem_inter.mp h).1).symm)
      have hnew : uncoveredNeighbors G (U.erase u) v = k v := by
        exact congrArg Finset.card ((Finset.inter_erase _ _ _).trans (Finset.erase_eq_of_notMem hs))
      rw [ite_eq_right hv, hnew, mul_one]
  change (∏ v, poissonTail x (uncoveredNeighbors G (U.erase u) v) ^ r) =
    (∏ v, P v) * ∏ v ∈ G.neighborFinset u, Q v
  simp_rw [hfactor, Finset.prod_mul_distrib]
  rw [← Finset.prod_filter]
  have hfilter : (Finset.univ : Finset V).filter (fun v => v ∈ G.neighborFinset u) =
      G.neighborFinset u := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfilter]

/-- The explicit barrier is a subsolution of the graph's backward equation. -/
theorem poissonBarrier_deriv_le_generator (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (U : Finset V) {t : ℝ} (ht : 0 < t) :
    deriv (poissonBarrier G d U) t ≤ coverageGenerator G (poissonBarrier G d) U t := by
  let x : ℝ := (d : ℝ) * t
  have hdx : 0 < (d : ℝ) := by exact_mod_cast hd
  have hx : 0 < x := mul_pos hdx ht
  have hb : 0 ≤ poissonBarrier G d U t :=
    Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (poisson_tail_pos hx _).le _
  rw [(hasDerivAt_poissonBarrier G d hd U ht).deriv]
  refine (mul_le_mul_of_nonneg_left (poisson_ratio_generator G d hd hreg U hx) hb).trans_eq ?_
  rw [Finset.mul_sum, coverageGenerator]
  apply Finset.sum_congr rfl
  intro u hu
  rw [poissonBarrier_erase G d hd U hu ht]
  unfold coverageRate
  ring

/-- Any solution of the covering backward equation with the correct initial
condition lies above the explicit Poisson-tail barrier. -/
theorem poissonBarrier_le_of_backward_equation (d : ℕ) (hd : 0 < d)
    (hreg : ∀ v, G.degree v = d) (F : Finset V → ℝ → ℝ)
    (hcont : ∀ U, ContinuousOn (F U) (Ici 0))
    (hinit : ∀ U, F U 0 = if U = ∅ then 1 else 0)
    (hF : ∀ U t, 0 < t → HasDerivAt (F U) (coverageGenerator G F U t) t) :
    ∀ U t, 0 ≤ t → poissonBarrier G d U t ≤ F U t := by
  let H := poissonBarrier G d
  let D (U : Finset V) (t : ℝ) := F U t - H U t
  let slack (U : Finset V) (t : ℝ) := coverageGenerator G H U t - deriv (H U) t
  let exit (U : Finset V) := ∑ u ∈ U, coverageRate G U u
  have hD := comparison_of_backward_equation D slack (coverageRate G) exit
    (fun U => (hcont U).sub (poissonBarrier_continuous G d U).continuousOn)
    (fun U => sub_eq_zero.mpr ((hinit U).trans (poissonBarrier_initial G d hd hreg U).symm))
    (fun U u _ => Finset.sum_nonneg fun _ _ => div_nonneg zero_le_one (Nat.cast_nonneg _))
    (fun U t ht => sub_nonneg.mpr (poissonBarrier_deriv_le_generator G d hd hreg U ht))
    ?_
  · exact fun U t ht => sub_nonneg.mp (hD U t ht)
  · intro U t ht
    have hp := hasDerivAt_poissonBarrier G d hd U ht
    have hH : HasDerivAt (H U) (deriv (H U) t) t := hp.differentiableAt.hasDerivAt
    have h := (hF U t ht).sub hH
    have he : (∑ u ∈ U, coverageRate G U u * D (U.erase u) t) + slack U t - exit U * D U t =
        coverageGenerator G F U t - deriv (H U) t := by
      simp only [D, exit, slack, coverageGenerator, Finset.sum_mul]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [he]
    exact h

end ManuscriptProofs.GraphCollector
