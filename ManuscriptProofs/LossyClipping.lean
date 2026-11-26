import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open MeasureTheory Set intervalIntegral

namespace ManuscriptProofs.LossyQubit

/-- A mesh error uniform over every monotone response, even one whose only
positive value on the interval is at the right endpoint. -/
theorem clipped_interval_average (f : ℝ → ℝ) (hf : MonotoneOn f (Icc 0 1))
    (h0 : 0 ≤ f 0) (h1 : f 1 ≤ 1) {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ t in (0 : ℝ)..1, f (min 1 (t+h))) ≤ (∫ t in (0 : ℝ)..1, f t) + h := by
  let g := fun t : ℝ => f (min 1 (t+h))
  have hg : MonotoneOn g (Icc 0 1) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨le_min zero_le_one (add_nonneg hx.1 hh), min_le_left _ _⟩
    · exact ⟨le_min zero_le_one (add_nonneg hy.1 hh), min_le_left _ _⟩
    · exact min_le_min_left 1 (by linarith)
  have integ {u : ℝ → ℝ} (hu : MonotoneOn u (Icc 0 1)) {l b : ℝ}
      (hl : 0 ≤ l) (hlb : l ≤ b) (hb : b ≤ 1) : IntervalIntegrable u volume l b :=
    (hu.mono (by rw [uIcc_of_le hlb]; exact Icc_subset_Icc hl hb)).intervalIntegrable
  have hcut : 0 ≤ 1-h := by linarith
  have hlast : 1-h ≤ 1 := by linarith
  have hleft : (∫ t in (0:ℝ)..(1-h), g t) = ∫ t in h..1, f t := calc
    _ = ∫ t in (0:ℝ)..(1-h), f (t+h) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hcut] at ht
      exact congrArg f (min_eq_right (by linarith [ht.2]))
    _ = _ := by rw [integral_comp_add_right]; simp
  have hright : (∫ t in (1-h)..1, g t) = h*f 1 := calc
    _ = ∫ _ in (1-h)..1, f 1 := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hlast] at ht
      exact congrArg f (min_eq_left (by linarith [ht.1]))
    _ = _ := by rw [intervalIntegral.integral_const]; simp
  have hhead : 0 ≤ ∫ t in (0:ℝ)..h, f t :=
    intervalIntegral.integral_nonneg hh (fun t ht => h0.trans (hf ⟨le_rfl,zero_le_one⟩ ⟨ht.1,ht.2.trans hh1⟩ ht.1))
  have hsplit := integral_add_adjacent_intervals (integ hf le_rfl hh hh1) (integ hf hh hh1 le_rfl)
  change (∫ t in (0:ℝ)..1, g t) ≤ _
  rw [← integral_add_adjacent_intervals (integ hg le_rfl hcut hlast) (integ hg hcut hlast le_rfl),
    hleft, hright]
  linarith [mul_le_mul_of_nonneg_left h1 hh]

/-- A representative score v lies within h above the true score u. When
u has the uniform law, grouping the representatives by cells gives the
paper's area-weighted upper estimate. -/
theorem representative_average {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u v : X → ℝ) (f : ℝ → ℝ) (hf : Monotone f) (h0 : 0 ≤ f 0) (h1 : f 1 ≤ 1)
    {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hu : MeasurePreserving u μ (volume.restrict (Ioc 0 1)))
    (hv : ∀ x, v x ≤ 1 ∧ v x ≤ u x+h) (hint : Integrable (fun x => f (v x)) μ) :
    (∫ x, f (v x) ∂μ) ≤ (∫ t in (0:ℝ)..1, f t) + h := by
  let g := fun t : ℝ => f (min 1 (t+h))
  have hgm : Monotone g := fun x y hxy => hf (min_le_min_left 1 (by linarith))
  have hgi : Integrable g (volume.restrict (Ioc 0 1)) :=
    (hgm.intervalIntegrable (a := 0) (b := 1)).1
  have hcomp := hu.integrable_comp_of_integrable hgi
  calc
    _ ≤ ∫ x, g (u x) ∂μ := MeasureTheory.integral_mono hint hcomp (fun x => hf (le_min (hv x).1 (hv x).2))
    _ = ∫ t, g t ∂(volume.restrict (Ioc 0 1)) := by
      rw [← hu.map_eq]
      exact (integral_map hu.measurable.aemeasurable hgm.measurable.aestronglyMeasurable).symm
    _ = ∫ t in (0:ℝ)..1, g t := (integral_of_le zero_le_one).symm
    _ ≤ _ := clipped_interval_average f (hf.monotoneOn _) h0 h1 hh hh1

/-- The branch response used in the paper, including its rank-one endpoint. -/
noncomputable def branchResponse (r t : ℝ) : ℝ :=
  if r=1 then (if t=1 then 1 else 0) else (1-r^2)/(2*(1-r*t))

/-- The actual finite-menu approximation with the same mesh error for every
branch strength, including the discontinuous rank-one response. -/
theorem branch_quadrature {X : Type*} [MeasurableSpace X] (μ : Measure X) (u v : X → ℝ)
    {h r : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hu : MeasurePreserving u μ (volume.restrict (Ioc 0 1)))
    (hv : ∀ x, v x ∈ Icc 0 1) (hclose : ∀ x, v x ≤ u x+h)
    (hint : Integrable (fun x => branchResponse r (v x)) μ) :
    (∫ x, branchResponse r (v x) ∂μ) ≤ (∫ t in (0:ℝ)..1, branchResponse r t) + h := by
  let f := branchResponse r
  have hmono : MonotoneOn f (Icc 0 1) := by
    intro x hx y hy hxy
    by_cases he : r=1
    · subst r
      by_cases hx' : x=1
      · have hy' : y=1 := by linarith [hy.2]
        simp [f,branchResponse,hx',hy']
      · simp [f,branchResponse,hx']
        split <;> norm_num
    · have hr' := lt_of_le_of_ne hr1 he
      have hn : 0 ≤ 1-r^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (by linarith : 0 ≤ 1+r)]
      have hp : 0 < 2*(1-r*y) := by
        have hp := mul_le_mul_of_nonneg_left hy.2 hr
        linarith
      simp only [f,branchResponse,he,↓reduceIte]
      apply div_le_div_of_nonneg_left hn hp
      linarith [mul_le_mul_of_nonneg_left hxy hr]
  let clip := fun t : ℝ => max 0 (min 1 t)
  have hclip (t : ℝ) : clip t ∈ Icc 0 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hid {t : ℝ} (ht : t ∈ Icc 0 1) : clip t = t :=
    by simp [clip, min_eq_right ht.2, max_eq_right ht.1]
  have hg : Monotone (fun t => f (clip t)) := fun x y hxy =>
    hmono (hclip x) (hclip y) (max_le_max_left 0 (min_le_min_left 1 hxy))
  have hends : 0 ≤ f 0 ∧ f 1 ≤ 1 := by
    by_cases he : r=1
    · simp [f,branchResponse,he]
    · have hr' := lt_of_le_of_ne hr1 he
      simp [f,branchResponse,he]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ 1+r by linarith)]
      · apply (div_le_one (by linarith : 0 < 2*(1-r))).2
        nlinarith [sq_nonneg (1-r)]
  have hv' : (fun x => f (clip (v x))) = (fun x => branchResponse r (v x)) :=
    funext fun x => congrArg f (hid (hv x))
  have hb := representative_average μ u v (fun t => f (clip t)) hg
    (by simpa [clip] using hends.1) (by simpa [clip] using hends.2) hh hh1 hu
    (fun x => ⟨(hv x).2,hclose x⟩) (by rwa [hv'])
  rw [hv'] at hb
  have heq : (∫ t in (0:ℝ)..1, f (clip t)) = ∫ t in (0:ℝ)..1, branchResponse r t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact congrArg f (hid (by simpa [uIcc_of_le zero_le_one] using ht))
  rwa [heq] at hb

end ManuscriptProofs.LossyQubit
