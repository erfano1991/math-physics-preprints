import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

namespace ManuscriptProofs.Qutrit

/-- Power basis for the Haar switch moment s*c(s). The certificate script
derives these coefficients from the finite angular and radial moment sums. -/
noncomputable def switchMoment (s : ℝ) : ℝ :=
  (31229004446640
  + 52372067844096 * s
  + 147033739966113 * s ^ 2
  - 148349739073536 * s ^ 3
  - 35635226833206 * s ^ 4
  + 1364675118807 * s ^ 6
  - 896931175140 * s ^ 8
  - 526800058785 * s ^ 10
  - 15955401462 * s ^ 12
  - 3598185591 * s ^ 14) / 3404184409866240

noncomputable def kappa : ℝ := 339259 / 1107025920
noncomputable def gamma : ℝ := 419 / 11440

/-- Bernstein expansion after subtracting the endpoint value. The binomial
multiplicities are absorbed into the nonnegative integer coefficients. -/
theorem switch_floor {s : ℝ} (hs : 0 ≤ s) (ht : s ≤ 1) :
    kappa ≤ switchMoment s - s / 20 + gamma * s ^ 3 := by
  have hid : switchMoment s - s / 20 + gamma * s ^ 3 - kappa =
      (30185758594992 * (1-s) ^ 14
  + 304763467680672 * s ^ 1 * (1-s) ^ 13
  + 1362054787670577 * s ^ 2 * (1-s) ^ 12
  + 3537054592155084 * s ^ 3 * (1-s) ^ 11
  + 5922756703699836 * s ^ 4 * (1-s) ^ 10
  + 6867627071489184 * s ^ 5 * (1-s) ^ 9
  + 6265594304945976 * s ^ 6 * (1-s) ^ 8
  + 5763773691836160 * s ^ 7 * (1-s) ^ 7
  + 5917519848624384 * s ^ 8 * (1-s) ^ 6
  + 5382307026480384 * s ^ 9 * (1-s) ^ 5
  + 3531622254031872 * s ^ 10 * (1-s) ^ 4
  + 1508457979252224 * s ^ 11 * (1-s) ^ 3
  + 376059920011776 * s ^ 12 * (1-s) ^ 2
  + 41813346871296 * s ^ 13 * (1-s) ^ 1) / 3404184409866240 := by
    unfold switchMoment gamma kappa
    ring
  have hu : 0 ≤ 1-s := sub_nonneg.mpr ht
  apply sub_nonneg.mp
  rw [hid]
  positivity

theorem endpoint_exact : switchMoment 1 - 1/20 + gamma = kappa := by
  norm_num [switchMoment, gamma, kappa]

/-- For any two distinct rays the prescribed thinning is a probability. -/
theorem switch_probability {s : ℝ} (hs : 0 < s) (ht : s ≤ 1) :
    let c := switchMoment s / s
    let a := 1/20 + kappa - gamma*s^2
    0 < c ∧ 0 ≤ a/c ∧ a/c ≤ 1 := by
  have hk : 0 ≤ kappa := by norm_num [kappa]
  have hg : 0 ≤ gamma := by norm_num [gamma]
  have hgt : gamma < 1/20 := by norm_num [gamma]
  have hsq : s^2 ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 1+s by linarith)]
  have ha : 0 < 1/20 + kappa - gamma*s^2 := by nlinarith [mul_nonneg hg (sub_nonneg.mpr hsq)]
  have hle : 1/20 + kappa - gamma*s^2 ≤ switchMoment s / s := by
    apply (le_div_iff₀ hs).2
    nlinarith [switch_floor hs.le ht, mul_nonneg hk (sub_nonneg.mpr ht)]
  have hc := lt_of_lt_of_le ha hle
  exact ⟨hc, div_nonneg ha.le hc.le, (div_le_one hc).2 hle⟩

theorem visibility_and_gap :
    (2:ℝ)/5 + 3*kappa = 29588543/73801728 ∧
    (5:ℝ)/12 - (2/5 + 3*kappa) = 1162177/73801728 := by
  norm_num [kappa]

end ManuscriptProofs.Qutrit
