import ManuscriptProofs.QutritCertificate
import Mathlib.Data.Nat.Choose.Basic

namespace ManuscriptProofs.Qutrit

/- Exact power coefficients of the finite angular and radial moment sum.
All computations in this section use rational arithmetic in the kernel. -/
private def sumTo (n : ℕ) (f : ℕ → ℚ) : ℚ := ((List.range (n+1)).map f).sum

private def alternating (j : ℕ) : ℚ := if j % 2 = 0 then 1 else -1

/-- Coefficient of s^d in (1-s²)^b (-s)^a. -/
private def angularCoeff (a b d : ℕ) : ℚ :=
  if a ≤ d ∧ (d-a) % 2 = 0 then
    alternating (a + (d-a)/2) * (b.choose ((d-a)/2) : ℚ)
  else 0

/-- Coefficient of degree d in M_{r,n} after the binomial expansion
in the paper. The innermost sum integrates z^(r+a) (1-z²)^b. -/
def haarMomentCoeff (r n d : ℕ) : ℚ :=
  sumTo (n/2) fun b =>
    ((n.choose (2*b) : ℚ) * ((2*b).choose b : ℚ) / (2^n * 4^b)) *
    sumTo (n-2*b) fun a =>
      let c := angularCoeff a b d
      if c = 0 then 0 else
        (c * ((n-2*b).choose a : ℚ)) *
        sumTo b (fun j => alternating j * (b.choose j : ℚ) / (r+a+2*j+1 : ℕ))

/-- Coefficients of 1-(1-y)^7 (1+7y+28y²). -/
private def gate (m : ℕ) : ℚ :=
  let coeff := fun i => alternating i * (Nat.choose 7 i : ℚ)
  (if m=0 then 1 else 0) - coeff m -
    (if 1≤m then 7*coeff (m-1) else 0) -
    (if 2≤m then 28*coeff (m-2) else 0)

/-- Integrating H(y)(3-7y) against 6y(1-y) dy / 8 by monomials. -/
def gateBias : ℚ :=
  sumTo 9 fun m => ((if m=0 then 1 else 0) - gate m) * (6/8) *
    (3/((m+2)*(m+3) : ℕ) - 7/((m+3)*(m+4) : ℕ))

theorem gate_bias_exact : (gateBias : ℝ) = gamma := by
  have h : gateBias = (419/11440 : ℚ) := by decide +kernel
  rw [h]
  norm_num [gamma]

private def shifted (offset d : ℕ) (f : ℕ → ℚ) : ℚ :=
  if offset ≤ d then f (d-offset) else 0

/-- Degree-d coefficient of s*c(s) from the two radial terms, with the
actual choices λ=2/3, k=8/9 and both proposal powers i=0,1. -/
def radialSwitchCoeff (d : ℕ) : ℚ :=
  sumTo 9 fun m =>
    let g := gate m
    if g = 0 then 0 else
      let L := haarMomentCoeff 1
      let K := haarMomentCoeff 2
      3*g*((L (m+2) d/9 - 4/9*shifted 2 d (L (m+2))
            + 1/3*shifted 1 d (K (m+1)) + 2/3*shifted 2 d (L (m+1))) / (m+5 : ℕ)
          + 8/9*sumTo 1 (fun i =>
              shifted 2 d (fun j => L (m+i+2) j - L (m+i+3) j) / (m+i+6 : ℕ)))

private theorem sumTo_zero (n : ℕ) (f : ℕ → ℚ) (hf : ∀ k ≤ n, f k = 0) :
    sumTo n f = 0 := by
  unfold sumTo
  have he : (List.range (n+1)).map f = (List.range (n+1)).map (fun _ => (0:ℚ)) :=
    List.map_congr_left fun k hk => hf k (by simpa [Nat.lt_succ_iff] using List.mem_range.mp hk)
  simp [he]

private theorem moment_zero_above_degree {r n d : ℕ} (h : n < d) : haarMomentCoeff r n d = 0 := by
  unfold haarMomentCoeff
  apply sumTo_zero
  intro b hb
  apply mul_eq_zero_of_right
  apply sumTo_zero
  intro a ha
  have hzero : angularCoeff a b d = 0 := by
    unfold angularCoeff
    split_ifs with hh
    · rw [Nat.choose_eq_zero_of_lt (by omega : b < (d-a)/2), Nat.cast_zero, mul_zero]
    · rfl
  simp [hzero]

theorem radial_zero_above_degree {d : ℕ} (hd : 15 < d) : radialSwitchCoeff d = 0 := by
  unfold radialSwitchCoeff
  apply sumTo_zero
  intro m hm
  by_cases hg : gate m = 0
  · simp [hg]
  · have ht : sumTo 1 (fun i => shifted 2 d (fun j => haarMomentCoeff 1 (m+i+2) j -
          haarMomentCoeff 1 (m+i+3) j) / (m+i+6 : ℕ)) = 0 := by
      apply sumTo_zero
      intro i hi
      simp [shifted, show 2 ≤ d by omega, moment_zero_above_degree (n := m+i+2) (d := d-2) (by omega),
        moment_zero_above_degree (n := m+i+3) (d := d-2) (by omega)]
    simp only [hg, ↓reduceIte, ht, mul_zero, add_zero]
    simp [shifted, show 2 ≤ d by omega, show 1 ≤ d by omega,
      moment_zero_above_degree (n := m+2) (d := d) (by omega),
      moment_zero_above_degree (n := m+2) (d := d-2) (by omega),
      moment_zero_above_degree (n := m+1) (d := d-1) (by omega),
      moment_zero_above_degree (n := m+1) (d := d-2) (by omega)]

/-- The maximum possible degree before cancellation is 15 (m≤9, i≤1).
The extra coefficient at degree 15 is explicitly checked to vanish. -/
def radialCoefficients : List ℚ := (List.range 16).map radialSwitchCoeff

def switchNumerators : List ℤ :=
  [31229004446640, 52372067844096, 147033739966113, -148349739073536,
   -35635226833206, 0, 1364675118807, 0, -896931175140, 0,
   -526800058785, 0, -15955401462, 0, -3598185591, 0]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem radial_coefficients_exact :
    radialCoefficients = switchNumerators.map (fun n => (n : ℚ)/3404184409866240) := by
  decide +kernel

noncomputable def evalCoefficients (s : ℝ) (p : List ℚ) : ℝ :=
  p.foldr (fun a z => (a : ℝ) + s*z) 0

/-- The paper's finite moment expression gives precisely the real polynomial
used in the Bernstein proof, for every real s. -/
theorem radial_sum_eq_switch (s : ℝ) : evalCoefficients s radialCoefficients = switchMoment s := by
  rw [radial_coefficients_exact]
  norm_num [evalCoefficients, switchNumerators, switchMoment, List.foldr]
  ring

theorem radial_sum_floor {s : ℝ} (hs : 0 ≤ s) (ht : s ≤ 1) :
    kappa ≤ evalCoefficients s radialCoefficients - s/20 + gamma*s^3 := by
  rw [radial_sum_eq_switch]
  exact switch_floor hs ht

end ManuscriptProofs.Qutrit
