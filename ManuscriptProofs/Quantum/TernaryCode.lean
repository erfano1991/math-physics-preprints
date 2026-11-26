import ManuscriptProofs.Quantum.DilationBridge

open scoped Matrix Kronecker
namespace ManuscriptProofs.Quantum

variable {d e D : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
  [Fintype D] [DecidableEq D]

/-- The ternary-binary supporting matrix has an invertible system factor.
Cancel it inside the dilation range and extract a full quantum code. -/
theorem noiseless_code_of_invertible_lift_factor
    (V : Matrix (d × e) D ℂ) (hV : Vᴴ * V = 1) (Y : Operator D)
    (K R : Operator d) (hKR : K*R = 1) (hRK : R*K = 1)
    (H : Operator e) (hH : H ≠ 0) (hf : liftToDilation V Y = K ⊗ₖ H) :
    ∃ J : Matrix D d ℂ, Jᴴ * J = 1 ∧
      ∀ X : Operator d, Jᴴ * compress V (X ⊗ₖ (1 : Operator e)) * J = X := by
  let B := (1 : Operator d) ⊗ₖ H
  let P := V * Vᴴ
  have h₁ : (K ⊗ₖ H) * (R ⊗ₖ (1 : Operator e)) = B := by
    rw [← Matrix.mul_kronecker_mul, hKR, mul_one]
  have h₂ : (R ⊗ₖ (1 : Operator e)) * (K ⊗ₖ H) = B := by
    rw [← Matrix.mul_kronecker_mul, hRK, one_mul]
  obtain ⟨_, hl, hr⟩ := lift_compress_support V hV Y
  rw [hf] at hl hr
  have hPB : P * B = B := by
    change (V * Vᴴ) * B = B
    rw [← h₁, ← Matrix.mul_assoc, hl]
  have hBP : B * P = B := by
    change B * (V * Vᴴ) = B
    rw [← h₂, Matrix.mul_assoc, hr]
  apply noiseless_code_of_lift_factorization V hV (compress V B) H hH
  calc
    liftToDilation V (compress V B) = (P * B) * P := by
      simp only [liftToDilation, compress, P, Matrix.mul_assoc]
    _ = B := by rw [hPB, hBP]

end ManuscriptProofs.Quantum
