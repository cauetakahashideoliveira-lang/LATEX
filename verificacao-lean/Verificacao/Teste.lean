import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Linarith

/-! Teste do ambiente: dois fatos do documento `teste-configuracao`. -/

/-- Série de Basel: ∑ 1/n² = π²/6 (o termo n = 0 vale 0 em ℝ, pois 1/0 = 0). -/
example : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two

/-- Desigualdade testada também com o Z3. -/
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]
