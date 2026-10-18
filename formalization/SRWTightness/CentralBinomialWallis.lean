import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Central

open Filter
open scoped Topology

namespace SRWTightness

noncomputable def centralBinomialRatio (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ) / 4 ^ n

theorem centralBinomialRatio_succ (n : ℕ) :
    centralBinomialRatio (n + 1) = (2 * (n : ℝ) + 1) / (2 * n + 2) * centralBinomialRatio n := by
  have hb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  unfold centralBinomialRatio
  rw [pow_succ]
  have hn : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  have hp : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  nlinarith [hb]

theorem centralBinomialRatio_wallis (n : ℕ) :
    Real.Wallis.W n * ((2 * (n : ℝ) + 1) * centralBinomialRatio n ^ 2) = 1 := by
  induction n with
  | zero => simp [Real.Wallis.W, centralBinomialRatio]
  | succ n ih =>
    rw [Real.Wallis.W_succ, centralBinomialRatio_succ]
    push_cast
    calc
      _ = Real.Wallis.W n * ((2 * (n : ℝ) + 1) * centralBinomialRatio n ^ 2) := by
        have h1 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
        have h2 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
        have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
        field_simp
        <;> ring
      _ = 1 := ih

theorem centralBinomialRatio_sq (n : ℕ) :
    centralBinomialRatio n ^ 2 = 1 / ((2 * (n : ℝ) + 1) * Real.Wallis.W n) := by
  have hp : (2 * (n : ℝ) + 1) * Real.Wallis.W n ≠ 0 :=
    (mul_pos (by positivity) (Real.Wallis.W_pos n)).ne'
  apply (eq_div_iff hp).2
  nlinarith [centralBinomialRatio_wallis n]

theorem tendsto_nat_mul_centralBinomialRatio_sq :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * centralBinomialRatio n ^ 2) atTop (𝓝 (1 / Real.pi)) := by
  have h := Stirling.tendsto_self_div_two_mul_self_add_one.div Real.Wallis.tendsto_W_nhds_pi_div_two
    (by positivity : Real.pi / 2 ≠ 0)
  convert h using 1
  · ext n
    rw [centralBinomialRatio_sq]
    dsimp only [Pi.div_apply]
    simp only [div_div, mul_one_div]
  · congr 1
    field_simp

end SRWTightness
