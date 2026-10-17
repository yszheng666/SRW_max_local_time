import SRWTightness.LogPowerDomination
import Mathlib.Analysis.PSeries

open Filter
namespace SRWTightness

/-- Positive stretched-exponential sequences are summable by comparison with the square p-series. -/
theorem stretched_exponential_summable (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) :
    Summable (fun n : ℕ ↦ Real.exp (-c * (n : ℝ) ^ γ)) := by
  have hp : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply hp.of_norm_bounded_eventually_nat
  have hh : ∀ᶠ n : ℕ in atTop, 2 * Real.log (n : ℝ) + 0 ≤ c * (n : ℝ) ^ γ :=
    tendsto_natCast_atTop_atTop.eventually (affine_log_eventually_le_rpow 2 0 c γ hc hγ)
  filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.rpow_def_of_pos hnpos (-2)]
  exact Real.exp_le_exp.mpr (by linarith only [hn])

end SRWTightness
