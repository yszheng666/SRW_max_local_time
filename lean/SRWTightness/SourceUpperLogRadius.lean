import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
namespace SRWTightness

/-- The upper-bound logarithmic terminal radius D_+=(8 log t)^4. -/
noncomputable def sourceUpperLogRadius (t : ℝ) : ℝ := (8 * Real.log t) ^ 4

/-- The exact manuscript radius parameter eventually exceeds every fixed terminal threshold. -/
theorem sourceUpperLogRadius_tendsto : Tendsto sourceUpperLogRadius atTop atTop := by
  exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
    (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 8))

theorem sourceUpperLogRadius_eventually (u₀ : ℝ) :
    ∀ᶠ t : ℝ in atTop, u₀ ≤ sourceUpperLogRadius t :=
  sourceUpperLogRadius_tendsto.eventually (eventually_ge_atTop u₀)

end SRWTightness
