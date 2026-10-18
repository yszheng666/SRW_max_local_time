import SRWTightness.PairTiltMean
import Mathlib.Tactic.Linarith

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem pair_tilt_site_mean_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G S : Ω → ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hS : MemLp S 2 μ)
    (d v Cz Cc : ℝ) (hFS : covariance F S μ = v)
    (hvar : |covariance F F μ - d| ≤ Cz) (hcross : |covariance F G μ - v| ≤ Cc) :
    |covariance F ((2 : ℝ) • (F + G - S)) μ - 2 * d| ≤ 2 * Cz + 2 * Cc := by
  rw [pair_tilt_coordinate_covariance μ F F G S hF hF hG hS, hFS]
  obtain ⟨hv1, hv2⟩ := abs_le.mp hvar
  obtain ⟨hc1, hc2⟩ := abs_le.mp hcross
  apply abs_le.mpr
  constructor <;> linarith

/-- The last average has the positive twice-discrete-error mean correction. -/
theorem pair_tilt_last_average_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (F G S : Ω → ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hS : MemLp S 2 μ)
    (v e : ℝ) (hFS : covariance F S μ = v) (hGS : covariance G S μ = v)
    (hSS : covariance S S μ = v - e) :
    covariance S ((2 : ℝ) • (F + G - S)) μ = 2 * v + 2 * e := by
  rw [pair_tilt_coordinate_covariance μ S F G S hS hF hG hS,
    covariance_comm S F, covariance_comm S G, hFS, hGS, hSS]
  ring

/-- Strictly outer averages have exactly the Brownian drift under the leading tilt. -/
theorem pair_tilt_outer_average_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Y F G S : Ω → ℝ)
    (hY : MemLp Y 2 μ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (hS : MemLp S 2 μ)
    (v : ℝ) (hYF : covariance Y F μ = v) (hYG : covariance Y G μ = v)
    (hYS : covariance Y S μ = v) :
    covariance Y ((2 : ℝ) • (F + G - S)) μ = 2 * v := by
  rw [pair_tilt_coordinate_covariance μ Y F G S hY hF hG hS, hYF, hYG, hYS]
  ring

end SRWTightness
