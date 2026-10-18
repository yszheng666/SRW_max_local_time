import SRWTightness.BesselFiniteGridHitting
import SRWTightness.BesselContinuity
import SRWTightness.ContinuousHittingFromGrids
import SRWTightness.BesselInitialFromDelayed

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- The complete original delayed hitting input holds for the actual radial process. -/
theorem besselThreeDelayedHittingInput_internal : BesselThreeDelayedHittingInput := by
  intro T x b s hT hx hb hs hsT
  let μ := independentBridgeLaw (Fin 3)
  let I := ∫ ω, (actualBesselThree T x s ω)⁻¹ ∂μ
  have hI : 0 ≤ I := integral_nonneg (fun ω ↦ inv_nonneg.mpr (Real.sqrt_nonneg _))
  have hbound (c : ℝ) (hbc : b < c) :
      μ.real {ω | ∃ t ∈ Set.Icc s T, actualBesselThree T x t ω ≤ b} ≤ c * I := by
    apply continuous_hitting_from_grids μ (fun t ω ↦ actualBesselThree T x t ω)
      (actualBesselThree_ae_continuous T x) s T b c (c * I) hsT hbc
      (mul_nonneg (hb.trans hbc).le hI)
    intro n
    have hN : 0 < (2 : ℕ) ^ n := by positivity
    have hq := stoppedUniformTimeGrid_mono s T (2 ^ n) hsT
    have hmem (j : ℕ) := stoppedUniformTimeGrid_mem s T (2 ^ n) j hsT hN
    have hh := bessel_finite_grid_hitting T x c hT hx (hb.trans hbc)
      (stoppedUniformTimeGrid s T (2 ^ n)) hq
      (fun j ↦ hs.trans_le (hmem j).1) (fun j ↦ (hmem j).2) (2 ^ n)
    simpa only [stoppedUniformTimeGrid_zero] using hh
  have hlim : Tendsto (fun n : ℕ ↦ (b + 1 / ((n : ℝ) + 1)) * I) atTop
      (nhds (b * I)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
  exact ge_of_tendsto hlim (Eventually.of_forall (fun n ↦
    hbound (b + 1 / ((n : ℝ) + 1)) (by
      have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith)))

/-- The complete original initial hitting input is now internally proved as well. -/
theorem besselThreeHittingInput_internal : BesselThreeHittingInput :=
  besselThreeHittingInput_of_delayed besselThreeDelayedHittingInput_internal

end SRWTightness
