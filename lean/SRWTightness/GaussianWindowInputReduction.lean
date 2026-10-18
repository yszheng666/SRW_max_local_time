import SRWTightness.SourceGaussianEndpointWindow

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- One standardized Gaussian interval input also supplies compact unit-window positivity. -/
theorem gaussianIntervalInput_unitWindow (hGaussian : GaussianIntervalInput) :
    GaussianUnitWindowInput := by
  intro L U vmin vmax hLU hvmin hvmax
  let B := |L| + |U| + 1
  let R := B / Real.sqrt vmin
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrmin : 0 < Real.sqrt vmin := Real.sqrt_pos.mpr hvmin
  have hrmax : 0 < Real.sqrt vmax := Real.sqrt_pos.mpr (hvmin.trans_le hvmax)
  have hR : 0 ≤ R := div_nonneg hB hrmin.le
  obtain ⟨c, C, hc, hC, hg⟩ := hGaussian R hR
  refine ⟨c / Real.sqrt vmax, by positivity, ?_⟩
  intro z v hz hv
  have hroot : Real.sqrt vmin ≤ Real.sqrt v := Real.sqrt_le_sqrt hv.1
  have hrootU : Real.sqrt v ≤ Real.sqrt vmax := Real.sqrt_le_sqrt hv.2
  have he : R * Real.sqrt vmin = B := by
    dsimp [R]
    exact div_mul_cancel₀ B hrmin.ne'
  have hBr : B ≤ R * Real.sqrt v := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left hroot hR
  have hzL : |z| ≤ B := by
    rw [abs_le]
    dsimp [B]
    constructor <;> linarith [hz.1, hz.2, neg_abs_le L, le_abs_self U,
      abs_nonneg L, abs_nonneg U]
  have hzU : |z + 1| ≤ B := by
    rw [abs_le]
    dsimp [B]
    constructor <;> linarith [hz.1, hz.2, neg_abs_le L, le_abs_self U,
      abs_nonneg L, abs_nonneg U]
  have hb := (hg v z (z + 1) (hvmin.trans_le hv.1) (by linarith)
    (hzL.trans hBr) (hzU.trans hBr)).1
  have hd : z + 1 - z = 1 := by ring
  rw [hd, mul_one] at hb
  exact (div_le_div_of_nonneg_left hc.le (hrmin.trans_le hroot) hrootU).trans hb

end SRWTightness
