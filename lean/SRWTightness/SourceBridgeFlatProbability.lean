import SRWTightness.ExternalBridgeReflection
import SRWTightness.SourceBridgeParameters
import SRWTightness.BridgeExponentialBounds

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Explicit two-sided version of source (7.14), conditional only on standard reflection. -/
theorem sourceBridge_flat_probability_bounds (hReflection : BridgeReflectionInput)
    (d H q b : ℝ) (hH : 1 ≤ H) (hd : 256 * H ≤ d)
    (hq : q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d))
    (hb : b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H)) :
    q * Real.sqrt H / d ≤ gaussianCoefficientLaw.real (bridgeFlatEvent (d - H) b q) ∧
      gaussianCoefficientLaw.real (bridgeFlatEvent (d - H) b q) ≤ 8 * q * Real.sqrt H / d := by
  have ha := sourceBridge_endpoint_distance H q b hb
  have hp := sourceBridge_parameter_bounds d H q (q - b) hH hd ha hq
  have hT : 0 < d - H := hp.1
  have hH0 : 0 < H := by linarith
  have hd0 : 0 < d := by linarith
  have hq0 : 0 < q := (Real.sqrt_pos.mpr hd0).trans_le hq.1
  have ha0 : 0 < q - b := (Real.sqrt_pos.mpr hH0).trans_le ha.1
  have hroot : 1 ≤ Real.sqrt H := by simpa using Real.sqrt_le_sqrt hH
  have haU : q - b ≤ 2 * Real.sqrt H := by linarith [ha.2]
  have hz0 : 0 ≤ 2 * q * (q - b) / (d - H) := by positivity
  have hz1 : 2 * q * (q - b) / (d - H) ≤ 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hp.2.2.2.1
  rw [hReflection (d - H) b q hp.1 hq0 (by linarith)]
  have hf := bridge_reflection_factor_bounds _ hz0 hz1
  constructor
  · apply le_trans _ hf.1
    calc
      _ ≤ q * (q - b) / d :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ha.1 hq0.le) hd0.le
      _ ≤ q * (q - b) / (d - H) :=
        div_le_div_of_nonneg_left (by positivity) hp.1 (by linarith)
      _ = _ := by ring
  · apply hf.2.trans
    calc
      _ ≤ 4 * q * Real.sqrt H / (d - H) := by
        apply div_le_div_of_nonneg_right _ hp.1.le
        nlinarith [mul_le_mul_of_nonneg_left haU (by positivity : 0 ≤ 2 * q)]
      _ ≤ 4 * q * Real.sqrt H / (d / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = _ := by ring

end SRWTightness
