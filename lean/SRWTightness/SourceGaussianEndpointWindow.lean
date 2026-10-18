import SRWTightness.ExternalGaussianWindow
import SRWTightness.SourceBridgeParameters

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Standard Gaussian density bounds on intervals whose standardized endpoints stay bounded. -/
def GaussianIntervalInput : Prop :=
  ∀ R : ℝ, 0 ≤ R → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ v l u : ℝ, 0 < v → l ≤ u →
      |l| ≤ R * Real.sqrt v → |u| ≤ R * Real.sqrt v →
      c * (u - l) / Real.sqrt v ≤ (gaussianReal 0 v.toNNReal).real (Set.Icc l u) ∧
      (gaussianReal 0 v.toNNReal).real (Set.Icc l u) ≤ C * (u - l) / Real.sqrt v

/-- Source endpoint windows have bounded standardized endpoints. -/
theorem source_endpoint_window_standardized (d H q : ℝ) (hH : 1 ≤ H)
    (hd : 256 * H ≤ d) (hq : q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d)) :
    0 < d - H ∧ Real.sqrt (d - H) ≤ Real.sqrt d ∧
      Real.sqrt d ≤ 2 * Real.sqrt (d - H) ∧
      |q - Real.sqrt H - 1| ≤ 6 * Real.sqrt (d - H) ∧
      |q - Real.sqrt H| ≤ 6 * Real.sqrt (d - H) := by
  have hT : 0 < d - H := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hH0 : 0 ≤ H := by linarith
  have ht1 : 1 ≤ Real.sqrt (d - H) := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ d - H by linarith)
  have hroot : Real.sqrt d ≤ 2 * Real.sqrt (d - H) := by
    nlinarith [Real.sq_sqrt hd0, Real.sq_sqrt hT.le, Real.sqrt_nonneg d]
  have hHT : Real.sqrt H ≤ Real.sqrt (d - H) :=
    Real.sqrt_le_sqrt (by linarith)
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg d).trans hq.1
  refine ⟨hT, Real.sqrt_le_sqrt (by linarith), hroot, ?_, ?_⟩
  · rw [abs_le]
    constructor <;> linarith [hq.2, Real.sqrt_nonneg H]
  · rw [abs_le]
    constructor <;> linarith [hq.2, Real.sqrt_nonneg H]

/-- The source terminal-average endpoint window has probability comparable to d^(-1/2). -/
theorem source_endpoint_window_probability (hGaussian : GaussianIntervalInput) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ d H q : ℝ,
      1 ≤ H → 256 * H ≤ d → q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      c / Real.sqrt d ≤ (gaussianReal 0 (d - H).toNNReal).real
        (Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H)) ∧
      (gaussianReal 0 (d - H).toNNReal).real
        (Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H)) ≤ C / Real.sqrt d := by
  obtain ⟨c, C, hc, hC, hg⟩ := hGaussian 6 (by norm_num)
  refine ⟨c, 2 * C, hc, by positivity, ?_⟩
  intro d H q hH hd hq
  obtain ⟨hT, hTd, hdT, hl, hu⟩ := source_endpoint_window_standardized d H q hH hd hq
  have hh := hg (d - H) (q - Real.sqrt H - 1) (q - Real.sqrt H)
    hT (by linarith) hl hu
  have he : q - Real.sqrt H - (q - Real.sqrt H - 1) = 1 := by ring
  rw [he, mul_one, mul_one] at hh
  have hrt : 0 < Real.sqrt (d - H) := Real.sqrt_pos.mpr hT
  have hrd : 0 < Real.sqrt d := hrt.trans_le hTd
  constructor
  · exact (div_le_div_of_nonneg_left hc.le hrt hTd).trans hh.1
  · apply hh.2.trans
    apply (div_le_div_iff₀ hrt hrd).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdT hC.le]

end SRWTightness
