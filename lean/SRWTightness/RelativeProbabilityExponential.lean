import SRWTightness.CompetingMassComparison
import SRWTightness.ActualMarkEventComparison

namespace SRWTightness

/-- Small relative errors give exponential comparison, including zero reference probability. -/
theorem relative_probability_exponential (p q ε : ℝ) (hq : 0 ≤ q) (hε : 0 ≤ ε)
    (hsmall : ε ≤ 1 / 2) (hp : |p - q| ≤ ε * q) :
    Real.exp (-(2 * ε)) * q ≤ p ∧ p ≤ Real.exp (2 * ε) * q := by
  have hh := half_probability_exponential_bounds ((1 - ε) / 2) (ε / 2)
    (by positivity) (by linarith) (by
      rw [show (1 - ε) / 2 - 1 / 2 = -(ε / 2) by ring, abs_neg,
        abs_of_nonneg (show 0 ≤ ε / 2 by positivity)])
  rw [show 4 * (ε / 2) = 2 * ε by ring] at hh
  have hl : Real.exp (-(2 * ε)) ≤ 1 - ε := by linarith [hh.1]
  have hu : 1 + ε ≤ Real.exp (2 * ε) := by linarith [Real.add_one_le_exp (2 * ε)]
  have hpl := (abs_le.mp hp).1
  have hpu := (abs_le.mp hp).2
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hl hq]
  · nlinarith [mul_le_mul_of_nonneg_right hu hq]

/-- Actual occupation mark events inherit exponential bounds from entrance atom comparison. -/
theorem actual_mark_event_exponential_comparison (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ v ∈ K, |(competingEntranceLaw D K x).real {v} - α * equilibriumMeasure D K v| ≤
      ε * (α * equilibriumMeasure D K v)) (s : Set (Mark K)) (hs : MeasurableSet s) :
    Real.exp (-(2 * ε)) * (referenceMarkLaw D K α).real s ≤ (killedMarkLaw D K x).real s ∧
      (killedMarkLaw D K x).real s ≤ Real.exp (2 * ε) * (referenceMarkLaw D K α).real s :=
  relative_probability_exponential _ _ ε (MeasureTheory.measureReal_nonneg) hε hsmall
    (actual_mark_event_relative_comparison D K x α ε hα hε hcap hu s hs)

end SRWTightness
