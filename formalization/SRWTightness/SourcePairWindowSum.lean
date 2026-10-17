import SRWTightness.SourcePairUpperEvent
import SRWTightness.PairWindowGeometricSum
import SRWTightness.CountableCoverRealBound

open MeasureTheory

namespace SRWTightness

/-- Summing the three unit-window weights controls the unsplit source pair event. -/
theorem source_pair_window_sum (t A : ℝ) (I i : ℕ) (At q f r W : ℝ)
    (μ : Measure ((PairObservationIndex (I - i + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    [IsFiniteMeasure μ] (hf : 0 ≤ f) (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W)
    (hbound : ∀ n m l : ℕ, μ.real (sourcePairWindowEvent t A I i At q f n m l) ≤
      W * (r ^ n * (r ^ m * (r ^ l * (f + l + 1))))) :
    μ.real (sourcePairUpperEvent t A I i At q f) ≤ W * ((f + 1) / (1 - r) ^ 4) := by
  have hg := pair_window_geometric_sum r f hr0 hr1 hf
  have hh := countable_cover_real_bound μ (sourcePairUpperEvent t A I i At q f)
    (fun p : ℕ × ℕ × ℕ ↦ sourcePairWindowEvent t A I i At q f p.1 p.2.1 p.2.2)
    (fun p : ℕ × ℕ × ℕ ↦ W * (r ^ p.1 * (r ^ p.2.1 * (r ^ p.2.2 * (f + p.2.2 + 1)))))
    (sourcePairUpperEvent_window_cover t A I i At q f)
    (fun p ↦ by positivity) (hg.1.mul_left W) (fun p ↦ hbound p.1 p.2.1 p.2.2)
  rw [tsum_mul_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hg.2 hW)

end SRWTightness
