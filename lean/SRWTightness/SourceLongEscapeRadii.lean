import SRWTightness.SourceExcursionDomains
import SRWTightness.BufferedLongEscapeParameter

namespace SRWTightness

/-- The long source radius spans exactly J+1 exponential steps from the short inner scale. -/
theorem sourceRecordRadius_long (m : ℝ) (ℓ ν J : ℕ) (hJ : J ≤ ν) :
    Real.exp ((J : ℝ) + 1) * sourceRecordRadius m ℓ (ν + 1) =
      sourceRecordRadius m ℓ (ν - J) := by
  have he : ((J : ℝ) + 1) + ((ℓ : ℝ) - ((ν + 1 : ℕ) : ℝ)) =
      (ℓ : ℝ) - ((ν - J : ℕ) : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  unfold sourceRecordRadius
  calc
    _ = m * Real.exp (((J : ℝ) + 1) + ((ℓ : ℝ) - ((ν + 1 : ℕ) : ℝ))) := by
      rw [Real.exp_add ((J : ℝ) + 1) ((ℓ : ℝ) - ((ν + 1 : ℕ) : ℝ))]
      ring
    _ = _ := by rw [he]

/-- The source's geometric root-count parameter, using its actual buffered radii. -/
noncomputable def sourceLongEscapeParameter (m r : ℝ) (ℓ ν J : ℕ) : ℝ :=
  bufferedLongEscapeParameter (sourceRecordRadius m ℓ (ν + 1)) (sourceRecordBuffer r) (J : ℝ)

/-- This parameter is exactly the logarithmic ratio in equation (8.1). -/
theorem sourceLongEscapeParameter_eq (m r : ℝ) (ℓ ν J : ℕ) (hJ : J ≤ ν) :
    sourceLongEscapeParameter m r ℓ ν J =
      Real.log ((sourceRecordRadius m ℓ ν + sourceRecordBuffer r) /
        (sourceRecordRadius m ℓ (ν + 1) - sourceRecordBuffer r)) /
      Real.log ((sourceRecordRadius m ℓ (ν - J) + sourceRecordBuffer r) /
        (sourceRecordRadius m ℓ (ν + 1) - sourceRecordBuffer r)) := by
  unfold sourceLongEscapeParameter bufferedLongEscapeParameter
  rw [sourceRecordRadius_successor, sourceRecordRadius_long m ℓ ν J hJ]

end SRWTightness
