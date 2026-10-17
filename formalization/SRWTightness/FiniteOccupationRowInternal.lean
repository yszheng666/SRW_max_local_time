import SRWTightness.ObservationPositiveHarmonic
import SRWTightness.FiniteHorizonOccupation

namespace SRWTightness

/-- The full finite occupation row-contraction integrability input holds for the actual walk. -/
theorem finite_occupation_row_integrability_input_internal :
    FiniteOccupationRowIntegrabilityInput := by
  intro D A hAD v hv hrow x
  obtain ⟨F, hF, hhar⟩ := observation_positive_harmonic D A hAD v hv hrow
  exact integrable_monomial_of_positive_harmonic D A v
    (fun z ↦ zero_le_one.trans (hv z)) F hF hhar x

end SRWTightness
