import SRWTightness.ContinuationDecay

namespace SRWTightness

/-- Exact conversion from logarithmic radius to the source inverse-square radius factor. -/
theorem continuation_radius_decay_identity (t ν x : ℝ) :
    Real.exp (-2 * t - 2 * ν + 2 * x) =
      Real.exp (-2 * ν + 2 * x) / (Real.exp t) ^ 2 := by
  rw [show -2 * t - 2 * ν + 2 * x = -(t + t) + (-2 * ν + 2 * x) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_add]
  ring

end SRWTightness
