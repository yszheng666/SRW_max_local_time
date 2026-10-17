import SRWTightness.SRWFourierProduct
import SRWTightness.CosineCentralBinomial
import SRWTightness.CentralBinomialWallis

open Filter
open scoped Topology

namespace SRWTightness

/-- Exact return probability for the original, non-lazy planar SRW. -/
theorem transitionProbability_return_even (n : ℕ) :
    transitionProbability (2 * n) 0 = centralBinomialRatio n ^ 2 := by
  rw [transitionProbability_product]
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add, sub_self, cosineMoment_origin_even]
  unfold centralBinomialRatio
  have hp := Real.pi_ne_zero
  field_simp
  <;> ring

theorem transitionProbability_return_odd (n : ℕ) :
    transitionProbability (2 * n + 1) 0 = 0 := by
  rw [transitionProbability_product]
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add, sub_self, cosineMoment_origin_odd, mul_zero]

/-- The sharp leading return constant accounts for the period-two lattice. -/
theorem tendsto_nat_mul_return_even :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * transitionProbability (2 * n) 0) atTop (𝓝 (1 / Real.pi)) := by
  simpa only [transitionProbability_return_even] using tendsto_nat_mul_centralBinomialRatio_sq

end SRWTightness
