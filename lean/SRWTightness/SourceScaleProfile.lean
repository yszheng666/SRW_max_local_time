import SRWTightness.SourceScaleEstimates
import SRWTightness.SourceScaleThreshold

namespace SRWTightness

/-- Exact source profile (5.1), maximal scale (5.7), and all four estimates (5.9).
The constants are independent of t, the scale index, and the lattice center. -/
theorem source_scale_profile (b : Site) (t A q : ℝ) (hA : 4 ≤ A) (hq : 1 < q)
    (ht : sourceScaleThreshold A ≤ t) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * q ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) ∧
      (∀ i ≤ I,
        |sourceEquilibriumTime b (sourceLowerRadius t) (A * q ^ i) 14 -
          (sourceLowerTime (sourceLowerRadius t) - Real.log (A * q ^ i))| ≤
            sourceEquilibriumTimeError + sourceLowerTimeError ∧
        sourceDiscreteError b (sourceLowerRadius t) (A * q ^ i) 14 ≤
          (diskEquilibriumWeightConstant / (2 * (2 / Real.pi))) / (A * q ^ i)) ∧
      |sourceEquilibriumTime b (sourceLowerRadius t) (A * q ^ I) 14 - 6 * Real.log t| ≤
        sourceEquilibriumTimeError + Real.log q ∧
      (I : ℝ) ≤ ((1 + sourceLowerTimeError) / Real.log q) * sourceLowerTime (sourceLowerRadius t) := by
  obtain ⟨ht2, hcut, hm70, hd⟩ := sourceScaleThreshold_conditions t A hA ht
  have hA0 : 0 < A := by linarith
  let I := geometricTerminalIndex A q (sourceLowerRadius t / t ^ 6) hA0 hq hcut
  have hs := source_scale_estimates b (sourceLowerRadius t) t A q 14 (by linarith)
    ht2 hA hq hcut (by norm_num) (by linarith) hd
  exact ⟨I, geometricTerminalIndex_max_iff A q _ hA0 hq hcut, hs⟩

/-- The original t=log(R) formulation, with an explicit sufficiently-large log-radius threshold. -/
theorem source_scale_profile_at_radius (b : Site) (R A q : ℝ) (hA : 4 ≤ A) (hq : 1 < q)
    (hR : sourceScaleThreshold A ≤ Real.log R) :
    ∃ I : ℕ,
      (∀ i : ℕ, A * q ^ i ≤ sourceLowerRadius (Real.log R) / (Real.log R) ^ 6 ↔ i ≤ I) ∧
      (∀ i ≤ I,
        |sourceEquilibriumTime b (sourceLowerRadius (Real.log R)) (A * q ^ i) 14 -
          (sourceLowerTime (sourceLowerRadius (Real.log R)) - Real.log (A * q ^ i))| ≤
            sourceEquilibriumTimeError + sourceLowerTimeError ∧
        sourceDiscreteError b (sourceLowerRadius (Real.log R)) (A * q ^ i) 14 ≤
          (diskEquilibriumWeightConstant / (2 * (2 / Real.pi))) / (A * q ^ i)) ∧
      |sourceEquilibriumTime b (sourceLowerRadius (Real.log R)) (A * q ^ I) 14 -
        6 * Real.log (Real.log R)| ≤ sourceEquilibriumTimeError + Real.log q ∧
      (I : ℝ) ≤ ((1 + sourceLowerTimeError) / Real.log q) *
        sourceLowerTime (sourceLowerRadius (Real.log R)) :=
  source_scale_profile b (Real.log R) A q hA hq hR

end SRWTightness
