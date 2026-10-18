import SRWTightness.SourceEarlyCapacityDenominator

open Filter
namespace SRWTightness

/-- The actual short-annulus capacities are uniformly bounded at all early levels. -/
theorem source_early_capacity_bound (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t → ∀ b : Site,
      capacity
        (sourceExitDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
        (sourceEntranceDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) ≤ 2 / (2 / Real.pi) := by
  obtain ⟨D, hD, hc⟩ := source_early_capacity_denominator hinput
  filter_upwards [hc] with t ht
  intro ν hν b
  obtain ⟨d, hd, _, heq⟩ := ht ν hν b
  rw [heq]
  calc
    d⁻¹ = 1 / d := by simp
    _ ≤ 1 / ((2 / Real.pi) / 2) := one_div_le_one_div_of_le (by positivity) hd
    _ = 2 / (2 / Real.pi) := by ring

end SRWTightness
