import SRWTightness.PotentialKernelSeries

namespace SRWTightness

/-- The minimal large-distance consequence of Lawler--Limic Theorem 4.4.4 used for annuli. -/
def PotentialKernelAsymptoticInput : Prop :=
  ∃ κ C R₀ : ℝ, 0 ≤ C ∧ 1 ≤ R₀ ∧ ∀ z : Site,
    R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤
        C / normSq z

end SRWTightness
