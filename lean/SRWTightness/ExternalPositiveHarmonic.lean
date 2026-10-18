import SRWTightness.LatticeTranslation
import SRWTightness.DiskFiniteDomain

namespace SRWTightness

/-- Standard positive-harmonic difference/Harnack estimate used in source (2.13).
The constant is uniform in the function, so tiny harmonic-measure atoms are covered. -/
def PositiveHarmonicRelativeInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (b : Site) (A B : ℝ), 1 ≤ A → 8 * A ≤ B →
    ∀ f : Site → ℝ, (∀ y, 0 ≤ f y) →
    (∀ y ∈ translateFinset b (diskFinset B),
      f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d)) →
    ∀ x ∈ translateFinset b (diskFinset (2 * A)),
      |f x - f b| ≤ C * (A / B) * f b

end SRWTightness
