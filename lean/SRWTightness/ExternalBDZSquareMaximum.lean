import SRWTightness.LatticeSquare
import SRWTightness.GaussianField

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- BDZ Lemma 3.8 (39), packaged with translation, normalization and closed thresholds. -/
def BDZDyadicSquareMaximumInput : Prop :=
  ∃ P c : ℝ, 0 < P ∧ 0 < c ∧ ∀ (a : Site) (n : ℕ), 2 ≤ n →
    ∀ u : ℝ, 1 ≤ u →
      (gaussianGreenLaw (latticeSquareInterior a (2 ^ n))
        (latticeSquareInterior a (2 ^ n))).real
        {φ | ∃ x : latticeSquareInterior a (2 ^ n),
          2 * Real.log ((2 : ℝ) ^ n) -
            (3 / 4 : ℝ) * Real.log (Real.log ((2 : ℝ) ^ n)) + u ≤
              φ x / Real.sqrt (2 / Real.pi)} ≤
        P * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / Real.log ((2 : ℝ) ^ n))

end SRWTightness
