import SRWTightness.SourceCommonLiteralChernoff
import SRWTightness.FiniteResolventRowInternal

open MeasureTheory Filter

namespace SRWTightness

/-- The literal common-mark Chernoff estimate with the finite resolvent bound proved internally. -/
theorem source_common_literal_chernoff_internal_resolvent
    (hOcc : FiniteOccupationRowIntegrabilityInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      (j : ℤ) = sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ W : ℝ, 0 < W → (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1 →
      ∀ (u : ℝ) (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      let K := sourceCommonPairObservation b w
      (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
        {Y | ∀ v : K, ((v : Site) = b ∨ (v : Site) = w) →
          sourceTerminalVisitCutoff t ≤ sumMarks K k Y v} ≤
        Real.exp (-(2 / Real.pi) * sourceTerminalHeight t ^ 2 * Real.log (1 + W) +
          sourceCommonPairIntensity t j * u ^ 2 * W /
            (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W)) := by
  exact source_common_literal_chernoff hOcc finite_resolvent_row_bound_input_internal

end SRWTightness
