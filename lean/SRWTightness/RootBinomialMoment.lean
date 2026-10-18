import SRWTightness.WordCompletionSites
import SRWTightness.RecordExitSlice
import Mathlib.Data.Nat.Choose.Basic

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- Nonnegative factorial moments are allowed to be infinite until a bound is proved. -/
noncomputable def rootBinomialMoment (μ : Measure WordMark)
    (L₁ C₁ L₂ C₂ : Finset Site) (p : ℕ) : ℝ≥0∞ :=
  ∫⁻ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y).choose p : ℝ≥0∞) ∂μ

noncomputable def killedRootBinomialMoment (D L₁ C₁ L₂ C₂ : Finset Site)
    (x : Site) (p : ℕ) : ℝ≥0∞ :=
  rootBinomialMoment (killedWordMarkLaw D x) L₁ C₁ L₂ C₂ p

/-- The relevant restart states are actual exits of either short domain. -/
def rootCompletionSet (C₁ C₂ : Finset Site) : Set Site :=
  domainExitBoundary C₁ ∪ domainExitBoundary C₂

theorem rootBinomialMoment_zero (μ : Measure WordMark) [IsProbabilityMeasure μ]
    (L₁ C₁ L₂ C₂ : Finset Site) : rootBinomialMoment μ L₁ C₁ L₂ C₂ 0 = 1 := by
  simp [rootBinomialMoment]

theorem killedRootBinomialMoment_zero (D L₁ C₁ L₂ C₂ : Finset Site) (x : Site) :
    killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 0 = 1 :=
  rootBinomialMoment_zero _ _ _ _ _

theorem rootBinomialMoment_one (μ : Measure WordMark) (L₁ C₁ L₂ C₂ : Finset Site) :
    rootBinomialMoment μ L₁ C₁ L₂ C₂ 1 =
      ∫⁻ Y, ((wordMarkRootCount L₁ C₁ Y + wordMarkRootCount L₂ C₂ Y : ℕ) : ℝ≥0∞) ∂μ := by
  simp [rootBinomialMoment]

end SRWTightness
