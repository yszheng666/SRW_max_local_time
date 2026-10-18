import SRWTightness.SourceMainInternalReflection
import SRWTightness.LiteraturePositiveHarmonic
import SRWTightness.LiteratureBDZSquareMaximum

open MeasureTheory
namespace SRWTightness

/-- Main claims from literature-shaped external inputs. The harmonic path/scale
conversion and the DGFF model/translation/normalization/height conversion are
proved internally, rather than included in the external premises. -/
theorem source_main_claims_from_literature
    [MeasurableSpace (List WordMark)] [MeasurableSingletonClass (List WordMark)]
    (hP : PotentialKernelAsymptoticInput)
    (hLL : LLPositiveHarmonicDifferenceInput)
    (hGW : GWBarrierUpperInput)
    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hLower : GWBarrierLowerInput)
    (hBDZ : BDZLiteratureDyadicMaximumInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  exact source_main_claims_internal_reflection hP
    (positive_harmonic_relative_of_literature hLL) hGW hBE hLower
    (bdz_dyadic_square_maximum_of_literature hBDZ)

end SRWTightness
