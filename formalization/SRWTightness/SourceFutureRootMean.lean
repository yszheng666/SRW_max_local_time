import SRWTightness.KilledWordPairMean
import SRWTightness.SourceCommonReferenceWord

open MeasureTheory
namespace SRWTightness

/-- The subsequent two-label root count started at x and killed at the common boundary. -/
noncomputable def sourceFutureRootMean (t : ℝ) (b w x : Site) (j ν : ℕ) : ℝ :=
  ∫ Y, ((sourceCommonWordRootCount t b ν Y +
    sourceCommonWordRootCount t w ν Y : ℕ) : ℝ)
    ∂killedWordMarkLaw (sourceCommonPairDomain t b j) x

/-- Actual subsequent counts reduce to two Green-capacity sums in the common killing domain. -/
theorem sourceFutureRootMean_eq (hLast : FiniteLastVisitCountInput)
    (t : ℝ) (b w x : Site) (j ν : ℕ)
    (hgeometry : ∀ z ∈ ({b, w} : Finset Site),
      sourceEntranceDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν ⊆
      sourceExitDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν ∧
      sourceExitDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν ⊆
      sourceCommonPairDomain t b j) :
    let m := sourceLowerRadius t
    let ℓ := sourceRootDepth (Real.exp t) m
    sourceFutureRootMean t b w x j ν =
      (∑ y ∈ sourceEntranceDomain m 1 ℓ b ν,
        killedGreen (sourceCommonPairDomain t b j) x y *
          equilibriumMeasure (sourceExitDomain m 1 ℓ b ν)
            (sourceEntranceDomain m 1 ℓ b ν) y) +
      ∑ y ∈ sourceEntranceDomain m 1 ℓ w ν,
        killedGreen (sourceCommonPairDomain t b j) x y *
          equilibriumMeasure (sourceExitDomain m 1 ℓ w ν)
            (sourceEntranceDomain m 1 ℓ w ν) y := by
  have hb := hgeometry b (by simp)
  have hw := hgeometry w (by simp)
  exact integral_killedWordMark_pair_roots hLast _ _ _ _ _ hb.1 hw.1 hb.2 hw.2 x

end SRWTightness
