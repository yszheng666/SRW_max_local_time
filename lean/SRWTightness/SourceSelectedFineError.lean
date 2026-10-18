import SRWTightness.SourceFineErrorNonnegative
import SRWTightness.SelectedSegmentError
import SRWTightness.SourceDecouplingError

namespace SRWTightness

/-- Local comparison costs selected by the actual entrance label of each long segment. -/
noncomputable def sourceSelectedFineError (A C B W t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (ω : Sample) : ℝ :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let F₀ := fun y u ↦ wordChildRecords (K b) (sourceExitDomain m 1 ℓ b ν) y
    (sourceLongFineRecord t b K₀ ν) u
  let F₁ := fun y u ↦ wordChildRecords (K w) (sourceExitDomain m 1 ℓ w ν) y
    (sourceLongFineRecord t w K₁ ν) u
  (killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w) 0
    (fun y u ↦ A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14) *
        (if twoDomainExteriorLabel (K w) y then ((F₁ y u).length : ℝ) else ((F₀ y u).length : ℝ)) +
      (if twoDomainExteriorLabel (K w) y then ((F₁ y u).map (sourceLongFineError B W t a₁ K₁ ν)).sum
       else ((F₀ y u).map (sourceLongFineError B W t a₀ K₀ ν)).sum)) ω).sum

/-- The selected costs are dominated pointwise by the complete two-site grouped forests. -/
theorem source_selected_fine_error_bound (A C B W t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (ω : Sample)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hW : 0 ≤ W) (ht : 1 ≤ t)
    (ha₀ : 1 ≤ a₀) (hc₀ : a₀ ≤ sourceLowerRadius t / t ^ 6)
    (ha₁ : 1 ≤ a₁) (hc₁ : a₁ ≤ sourceLowerRadius t / t ^ 6)
    (hrad : 14 ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1)) :
    sourceSelectedFineError A C B W t a₀ a₁ b w K₀ K₁ ν J ω ≤
      A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) * (sourceLongSegmentCount t b w ν J ω : ℝ) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14) *
        (((sourceGroupedFineForest t b w b K₀ ν J ω).length : ℝ) +
          ((sourceGroupedFineForest t b w w K₁ ν J ω).length : ℝ)) +
      ((sourceGroupedFineForest t b w b K₀ ν J ω).map (sourceLongFineError B W t a₀ K₀ ν)).sum +
      ((sourceGroupedFineForest t b w w K₁ ν J ω).map (sourceLongFineError B W t a₁ K₁ ν)).sum := by
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let xs := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w) 0
    (fun y u ↦ (y, u)) ω
  let F₀ := fun p : Site × PathWord ↦ wordChildRecords (K b) (sourceExitDomain m 1 ℓ b ν) p.1
    (sourceLongFineRecord t b K₀ ν) p.2
  let F₁ := fun p : Site × PathWord ↦ wordChildRecords (K w) (sourceExitDomain m 1 ℓ w ν) p.1
    (sourceLongFineRecord t w K₁ ν) p.2
  have h := selected_forest_error_bound xs (fun p ↦ twoDomainExteriorLabel (K w) p.1)
    (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)))
    (C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14)) F₀ F₁
    (sourceLongFineError B W t a₀ K₀ ν) (sourceLongFineError B W t a₁ K₁ ν)
    (div_nonneg (by positivity) (sub_nonneg.mpr hrad))
    (source_long_fine_error_nonneg B W t a₀ hB hW ht ha₀ hc₀ K₀ ν)
    (source_long_fine_error_nonneg B W t a₁ hB hW ht ha₁ hc₁ K₁ ν)
  simpa only [xs, F₀, F₁, sourceSelectedFineError, sourceGroupedFineForest,
    sourceLongSegmentCount, sourcePairExteriorRecord, killedExteriorRecord, wordExteriorRecord,
    packExteriorRecord_length, killedChildRecords, wordChildRecords, List.flatMap_def,
    List.map_map, Function.comp_def, List.length_map, m, ℓ, K, D] using h

end SRWTightness
