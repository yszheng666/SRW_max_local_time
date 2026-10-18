import SRWTightness.ExteriorRecordComparison
import SRWTightness.SourceExteriorRecordValues
import SRWTightness.SourceExteriorSlotRecordLaw

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The full actual conditional law of a fixed tagged fine-record tuple is compared with its
product reference weight, with precisely the sum of the local errors. -/
theorem source_exterior_record_product (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      ∀ (a₀ a₁ : ℝ) (K₀ K₁ : Finset Site),
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 → K₀ ⊆ translateFinset b (diskFinset a₀) →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 → K₁ ⊆ translateFinset w (diskFinset a₁) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν,
      (∀ i, sourceExteriorFineCompatible t K₀ K₁ ν (h.1.get i) (r i)) →
      let E := ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i)
      let weight := ∏ i, sourceExteriorFineWeight t b w K₀ K₁ ν J (r i)
      let mass := pathLaw.real {ω |
        (h.1.zip (U ω)).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2) = List.ofFn r ∧
        sourcePairExteriorRecord t b w ν J ω = h} /
          pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}
      Real.exp (-E) * weight ≤ mass ∧ mass ≤ Real.exp E * weight := by
  obtain ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, hslot⟩ :=
    source_exterior_slot_record_law hF hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hslot, source_exterior_geometry] with t ht hg
  intro b w ν J hb hw hbw hd hν hform hJ a₀ a₁ K₀ K₁ ha₀ hc₀ hK₀ ha₁ hc₁ hK₁
  dsimp only
  intro h hh r hr
  obtain ⟨hkb, hkw, hCD, hgapb, hgapw, _⟩ := hg b w ν J hb hw hbw hd hν hform
  have he := exterior_conditional_word_event hF _ _ _ _ _ 0 hkb hkw hCD hgapb hgapw h hh
    {us | (h.1.zip us).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2) = List.ofFn r}
  simp only [Set.mem_setOf_eq] at he
  simp only [sourcePairExteriorRecord]
  rw [he]
  apply exterior_record_product_comparison
  intro i
  dsimp only
  have hs := hr i
  have hp := ht b w ν J hb hw hbw hd hν hform hJ h hh (h.1.get i) (List.get_mem _ _)
  cases hri : r i with
  | inl rs =>
    have hs' : (h.1.get i).2.1 = false ∧ rs ≠ [] := by
      simpa only [hri, sourceExteriorFineCompatible, Sum.elim_inl] using hs
    simp only [hs'.1, Bool.false_eq_true, if_false] at hp
    cases rs with
    | nil => exact False.elim (hs'.2 rfl)
    | cons v vs =>
      have hv := hp a₀ K₀ ha₀ hc₀ hK₀ v vs
      simpa only [killedWordBridgeLaw_record, hri, sourceExteriorFineError,
        sourceExteriorFineWeight, sourceLongFineListWeight, sourceLongFineListError,
        sourceExteriorFineRecord, hs'.1, Bool.false_eq_true, if_false, Sum.elim_inl,
        Sum.inl.injEq, killedChildRecords, Set.mem_setOf_eq, List.length_cons,
        Nat.cast_add, Nat.cast_one, add_assoc] using hv
  | inr rs =>
    have hs' : (h.1.get i).2.1 = true ∧ rs ≠ [] := by
      simpa only [hri, sourceExteriorFineCompatible, Sum.elim_inr] using hs
    simp only [hs'.1, if_true] at hp
    cases rs with
    | nil => exact False.elim (hs'.2 rfl)
    | cons v vs =>
      have hv := hp a₁ K₁ ha₁ hc₁ hK₁ v vs
      simpa only [killedWordBridgeLaw_record, hri, sourceExteriorFineError,
        sourceExteriorFineWeight, sourceLongFineListWeight, sourceLongFineListError,
        sourceExteriorFineRecord, hs'.1, if_true, Sum.elim_inr, Sum.inr.injEq,
        killedChildRecords, Set.mem_setOf_eq, List.length_cons,
        Nat.cast_add, Nat.cast_one, add_assoc] using hv

end SRWTightness
