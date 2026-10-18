import SRWTightness.SourceConditionalTupleAuxiliary
import SRWTightness.OrderedTaggedForestMixture
import SRWTightness.PositiveAtomSupport

open MeasureTheory Filter
namespace SRWTightness

/-- On a positive exterior fiber the actual fixed tuple has the prescribed labels and reconstructs
both ordered grouped forests, almost surely under the original walk law. -/
theorem source_fine_tuple_support (hExt : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (h : ExteriorPathRecord),
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h →
        orderedTaggedCompatible (fun i ↦ (h.1.get i).2.1)
          (sourceFineTuple t b w K₀ K₁ ν J h ω) ∧
        orderedTaggedForests (sourceFineTuple t b w K₀ K₁ ν J h ω) =
          (sourceGroupedFineForest t b w b K₀ ν J ω,
            sourceGroupedFineForest t b w w K₁ ν J ω) := by
  filter_upwards [source_exterior_tagged_forests hExt] with t hsupp
  intro b w ν J hb hw hbw hd hν hform K₀ K₁ h hh
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    0 (fun _ u ↦ u)
  let Z := sourcePairExteriorRecord t b w ν J
  have hpos := ae_support_of_positive_atoms pathLaw (fun ω ↦ (U ω, Z ω))
    (fun r ↦ 0 < pathLaw.real {ω | (U ω, Z ω) = r}) (fun _ hr ↦ hr)
  filter_upwards [hpos] with ω hp
  intro hω
  change Z ω = h at hω
  have hlen : (U ω).length = h.1.length := by
    have he := killedExteriorRecord_length (diskFinset (Real.exp t)) (K b ∪ K w)
      (C b ∪ C w) (twoDomainExteriorLabel (K w)) 0 ω
    change (Z ω).1.length = (U ω).length at he
    rw [hω] at he
    exact he.symm
  have hp' : 0 < pathLaw.real {ω' | U ω' = U ω ∧ Z ω' = h} := by
    simpa only [Prod.mk.injEq, hω] using hp
  have hs := hsupp b w ν J hb hw hbw hd hν hform K₀ K₁ h (U ω) hlen hh hp'
  have he := exterior_fixed_tuple_list h (sourceExteriorFineRecord t b w K₀ K₁ ν)
    (U ω) hlen
  constructor
  · intro i
    have hpair := exterior_fixed_tuple_list h (fun y u ↦ (y, u)) (U ω) hlen
    have hi : (h.1.get i, (U ω).getD i.val ⟨0, Fin.elim0⟩) ∈ h.1.zip (U ω) := by
      have hm : (h.1.get i, (U ω).getD i.val ⟨0, Fin.elim0⟩) ∈
          List.ofFn (exteriorFixedTuple h (fun y u ↦ (y, u)) (U ω)) :=
        List.mem_ofFn.mpr ⟨i, rfl⟩
      simpa only [hpair, Prod.mk.eta, List.map_id'] using hm
    exact hs.1 _ hi
  · change (taggedForestLeft (List.ofFn (exteriorFixedTuple h
        (sourceExteriorFineRecord t b w K₀ K₁ ν) (U ω))),
      taggedForestRight (List.ofFn (exteriorFixedTuple h
        (sourceExteriorFineRecord t b w K₀ K₁ ν) (U ω)))) = _
    rw [he]
    exact Prod.ext (hs.2 ω hω rfl).1 (hs.2 ω hω rfl).2

end SRWTightness
