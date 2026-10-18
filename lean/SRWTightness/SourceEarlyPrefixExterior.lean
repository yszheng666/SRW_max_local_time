import SRWTightness.SourcePrefixCountRepresentation
import SRWTightness.SourceEarlyPrefixEvent
import SRWTightness.SourceEarlyPrefixContainment
import SRWTightness.SourceOriginalJointRootBound

open Filter
namespace SRWTightness

/-- Equation 8.9: the original prefix event is a literal preimage of the actual exterior record,
so it is measurable in the exterior sigma algebra, without null-set completion or root independence. -/
theorem source_early_prefix_exterior (hF : ExteriorNestedCountInvarianceInput)
    (J₀ : ℕ) (hJ₀ : 3 ≤ J₀) :
    ∃ a₀ : ℕ, ∀ᶠ t : ℝ in atTop, ∀ b w : Site,
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let Z := sourcePairExteriorRecord t b w ν J
      (∃ G : Set ExteriorPathRecord, sourceEarlyPrefixEvent t b j = Z ⁻¹' G) ∧
        @MeasurableSet Sample (MeasurableSpace.comap Z ⊤) (sourceEarlyPrefixEvent t b j) := by
  obtain ⟨a₀, hgeometry⟩ := source_early_distance_geometry J₀
  obtain ⟨a₁, hprefix⟩ := source_early_prefix_containment J₀ hJ₀
  refine ⟨max a₀ a₁, ?_⟩
  filter_upwards [hgeometry, hprefix, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hgeometry hprefix hN htime hm16 ht0
  intro b w hb hw hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  obtain ⟨_, _, hν, hgeom, _⟩ :=
    hgeometry b w hb hw hbw ((le_max_left _ _).trans ha) hrange
  obtain ⟨hC, hB₀, hB₁⟩ :=
    hprefix b w hbw ((le_max_right _ _).trans ha) hrange
  have hKC : K b ∪ K w ⊆ C b ∪ C w := Finset.union_subset_union hgeom.1 hgeom.2.1
  have hB : domainExitBoundary (C b ∪ C w) ⊆
      (sourceEntranceDomain m 1 ℓ b j : Set Site) := by
    intro y hy
    rcases domainExitBoundary_union_subset (C b) (C w) hy with hy | hy
    · exact hB₀ hy
    · exact hB₁ hy
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hjν : j ≤ ν := by dsimp [j, ν]; omega
  have hjℓ : j + 1 ≤ ℓ := by
    have hp : 0 < ℓ - 1 := hN.1
    omega
  obtain ⟨g, hg⟩ := source_prefix_count_representation hF t b j (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) hKC hm16 hjℓ hC hB
  have hrep : ∃ G : Set ExteriorPathRecord,
      sourceEarlyPrefixEvent t b j = sourcePairExteriorRecord t b w ν J ⁻¹' G :=
    source_early_prefix_event_of_counts t b j _ g hg
  refine ⟨hrep, ?_⟩
  obtain ⟨G, hG⟩ := hrep
  exact ⟨G, MeasurableSpace.measurableSet_top, hG.symm⟩

end SRWTightness
