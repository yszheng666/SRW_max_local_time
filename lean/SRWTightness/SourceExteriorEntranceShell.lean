import SRWTightness.ExteriorEntranceBoundary
import SRWTightness.InnerUnionBoundaryRadial
import SRWTightness.SourceExteriorGeometry
import SRWTightness.SourceOriginalJointRootBound

open Filter
namespace SRWTightness

/-- Every positive source exterior atom supplies the exact selected-site entrance shell and exterior exit. -/
theorem source_exterior_entrance_shell :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
        s.2.2.1 ∈ sourceEntranceDomain m 1 ℓ z ν ∧
        (ρ - 14 - 1 ≤ Real.sqrt (normSq (s.2.2.1 - z)) ∧
          Real.sqrt (normSq (s.2.2.1 - z)) ≤ ρ - 14) ∧
        s.2.2.2 ∉ sourceExitDomain m 1 ℓ z (ν - J) := by
  filter_upwards [source_exterior_geometry, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hg hN htime hm ht0
  intro b w ν J hb hw hbw ha hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := sourceRecordRadius m ℓ (ν + 1)
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  obtain ⟨hK₀, hK₁, hCD, _, _, hzero⟩ := hg b w ν J hb hw hbw ha hν hform
  have hKC : K b ∪ K w ⊆ C b ∪ C w := Finset.union_subset_union hK₀ hK₁
  have hx : (0 : Site) ∉ K b ∪ K w := fun h ↦ hzero (hKC h)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hr : m ≤ ρ := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ (ν + 1) hi
  intro h hh s hs
  let z := if s.2.1 then w else b
  have hz : z = b ∨ z = w := by dsimp [z]; split <;> simp
  have hslot := exterior_atom_slot (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) 0 h hh s hs
  have hstart : s.2.2.1 ∈ K z := by
    cases hl : s.2.1
    · have hn : s.2.2.1 ∉ K w := by
        have he := hslot.2.2
        rw [hl] at he
        simpa only [twoDomainExteriorLabel, decide_eq_false_iff_not] using he.symm
      simpa only [z, hl, Bool.false_eq_true, if_false] using (Finset.mem_union.mp hslot.1).resolve_right hn
    · have hin : s.2.2.1 ∈ K w := by
        have he := hslot.2.2
        rw [hl] at he
        simpa only [twoDomainExteriorLabel, decide_eq_true_eq] using he.symm
      simpa only [z, hl, if_true] using hin
  have hKz : K z ⊆ K b ∪ K w := by
    rcases hz with he | he
    · rw [he]; exact Finset.subset_union_left
    · rw [he]; exact Finset.subset_union_right
  have hCz : C z ⊆ C b ∪ C w := by
    rcases hz with he | he
    · rw [he]; exact Finset.subset_union_left
    · rw [he]; exact Finset.subset_union_right
  have hKd : K z = translateFinset z (diskFinset (ρ - 14)) := by
    norm_num [K, sourceEntranceDomain, sourceRecordBuffer, ρ]
  have hbnd := exterior_atom_entrance_boundary (diskFinset (Real.exp t)) (K b ∪ K w)
    (C b ∪ C w) hKC hCD (twoDomainExteriorLabel (K w)) 0 hx h hh s hs
  have hshell := inner_union_boundary_radial (diskFinset (Real.exp t)) (K b ∪ K w)
    z (ρ - 14) (by dsimp [m] at hr; linarith) (hKd ▸ hKz) s.2.2.1 hbnd.1 (hKd ▸ hstart)
  exact ⟨hstart, hshell, fun he ↦ hslot.2.1 (hCz he)⟩

end SRWTightness
