import SRWTightness.ExteriorLabelRecordSupport
import SRWTightness.SourceExteriorFiber
import SRWTightness.SourceEarlyLongBallDisjoint
import SRWTightness.SourceNestedWordFlatten
import SRWTightness.SourceOriginalJointRootBound

open Filter
namespace SRWTightness

/-- Every positive actual exterior/word atom has exactly the short-root support selected by its labels. -/
theorem source_exterior_label_support (hF : ExteriorBridgeFactorizationInput) {M₀ M₁ : Type*} :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let S := fun z ↦ sourceExitDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ (h : ExteriorPathRecord) (us : List PathWord), us.length = h.1.length →
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      0 < pathLaw.real {ω | killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w)
        (C b ∪ C w) 0 (fun _ u ↦ u) ω = us ∧ sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ (F₀ : Site → PathWord → M₀) (F₁ : Site → PathWord → M₁), ∀ p ∈ h.1.zip us,
      (p.1.2.1 = false →
        wordChildRecords (K b) (S b) p.1.2.2.1 F₀ p.2 ≠ [] ∧
        wordChildRecords (K w) (S w) p.1.2.2.1 F₁ p.2 = []) ∧
      (p.1.2.1 = true →
        wordChildRecords (K w) (S w) p.1.2.2.1 F₁ p.2 ≠ [] ∧
        wordChildRecords (K b) (S b) p.1.2.2.1 F₀ p.2 = []) := by
  filter_upwards [source_exterior_bridges hF, source_early_long_balls_disjoint,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)]
      with t he hd hN htime hm16 ht0
  intro b w ν J hb hw hbw ha hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let S := fun z ↦ sourceExitDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hm : sourceRecordBuffer 1 + 2 ≤ m := by norm_num [sourceRecordBuffer]; exact hm16
  have hK (z : Site) : K z ⊆ S z :=
    sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num) hm hi
  have hS (z : Site) : S z ⊆ C z :=
    sourceExitDomain_antitone m 1 ℓ z (by norm_num) hm (Nat.sub_le ν J)
  intro h us hlen hh hu F₀ F₁
  have hprod : labeledExteriorBridgeWordProduct (C b) (C w) h us ≠ 0 := by
    have heq := he b w ν J hb hw hbw ha hν hform h hh us hlen
    rw [← heq]
    exact div_ne_zero hu.ne' hh.ne'
  exact exterior_label_record_support (diskFinset (Real.exp t)) (K b) (K w) (S b) (S w)
    (C b) (C w) (hK b) (hK w) (hS b) (hS w) (hd b w ν J hbw ha hν hform)
    0 h hh us hprod F₀ F₁

end SRWTightness
