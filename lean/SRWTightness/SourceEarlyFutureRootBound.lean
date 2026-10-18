import SRWTightness.ExitRootMeanLinearBound
import SRWTightness.SourceEarlyCapacityBound
import SRWTightness.SourceEarlyShortGaps
import SRWTightness.SourceLevelLogRatio
import SRWTightness.SourceEarlyCommonObservation
import SRWTightness.SourceFutureRootMean

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.17: every actual short completion site has uniformly bounded future mean. -/
theorem source_early_future_root_bound (hLast : FiniteLastVisitCountInput)
    (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      ∀ z ∈ ({b, w} : Finset Site), ∀ x ∈ domainExitBoundary
        (sourceExitDomain (sourceLowerRadius t) 1
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) z ν),
        sourceFutureRootMean t b w x j ν ≤ C * ((J : ℝ) + 1) := by
  let g : ℝ := 2 / Real.pi
  let K : ℝ := 5 + 3 * Real.log 2
  let M : ℝ := 2 / g
  let C := 2 * M * (2 * g + g * K + |diskGreenAdditiveConstant|)
  have hg : 0 < g := by dsimp [g]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨Jmin, ho⟩ := source_early_common_observation
  refine ⟨C, by dsimp [C]; positivity, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, ho⟩ := ho J₀ hJ₀
  obtain ⟨a₁, hl⟩ := source_early_distance_levels J₀
  obtain ⟨a₂, ha₂, hgap⟩ := source_early_distance_gap_small J₀
  refine ⟨max a₀ (max a₁ a₂), ha₀.trans (le_max_left _ _), ?_⟩
  filter_upwards [ho, hl, source_early_root_observation_geometry, source_early_short_gaps,
    source_early_capacity_bound hinput, source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ))]
    with t ho hl hgeo hsg hc hlev hm16
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r₀ := sourceRecordRadius m ℓ ν
  let r := r₀ + 14
  let s := sourceRecordRadius m ℓ (ν + 1) - 14
  let R := sourceRecordRadius m ℓ j + 14
  have ha₀' := (le_max_left a₀ (max a₁ a₂)).trans ha
  have ha₁' := (le_max_left a₁ a₂).trans ((le_max_right _ _).trans ha)
  have ha₂' := (le_max_right a₁ a₂).trans ((le_max_right _ _).trans ha)
  have ha1 : 1 ≤ a := ha₀.trans ha₀'
  have hJa : J ≤ a := by have hh := hgap a ha₂'; dsimp [J]; omega
  have hν := (hl a ha₁' hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  have hm : 0 < m := sourceLowerRadius_pos t
  have hr₀ : 0 < r₀ := by dsimp [r₀, sourceRecordRadius]; positivity
  have hbuffer : 14 ≤ sourceRecordRadius m ℓ j := by
    have hh := sourceRecordRadius_ge_terminal m hm.le ℓ j (by
      have hh : j + 1 ≤ ℓ := (hlev.2 j hj).1
      exact (Nat.le_succ j).trans hh)
    linarith
  have hR : 1 ≤ R := by dsimp [R]; linarith
  obtain ⟨hs, hown, hother⟩ := hsg b w ν J hbw ha1 hν rfl
  change 0 ≤ s at hs
  change r₀ / 2 ≤ r - s at hown
  have hother' : r₀ / 2 ≤ ρ - (r + 1) - s := by
    change r₀ / 2 ≤ ρ - (r₀ + 15) - s at hother
    dsimp [r]; linarith
  have hsr : s < r := by linarith
  have hsep : 0 < ρ - (r + 1) - s := by linarith
  have hlog₁ := source_early_gap_log_ratio m (r - s) ℓ a J hm hJa hbuffer hown
  have hlog₂ := source_early_gap_log_ratio m (ρ - (r + 1) - s) ℓ a J hm hJa
    hbuffer hother'
  have hKD := (ho b w hbw ha₀' hrange).2.2.2.1
  have houter (z : Site) : sourceExitDomain m 1 ℓ z ν =
      translateFinset z (diskFinset r) := by
    norm_num [sourceExitDomain, sourceRecordBuffer, r, r₀]
  have hinner (z : Site) : sourceEntranceDomain m 1 ℓ z ν =
      translateFinset z (diskFinset s) := by
    norm_num [sourceEntranceDomain, sourceRecordBuffer, s]
  have hD : sourceCommonPairDomain t b j = translateFinset b (diskFinset R) := by
    norm_num [sourceCommonPairDomain, sourceExitDomain, sourceRecordBuffer, R, m, ℓ]
  have hcontain (z : Site) (hz : z ∈ ({b, w} : Finset Site)) :
      translateFinset z (diskFinset r) ⊆ translateFinset b (diskFinset R) ∧
      domainExitBoundary (translateFinset z (diskFinset r)) ⊆
        (translateFinset b (diskFinset R) : Set Site) := by
    have hh := hgeo b w ν J hbw ha1 hν rfl z hz
    rw [houter z] at hh
    rw [hD] at hKD
    exact ⟨hh.2.1.trans hKD, fun x hx ↦ hKD (hh.2.2 hx)⟩
  have hcap : capacity (diskFinset r) (diskFinset s) ≤ M := by
    have hh := hc ν hν b
    change capacity (sourceExitDomain m 1 ℓ b ν) (sourceEntranceDomain m 1 ℓ b ν) ≤ M at hh
    rwa [houter b, hinner b, capacity_translate] at hh
  have hpair (z u x : Site) (hz : z ∈ ({b, w} : Finset Site))
      (hu : u ∈ ({b, w} : Finset Site))
      (hρ : Real.sqrt (normSq (u - z)) = ρ)
      (hx : x ∈ domainExitBoundary (translateFinset z (diskFinset r))) :
      (∫ Y, ((wordMarkRootCount (translateFinset z (diskFinset s))
        (translateFinset z (diskFinset r)) Y +
        wordMarkRootCount (translateFinset u (diskFinset s))
        (translateFinset u (diskFinset r)) Y : ℕ) : ℝ)
        ∂killedWordMarkLaw (translateFinset b (diskFinset R)) x) ≤ C * ((J : ℝ) + 1) := by
    apply exit_root_pair_mean_linear_bound hLast b z u x R r s hR hs hsr
      (by simpa only [hρ] using hsep) hx ((hcontain z hz).2 hx)
      (hcontain z hz).1 (hcontain u hu).1 J K M (by positivity) hK hM hcap
    · dsimp [R, j, K]
      linarith [hlog₁]
    · rw [hρ]
      dsimp [R, j, K]
      linarith [hlog₂]
  intro z hz x hx
  change x ∈ domainExitBoundary (sourceExitDomain m 1 ℓ z ν) at hx
  rw [houter z] at hx
  change (∫ Y, ((wordMarkRootCount (sourceEntranceDomain m 1 ℓ b ν)
    (sourceExitDomain m 1 ℓ b ν) Y + wordMarkRootCount (sourceEntranceDomain m 1 ℓ w ν)
    (sourceExitDomain m 1 ℓ w ν) Y : ℕ) : ℝ)
    ∂killedWordMarkLaw (sourceCommonPairDomain t b j) x) ≤ C * ((J : ℝ) + 1)
  rw [houter b, houter w, hinner b, hinner w, hD]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz
  · subst z
    have hh := hpair b w x (by simp) (by simp) rfl hx
    exact hh
  · subst z
    have hsym : Real.sqrt (normSq (b - w)) = ρ := by
      rw [show b - w = -(w - b) by abel, normSq_neg]
    have hh := hpair w b x (by simp) (by simp) hsym hx
    simpa only [Nat.add_comm] using hh

end SRWTightness
