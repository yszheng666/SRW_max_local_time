import SRWTightness.SourceRemainingJointRootBound

open MeasureTheory Filter
namespace SRWTightness

/-- The long-radius separation holds even when the true logarithmic distance index is negative. -/
theorem source_pair_long_radius_all_indices (t ρ : ℝ) (hρ : 0 < ρ)
    (ν J : ℕ) (hν : ν = sourceCommonPairDistanceIndex t ρ + J + 5) :
    sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν - J) < Real.exp (-4) * ρ := by
  let a := sourceCommonPairDistanceIndex t ρ
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)
  have hfloor : Real.log (r / ρ) < (a : ℝ) + 1 := Nat.lt_floor_add_one _
  have he : Real.log (sourceCommonPairInnerRadius t a) - Real.log ρ =
      Real.log (r / ρ) - (a : ℝ) - 1 := by
    rw [Real.log_div hr.ne' hρ.ne']
    dsimp only [sourceCommonPairInnerRadius, r, sourceRecordRadius]
    rw [Real.log_mul (sourceLowerRadius_pos t).ne' (Real.exp_pos _).ne',
      Real.log_mul (sourceLowerRadius_pos t).ne' (Real.exp_pos _).ne']
    simp only [Real.log_exp, Nat.cast_zero, Nat.cast_add, Nat.cast_one]
    ring
  have hinner : sourceCommonPairInnerRadius t a < ρ := by
    have hh := Real.exp_lt_exp.mpr (show Real.log (sourceCommonPairInnerRadius t a) <
      Real.log ρ by linarith only [he, hfloor])
    simpa only [Real.exp_log (sourceCommonPairInnerRadius_pos t a), Real.exp_log hρ] using hh
  have hindex : ν - J = a + 5 := by dsimp only [a]; omega
  have heq : sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν - J) =
      Real.exp (-4) * sourceCommonPairInnerRadius t a := by
    rw [hindex]
    unfold sourceCommonPairInnerRadius sourceRecordRadius
    rw [show ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) - ((a + 5 : ℕ) : ℝ)) =
      -4 + ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) - ((a + 1 : ℕ) : ℝ)) by
        push_cast; ring, Real.exp_add]
    ring
  rw [heq]
  exact mul_lt_mul_of_pos_left hinner (Real.exp_pos _)

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_geometry_all_indices :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      K b ⊆ C b ∧ K w ⊆ C w ∧ C b ∪ C w ⊆ diskFinset (Real.exp t) ∧
        (∀ y ∈ domainExitBoundary (C b), y ∉ C w) ∧
        (∀ y ∈ domainExitBoundary (C w), y ∉ C b) ∧ 0 ∉ C b ∪ C w := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (60 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t ht hN htime hm60 ht0
  intro b w ν J hb hw hbw hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ (ν - J)
  let B := r + 14
  have hm : 0 < m := sourceLowerRadius_pos t
  have hscale : 32 * m ≤ Real.exp t := by
    have hh := (hT t ht).2
    change 32 * sourceLowerRadius t ≤ Real.exp t
    nlinarith [Real.exp_one_gt_two, sourceLowerRadius_pos t]
  have hbr := (source_root_depth_bracket (Real.exp t) m hm hscale).1
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν + 1 ≤ ℓ := by
    have hpos : 0 < ℓ - 1 := hN.1
    omega
  have hρ : 0 < ρ := by
    have hh := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    exact Real.sqrt_pos.2 (by linarith)
  have hrbound : r < Real.exp (-4) * ρ := source_pair_long_radius_all_indices t ρ hρ ν J hform
  have hrlo : m ≤ r := sourceRecordRadius_ge_terminal m hm.le ℓ (ν - J) (by omega)
  have he4 : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4) (by norm_num)
        (by linarith [Real.add_one_le_exp (4 : ℝ)]))
  have hrρ : r < ρ / 5 := by
    have hh := mul_le_mul_of_nonneg_right he4 hρ.le
    nlinarith
  have hB0 : 0 ≤ B := by dsimp [B]; linarith
  have hgap : B + B + 1 ≤ ρ := by dsimp [B]; change 60 ≤ m at hm60; linarith
  have hmono := sourceRecordRadius_antitone m hm.le ℓ (Nat.zero_le (ν - J))
  have hBupper : B ≤ Real.exp t / 32 + 14 := by dsimp [B, r]; linarith
  have hRlarge : 1920 ≤ Real.exp t := by change 60 ≤ m at hm60; linarith
  have hdomain (z : Site) : sourceExitDomain m 1 ℓ z (ν - J) =
      translateFinset z (diskFinset B) := by
    norm_num [sourceExitDomain, sourceRecordBuffer, B, r]
  have hinner (z : Site) : sourceEntranceDomain m 1 ℓ z ν ⊆ sourceExitDomain m 1 ℓ z (ν - J) := by
    have hs := sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num)
      (by norm_num [sourceRecordBuffer]; change 60 ≤ m at hm60; linarith) hνℓ
    have hrad := sourceRecordRadius_antitone m hm.le ℓ (Nat.sub_le ν J)
    have hshort : 0 ≤ sourceRecordRadius m ℓ ν + 14 := by unfold sourceRecordRadius; positivity
    have hnest : sourceExitDomain m 1 ℓ z ν ⊆ sourceExitDomain m 1 ℓ z (ν - J) := by
      unfold sourceExitDomain sourceRecordBuffer
      norm_num only
      exact Finset.image_subset_image (diskFinset_mono _ _ hshort (by linarith))
    exact hs.trans hnest
  have hfit (z : Site) (hz : z ∈ sourceCandidateAnnulus (Real.exp t)) :
      sourceExitDomain m 1 ℓ z (ν - J) ⊆ diskFinset (Real.exp t) ∧
        0 ∉ sourceExitDomain m 1 ℓ z (ν - J) := by
    have hzc := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos _) z).mp hz
    rw [hdomain]
    refine ⟨(root_domain_and_exit_inside z B (Real.exp t) hB0 (by linarith)).1, ?_⟩
    intro hz0
    have hnorm : normSq z < B ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
        zero_sub, normSq_neg] using hz0
    have hsq := normSq_eq_sq_sqrt z
    have hnon := Real.sqrt_nonneg (normSq z)
    nlinarith
  have hbfit := hfit b hb
  have hwfit := hfit w hw
  refine ⟨hinner b, hinner w, Finset.union_subset hbfit.1 hwfit.1, ?_, ?_, ?_⟩
  · change ∀ y ∈ domainExitBoundary (sourceExitDomain m 1 ℓ b (ν - J)),
      y ∉ sourceExitDomain m 1 ℓ w (ν - J)
    rw [hdomain b, hdomain w]
    exact translated_disk_exit_gap b w B B hB0 hB0 hgap
  · have hgap' : B + B + 1 ≤ Real.sqrt (normSq (b - w)) := by
      simpa only [show b - w = -(w - b) by abel, normSq_neg] using hgap
    change ∀ y ∈ domainExitBoundary (sourceExitDomain m 1 ℓ w (ν - J)),
      y ∉ sourceExitDomain m 1 ℓ b (ν - J)
    rw [hdomain w, hdomain b]
    exact translated_disk_exit_gap w b B B hB0 hB0 hgap'
  · simpa only [Finset.mem_union, not_or] using And.intro hbfit.2 hwfit.2

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_entrance_shell_all_indices :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
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
  filter_upwards [source_exterior_geometry_all_indices, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hg hN htime hm ht0
  intro b w ν J hb hw hbw hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := sourceRecordRadius m ℓ (ν + 1)
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  obtain ⟨hK₀, hK₁, hCD, _, _, hzero⟩ := hg b w ν J hb hw hbw hν hform
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
      simpa only [z, hl, Bool.false_eq_true, if_false] using (Finset.mem_union.mp
        hslot.1).resolve_right hn
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

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_exit_positive_all_indices (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
        0 < traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2 := by
  filter_upwards [source_exterior_geometry_all_indices] with t ht
  intro b w ν J hb hw hbw hν hform
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw hν hform
  dsimp only
  intro h hh s hs
  have hp := exterior_atom_exit_positive hF _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁ h hh s hs
  split <;> simp_all

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_slot_record_law_all_indices (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
      ∀ (a : ℝ) (K : Finset Site), 1 ≤ a → a ≤ m / t ^ 6 →
      K ⊆ translateFinset z (diskFinset a) →
      ∀ (r : FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))
        (rs : List (FiniteExcursionRecord (Mark K) (ℓ - (ν + 1)))),
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
        (C * 15 / (ρ - 14) * ((rs.length : ℝ) + 1) +
        ((r :: rs).map (sourceLongFineError B W t a K ν)).sum)
      let weight := p * (1 - p) ^ rs.length * ((r :: rs).map (sourceLongFineReferenceMass t z K
        ν)).prod
      let event := {ω | killedChildRecords (sourceExitDomain m 1 ℓ z (ν - J))
        (sourceEntranceDomain m 1 ℓ z ν) (sourceExitDomain m 1 ℓ z ν) s.2.2.1
        (sourceLongFineRecord t z K ν) ω = r :: rs}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 ω = s.2.2.2} /
        traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2
      Real.exp (-E) * weight ≤ conditional ∧ conditional ≤ Real.exp E * weight := by
  obtain ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, hlaw⟩ :=
    source_conditioned_long_record_law hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hlaw, source_exterior_entrance_shell_all_indices,
    source_exterior_exit_positive_all_indices hF]
    with t ht hshell hexit
  intro b w ν J hb hw hbw hν hform hJ
  dsimp only
  intro h hh s hs
  intro a K ha hcut hK r rs
  obtain ⟨hx, hxlohi, he⟩ := hshell b w ν J hb hw hbw hν hform h hh s hs
  have hep := hexit b w ν J hb hw hbw hν hform h hh s hs
  exact ht _ a K ha hcut hK ν J hν hJ (by omega) _ _ hx hxlohi.1 hxlohi.2 he hep r rs

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_record_product_all_indices (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
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
    source_exterior_slot_record_law_all_indices hF hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hslot, source_exterior_geometry_all_indices] with t ht hg
  intro b w ν J hb hw hbw hν hform hJ a₀ a₁ K₀ K₁ ha₀ hc₀ hK₀ ha₁ hc₁ hK₁
  dsimp only
  intro h hh r hr
  obtain ⟨hkb, hkw, hCD, hgapb, hgapw, _⟩ := hg b w ν J hb hw hbw hν hform
  have he := exterior_conditional_word_event hF _ _ _ _ _ 0 hkb hkw hCD hgapb hgapw h hh
    {us | (h.1.zip us).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2) = List.ofFn r}
  simp only [Set.mem_setOf_eq] at he
  simp only [sourcePairExteriorRecord]
  rw [he]
  apply exterior_record_product_comparison
  intro i
  dsimp only
  have hs := hr i
  have hp := ht b w ν J hb hw hbw hν hform hJ h hh (h.1.get i) (List.get_mem _ _)
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

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_conditional_tuple_domination_all_indices (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C B W J₀ : ℝ, 0 < A ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) → ∀ (a₀ a₁ : ℝ) (K₀ K₁ : Finset Site),
      ∀ [MeasurableSpace (SourceFineRecord t K₀ ν)]
        [MeasurableSingletonClass (SourceFineRecord t K₀ ν)]
        [MeasurableSpace (SourceFineRecord t K₁ ν)]
        [MeasurableSingletonClass (SourceFineRecord t K₁ ν)]
        [MeasurableSpace (List (SourceFineRecord t K₀ ν))]
        [MeasurableSingletonClass (List (SourceFineRecord t K₀ ν))]
        [MeasurableSpace (List (SourceFineRecord t K₁ ν))]
        [MeasurableSingletonClass (List (SourceFineRecord t K₁ ν))],
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 → K₀ ⊆ translateFinset b (diskFinset a₀) →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 → K₁ ⊆ translateFinset w (diskFinset a₁) →
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ (k l : ℕ) (E : ℝ),
      (sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h).restrict
        (orderedTupleErrorRegion (fun i ↦ (h.1.get i).2.1) k l
          (fun r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν ↦
            ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i)) E) ≤
        ENNReal.ofReal (Real.exp E) • orderedTaggedCountMeasure
          (sourceLongEscapeParameter (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
          (fun i ↦ (h.1.get i).2.1)
          (sourceFineReferenceMeasure t b K₀ ν) (sourceFineReferenceMeasure t w K₁ ν) k l := by
  obtain ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, hprod⟩ :=
    source_exterior_record_product_all_indices hF hR hP hH hM hT
  refine ⟨A, C, B, W, J₀, hA, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hprod, source_reference_parameter_early] with t ht hparam
  intro b w ν J hb hw hbw hν hform hJ a₀ a₁ K₀ K₁
  intro m₀ s₀ m₁ s₁ lm₀ ls₀ lm₁ ls₁ ha₀ hc₀ hK₀ ha₁ hc₁ hK₁ h hh k l E
  letI := finiteExcursionRecord_countable (Mark K₀)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := finiteExcursionRecord_countable (Mark K₁)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
  letI := sourceConditionalFineTupleLaw_probability t b w K₀ K₁ ν J h hh
  have hJpos : 1 ≤ J := by exact_mod_cast (show (1 : ℝ) ≤ J by linarith)
  have hp := hparam ν J hν hJpos
  apply ordered_tuple_error_domination _ _ _ _ hp.1.le hp.2.le
  intro r hr
  have hcompat : ∀ i, sourceExteriorFineCompatible t K₀ K₁ ν (h.1.get i) (r i) := hr
  have hbnd := (ht b w ν J hb hw hbw hν hform hJ a₀ a₁ K₀ K₁
    ha₀ hc₀ hK₀ ha₁ hc₁ hK₁ h hh r hcompat).2
  rw [← sourceConditionalFineTupleLaw_atom t b w K₀ K₁ ν J h r] at hbnd
  simpa only [source_tagged_block_weight] using hbnd

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_bridges_all_indices (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let D := diskFinset (Real.exp t)
      let label := twoDomainExteriorLabel (K w)
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} →
      ∀ us : List PathWord, us.length = h.1.length →
      pathLaw.real {ω | killedChildRecords D (K b ∪ K w) (C b ∪ C w) 0 (fun _ u ↦ u) ω = us ∧
        killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} /
        pathLaw.real {ω | killedExteriorRecord D (K b ∪ K w) (C b ∪ C w) label 0 ω = h} =
          labeledExteriorBridgeWordProduct (C b) (C w) h us := by
  filter_upwards [source_exterior_geometry_all_indices] with t ht
  intro b w ν J hb hw hbw hν hform
  obtain ⟨hK₀, hK₁, hCD, hgap₀, hgap₁, _⟩ := ht b w ν J hb hw hbw hν hform
  dsimp only
  intro h hh us hlen
  exact exterior_two_domain_bridges hF _ _ _ _ _ 0 hK₀ hK₁ hCD hgap₀ hgap₁ h hh us hlen

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_early_long_balls_disjoint_all_indices :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ), b ≠ w →

      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      Disjoint (sourceExitDomain m 1 ℓ b (ν - J)) (sourceExitDomain m 1 ℓ w (ν - J)) := by
  filter_upwards [source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (14 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hN htime hm14 ht0
  intro b w ν J hbw hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let ρ := Real.sqrt (normSq (w - b))
  let r := sourceRecordRadius m ℓ (ν - J)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hνℓ : ν - J ≤ ℓ := by omega
  have hrad : m ≤ r := sourceRecordRadius_ge_terminal m (sourceLowerRadius_pos t).le ℓ _ hνℓ
  have hρ : 0 < ρ := by
    have hh := one_le_normSq_of_ne_zero (w - b) (sub_ne_zero.mpr hbw.symm)
    exact Real.sqrt_pos.2 (by linarith)
  have hsmall : r < Real.exp (-4) * ρ := source_pair_long_radius_all_indices t ρ hρ ν J hform
  have he : Real.exp (-4) ≤ (1 / 5 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (a := (5 : ℝ)) (b := Real.exp 4)
        (by norm_num) (by linarith [Real.add_one_le_exp (4 : ℝ)]))
  have hbound := hsmall.trans_le (mul_le_mul_of_nonneg_right he hρ.le)
  have hm : 14 ≤ m := hm14
  have hh := translated_disks_disjoint b w (r + 14) (r + 14) (by linarith)
    (by linarith) (by change r + 14 + (r + 14) ≤ ρ; linarith)
  simpa only [sourceExitDomain, sourceRecordBuffer, mul_one,
    show (4 : ℝ) + 10 = 14 by norm_num] using hh

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_label_support_all_indices (hF : ExteriorBridgeFactorizationInput) {M₀ M₁ :
  Type*} :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
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
  filter_upwards [source_exterior_bridges_all_indices hF,
    source_early_long_balls_disjoint_all_indices,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)]
      with t he hd hN htime hm16 ht0
  intro b w ν J hb hw hbw hν hform
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
    have heq := he b w ν J hb hw hbw hν hform h hh us hlen
    rw [← heq]
    exact div_ne_zero hu.ne' hh.ne'
  exact exterior_label_record_support (diskFinset (Real.exp t)) (K b) (K w) (S b) (S w)
    (C b) (C w) (hK b) (hK w) (hS b) (hS w) (hd b w ν J hbw hν hform)
    0 h hh us hprod F₀ F₁

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_tagged_forests_all_indices (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u)
      ∀ (K₀ K₁ : Finset Site) (h : ExteriorPathRecord) (us : List PathWord),
      us.length = h.1.length →
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      0 < pathLaw.real {ω | U ω = us ∧ sourcePairExteriorRecord t b w ν J ω = h} →
      let vs := (h.1.zip us).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2)
      (∀ p ∈ h.1.zip us, sourceExteriorFineCompatible t K₀ K₁ ν p.1
        (sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2)) ∧
      ∀ ω : Sample, sourcePairExteriorRecord t b w ν J ω = h → U ω = us →
        taggedForestLeft vs = sourceGroupedFineForest t b w b K₀ ν J ω ∧
        taggedForestRight vs = sourceGroupedFineForest t b w w K₁ ν J ω := by
  filter_upwards [source_exterior_label_support_all_indices (M₀ := Unit) (M₁ := Unit) hF] with t ht
  intro b w ν J hb hw hbw hν hform
  dsimp only
  intro K₀ K₁ h us hlen hh hu
  have hs := ht b w ν J hb hw hbw hν hform h us hlen hh hu
    (fun _ _ ↦ ()) (fun _ _ ↦ ())
  constructor
  · intro p hp
    have hsp := hs p hp
    cases hl : p.1.2.1
    · have hn := (hsp.1 hl).1
      have hn' : wordChildRecords
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          p.1.2.2.1 (sourceLongFineRecord t b K₀ ν) p.2 ≠ [] := by
        simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using hn
      simpa only [sourceExteriorFineRecord, sourceExteriorFineCompatible, hl,
        Bool.false_eq_true, if_false, Sum.elim_inl, true_and] using hn'
    · have hn := (hsp.2 hl).1
      have hn' : wordChildRecords
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
          p.1.2.2.1 (sourceLongFineRecord t w K₁ ν) p.2 ≠ [] := by
        simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using hn
      simpa only [sourceExteriorFineRecord, sourceExteriorFineCompatible, hl,
        if_true, Sum.elim_inr, true_and] using hn'
  · intro ω hω huω
    constructor
    · refine Eq.trans ?_ (source_exterior_fine_forest t b w b K₀ ν J ω h us hω huω)
      simp only [taggedForestLeft, List.flatMap_map]
      apply List.flatMap_congr
      intro p hp
      have hsp := hs p hp
      cases hl : p.1.2.1
      · simp only [sourceExteriorFineRecord, hl, Bool.false_eq_true, if_false, Sum.elim_inl, id_eq]
      · have hz : wordChildRecords
            (sourceEntranceDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
            (sourceExitDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
            p.1.2.2.1 (sourceLongFineRecord t b K₀ ν) p.2 = [] := by
          simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using (hsp.2 hl).2
        simpa only [sourceExteriorFineRecord, hl, if_true, Sum.elim_inr] using hz.symm
    · refine Eq.trans ?_ (source_exterior_fine_forest t b w w K₁ ν J ω h us hω huω)
      simp only [taggedForestRight, List.flatMap_map]
      apply List.flatMap_congr
      intro p hp
      have hsp := hs p hp
      cases hl : p.1.2.1
      · have hz : wordChildRecords
            (sourceEntranceDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
            (sourceExitDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
            p.1.2.2.1 (sourceLongFineRecord t w K₁ ν) p.2 = [] := by
          simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using (hsp.1 hl).2
        simpa only [sourceExteriorFineRecord, hl, Bool.false_eq_true, if_false, Sum.elim_inl] using
          hz.symm
      · simp only [sourceExteriorFineRecord, hl, if_true, Sum.elim_inr, id_eq]

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_fine_tuple_support_all_indices (hExt : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
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
  filter_upwards [source_exterior_tagged_forests_all_indices hExt] with t hsupp
  intro b w ν J hb hw hbw hν hform K₀ K₁ h hh
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
  have hs := hsupp b w ν J hb hw hbw hν hform K₀ K₁ h (U ω) hlen hh hp'
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

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_long_grouped_records_all_indices (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let D := diskFinset (Real.exp t)
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ z : Site, z = b ∨ z = w → ∀ {M : Type} (F : Site → PathWord → M),
      (fun ω ↦ (actualTerminalWordRecords (sourceExcursionLevels m 1 ℓ z 0 (ν + 1)) D 0 ω).map
        (fun p ↦ F p.1 p.2)) =ᵐ[pathLaw]
        fun ω ↦ (killedChildRecords D (K b ∪ K w) (C b ∪ C w) 0
          (fun y u ↦ wordChildRecords (K z) (sourceExitDomain m 1 ℓ z ν) y F u) ω).flatten := by
  filter_upwards [source_actual_nested_words hF, source_exterior_geometry_all_indices,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hwords hgeom hN htime hm16 ht0
  intro b w ν J hb hw hbw hν hform
  dsimp only
  intro z hz M F
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  obtain ⟨hKb, hKw, hCD, _, _, _⟩ := hgeom b w ν J hb hw hbw hν hform
  have hKC : K b ∪ K w ⊆ C b ∪ C w := Finset.union_subset_union hKb hKw
  have hzann : z ∈ sourceCandidateAnnulus (Real.exp t) := by rcases hz with rfl | rfl <;> assumption
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hm : sourceRecordBuffer 1 + 2 ≤ m := by norm_num [sourceRecordBuffer]; exact hm16
  have hshort : K z ⊆ sourceExitDomain m 1 ℓ z ν :=
    sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num) hm hi
  have hK : K z ⊆ K b ∪ K w := by
    rcases hz with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have hC : sourceExitDomain m 1 ℓ z ν ⊆ C b ∪ C w := by
    have hh : sourceExitDomain m 1 ℓ z ν ⊆ C z :=
      sourceExitDomain_antitone m 1 ℓ z (by norm_num) hm (Nat.sub_le ν J)
    rcases hz with rfl | rfl
    · exact hh.trans Finset.subset_union_left
    · exact hh.trans Finset.subset_union_right
  have hg := killed_child_records_flatten hF (diskFinset (Real.exp t))
    (K b ∪ K w) (C b ∪ C w) (K z) (sourceExitDomain m 1 ℓ z ν)
    hKC hshort hK hC hCD 0 F
  filter_upwards [hwords z hzann ν hν, hg] with ω hω hgω
  rw [hω, killed_child_word_pairs_map]
  exact hgω.symm

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_grouped_fine_error_all_indices (hF : TwoLevelWordFlatteningInput)
    (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ z : Site, z = b ∨ z = w → ∀ (Kobs : Finset Site) (a : ℝ),
      1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ᵐ ω ∂pathLaw,
        sourceActualFineForest t z Kobs ν ω = sourceGroupedFineForest t b w z Kobs ν J ω ∧
        (sourceActualCount t z 0 ω = 1 → sourceWalkCoarseBand t z ω →
          ((sourceGroupedFineForest t b w z Kobs ν J ω).map
            (sourceLongFineError B W t a Kobs ν)).sum ≤ sourceForestQuadraticError B W 8 t) := by
  filter_upwards [source_actual_fine_error hF B W hB hW, source_actual_nested_words hF,
    source_long_grouped_records_all_indices hF, source_root_gw_horizon_large,
      source_continuation_remaining_time,
    eventually_ge_atTop (0 : ℝ)] with t herror hwords hgroup hN htime ht0
  intro b w ν J hb hw hbw hν hform z hz Kobs a hamin hcut
  have hzann : z ∈ sourceCandidateAnnulus (Real.exp t) := by rcases hz with rfl | rfl <;> assumption
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  filter_upwards [herror z hzann Kobs ν hi a hamin hcut, hwords z hzann ν hν,
    hgroup b w ν J hb hw hbw hν hform z hz (sourceLongFineRecord t z Kobs ν)]
    with ω he hw hg
  rw [hw, killed_child_word_pairs_map] at hg
  have hid : sourceActualFineForest t z Kobs ν ω = sourceGroupedFineForest t b w z Kobs ν J ω := hg
  refine ⟨hid, ?_⟩
  intro hroot hbar
  rw [← hid]
  exact he hroot hbar

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_grouped_fine_count_all_indices (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ z : Site, z = b ∨ z = w → ∀ Kobs : Finset Site,
      ∀ᵐ ω ∂pathLaw,
        (sourceGroupedFineForest t b w z Kobs ν J ω).length = sourceActualCount t z ν ω := by
  filter_upwards [source_long_grouped_records_all_indices hF] with t ht
  intro b w ν J hb hw hbw hν hform z hz Kobs
  filter_upwards [ht b w ν J hb hw hbw hν hform z hz
    (sourceLongFineRecord t z Kobs ν)] with ω hω
  simpa only [sourceGroupedFineForest, List.length_map, sourceActualCount,
    sourceForwardRecordCount, Nat.sub_zero] using (congrArg List.length hω).symm

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_fine_tuple_actual_forests_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a : ℝ), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h →
        let r := sourceFineTuple t b w K₀ K₁ ν J h ω
        orderedTaggedCompatible (fun i ↦ (h.1.get i).2.1) r ∧
        orderedTaggedForests r =
          (sourceActualFineForest t b K₀ ν ω, sourceActualFineForest t w K₁ ν ω) ∧
        (orderedTaggedForests r).1.length = sourceActualCount t b ν ω ∧
        (orderedTaggedForests r).2.length = sourceActualCount t w ν ω := by
  filter_upwards [source_fine_tuple_support_all_indices hExt,
    source_grouped_fine_error_all_indices hFlat 0 0 le_rfl le_rfl,
    source_grouped_fine_count_all_indices hFlat] with t hsupp hforest hcount
  intro b w ν J hb hw hbw hν hform K₀ K₁ a ha hacut h hh
  filter_upwards [hsupp b w ν J hb hw hbw hν hform K₀ K₁ h hh,
    hforest b w ν J hb hw hbw hν hform b (Or.inl rfl) K₀ a ha hacut,
    hforest b w ν J hb hw hbw hν hform w (Or.inr rfl) K₁ a ha hacut,
    hcount b w ν J hb hw hbw hν hform b (Or.inl rfl) K₀,
    hcount b w ν J hb hw hbw hν hform w (Or.inr rfl) K₁]
    with ω hs hf₀ hf₁ hc₀ hc₁
  intro hω
  obtain ⟨hcompat, hpair⟩ := hs hω
  dsimp only
  refine ⟨hcompat, ?_, ?_, ?_⟩
  · exact hpair.trans (Prod.ext hf₀.1.symm hf₁.1.symm)
  · exact (congrArg (fun p ↦ p.1.length) hpair).trans hc₀
  · exact (congrArg (fun p ↦ p.2.length) hpair).trans hc₁

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_conditional_remaining_region_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (A C a₀ a₁ : ℝ) (K₀ K₁ : Finset Site), 0 ≤ A → 0 ≤ C →
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
      sourceActualCount t b ν p.1 = k → sourceActualCount t w ν p.1 = l →
      forestPopulationList _ (sourceActualFineForest t b K₀ ν p.1) ∈
        sourceContinuationBand t ν
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      forestPopulationList _ (sourceActualFineForest t w K₁ ν p.1) ∈
        sourceContinuationBand t ν
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      sourceFineTuple t b w K₀ K₁ ν J h p.1 ∈
        orderedTupleErrorRegion (fun i ↦ (h.1.get i).2.1) k l
          (fun r ↦ ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i))
          (16 * ((ν : ℝ) + 1) ^ 2 *
            (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
              C * 15 / (sourceRecordRadius (sourceLowerRadius t)
                (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
            2 * sourceForestQuadraticError B W 8 t) := by
  filter_upwards [source_fine_tuple_actual_forests_all_indices hExt hFlat,
    source_tuple_remaining_region B W hB hW] with t hforest hregion
  intro b w ν J hb hw hbw hν hform hdepth A C a₀ a₁ K₀ K₁ hA hC
    ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
  have hs := source_conditional_path_support t b w ν J h _
    (hforest b w ν J hb hw hbw hν hform K₀ K₁ a₀ ha₀ hc₀ h hh)
  filter_upwards [hs] with p hp
  intro hx hy hb₀ hb₁
  obtain ⟨hcompat, hpair, hcount₀, hcount₁⟩ := hp
  apply hregion ν J hdepth A C a₀ a₁ K₀ K₁ hA hC ha₀ hc₀ ha₁ hc₁
    h.1.length (fun i ↦ (h.1.get i).2.1) _ k l hcompat
    (hcount₀.trans hx) (hcount₁.trans hy) hk hl
  · simpa only [hpair] using hb₀
  · simpa only [hpair] using hb₁

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_conditional_fine_tuple_actual_forests_all_indices (hExt :
  ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a : ℝ), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
        let r := sourceFineTuple t b w K₀ K₁ ν J h p.1
        orderedTaggedCompatible (fun i ↦ (h.1.get i).2.1) r ∧
        orderedTaggedForests r =
          (sourceActualFineForest t b K₀ ν p.1, sourceActualFineForest t w K₁ ν p.1) ∧
        (orderedTaggedForests r).1.length = sourceActualCount t b ν p.1 ∧
        (orderedTaggedForests r).2.length = sourceActualCount t w ν p.1 := by
  filter_upwards [source_fine_tuple_actual_forests_all_indices hExt hFlat] with t ht
  intro b w ν J hb hw hbw hν hform K₀ K₁ a ha hacut h hh
  exact source_conditional_path_support t b w ν J h _
    (ht b w ν J hb hw hbw hν hform K₀ K₁ a ha hacut h hh)

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_conditional_remaining_event_image_all_indices (hExt :
  ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (A γ : ℝ) (I₀ I₁ : ℕ)
        (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} → ∀ k l : ℕ,
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
      p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν →
      p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν →
      sourceActualCount t b ν p.1 = k → sourceActualCount t w ν p.1 = l →
      (sourceFineTuple t b w
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν J h p.1,
          (p.2 b, p.2 w)) ∈ sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l := by
  filter_upwards [source_conditional_fine_tuple_actual_forests_all_indices hExt hFlat] with t ht
  intro b w ν J hb hw hbw hν hform A γ I₀ I₁ z₀ z₁ ha hc h hh k l
  filter_upwards [ht b w ν J hb hw hbw hν hform _ _
    (A * diskEnergyGapRatio ^ I₀) ha hc h hh] with p hp
  intro hs₀ hs₁ hx hy
  change (_, p.2 b) ∈ sourceContinuationForestEvent _ _ _ _ _ _ _ _
    (sourceActualCount t b ν p.1) at hs₀
  change (_, p.2 w) ∈ sourceContinuationForestEvent _ _ _ _ _ _ _ _
    (sourceActualCount t w ν p.1) at hs₁
  rw [hx] at hs₀
  rw [hy] at hs₁
  change ((orderedTaggedForests _).1, p.2 b) ∈ _ ∧
    ((orderedTaggedForests _).2, p.2 w) ∈ _
  rw [hp.2.1]
  exact ⟨hs₀, hs₁⟩

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_conditional_remaining_upper_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ D C B W J₀ : ℝ, 0 < D ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) → ∀ (A γ : ℝ) (I₀ I₁ : ℕ)
        (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))
      (hα : 0 ≤ sourceReferenceIntensity (sourceLowerRadius t) 14)
      (hcap₀ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ≤ 1)
      (hcap₁ : sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset w (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
          (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ≤ 1)
      (hγ : 0 ≤ γ),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ A * diskEnergyGapRatio ^ I₁ →
      A * diskEnergyGapRatio ^ I₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      (ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h}).real
        {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
          p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
          sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l} ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) *
        (sourceReferenceJointCountWeight t ν J h k l *
          (sourceContinuationProbability t A γ b I₀ z₀ ν k *
            sourceContinuationProbability t A γ w I₁ z₁ ν l)) := by
  obtain ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, hdom⟩ :=
    source_conditional_tuple_domination_all_indices hExt hR hP hH hM hT
  refine ⟨D, C, B, W, J₀, hD, hC, hB, hW, hJ₀, ?_⟩
  filter_upwards [hdom, source_conditional_remaining_region_all_indices hExt hFlat B W hB hW,
    source_conditional_remaining_event_image_all_indices hExt hFlat,
      source_reference_parameter_early,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    eventually_ge_atTop (0 : ℝ)] with t hd hregion himage hparam hN htime ht0
  intro b w ν J hb hw hbw hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hα hcap₀ hcap₁ hγ ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
  have hnreal : (ν : ℝ) ≤
      ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hnreal
  have hdepth : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  have hJpos : 1 ≤ J := by exact_mod_cast (show (1 : ℝ) ≤ J by linarith)
  have hp := hparam ν J hν hJpos
  let K₀ := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))
  let K₁ := translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))
  let E := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
    2 * sourceForestQuadraticError B W 8 t
  let G := orderedTupleErrorRegion (fun i : Fin h.1.length ↦ (h.1.get i).2.1) k l
    (fun r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν ↦
      ∑ i, sourceExteriorFineError D C B W t (A * diskEnergyGapRatio ^ I₀)
        (A * diskEnergyGapRatio ^ I₁) K₀ K₁ ν J (r i)) E
  apply source_conditional_remaining_upper_of_domination t A γ b w I₀ I₁ ν J z₀ z₁
    hGW₀ hGW₁ hMix hα hcap₀ hcap₁ hγ hp.1.le hp.2.le h k l E hbw hh G
  · exact hd b w ν J hb hw hbw hν hform hJ
      (A * diskEnergyGapRatio ^ I₀) (A * diskEnergyGapRatio ^ I₁) K₀ K₁
      ha₀ hc₀ (Finset.Subset.refl _) ha₁ hc₁ (Finset.Subset.refl _) h hh k l E
  · have hr := hregion b w ν J hb hw hbw hν hform hdepth D C
      (A * diskEnergyGapRatio ^ I₀) (A * diskEnergyGapRatio ^ I₁) K₀ K₁ hD.le hC.le
      ha₀ hc₀ ha₁ hc₁ h hh k l hk hl
    have hi := himage b w ν J hb hw hbw hν hform A γ I₀ I₁ z₀ z₁
      ha₀ hc₀ h hh k l
    filter_upwards [hr, hi] with p hrp hip
    rintro ⟨hs₀, hs₁, hx, hy⟩
    exact ⟨hrp hx hy hs₀.2.1 hs₁.2.1, hip hs₀ hs₁ hx hy⟩

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_slot_count_law_all_indices (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let ρ := sourceRecordRadius m ℓ (ν + 1)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ s ∈ h.1, let z := if s.2.1 then w else b
      ∀ k : ℕ,
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      let E := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 / (ρ - 14) * ((k : ℝ) + 1)
      let event := {ω | (killedChildIntervals (sourceExitDomain m 1 ℓ z (ν - J))
        (sourceEntranceDomain m 1 ℓ z ν) (sourceExitDomain m 1 ℓ z ν) s.2.2.1 ω).length = k + 1}
      let conditional := pathLaw.real {ω | ω ∈ event ∧
        domainExitLocation (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 ω = s.2.2.2} /
        traceExitProbability (sourceExitDomain m 1 ℓ z (ν - J)) s.2.2.1 s.2.2.2
      Real.exp (-E) * (p * (1 - p) ^ k) ≤ conditional ∧
        conditional ≤ Real.exp E * (p * (1 - p) ^ k) := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, hlaw⟩ :=
    source_conditioned_long_root_count hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [hlaw, source_exterior_entrance_shell_all_indices,
    source_exterior_exit_positive_all_indices hF]
    with t ht hshell hexit
  intro b w ν J hb hw hbw hν hform hJ
  dsimp only
  intro h hh s hs
  intro k
  obtain ⟨hx, hxlohi, he⟩ := hshell b w ν J hb hw hbw hν hform h hh s hs
  have hep := hexit b w ν J hb hw hbw hν hform h hh s hs
  exact ht ν J hν hJ (by omega) _ _ _ hx hxlohi.1 hxlohi.2 he hep k

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_count_product_all_indices (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u)
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k : Fin h.1.length → ℕ,
      let E := Finset.univ.sum (fun i : Fin h.1.length ↦ A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
        C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14) * ((k i : ℝ) + 1))
      let weight := ∏ i : Fin h.1.length, p * (1 - p) ^ k i
      let mass := pathLaw.real {ω |
        (h.1.zip (U ω)).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) =
          List.ofFn (fun i ↦ k i + 1) ∧ sourcePairExteriorRecord t b w ν J ω = h} /
          pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}
      Real.exp (-E) * weight ≤ mass ∧ mass ≤ Real.exp E * weight := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, hslot⟩ :=
    source_exterior_slot_count_law_all_indices hF hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [hslot, source_exterior_geometry_all_indices] with t ht hg
  intro b w ν J hb hw hbw hν hform hJ
  dsimp only
  intro h hh k
  obtain ⟨hkb, hkw, hCD, hgapb, hgapw, _⟩ := hg b w ν J hb hw hbw hν hform
  have he := exterior_conditional_word_event hF _ _ _ _ _ 0 hkb hkw hCD hgapb hgapw h hh
    {us | (h.1.zip us).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) =
      List.ofFn (fun i ↦ k i + 1)}
  simp only [Set.mem_setOf_eq] at he
  simp only [sourcePairExteriorRecord]
  rw [he]
  apply exterior_record_product_comparison
  intro i
  dsimp only
  have hp := ht b w ν J hb hw hbw hν hform hJ h hh (h.1.get i) (List.get_mem _ _) (k i)
  cases hl : (h.1.get i).2.1 <;>
    simpa only [killedWordBridgeLaw_record, sourceExteriorRootCount, hl, Bool.false_eq_true,
      if_false, if_true, killedChildIntervals, Set.mem_setOf_eq] using hp

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_long_grouped_root_count_all_indices (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ z : Site, z = b ∨ z = w → sourceActualCount t z ν =ᵐ[pathLaw]
        fun ω ↦ ((killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w) 0
          (fun y u ↦ wordChildRecords (K z) (sourceExitDomain m 1 ℓ z ν) y
            (fun x v ↦ (x, v)) u) ω).flatten).length := by
  filter_upwards [source_long_grouped_records_all_indices hF] with t ht
  intro b w ν J hb hw hbw hν hform
  dsimp only
  intro z hz
  filter_upwards [ht b w ν J hb hw hbw hν hform z hz (fun x v ↦ (x, v))] with ω hω
  simpa only [List.length_map, sourceActualCount, sourceForwardRecordCount, Nat.sub_zero] using
    congrArg List.length hω

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_exterior_original_counts_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
        0 (fun _ u ↦ u)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h →
      ∀ r : Fin h.1.length → ℕ,
      (h.1.zip (U ω)).map (fun p ↦ sourceExteriorRootCount t b w ν p.1 p.2) = List.ofFn r →
      sourceActualCount t b ν ω = labeledRootTotal (fun i ↦ (h.1.get i).2.1) r false ∧
      sourceActualCount t w ν ω = labeledRootTotal (fun i ↦ (h.1.get i).2.1) r true := by
  filter_upwards [source_exterior_label_support_all_indices (M₀ := Unit) (M₁ := Unit) hExt,
    source_long_grouped_root_count_all_indices hFlat] with t hsupp hgroup
  intro b w ν J hb hw hbw hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let S := fun z ↦ sourceExitDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w) 0 (fun _ u ↦ u)
  let Z := sourcePairExteriorRecord t b w ν J
  have hpos := ae_support_of_positive_atoms pathLaw (fun ω ↦ (U ω, Z ω))
    (fun r ↦ 0 < pathLaw.real {ω | (U ω, Z ω) = r}) (fun _ hr ↦ hr)
  intro h hh
  filter_upwards [hpos, hgroup b w ν J hb hw hbw hν hform b (Or.inl rfl),
    hgroup b w ν J hb hw hbw hν hform w (Or.inr rfl)] with ω hp hx hy
  intro hω r hr
  change Z ω = h at hω
  have hlen : (U ω).length = h.1.length := by
    have he := killedExteriorRecord_length (diskFinset (Real.exp t)) (K b ∪ K w)
      (C b ∪ C w) (twoDomainExteriorLabel (K w)) 0 ω
    change (Z ω).1.length = (U ω).length at he
    rw [hω] at he
    exact he.symm
  have hp' : 0 < pathLaw.real {ω' | U ω' = U ω ∧ Z ω' = h} := by
    simpa only [Prod.mk.injEq, hω] using hp
  have hs := hsupp b w ν J hb hw hbw hν hform h (U ω) hlen hh hp'
    (fun _ _ ↦ ()) (fun _ _ ↦ ())
  have he₀ := exterior_word_fiber_records (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) 0 ω h (U ω) hω rfl
    (fun y u ↦ wordChildRecords (K b) (S b) y (fun x v ↦ (x, v)) u)
  have he₁ := exterior_word_fiber_records (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) 0 ω h (U ω) hω rfl
    (fun y u ↦ wordChildRecords (K w) (S w) y (fun x v ↦ (x, v)) u)
  have hx' := hx.trans (congrArg (fun rs ↦ rs.flatten.length) he₀).symm
  have hy' := hy.trans (congrArg (fun rs ↦ rs.flatten.length) he₁).symm
  simp only [List.length_flatten, List.map_map, Function.comp_def, wordChildRecords,
    List.length_map] at hx' hy'
  constructor
  · rw [hx', exterior_count_total_of_tuple h (U ω) (sourceExteriorRootCount t b w ν) r hr false]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    cases hl : p.1.2.1
    · simp [sourceExteriorRootCount, hl, K, S, m, ℓ]
    · have hz : wordChildIntervals (K b) (S b) p.1.2.2.1 p.2 = [] := by
        simpa only [wordChildRecords, List.map_eq_nil_iff] using ((hs p hp).2 hl).2
      simp [sourceExteriorRootCount, hl, hz]
  · rw [hy', exterior_count_total_of_tuple h (U ω) (sourceExteriorRootCount t b w ν) r hr true]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    cases hl : p.1.2.1
    · have hz : wordChildIntervals (K w) (S w) p.1.2.2.1 p.2 = [] := by
        simpa only [wordChildRecords, List.map_eq_nil_iff] using ((hs p hp).1 hl).2
      simp [sourceExteriorRootCount, hl, hz]
    · simp [sourceExteriorRootCount, hl, K, S, m, ℓ]

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_reference_count_lower_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceReferenceJointCountWeight t ν J h k l ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 /
            (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))) *
        (pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h ∧
          sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} /
          pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) := by
  classical
  obtain ⟨A, C, J₀, hA, hC, hJ₀, ht⟩ := source_exterior_count_product_all_indices hExt hR hP hH hM
    hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [ht, source_exterior_original_counts_all_indices hExt hFlat,
    source_count_product_error_cap] with t hprod hcounts hcap
  intro b w ν J hb hw hbw hν hform hJ h hh k l hk hl
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w) 0 (fun _ u ↦ u)
  let Z := sourcePairExteriorRecord t b w ν J
  let H := {ω | Z ω = h}
  let μ := ProbabilityTheory.cond pathLaw H
  let f := fun ω ↦ (h.1.zip (U ω)).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2)
  let label := fun i : Fin h.1.length ↦ (h.1.get i).2.1
  let p := sourceLongEscapeParameter m 1 ℓ ν J
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14)
  let F := 16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε)
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  have hZ : Measurable Z := measurable_killedExteriorRecord _ _ _ _ _
  have hHm : MeasurableSet H := hZ (measurableSet_singleton h)
  have hμ : pathLaw H ≠ 0 := by
    intro hz
    exact hh.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)
  letI : IsProbabilityMeasure μ := ProbabilityTheory.cond_isProbabilityMeasure hμ
  have hU : Measurable U := measurable_killedChildRecords _ _ _ _ _
  have hf (r : Fin h.1.length → ℕ) : MeasurableSet {ω | f ω = List.ofFn r} :=
    hU ((Set.to_countable {us | (h.1.zip us).map
      (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) = List.ofFn r}).measurableSet)
  have hc : ∀ᵐ ω ∂μ, ∀ r : Fin h.1.length → ℕ, f ω = List.ofFn r →
      sourceActualCount t b ν ω = labeledRootTotal label r false ∧
      sourceActualCount t w ν ω = labeledRootTotal label r true := by
    have hcc := (ProbabilityTheory.cond_absolutelyContinuous (μ := pathLaw) (s := H)).ae_le
      (hcounts b w ν J hb hw hbw hν hform h hh)
    filter_upwards [hcc, ProbabilityTheory.ae_cond_mem (μ := pathLaw) hHm] with ω hcω hω
    exact hcω hω
  have hp (r : Fin h.1.length → ℕ) (hr : ∀ i, 0 < r i)
      (hrk : labeledRootTotal label r false = k) (hrl : labeledRootTotal label r true = l) :
      (∏ i, p * (1-p) ^ (r i - 1)) ≤ Real.exp F * μ.real {ω | f ω = List.ofFn r} := by
    have hri (i) : r i - 1 + 1 = r i := Nat.sub_add_cancel (hr i)
    have hrr (i) : ((r i - 1 : ℕ) : ℝ) + 1 = (r i : ℝ) := by exact_mod_cast hri i
    have he := (hprod b w ν J hb hw hbw hν hform hJ h hh (fun i ↦ r i - 1)).1
    simp only [hri, hrr] at he
    have hE : (∑ i, (δ + ε * (r i : ℝ))) ≤ F :=
      hcap ν hν J A C hA.le hC.le label r k l hr hrk hrl hk hl
    have hm : μ.real {ω | f ω = List.ofFn r} =
        pathLaw.real {ω | f ω = List.ofFn r ∧ Z ω = h} / pathLaw.real H :=
      conditional_real_apply pathLaw H _ hHm
    rw [← hm] at he
    change Real.exp (-(∑ i, (δ + ε * (r i : ℝ)))) *
      (∏ i, p * (1-p) ^ (r i - 1)) ≤ μ.real {ω | f ω = List.ofFn r} at he
    have hsmall : (∏ i, p * (1-p) ^ (r i - 1)) ≤
        Real.exp (∑ i, (δ + ε * (r i : ℝ))) * μ.real {ω | f ω = List.ofFn r} := by
      have he' := mul_le_mul_of_nonneg_left he (Real.exp_pos (∑ i, (δ + ε * (r i : ℝ)))).le
      simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, add_neg_cancel,
        Real.exp_zero, one_mul] using he'
    exact hsmall.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hE) (measureReal_nonneg))
  have hsum := reference_count_mixture_lower μ label f (sourceActualCount t b ν)
    (sourceActualCount t w ν) p F k l hf hc hp
  rw [conditional_real_apply pathLaw H _ hHm] at hsum
  have hevent : {ω | sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} ∩ H =
      {ω | Z ω = h ∧ sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} := by
    ext ω
    exact and_comm
  rw [hevent] at hsum
  exact hsum

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_enlarged_reference_count_lower_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      ∀ h : ExteriorPathRecord,
      0 < sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceReferenceJointCountWeight t ν J h k l ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 /
            (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))) *
        (sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h ∧
          sourceActualCount t b ν v.1 = k ∧ sourceActualCount t w ν v.1 = l} /
          sourceEnlargedLaw.real {v | sourcePairExteriorRecord t b w ν J v.1 = h}) := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, ht⟩ :=
    source_reference_count_lower_all_indices hExt hFlat hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [ht] with t hlow
  intro b w ν J hb hw hbw hν hform hJ h hh k l hk hl
  have hden := source_enlarged_path_event {ω | sourcePairExteriorRecord t b w ν J ω = h}
  have hnum := source_enlarged_path_event {ω | sourcePairExteriorRecord t b w ν J ω = h ∧
    sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l}
  simp only [Set.mem_setOf_eq] at hden hnum
  rw [hden] at hh
  rw [hnum, hden]
  exact hlow b w ν J hb hw hbw hν hform hJ h hh k l hk hl

/-- The corresponding exterior/count estimate also covers distance index zero. -/
theorem source_remaining_joint_root_bound_all_indices (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ D C B W J₀ : ℝ, 0 < D ∧ 0 < C ∧ 0 ≤ B ∧ 0 ≤ W ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) → ∀ (A γ : ℝ) (I₀ I₁ : ℕ)
        (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
      [MeasurableSpace (List (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))]
      [MeasurableSpace (List (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSingletonClass (List (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)]
      [MeasurableSpace (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSingletonClass (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν)]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν))]
      [MeasurableSpace (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      [MeasurableSingletonClass (List (SourceFineRecord t
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))]
      (hGW₀ : MarkedGWForestJointInput (Mark
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))))
      (hGW₁ : MarkedGWForestJointInput (Mark
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))))
      (hMix :
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        letI := finiteExcursionRecord_countable
          (Mark (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))))
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))
        OrderedForestMixtureInput
          (SourceFineRecord t (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀))) ν)
          (SourceFineRecord t (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν))
      (hγ : 0 ≤ γ),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ A * diskEnergyGapRatio ^ I₁ →
      A * diskEnergyGapRatio ^ I₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ G : Set ExteriorPathRecord,
      sourceEnlargedLaw.real
        {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
          p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
          sourcePairExteriorRecord t b w ν J p.1 ∈ G ∧
          sourceActualCount t b ν p.1 ≤ sourceEarlyRootCap t ν ∧
          sourceActualCount t w ν p.1 ≤ sourceEarlyRootCap t ν} ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) *
        ∫ ω, {u : Sample | sourcePairExteriorRecord t b w ν J u ∈ G ∧
            sourceActualCount t b ν u ≤ sourceEarlyRootCap t ν ∧
            sourceActualCount t w ν u ≤ sourceEarlyRootCap t ν}.indicator
          (fun u ↦ sourceContinuationProbability t A γ b I₀ z₀ ν (sourceActualCount t b ν u) *
            sourceContinuationProbability t A γ w I₁ z₁ ν (sourceActualCount t w ν u)) ω
          ∂pathLaw := by
  obtain ⟨D₁, C₁, B, W, J₁, hD₁, hC₁, hB, hW, hJ₁, hupper⟩ :=
    source_conditional_remaining_upper_all_indices hExt hFlat hR hP hH hM hT
  obtain ⟨D₂, C₂, J₂, hD₂, hC₂, hJ₂, hlower⟩ :=
    source_enlarged_reference_count_lower_all_indices hExt hFlat hR hP hH hM hT
  refine ⟨D₁ + D₂, C₁ + C₂, B, W, max J₁ J₂, add_pos hD₁ hD₂, add_pos hC₁ hC₂,
    hB, hW, hJ₁.trans (le_max_left _ _), ?_⟩
  filter_upwards [hupper, hlower, eventually_ge_atTop sourceCapacityHalfThreshold,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ))]
    with t hu hl htcap hm
  intro b w ν J hb hw hbw hν hform hJ A γ I₀ I₁ z₀ z₁
    lm₀ ls₀ lm₁ ls₁ rm₀ rs₀ rm₁ rs₁ fm₀ fs₀ fm₁ fs₁ hGW₀ hGW₁ hMix
    hγ ha₀ hc₀ ha₁ hc₁ G
  have hJu : J₁ ≤ (J : ℝ) := (le_max_left _ _).trans hJ
  have hJl : J₂ ≤ (J : ℝ) := (le_max_right _ _).trans hJ
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1.le
  have hcap₀ := (source_capacity_half_profile b t (A * diskEnergyGapRatio ^ I₀) _
    htcap ha₀ hc₀ (Finset.Subset.refl _)).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  have hcap₁ := (source_capacity_half_profile w t (A * diskEnergyGapRatio ^ I₁) _
    htcap ha₁ hc₁ (Finset.Subset.refl _)).trans (show (1 / 2 : ℝ) ≤ 1 by norm_num)
  let E := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D₁ * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C₁ * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
    2 * sourceForestQuadraticError B W 8 t
  let F := 16 * ((ν : ℝ) + 1) ^ 2 *
    (D₂ * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C₂ * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))
  have hbound := source_event_original_joint_root_bound t A γ b w I₀ I₁ ν J z₀ z₁
    hα hcap₀ hcap₁
    (sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∩
      sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν)
    G (sourceReferenceJointCountWeight t ν J) E F
  simp only [Set.mem_inter_iff, and_assoc] at hbound
  refine (hbound ?_ ?_).trans_eq ?_
  · intro h hh k l hk hlcap
    have hden := source_enlarged_path_event
      {ω | sourcePairExteriorRecord t b w ν J ω = h}
    simp only [Set.mem_setOf_eq] at hden
    have hhpath : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} := by
      rwa [hden] at hh
    have hup := hu b w ν J hb hw hbw hν hform hJu A γ I₀ I₁ z₀ z₁
      hGW₀ hGW₁ hMix hα hcap₀ hcap₁ hγ ha₀ hc₀ ha₁ hc₁ h hhpath k l hk hlcap
    rw [source_remaining_conditional_probability] at hup
    exact hup
  · intro h hh k l hk hlcap
    exact hl b w ν J hb hw hbw hν hform hJl h hh k l hk hlcap
  · congr 2
    dsimp [E, F]
    ring

end SRWTightness
