import SRWTightness.DiskForestReferenceUpper
import SRWTightness.SourceProfileSingleRoot
import SRWTightness.SourceProfileReturnRate
import SRWTightness.SourceProfileReferenceMeasure

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual source forest is bounded by independent reference trees with the source return rate. -/
theorem source_profile_forest_upper (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧
    ∀ (b : Site) (t a R : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → MarkedGWTreeInput (Mark K) →
      32 * sourceLowerRadius t ≤ R → R ≤ Real.exp t →
      ∀ (ℓ k : ℕ), ℓ = sourceRootDepth R (sourceLowerRadius t) → k < ℓ →
      sourceRecordRadius (sourceLowerRadius t) ℓ (k + 1) - 14 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) + (sourceRecordRadius (sourceLowerRadius t) ℓ k + 14) + 1 < R →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - (k + 1)))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - (k + 1)))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - (k + 1))))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - (k + 1))))],
      let n := ℓ - (k + 1)
      let η := finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
        (fun _ : Mark K ↦ 2 * (W * (a + 1) / sourceLowerRadius t *
          Real.log (sourceLowerRadius t / a))) n
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      ∀ (j : ℕ), 1 ≤ j → ∀ (s : Set (List (FiniteExcursionRecord (Mark K) n))) (E : ℝ),
        (∀ rs ∈ s, rs.length = j) → (∀ rs ∈ s, (rs.map η).sum ≤ E) →
        pathLaw {ω | killedChildRecords (diskFinset R)
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b k)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b k) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s} ≤
          ENNReal.ofReal ((1 - 1 / ((k : ℝ) + sourceRootReturnShift)) ^ (j - 1) *
            Real.exp E) * independentForestLaw μ j s := by
  obtain ⟨B, W, T₁, hB, hW, hsingle⟩ := source_profile_single_root_comparison hinput
  obtain ⟨T₂, hreturn⟩ := source_profile_return_rate hinput
  refine ⟨B, W, max (max T₁ T₂) (max (sourceScaleThreshold 4) sourceCapacityHalfThreshold),
    hB, hW, ?_⟩
  intro b t a R K ht ha hcut hK hmarked hscale htime ℓ k hℓ hk hout hfit
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro j hj s E hlen herr
  have ht₁ : T₁ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have ht₂ : T₂ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have htbase : sourceScaleThreshold 4 ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htcap : sourceCapacityHalfThreshold ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) hm.le ℓ (k + 1)
    (by omega)
  have hmono := sourceRecordRadius_antitone (sourceLowerRadius t) hm.le ℓ (Nat.le_succ k)
  have hc : 0 ≤ sourceRecordRadius (sourceLowerRadius t) ℓ k + 14 := by linarith
  have hb := Real.sqrt_nonneg (normSq b)
  have hR : 0 < R := by linarith
  have hbR : normSq b ≤ R ^ 2 := by
    have hs := Real.sq_sqrt (normSq_nonneg b)
    nlinarith
  have hshift : 1 ≤ (k : ℝ) + sourceRootReturnShift := by
    have hlog32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hρ : 0 ≤ 1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hshift
    simpa only [one_div_one] using sub_nonneg.mpr hh
  letI := finiteExcursionRecord_countable (Mark K) (ℓ - (k + 1))
  letI := (source_profile_reference_measure b t a K hmarked htcap ha hcut hK
    (ℓ - (k + 1))).1
  have hbuffer : sourceRecordBuffer 1 = 14 := by norm_num [sourceRecordBuffer]
  simp only [sourceEntranceDomain, sourceExitDomain, hbuffer]
  apply disk_forest_reference_upper R b
    (sourceRecordRadius (sourceLowerRadius t) ℓ (k + 1) - 14)
    (sourceRecordRadius (sourceLowerRadius t) ℓ k + 14)
    (by linarith) (by linarith) hfit hout _ _ hρ _ _ ?_ ?_ j hj s E hlen herr
  · intro y hylo hyhi
    have hyR : y ∈ diskFinset R := by
      have hs := Real.sq_sqrt (normSq_nonneg (y - b))
      have hn := Real.sqrt_nonneg (normSq (y - b))
      have hh := normSq_add_bound b (y - b) hb (by linarith :
        0 ≤ sourceRecordRadius (sourceLowerRadius t) ℓ k + 14 + 1)
        (le_of_eq (normSq_eq_sq_sqrt b)) (by nlinarith)
      rw [show b + (y - b) = y by abel] at hh
      apply (mem_diskFinset R y).mpr
      exact hh.trans_lt ((sq_lt_sq₀ (by positivity) hR.le).mpr (by linarith))
    have hh := hreturn t ht₂ R hscale htime k (hℓ ▸ hk) b y hbR hyR
    simpa only [← hℓ, sourceEntranceDomain, hbuffer] using hh (by simpa [← hℓ] using hylo)
  · intro z hzlo hzhi r
    rw [finiteRecordReferenceMeasure_real_singleton]
    have hh := (hsingle b t a K ht₁ ha hcut hK ℓ k hk z r hzlo hzhi).2
    simpa only [sourceExitDomain, hbuffer, sourceReferenceIntensity] using hh

end SRWTightness
