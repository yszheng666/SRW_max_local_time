import SRWTightness.SourceAnnularCoarseEvent
import SRWTightness.AuxiliaryRelativeComparison

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Actual source coarse-record comparison includes a common independent auxiliary space. -/
theorem source_annular_coarse_auxiliary (Ξ : Type*) [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsFiniteMeasure ν] (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → MarkedGWTreeInput (Mark K) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      let F := killedChildRecords (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
        (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
        (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
          (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
      ∀ S : Set (List (FiniteExcursionRecord (Mark K) n) × Ξ), MeasurableSet S →
        (∀ p ∈ S, p.1.length = 1) →
        (∀ r y, ([r], y) ∈ S → ∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight (finiteRecordPopulationList n r) j ≤
            4 + sourceBarrierSlope t * j -
              (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
      let E := sourceForestQuadraticError B W 8 t
      let p := (pathLaw.prod ν).real ((fun p ↦ (F p.1, p.2)) ⁻¹' S)
      let q := ((independentForestLaw μ 1).prod ν).real S
      c * Real.exp (-E) * q ≤ p ∧ p ≤ Real.exp E * q := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ := source_annular_coarse_event_comparison hinput
  refine ⟨B, W, c, max T sourceCapacityHalfThreshold, hB, hW, hc, ?_⟩
  intro b t a K ht ha hcut hK hmarked hblo hbhi ℓ hℓ inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro S hS hlen hcoarse
  let n := ℓ - 1
  let μ := finiteRecordReferenceMeasure
    (referenceMarkLaw
      (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
  let F := killedChildRecords (diskFinset (Real.exp t))
    (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
    (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
    (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
      (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n)
  let E := sourceForestQuadraticError B W 8 t
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_right _ _).trans ht
  letI := finiteExcursionRecord_countable (Mark K) n
  letI := (source_profile_reference_measure b t a K hmarked htcap ha hcut hK n).1
  have hF : Measurable F := measurable_killedChildRecords _ _ _ _ _
  apply auxiliary_relative_comparison pathLaw (independentForestLaw μ 1) ν
    (c * Real.exp (-E)) (Real.exp E) ((fun p ↦ (F p.1, p.2)) ⁻¹' S) S
    (hS.preimage ((hF.comp measurable_fst).prodMk measurable_snd)) hS
  apply Filter.Eventually.of_forall
  intro y
  let s := (fun rs ↦ (rs, y)) ⁻¹' S
  have hb := hh b t a K ((le_max_left _ _).trans ht) ha hcut hK hmarked hblo hbhi ℓ hℓ s
    (fun rs hrs ↦ hlen (rs, y) hrs) (fun r hr ↦ hcoarse r y hr)
  have hlow := ENNReal.toReal_mono (measure_ne_top pathLaw _) hb.1
  have hupp := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (independentForestLaw μ 1) s)) hb.2
  change (ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw μ 1 s).toReal ≤
    (pathLaw (F ⁻¹' s)).toReal at hlow
  change (pathLaw (F ⁻¹' s)).toReal ≤
    (ENNReal.ofReal (Real.exp E) * independentForestLaw μ 1 s).toReal at hupp
  have hcE : 0 ≤ c * Real.exp (-E) := mul_nonneg hc.le (Real.exp_nonneg _)
  have hpre : F ⁻¹' s = (fun x ↦ (x, y)) ⁻¹' ((fun p ↦ (F p.1, p.2)) ⁻¹' S) := by
    ext ω
    rfl
  rw [hpre] at hlow hupp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcE] at hlow
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg E)] at hupp
  exact ⟨hlow, hupp⟩

end SRWTightness
