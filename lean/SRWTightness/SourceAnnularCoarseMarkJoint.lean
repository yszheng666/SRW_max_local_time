import SRWTightness.SourceAnnularCoarseEvent
import SRWTightness.SourceProfileReferenceJoint
import SRWTightness.SingleRootReferenceEvent

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Actual coarse-and-terminal-record probabilities compare to the independent-mark GW integral. -/
theorem source_annular_coarse_mark_joint (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      ∀ [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))],
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) → MarkedGWJointInput (Mark K) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      ∀ s : Set GeometricGWRecord,
        (∀ g ∈ s, ∀ j : ℕ, 0 < j → j ≤ n →
          geometricGWHeight g j ≤ 4 + sourceBarrierSlope t * j -
            (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ)) →
      ∀ F : GeometricGWRecord → Set (List (Mark K)),
      let S := {rs | ∃ r : FiniteExcursionRecord (Mark K) n,
        (finiteRecordPopulationList n r ∈ s ∧
          finiteRecordLeaves n r ∈ F (finiteRecordPopulationList n r)) ∧ rs = [r]}
      let ν := referenceMarkLaw
        (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
        (sourceReferenceIntensity (sourceLowerRadius t) 14)
      let Q := ∫⁻ g in s, independentForestLaw ν (geometricGWPopulation g n) (F g)
        ∂geometricGWRecordLaw 1 n
      let E := sourceForestQuadraticError B W 8 t
      let p := pathLaw {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ S}
      ENNReal.ofReal (c * Real.exp (-E)) * Q ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * Q := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ := source_annular_coarse_event_comparison hinput
  refine ⟨B, W, c, max T sourceCapacityHalfThreshold, hB, hW, hc, ?_⟩
  intro b t a K instMark instMarkSingle ht ha hcut hK hjoint hblo hbhi ℓ hℓ
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro s hs F
  let n := ℓ - 1
  let ν := referenceMarkLaw
    (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
    (sourceReferenceIntensity (sourceLowerRadius t) 14)
  let A : Set (FiniteExcursionRecord (Mark K) n) :=
    {r | finiteRecordPopulationList n r ∈ s ∧
      finiteRecordLeaves n r ∈ F (finiteRecordPopulationList n r)}
  let S : Set (List (FiniteExcursionRecord (Mark K) n)) := {rs | ∃ r ∈ A, rs = [r]}
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_right _ _).trans ht
  have hmarked := markedGWJoint_population hjoint
  letI := finiteExcursionRecord_countable (Mark K) n
  letI := (source_profile_reference_measure b t a K hmarked htcap ha hcut hK n).1
  have hlen : ∀ rs ∈ S, rs.length = 1 := by
    rintro rs ⟨r, hr, rfl⟩
    rfl
  have hcoarse : ∀ r, [r] ∈ S → ∀ j : ℕ, 0 < j → j ≤ n →
      geometricGWHeight (finiteRecordPopulationList n r) j ≤
        4 + sourceBarrierSlope t * j -
          (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) := by
    intro r hr
    obtain ⟨v, hv, he⟩ := hr
    have hrv : r = v := by simpa using he
    subst v
    exact hs _ hv.1
  have hb := hh b t a K ((le_max_left _ _).trans ht) ha hcut hK hmarked
    hblo hbhi ℓ hℓ S hlen hcoarse
  have hj := source_profile_reference_joint b t a K hjoint htcap ha hcut hK n s F
  have hq : independentForestLaw (finiteRecordReferenceMeasure ν n) 1 S =
      ∫⁻ g in s, independentForestLaw ν (geometricGWPopulation g n) (F g)
        ∂geometricGWRecordLaw 1 n := by
    rw [independentForestLaw_single_root_event]
    exact hj
  rw [hq] at hb
  exact hb

end SRWTightness
