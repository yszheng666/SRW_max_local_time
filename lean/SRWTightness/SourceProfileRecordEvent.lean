import SRWTightness.SourceProfileRecordComparison
import SRWTightness.ActualFiniteRecordEvent

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual source profile admits joint record-event comparison under a uniform error budget. -/
theorem source_profile_record_event (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W t₀ : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      t₀ ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      let m := sourceLowerRadius t
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let δ : ℕ → ℝ := fun j ↦ 4 * (B * 14 / growingRecordRadius m j)
      let Q : Mark K → ℝ := fun v ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
          (sourceReferenceIntensity m 14)).real {v}
      ∀ n x (s : Set (FiniteExcursionRecord (Mark K) n)) (E : ℝ),
      growingRecordRadius m n - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - 14 →
      (∀ r ∈ s, finiteRecordError δ η n r ≤ E) →
      ENNReal.ofReal (Real.exp (-E)) *
          (∑' r : s, ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) ≤
        pathLaw {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω) ∈ s} ∧
      pathLaw {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω) ∈ s} ≤
        ENNReal.ofReal (Real.exp E) *
          (∑' r : s, ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) := by
  obtain ⟨B, W, t₀, hB, hW, hh⟩ := source_profile_record_comparison hinput
  refine ⟨B, W, t₀, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK
  dsimp only
  intro n x s E hxlo hxhi he
  apply actual_finite_record_event_comparison
    (growingRecordEntrance b (sourceLowerRadius t) 14)
    (growingRecordExit b (sourceLowerRadius t) 14) (wordOccupationMark K) n x
    _ _ _ (fun _ ↦ measureReal_nonneg) s E he
  intro r hr
  exact hh b t a K ht ha hcut hK n x r hxlo hxhi

end SRWTightness
