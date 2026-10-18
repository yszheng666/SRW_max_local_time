import SRWTightness.SourceProfileRecordComparison
import SRWTightness.ActualFiniteRecordEvent
import SRWTightness.KilledRecordFunctional

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The actual source profile admits nonnegative record-functional comparison under a uniform error budget. -/
theorem source_profile_record_functional (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W t₀ : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      t₀ ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      let m := sourceLowerRadius t
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let δ : ℕ → ℝ := fun j ↦ 4 * (B * 14 / growingRecordRadius m j)
      let Q : Mark K → ℝ := fun v ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
          (sourceReferenceIntensity m 14)).real {v}
      ∀ n x (s : Set (FiniteExcursionRecord (Mark K) n))
        (g : FiniteExcursionRecord (Mark K) n → ℝ≥0∞) (E : ℝ),
      growingRecordRadius m n - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - 14 →
      (∀ r, r ∉ s → g r = 0) →
      (∀ r ∈ s, finiteRecordError δ η n r ≤ E) →
      ENNReal.ofReal (Real.exp (-E)) *
          (∑' r, g r * ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) ≤
        ∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω)) ∂pathLaw ∧
      (∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω)) ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) *
          (∑' r, g r * ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) := by
  obtain ⟨B, W, t₀, hB, hW, hh⟩ := source_profile_record_comparison hinput
  refine ⟨B, W, t₀, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK
  dsimp only
  intro n x s g E hxlo hxhi hg he
  letI := finiteExcursionRecord_countable (Mark K) n
  apply killed_record_functional_exponential
    (growingRecordExit b (sourceLowerRadius t) 14 n) x
    (actualFiniteWordRecord (growingRecordEntrance b (sourceLowerRadius t) 14)
      (growingRecordExit b (sourceLowerRadius t) 14) (wordOccupationMark K) n x)
    _ _ s g E (finiteRecordReferenceWeight_nonneg _ (fun _ ↦ measureReal_nonneg) n) hg he
  intro r hr
  exact hh b t a K ht ha hcut hK n x r hxlo hxhi

end SRWTightness
