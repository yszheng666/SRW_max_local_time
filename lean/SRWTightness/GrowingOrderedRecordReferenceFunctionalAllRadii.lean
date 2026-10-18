import SRWTightness.GrowingOrderedRecordFunctionalAllRadii
import SRWTightness.FiniteRecordReferenceFunctional

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The general ordered-record comparison is an inequality of actual and reference expectations. -/
theorem growing_ordered_record_reference_functional_all_radii
    (hinput : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 128 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → a ≤ m / 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      let η : WordMark → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let δ : ℕ → ℝ := fun j ↦ 4 * (B * H / growingRecordRadius m j)
      let ν := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))
      ∀ (n : ℕ) [MeasurableSpace (FiniteExcursionRecord WordMark n)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
        (x : Site) (s : Set (FiniteExcursionRecord WordMark n))
        (g : FiniteExcursionRecord WordMark n → ℝ≥0∞) (E : ℝ),
      growingRecordRadius m n - H - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - H →
      (∀ r, r ∉ s → g r = 0) → (∀ r ∈ s, finiteRecordError δ η n r ≤ E) →
      ENNReal.ofReal (Real.exp (-E)) *
          (∫⁻ r, g r ∂finiteRecordReferenceMeasure ν n) ≤
        ∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω)) ∂pathLaw ∧
      (∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω)) ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) *
          (∫⁻ r, g r ∂finiteRecordReferenceMeasure ν n) := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_record_functional_comparison_all_radii hinput hHarm
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
  dsimp only
  intro n _ _ x s g E hxlo hxhi hg he
  simpa only [finite_record_reference_functional] using
    hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap n x s g E hxlo hxhi hg he

end SRWTightness
