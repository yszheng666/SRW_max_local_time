import SRWTightness.GrowingOrderedRecordReferenceFunctionalAllRadii

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Every measurable projection of the full ordered tree inherits the same functional bound. -/
theorem growing_projected_record_functional_all_radii (hinput : PotentialKernelAsymptoticInput)
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
        (x : Site) {Y : Type*} [MeasurableSpace Y]
        (π : FiniteExcursionRecord WordMark n → Y) (g : Y → ℝ≥0∞)
        (hg : Measurable g) (s : Set (FiniteExcursionRecord WordMark n)) (E : ℝ),
      growingRecordRadius m n - H - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - H →
      (∀ r, r ∉ s → g (π r) = 0) → (∀ r ∈ s, finiteRecordError δ η n r ≤ E) →
      ENNReal.ofReal (Real.exp (-E)) *
          (∫⁻ y, g y ∂Measure.map π (finiteRecordReferenceMeasure ν n)) ≤
        ∫⁻ ω, g (π (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω))) ∂pathLaw ∧
      (∫⁻ ω, g (π (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω))) ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) *
          (∫⁻ y, g y ∂Measure.map π (finiteRecordReferenceMeasure ν n)) := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_record_reference_functional_all_radii hinput hHarm
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
  dsimp only
  intro n _ _ x Y _ π g hg s E hxlo hxhi hs he
  letI := finiteExcursionRecord_countable WordMark n
  rw [lintegral_map hg (measurable_of_countable π)]
  exact hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
    n x s (fun r ↦ g (π r)) E hxlo hxhi hs he

end SRWTightness
