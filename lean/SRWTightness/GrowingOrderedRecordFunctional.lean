import SRWTightness.GrowingOrderedRecordComparison
import SRWTightness.ActualFiniteRecordEvent
import SRWTightness.KilledRecordFunctional

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Arbitrary admissible buffers admit comparison of all supported ordered-record functionals. -/
theorem growing_ordered_record_functional_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 8 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → 2 * a < m - H - 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 →
      let η : WordMark → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let δ : ℕ → ℝ := fun j ↦ 4 * (B * H / growingRecordRadius m j)
      let Q : WordMark → ℝ := fun v ↦
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real {v}
      ∀ n x (s : Set (FiniteExcursionRecord WordMark n))
        (g : FiniteExcursionRecord WordMark n → ℝ≥0∞) (E : ℝ),
      growingRecordRadius m n - H - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - H →
      (∀ r, r ∉ s → g r = 0) → (∀ r ∈ s, finiteRecordError δ η n r ≤ E) →
      ENNReal.ofReal (Real.exp (-E)) *
          (∑' r, g r * ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) ≤
        ∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω)) ∂pathLaw ∧
      (∫⁻ ω, g (actualFiniteWordRecord (growingRecordEntrance b m H)
          (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x
          (killedPathWord (growingRecordExit b m H n) x ω)) ∂pathLaw) ≤
        ENNReal.ofReal (Real.exp E) *
          (∑' r, g r * ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_ordered_record_probability_comparison hinput
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr
  dsimp only
  intro n x s g E hxlo hxhi hg he
  letI := finiteExcursionRecord_countable WordMark n
  apply killed_record_functional_exponential (growingRecordExit b m H n) x
    (actualFiniteWordRecord (growingRecordEntrance b m H) (growingRecordExit b m H)
      (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n x)
    _ _ s g E (finiteRecordReferenceWeight_nonneg _ (fun _ ↦ measureReal_nonneg) n) hg he
  intro r hr
  exact hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr n x r hxlo hxhi

end SRWTightness
