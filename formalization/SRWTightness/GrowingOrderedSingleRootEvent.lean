import SRWTightness.GrowingOrderedSingleRoot
import SRWTightness.SingleRootEventComparison
import SRWTightness.MarkedTreeNormalization

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Arbitrary ordered one-root joint events inherit both bounds with their nonreturn factor. -/
theorem growing_ordered_single_root_event (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 8 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → 2 * a < m - H - 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 →
      ∀ (n : ℕ) [MeasurableSpace (FiniteExcursionRecord WordMark n)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))],
      let η := finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
        (fun _ : WordMark ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n
      let ν := finiteRecordReferenceMeasure
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))) n
      ∀ (D : Finset Site) (x : Site),
      growingRecordExit b m H n ⊆ D → x ∈ D \ growingRecordEntrance b m H n →
      ∀ (c₁ c₂ : ℝ), 0 ≤ c₁ → 0 ≤ c₂ →
      c₁ ≤ setHitProbability D (growingRecordEntrance b m H n) x →
      (∀ y ∈ domainExitBoundary (growingRecordExit b m H n),
        c₂ ≤ competingExitMass D (growingRecordEntrance b m H n) y) →
      ∀ (s : Set (List (FiniteExcursionRecord WordMark n))) (E : ℝ),
      (∀ rs ∈ s, rs.length = 1) → (∀ r, [r] ∈ s → η r ≤ E) →
      let p := pathLaw {ω | killedChildRecords D (growingRecordEntrance b m H n)
        (growingRecordExit b m H n) x
        (actualFiniteWordRecord (growingRecordEntrance b m H) (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n) ω ∈ s}
      ENNReal.ofReal (c₁ * c₂ * Real.exp (-E)) * independentForestLaw ν 1 s ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw ν 1 s := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_ordered_single_root hinput
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr n _ _ _ _
  dsimp only
  intro D x hCD hx c₁ c₂ hc₁ hc₂ hI hq s E hlen he
  have hm0 : 0 < m := by linarith
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hα : 0 ≤ (2 / Real.pi) *
      Real.log ((Real.exp 1 * m + H) / (m - H)) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    apply (one_le_div (by linarith : 0 < m - H)).mpr
    nlinarith
  letI := finiteExcursionRecord_countable WordMark n
  letI := referenceWordMarkLaw_probability
    (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
    ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) hα (by linarith)
  letI := finite_record_reference_measure_probability_internal
    (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))) n
  apply single_root_event_comparison pathLaw _ _ _ (c₁ * c₂) E
    (mul_nonneg hc₁ hc₂) s hlen ?_ he ?_
  · intro rs hrs
    exact measurableSet_killedChildRecords_eq _ _ _ _ _ rs
  · intro r hr
    rw [finiteRecordReferenceMeasure_real_singleton]
    exact hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr
      n D x hCD hx c₁ c₂ hc₂ hI hq r

end SRWTightness
