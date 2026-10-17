import SRWTightness.GrowingOrderedRecordComparisonAllRadii
import SRWTightness.OrderedLiteralForestComparison

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Arbitrary-buffer ordered root comparisons give joint forest bounds for actual killed walks. -/
theorem growing_ordered_forest_upper_all_radii (hinput : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 128 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → a ≤ m / 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      ∀ (n : ℕ) [MeasurableSpace (FiniteExcursionRecord WordMark n)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))],
      let u := growingRecordRadius m n - H
      let v := Real.exp 1 * growingRecordRadius m n + H
      let F := actualFiniteWordRecord (growingRecordEntrance b m H)
        (growingRecordExit b m H) (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n
      let η := finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
        (fun _ : WordMark ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n
      let ν := finiteRecordReferenceMeasure
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))) n
      ∀ (R ρ : ℝ), 0 ≤ ρ →
      Real.sqrt (normSq b) + v + 1 < R → u ≤ Real.sqrt (normSq b) →
      (∀ y : Site, v ≤ Real.sqrt (normSq (y - b)) →
        Real.sqrt (normSq (y - b)) ≤ v + 1 →
        setHitProbability (diskFinset R) (translateFinset b (diskFinset u)) y ≤ ρ) →
      ∀ (j : ℕ), 1 ≤ j → ∀ (s : Set (List (FiniteExcursionRecord WordMark n))) (E : ℝ),
      (∀ rs ∈ s, rs.length = j → (rs.map η).sum ≤ E) →
      pathLaw.real {ω |
        (killedChildRecords (diskFinset R) (growingRecordEntrance b m H n)
          (growingRecordExit b m H n) 0 F ω).length = j ∧
        killedChildRecords (diskFinset R) (growingRecordEntrance b m H n)
          (growingRecordExit b m H n) 0 F ω ∈ s} ≤
        ρ ^ (j - 1) * Real.exp E * (independentForestLaw ν j).real s := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_record_probability_comparison_all_radii hinput hHarm
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
  intro n _ _ _ _
  dsimp only
  intro R ρ hρ hfit hout hreturn j hj s E he
  have hm0 : 0 < m := by linarith
  have hbase := growingRecordRadius_ge_base m hm0.le n
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hα : 0 ≤ (2 / Real.pi) *
      Real.log ((Real.exp 1 * m + H) / (m - H)) := by
    apply mul_nonneg (by positivity)
    apply Real.log_nonneg
    apply (one_le_div (by linarith : 0 < m - H)).mpr
    nlinarith
  apply ordered_literal_forest_upper _ K _ hα (by linarith) n R b
    (growingRecordRadius m n - H) (Real.exp 1 * growingRecordRadius m n + H)
    (by linarith) (by nlinarith) hfit hout _ ρ hρ _ hreturn
  · intro z hzlo hzhi r
    exact (hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap n z r hzlo hzhi).2
  · exact hj
  · exact he

end SRWTightness
