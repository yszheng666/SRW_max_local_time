import SRWTightness.GrowingOrderedRecordComparison
import SRWTightness.RadialSingleRootComparison

open MeasureTheory
namespace SRWTightness

/-- General-buffer ordered one-root bounds preserve first entrance and final nonreturn factors. -/
theorem growing_ordered_single_root (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 8 ≤ M ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → 2 * a < m - H - 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 →
      let η : WordMark → ℝ := fun _ ↦ 2 * (W * (a + 1) / m * Real.log (m / a))
      let Q : WordMark → ℝ := fun v ↦
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real {v}
      ∀ (n : ℕ) (D : Finset Site) (x : Site),
      growingRecordExit b m H n ⊆ D → x ∈ D \ growingRecordEntrance b m H n →
      ∀ (c₁ c₂ : ℝ), 0 ≤ c₂ →
      c₁ ≤ setHitProbability D (growingRecordEntrance b m H n) x →
      (∀ y ∈ domainExitBoundary (growingRecordExit b m H n),
        c₂ ≤ competingExitMass D (growingRecordEntrance b m H n) y) →
      ∀ (r : FiniteExcursionRecord WordMark n),
      let ε := finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i)) η n r
      let p := pathLaw.real {ω | killedChildRecords D (growingRecordEntrance b m H n)
        (growingRecordExit b m H n) x
        (actualFiniteWordRecord (growingRecordEntrance b m H) (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n) ω = [r]}
      c₁ * c₂ * Real.exp (-ε) * finiteRecordReferenceWeight Q n r ≤ p ∧
        p ≤ Real.exp ε * finiteRecordReferenceWeight Q n r := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_record_probability_comparison hinput
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr
  dsimp only
  intro n D x hCD hx c₁ c₂ hc₂ hI hq r
  have hm0 : 0 < m := by linarith
  have hbase := growingRecordRadius_ge_base m hm0.le n
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hAC : growingRecordEntrance b m H n ⊆ growingRecordExit b m H n := by
    intro y hy
    simp only [growingRecordEntrance, growingRecordExit, mem_translateFinset_iff] at hy ⊢
    exact diskFinset_mono _ _ (by linarith) (by nlinarith) hy
  apply radial_single_root_comparison D (growingRecordExit b m H n) b
    (growingRecordRadius m n - H) (by linarith) hAC hCD x hx _ r c₁ c₂ _ _ hc₂
  · exact finiteRecordReferenceWeight_nonneg _ (fun _ ↦ measureReal_nonneg) n r
  · exact hI
  · exact hq
  · intro z hzlo hzhi
    exact hh b m H a K hH hm hTm hMm hsmall ha hsep hK hcap herr n z r hzlo hzhi

end SRWTightness
