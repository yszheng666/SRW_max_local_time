import SRWTightness.GrowingOrderedForestUpperAllRadii
import SRWTightness.SourceGeneralRootReturnUniversal
import SRWTightness.SourceGeneralAnnularGeometry
import SRWTightness.SourceGeneralRootLevelDomains
import SRWTightness.RootRadialLayerInside

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- General source forests have the reciprocal-level return factor
without exterior-kernel inputs. -/
theorem source_annular_forest_upper_full (hinput : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ B W T M A : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 128 ≤ M ∧ 2 ≤ A ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      8 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → a ≤ m / 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      ∀ R : ℝ, 32 * m ≤ R →
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      let ℓ := sourceRootDepth R m
      A ≤ m - H →
      ∀ k : ℕ, k < ℓ →
      let n := ℓ - (k + 1)
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark n)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))],
      let F := actualFiniteWordRecord (growingRecordEntrance b m H)
        (growingRecordExit b m H) (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n
      let η := finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
        (fun _ : WordMark ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n
      let ν := finiteRecordReferenceMeasure
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))) n
      ∀ (j : ℕ), 1 ≤ j → ∀ (s : Set (List (FiniteExcursionRecord WordMark n))) (E : ℝ),
      (∀ rs ∈ s, rs.length = j → (rs.map η).sum ≤ E) →
      pathLaw.real {ω |
        (killedChildRecords (diskFinset R) (growingRecordEntrance b m H n)
          (growingRecordExit b m H n) 0 F ω).length = j ∧
        killedChildRecords (diskFinset R) (growingRecordEntrance b m H n)
          (growingRecordExit b m H n) 0 F ω ∈ s} ≤
        (1 - 1 / ((k : ℝ) + sourceRootReturnShift)) ^ (j - 1) * Real.exp E *
          (independentForestLaw ν j).real s := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ := growing_ordered_forest_upper_all_radii hinput hHarm
  obtain ⟨A, hA, hreturn⟩ := source_general_root_return_universal hinput
  refine ⟨B, W, T, M, A, hB, hW, hT, hM, hA, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap R hscale hblo hbhi
  dsimp only
  intro hlarge k hk _ _ _ _ j hj s E he
  have hm0 : 0 < m := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hR : 0 < R := by linarith
  have hC : 1 ≤ sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  have hden : 0 < (k : ℝ) + sourceRootReturnShift := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hρ : 0 ≤ 1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hh' := (div_le_one hden).mpr (show (1 : ℝ) ≤ k + sourceRootReturnShift by linarith)
    linarith
  have hu : growingRecordRadius m (sourceRootDepth R m - (k + 1)) - H =
      sourceRecordRadius m (sourceRootDepth R m) (k + 1) - H := by
    rw [← source_single_root_radius m _ k hk]
  have hv : Real.exp 1 * growingRecordRadius m (sourceRootDepth R m - (k + 1)) + H =
      sourceRecordRadius m (sourceRootDepth R m) k + H := by
    rw [← source_single_root_radius m _ k hk, ← sourceRecordRadius_successor m _ k]
  have hg := source_general_annular_geometry R m H (by linarith) hH0 (by linarith)
    hscale b hblo hbhi k
  have hrad := sourceRecordRadius_ge_terminal m hm0.le (sourceRootDepth R m) k hk.le
  have hc : 0 ≤ sourceRecordRadius m (sourceRootDepth R m) k + H := by linarith
  have hbR : normSq b ≤ R ^ 2 := by
    have hb0 := Real.sqrt_nonneg (normSq b)
    have hb2 := Real.sq_sqrt (normSq_nonneg b)
    nlinarith
  apply hh b m H a K (by linarith) hm hTm hMm hsmall ha hsep hK hcap
    (sourceRootDepth R m - (k + 1)) R (1 - 1 / ((k : ℝ) + sourceRootReturnShift)) hρ
  · simpa only [hv] using hg.2
  · simpa only [hu] using hg.1
  · intro y hylo hyhi
    rw [hv] at hylo hyhi
    have hyD := root_radial_layer_inside b _ R hc hg.2 y hyhi
    have hr := hreturn R m H hm0 hH (by linarith) hscale hlarge k hk b y hbR hyD hylo
    simpa only [hu] using hr
  · exact hj
  · exact he

end SRWTightness
