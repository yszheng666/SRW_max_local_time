import SRWTightness.GrowingOrderedSingleRootEventAllRadii
import SRWTightness.SourceGeneralAnnularEntrance
import SRWTightness.SourceGeneralAnnularNonreturn
import SRWTightness.SourceGeneralRootDomains

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The source annular one-root joint comparison holds for all separated scales and buffers. -/
theorem source_general_annular_single_root_event_all_radii (hinput : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ B W T M c : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 128 ≤ M ∧ 0 < c ∧
      ∀ (b : Site) (m H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ m → T ≤ m - H → M ≤ m →
      B * H / m ≤ 1 / 4 → 0 < a → a ≤ m / 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
      ∀ R : ℝ, 32 * Real.exp 1 * m ≤ R →
      R / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ R / 3 →
      let n := sourceRootDepth R m - 1
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark n)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))],
      let η := finiteRecordError (fun i ↦ 4 * (B * H / growingRecordRadius m i))
        (fun _ : WordMark ↦ 2 * (W * (a + 1) / m * Real.log (m / a))) n
      let ν := finiteRecordReferenceMeasure
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))) n
      ∀ (s : Set (List (FiniteExcursionRecord WordMark n))) (E : ℝ),
      (∀ rs ∈ s, rs.length = 1) → (∀ r, [r] ∈ s → η r ≤ E) →
      let p := pathLaw {ω | killedChildRecords (diskFinset R) (growingRecordEntrance b m H n)
        (growingRecordExit b m H n) 0
        (actualFiniteWordRecord (growingRecordEntrance b m H) (growingRecordExit b m H)
          (firstEntranceWordOfWord (growingRecordExit b m H 0) K) n) ω ∈ s}
      ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw ν 1 s ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw ν 1 s := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_single_root_event_all_radii hinput hHarm
  obtain ⟨c₁, A₁, hc₁, hfirst⟩ := source_general_annular_entrance hinput
  obtain ⟨c₂, A₂, hc₂, hlast⟩ := source_general_annular_nonreturn hinput
  refine ⟨B, W, max T (max A₁ A₂), M, c₁ * c₂, hB, hW,
    hT.trans (le_max_left _ _), hM, mul_pos hc₁ hc₂, ?_⟩
  intro b m H a K hH hm hTm hMm hsmall ha hsep hK hcap
  intro R hscale hblo hbhi
  dsimp only
  intro _ _ _ _ s E hlen he
  have hm0 : 0 < m := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hhalf : 2 * H ≤ m := by linarith
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : 32 * m ≤ R := by nlinarith
  have hR : 0 < R := by linarith
  have hℓ := source_root_depth_pos R m hm0 hscale
  have hg := source_general_annular_geometry R m H (by linarith) hH0
    (by linarith) hbase b hblo hbhi 0
  have hrad := sourceRecordRadius_ge_terminal m hm0.le (sourceRootDepth R m) 0
    (Nat.zero_le _)
  have hc : 0 ≤ sourceRecordRadius m (sourceRootDepth R m) 0 + H := by linarith
  have hd := root_domain_and_exit_inside b _ R hc hg.2
  have hCD : growingRecordExit b m H (sourceRootDepth R m - 1) ⊆ diskFinset R := by
    rw [source_general_root_exit m H _ hℓ b]
    exact hd.1
  have hx : (0 : Site) ∈ diskFinset R \ growingRecordEntrance b m H
      (sourceRootDepth R m - 1) := by
    rw [source_general_root_entrance m H _ hℓ b]
    apply Finset.mem_sdiff.mpr
    constructor
    · apply (mem_diskFinset R 0).mpr
      simpa [disk, normSq] using sq_pos_of_pos hR
    · intro hz
      have hz' : normSq b < (sourceRecordRadius m (sourceRootDepth R m) 1 - H) ^ 2 := by
        simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq,
          zero_sub, normSq_neg] using hz
      have hb2 := Real.sq_sqrt (normSq_nonneg b)
      have hb0 := Real.sqrt_nonneg (normSq b)
      have hr1 := sourceRecordRadius_ge_terminal m hm0.le (sourceRootDepth R m) 1
        (by omega)
      nlinarith [hg.1]
  apply hh b m H a K hH hm ((le_max_left _ _).trans hTm) hMm hsmall ha hsep
    hK hcap (sourceRootDepth R m - 1) (diskFinset R) 0 hCD hx c₁ c₂ hc₁.le hc₂.le
  · rw [source_general_root_entrance m H _ hℓ b]
    exact hfirst R m H ((le_max_left _ _).trans ((le_max_right _ _).trans hTm))
      hH0 hhalf hscale b hblo hbhi
  · rw [source_general_root_exit m H _ hℓ b, source_general_root_entrance m H _ hℓ b]
    exact hlast R m H ((le_max_right _ _).trans ((le_max_right _ _).trans hTm))
      hH0 hhalf hscale b hblo hbhi
  · exact hlen
  · exact he

end SRWTightness
