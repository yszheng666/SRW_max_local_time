import SRWTightness.SourceContinuationWindowIntegral
import SRWTightness.TerminalRightWindows

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- The shifted coarse barriers with the original terminal deficit band. -/
def sourceContinuationBand (t : ℝ) (ν L : ℕ) : Set GeometricGWRecord :=
  {r | (∀ i : ℕ, 0 < i → i ≤ L →
      geometricGWHeight r i ≤ sourceCommonPairEndpoint t (ν + i)) ∧
    sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L ∈
      Set.Icc (Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
        (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))}

/-- The existing terminal covering windows cover every shifted coarse-band record. -/
theorem source_continuation_outer_window_cover (t : ℝ) (ν L : ℕ) (r : GeometricGWRecord)
    (hr : r ∈ sourceContinuationBand t ν L) :
    (∃ i ≤ ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊,
      r ∈ sourceContinuationWindow t ν L
        (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i)) ∨
    r ∈ sourceContinuationWindow t ν L
      (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))) := by
  obtain h | h := terminal_right_outer_cover _ _ hr.2
  · obtain ⟨i, hi, _, hq⟩ := h
    left
    refine ⟨i, hi, hr.1, ?_⟩
    unfold sourceTerminalRoot
    exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
  · right
    refine ⟨hr.1, ?_⟩
    unfold sourceTerminalRoot
    exact ⟨by linarith [h.2.2], by linarith [h.2.1]⟩

/-- Band-restricted covering windows give an upper bound without assuming disjointness. -/
theorem source_continuation_band_integral_upper (t : ℝ) (ν L k : ℕ) (P : GeometricGWRecord → ℝ)
    (hP : Integrable P (geometricGWRecordLaw k L)) (hP0 : ∀ r, 0 ≤ P r) :
    (∫ r in sourceContinuationBand t ν L, P r ∂geometricGWRecordLaw k L) ≤
      (∑ i ∈ Finset.range (⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊ + 1),
        ∫ r in sourceContinuationBand t ν L ∩ sourceContinuationWindow t ν L
          (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i),
          P r ∂geometricGWRecordLaw k L) +
        ∫ r in sourceContinuationBand t ν L ∩ sourceContinuationWindow t ν L
          (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))),
          P r ∂geometricGWRecordLaw k L := by
  classical
  let n := ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊
  let B := sourceContinuationBand t ν L
  let S := fun i ↦ B ∩ sourceContinuationWindow t ν L
    (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i)
  let T := B ∩ sourceContinuationWindow t ν L
    (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
  have hB : MeasurableSet B := Set.to_countable _ |>.measurableSet
  have hS : ∀ i, MeasurableSet (S i) := fun _ ↦ Set.to_countable _ |>.measurableSet
  have hT : MeasurableSet T := Set.to_countable _ |>.measurableSet
  have hSI : ∀ i ∈ Finset.range (n + 1), Integrable ((S i).indicator P)
      (geometricGWRecordLaw k L) := fun i _ ↦ hP.indicator (hS i)
  have hTI := hP.indicator hT
  have hsumI := integrable_finsetSum (Finset.range (n + 1)) hSI
  have hSn : ∀ i r, 0 ≤ (S i).indicator P r := fun _ ↦ Set.indicator_nonneg (fun r _ ↦ hP0 r)
  have hTn : ∀ r, 0 ≤ T.indicator P r := Set.indicator_nonneg (fun r _ ↦ hP0 r)
  have hpoint : ∀ r, B.indicator P r ≤
      (∑ i ∈ Finset.range (n + 1), (S i).indicator P r) + T.indicator P r := by
    intro r
    by_cases hr : r ∈ B
    · rw [Set.indicator_of_mem hr]
      obtain hi | ht := source_continuation_outer_window_cover t ν L r hr
      · obtain ⟨i, hi, hri⟩ := hi
        have his : r ∈ S i := ⟨hr, hri⟩
        have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) ↦ hSn j r)
          (show i ∈ Finset.range (n + 1) from Finset.mem_range.mpr (by omega))
        rw [Set.indicator_of_mem his] at hh
        linarith [hTn r]
      · have hrt : r ∈ T := ⟨hr, ht⟩
        rw [Set.indicator_of_mem hrt]
        exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ ↦ hSn i r))
    · rw [Set.indicator_of_notMem hr]
      exact add_nonneg (Finset.sum_nonneg (fun i _ ↦ hSn i r)) (hTn r)
  have hh := integral_mono (hP.indicator hB) (hsumI.add hTI) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hsumI hTI, integral_finsetSum _ hSI,
    integral_indicator hB, integral_indicator hT] at hh
  simp_rw [integral_indicator (hS _)] at hh
  exact hh

end SRWTightness
