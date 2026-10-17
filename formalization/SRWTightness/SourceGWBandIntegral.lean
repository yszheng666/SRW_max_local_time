import SRWTightness.SourceGWBandWindows
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- Disjoint complete windows give a lower bound for the weighted full-band event. -/
theorem source_gw_band_integral_lower (t : ℝ) (L : ℕ) (P : GeometricGWRecord → ℝ)
    (hP : Integrable P (geometricGWRecordLaw 1 L)) (hP0 : ∀ r, 0 ≤ P r) :
    (∑ i ∈ Finset.range ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊,
      ∫ r in sourceGWCoarseWindowEvent t L
        (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i + 1),
        P r ∂geometricGWRecordLaw 1 L) ≤
      ∫ r in sourceGWCoarseBandEvent t L, P r ∂geometricGWRecordLaw 1 L := by
  let n := ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊
  let S := fun i ↦ sourceGWCoarseWindowEvent t L
    (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i + 1)
  have hm : ∀ i ∈ Finset.range n, MeasurableSet (S i) :=
    fun _ _ ↦ Set.to_countable _ |>.measurableSet
  have hj : Set.Pairwise (↑(Finset.range n)) (fun i j ↦ Disjoint (S i) (S j)) := by
    intro i hi j hj hij
    exact source_gw_inner_windows_disjoint t L i j hij
  have hs : (⋃ i ∈ Finset.range n, S i) ⊆ sourceGWCoarseBandEvent t L := by
    intro r hr
    obtain ⟨i, hi, hr⟩ := Set.mem_iUnion₂.mp hr
    exact source_gw_inner_window_subset t L i (Finset.mem_range.mp hi) hr
  rw [← integral_biUnion_finset (Finset.range n) hm hj (fun _ _ ↦ hP.integrableOn)]
  exact setIntegral_mono_set hP.integrableOn (Filter.Eventually.of_forall hP0)
    (Filter.Eventually.of_forall hs)

/-- Band-restricted covering windows give an upper bound without assuming disjointness. -/
theorem source_gw_band_integral_upper (t : ℝ) (L : ℕ) (P : GeometricGWRecord → ℝ)
    (hP : Integrable P (geometricGWRecordLaw 1 L)) (hP0 : ∀ r, 0 ≤ P r) :
    (∫ r in sourceGWCoarseBandEvent t L, P r ∂geometricGWRecordLaw 1 L) ≤
      (∑ i ∈ Finset.range (⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊ + 1),
        ∫ r in sourceGWCoarseBandEvent t L ∩ sourceGWCoarseWindowEvent t L
          (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i),
          P r ∂geometricGWRecordLaw 1 L) +
        ∫ r in sourceGWCoarseBandEvent t L ∩ sourceGWCoarseWindowEvent t L
          (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t))),
          P r ∂geometricGWRecordLaw 1 L := by
  classical
  let n := ⌊Real.sqrt (sourceLowerTime (sourceLowerRadius t))⌋₊
  let B := sourceGWCoarseBandEvent t L
  let S := fun i ↦ B ∩ sourceGWCoarseWindowEvent t L
    (terminalWindowLeft (sourceLowerTime (sourceLowerRadius t)) i)
  let T := B ∩ sourceGWCoarseWindowEvent t L
    (2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)))
  have hB : MeasurableSet B := Set.to_countable _ |>.measurableSet
  have hS : ∀ i, MeasurableSet (S i) := fun _ ↦ Set.to_countable _ |>.measurableSet
  have hT : MeasurableSet T := Set.to_countable _ |>.measurableSet
  have hSI : ∀ i ∈ Finset.range (n + 1), Integrable ((S i).indicator P)
      (geometricGWRecordLaw 1 L) := fun i _ ↦ hP.indicator (hS i)
  have hTI := hP.indicator hT
  have hsumI := integrable_finsetSum (Finset.range (n + 1)) hSI
  have hSn : ∀ i r, 0 ≤ (S i).indicator P r := fun _ ↦ Set.indicator_nonneg (fun r _ ↦ hP0 r)
  have hTn : ∀ r, 0 ≤ T.indicator P r := Set.indicator_nonneg (fun r _ ↦ hP0 r)
  have hpoint : ∀ r, B.indicator P r ≤
      (∑ i ∈ Finset.range (n + 1), (S i).indicator P r) + T.indicator P r := by
    intro r
    by_cases hr : r ∈ B
    · rw [Set.indicator_of_mem hr]
      obtain hi | ht := source_gw_outer_window_cover t L r hr
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
