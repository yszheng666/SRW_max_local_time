import SRWTightness.SourceCommonPairEndpoint
import SRWTightness.SourceGWCoarseEvent

open MeasureTheory
namespace SRWTightness

/-- The source coarse barrier after generation nu, with its original terminal unit window. -/
def sourceContinuationWindow (t : ℝ) (ν L : ℕ) (q : ℝ) : Set GeometricGWRecord :=
  {r | (∀ i : ℕ, 0 < i → i ≤ L →
      geometricGWHeight r i ≤ sourceCommonPairEndpoint t (ν + i)) ∧
    geometricGWHeight r L ∈ Set.Ico (sourceTerminalRoot t q) (sourceTerminalRoot t q + 1)}

/-- The shifted source window lies in the external upper-barrier event at the true initial height. -/
theorem source_continuation_window_subset (t : ℝ) (ν L : ℕ) (q : ℝ) (hL : 0 < L)
    (hN : (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ))
    (hT : (ν : ℝ) + (L : ℝ) ≤ sourceTotalTime t) :
    sourceContinuationWindow t ν L q ⊆ gwUpperBarrierEvent L
      (4 + sourceBarrierSlope t * ν)
      (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ))
      (sourceTerminalRoot t q) 1 1 (1 / 10) := by
  intro r hr
  refine ⟨?_, ⟨hr.2.1, hr.2.2.le⟩⟩
  intro i hi hiL
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hiL' : (i : ℝ) ≤ L := by exact_mod_cast hiL.le
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hν0 : (0 : ℝ) ≤ ν := Nat.cast_nonneg _
  have hbase : 0 ≤ min ((ν : ℝ) + i) (sourceTotalTime t - ((ν : ℝ) + i)) := by
    apply le_min <;> linarith
  have hcurve := Real.rpow_nonneg hbase (2 / 5 : ℝ)
  have hupper : 0 ≤ gwBarrierCurvature (1 / 2 - 1 / 10) i L :=
    Real.rpow_nonneg (le_min hi0 (by linarith)) _
  have hline : gwBarrierLine (4 + sourceBarrierSlope t * ν)
      (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) i L =
      4 + sourceBarrierSlope t * ((ν : ℝ) + i) := by
    unfold gwBarrierLine
    rw [← hN]
    field_simp
    <;> ring
  have hh := hr.1 i hi hiL.le
  simp only [sourceCommonPairEndpoint, Nat.cast_add] at hh
  rw [hline, one_mul]
  linarith

/-- The existing upper GW input bounds a shifted source window for any positive initial population. -/
theorem source_continuation_window_upper (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t q : ℝ) (ν L k : ℕ), 0 < L → 0 < k →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) →
      (ν : ℝ) + (L : ℝ) ≤ sourceTotalTime t →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 * L →
      Real.sqrt 2 ≤ sourceTerminalRoot t q → sourceTerminalRoot t q ≤ 4 * L →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
      sourceTerminalRoot t q ≤ 4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) →
      (geometricGWRecordLaw k L).real (sourceContinuationWindow t ν L q) ≤
        C * gwBarrierPrefactor L (Real.sqrt (2 * (k : ℝ))) (sourceTerminalRoot t q)
          (4 + sourceBarrierSlope t * ν)
          (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) *
          Real.sqrt (Real.sqrt (2 * (k : ℝ)) / (sourceTerminalRoot t q * L)) := by
  obtain ⟨C, hC, hu⟩ := hGW 1 1 4 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro t q ν L k hL hk hN hT hx hy0 hy hxA hyB
  exact (measureReal_mono (source_continuation_window_subset t ν L q hL hN hT)).trans
    (hu L k _ _ _ hL hk hx hy0 hy hxA hyB)

end SRWTightness
