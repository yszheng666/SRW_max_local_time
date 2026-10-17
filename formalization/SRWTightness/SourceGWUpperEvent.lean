import SRWTightness.SourceGWCoarseEvent

open Filter
open scoped Topology

namespace SRWTightness

/-- The full source coarse event is contained in the external upper-barrier event. -/
theorem source_gw_coarse_subset_upper :
    ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, sourceGWCoarseWindowEvent t L q ⊆
        gwUpperBarrierEvent L 4
          (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ))
          (sourceTerminalRoot t q) 1 1 (1 / 10) := by
  filter_upwards [source_gw_natural_generation,
    source_lower_time_eventually_ge 1] with t hNat hd
  let L := (sourceCoarseGeneration t).toNat
  have hL : (L : ℝ) = (sourceCoarseGeneration t : ℝ) := hNat.1
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hNat.2
  have htime : sourceTotalTime t = (L : ℝ) + sourceLowerTime (sourceLowerRadius t) := by
    unfold sourceTotalTime
    rw [hL]
  dsimp only
  intro q r hr
  refine ⟨?_, ⟨hr.2.1, hr.2.2.le⟩⟩
  intro j hj hjL
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hjL' : (j : ℝ) ≤ L := by exact_mod_cast hjL.le
  have hbase : 0 ≤ min (j : ℝ) (sourceTotalTime t - j) := by
    rw [htime]
    exact le_min hj0 (by linarith)
  have hs := Real.rpow_nonneg hbase (2 / 5 : ℝ)
  have hc : 0 ≤ gwBarrierCurvature (1 / 2 - 1 / 10) j L :=
    Real.rpow_nonneg (le_min hj0 (by linarith)) _
  have hline : gwBarrierLine 4
      (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) j L =
      4 + sourceBarrierSlope t * j := by
    unfold gwBarrierLine
    rw [← hL]
    field_simp
    <;> ring
  rw [hline, one_mul]
  have hh := hr.1 j hj hjL.le
  linarith

end SRWTightness
