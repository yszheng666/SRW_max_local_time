import SRWTightness.SourceGWLowerTubeProbability

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The actual floor-defined source generation is eventually a positive natural horizon. -/
theorem source_gw_natural_generation :
    ∀ᶠ t : ℝ in atTop,
      ((sourceCoarseGeneration t).toNat : ℝ) = (sourceCoarseGeneration t : ℝ) ∧
        0 < (sourceCoarseGeneration t).toNat := by
  filter_upwards [source_deficit_large_conditions] with t ht
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  unfold sourceTotalTime at hT
  have hN : (0 : ℝ) < (sourceCoarseGeneration t : ℝ) := by linarith
  have hNi : (0 : ℤ) < sourceCoarseGeneration t := by exact_mod_cast hN
  have hc : ((sourceCoarseGeneration t).toNat : ℤ) = sourceCoarseGeneration t :=
    Int.toNat_of_nonneg hNi.le
  have hcr : ((sourceCoarseGeneration t).toNat : ℝ) = (sourceCoarseGeneration t : ℝ) := by
    exact_mod_cast hc
  refine ⟨hcr, ?_⟩
  have hp : (0 : ℝ) < ((sourceCoarseGeneration t).toNat : ℝ) := by rw [hcr]; exact hN
  exact_mod_cast hp

/-- Lower tube probability on the actual natural source horizon; no horizon identity is assumed. -/
theorem source_gw_actual_lower_tube_probability (hGW : GWBarrierLowerInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let y := sourceTerminalRoot t q + 1 / 4
        c * gwBarrierPrefactor L (Real.sqrt 2) y 4 (sourceGWLowerEndpoint t) *
            min (Real.sqrt (Real.sqrt 2 / (y * L))) 1 ≤
          (geometricGWRecordLaw 1 L).real (sourceGWLowerTubeEvent t L q) := by
  obtain ⟨c, hc, hh⟩ := source_gw_lower_tube_probability hGW
  refine ⟨c, hc, ?_⟩
  filter_upwards [hh, source_gw_natural_generation] with t ht hN
  exact ht _ hN.1

end SRWTightness
