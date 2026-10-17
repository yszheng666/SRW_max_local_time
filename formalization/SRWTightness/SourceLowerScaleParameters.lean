import SRWTightness.SourceCoarseTime
import SRWTightness.SourceRootDepth
import SRWTightness.SourceForestApplicationGeometry

open Filter

namespace SRWTightness

/-- Source (5.1), including agreement of the natural root depth with the signed floor. -/
theorem source_lower_scale_parameters (R : ℝ) (j : ℕ) (hR : 0 < R)
    (hscale : 32 * sourceLowerRadius (Real.log R) ≤ R) :
    sourceLowerLogRadius (Real.log R) = (2000 * Real.log (Real.log R)) ^ (5 / 2 : ℝ) ∧
    sourceLowerRadius (Real.log R) = Real.exp (sourceLowerLogRadius (Real.log R)) ∧
    sourceRecordBuffer 1 = 14 ∧
    (sourceRootDepth R (sourceLowerRadius (Real.log R)) : ℤ) =
      Int.floor (Real.log (R / (32 * sourceLowerRadius (Real.log R)))) ∧
    sourceCoarseGeneration (Real.log R) =
      (sourceRootDepth R (sourceLowerRadius (Real.log R)) : ℤ) - 1 ∧
    sourceRecordRadius (sourceLowerRadius (Real.log R))
      (sourceRootDepth R (sourceLowerRadius (Real.log R))) j =
      sourceLowerRadius (Real.log R) * Real.exp
        ((sourceRootDepth R (sourceLowerRadius (Real.log R)) : ℝ) - (j : ℝ)) ∧
    sourceLowerTime (sourceLowerRadius (Real.log R)) =
      diskGreen (Real.exp 1 * sourceLowerRadius (Real.log R) - 1) 0 0 / (2 / Real.pi) ∧
    sourceTotalTime (Real.log R) =
      (sourceCoarseGeneration (Real.log R) : ℝ) +
        sourceLowerTime (sourceLowerRadius (Real.log R)) := by
  have hlog : 0 ≤ Real.log (R / (32 * sourceLowerRadius (Real.log R))) :=
    Real.log_nonneg ((one_le_div (mul_pos (by norm_num) (sourceLowerRadius_pos _))).mpr hscale)
  have hf : (sourceRootDepth R (sourceLowerRadius (Real.log R)) : ℤ) =
      Int.floor (Real.log (R / (32 * sourceLowerRadius (Real.log R)))) :=
    Int.natCast_floor_eq_floor hlog
  refine ⟨rfl, rfl, ?_, hf, ?_, rfl, rfl, rfl⟩
  · norm_num [sourceRecordBuffer]
  · rw [hf]
    exact sourceCoarseGeneration_at_radius R hR

/-- The geometric premise needed to identify the two floor conventions is eventual in R. -/
theorem source_lower_scale_parameter_range :
    ∀ᶠ R : ℝ in atTop, 0 < R ∧ 32 * sourceLowerRadius (Real.log R) ≤ R := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop T)] with R hR ht
  have he := (hT (Real.log R) ht).2
  rw [Real.exp_log hR] at he
  have hm := sourceLowerRadius_pos (Real.log R)
  exact ⟨hR, by nlinarith [Real.exp_one_gt_two]⟩

end SRWTightness
