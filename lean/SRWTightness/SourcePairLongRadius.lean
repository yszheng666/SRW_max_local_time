import SRWTightness.SourceCommonPairDistance

namespace SRWTightness

/-- The manuscript distance floor makes the long radius at nu-J smaller than exp(-4) times the distance. -/
theorem source_pair_long_radius (t ρ : ℝ) (hρ : 0 < ρ)
    (houter : ρ ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0)
    (ν J : ℕ) (hν : ν = sourceCommonPairDistanceIndex t ρ + J + 5) :
    sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν - J) < Real.exp (-4) * ρ := by
  let a := sourceCommonPairDistanceIndex t ρ
  have hlog := (source_common_pair_log_separation t ρ hρ houter a 0 (by simp [a])).2
  norm_num only at hlog
  have hinner : sourceCommonPairInnerRadius t a < ρ := by
    have he := Real.exp_lt_exp.mpr (show Real.log (sourceCommonPairInnerRadius t a) <
      Real.log ρ by linarith)
    simpa only [Real.exp_log (sourceCommonPairInnerRadius_pos t a), Real.exp_log hρ] using he
  have hindex : ν - J = a + 5 := by dsimp [a]; omega
  have hr : sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν - J) =
      Real.exp (-4) * sourceCommonPairInnerRadius t a := by
    rw [hindex]
    unfold sourceCommonPairInnerRadius sourceRecordRadius
    rw [show ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) - ((a + 5 : ℕ) : ℝ)) =
      -4 + ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) - ((a + 1 : ℕ) : ℝ)) by
        push_cast; ring, Real.exp_add]
    ring
  rw [hr]
  exact mul_lt_mul_of_pos_left hinner (Real.exp_pos _)

end SRWTightness
