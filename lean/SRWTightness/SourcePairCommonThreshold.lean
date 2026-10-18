import SRWTightness.SourceSuccessVisits

namespace SRWTightness

/-- Two successful sites meet the same occupation threshold when normalized with the first site's count. -/
theorem source_pair_common_threshold (t A γ : ℝ) (b w : Site) (I J : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J))) (hz' : (z' : Site) = w)
    (ht : sourceScaleThreshold 4 ≤ t) (ω : Sample)
    (β β' : ℕ → GaussianCoefficientSpace)
    (hb : (ω, β) ∈ sourceLocalTimeSuccessEvent t A γ b I z)
    (hw : (ω, β') ∈ sourceLocalTimeSuccessEvent t A γ w J z') :
    let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
    let α := sourceReferenceIntensity (sourceLowerRadius t) 14
    let u := Real.sqrt (2 * (k : ℝ))
    sourceTerminalThreshold t u ≤
      ((domainLocalTime (diskFinset (Real.exp t)) 0 z ω : ℝ) - α * k) /
        (u * Real.sqrt (α * (2 / Real.pi))) ∧
    sourceTerminalThreshold t u ≤
      ((domainLocalTime (diskFinset (Real.exp t)) 0 w ω : ℝ) - α * k) /
        (u * Real.sqrt (α * (2 / Real.pi))) := by
  let k := sourceActualCount t b (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) ω
  have hk : 0 < k := hb.2.1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hu2 : Real.sqrt (2 * (k : ℝ)) ^ 2 / 2 = (k : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hα := sourceReferenceIntensity_ge_greenConstant (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hd : 0 < Real.sqrt (2 * (k : ℝ)) *
      Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi)) := by
    apply mul_pos (Real.sqrt_pos.mpr (by positivity))
    exact Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hg hα) hg)
  have hvb := source_success_visits t A γ b I z ht (ω, β) hb
  have hvw := source_success_visits t A γ w J z' ht (ω, β') hw
  simp only [hz'] at hvw
  dsimp only
  rw [sourceTerminalThreshold_visit_formula t _ k hu2]
  constructor
  · apply (div_le_div_iff_of_pos_right hd).mpr
    have hh : (sourceTerminalVisitCutoff t : ℝ) ≤
        (domainLocalTime (diskFinset (Real.exp t)) 0 z ω : ℝ) := by exact_mod_cast hvb
    linarith
  · apply (div_le_div_iff_of_pos_right hd).mpr
    have hh : (sourceTerminalVisitCutoff t : ℝ) ≤
        (domainLocalTime (diskFinset (Real.exp t)) 0 w ω : ℝ) := by exact_mod_cast hvw
    linarith

end SRWTightness
