import SRWTightness.SourceWalkSuccessEvent
import SRWTightness.DiskOnePoint

namespace SRWTightness

/-- A successful original event reaches the exact integer occupation threshold at its observed site. -/
theorem source_success_visits (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (ht : sourceScaleThreshold 4 ≤ t) (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceLocalTimeSuccessEvent t A γ b I z) :
    sourceTerminalVisitCutoff t ≤ domainLocalTime (diskFinset (Real.exp t)) 0 z p.1 := by
  let k := sourceActualCount t b
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1) p.1
  have hk : 0 < k := hp.2.1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hu : 0 < Real.sqrt (2 * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hu2 : Real.sqrt (2 * (k : ℝ)) ^ 2 / 2 = (k : ℝ) := by
    rw [Real.sq_sqrt (by positivity)]
    ring
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1
  have hα := sourceReferenceIntensity_ge_greenConstant (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  have hden : 0 < Real.sqrt (2 * (k : ℝ)) *
      Real.sqrt (sourceReferenceIntensity (sourceLowerRadius t) 14 * (2 / Real.pi)) := by
    exact mul_pos hu (Real.sqrt_pos.mpr (mul_pos (lt_of_lt_of_le hg hα) hg))
  have hh := hp.2.2.2.1
  change sourceTerminalThreshold t (Real.sqrt (2 * (k : ℝ))) ≤
    sourceWalkObservation t A b I z k p.1 (Fin.last (I + 1)) at hh
  rw [sourceTerminalThreshold_visit_formula t _ k hu2] at hh
  simp only [sourceWalkObservation, diskObservationIndex_last, domainLocalObservation] at hh
  have hnum := (div_le_div_iff_of_pos_right hden).mp hh
  have hreal : (sourceTerminalVisitCutoff t : ℝ) ≤
      (domainLocalTime (diskFinset (Real.exp t)) 0 z p.1 : ℝ) := by linarith
  exact_mod_cast hreal

/-- Success therefore forces the disk maximum above the manuscript integer threshold. -/
theorem source_success_disk_max (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (ht : sourceScaleThreshold 4 ≤ t) (p : Sample × (ℕ → GaussianCoefficientSpace))
    (hp : p ∈ sourceLocalTimeSuccessEvent t A γ b I z) :
    sourceTerminalVisitCutoff t ≤ diskMax (Real.exp t) p.1 := by
  have hh := source_success_visits t A γ b I z ht p hp
  rw [domainLocalTime_disk] at hh
  exact hh.trans (localTime_le_max p.1 (exitSteps (Real.exp t) p.1) z)

end SRWTightness
