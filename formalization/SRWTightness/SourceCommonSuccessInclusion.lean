import SRWTightness.SourceCommonActualHighBound
import SRWTightness.SourceSuccessVisits

namespace SRWTightness

/-- Two source successes force the common-prefix event of the original walk. -/
theorem source_common_success_inclusion (t A γ : ℝ) (b w : Site) (I J j : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (z' : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ J)))
    (hz : (z : Site) = b) (hz' : (z' : Site) = w)
    (ht : sourceScaleThreshold 4 ≤ t)
    (hj : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (ω : Sample) (β β' : ℕ → GaussianCoefficientSpace)
    (hb : (ω, β) ∈ sourceLocalTimeSuccessEvent t A γ b I z)
    (hw : (ω, β') ∈ sourceLocalTimeSuccessEvent t A γ w J z') :
    ω ∈ sourceCommonActualHighEvent t b w j := by
  refine ⟨hb.1, ?_, ?_⟩
  · intro i hi hij
    exact hb.2.2.1.1 i hi (by omega)
  · have hvb := source_success_visits t A γ b I z ht (ω, β) hb
    have hvw := source_success_visits t A γ w J z' ht (ω, β') hw
    simp only [hz] at hvb
    simp only [hz'] at hvw
    have hcut : (2 / Real.pi) * sourceTerminalHeight t ^ 2 / 2 ≤
        (sourceTerminalVisitCutoff t : ℝ) := by
      rw [sourceTerminalVisitCutoff_green_form]
      exact Nat.le_ceil _
    intro v
    have hv : (v : Site) = b ∨ (v : Site) = w := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using v.property
    rcases hv with hv | hv
    · rw [hv]
      exact hcut.trans (by exact_mod_cast hvb)
    · rw [hv]
      exact hcut.trans (by exact_mod_cast hvw)

end SRWTightness
