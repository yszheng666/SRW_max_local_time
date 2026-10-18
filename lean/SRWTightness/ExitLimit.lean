import SRWTightness.ExitFinite

open MeasureTheory Filter
open scoped Topology ENNReal

namespace SRWTightness

/-- Finite version of the exit time, with value zero on the now-proved null exceptional set. -/
noncomputable def exitSteps (R : ℝ) (ω : Sample) : ℕ := (exitTime R ω).untopD 0

 theorem boundedTime_mono (R : ℝ) (ω : Sample) : Monotone (fun N ↦ boundedTime R N ω) := by
  intro m n h
  have hle : (boundedTime R m ω : WithTop ℕ) ≤ boundedTime R n ω := by
    rw [coe_boundedTime, coe_boundedTime]
    exact min_le_min_left _ (by exact_mod_cast h)
  exact_mod_cast hle

 theorem boundedTime_eventually_eq (R : ℝ) (ω : Sample) (ht : exitTime R ω ≠ ⊤) :
    ∀ᶠ N in atTop, boundedTime R N ω = exitSteps R ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
  filter_upwards [eventually_ge_atTop k] with N hN
  have hle : (k : WithTop ℕ) ≤ N := by exact_mod_cast hN
  simp [boundedTime, boundedExit, exitSteps, ← hk, min_eq_left hle, WithTop.untopA]
  rfl

 theorem ae_tendsto_boundedTime {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂pathLaw, Tendsto (fun N ↦ (boundedTime R N ω : ℝ)) atTop
      (𝓝 (exitSteps R ω : ℝ)) := by
  filter_upwards [exitTime_ne_top_ae hR] with ω hω
  apply tendsto_const_nhds.congr'
  filter_upwards [boundedTime_eventually_eq R ω hω] with N hN
  simp only [hN]

end SRWTightness
