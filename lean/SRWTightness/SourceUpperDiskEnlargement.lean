import SRWTightness.DiskMonotone
import SRWTightness.CenteringAlgebra
import SRWTightness.SourceUpperInnerSourceEvent

open Filter MeasureTheory

namespace SRWTightness

/-- The fixed height loss when the killed disk radius is doubled. -/
noncomputable def sourceUpperDoublingShift : ℝ :=
  (2 / Real.sqrt Real.pi) * Real.log 2

/-- Doubling the disk changes its centering by at most the fixed height loss. -/
theorem source_upper_doubling_center (R : ℝ) (hR : 1 < R) :
    diskCenter (2 * R) - diskCenter R ≤ sourceUpperDoublingShift := by
  have h := diskCenter_quotient_difference_le (2 * R) 2 (by norm_num) (by linarith)
  simpa [sourceUpperDoublingShift] using h

/-- A high point of the full killed disk survives in the half-radius disk of the doubled domain. -/
theorem source_upper_disk_enlargement (R s : ℝ) (hR : 1 < R)
    (hcenter : 0 ≤ diskCenter R + s) :
    {ω | s < diskFluctuation R ω} ≤ᵐ[pathLaw]
      {ω | ∃ x ∈ diskFinset ((2 * R) / 2),
        diskCenter (2 * R) + (s - sourceUpperDoublingShift) ≤
          Real.sqrt (localTime ω (exitSteps (2 * R) ω) x : ℝ)} := by
  filter_upwards [exitTime_ne_top_ae (by linarith : 0 ≤ R),
    exitTime_ne_top_ae (by linarith : 0 ≤ 2 * R)] with ω hi ho
  intro hhigh
  have hh : diskCenter R + s < Real.sqrt (diskMax R ω : ℝ) := by
    change s < Real.sqrt (diskMax R ω : ℝ) - diskCenter R at hhigh
    linarith
  have hnonempty : (visited ω (exitSteps R ω)).Nonempty := by
    by_contra hn
    have he : visited ω (exitSteps R ω) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz : diskMax R ω = 0 := by change (visited ω (exitSteps R ω)).sup _ = 0; rw [he]; rfl
    rw [hz, Nat.cast_zero, Real.sqrt_zero] at hh
    linarith
  obtain ⟨x, hx, hmax⟩ := Finset.exists_mem_eq_sup
    (visited ω (exitSteps R ω)) hnonempty (localTime ω (exitSteps R ω))
  obtain ⟨k, hk, hkx⟩ := Finset.mem_image.mp hx
  have hklt : (k : WithTop ℕ) < exitTime R ω := by
    rw [← coe_exitSteps R ω hi]
    exact WithTop.coe_lt_coe.mpr (Finset.mem_range.mp hk)
  have hmem := before_exit_mem R ω k hklt
  have hxR : x ∈ diskFinset ((2 * R) / 2) := by
    apply (mem_diskFinset _ _).mpr
    have he : (2 * R) / 2 = R := by ring
    rw [he, ← hkx]
    exact hmem
  have htime := exitTime_mono_radius (by linarith : 0 ≤ R)
    (by linarith : R ≤ 2 * R) ω
  rw [← coe_exitSteps R ω hi, ← coe_exitSteps (2 * R) ω ho] at htime
  have hlocal := localTime_mono ω (WithTop.coe_le_coe.mp htime) x
  have hmax' : diskMax R ω = localTime ω (exitSteps R ω) x := hmax
  rw [hmax'] at hh
  refine ⟨x, hxR, ?_⟩
  have hsqrt := Real.sqrt_le_sqrt (show (localTime ω (exitSteps R ω) x : ℝ) ≤
    localTime ω (exitSteps (2 * R) ω) x by exact_mod_cast hlocal)
  have hc := source_upper_doubling_center R hR
  linarith

/-- The corresponding comparison holds for actual event probabilities. -/
theorem source_upper_disk_enlargement_probability (R s : ℝ) (hR : 1 < R)
    (hcenter : 0 ≤ diskCenter R + s) :
    pathLaw.real {ω | s < diskFluctuation R ω} ≤
      pathLaw.real {ω | ∃ x ∈ diskFinset ((2 * R) / 2),
        diskCenter (2 * R) + (s - sourceUpperDoublingShift) ≤
          Real.sqrt (localTime ω (exitSteps (2 * R) ω) x : ℝ)} := by
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono_ae (source_upper_disk_enlargement R s hR hcenter))

end SRWTightness
