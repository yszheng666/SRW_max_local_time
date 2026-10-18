import SRWTightness.SourceUpperDiskEnlargement
import SRWTightness.SourceUpperShiftedTail
import SRWTightness.SpatialTargets

open Filter MeasureTheory

namespace SRWTightness

set_option maxHeartbeats 1000000 in
/-- The actual half-radius estimate implies the full spatial upper-tail claim. -/
theorem source_upper_disk_tail_of_inner (C : ℝ) (hC : 0 < C)
    (hinner : ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) atTop ≤
        C * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
          Real.exp (-3 * s / 2))) : DiskUpperTailClaim := by
  let d := sourceUpperDoublingShift
  have hd : 0 ≤ d := by
    dsimp [d, sourceUpperDoublingShift]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  refine ⟨C * (2 * Real.exp (3 * d / 2)), d + 1, by positivity, by linarith, ?_⟩
  intro s hs
  have hsd : d ≤ s := by linarith
  have hs0 : 0 ≤ s := hd.trans hsd
  let u : ℝ → ℝ := fun R ↦ pathLaw.real
    {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + (s - d) ≤
      Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}
  have hprob : (fun R : ℝ ↦ pathLaw.real {ω | s < diskFluctuation R ω}) ≤ᶠ[atTop]
      (fun R : ℝ ↦ u (2 * R)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop 2)] with R hR hlog
    exact source_upper_disk_enlargement_probability R s hR
      (source_upper_center_nonneg R s hlog hs0)
  have huBound : atTop.IsBoundedUnder (· ≤ ·) u :=
    isBoundedUnder_of ⟨1, fun _ ↦ measureReal_le_one⟩
  have huNonneg : ∀ R, 0 ≤ u R := fun _ ↦ measureReal_nonneg
  have hcompBound : atTop.IsBoundedUnder (· ≤ ·) (fun R : ℝ ↦ u (2 * R)) :=
    isBoundedUnder_of ⟨1, fun _ ↦ measureReal_le_one⟩
  have hlim : limsup (fun R : ℝ ↦ pathLaw.real {ω | s < diskFluctuation R ω}) atTop ≤
      limsup (fun R : ℝ ↦ u (2 * R)) atTop :=
    limsup_le_limsup hprob
      (isCoboundedUnder_le_of_le atTop (fun _ ↦ measureReal_nonneg)) hcompBound
  have hscale : Tendsto (fun R : ℝ ↦ 2 * R) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hcomp : limsup (fun R : ℝ ↦ u (2 * R)) atTop ≤ limsup u atTop := by
    exact hscale.limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le _ huNonneg) huBound
  have hinnerBound : limsup u atTop ≤
      C * ((1 + (s - d)) * Real.exp (-(2 * Real.sqrt Real.pi * (s - d))) +
        Real.exp (-3 * (s - d) / 2)) := hinner (s - d) (sub_nonneg.mpr hsd)
  have hh := (hlim.trans hcomp).trans hinnerBound
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left (source_upper_shifted_tail_bound d s hd hsd) hC.le
  simpa only [mul_assoc] using hb

end SRWTightness
