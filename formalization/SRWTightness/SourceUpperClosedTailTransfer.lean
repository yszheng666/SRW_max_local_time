import SRWTightness.SourceUpperClosedInnerEnlargement
import SRWTightness.SourceUpperTwoTailShift
import SRWTightness.SpatialTargets

open Filter MeasureTheory

namespace SRWTightness

set_option maxHeartbeats 1000000 in
/-- The open half-radius estimate gives the literal closed half-radius two-tail bound. -/
theorem source_upper_closed_tail_of_inner (C : ℝ) (hC : 0 < C)
    (hinner : ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + s ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}) atTop ≤
        C * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
          Real.exp (-3 * s / 2))) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℝ, 0 ≤ s →
      limsup (fun R : ℝ ↦ pathLaw.real (sourceUpperClosedInnerEvent R s)) atTop ≤
        D * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + Real.exp (-3 * s / 2)) := by
  let d := sourceUpperDoublingShift
  have hd : 0 ≤ d := by
    dsimp [d, sourceUpperDoublingShift]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))
  let F := Real.exp (2 * Real.sqrt Real.pi * d)
  let B := Real.exp (3 * d / 2)
  refine ⟨C * F + B, by dsimp [F, B]; positivity, ?_⟩
  intro s hs0
  have htail0 : 0 ≤ (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
      Real.exp (-3 * s / 2) := by positivity
  by_cases hsd : d ≤ s
  · have hlarge : limsup (fun R : ℝ ↦ pathLaw.real (sourceUpperClosedInnerEvent R s)) atTop ≤
        (C * F) * ((1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
          Real.exp (-3 * s / 2)) := by
      let u : ℝ → ℝ := fun R ↦ pathLaw.real
        {ω | ∃ x ∈ diskFinset (R / 2), diskCenter R + (s - d) ≤
          Real.sqrt (localTime ω (exitSteps R ω) x : ℝ)}
      have hprob : (fun R : ℝ ↦ pathLaw.real (sourceUpperClosedInnerEvent R s)) ≤ᶠ[atTop]
          (fun R : ℝ ↦ u (2 * R)) := by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with R hR
        exact source_upper_closed_inner_probability R s hR
      have huBound : atTop.IsBoundedUnder (· ≤ ·) u :=
        isBoundedUnder_of ⟨1, fun _ ↦ measureReal_le_one⟩
      have huNonneg : ∀ R, 0 ≤ u R := fun _ ↦ measureReal_nonneg
      have hcompBound : atTop.IsBoundedUnder (· ≤ ·) (fun R : ℝ ↦ u (2 * R)) :=
        isBoundedUnder_of ⟨1, fun _ ↦ measureReal_le_one⟩
      have hlim : limsup (fun R : ℝ ↦ pathLaw.real (sourceUpperClosedInnerEvent R s)) atTop ≤
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
      have hb := mul_le_mul_of_nonneg_left (source_upper_two_tail_shift d s hd) hC.le
      simpa only [F, mul_assoc] using hb

    exact hlarge.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (by dsimp [B]; positivity)) htail0)
  · have hlim : limsup (fun R : ℝ ↦ pathLaw.real (sourceUpperClosedInnerEvent R s)) atTop ≤ 1 :=
      limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun _ ↦ measureReal_nonneg))
        (Eventually.of_forall (fun _ ↦ measureReal_le_one))
    have hone : 1 ≤ B * Real.exp (-3 * s / 2) := by
      dsimp [B]
      rw [← Real.exp_add]
      apply Real.one_le_exp
      linarith only [lt_of_not_ge hsd]
    have hfactor : B ≤ C * F + B := le_add_of_nonneg_left (by dsimp [F]; positivity)
    have hshape : Real.exp (-3 * s / 2) ≤
        (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) + Real.exp (-3 * s / 2) :=
      le_add_of_nonneg_left (by positivity)
    exact hlim.trans (hone.trans (mul_le_mul hfactor hshape (Real.exp_pos _).le
      (by dsimp [F, B]; positivity)))

end SRWTightness
