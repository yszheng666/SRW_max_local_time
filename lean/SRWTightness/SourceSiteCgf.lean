import SRWTightness.SourceCgfError
import SRWTightness.SourcePointEnergyTime
import SRWTightness.SourceTimePowerDecay

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

noncomputable def sourceSiteCgfError (t : ℝ) : ℝ :=
  sourceCgfErrorConstant 1 2 * sourceLowerTime (sourceLowerRadius t) ^ 3 / t

theorem sourceSiteCgfError_tendsto_zero : Tendsto sourceSiteCgfError atTop (𝓝 0) := by
  have hh := (sourceLowerTime_pow_div_t_tendsto_zero 3).const_mul (sourceCgfErrorConstant 1 2)
  change Tendsto (fun t ↦ sourceSiteCgfError t) atTop (𝓝 0)
  convert hh using 1
  · funext t; unfold sourceSiteCgfError; ring
  · simp

/-- The cumulant of the exact site tilt equals twice its variance time up to a vanishing error. -/
theorem source_site_cgf_error :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (M : Finset Site),
      let m := sourceLowerRadius t
      let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      M ⊆ D → α * capacity D M ≤ 1 → ∀ (u : ℝ), t ≤ u →
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) → ∀ z : M,
        |cgf (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
          (markProductLaw D M α k) 1 - 2 * pointEnergyTime D z α (2 / Real.pi)| ≤
            sourceSiteCgfError t := by
  filter_upwards [(source_observation_cgf_error 1 2 (by norm_num) (by norm_num)).2,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t happ ht
  dsimp only
  intro b M hMD hcap u hu k hk z
  have hconds := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have hu0 : 0 < u := by linarith [hconds.1]
  have hm := hconds.2.2.1
  have hα := (sourceReferenceIntensity_bounds (sourceLowerRadius t) 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith)).1
  let w : Unit → M → ℝ := fun _ x ↦ if x = z then 1 else 0
  have hw (i : Unit) (x : M) : 0 ≤ w i x := by dsimp [w]; split <;> norm_num
  have hw1 (i : Unit) : ∑ x : M, w i x = 1 := by simp [w]
  have hwF (i : Unit) : normalizedWeightedSum M k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi) u (w i) =
      normalizedMarkSum M k (sourceReferenceIntensity (sourceLowerRadius t) 14)
        (2 / Real.pi) u z := by
    funext Y
    simp [normalizedWeightedSum, w]
  have hh := happ Unit b M hMD hcap u (by simpa using hu) k hk w hw hw1
    (fun _ ↦ 2) (by norm_num)
  dsimp only at hh
  simp only [hwF, Fintype.sum_unique] at hh
  have hc := normalizedMarkSum_covariance _ M hMD _ (2 / Real.pi) u hα
    (by positivity) hu0 hcap k hk z z
  rw [hc] at hh
  simp only [ite_true] at hh
  convert hh using 1 <;> simp only [sourceSiteCgfError, pointEnergyTime] <;> congr 1 <;> ring

end SRWTightness
