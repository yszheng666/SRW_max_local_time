import SRWTightness.ClippedRadiusBarrier
import SRWTightness.MaximumPrinciple

open MeasureTheory

namespace SRWTightness

noncomputable def annulusFinset (a R : ℝ) : Finset Site := diskFinset R \ diskFinset a

noncomputable def annulusOuterExitProbability (a R : ℝ) (x : Site) : ℝ :=
  pathLaw.real {ω | domainExitLocation (annulusFinset a R) x ω ∉ diskFinset R}

theorem exitPayoff_outside_eq_probability (D K : Finset Site) (x : Site) :
    exitPayoff D (fun y ↦ if y ∉ K then 1 else 0) x =
      pathLaw.real {ω | domainExitLocation D x ω ∉ K} := by
  have hs : MeasurableSet {ω | domainExitLocation D x ω ∉ K} := by
    change MeasurableSet (domainExitLocation D x ⁻¹' (K : Set Site)ᶜ)
    exact (measurable_domainExitLocation D x) (Finset.measurableSet K).compl
  simpa only [exitPayoff, Set.indicator, Set.mem_setOf_eq, Pi.one_apply] using
    (integral_indicator_one (μ := pathLaw) hs)

/-- The actual annulus exit probability is controlled by the explicit radial barrier. -/
theorem annulusOuterExitProbability_le_barrier (a : ℝ) (ha : 4 ≤ a) (x : Site) :
    annulusOuterExitProbability a (2 * a) x ≤ (4 / 3 : ℝ) * clippedRadiusBarrier a x := by
  let D := annulusFinset a (2 * a)
  have hsup : exitPayoff D (clippedRadiusBarrier a) x ≤ clippedRadiusBarrier a x := by
    apply exitPayoff_le_superharmonic
    intro z hz
    have hznot : z ∉ diskFinset a := (Finset.mem_sdiff.mp hz).2
    have hzsq : a ^ 2 ≤ normSq z := by
      simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hznot
    exact clippedRadiusBarrier_supermean a ha z hzsq
  have hpoint (z : Site) : (if z ∉ diskFinset (2 * a) then (1 : ℝ) else 0) ≤
      (4 / 3 : ℝ) * clippedRadiusBarrier a z := by
    by_cases hz : z ∉ diskFinset (2 * a)
    · rw [if_pos hz]
      have hzs : (2 * a) ^ 2 ≤ normSq z := by
        simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hz
      linarith [clippedRadiusBarrier_outer_lower a ha z hzs]
    · rw [if_neg hz]
      exact mul_nonneg (by norm_num) (clippedRadiusBarrier_nonneg a z)
  have hh := exitPayoff_mono_on_compl D
    (fun z ↦ if z ∉ diskFinset (2 * a) then 1 else 0)
    (fun z ↦ (4 / 3 : ℝ) * clippedRadiusBarrier a z) (fun z _ ↦ hpoint z) x
  rw [exitPayoff_outside_eq_probability] at hh
  have he : exitPayoff D (fun z ↦ (4 / 3 : ℝ) * clippedRadiusBarrier a z) x =
      (4 / 3 : ℝ) * exitPayoff D (clippedRadiusBarrier a) x := by
    exact integral_const_mul _ _
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hsup (by norm_num))

/-- Uniform boundary-to-double-radius escape bound for the actual planar SRW. -/
theorem annulusOuterExitProbability_near_upper (a : ℝ) (ha : 4 ≤ a) (x : Site)
    (hxlo : a ^ 2 ≤ normSq x) (hxhi : normSq x ≤ (a + 1) ^ 2) :
    annulusOuterExitProbability a (2 * a) x ≤ 16 / (3 * a) := by
  have hh := (annulusOuterExitProbability_le_barrier a ha x).trans
    (mul_le_mul_of_nonneg_left (clippedRadiusBarrier_near_upper a ha x hxlo hxhi)
      (by norm_num : (0 : ℝ) ≤ 4 / 3))
  calc
    _ ≤ (4 / 3 : ℝ) * (4 / a) := hh
    _ = 16 / (3 * a) := by ring

end SRWTightness
