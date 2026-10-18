import SRWTightness.GreenPotentialFlatness
import SRWTightness.PotentialKernelUnitRadius
import SRWTightness.AnnulusExitGeometry
import SRWTightness.GreenDomainDecomposition
import SRWTightness.DiskDiagonalLogBound

open Filter
open scoped Topology
namespace SRWTightness

/-- One-step overshoot transfers the same potential-kernel constant to the disk diagonal. -/
theorem diskGreen_origin_fine_bound (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤
        C / normSq z)
    (R : ℝ) (hR : 2 ≤ R) (hlarge : R₀ + 1 ≤ R) :
    |diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + κ)| ≤
      (4 * C + 2 * (2 / Real.pi)) / R := by
  have hx : (0 : Site) ∈ diskFinset R := by
    simp only [mem_diskFinset, disk, Set.mem_setOf_eq]
    norm_num [normSq]
    nlinarith
  have hb : ∀ z ∈ domainExitBoundary (diskFinset R),
      |potentialKernel (z - 0) - ((2 / Real.pi) * Real.log R + κ)| ≤
        (4 * C + 2 * (2 / Real.pi)) / R := by
    intro z hz
    obtain ⟨hout, y, hy, d, he⟩ := hz
    have hlo : R ^ 2 ≤ normSq z := by
      simpa only [mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hout
    have hyR : normSq y ≤ R ^ 2 :=
      (show normSq y < R ^ 2 from (mem_diskFinset R y).mp hy).le
    have hhi : normSq z ≤ (R + 1) ^ 2 := by
      rw [he]
      exact normSq_step_le y d (by linarith) hyR
    simpa only [sub_zero] using potential_kernel_unit_radius_bound κ C R₀ hC hR₀
      hbound R hR hlarge z (by nlinarith) hhi
  have hp : |potentialKernel ((0 : Site) - 0) - (0 : ℝ)| ≤ 0 := by
    simp [potentialKernel_zero]
  have hh := green_flatness_from_potential_bounds (diskFinset R) 0 0 hx
    ((2 / Real.pi) * Real.log R + κ) 0 ((4 * C + 2 * (2 / Real.pi)) / R) 0 hb hp
  simpa only [diskGreen, sub_zero, add_zero] using hh

/-- The same fine estimate holds at every translated disk center. -/
theorem diskGreen_center_fine_bound (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤
        C / normSq z)
    (R : ℝ) (hR : 2 ≤ R) (hlarge : R₀ + 1 ≤ R) (b : Site) :
    |killedGreen (translateFinset b (diskFinset R)) b b -
      ((2 / Real.pi) * Real.log R + κ)| ≤ (4 * C + 2 * (2 / Real.pi)) / R := by
  have he := killedGreen_translate b (diskFinset R) 0 0
  simp only [add_zero] at he
  rw [he]
  exact diskGreen_origin_fine_bound κ C R₀ hC hR₀ hbound R hR hlarge

/-- The fine input yields a common constant and an explicit inverse-radius diagonal error. -/
theorem diskGreen_fine_asymptotic (hinput : PotentialKernelAsymptoticInput) :
    ∃ κ B R₁ : ℝ, 0 ≤ B ∧ 2 ≤ R₁ ∧
      (∀ R : ℝ, R₁ ≤ R →
        |diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + κ)| ≤ B / R) ∧
      Tendsto (fun R : ℝ ↦ diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + κ))
        atTop (𝓝 0) := by
  obtain ⟨κ, C, R₀, hC, hR₀, hb⟩ := hinput
  let B : ℝ := 4 * C + 2 * (2 / Real.pi)
  let R₁ : ℝ := max 2 (R₀ + 1)
  have herr : ∀ R : ℝ, R₁ ≤ R →
      |diskGreen R 0 0 - ((2 / Real.pi) * Real.log R + κ)| ≤ B / R := by
    intro R hR
    exact diskGreen_origin_fine_bound κ C R₀ hC hR₀ hb R
      ((le_max_left _ _).trans hR) ((le_max_right _ _).trans hR)
  refine ⟨κ, B, R₁, by dsimp [B]; positivity, le_max_left _ _, herr, ?_⟩
  have hlim : Tendsto (fun R : ℝ ↦ B / R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).const_mul B
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop R₁] with R hR
  simpa only [Real.norm_eq_abs] using herr R hR

end SRWTightness
