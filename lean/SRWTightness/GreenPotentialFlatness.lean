import SRWTightness.PotentialRadialPerturbation
import SRWTightness.PotentialKernelGreen
import SRWTightness.RecordExitSlice

open MeasureTheory

namespace SRWTightness

/-- Uniform boundary and initial potential errors give flatness of the actual killed Green kernel. -/
theorem green_flatness_from_potential_bounds (D : Finset Site) (x y : Site) (hx : x ∈ D)
    (cR cr E F : ℝ)
    (hb : ∀ z ∈ domainExitBoundary D, |potentialKernel (z - y) - cR| ≤ E)
    (hp : |potentialKernel (x - y) - cr| ≤ F) :
    |killedGreen D x y - (cR - cr)| ≤ E + F := by
  have hlo : cR - E ≤ exitPayoff D (fun z ↦ potentialKernel (z - y)) x := by
    calc
      _ = ∫ _ : Sample, cR - E ∂pathLaw := by simp
      _ ≤ _ := by
        apply integral_mono_ae (integrable_const _)
          (integrable_domainExit_payoff D x (fun z ↦ potentialKernel (z - y)))
        filter_upwards [domainExitLocation_mem_boundary_ae D x hx] with ω hω
        have hh := (abs_le.mp (hb _ hω)).1
        linarith
  have hhi : exitPayoff D (fun z ↦ potentialKernel (z - y)) x ≤ cR + E := by
    calc
      _ ≤ ∫ _ : Sample, cR + E ∂pathLaw := by
        apply integral_mono_ae (integrable_domainExit_payoff D x (fun z ↦ potentialKernel (z - y)))
          (integrable_const _)
        filter_upwards [domainExitLocation_mem_boundary_ae D x hx] with ω hω
        have hh := (abs_le.mp (hb _ hω)).2
        linarith
      _ = _ := by simp
  rw [potentialKernel_green_representation]
  obtain ⟨hpl, hpu⟩ := abs_le.mp hp
  apply abs_le.mpr
  constructor <;> linarith

/-- A quantitative Green flatness bound under actual boundary and start radial perturbations. -/
theorem green_flatness_radial_perturbation (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (D : Finset Site) (x y : Site) (hx : x ∈ D)
    (R r A B : ℝ) (hR : 0 < R) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAR : 2 * A ≤ R) (hBr : 2 * B ≤ r) (hRl : R₀ ≤ R - A) (hrl : R₀ ≤ r - B)
    (hb : ∀ z ∈ domainExitBoundary D,
      R - A ≤ Real.sqrt (normSq (z - y)) ∧ Real.sqrt (normSq (z - y)) ≤ R + A)
    (hp : r - B ≤ Real.sqrt (normSq (x - y)) ∧ Real.sqrt (normSq (x - y)) ≤ r + B) :
    |killedGreen D x y - (2 / Real.pi) * (Real.log R - Real.log r)| ≤
      (4 * C / R ^ 2 + (2 / Real.pi) * (2 * A / R)) +
      (4 * C / r ^ 2 + (2 / Real.pi) * (2 * B / r)) := by
  have hh := green_flatness_from_potential_bounds D x y hx
    ((2 / Real.pi) * Real.log R + κ) ((2 / Real.pi) * Real.log r + κ)
    (4 * C / R ^ 2 + (2 / Real.pi) * (2 * A / R))
    (4 * C / r ^ 2 + (2 / Real.pi) * (2 * B / r))
    (fun z hz ↦ potential_kernel_radial_perturbation κ C R₀ hC hR₀ hbound R A hR hA hAR hRl
      (z - y) (hb z hz).1 (hb z hz).2)
    (potential_kernel_radial_perturbation κ C R₀ hC hR₀ hbound r B hr hB hBr hrl
      (x - y) hp.1 hp.2)
  convert hh using 1 <;> congr 1 <;> ring

end SRWTightness
