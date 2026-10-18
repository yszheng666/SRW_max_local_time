import SRWTightness.GreenPotentialFlatness
import SRWTightness.PotentialRadialGap

namespace SRWTightness

/-- Quantitative actual Green flatness under positive radial gaps. -/
theorem green_flatness_radial_gap (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (D : Finset Site) (x y : Site) (hx : x ∈ D)
    (R r A B : ℝ) (hR : 0 < R) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hRl : R₀ ≤ R - A) (hrl : R₀ ≤ r - B)
    (hb : ∀ z ∈ domainExitBoundary D,
      R - A ≤ Real.sqrt (normSq (z - y)) ∧ Real.sqrt (normSq (z - y)) ≤ R + A)
    (hp : r - B ≤ Real.sqrt (normSq (x - y)) ∧ Real.sqrt (normSq (x - y)) ≤ r + B) :
    |killedGreen D x y - (2 / Real.pi) * (Real.log R - Real.log r)| ≤
      (C / (R - A) ^ 2 + (2 / Real.pi) * (A / (R - A))) +
      (C / (r - B) ^ 2 + (2 / Real.pi) * (B / (r - B))) := by
  have hh := green_flatness_from_potential_bounds D x y hx
    ((2 / Real.pi) * Real.log R + κ) ((2 / Real.pi) * Real.log r + κ)
    (C / (R - A) ^ 2 + (2 / Real.pi) * (A / (R - A)))
    (C / (r - B) ^ 2 + (2 / Real.pi) * (B / (r - B)))
    (fun z hz ↦ potential_kernel_radial_gap κ C R₀ hC hR₀ hbound R A hA hRl
      (z - y) (hb z hz).1 (hb z hz).2)
    (potential_kernel_radial_gap κ C R₀ hC hR₀ hbound r B hB hrl
      (x - y) hp.1 hp.2)
  convert hh using 1 <;> congr 1 <;> ring

end SRWTightness
