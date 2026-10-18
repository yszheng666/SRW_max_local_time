import SRWTightness.GreenDomainDecomposition
import SRWTightness.ExitPayoffRangeComparison

namespace SRWTightness

/-- Original-domain Green flatness transfers to the punctured Green kernel with twice the error. -/
theorem punctured_green_flatness_error (D K : Finset Site) (hKD : K ⊆ D)
    (x z : Site) (α E : ℝ) (hE : 0 ≤ E)
    (hK : ∀ y ∈ K, |killedGreen D y z - α| ≤ E)
    (hx : |killedGreen D x z - α| ≤ E) :
    |killedGreen (D \ K) x z - α * (1 - setHitProbability D K x)| ≤ 2 * E := by
  have hh : exitPayoff (D \ K) (setHitProbability D K) x = setHitProbability D K x := by
    symm
    apply harmonic_eq_exitPayoff
    intro y hy
    exact setHitProbability_harmonic D K y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have hb (y : Site) (hy : y ∉ D \ K) :
      |killedGreen D y z - α * setHitProbability D K y| ≤ E := by
    by_cases hyK : y ∈ K
    · simpa only [setHitProbability_one D K y (hKD hyK) hyK, mul_one] using hK y hyK
    · have hyD : y ∉ D := fun h ↦ hy (Finset.mem_sdiff.mpr ⟨h, hyK⟩)
      simpa only [killedGreen_zero_of_not_mem D y z hyD,
        setHitProbability_zero_of_not_mem D K y hyD, mul_zero, sub_zero, abs_zero] using hE
  have hlo := exitPayoff_mono_on_compl (D \ K)
    (fun y ↦ -E + α * setHitProbability D K y) (fun y ↦ killedGreen D y z)
    (fun y hy ↦ by have h := (abs_le.mp (hb y hy)).1; linarith) x
  have hhi := exitPayoff_mono_on_compl (D \ K)
    (fun y ↦ killedGreen D y z) (fun y ↦ E + α * setHitProbability D K y)
    (fun y hy ↦ by have h := (abs_le.mp (hb y hy)).2; linarith) x
  rw [exitPayoff_affine, hh] at hlo hhi
  have hd := green_domain_decomposition D (D \ K) Finset.sdiff_subset x z
  obtain ⟨hxl, hxu⟩ := abs_le.mp hx
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A quantitative escape lower bound turns the punctured Green absolute error into relative error. -/
theorem punctured_green_relative_from_flatness (D K : Finset Site) (hKD : K ⊆ D)
    (x z : Site) (α E c t : ℝ) (hE : 0 ≤ E) (hc : 0 < c) (ht : 0 < t)
    (hK : ∀ y ∈ K, |killedGreen D y z - α| ≤ E)
    (hx : |killedGreen D x z - α| ≤ E)
    (hq : c / t ≤ 1 - setHitProbability D K x) :
    |killedGreen (D \ K) x z - α * (1 - setHitProbability D K x)| ≤
      (2 * E / c * t) * (1 - setHitProbability D K x) := by
  refine (punctured_green_flatness_error D K hKD x z α E hE hK hx).trans ?_
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mp hq)
    (show 0 ≤ 2 * E / c by positivity)
  have he : (2 * E / c) * c = 2 * E := by field_simp
  rw [he] at hh
  nlinarith

end SRWTightness
