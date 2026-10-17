import SRWTightness.OccupationTail

open MeasureTheory

namespace SRWTightness

 theorem integral_direction_average (f : Direction → ℝ) :
    ∫ d, f d ∂directionLaw = (1 / 4 : ℝ) * ∑ d : Direction, f d := by
  rw [directionLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply]
  have hc : Fintype.card Direction = 4 := rfl
  rw [hc]
  simp only [ENNReal.toReal_inv, smul_eq_mul]
  rw [← Finset.mul_sum]
  norm_num

 theorem occupationTail_first_step_of_ne (D : Finset Site) (x y : Site)
    (hx : x ∈ D) (hxy : x ≠ y) (k : ℕ) :
    occupationTail D y k x =
      (1 / 4 : ℝ) * ∑ d : Direction, occupationTail D y k (x + step d) := by
  have he : occupationIndicator D x y k =ᵐ[pathLaw]
      (fun ω ↦ occupationIndicator D (x + step (ω 0)) y k (shift 1 ω)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have h := domainLocalTime_first_step D x y hx ω hω
    simp only [if_neg hxy, zero_add] at h
    simp only [occupationIndicator, h]
  unfold occupationTail
  rw [integral_congr_ae he]
  rw [integral_first_step_future
    (fun d ↦ occupationIndicator D (x + step d) y k)
    (fun d ↦ measurable_occupationIndicator D _ y k)
    (fun d ↦ integrable_occupationIndicator D _ y k)]
  exact integral_direction_average _

 theorem occupationTail_succ_at_self (D : Finset Site) (y : Site) (hy : y ∈ D) (k : ℕ) :
    occupationTail D y (k + 1) y =
      (1 / 4 : ℝ) * ∑ d : Direction, occupationTail D y k (y + step d) := by
  have he : occupationIndicator D y y (k + 1) =ᵐ[pathLaw]
      (fun ω ↦ occupationIndicator D (y + step (ω 0)) y k (shift 1 ω)) := by
    filter_upwards [domainExit_ne_top_ae D y] with ω hω
    have h := domainLocalTime_first_step D y y hy ω hω
    simp at h
    have hh : k + 1 ≤ domainLocalTime D y y ω ↔
        k ≤ domainLocalTime D (y + step (ω 0)) y (shift 1 ω) := by omega
    simp only [occupationIndicator, hh]
  unfold occupationTail
  rw [integral_congr_ae he]
  rw [integral_first_step_future
    (fun d ↦ occupationIndicator D (y + step d) y k)
    (fun d ↦ measurable_occupationIndicator D _ y k)
    (fun d ↦ integrable_occupationIndicator D _ y k)]
  exact integral_direction_average _

end SRWTightness
