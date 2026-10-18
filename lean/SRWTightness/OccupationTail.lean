import SRWTightness.OccupationFirstStep
import SRWTightness.FirstStepLaw

open MeasureTheory

namespace SRWTightness

noncomputable def occupationIndicator (D : Finset Site) (x y : Site) (k : ℕ)
    (ω : Sample) : ℝ := if k ≤ domainLocalTime D x y ω then 1 else 0

 theorem measurable_occupationIndicator (D : Finset Site) (x y : Site) (k : ℕ) :
    Measurable (occupationIndicator D x y k) :=
  (measurable_of_countable (fun m : ℕ ↦ if k ≤ m then (1 : ℝ) else 0)).comp
    (measurable_domainLocalTime D x y)

 theorem integrable_occupationIndicator (D : Finset Site) (x y : Site) (k : ℕ) :
    Integrable (occupationIndicator D x y k) pathLaw := by
  refine ⟨(measurable_occupationIndicator D x y k).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [] with ω
  unfold occupationIndicator
  split_ifs <;> norm_num

noncomputable def occupationTail (D : Finset Site) (y : Site) (k : ℕ) (x : Site) : ℝ :=
  ∫ ω, occupationIndicator D x y k ω ∂pathLaw

 theorem occupationTail_eq_probability (D : Finset Site) (x y : Site) (k : ℕ) :
    occupationTail D y k x = pathLaw.real {ω | k ≤ domainLocalTime D x y ω} := by
  have hs : MeasurableSet {ω | k ≤ domainLocalTime D x y ω} :=
    (measurable_domainLocalTime D x y) measurableSet_Ici
  simpa [occupationTail, occupationIndicator, Set.indicator] using
    (integral_indicator_one (μ := pathLaw) hs)

 theorem occupationTail_nonneg (D : Finset Site) (x y : Site) (k : ℕ) :
    0 ≤ occupationTail D y k x := by
  rw [occupationTail_eq_probability]
  exact measureReal_nonneg

 theorem occupationTail_zero_of_not_mem (D : Finset Site) (x y : Site) (hx : x ∉ D)
    (k : ℕ) (hk : 0 < k) : occupationTail D y k x = 0 := by
  simp [occupationTail, occupationIndicator, domainLocalTime_zero_of_not_mem D x y hx,
    Nat.not_le_of_gt hk]

 theorem occupationTail_one_at_self (D : Finset Site) (y : Site) (hy : y ∈ D) :
    occupationTail D y 1 y = 1 := by
  have he : occupationIndicator D y y 1 =ᵐ[pathLaw] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [domainExit_ne_top_ae D y] with ω hω
    have h := domainLocalTime_first_step D y y hy ω hω
    have hn : 1 ≤ domainLocalTime D y y ω := by
      rw [h]
      simp
    simp [occupationIndicator, hn]
  unfold occupationTail
  rw [integral_congr_ae he]
  simp

end SRWTightness
