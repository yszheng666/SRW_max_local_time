import SRWTightness.Law

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Every prescribed finite increment prefix has its exact independent uniform cylinder mass. -/
theorem finite_direction_prefix_mass (n : ℕ) (υ : Sample) :
    pathLaw {ω | ∀ i < n, ω i = υ i} = ((4 : ℝ≥0∞)⁻¹) ^ n := by
  have he : {ω : Sample | ∀ i < n, ω i = υ i} =
      Set.pi (Finset.range n) (fun i ↦ {υ i}) := by
    ext ω
    simp
  rw [he, pathLaw, Measure.infinitePi_pi _ (by intro i hi; exact measurableSet_singleton _)]
  simp only [direction_mass, Finset.prod_const, Finset.card_range]

/-- The real-valued mass of a prescribed finite increment prefix is four to minus its length. -/
theorem finite_direction_prefix_real_mass (n : ℕ) (υ : Sample) :
    pathLaw.real {ω | ∀ i < n, ω i = υ i} = (1 / 4 : ℝ) ^ n := by
  rw [Measure.real, finite_direction_prefix_mass]
  simp

end SRWTightness
