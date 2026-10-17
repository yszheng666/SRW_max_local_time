import SRWTightness.BesselPast
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Adapted

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The sigma algebra of the full vector past increases with its terminal time. -/
theorem besselPast_space_mono (T r s : ℝ) (hrs : r ≤ s) :
    MeasurableSpace.comap (besselPast T r) inferInstance ≤
      MeasurableSpace.comap (besselPast T s) inferInstance := by
  let R : (Fin 3 → Set.Icc (0 : ℝ) s → ℝ) → (Fin 3 → Set.Icc (0 : ℝ) r → ℝ) :=
    fun p i u ↦ p i ⟨u, u.property.1, u.property.2.trans hrs⟩
  have hR : Measurable R := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro u
    exact (measurable_pi_apply
      (⟨u, u.property.1, u.property.2.trans hrs⟩ : Set.Icc (0 : ℝ) s)).comp
        (measurable_pi_apply i)
  have hP : Measurable[MeasurableSpace.comap (besselPast T s) inferInstance]
      (besselPast T s) := measurable_iff_comap_le.mpr le_rfl
  exact (hR.comp hP).comap_le

/-- The full vector past sampled at any nondecreasing time grid forms a filtration. -/
noncomputable def besselPastFiltration (T : ℝ) (q : ℕ → ℝ) (hq : Monotone q) :
    Filtration ℕ (inferInstance : MeasurableSpace (Fin 3 → GaussianCoefficientSpace)) where
  seq n := MeasurableSpace.comap (besselPast T (q n)) inferInstance
  mono' := fun n m hnm ↦ besselPast_space_mono T (q n) (q m) (hq hnm)
  le' := fun n ↦ (besselPast_measurable T (q n)).comap_le

/-- The reciprocal radius is strongly adapted to the actual full-past filtration. -/
theorem bessel_inverse_stronglyAdapted (T x : ℝ) (q : ℕ → ℝ) (hq : Monotone q)
    (hpos : ∀ n, 0 ≤ q n) :
    StronglyAdapted (besselPastFiltration T q hq)
      (fun n ω ↦ (actualBesselThree T x (q n) ω)⁻¹) := by
  intro n
  have hP : Measurable[besselPastFiltration T q hq n] (besselPast T (q n)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact (((besselPastRadius_measurable x (q n) (hpos n)).inv).comp hP).stronglyMeasurable

end SRWTightness
