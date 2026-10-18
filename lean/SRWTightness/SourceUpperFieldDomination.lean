import SRWTightness.FiniteGaussianPositiveMaximumLaw
import SRWTightness.HarmonicRegressionBounds

open MeasureTheory Set
namespace SRWTightness

/-- Fine-field and regression coordinates are dominated by the two actual maxima. -/
theorem source_upper_field_pointwise_domination {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (F η : EuclideanSpace ℝ ι)
    (x : ι) (hx : x ∈ J) (σ m b v C t : ℝ)
    (hv : 0 < v) (hCv : C ≤ v) (hb : |b - 1| ≤ C / v) :
    F x / σ + (b * t + η x) ≤ m + (1 + C / v) * max t 0 +
      (finiteGaussianPositiveMaximum J hJ σ m F + finiteGaussianAbsMaximum J hJ η) := by
  have hFine : F x / σ ≤ m + finiteGaussianPositiveMaximum J hJ σ m F := by
    have hx' := Finset.le_sup' (fun y ↦ F y / σ) hx
    have hm := le_max_left (J.sup' hJ (fun y ↦ F y / σ) - m) 0
    change F x / σ ≤ m + max (J.sup' hJ (fun y ↦ F y / σ) - m) 0
    linarith
  have hRes : |η x| ≤ finiteGaussianAbsMaximum J hJ η :=
    Finset.le_sup' (fun y ↦ |η y|) hx
  have hReg := gaussian_regression_pointwise_domination b v C t (η x) hv hCv hb
  linarith

/-- Exceedance by the reconstructed field implies exceedance by the scalar and two maxima. -/
theorem source_upper_field_event_subset {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o : ι) (J : Finset ι) (hJ : J.Nonempty) (σ m C a : ℝ)
    (hv : 0 < S o o) (hCv : C ≤ S o o)
    (hb : ∀ x ∈ J, |S x o / S o o - 1| ≤ C / S o o) :
    {p : EuclideanSpace ℝ ι × (ℝ × EuclideanSpace ℝ ι) |
      ∃ x ∈ J, a ≤ p.1 x / σ + finiteGaussianRegressionRebuild S o p.2 x} ⊆
    {p | a - m ≤ (1 + C / S o o) * max p.2.1 0 +
      (finiteGaussianPositiveMaximum J hJ σ m p.1 +
        finiteGaussianAbsMaximum J hJ p.2.2)} := by
  rintro ⟨F, t, η⟩ ⟨x, hx, hax⟩
  have ht := source_upper_field_pointwise_domination J hJ F η x hx σ m
    (S x o / S o o) (S o o) C t hv hCv (hb x hx)
  change a ≤ F x / σ + (S x o / S o o * t + η x) at hax
  change a - m ≤ (1 + C / S o o) * max t 0 +
    (finiteGaussianPositiveMaximum J hJ σ m F + finiteGaussianAbsMaximum J hJ η)
  linarith

/-- The field-to-scalar event comparison on the actual joint probability space. -/
theorem source_upper_field_probability_domination {ι : Type*} [Fintype ι]
    (ρ : Measure (EuclideanSpace ℝ ι × (ℝ × EuclideanSpace ℝ ι))) [IsFiniteMeasure ρ]
    (S : Matrix ι ι ℝ) (o : ι) (J : Finset ι) (hJ : J.Nonempty) (σ m C a : ℝ)
    (hv : 0 < S o o) (hCv : C ≤ S o o)
    (hb : ∀ x ∈ J, |S x o / S o o - 1| ≤ C / S o o) :
    ρ.real {p | ∃ x ∈ J,
      a ≤ p.1 x / σ + finiteGaussianRegressionRebuild S o p.2 x} ≤
    ρ.real {p | a - m ≤ (1 + C / S o o) * max p.2.1 0 +
      (finiteGaussianPositiveMaximum J hJ σ m p.1 +
        finiteGaussianAbsMaximum J hJ p.2.2)} := by
  exact measureReal_mono
    (source_upper_field_event_subset S o J hJ σ m C a hv hCv hb) (measure_ne_top _ _)

end SRWTightness
