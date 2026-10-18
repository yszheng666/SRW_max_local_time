import SRWTightness.PotentialFourierBounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace SRWTightness

noncomputable def fourierIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc (-Real.pi) Real.pi)

instance fourierIntervalMeasure_isFiniteMeasure : IsFiniteMeasure fourierIntervalMeasure := by
  constructor
  simpa [fourierIntervalMeasure] using
    (isCompact_Icc : IsCompact (Set.Icc (-Real.pi) Real.pi)).measure_lt_top (μ := (volume : Measure ℝ))

noncomputable def fourierBoxMeasure : Measure (ℝ × ℝ) := fourierIntervalMeasure.prod fourierIntervalMeasure

instance fourierBoxMeasure_isFiniteMeasure : IsFiniteMeasure fourierBoxMeasure := by
  unfold fourierBoxMeasure
  infer_instance

theorem fourierIntervalMeasure_support : ∀ᵐ t ∂fourierIntervalMeasure, |t| ≤ Real.pi := by
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
  exact abs_le.mpr ht

theorem fourierBoxMeasure_support : ∀ᵐ θ ∂fourierBoxMeasure,
    |θ.1| ≤ Real.pi ∧ |θ.2| ≤ Real.pi := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := fourierIntervalMeasure)
    (ν := fourierIntervalMeasure)).ae fourierIntervalMeasure_support
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := fourierIntervalMeasure)
    (ν := fourierIntervalMeasure)).ae fourierIntervalMeasure_support
  exact h1.and h2

theorem integrable_potentialFourierIntegrand (z : Site) :
    Integrable (potentialFourierIntegrand z) fourierBoxMeasure := by
  apply (integrable_const (Real.pi ^ 2 * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2))).mono'
    (measurable_potentialFourierIntegrand z).aestronglyMeasurable
  filter_upwards [fourierBoxMeasure_support] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (potentialFourierIntegrand_nonneg z θ)]
  exact potentialFourierIntegrand_bound z θ hθ.1 hθ.2

/-- The real Fourier integral for the planar simple-random-walk potential kernel. -/
noncomputable def potentialKernel (z : Site) : ℝ :=
  (4 * Real.pi ^ 2)⁻¹ * ∫ θ, potentialFourierIntegrand z θ ∂fourierBoxMeasure

theorem potentialKernel_zero : potentialKernel (0 : Site) = 0 := by
  simp [potentialKernel, potentialFourierIntegrand, fourierPhase]

theorem potentialKernel_nonneg (z : Site) : 0 ≤ potentialKernel z := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (potentialFourierIntegrand_nonneg z)

theorem potentialKernel_neg (z : Site) : potentialKernel (-z) = potentialKernel z := by
  unfold potentialKernel
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  unfold potentialFourierIntegrand fourierPhase
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_mul, ← neg_add, Real.cos_neg]

end SRWTightness
