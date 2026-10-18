import SRWTightness.PairResidualProductLaw
import SRWTightness.GaussianResidualWindowProduct

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- A measurable pair event inherits the independent residual section bound after reconstruction. -/
theorem pair_residual_event_upper {n : ℕ} (last : Fin n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure (ℕ → GaussianCoefficientSpace)) [IsProbabilityMeasure ν]
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosDef) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, (gaussianCovarianceDensity R x).toReal ≤ C)
    (ρ : Measure (PairObservationIndex n → ℝ))
    (hρ : ρ = (μ.prod (gaussianCoordinateLaw R)).map (pairResidualCoordinates last))
    (s : Set ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace))) (hs : MeasurableSet s)
    (E : Set ((PairObservationIndex n → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (hE : MeasurableSet E)
    (a : ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) → Fin 2 → ℝ)
    (ha : Measurable a)
    (hsub : ∀ᵐ ω ∂ν, ∀ (x : Fin n → ℝ) (r : Fin 2 → ℝ),
      (pairResidualCoordinates last (x, r), ω) ∈ E →
        (x, ω) ∈ s ∧ ∀ j, a (x, ω) j ≤ r j ∧ r j < a (x, ω) j + 1) :
    (ρ.prod ν).real E ≤ C * (μ.prod ν).real s := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure R
  have hm : Measurable (fun p : ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) ×
      (Fin 2 → ℝ) ↦ (pairResidualCoordinates last (p.1.1, p.2), p.1.2)) :=
    ((pairResidualCoordinates_measurable last).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)
  rw [pair_residual_auxiliary_law last μ (gaussianCoordinateLaw R) ν ρ hρ,
    map_measureReal_apply hm hE]
  have hbase := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hsub
  have hall := (Measure.quasiMeasurePreserving_fst (μ := μ.prod ν)
    (ν := gaussianCoordinateLaw R)).ae hbase
  have hmono : ((μ.prod ν).prod (gaussianCoordinateLaw R))
      ((fun p ↦ (pairResidualCoordinates last (p.1.1, p.2), p.1.2)) ⁻¹' E) ≤
      ((μ.prod ν).prod (gaussianCoordinateLaw R))
        {p | p.1 ∈ s ∧ ∀ j, a p.1 j ≤ p.2 j ∧ p.2 j < a p.1 j + 1} := by
    apply measure_mono_ae
    filter_upwards [hall] with p hp
    exact hp p.1.1 p.2
  exact (ENNReal.toReal_mono (measure_ne_top _ _) hmono).trans
    (gaussian_residual_window_product (μ.prod ν) R hR C hC hbound s hs a ha)

end SRWTightness
