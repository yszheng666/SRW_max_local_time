import SRWTightness.BesselInverseSupermartingale
import SRWTightness.NonnegativeSupermartingaleMaximal

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Every finite positive-time grid has the sharp delayed radial hitting bound. -/
theorem bessel_finite_grid_hitting (T x b : ℝ) (hT : 0 < T) (hx : 0 < x) (hb : 0 < b)
    (q : ℕ → ℝ) (hq : Monotone q) (hpos : ∀ n, 0 < q n) (hupper : ∀ n, q n ≤ T)
    (N : ℕ) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ j ≤ N, actualBesselThree T x (q j) ω ≤ b} ≤
        b * ∫ ω, (actualBesselThree T x (q 0) ω)⁻¹ ∂independentBridgeLaw (Fin 3) := by
  let μ := independentBridgeLaw (Fin 3)
  have hS := bessel_inverse_supermartingale T x hT hx q hq hpos hupper
  have hmax := nonnegative_supermartingale_maximal μ (besselPastFiltration T q hq)
    (fun n ω ↦ (actualBesselThree T x (q n) ω)⁻¹) hS
    (fun n ω ↦ inv_nonneg.mpr (Real.sqrt_nonneg _)) (1 / b) N
  have hp : ∀ᵐ ω ∂μ, ∀ j : ℕ, 0 < actualBesselThree T x (q j) ω := by
    apply ae_all_iff.mpr
    intro j
    exact bessel_three_positive_input_internal T x (q j) hT hx (hpos j) (hupper j)
  have hsub : {ω | ∃ j ≤ N, actualBesselThree T x (q j) ω ≤ b} ≤ᵐ[μ]
      {ω | ∃ j ≤ N, 1 / b ≤ (actualBesselThree T x (q j) ω)⁻¹} := by
    filter_upwards [hp] with ω hω
    rintro ⟨j, hj, hh⟩
    refine ⟨j, hj, ?_⟩
    simpa only [one_div] using one_div_le_one_div_of_le (hω j) hh
  have hmeasure := measure_mono_ae hsub
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
  have hmul := (mul_le_mul_of_nonneg_left hreal (by positivity : 0 ≤ 1 / b)).trans hmax
  have he : (1 / b) * μ.real {ω | ∃ j ≤ N, actualBesselThree T x (q j) ω ≤ b} =
      μ.real {ω | ∃ j ≤ N, actualBesselThree T x (q j) ω ≤ b} / b := by ring
  change (1 / b) * μ.real {ω | ∃ j ≤ N, actualBesselThree T x (q j) ω ≤ b} ≤ _ at hmul
  rw [he] at hmul
  simpa only [mul_comm] using (div_le_iff₀ hb).mp hmul

end SRWTightness
