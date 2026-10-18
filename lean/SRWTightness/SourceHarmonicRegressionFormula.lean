import SRWTightness.GaussianRegressionInternal
import SRWTightness.ExternalBufferedSquareGreen
import SRWTightness.SquareHarmonicRegressionBounds
import SRWTightness.HarmonicRegressionAnchor

open MeasureTheory ProbabilityTheory Matrix
namespace SRWTightness

/-- Literal harmonic coefficients on the actual buffered source squares retain a uniform C/v bound.
-/
theorem source_buffered_harmonic_regression_coefficient (hGreen : BufferedSquareGreenInput) :
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧
      ∀ (D E : Finset Site) (a b : Site) (m n : ℕ),
        D = latticeSquareInterior b (2 ^ m) → E = latticeSquareInterior a (2 ^ n) →
        2 ≤ n → n ≤ m → E ⊆ D →
        B + 1 ≤ Real.log ((2 : ℝ) ^ m) - Real.log ((2 : ℝ) ^ n) → ∀ o x : E,
        squareProportionalBuffer δ a (2 ^ n) x →
        squareProportionalBuffer δ a (2 ^ n) o →
        squareProportionalBuffer δ b (2 ^ m) x →
        squareProportionalBuffer δ b (2 ^ m) o →
        let S := normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))
        0 < S o o ∧
        |S o o - (Real.log ((2 : ℝ) ^ m) - Real.log ((2 : ℝ) ^ n))| ≤ B ∧
        |S x o / S o o - 1| ≤ C / S o o := by
  intro δ hδ hδhalf
  obtain ⟨C₀, L, B, hC₀, hL, hB, hh⟩ := hGreen δ hδ hδhalf
  refine ⟨C₀ + 4 * L, B, by linarith, hB, ?_⟩
  intro D E a b m n hD hE hn hnm hED hgap o x hx ho hxD hoD
  dsimp only
  have he := hh D E a b m n hD hE hn hnm hED o o ho ho hoD hoD
  have hv : 0 < normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi)) o o := by
    have hbounds := abs_le.mp he.2.2
    linarith
  have hf := hh D E a b m n hD hE hn hnm hED x o hx ho hxD hoD
  refine ⟨hv, he.2.2, ?_⟩
  apply square_harmonic_regression_coefficient D E hED a (2 ^ n) hE
    (by positivity) (Real.sqrt (2 / Real.pi)) o x C₀ L hC₀ hL.le hv hf.1
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hf.2.1

/-- The normalized actual harmonic law has independent reference scalar and anchored residual. -/
theorem source_harmonic_regression_formula_internal (D E : Finset Site) (hED : E ⊆ D)
    (σ : ℝ) (o : E) (hv : 0 < normalizedHarmonicCov D E σ o o) :
    let S := normalizedHarmonicCov D E σ
    let μ := gaussianReal 0 (S o o).toNNReal
    let ν := multivariateGaussian (0 : EuclideanSpace ℝ E) (finiteGaussianRegressionCov S o)
    (μ.prod ν).map (finiteGaussianRegressionRebuild S o) =
        multivariateGaussian (0 : EuclideanSpace ℝ E) S ∧
      IndepFun Prod.fst Prod.snd (μ.prod ν) ∧
      (∀ᵐ η ∂ν, η o = 0) ∧
      (∀ x y : E,
        covariance (fun η : EuclideanSpace ℝ E ↦ η x) (fun η ↦ η x) ν +
          covariance (fun η : EuclideanSpace ℝ E ↦ η y) (fun η ↦ η y) ν -
          2 * covariance (fun η : EuclideanSpace ℝ E ↦ η x) (fun η ↦ η y) ν ≤
            S x x + S y y - 2 * S x y) := by
  dsimp only
  have hS := normalizedHarmonicCov_posSemidef D E hED σ
  have hR := finite_gaussian_regression_cov_posSemidef _ o hS hv
  refine ⟨(finite_gaussian_regression_input_internal E _ o hS hv).2, ?_,
    finite_gaussian_regression_anchor_ae _ o hv hR, ?_⟩
  · exact indepFun_prod measurable_id measurable_id
  · intro x y
    rw [covariance_eval_multivariateGaussian hR x x,
      covariance_eval_multivariateGaussian hR y y,
      covariance_eval_multivariateGaussian hR x y]
    exact finite_gaussian_regression_increment _ o x y hv

/-- Each coordinate of the reconstruction has the literal regression form in source(4.6). -/
theorem source_harmonic_regression_coordinate {ι : Type*} [Fintype ι]
    (S : Matrix ι ι ℝ) (o x : ι) (V : ℝ) (η : EuclideanSpace ℝ ι) :
    finiteGaussianRegressionRebuild S o (V, η) x = S x o / S o o * V + η x := rfl

end SRWTightness
