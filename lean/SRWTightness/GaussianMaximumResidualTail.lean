import SRWTightness.GaussianRegressionMaximaTransport

open MeasureTheory Set
namespace SRWTightness

/-- The upper tail of the actual residual-sum law is the previously estimated product event. -/
theorem finiteGaussianMaximumResidualLaw_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m u : ℝ) :
    (finiteGaussianMaximumResidualLaw S T J hJ σ m).real (Ici u) =
      ((finiteGaussianPositiveMaximumLaw S J hJ σ m).prod
        (finiteGaussianAbsMaximumLaw T J hJ)).real {p | u ≤ p.1 + p.2} := by
  rw [finiteGaussianMaximumResidualLaw,
    map_measureReal_apply (show Measurable (fun p : ℝ × ℝ ↦ p.1 + p.2) by fun_prop)
      measurableSet_Ici]
  rfl

end SRWTightness
