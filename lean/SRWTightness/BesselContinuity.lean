import SRWTightness.ExternalBesselThree

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual three-coordinate radial construction has continuous paths almost surely. -/
theorem actualBesselThree_ae_continuous (T x : ℝ) :
    ∀ᵐ ω ∂independentBridgeLaw (Fin 3), Continuous (fun t ↦ actualBesselThree T x t ω) := by
  have hh : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      ∀ i : Fin 3, Continuous (fun t ↦ gaussianDyadicPath (ω i) t) := by
    apply ae_all_iff.mpr
    intro i
    have hp := measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw) i
    exact hp.quasiMeasurePreserving.ae gaussianDyadicPath_ae_continuous
  filter_upwards [hh] with ω hω
  unfold actualBesselThree
  apply Continuous.sqrt
  apply continuous_finset_sum
  intro i hi
  exact (continuous_const.add (continuous_const.mul
    ((hω i).comp (continuous_id.div_const T)))).pow 2

end SRWTightness
