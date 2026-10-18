import SRWTightness.SourceLocalTimeSuccessMeasurable

open MeasureTheory

namespace SRWTightness

/-- Independent complete bridge families at every lattice site. -/
noncomputable def sourceSiteBridgeLaw : Measure (Site → ℕ → GaussianCoefficientSpace) :=
  Measure.infinitePi (fun _ : Site ↦ independentBridgeLaw ℕ)

instance sourceSiteBridgeLaw_probability : IsProbabilityMeasure sourceSiteBridgeLaw := by
  unfold sourceSiteBridgeLaw
  infer_instance

/-- The manuscript common enlarged space retains a single shared SRW path. -/
noncomputable def sourceEnlargedLaw : Measure (Sample × (Site → ℕ → GaussianCoefficientSpace)) :=
  pathLaw.prod sourceSiteBridgeLaw

instance sourceEnlargedLaw_probability : IsProbabilityMeasure sourceEnlargedLaw := by
  unfold sourceEnlargedLaw
  infer_instance

/-- Project the shared walk and the auxiliary bridges of one specified site. -/
def sourceSiteProjection (b : Site)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace)) :
    Sample × (ℕ → GaussianCoefficientSpace) := (p.1, p.2 b)

/-- The one-site marginal is exactly the product law used in the one-point estimates. -/
theorem source_site_projection_preserving (b : Site) :
    MeasurePreserving (sourceSiteProjection b) sourceEnlargedLaw
      (pathLaw.prod (independentBridgeLaw ℕ)) := by
  exact (MeasurePreserving.id pathLaw).prod
    (measurePreserving_eval_infinitePi (fun _ : Site ↦ independentBridgeLaw ℕ) b)

/-- A site success event on the common manuscript probability space. -/
def sourceSiteSuccessEvent (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))) :
    Set (Sample × (Site → ℕ → GaussianCoefficientSpace)) :=
  sourceSiteProjection b ⁻¹' sourceLocalTimeSuccessEvent t A γ b I z

/-- Passing to the common auxiliary space preserves each original continuous success probability. -/
theorem source_site_success_probability (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hs : NullMeasurableSet (sourceLocalTimeSuccessEvent t A γ b I z)
      (pathLaw.prod (independentBridgeLaw ℕ))) :
    sourceEnlargedLaw.real (sourceSiteSuccessEvent t A γ b I z) =
      (pathLaw.prod (independentBridgeLaw ℕ)).real (sourceLocalTimeSuccessEvent t A γ b I z) :=
  (source_site_projection_preserving b).measureReal_preimage hs

/-- The lifted site event remains measurable up to null sets. -/
theorem source_site_success_nullMeasurable (t A γ : ℝ) (b : Site) (I : ℕ)
    (z : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hs : NullMeasurableSet (sourceLocalTimeSuccessEvent t A γ b I z)
      (pathLaw.prod (independentBridgeLaw ℕ))) :
    NullMeasurableSet (sourceSiteSuccessEvent t A γ b I z) sourceEnlargedLaw :=
  hs.preimage (source_site_projection_preserving b).quasiMeasurePreserving

end SRWTightness
