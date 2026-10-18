import SRWTightness.ExitLocation
import SRWTightness.SetHitting

open MeasureTheory

namespace SRWTightness

/-- The one-step exterior boundary of a finite SRW domain. -/
def domainExitBoundary (D : Finset Site) : Set Site :=
  {y | y ∉ D ∧ ∃ z ∈ D, ∃ d : Direction, y = z + step d}

/-- Actual exit positions lie on the one-step exterior boundary when started inside. -/
theorem domainExitLocation_mem_boundary_ae (D : Finset Site) (x : Site) (hx : x ∈ D) :
    ∀ᵐ ω ∂pathLaw, domainExitLocation D x ω ∈ domainExitBoundary D := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  have hout : domainExitLocation D x ω ∉ D := position_domain_exit_not_mem D x ω hω
  refine ⟨hout, ?_⟩
  have hr := domainExitLocation_mem_range D x ω
  change domainExitLocation D x ω ∈
    insert x (D.biUnion (fun y ↦ Finset.univ.image (fun d : Direction ↦ y + step d))) at hr
  obtain he | hr := Finset.mem_insert.mp hr
  · exact False.elim (hout (he.symm ▸ hx))
  · obtain ⟨z, hz, hr⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨d, _, he⟩ := Finset.mem_image.mp hr
    exact ⟨z, hz, d, he.symm⟩

/-- Joint record/exit-position slice of the actual killed SRW, without an independence assumption. -/
noncomputable def recordExitSlice {R : Type*} (D : Finset Site) (x : Site)
    (F : Sample → R) (r : R) : Measure Site :=
  (pathLaw.restrict {ω | F ω = r}).map (domainExitLocation D x)

instance recordExitSlice_isFiniteMeasure {R : Type*} (D : Finset Site) (x : Site)
    (F : Sample → R) (r : R) : IsFiniteMeasure (recordExitSlice D x F r) := by
  unfold recordExitSlice
  infer_instance

/-- The total mass of a joint exit slice is exactly the probability of its specified record. -/
theorem recordExitSlice_mass {R : Type*} (D : Finset Site) (x : Site)
    (F : Sample → R) (r : R) :
    (recordExitSlice D x F r).real Set.univ = pathLaw.real {ω | F ω = r} := by
  unfold recordExitSlice
  rw [measureReal_def, Measure.map_apply (measurable_domainExitLocation D x) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ]
  rfl

/-- Restricting to any record preserves the actual exit-boundary support. -/
theorem recordExitSlice_supported {R : Type*} (D : Finset Site) (x : Site) (hx : x ∈ D)
    (F : Sample → R) (r : R) :
    ∀ᵐ y ∂recordExitSlice D x F r, y ∈ domainExitBoundary D := by
  unfold recordExitSlice
  apply (ae_map_iff (measurable_domainExitLocation D x).aemeasurable
    (Set.to_countable _ |>.measurableSet)).mpr
  exact ae_restrict_of_ae (domainExitLocation_mem_boundary_ae D x hx)

end SRWTightness
