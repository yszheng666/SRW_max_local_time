import SRWTightness.ExteriorWordLawMass
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory
namespace SRWTightness

/-- The complete actual internal-word law conditional on a positive exterior record equals the
ordered independent selected-domain bridge law. This is equality of measures, not just atom bounds. -/
theorem exterior_conditional_word_law (hF : ExteriorBridgeFactorizationInput)
    (D K₀ K₁ C₀ C₁ : Finset Site) (x : Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hCD : C₀ ∪ C₁ ⊆ D)
    (hgap₀ : ∀ y ∈ domainExitBoundary C₀, y ∉ C₁)
    (hgap₁ : ∀ y ∈ domainExitBoundary C₁, y ∉ C₀)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h}) :
    (ProbabilityTheory.cond pathLaw {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h}).map
        (killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ u ↦ u)) =
      exteriorIndependentWordLaw C₀ C₁ h := by
  let Z := killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x
  let U := killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ u ↦ u)
  have hμ : pathLaw {ω | Z ω = h} ≠ 0 := by
    intro hz
    exact hh.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)
  letI := ProbabilityTheory.cond_isProbabilityMeasure hμ
  letI := exteriorIndependentWordLaw_isProbabilityMeasure C₀ C₁ h
    (exterior_atom_exit_positive hF D K₀ K₁ C₀ C₁ x hK₀ hK₁ hCD hgap₀ hgap₁ h hh)
  have hU : Measurable U := measurable_killedChildRecords _ _ _ _ _
  letI : IsProbabilityMeasure ((ProbabilityTheory.cond pathLaw {ω | Z ω = h}).map U) :=
    Measure.isProbabilityMeasure_map hU.aemeasurable
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro us
  have hc : ((ProbabilityTheory.cond pathLaw {ω | Z ω = h}).map U).real {us} =
      pathLaw.real {ω | U ω = us ∧ Z ω = h} / pathLaw.real {ω | Z ω = h} := by
    rw [map_measureReal_apply hU (measurableSet_singleton _)]
    unfold Measure.real
    rw [ProbabilityTheory.cond_apply' (hU (measurableSet_singleton _)),
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    change (pathLaw.real {ω | Z ω = h})⁻¹ * pathLaw.real {ω | Z ω = h ∧ U ω = us} = _
    rw [show {ω | Z ω = h ∧ U ω = us} = {ω | U ω = us ∧ Z ω = h} by ext; exact and_comm]
    exact (div_eq_inv_mul _ _).symm
  rw [hc]
  by_cases hlen : us.length = h.1.length
  · rw [exteriorIndependentWordLaw_singleton C₀ C₁ h us hlen]
    exact exterior_two_domain_bridges hF D K₀ K₁ C₀ C₁ x hK₀ hK₁ hCD hgap₀ hgap₁ h hh us hlen
  · rw [exteriorIndependentWordLaw_wrong_length C₀ C₁ h us hlen]
    have hs : {ω | U ω = us ∧ Z ω = h} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      have he := killedExteriorRecord_length D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x ω
      change (Z ω).1.length = (U ω).length at he
      rw [hω.1, hω.2] at he
      exact hlen he.symm
    rw [hs, measureReal_empty, zero_div]

end SRWTightness
