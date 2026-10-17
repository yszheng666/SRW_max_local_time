import SRWTightness.SourceConditionalPairLaw

open MeasureTheory
namespace SRWTightness

/-- Any measurable path record retains its product law with the two selected auxiliaries after
conditioning on the actual exterior event. -/
theorem source_conditional_path_map_pair {R : Type*} [MeasurableSpace R]
    (f : Sample → R) (hf : Measurable f) (t : ℝ) (b w : Site) (ν J : ℕ)
    (hbw : b ≠ w) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) :
    MeasurePreserving
      (fun p : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦ (f p.1, (p.2 b, p.2 w)))
      (ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h})
      (((ProbabilityTheory.cond pathLaw
        {ω | sourcePairExteriorRecord t b w ν J ω = h}).map f).prod
          ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ))) := by
  have hμ : pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h} ≠ 0 := by
    intro hz
    exact hh.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)
  letI := ProbabilityTheory.cond_isProbabilityMeasure hμ
  have hm : MeasurePreserving f
      (ProbabilityTheory.cond pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h})
      ((ProbabilityTheory.cond pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h}).map f) :=
    ⟨hf, rfl⟩
  exact (hm.prod (MeasurePreserving.id
    ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ)))).comp
      (source_conditional_pair_preserving t b w ν J hbw h)

end SRWTightness
