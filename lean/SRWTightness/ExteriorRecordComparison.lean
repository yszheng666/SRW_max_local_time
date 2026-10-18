import SRWTightness.ExteriorRecordProductLaw

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

/-- Local prescribed-exit record comparisons tensorize over all actual exterior slots. -/
theorem exterior_record_product_comparison {R : Type*} (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (F : ExteriorSlot → PathWord → R) (r : Fin h.1.length → R)
    (q E : Fin h.1.length → ℝ)
    (hloc : ∀ i, let s := h.1.get i
      let a := (killedWordBridgeLaw (if s.2.1 then C₁ else C₀) s.2.2.1 s.2.2.2).real
        {u | F s u = r i}
      Real.exp (-E i) * q i ≤ a ∧ a ≤ Real.exp (E i) * q i) :
    let mass := (exteriorIndependentWordLaw C₀ C₁ h).real
      {us | (h.1.zip us).map (fun p ↦ F p.1 p.2) = List.ofFn r}
    Real.exp (-(∑ i, E i)) * (∏ i, q i) ≤ mass ∧
      mass ≤ Real.exp (∑ i, E i) * ∏ i, q i := by
  dsimp only
  have hm : (exteriorIndependentWordLaw C₀ C₁ h).real
      {us | (h.1.zip us).map (fun p ↦ F p.1 p.2) = List.ofFn r} =
      ∏ i, (killedWordBridgeLaw (if (h.1.get i).2.1 then C₁ else C₀)
        (h.1.get i).2.2.1 (h.1.get i).2.2.2).real {u | F (h.1.get i) u = r i} := by
    rw [exterior_record_product_law]
    apply Finset.prod_congr rfl
    intro i _
    exact (killedWordBridgeLaw_record _ _ _ _ _).symm
  rw [hm]
  exact finite_product_exponential_comparison _ q E (fun _ ↦ measureReal_nonneg) hloc

/-- Every event of the complete word list inherits the actual exterior conditional measure. -/
theorem exterior_conditional_word_event (hF : ExteriorBridgeFactorizationInput)
    (D K₀ K₁ C₀ C₁ : Finset Site) (x : Site)
    (hK₀ : K₀ ⊆ C₀) (hK₁ : K₁ ⊆ C₁) (hCD : C₀ ∪ C₁ ⊆ D)
    (hgap₀ : ∀ y ∈ domainExitBoundary C₀, y ∉ C₁)
    (hgap₁ : ∀ y ∈ domainExitBoundary C₁, y ∉ C₀)
    (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
      (twoDomainExteriorLabel K₁) x ω = h}) (S : Set (List PathWord)) :
    pathLaw.real {ω | killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ u ↦ u) ω ∈ S ∧
      killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x ω = h} /
      pathLaw.real {ω | killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁)
        (twoDomainExteriorLabel K₁) x ω = h} = (exteriorIndependentWordLaw C₀ C₁ h).real S := by
  let U := killedChildRecords D (K₀ ∪ K₁) (C₀ ∪ C₁) x (fun _ u ↦ u)
  let Z := killedExteriorRecord D (K₀ ∪ K₁) (C₀ ∪ C₁) (twoDomainExteriorLabel K₁) x
  have hU : Measurable U := measurable_killedChildRecords _ _ _ _ _
  have he := congrArg (fun μ : Measure (List PathWord) ↦ μ.real S)
    (exterior_conditional_word_law hF D K₀ K₁ C₀ C₁ x hK₀ hK₁ hCD hgap₀ hgap₁ h hh)
  rw [map_measureReal_apply hU (Set.to_countable S).measurableSet] at he
  have hc : (ProbabilityTheory.cond pathLaw {ω | Z ω = h}).real (U ⁻¹' S) =
      pathLaw.real {ω | U ω ∈ S ∧ Z ω = h} / pathLaw.real {ω | Z ω = h} := by
    unfold Measure.real
    rw [ProbabilityTheory.cond_apply' (hU (Set.to_countable S).measurableSet),
      ENNReal.toReal_mul, ENNReal.toReal_inv]
    change (pathLaw.real {ω | Z ω = h})⁻¹ * pathLaw.real {ω | Z ω = h ∧ U ω ∈ S} = _
    rw [show {ω | Z ω = h ∧ U ω ∈ S} = {ω | U ω ∈ S ∧ Z ω = h} by ext; exact and_comm]
    exact (div_eq_inv_mul _ _).symm
  exact hc.symm.trans he

end SRWTightness
