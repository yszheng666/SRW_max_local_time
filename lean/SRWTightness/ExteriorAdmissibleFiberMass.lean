import SRWTightness.ExteriorWordReplacement
import SRWTightness.ExteriorWordFiberSingleton
import SRWTightness.ExteriorBridgeNormalization
import SRWTightness.ListZipDivProduct

namespace SRWTightness

/-- Every admissible joint fiber has one common exterior normalization times its bridge product. -/
theorem exterior_admissible_fiber_mass (D K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (h : ExteriorPathRecord)
    (us : List PathWord) (hlen : us.length = h.1.length)
    (hgeom : ExteriorWordAdmissible D K C label x h)
    (he : ∀ slot ∈ h.1, 0 < traceExitProbability C slot.2.2.1 slot.2.2.2)
    (hwords : ∀ pair ∈ h.1.zip us,
      AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2) :
    pathLaw.real {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} =
        exteriorBridgeNormalization C h * exteriorBridgeWordProduct C h us := by
  obtain ⟨e, hw, hrec, hchild⟩ :=
    reassembleExteriorWord_admissible D K C label hKC hCD x h us hlen hgeom hwords
  have hf := exterior_word_fiber_cylinder_mass D K C label x e
    (reassembleExteriorWord h us) hw
  rw [hchild, hrec, reassembleExteriorWord_length h us hlen, pow_add] at hf
  have hsum (vs : List PathWord) :
      (1 / 4 : ℝ) ^ (vs.map PathWord.length).sum =
        (vs.map (fun v ↦ (1 / 4 : ℝ) ^ v.length)).prod := by
    induction vs with
    | nil => simp
    | cons v vs ih =>
      simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add, ih]
  rw [hsum] at hf
  have hprod : exteriorBridgeWordProduct C h us =
      ((h.1.zip us).map (fun pair ↦ (1 / 4 : ℝ) ^ pair.2.length /
        traceExitProbability C pair.1.2.2.1 pair.1.2.2.2)).prod := by
    unfold exteriorBridgeWordProduct
    congr 1
    apply List.map_congr_left
    intro pair hp
    exact killed_word_bridge_mass stoppedWordProbabilityInput_internal C _ _ _ (hwords pair hp)
  have hc := list_zip_div_product_cancel h.1 us
    (fun slot ↦ traceExitProbability C slot.2.2.1 slot.2.2.2)
    (fun v ↦ (1 / 4 : ℝ) ^ v.length) hlen (fun slot hs ↦ (he slot hs).ne')
  rw [hf, exteriorBridgeNormalization, hprod, mul_assoc, hc]

end SRWTightness
