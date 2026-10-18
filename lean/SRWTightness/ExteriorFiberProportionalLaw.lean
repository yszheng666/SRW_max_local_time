import SRWTightness.ExteriorAdmissibleFiberMass
import SRWTightness.ExteriorWordFiberZero
import SRWTightness.ExteriorAtomAdmissibility
import SRWTightness.ExteriorExitPositiveInternal
import SRWTightness.ExteriorWordLawMass

namespace SRWTightness

/-- All actual exterior/internal-word fibers share the same independent-bridge normalization. -/
theorem exterior_fiber_proportional_law (D K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hCD : C ⊆ D) (x : Site) (h : ExteriorPathRecord)
    (hh : 0 < pathLaw.real {ω | killedExteriorRecord D K C label x ω = h})
    (us : List PathWord) :
    pathLaw.real {ω | killedChildRecords D K C x (fun _ u ↦ u) ω = us ∧
      killedExteriorRecord D K C label x ω = h} =
        exteriorBridgeNormalization C h * (exteriorIndependentWordLaw C C h).real {us} := by
  by_cases hlen : us.length = h.1.length
  · have heq : (exteriorIndependentWordLaw C C h).real {us} =
        exteriorBridgeWordProduct C h us := by
      simpa only [labeledExteriorBridgeWordProduct, exteriorBridgeWordProduct, ite_self] using
        exteriorIndependentWordLaw_singleton C C h us hlen
    rw [heq]
    by_cases hw : ∀ pair ∈ h.1.zip us,
        AdmissibleExitWord C pair.1.2.2.1 pair.1.2.2.2 pair.2
    · exact exterior_admissible_fiber_mass D K C label hKC hCD x h us hlen
        (exterior_atom_admissible D K C label hKC hCD x h hh)
        (exterior_atom_exit_positive_internal D K C hKC label x h hh) hw
    · rw [exterior_word_fiber_zero_of_not_admissible D K C hKC label x h us hw,
        exteriorBridgeWordProduct_zero_of_not_admissible C h us hw, mul_zero]
  · rw [exterior_word_fiber_zero_wrong_length D K C label x h us hlen,
      exteriorIndependentWordLaw_wrong_length C C h us hlen, mul_zero]

end SRWTightness
