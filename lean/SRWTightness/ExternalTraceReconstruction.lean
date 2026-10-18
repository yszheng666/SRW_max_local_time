import SRWTightness.ExternalKilledTraceFactorization
import SRWTightness.ActualChildRecords

open MeasureTheory
namespace SRWTightness

/-- Standard finite-word reconstruction: a trace containing a child domain and its one-step
boundary determines the complete child words, without their absolute times or outside gaps.
This is an explicit deterministic foundation, with no probability or comparison estimate. -/
def TraceExcursionReconstructionInput : Prop :=
  ∀ (K C E : Finset Site) (x : Site), K ⊆ C → C ⊆ E →
    (∀ z ∈ domainExitBoundary C, z ∈ E) →
    ∃ decode : List Site → List (Site × PathWord), ∀ w : PathWord,
      x + position (wordPath w) w.length ∉ E →
      decode (wordVisitTrace E x w) =
        wordChildRecords K C x (fun y u ↦ (y, u)) w

/-- Generic deterministic reconstruction identifies the actual killed child records almost surely. -/
theorem killed_child_records_trace_representation (hR : TraceExcursionReconstructionInput)
    {M : Type*} (D K C E : Finset Site) (x : Site) (F : Site → PathWord → M)
    (hKC : K ⊆ C) (hCE : C ⊆ E) (hED : E ⊆ D)
    (hboundary : ∀ z ∈ domainExitBoundary C, z ∈ E) :
    ∃ g : List Site → List M,
      killedChildRecords D K C x F =ᵐ[pathLaw] fun ω ↦ g (killedVisitTrace D E x ω) := by
  obtain ⟨decode, hd⟩ := hR K C E x hKC hCE hboundary
  refine ⟨fun ξ ↦ (decode ξ).map (fun q ↦ F q.1 q.2), ?_⟩
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  have hw := hd (killedPathWord D x ω)
    (killedPathWord_endpoint_outside_child D E hED x ω hfin)
  dsimp only [killedVisitTrace]
  rw [hw]
  simp only [killedChildRecords, wordChildRecords, List.map_map, Function.comp_def]

end SRWTightness
