import SRWTightness.SourceCandidateAnnulus

namespace SRWTightness

/-- All candidates at closed Euclidean distance at most A from a specified candidate. -/
noncomputable def latticeCloseNeighbors (Z : Finset Site) (A : ℝ) (b : Z) : Finset Z := by
  classical
  exact Finset.univ.filter (fun w ↦ Real.sqrt (normSq ((w : Site) - (b : Site))) ≤ A)

/-- Translation injects the closed neighborhood into a fixed finite disk, uniformly in Z and b. -/
theorem lattice_close_neighbors_card (Z : Finset Site) (A : ℝ) (b : Z) :
    (latticeCloseNeighbors Z A b).card ≤ (diskFinset (|A| + 1)).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun w : Z ↦ (w : Site) - (b : Site))
  · intro w hw
    have hh : Real.sqrt (normSq ((w : Site) - (b : Site))) ≤ A :=
      (Finset.mem_filter.mp hw).2
    change ((w : Site) - (b : Site)) ∈ diskFinset (|A| + 1)
    rw [mem_diskFinset]
    change normSq ((w : Site) - (b : Site)) < (|A| + 1) ^ 2
    have hs := Real.sq_sqrt (normSq_nonneg ((w : Site) - (b : Site)))
    have hp := Real.sqrt_nonneg (normSq ((w : Site) - (b : Site)))
    have ha := le_abs_self A
    have ha0 := abs_nonneg A
    nlinarith
  · intro v hv w hw he
    apply Subtype.ext
    change (v : Site) - (b : Site) = (w : Site) - (b : Site) at he
    have he' := congrArg (fun x : Site ↦ x + (b : Site)) he
    simpa only [sub_add_cancel] using he'

end SRWTightness
