import SRWTightness.ExternalExteriorCountInvariance
import SRWTightness.SourcePrefixLevelGeometry
import SRWTightness.SourceWalkSuccessEvent

namespace SRWTightness

/-- The complete original source count prefix is determined by the erased exterior record.
All source-specific domain hypotheses are explicit; the generic finite-word invariance is the only input. -/
theorem source_prefix_count_representation (hF : ExteriorNestedCountInvarianceInput)
    (t : ℝ) (b : Site) (j : ℕ) (K C : Finset Site) (label : Site → Bool)
    (hKC : K ⊆ C) (hm : 16 ≤ sourceLowerRadius t)
    (hj : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t))
    (hC : C ⊆ sourceEntranceDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b j)
    (hB : domainExitBoundary C ⊆ (sourceEntranceDomain (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b j : Set Site)) :
    ∃ g : ExteriorPathRecord → ℕ → ℕ, ∀ ω : Sample, ∀ i ≤ j,
      g (killedExteriorRecord (diskFinset (Real.exp t)) K C label 0 ω) i =
        sourceActualCount t b i ω := by
  classical
  have hcount (ω ω' : Sample)
      (hω : killedExteriorRecord (diskFinset (Real.exp t)) K C label 0 ω =
        killedExteriorRecord (diskFinset (Real.exp t)) K C label 0 ω') (i : ℕ) (hi : i ≤ j) :
      sourceActualCount t b i ω = sourceActualCount t b i ω' := by
    have hlevels := source_prefix_level_geometry (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b j (by norm_num)
      (by norm_num [sourceRecordBuffer]; exact hm) hj C hC hB i hi
    have hh := hF K C label 0 _ hKC hlevels
      (killedPathWord (diskFinset (Real.exp t)) 0 ω)
      (killedPathWord (diskFinset (Real.exp t)) 0 ω') hω
    simpa only [sourceActualCount, sourceForwardRecordCount, actualTerminalWordRecords,
      Nat.sub_zero] using hh
  let f : Sample → ℕ → ℕ := fun ω i ↦ if i ≤ j then sourceActualCount t b i ω else 0
  have hf : Function.FactorsThrough f
      (killedExteriorRecord (diskFinset (Real.exp t)) K C label 0) := by
    intro ω ω' hω
    funext i
    by_cases hi : i ≤ j
    · simpa only [f, if_pos hi] using hcount ω ω' hω i hi
    · simp only [f, if_neg hi]
  obtain ⟨g, hg⟩ := (Function.factorsThrough_iff f).mp hf
  refine ⟨g, ?_⟩
  intro ω i hi
  have hh := congrFun (congrFun hg ω) i
  simpa only [f, if_pos hi, Function.comp_apply] using hh.symm

end SRWTightness
