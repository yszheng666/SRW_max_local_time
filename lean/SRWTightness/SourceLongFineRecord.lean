import SRWTightness.SourceProfileSingleRoot
import SRWTightness.SourceRootDepth

namespace SRWTightness

/-- The complete source fine record below one level-nu short root, retaining its actual killed word. -/
noncomputable def sourceLongFineRecord (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (x : Site) (w : PathWord) :
    FiniteExcursionRecord (Mark K) (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) :=
  actualFiniteWordRecord
    (sourceTreeEntrance (sourceLowerRadius t) 1 (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b)
    (sourceTreeExit (sourceLowerRadius t) 1 (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b)
    (wordOccupationMark K) (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) x w

/-- The actual source reference-tree atom for the remaining depth below a short root. -/
noncomputable def sourceLongFineReferenceMass (t : ℝ) (b : Site) (K : Finset Site) (ν : ℕ)
    (r : FiniteExcursionRecord (Mark K) (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) : ℝ :=
  finiteRecordReferenceWeight (fun v : Mark K ↦
    (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
      ((2 / Real.pi) * Real.log ((Real.exp 1 * sourceLowerRadius t + 14) /
        (sourceLowerRadius t - 14)))).real {v})
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) r

/-- The existing source profile error, including its terminal mark comparison contribution. -/
noncomputable def sourceLongFineError (B W t a : ℝ) (K : Finset Site) (ν : ℕ)
    (r : FiniteExcursionRecord (Mark K) (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) : ℝ :=
  finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) j))
    (fun _ : Mark K ↦ 2 * (W * (a + 1) / sourceLowerRadius t * Real.log (sourceLowerRadius t / a)))
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) r

/-- The named long-segment fine record, reference atom and error satisfy the established source single-root bound. -/
theorem source_long_fine_record_comparison (hP : PotentialKernelAsymptoticInput) :
    ∃ B W t₀ : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      t₀ ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 → K ⊆ translateFinset b (diskFinset a) →
      ∀ ν : ℕ, ν < sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ x (r : FiniteExcursionRecord (Mark K)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))),
      sourceRecordRadius (sourceLowerRadius t) (sourceRootDepth (Real.exp t) (sourceLowerRadius t))
          (ν + 1) - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
          (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14 →
      Real.exp (-sourceLongFineError B W t a K ν r) * sourceLongFineReferenceMass t b K ν r ≤
        pathLaw.real {ω | sourceLongFineRecord t b K ν x
          (killedPathWord (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) x ω) = r} ∧
      pathLaw.real {ω | sourceLongFineRecord t b K ν x
          (killedPathWord (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) x ω) = r} ≤
        Real.exp (sourceLongFineError B W t a K ν r) * sourceLongFineReferenceMass t b K ν r := by
  obtain ⟨B, W, t₀, hB, hW, hh⟩ := source_profile_single_root_comparison hP
  refine ⟨B, W, t₀, hB, hW, ?_⟩
  intro b t a K ht ha hcut hK ν hν x r hxlo hxhi
  exact hh b t a K ht ha hcut hK _ ν hν x r hxlo hxhi

end SRWTightness
