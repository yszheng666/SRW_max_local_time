import SRWTightness.SourceRootDepth
import SRWTightness.SourceLowerRadius
import SRWTightness.SourceExcursionDomains
import SRWTightness.SourceReferenceIntensity
import SRWTightness.TwoSiteDiscreteRow

namespace SRWTightness

/-- The physical inner radius at an arbitrary common coarse level. -/
noncomputable def sourceCommonPairInnerRadius (t : ℝ) (j : ℕ) : ℝ :=
  sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (j + 1)

/-- The manuscript's common killing disk, with its fixed buffer of fourteen. -/
noncomputable def sourceCommonPairDomain (t : ℝ) (b : Site) (j : ℕ) : Finset Site :=
  sourceExitDomain (sourceLowerRadius t) 1
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b j

/-- The same reference-intensity formula evaluated at the common coarse inner radius. -/
noncomputable def sourceCommonPairIntensity (t : ℝ) (j : ℕ) : ℝ :=
  sourceReferenceIntensity (sourceCommonPairInnerRadius t j) 14

/-- The actual normalized maximum row sum, without replacing G-I by G. -/
noncomputable def sourceCommonPairRowScale (t : ℝ) (b w : Site) (j : ℕ) : ℝ :=
  twoSiteDiscreteRowMax (sourceCommonPairDomain t b j) b w / (2 / Real.pi)

theorem sourceCommonPairInnerRadius_pos (t : ℝ) (j : ℕ) :
    0 < sourceCommonPairInnerRadius t j := by
  unfold sourceCommonPairInnerRadius sourceRecordRadius
  exact mul_pos (sourceLowerRadius_pos t) (Real.exp_pos _)

/-- The common source domain is exactly the buffered disk used by the reference intensity. -/
theorem sourceCommonPairDomain_eq (t : ℝ) (b : Site) (j : ℕ) :
    sourceCommonPairDomain t b j =
      translateFinset b (diskFinset (Real.exp 1 * sourceCommonPairInnerRadius t j + 14)) := by
  unfold sourceCommonPairDomain sourceExitDomain sourceCommonPairInnerRadius sourceRecordBuffer
  rw [sourceRecordRadius_successor]
  norm_num

/-- The common intensity has the numerator and denominator of the original coarse geometry. -/
theorem sourceCommonPairIntensity_eq (t : ℝ) (j : ℕ) :
    sourceCommonPairIntensity t j = (2 / Real.pi) * Real.log
      ((sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) j + 14) /
          (sourceCommonPairInnerRadius t j - 14)) := by
  unfold sourceCommonPairIntensity sourceReferenceIntensity
  rw [show Real.exp 1 * sourceCommonPairInnerRadius t j =
    sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) j from sourceRecordRadius_successor _ _ _]

theorem sourceCommonPairIntensity_bounds (t : ℝ) (j : ℕ)
    (hm : 70 ≤ sourceCommonPairInnerRadius t j) :
    0 < sourceCommonPairIntensity t j ∧ sourceCommonPairIntensity t j ≤ 2 * (2 / Real.pi) := by
  exact sourceReferenceIntensity_bounds _ 14 (sourceCommonPairInnerRadius_pos t j)
    (by norm_num) (by linarith)

end SRWTightness
