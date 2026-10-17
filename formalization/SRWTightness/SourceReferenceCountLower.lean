import SRWTightness.SourceExteriorOriginalCounts
import SRWTightness.SourceCountProductCap
import SRWTightness.ReferenceCountMixtureLower

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The common finite reference mixture for the two original counts. -/
noncomputable def sourceReferenceJointCountWeight (t : ℝ) (ν J : ℕ)
    (h : ExteriorPathRecord) (k l : ℕ) : ℝ :=
  referenceJointCountWeight (sourceLongEscapeParameter (sourceLowerRadius t) 1
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
    (fun i ↦ (h.1.get i).2.1) k l

/-- The reference count mixture is dominated by the original conditional joint count law, with
one uniform count error and with no replacement of the original counts by independent counts. -/
theorem source_reference_count_lower (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k l : ℕ, k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      sourceReferenceJointCountWeight t ν J h k l ≤
        Real.exp (16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) + C * 15 /
            (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14))) *
        (pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h ∧
          sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} /
          pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) := by
  classical
  obtain ⟨A, C, J₀, hA, hC, hJ₀, ht⟩ := source_exterior_count_product hExt hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [ht, source_exterior_original_counts hExt hFlat,
    source_count_product_error_cap] with t hprod hcounts hcap
  intro b w ν J hb hw hbw hd hν hform hJ h hh k l hk hl
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w) 0 (fun _ u ↦ u)
  let Z := sourcePairExteriorRecord t b w ν J
  let H := {ω | Z ω = h}
  let μ := ProbabilityTheory.cond pathLaw H
  let f := fun ω ↦ (h.1.zip (U ω)).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2)
  let label := fun i : Fin h.1.length ↦ (h.1.get i).2.1
  let p := sourceLongEscapeParameter m 1 ℓ ν J
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14)
  let F := 16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε)
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  have hZ : Measurable Z := measurable_killedExteriorRecord _ _ _ _ _
  have hHm : MeasurableSet H := hZ (measurableSet_singleton h)
  have hμ : pathLaw H ≠ 0 := by
    intro hz
    exact hh.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)
  letI : IsProbabilityMeasure μ := ProbabilityTheory.cond_isProbabilityMeasure hμ
  have hU : Measurable U := measurable_killedChildRecords _ _ _ _ _
  have hf (r : Fin h.1.length → ℕ) : MeasurableSet {ω | f ω = List.ofFn r} :=
    hU ((Set.to_countable {us | (h.1.zip us).map
      (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) = List.ofFn r}).measurableSet)
  have hc : ∀ᵐ ω ∂μ, ∀ r : Fin h.1.length → ℕ, f ω = List.ofFn r →
      sourceActualCount t b ν ω = labeledRootTotal label r false ∧
      sourceActualCount t w ν ω = labeledRootTotal label r true := by
    have hcc := (ProbabilityTheory.cond_absolutelyContinuous (μ := pathLaw) (s := H)).ae_le
      (hcounts b w ν J hb hw hbw hd hν hform h hh)
    filter_upwards [hcc, ProbabilityTheory.ae_cond_mem (μ := pathLaw) hHm] with ω hcω hω
    exact hcω hω
  have hp (r : Fin h.1.length → ℕ) (hr : ∀ i, 0 < r i)
      (hrk : labeledRootTotal label r false = k) (hrl : labeledRootTotal label r true = l) :
      (∏ i, p * (1-p) ^ (r i - 1)) ≤ Real.exp F * μ.real {ω | f ω = List.ofFn r} := by
    have hri (i) : r i - 1 + 1 = r i := Nat.sub_add_cancel (hr i)
    have hrr (i) : ((r i - 1 : ℕ) : ℝ) + 1 = (r i : ℝ) := by exact_mod_cast hri i
    have he := (hprod b w ν J hb hw hbw hd hν hform hJ h hh (fun i ↦ r i - 1)).1
    simp only [hri, hrr] at he
    have hE : (∑ i, (δ + ε * (r i : ℝ))) ≤ F :=
      hcap ν hν J A C hA.le hC.le label r k l hr hrk hrl hk hl
    have hm : μ.real {ω | f ω = List.ofFn r} =
        pathLaw.real {ω | f ω = List.ofFn r ∧ Z ω = h} / pathLaw.real H :=
      conditional_real_apply pathLaw H _ hHm
    rw [← hm] at he
    change Real.exp (-(∑ i, (δ + ε * (r i : ℝ)))) *
      (∏ i, p * (1-p) ^ (r i - 1)) ≤ μ.real {ω | f ω = List.ofFn r} at he
    have hsmall : (∏ i, p * (1-p) ^ (r i - 1)) ≤
        Real.exp (∑ i, (δ + ε * (r i : ℝ))) * μ.real {ω | f ω = List.ofFn r} := by
      have he' := mul_le_mul_of_nonneg_left he (Real.exp_pos (∑ i, (δ + ε * (r i : ℝ)))).le
      simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, add_neg_cancel,
        Real.exp_zero, one_mul] using he'
    exact hsmall.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hE) (measureReal_nonneg))
  have hsum := reference_count_mixture_lower μ label f (sourceActualCount t b ν)
    (sourceActualCount t w ν) p F k l hf hc hp
  rw [conditional_real_apply pathLaw H _ hHm] at hsum
  have hevent : {ω | sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} ∩ H =
      {ω | Z ω = h ∧ sourceActualCount t b ν ω = k ∧ sourceActualCount t w ν ω = l} := by
    ext ω
    exact and_comm
  rw [hevent] at hsum
  exact hsum

end SRWTightness
