import SRWTightness.DiskTraceAllInnerScales
import SRWTightness.SingletonTraceExit
import SRWTightness.LatticeNorm

namespace SRWTightness

/-- Source trace-disk relative ratio for every positive inner radius and sufficiently separated disks. -/
theorem disk_trace_ratio_positive_radii (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C Λ : ℝ, 0 < C ∧ 16 ≤ Λ ∧ ∀ a B : ℝ, 0 < a → Λ * a ≤ B →
      ∀ (b x e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) → x ∈ K →
      e ∉ translateFinset b (diskFinset B) →
      0 < traceExitProbability (translateFinset b (diskFinset B)) x e → ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace (translateFinset b (diskFinset B)) K x ω = ξ} →
      let D := translateFinset b (diskFinset B)
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤
        C * (a / B) * (1 + Real.log (B / a)) := by
  classical
  obtain ⟨C, Λ, hC, hΛ, hh⟩ := disk_trace_ratio_all_inner_scales hP hH hM hT
  refine ⟨C, Λ, hC, hΛ, ?_⟩
  intro a B ha hB b x e K hK hx he hep ξ hξ
  by_cases ha1 : 1 ≤ a
  · exact hh a B ha1 hB b x e K hK hx he hep ξ hξ
  · have haSmall : a < 1 := lt_of_not_ge ha1
    have hunique (y : Site) (hy : y ∈ K) : y = b := by
      by_contra hne
      have hnorm := one_le_normSq_of_ne_zero (y - b) (sub_ne_zero.mpr hne)
      have hsmall : normSq (y - b) < a ^ 2 := by
        simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hK hy
      nlinarith
    have hxb := hunique x hx
    subst x
    have hsingle : K = {b} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · exact hunique y
      · intro hy
        simpa only [hy] using hx
    have hB0 : 0 < B := by nlinarith
    have hab : a < B := by nlinarith
    have hbD : b ∈ translateFinset b (diskFinset B) := by
      have hz : normSq (b - b) = 0 := by norm_num [normSq]
      have hr : normSq (b - b) < B ^ 2 := by rw [hz]; positivity
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hr
    rw [hsingle] at hξ ⊢
    dsimp only
    rw [singleton_trace_conditional_ratio hM hT _ b e hbD he hep ξ hξ]
    simp only [sub_self, abs_zero]
    have hlog : 0 ≤ Real.log (B / a) := (Real.log_pos ((one_lt_div ha).mpr hab)).le
    positivity

end SRWTightness
