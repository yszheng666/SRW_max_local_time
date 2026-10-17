import SRWTightness.DiskTraceRatio

namespace SRWTightness

/-- Enlarging the containing inner ball removes the asymptotic inner-radius cutoff. -/
theorem disk_trace_ratio_all_inner_scales (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C Λ : ℝ, 0 < C ∧ 16 ≤ Λ ∧ ∀ a B : ℝ, 1 ≤ a → Λ * a ≤ B →
      ∀ (b x e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) → x ∈ K →
      e ∉ translateFinset b (diskFinset B) →
      0 < traceExitProbability (translateFinset b (diskFinset B)) x e → ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace (translateFinset b (diskFinset B)) K x ω = ξ} →
      let D := translateFinset b (diskFinset B)
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤
        C * (a / B) * (1 + Real.log (B / a)) := by
  obtain ⟨C, Λ, T, hC, hΛ, hT0, hh⟩ := disk_trace_ratio hP hH hM hT
  refine ⟨C * T, Λ * T, by positivity, by nlinarith, ?_⟩
  intro a B ha hB b x e K hK hx he hep ξ hξ
  let a' := max T a
  have ha0 : 0 < a := by linarith
  have hTa : T ≤ a' := le_max_left _ _
  have haa : a ≤ a' := le_max_right _ _
  have ha'0 : 0 < a' := by linarith
  have ha' : a' ≤ T * a := by
    apply max_le <;> nlinarith [mul_nonneg (show 0 ≤ T - 1 by linarith) ha0.le,
      mul_nonneg (show 0 ≤ a - 1 by linarith) (show 0 ≤ T by linarith)]
  have hΛa : Λ * a' ≤ B := by
    have hm := mul_le_mul_of_nonneg_left ha' (show 0 ≤ Λ by linarith)
    nlinarith
  have hab' : a' < B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hK' : K ⊆ translateFinset b (diskFinset a') := hK.trans
    (Finset.image_subset_image (diskFinset_mono a a' ha0.le haa))
  have hr := hh a' B hTa hΛa b x e K hK' hx he hep ξ hξ
  have hlog0 : 0 ≤ Real.log (B / a') := (Real.log_pos ((one_lt_div ha'0).mpr hab')).le
  have hlogs : Real.log (B / a') ≤ Real.log (B / a) :=
    Real.log_le_log (div_pos hB0 ha'0) (div_le_div_of_nonneg_left hB0.le ha0 haa)
  have hrat := div_le_div_of_nonneg_right ha' hB0.le
  have hp := mul_le_mul hrat (add_le_add (le_refl (1 : ℝ)) hlogs) (by linarith : 0 ≤ 1 + Real.log (B / a'))
    (by positivity : 0 ≤ T * a / B)
  have hu := mul_le_mul_of_nonneg_left hp hC.le
  have hu' : C * (a' / B) * (1 + Real.log (B / a')) ≤
      (C * T) * (a / B) * (1 + Real.log (B / a)) := by
    calc
      _ = C * ((a' / B) * (1 + Real.log (B / a'))) := by ring
      _ ≤ C * ((T * a / B) * (1 + Real.log (B / a))) := hu
      _ = _ := by ring
  exact hr.trans hu'

end SRWTightness
