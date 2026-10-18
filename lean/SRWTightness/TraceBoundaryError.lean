import SRWTightness.ExternalKilledExitDecomposition

open MeasureTheory
namespace SRWTightness

/-- The source boundary subtraction has absolute error at most twice the harmonic oscillation. -/
theorem trace_boundary_subtraction_error (hMarkov : KilledExitDecompositionInput)
    (D K : Finset Site) (hKD : K ⊆ D) (v e : Site) (he : e ∉ D)
    (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hv : |traceExitProbability D v e - s| ≤ δ * s)
    (hK : ∀ y ∈ K, |traceExitProbability D y e - s| ≤ δ * s) :
    |traceExitProbability (D \ K) v e - s * competingExitMass D K v| ≤ 2 * δ * s := by
  let μ := competingEntranceLaw D K v
  let m := μ.real Set.univ
  let I := ∫ y, traceExitProbability D y e ∂μ
  have hm0 : 0 ≤ m := measureReal_nonneg
  have hmass := competing_entrance_exit_mass D K v
  change m + competingExitMass D K v = 1 at hmass
  have hm1 : m ≤ 1 := by
    have hn : 0 ≤ competingExitMass D K v := measureReal_nonneg
    linarith
  have hi : Integrable (fun y ↦ traceExitProbability D y e) μ := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ traceExitProbability D y e from measureReal_nonneg)]
      exact measureReal_le_one)
  have hlo : (s - δ * s) * m ≤ I := by
    have hh := integral_mono_ae (integrable_const (s - δ * s)) hi (by
      filter_upwards [competingEntranceLaw_supported D K v] with y hy
      have hh := (abs_le.mp (hK y hy)).1
      linarith)
    simpa only [integral_const, smul_eq_mul, mul_comm] using hh
  have hhi : I ≤ (s + δ * s) * m := by
    have hh := integral_mono_ae hi (integrable_const (s + δ * s)) (by
      filter_upwards [competingEntranceLaw_supported D K v] with y hy
      have hh := (abs_le.mp (hK y hy)).2
      linarith)
    simpa only [integral_const, smul_eq_mul, mul_comm] using hh
  have hdecomp := hMarkov.1 D K hKD v e he
  change traceExitProbability D v e = traceExitProbability (D \ K) v e + I at hdecomp
  have hδs : 0 ≤ δ * s := mul_nonneg hδ hs
  have hsmall := mul_le_mul_of_nonneg_left hm1 hδs
  apply abs_le.mpr
  constructor <;> nlinarith [(abs_le.mp hv).1, (abs_le.mp hv).2]

end SRWTightness
