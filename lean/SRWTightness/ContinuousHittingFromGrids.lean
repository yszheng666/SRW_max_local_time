import SRWTightness.UniformGridApproximation
import SRWTightness.EventualEventUniformMass

open MeasureTheory Filter
namespace SRWTightness

/-- Bounds on every finite uniform grid control continuous-path hitting at any smaller level. -/
theorem continuous_hitting_from_grids {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℝ → Ω → ℝ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω))
    (a d b c M : ℝ) (had : a ≤ d) (hbc : b < c) (hM : 0 ≤ M)
    (hgrid : ∀ n : ℕ, μ.real
      {ω | ∃ j ≤ 2 ^ n, X (stoppedUniformTimeGrid a d (2 ^ n) j) ω ≤ c} ≤ M) :
    μ.real {ω | ∃ t ∈ Set.Icc a d, X t ω ≤ b} ≤ M := by
  let E : ℕ → Set Ω := fun n ↦
    {ω | ∃ j ≤ 2 ^ n, X (stoppedUniformTimeGrid a d (2 ^ n) j) ω ≤ c}
  have hsub : {ω | ∃ t ∈ Set.Icc a d, X t ω ≤ b} ≤ᵐ[μ]
      {ω | ∀ᶠ n in atTop, ω ∈ E n} := by
    filter_upwards [hcont] with ω hω
    rintro ⟨t, ht, hh⟩
    rcases eq_or_lt_of_le had with he | hlt
    · have hta : t = a := by rw [← he] at ht; exact le_antisymm ht.2 ht.1
      filter_upwards [] with n
      refine ⟨0, Nat.zero_le _, ?_⟩
      rw [stoppedUniformTimeGrid_zero]
      simpa only [hta] using hh.trans hbc.le
    · have hu1 : (t - a) / (d - a) ≤ 1 :=
        (div_le_one (sub_pos.mpr hlt)).mpr (by linarith [ht.2])
      have hlim := (hω.tendsto t).comp (stoppedUniformTimeGrid_dyadic_tendsto a d t hlt ht)
      have hev := hlim.eventually (gt_mem_nhds (hh.trans_lt hbc))
      filter_upwards [hev] with n hn
      exact ⟨dyadicTimeIndex n ((t - a) / (d - a)), dyadicTimeIndex_le n _ hu1, hn.le⟩
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  exact hm.trans (eventual_event_uniform_mass Ω μ E M hM hgrid)

end SRWTightness
