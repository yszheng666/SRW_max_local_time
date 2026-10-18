import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A nonnegative discrete supermartingale has the finite maximal bound from its initial mean. -/
theorem nonnegative_supermartingale_maximal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (f : ℕ → Ω → ℝ) (hf : Supermartingale f ℱ μ)
    (hnonneg : ∀ n ω, 0 ≤ f n ω) (ε : ℝ) (n : ℕ) :
    ε * μ.real {ω | ∃ j ≤ n, ε ≤ f j ω} ≤ ∫ ω, f 0 ω ∂μ := by
  let τ : Ω → ℕ∞ := fun ω ↦ (hittingBtwn f (Set.Ici ε) 0 n ω : ℕ)
  let Y : Ω → ℝ := stoppedValue f τ
  have ht : IsStoppingTime ℱ τ :=
    hf.stronglyAdapted.adapted.isStoppingTime_hittingBtwn measurableSet_Ici
  have hb (ω : Ω) : τ ω ≤ n := by
    dsimp [τ]
    exact_mod_cast (hittingBtwn_le (u := f) (s := Set.Ici ε) (n := 0) (m := n) ω)
  have hi : Integrable Y μ := integrable_stoppedValue ℕ ht hf.integrable hb
  have hY (ω : Ω) : 0 ≤ Y ω := by
    change 0 ≤ f (hittingBtwn f (Set.Ici ε) 0 n ω) ω
    exact hnonneg _ _
  have hE : MeasurableSet {ω | ∃ j ≤ n, ε ≤ f j ω} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j ≤ n
    · simpa only [hj, true_and] using
        measurableSet_le measurable_const ((hf.stronglyMeasurable j).measurable.le (ℱ.le j))
    · simp [hj]
  have hbound (ω : Ω) (hω : ∃ j ≤ n, ε ≤ f j ω) : ε ≤ Y ω := by
    obtain ⟨j, hj, hh⟩ := hω
    exact stoppedValue_hittingBtwn_mem ⟨j, ⟨Nat.zero_le _, hj⟩, hh⟩
  have hlow := setIntegral_ge_of_const_le_real hE (measure_ne_top μ _) hbound hi.integrableOn
  have hmid := setIntegral_le_integral (s := {ω | ∃ j ≤ n, ε ≤ f j ω}) hi
    (Filter.Eventually.of_forall hY)
  have hstop := hf.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) ht
    (show (fun _ : Ω ↦ (0 : ℕ∞)) ≤ τ from fun _ ↦ bot_le) hb
  change (∫ ω, -(f 0 ω) ∂μ) ≤ ∫ ω, -(Y ω) ∂μ at hstop
  simp only [integral_neg] at hstop
  exact hlow.trans (hmid.trans (neg_le_neg_iff.mp hstop))

end SRWTightness
