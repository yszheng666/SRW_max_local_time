import SRWTightness.DiskMonotone
import SRWTightness.DiskCenterGrowth
import SRWTightness.ExitTail

open MeasureTheory Filter

namespace SRWTightness

theorem diskCenter_compact_bound (R₀ R₁ : ℝ) (h₀ : 1 < R₀) (h₁ : R₀ ≤ R₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R ∈ Set.Icc R₀ R₁, |diskCenter R| ≤ C := by
  let C := (2 * Real.log R₁ + |Real.log (Real.log R₀)|) / Real.sqrt Real.pi
  have h₁p : 1 < R₁ := h₀.trans_le h₁
  have hlpos := Real.log_pos h₁p
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro R hR
  rw [abs_of_pos (diskCenter_pos R (h₀.trans_le hR.1))]
  have hl : Real.log R ≤ Real.log R₁ := Real.log_le_log (by linarith [hR.1]) hR.2
  have hll : Real.log (Real.log R₀) ≤ Real.log (Real.log R) :=
    Real.log_le_log (Real.log_pos h₀) (Real.log_le_log (by linarith) hR.1)
  dsimp [diskCenter, C]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [neg_abs_le (Real.log (Real.log R₀))]

/-- Uniform control over each compact interval of real radii, using the actual exit moment. -/
theorem compact_disk_tightness (R₀ R₁ : ℝ) (h₀ : 1 < R₀) (h₁ : R₀ ≤ R₁)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R ∈ Set.Icc R₀ R₁,
      pathLaw.real {ω | K < |diskFluctuation R ω|} < ε := by
  obtain ⟨C, hC, hc⟩ := diskCenter_compact_bound R₀ R₁ h₀ h₁
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 ((R₁ + 1) ^ 2 / ε))
  have hNp : (0 : ℝ) < N := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hN)
  have hNpos : 0 < N := Nat.cast_pos.mp hNp
  have hNe : (R₁ + 1) ^ 2 / N < ε := by
    apply (div_lt_iff₀ hNp).mpr
    have hh := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hN)
    linarith
  refine ⟨Real.sqrt N + C, by positivity, ?_⟩
  intro R hR
  have hr : 0 ≤ R := by linarith [hR.1]
  have hsub : {ω | Real.sqrt N + C < |diskFluctuation R ω|} ≤ᵐ[pathLaw]
      {ω | N < exitSteps R₁ ω} := by
    filter_upwards [ae_diskMax_mono hr hR.2] with ω hm
    intro ht
    by_contra hh
    have hn : exitSteps R₁ ω ≤ N := le_of_not_gt hh
    have hmax : diskMax R ω ≤ N := hm.trans ((diskMax_le_exitSteps R₁ ω).trans hn)
    have hs : Real.sqrt (diskMax R ω) ≤ Real.sqrt (N : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmax)
    have hb := abs_sub (Real.sqrt (diskMax R ω)) (diskCenter R)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hb
    have hd := hc R hR
    change Real.sqrt N + C < |Real.sqrt (diskMax R ω) - diskCenter R| at ht
    linarith
  have hm : pathLaw.real {ω | Real.sqrt N + C < |diskFluctuation R ω|} ≤
      pathLaw.real {ω | N < exitSteps R₁ ω} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact (hm.trans (prob_exitSteps_gt (by linarith) N hNpos)).trans_lt hNe

theorem diskTightness_of_eventual_tails
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ R : ℝ in atTop, pathLaw.real {ω | K < |diskFluctuation R ω|} < ε) :
    DiskTightnessClaim := by
  intro R₀ h₀ ε hε
  obtain ⟨K, hK, ht⟩ := h ε hε
  obtain ⟨R₁, h₁⟩ := eventually_atTop.mp ht
  obtain ⟨J, hJ, hj⟩ := compact_disk_tightness R₀ (max R₀ R₁) h₀ (le_max_left _ _) ε hε
  refine ⟨max K J, le_max_of_le_left hK, ?_⟩
  intro R hR
  by_cases hr : R₁ ≤ R
  · have hs : {ω | max K J < |diskFluctuation R ω|} ⊆ {ω | K < |diskFluctuation R ω|} :=
      by
        intro ω hh
        exact lt_of_le_of_lt (le_max_left K J) (show max K J < |diskFluctuation R ω| from hh)
    exact (measureReal_mono hs (measure_ne_top _ _)).trans_lt (h₁ R hr)
  · have hs : {ω | max K J < |diskFluctuation R ω|} ⊆ {ω | J < |diskFluctuation R ω|} :=
      by
        intro ω hh
        exact lt_of_le_of_lt (le_max_right K J) (show max K J < |diskFluctuation R ω| from hh)
    exact (measureReal_mono hs (measure_ne_top _ _)).trans_lt
      (hj R ⟨hR, (le_of_not_ge hr).trans (le_max_right _ _)⟩)

end SRWTightness
