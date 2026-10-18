import SRWTightness.SourceUpperTerminalWindows

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- An explicit unit-window weight retaining the terminal Gaussian deficit decay. -/
noncomputable def sourceUpperTerminalWindowWeight (t s C κ v : ℝ) : ℝ :=
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let q := sourceUpperTarget t s - v
  C * r ^ 2 * Real.exp (-2 * d) / d * (1 + max q 0 / Real.sqrt d) *
    Real.exp (-2 * q + 2 - κ * (max (q - 1) 0) ^ 2 / d)

/-- Every height in a unit window obeys its explicit terminal weight. -/
theorem source_upper_terminal_window_weight_bound (t s C κ u v : ℝ)
    (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (hd : 0 < upperTerminalDepth (sourceUpperLogRadius t)) (hu : u ∈ Set.Ico v (v + 1)) :
    sourceUpperTerminalMain t s C κ u ≤ sourceUpperTerminalWindowWeight t s C κ v := by
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let q := sourceUpperTarget t s - v
  let qu := sourceUpperTarget t s - u
  have hq : qu ≤ q := by dsimp [q, qu]; linarith [hu.1]
  have hqm : q - 1 ≤ qu := by dsimp [q, qu]; linarith [hu.2]
  have hp := max_le_max hq (le_refl (0 : ℝ))
  have hm := max_le_max hqm (le_refl (0 : ℝ))
  have hm0 : 0 ≤ max (q - 1) 0 := le_max_right _ _
  have hsquare : (max (q - 1) 0) ^ 2 ≤ (max qu 0) ^ 2 := by nlinarith
  have hdecay : κ * (max (q - 1) 0) ^ 2 / d ≤ κ * (max qu 0) ^ 2 / d :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare hκ) hd.le
  have hexp : -2 * qu - κ * (max qu 0) ^ 2 / d ≤
      -2 * q + 2 - κ * (max (q - 1) 0) ^ 2 / d := by linarith
  have hlinear : 1 + max qu 0 / Real.sqrt d ≤ 1 + max q 0 / Real.sqrt d :=
    add_le_add le_rfl (div_le_div_of_nonneg_right hp (Real.sqrt_nonneg d))
  have hfactor := mul_le_mul hlinear (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _)
    (by positivity : 0 ≤ 1 + max q 0 / Real.sqrt d)
  have hbase : 0 ≤ C * upperTerminalFineRadius (sourceUpperLogRadius t) ^ 2 *
      Real.exp (-2 * d) / d := by positivity
  simpa only [sourceUpperTerminalMain, sourceUpperTerminalWindowWeight, d, q, qu, mul_assoc]
    using mul_le_mul_of_nonneg_left hfactor hbase

/-- The actual terminal integral is bounded by fully specified finite window weights. -/
theorem source_upper_terminal_weighted_windows (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ (J : ℕ) (C κ : ℝ), 0 ≤ C → 0 ≤ κ →
      (∫⁻ g in sourceUpperGWBand t s (sourceUpperBlockRoot t b) (sourceUpperBlockForestDepth t b),
        sourceUpperTerminalIntegrand t s C κ (sourceUpperBlockForestDepth t b) g
        ∂geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)) ≤
      ∑ i ∈ Finset.range (⌊2 * t + 1⌋₊ + 1),
        ENNReal.ofReal (sourceUpperTerminalWindowWeight t s C κ (t - 1 + i)) *
          geometricGWRecordLaw J (sourceUpperBlockForestDepth t b)
            {g | g ∈ sourceUpperGWBand t s (sourceUpperBlockRoot t b)
                (sourceUpperBlockForestDepth t b) ∧
              geometricGWHeight g (sourceUpperBlockForestDepth t b) ∈
                Set.Ico (t - 1 + i) (t - 1 + i + 1)} := by
  obtain ⟨B, _, hc⟩ := source_upper_threshold_conditions hScale
  filter_upwards [source_upper_terminal_window_integral hScale, hc] with t ht htcond
  intro b hb s hs hslog J C κ hC hκ
  have hd : 0 < upperTerminalDepth (sourceUpperLogRadius t) := by
    linarith [htcond.2.2.2.2.2.2.1]
  apply ht b hb s hs hslog J C κ
  intro i hi u hu
  exact ENNReal.ofReal_le_ofReal
    (source_upper_terminal_window_weight_bound t s C κ u (t - 1 + i) hC hκ hd hu)

end SRWTightness
