import SRWTightness.SourceSiteCgf
import SRWTightness.SourceTerminalThresholdAsymptotic

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Explicit inverse-tilt exponent control on a unit-width terminal window. -/
theorem terminal_inverse_tilt_exponent (Λ V d q A F ε η C : ℝ)
    (hΛ : |Λ - 2 * V| ≤ ε) (hV : |V - d| ≤ C)
    (hA : |A - (2 * d + q)| ≤ η) (hF : A ≤ F) (hF' : F ≤ A + 1) :
    |(Λ - 2 * F) - (-2 * d - 2 * q)| ≤ ε + 2 * C + 2 * η + 2 := by
  obtain ⟨hΛl, hΛu⟩ := abs_le.mp hΛ
  obtain ⟨hVl, hVu⟩ := abs_le.mp hV
  obtain ⟨hAl, hAu⟩ := abs_le.mp hA
  apply abs_le.mpr
  constructor <;> linarith

noncomputable def sourceInverseTiltExponentConstant : ℝ :=
  2 * (sourcePointEnergyTimeError + sourceLowerTimeError) + 5

/-- On the actual source terminal window, the inverse tilt has the claimed exponential order. -/
theorem source_inverse_tilt_factor :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (M : Finset Site),
      let m := sourceLowerRadius t
      let d := sourceLowerTime m
      let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
      let α := sourceReferenceIntensity m 14
      M ⊆ D → α * capacity D M ≤ 1 → ∀ q : ℝ,
      Real.sqrt d ≤ q → q ≤ 2 * Real.sqrt d →
      let u := sourceTerminalRoot t q
      ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) → ∀ (z : M), (z : Site) = b →
      let Λ := cgf (fun Y ↦ 2 * normalizedMarkSum M k α (2 / Real.pi) u z Y)
        (markProductLaw D M α k) 1
      ∀ F : ℝ, sourceTerminalThreshold t u ≤ F → F ≤ sourceTerminalThreshold t u + 1 →
        Real.exp (-sourceInverseTiltExponentConstant) * Real.exp (-2 * d - 2 * q) ≤
          Real.exp (Λ - 2 * F) ∧
        Real.exp (Λ - 2 * F) ≤
          Real.exp sourceInverseTiltExponentConstant * Real.exp (-2 * d - 2 * q) := by
  have hcsmall := (tendsto_order.1 sourceSiteCgfError_tendsto_zero).2 1 (by norm_num)
  have hasmall := (tendsto_order.1 sourceTerminalThresholdError_tendsto_zero).2 1 (by norm_num)
  filter_upwards [source_site_cgf_error, source_deficit_large_conditions, hcsmall, hasmall]
    with t hcgf ht hcsmall hasmall
  dsimp only
  intro b M hMD hcap q hq hq2 k hk z hz F hF hF'
  have hu := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2
  have hc := hcgf b M hMD hcap _ hu.1 k hk z
  have ha := sourceTerminalThreshold_target_error t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).2.2.1
  have hv := sourcePointEnergyTime_lowerTime_bound b (sourceLowerRadius t) 14
    (by linarith) (by norm_num) (by linarith)
  rw [hz] at hc
  change |cgf _ _ 1 - 2 * sourcePointEnergyTime b (sourceLowerRadius t) 14| ≤ _ at hc
  have he := terminal_inverse_tilt_exponent _ _ _ q _ F _ _ _ hc hv ha hF hF'
  have he' : |(cgf (fun Y ↦ 2 * normalizedMarkSum M k
      (sourceReferenceIntensity (sourceLowerRadius t) 14) (2 / Real.pi)
      (sourceTerminalRoot t q) z Y)
      (markProductLaw (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14)))
        M (sourceReferenceIntensity (sourceLowerRadius t) 14) k) 1 - 2 * F) -
      (-2 * sourceLowerTime (sourceLowerRadius t) - 2 * q)| ≤
        sourceInverseTiltExponentConstant := by
    unfold sourceInverseTiltExponentConstant
    linarith
  obtain ⟨hl, hu⟩ := abs_le.mp he'
  constructor
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)

end SRWTightness
