import SRWTightness.SourceSharedRadiusEstimates
import SRWTightness.SourceCenteredSuccessCount

open MeasureTheory Filter
namespace SRWTightness

/-- The shared one-point estimate bounds the actual canonical successful-site count, at a
single observation level valid for all candidate sites. -/
theorem source_centered_first_moment_shared (J A γ : ℝ)
    (hTerminal : SourceTerminalEstimate J A γ) (hOne : SourceOnePointEstimate J A γ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∃ I₀ : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I₀) ∧
      c ≤ (∫ p, sourceCenteredSuccessCount t A γ I₀ p ∂sourceEnlargedLaw) ∧
        (∫ p, sourceCenteredSuccessCount t A γ I₀ p ∂sourceEnlargedLaw) ≤ C := by
  obtain ⟨a, B, hA, hmargin, ha, hB, hterminal⟩ := hTerminal
  obtain ⟨c, C, c₁, C₁, hA', hmargin', hc, hC, hc₁, hC₁, hone⟩ := hOne
  refine ⟨c₁, C₁, hc₁, hC₁, ?_⟩
  filter_upwards [hterminal, Real.tendsto_exp_atTop.eventually hone] with t ht hone
  obtain ⟨I₀, hI₀, z₀, hz₀, hb₀⟩ := ht 0
  obtain ⟨I, z, hz, hI, hprob, hlo, hhi⟩ := hone
  have hI' : ∀ (b : sourceCandidateAnnulus (Real.exp t)) (i : ℕ),
      A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I b := by
    simpa only [Real.log_exp] using hI
  have he := source_success_count_eq_centered t A γ I₀ I z hI₀ hI' hz
  refine ⟨I₀, hI₀, ?_, ?_⟩
  · simpa only [he] using hlo
  · simpa only [he] using hhi

end SRWTightness
