import SRWTightness.OrderedWordRelativeComparison
import SRWTightness.FirstEntranceRootLaw

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Entrance-atom relative control gives domination of the complete actual ordered-mark measure. -/
theorem firstEntranceWordMarkLaw_le_reference (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ y ∈ K, |(competingEntranceLaw D K x).real {y} - α * equilibriumMeasure D K y| ≤
      ε * (α * equilibriumMeasure D K y)) :
    firstEntranceWordMarkLaw D K x ≤ ENNReal.ofReal (1 + ε) • referenceWordMarkLaw D K α := by
  letI : IsProbabilityMeasure (referenceWordMarkLaw D K α) :=
    referenceWordMarkLaw_probability D K α hα (by linarith)
  apply Measure.le_iff.mpr
  intro s hs
  have hh := firstEntranceWordMark_event_relative_comparison D K x α ε hα hε hcap hu s hs
  have hreal : (firstEntranceWordMarkLaw D K x).real s ≤
      (1 + ε) * (referenceWordMarkLaw D K α).real s := by
    linarith [(abs_le.mp hh).2]
  have hnonneg : 0 ≤ 1 + ε := by linarith
  simpa only [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul hnonneg,
    ofReal_measureReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hreal

/-- The comparison controls all nonnegative ordered-word tests without a moment premise. -/
theorem firstEntranceWordMark_lintegral_le_reference (D K : Finset Site) (x : Site)
    (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ y ∈ K, |(competingEntranceLaw D K x).real {y} - α * equilibriumMeasure D K y| ≤
      ε * (α * equilibriumMeasure D K y)) (f : WordMark → ℝ≥0∞) :
    (∫⁻ Y, f Y ∂firstEntranceWordMarkLaw D K x) ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ Y, f Y ∂referenceWordMarkLaw D K α := by
  have hh := lintegral_mono'
    (firstEntranceWordMarkLaw_le_reference D K x α ε hα hε hcap hu) (le_refl f)
  simpa only [lintegral_smul_measure, smul_eq_mul] using hh

/-- Original joint root moments are bounded by the common ordered reference mark. -/
theorem original_pair_root_lintegral_le_reference (D K L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ K) (hL₂ : L₂ ⊆ K) (x : Site) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 ≤ ε) (hcap : α * capacity D K ≤ 1 / 2)
    (hu : ∀ y ∈ K, |(competingEntranceLaw D K x).real {y} - α * equilibriumMeasure D K y| ≤
      ε * (α * equilibriumMeasure D K y)) (F : ℕ × ℕ → ℝ≥0∞) :
    (∫⁻ ω, F (wordMarkRootCount L₁ C₁ (killedWordMark D x ω),
      wordMarkRootCount L₂ C₂ (killedWordMark D x ω)) ∂pathLaw) ≤
      ENNReal.ofReal (1 + ε) * ∫⁻ Y,
        F (wordMarkRootCount L₁ C₁ Y, wordMarkRootCount L₂ C₂ Y) ∂referenceWordMarkLaw D K α := by
  rw [firstEntranceWordMark_pair_root_lintegral D K L₁ C₁ L₂ C₂ hL₁ hL₂ x F]
  exact firstEntranceWordMark_lintegral_le_reference D K x α ε hα hε hcap hu _

end SRWTightness
