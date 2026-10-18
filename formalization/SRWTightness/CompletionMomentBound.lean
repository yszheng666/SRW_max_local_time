import SRWTightness.FiniteRootCompletionInput

open scoped ENNReal
open MeasureTheory
namespace SRWTightness

/-- Nonnegative completion sums remain valid even before finiteness is known. -/
theorem completion_site_enorm_sum_le (xs : List Site) (f : Site → ℝ≥0∞) (B : ℝ≥0∞)
    (hf : ∀ x ∈ xs, f x ≤ B) : (xs.map f).sum ≤ (xs.length : ℝ≥0∞) * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy ↦ hf y (by simp [hy]))
    simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul, add_comm] using add_le_add hx ht

/-- Completion support and a uniform restart bound control a nonnegative moment sum. -/
theorem completion_moment_sum_bound (μ : Measure WordMark) (L₁ C₁ L₂ C₂ : Finset Site)
    (S : Set Site) (f : Site → ℝ≥0∞) (B : ℝ≥0∞)
    (hs : ∀ᵐ Y ∂μ, ∀ z ∈ wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y, z ∈ S)
    (hf : ∀ z ∈ S, f z ≤ B) :
    (∫⁻ Y, ((wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y).map f).sum ∂μ) ≤
      rootBinomialMoment μ L₁ C₁ L₂ C₂ 1 * B := by
  rw [rootBinomialMoment_one, ← lintegral_mul_const B (measurable_of_countable _)]
  apply lintegral_mono_ae
  filter_upwards [hs] with Y hY
  simpa only [wordMarkPairCompletionSites_length] using
    completion_site_enorm_sum_le (wordMarkPairCompletionSites L₁ C₁ L₂ C₂ Y) f B
      (fun z hz ↦ hf z (hY z hz))

/-- Strong Markov completion recursion implies all orders, without assumed integrability. -/
theorem killed_root_factorial_bound (hrec : FiniteRootCompletionInput)
    (D L₁ C₁ L₂ C₂ : Finset Site) (hL₁ : L₁ ⊆ C₁) (hL₂ : L₂ ⊆ C₂)
    (hC₁ : C₁ ⊆ D) (hC₂ : C₂ ⊆ D) (hdis : Disjoint C₁ C₂)
    (hexit : ∀ z ∈ rootCompletionSet C₁ C₂, z ∈ D ∧ z ∉ C₁ ∧ z ∉ C₂)
    (R : ℝ≥0∞)
    (hmean : ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 ≤ R) :
    ∀ p : ℕ, ∀ x ∈ rootCompletionSet C₁ C₂,
      killedRootBinomialMoment D L₁ C₁ L₂ C₂ x p ≤ R ^ p := by
  intro p
  induction p with
  | zero => intro x hx; simp [killedRootBinomialMoment_zero]
  | succ p ih =>
    intro x hx
    obtain ⟨hs, heq⟩ := hrec D L₁ C₁ L₂ C₂ hL₁ hL₂ hC₁ hC₂ hdis hexit x
    rw [heq p]
    calc
      _ ≤ killedRootBinomialMoment D L₁ C₁ L₂ C₂ x 1 * R ^ p :=
        completion_moment_sum_bound _ _ _ _ _ _ _ _ hs ih
      _ ≤ R * R ^ p := mul_le_mul_right' (hmean x hx) _
      _ = R ^ (p + 1) := by rw [pow_succ]; exact mul_comm _ _

end SRWTightness
