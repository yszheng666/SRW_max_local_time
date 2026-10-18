import SRWTightness.TerminalWindowEvent
import SRWTightness.TerminalInterpolation

namespace SRWTightness

/-- The terminal window written with explicit interpolation endpoints and centering. -/
noncomputable def sourceTerminalWindow {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (A v₀ q aStar d γ : ℝ) (clock : τ → ℝ)
    (left right : τ → Option ι) (weight : τ → ℝ) (mean : ι → ℝ) :
    Set ((ι → ℝ) × C(τ, ℝ)) :=
  terminalWindowEvent site last A (A + 1)
    (2 * v₀ + q - aStar - 1) (2 * v₀ + q - aStar)
    (fun t ↦ interpolationWeights (left t) (right t) (weight t))
    (fun t ↦ q - (d - clock t) ^ γ +
      ∑ i, interpolationWeights (left t) (right t) (weight t) i * mean i)

/-- This event has precisely the two coordinate windows and centered interpolated path inequality. -/
theorem mem_sourceTerminalWindow {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (A v₀ q aStar d γ : ℝ) (clock : τ → ℝ)
    (left right : τ → Option ι) (weight : τ → ℝ) (mean x : ι → ℝ) (path : C(τ, ℝ)) :
    (x, path) ∈ sourceTerminalWindow site last A v₀ q aStar d γ clock left right weight mean ↔
      A ≤ x site ∧ x site ≤ A + 1 ∧
      q - aStar - 1 ≤ x last - 2 * v₀ ∧ x last - 2 * v₀ ≤ q - aStar ∧
      ∀ t, linearObservationInterpolation (left t) (right t) (weight t) (x - mean) +
        path t ≤ q - (d - clock t) ^ γ := by
  change (A ≤ x site ∧ x site ≤ A + 1 ∧
    2 * v₀ + q - aStar - 1 ≤ x last ∧ x last ≤ 2 * v₀ + q - aStar ∧ _) ↔ _
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, by linarith, by linarith, ?_⟩
    intro t
    rw [centered_interpolation_identity]
    have hh := h5 t
    dsimp only at hh
    linarith
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, by linarith, by linarith, ?_⟩
    intro t
    have hh := h5 t
    rw [centered_interpolation_identity] at hh
    dsimp only
    linarith

theorem sourceTerminalWindow_section_convex {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (A v₀ q aStar d γ : ℝ) (clock : τ → ℝ)
    (left right : τ → Option ι) (weight : τ → ℝ) (mean : ι → ℝ) (path : C(τ, ℝ)) :
    Convex ℝ ((fun x ↦ (x, path)) ⁻¹'
      sourceTerminalWindow site last A v₀ q aStar d γ clock left right weight mean) :=
  terminalWindowEvent_section_convex _ _ _ _ _ _ _ _ path

theorem sourceTerminalWindow_isClosed {ι τ : Type*} [Fintype ι] [TopologicalSpace τ]
    (site last : ι) (A v₀ q aStar d γ : ℝ) (clock : τ → ℝ)
    (left right : τ → Option ι) (weight : τ → ℝ) (mean : ι → ℝ) :
    IsClosed (sourceTerminalWindow site last A v₀ q aStar d γ clock left right weight mean) :=
  terminalWindowEvent_isClosed _ _ _ _ _ _ _ _

end SRWTightness
