import SRWTightness.BoundaryRelativeComparison

namespace SRWTightness

/-- The annulus escape lower bound converts the source boundary error into a relative interior one. -/
theorem trace_relative_boundary_propagation (Ω : Finset Site) (U Q : Site → ℝ)
    (hU : ∀ y ∈ Ω, U y = (1 / 4 : ℝ) * ∑ d : Direction, U (y + step d))
    (hQ : ∀ y ∈ Ω, Q y = (1 / 4 : ℝ) * ∑ d : Direction, Q (y + step d))
    (s η q₀ : ℝ) (hs : 0 ≤ s) (hη : 0 ≤ η) (hq₀ : 0 < q₀)
    (hb : ∀ y ∈ domainExitBoundary Ω,
      (U y = 0 ∧ Q y = 0) ∨ (q₀ ≤ Q y ∧ |U y - s * Q y| ≤ η * s))
    (x : Site) (hx : x ∈ Ω) :
    |U x - s * Q x| ≤ (η * s / q₀) * Q x := by
  apply harmonic_relative_error_on_boundary Ω U Q hU hQ s (η * s / q₀) _ x hx
  intro y hy
  rcases hb y hy with hz | ho
  · simp [hz.1, hz.2]
  · have hh := mul_le_mul_of_nonneg_left ho.1
      (show 0 ≤ η * s / q₀ by positivity)
    have he : (η * s / q₀) * q₀ = η * s := by field_simp
    rw [he] at hh
    exact ho.2.trans hh

end SRWTightness
