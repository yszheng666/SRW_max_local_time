import SRWTightness.PairResidualProductLaw
import SRWTightness.PairWindows

open MeasureTheory

namespace SRWTightness

/-- Residual window locations after conditioning on the retained Gaussian endpoint. -/
noncomputable def pairResidualWindowLocation {n : ℕ} (last : Fin n)
    (mean : PairObservationIndex n → ℝ) (At : ℝ) (nn mm : ℕ)
    (p : (Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) (j : Fin 2) : ℝ :=
  if j = 0 then At + nn - mean (.inr false) - p.1 last
  else At + mm - mean (.inr true) - p.1 last

theorem pairResidualWindowLocation_measurable {n : ℕ} (last : Fin n)
    (mean : PairObservationIndex n → ℝ) (At : ℝ) (nn mm : ℕ) :
    Measurable (pairResidualWindowLocation last mean At nn mm) := by
  apply measurable_pi_iff.mpr
  intro j
  unfold pairResidualWindowLocation
  split_ifs <;> fun_prop

/-- The two original site windows become exactly translated unit residual windows. -/
theorem pairWindow_residual_unit_windows {n : ℕ} (last : Fin n)
    (mean : PairObservationIndex n → ℝ) (At top : ℝ) (nn mm l : ℕ)
    (x : Fin n → ℝ) (r : Fin 2 → ℝ) (ω : ℕ → GaussianCoefficientSpace)
    (hp : mean + pairResidualCoordinates last (x, r) ∈ pairWindow last At top nn mm l) :
    ∀ j, pairResidualWindowLocation last mean At nn mm (x, ω) j ≤ r j ∧
      r j < pairResidualWindowLocation last mean At nn mm (x, ω) j + 1 := by
  have h0 : At + nn ≤ mean (.inr false) + (x last + r 0) ∧
      mean (.inr false) + (x last + r 0) < At + nn + 1 := hp.1
  have h1 : At + mm ≤ mean (.inr true) + (x last + r 1) ∧
      mean (.inr true) + (x last + r 1) < At + mm + 1 := hp.2.1
  intro j
  fin_cases j
  · change At + nn - mean (.inr false) - x last ≤ r 0 ∧
      r 0 < At + nn - mean (.inr false) - x last + 1
    constructor <;> linarith [h0.1, h0.2]
  · change At + mm - mean (.inr true) - x last ≤ r 1 ∧
      r 1 < At + mm - mean (.inr true) - x last + 1
    constructor <;> linarith [h1.1, h1.2]

end SRWTightness
