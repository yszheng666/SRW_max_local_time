import SRWTightness.Targets

open MeasureTheory Filter

namespace SRWTightness

/-- Exact positive-probability seed proposition on the canonical SRW; no proof is assumed globally. -/
def DiskSeedClaim : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∃ Rstar : ℝ, ∀ R : ℝ, Rstar ≤ R →
    p ≤ pathLaw.real {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)}

/-- The manuscript's upper-tail proposition, kept as an explicit unproved input. -/
def DiskUpperTailClaim : Prop :=
  ∃ C s₀ : ℝ, 0 < C ∧ 0 < s₀ ∧ ∀ s : ℝ, s₀ ≤ s →
    limsup (fun R : ℝ ↦ pathLaw.real {ω | s < diskFluctuation R ω}) atTop ≤
      C * (1 + s) * Real.exp (-3 * s / 2)

end SRWTightness
