import SRWTightness.StepBound
import Mathlib.Tactic.Linarith

namespace SRWTightness

 theorem normSq_add (x y : Site) :
    normSq (x + y) = normSq x + normSq y +
      2 * ((x.1 : ℝ) * y.1 + (x.2 : ℝ) * y.2) := by
  simp only [normSq, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

/-- Euclidean triangle inequality in squared coordinates, with no change of lattice model. -/
theorem normSq_add_bound (x y : Site) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : normSq x ≤ a ^ 2) (hy : normSq y ≤ b ^ 2) :
    normSq (x + y) ≤ (a + b) ^ 2 := by
  let d : ℝ := (x.1 : ℝ) * y.1 + (x.2 : ℝ) * y.2
  have hcs : d ^ 2 ≤ normSq x * normSq y := by
    dsimp [d, normSq]
    nlinarith [sq_nonneg ((x.1 : ℝ) * y.2 - (x.2 : ℝ) * y.1)]
  have hp : normSq x * normSq y ≤ a ^ 2 * b ^ 2 :=
    mul_le_mul hx hy (normSq_nonneg y) (sq_nonneg a)
  have hd : d ≤ a * b := by
    have hab := mul_nonneg ha hb
    nlinarith
  rw [normSq_add]
  change normSq x + normSq y + 2 * d ≤ (a + b) ^ 2
  nlinarith

end SRWTightness
