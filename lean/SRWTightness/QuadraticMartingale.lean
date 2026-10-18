import SRWTightness.ConditionalStep
import SRWTightness.CoordinateBounds
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace SRWTightness

noncomputable def quadraticProcess (n : ℕ) (ω : Sample) : ℝ :=
  normSq (position ω n) - n

 theorem stronglyAdapted_quadraticProcess : StronglyAdapted history quadraticProcess := by
  intro n
  exact ((measurable_of_countable normSq).comp (adapted_position n)).stronglyMeasurable.sub
    stronglyMeasurable_const

 theorem integrable_quadraticProcess (n : ℕ) : Integrable (quadraticProcess n) pathLaw :=
  (integrable_normSq_position n).sub (integrable_const _)

 theorem condExp_coord_increment (j : Fin 2) (n : ℕ) :
    pathLaw[fun ω : Sample ↦ coord j (step (ω n)) | history n] =ᵐ[pathLaw] 0 := by
  fin_cases j
  · simpa [coord] using condExp_increment_fst n
  · simpa [coord] using condExp_increment_snd n

 theorem condExp_coord_product (j : Fin 2) (n : ℕ) :
    pathLaw[fun ω : Sample ↦ coord j (position ω n) * coord j (step (ω n)) |
      history n] =ᵐ[pathLaw] 0 := by
  have hp := condExp_mul_of_stronglyMeasurable_left
    (history_measurable_coord j n).stronglyMeasurable
    (integrable_coord_product j n) (integrable_coord_increment j n)
  filter_upwards [hp, condExp_coord_increment j n] with ω hω hz
  simpa only [Pi.mul_def, Pi.mul_apply, hz, Pi.zero_apply, mul_zero] using hω

/-- The genuine SRW squared displacement minus elapsed time is a martingale. -/
theorem martingale_quadraticProcess : Martingale quadraticProcess history pathLaw := by
  apply martingale_of_condExp_sub_eq_zero_nat stronglyAdapted_quadraticProcess
    integrable_quadraticProcess
  intro n
  let p : Fin 2 → Sample → ℝ := fun j ω ↦ coord j (position ω n) * coord j (step (ω n))
  have heq : quadraticProcess (n + 1) - quadraticProcess n = (2 : ℝ) • (p 0 + p 1) := by
    funext ω
    simp only [Pi.sub_apply, quadraticProcess, position, normSq_add_step, Nat.cast_add,
      Nat.cast_one, Pi.smul_apply, Pi.add_apply, smul_eq_mul, p, coord]
    norm_num
    <;> ring
  rw [heq]
  have hs := condExp_add (integrable_coord_product 0 n) (integrable_coord_product 1 n)
    (history n)
  have hm := condExp_smul (2 : ℝ) (p 0 + p 1) (history n) (μ := pathLaw)
  filter_upwards [hm, hs, condExp_coord_product 0 n, condExp_coord_product 1 n]
    with ω hmul hadd hzero₀ hzero₁
  change pathLaw[(2 : ℝ) • (p 0 + p 1) | history n] ω = 0
  change pathLaw[p 0 + p 1 | history n] ω =
    pathLaw[p 0 | history n] ω + pathLaw[p 1 | history n] ω at hadd
  change pathLaw[p 0 | history n] ω = 0 at hzero₀
  change pathLaw[p 1 | history n] ω = 0 at hzero₁
  simpa only [Pi.smul_apply, smul_eq_mul, hadd, hzero₀, hzero₁, add_zero, mul_zero] using hmul

end SRWTightness
