import SRWTightness.Filtration
import SRWTightness.QuadraticStep
import SRWTightness.Moments

open MeasureTheory

namespace SRWTightness

/-- The two real coordinate projections of a lattice point. -/
def coord (j : Fin 2) (x : Site) : ℝ := if j = 0 then x.1 else x.2

 theorem abs_coord_le (j : Fin 2) (x : Site) {a : ℝ} (ha : 0 ≤ a)
    (h : normSq x ≤ a ^ 2) : |coord j x| ≤ a := by
  unfold coord
  split_ifs
  · exact abs_fst_le_normSq_bound x ha h
  · exact abs_snd_le_normSq_bound x ha h

 theorem normSq_step (d : Direction) : normSq (step d) = 1 := by
  fin_cases d <;> simp [step, normSq]

 theorem coord_position_bound (j : Fin 2) (n : ℕ) (ω : Sample) :
    |coord j (position ω n)| ≤ n :=
  abs_coord_le j _ (Nat.cast_nonneg _) (normSq_position_le ω n)

 theorem coord_increment_bound (j : Fin 2) (n : ℕ) (ω : Sample) :
    |coord j (step (ω n))| ≤ 1 := by
  apply abs_coord_le j _ zero_le_one
  simp [normSq_step]

 theorem history_measurable_coord (j : Fin 2) (n : ℕ) :
    Measurable[history n] (fun ω ↦ coord j (position ω n)) :=
  (measurable_of_countable (coord j)).comp (adapted_position n)

 theorem measurable_coord_increment (j : Fin 2) (n : ℕ) :
    Measurable (fun ω : Sample ↦ coord j (step (ω n))) :=
  (measurable_of_countable (fun d ↦ coord j (step d))).comp (measurable_pi_apply n)

 theorem integrable_coord_increment (j : Fin 2) (n : ℕ) :
    Integrable (fun ω : Sample ↦ coord j (step (ω n))) pathLaw := by
  refine ⟨(measurable_coord_increment j n).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [] with ω
  exact coord_increment_bound j n ω

 theorem integrable_coord_product (j : Fin 2) (n : ℕ) :
    Integrable (fun ω : Sample ↦ coord j (position ω n) * coord j (step (ω n))) pathLaw := by
  have hm := ((measurable_of_countable (coord j)).comp (measurable_position n)).mul
    (measurable_coord_increment j n)
  refine ⟨hm.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := (n : ℝ)) ?_⟩
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul (coord_position_bound j n ω) (coord_increment_bound j n ω)
    (abs_nonneg _) (Nat.cast_nonneg n)

end SRWTightness
