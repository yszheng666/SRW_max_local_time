import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Nat.Choose.Sum

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem integrable_independent_add_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hXY : IndepFun X Y μ) (m : ℕ)
    (hX : ∀ i ≤ m, Integrable (fun ω ↦ X ω ^ i) μ)
    (hY : ∀ i ≤ m, Integrable (fun ω ↦ Y ω ^ i) μ) :
    Integrable (fun ω ↦ (X ω + Y ω) ^ m) μ := by
  simp_rw [add_pow]
  apply integrable_finsetSum
  intro i hi
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hd : IndepFun (fun ω ↦ X ω ^ i) (fun ω ↦ Y ω ^ (m - i)) μ :=
    hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const (m - i))
  exact (hd.integrable_mul (hX i hi') (hY (m - i) (Nat.sub_le _ _))).mul_const _

 theorem integral_independent_add_power {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hXY : IndepFun X Y μ) (m : ℕ)
    (hX : ∀ i ≤ m, Integrable (fun ω ↦ X ω ^ i) μ)
    (hY : ∀ i ≤ m, Integrable (fun ω ↦ Y ω ^ i) μ) :
    (∫ ω, (X ω + Y ω) ^ m ∂μ) =
      ∑ i ∈ Finset.range (m + 1), (∫ ω, X ω ^ i ∂μ) *
        (∫ ω, Y ω ^ (m - i) ∂μ) * (m.choose i : ℝ) := by
  have hI (i : ℕ) (hi : i ∈ Finset.range (m + 1)) :
      Integrable (fun ω ↦ X ω ^ i * Y ω ^ (m - i) * (m.choose i : ℝ)) μ := by
    have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hd : IndepFun (fun ω ↦ X ω ^ i) (fun ω ↦ Y ω ^ (m - i)) μ :=
      hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const (m - i))
    exact (hd.integrable_mul (hX i hi') (hY (m - i) (Nat.sub_le _ _))).mul_const _
  simp_rw [add_pow]
  rw [integral_finsetSum _ hI]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_mul_const]
  congr 1
  have hi' : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  exact IndepFun.integral_fun_mul_eq_mul_integral
    (hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const (m - i)))
    (hX i hi').aestronglyMeasurable
      (hY (m - i) (Nat.sub_le _ _)).aestronglyMeasurable

end SRWTightness
