import SRWTightness.Capacity
import SRWTightness.EquilibriumSweep

open MeasureTheory

namespace SRWTightness

theorem setHitProbability_le_one (D K : Finset Site) (x : Site) : setHitProbability D K x ≤ 1 := by
  rw [setHitProbability_eq_probability]
  exact (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)

theorem capacity_mono_set (D K L : Finset Site) (hKL : K ⊆ L) (hLD : L ⊆ D) :
    capacity D K ≤ capacity D L := by
  have hs := equilibrium_sweep D K L hKL hLD (setHitProbability D K)
    (setHitProbability_zero_of_not_mem D K) (setHitProbability_harmonic D K)
  have hr : (∑ x ∈ K, equilibriumMeasure D K x * setHitProbability D K x) = capacity D K := by
    unfold capacity
    apply Finset.sum_congr rfl
    intro x hx
    rw [setHitProbability_one D K x (hLD (hKL hx)) hx, mul_one]
  rw [hr] at hs
  rw [← hs]
  unfold capacity
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_of_le_one_right (equilibriumMeasure_nonneg D L x) (setHitProbability_le_one D K x)

theorem capacity_inverse_mono_set (D K L : Finset Site) (hKL : K ⊆ L) (hLD : L ⊆ D)
    (hne : K.Nonempty) : 1 / capacity D L ≤ 1 / capacity D K :=
  one_div_le_one_div_of_le (capacity_pos D K (hKL.trans hLD) hne) (capacity_mono_set D K L hKL hLD)

end SRWTightness
