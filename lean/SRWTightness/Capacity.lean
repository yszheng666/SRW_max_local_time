import SRWTightness.EquilibriumProbability

open MeasureTheory

namespace SRWTightness

noncomputable def capacity (D K : Finset Site) : ℝ := ∑ x ∈ K, equilibriumMeasure D K x

 theorem equilibriumMeasure_nonneg (D K : Finset Site) (x : Site) :
    0 ≤ equilibriumMeasure D K x := by
  unfold equilibriumMeasure
  split_ifs
  · exact measureReal_nonneg
  · exact le_rfl

 theorem capacity_nonneg (D K : Finset Site) : 0 ≤ capacity D K :=
  Finset.sum_nonneg (fun x _ ↦ equilibriumMeasure_nonneg D K x)

 theorem capacity_pos (D K : Finset Site) (hKD : K ⊆ D) (hne : K.Nonempty) :
    0 < capacity D K := by
  by_contra h
  have hc : capacity D K ≤ 0 := le_of_not_gt h
  have he (x : Site) (hx : x ∈ K) : equilibriumMeasure D K x = 0 := by
    apply le_antisymm _ (equilibriumMeasure_nonneg D K x)
    exact (Finset.single_le_sum (fun y _ ↦ equilibriumMeasure_nonneg D K y) hx).trans hc
  obtain ⟨z, hz⟩ := hne
  have hg := green_equilibrium_on_set D K hKD z hz
  have hzsum : (∑ x ∈ K, killedGreen D z x * equilibriumMeasure D K x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [he x hx, mul_zero]
  linarith

noncomputable def equilibriumWeight (D K : Finset Site) (x : Site) : ℝ :=
  equilibriumMeasure D K x / capacity D K

 theorem equilibriumWeight_nonneg (D K : Finset Site) (x : Site) :
    0 ≤ equilibriumWeight D K x :=
  div_nonneg (equilibriumMeasure_nonneg D K x) (capacity_nonneg D K)

 theorem equilibriumWeight_sum (D K : Finset Site) (hKD : K ⊆ D) (hne : K.Nonempty) :
    ∑ x ∈ K, equilibriumWeight D K x = 1 := by
  simp only [equilibriumWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (capacity_pos D K hKD hne))

 theorem equilibriumWeight_le_one (D K : Finset Site) (hKD : K ⊆ D)
    (hne : K.Nonempty) (x : Site) : equilibriumWeight D K x ≤ 1 := by
  by_cases hx : x ∈ K
  · have h := Finset.single_le_sum (fun y _ ↦ equilibriumWeight_nonneg D K y) hx
    rwa [equilibriumWeight_sum D K hKD hne] at h
  · simp [equilibriumWeight, equilibriumMeasure, hx]

 theorem equilibriumWeight_sq_sum_le_one (D K : Finset Site) (hKD : K ⊆ D)
    (hne : K.Nonempty) : ∑ x ∈ K, equilibriumWeight D K x ^ 2 ≤ 1 := by
  calc
    _ ≤ ∑ x ∈ K, equilibriumWeight D K x := by
      apply Finset.sum_le_sum
      intro x hx
      have hn := equilibriumWeight_nonneg D K x
      have hu := equilibriumWeight_le_one D K hKD hne x
      nlinarith
    _ = 1 := equilibriumWeight_sum D K hKD hne

 theorem equilibriumWeight_green (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) :
    ∑ x ∈ K, equilibriumWeight D K x * killedGreen D x z = 1 / capacity D K := by
  simp only [equilibriumWeight, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [equilibrium_green_on_set D K hKD z hz]

end SRWTightness
