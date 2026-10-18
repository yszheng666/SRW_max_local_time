import SRWTightness.NormalizedWeightedCovariance
import SRWTightness.EquilibriumWeightBilinear

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def normalizedEquilibriumAverage (D A K : Finset Site) (k : ℕ) (α g u : ℝ) :
    MarkSamples A k → ℝ :=
  normalizedWeightedSum A k α g u (fun z ↦ equilibriumWeight D K z)

theorem equilibriumWeight_bilinear_subtype (D A K L : Finset Site) :
    (∑ y : A, ∑ z : A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z) =
      ∑ y ∈ A, ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z := by
  calc
    _ = ∑ y : A, ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z := by
      apply Finset.sum_congr rfl
      intro y _
      exact Finset.sum_coe_sort A (fun z ↦ equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z)
    _ = _ := Finset.sum_coe_sort A (fun y ↦ ∑ z ∈ A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z)

theorem normalizedEquilibriumAverage_covariance_nested (D A K L : Finset Site)
    (hKL : K ⊆ L) (hLA : L ⊆ A) (hAD : A ⊆ D) (hne : K.Nonempty)
    (hdis : ∀ x : Site, equilibriumWeight D K x * equilibriumWeight D L x = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedEquilibriumAverage D A K k α g u)
      (normalizedEquilibriumAverage D A L k α g u) (markProductLaw D A α k) =
        1 / (g * capacity D L) - α / (2 * g) := by
  have hKA := hKL.trans hLA
  have hw : (∑ x : A, equilibriumWeight D K x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over D A K hKA (hKA.trans hAD) hne
  have hv : (∑ x : A, equilibriumWeight D L x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over D A L hLA (hLA.trans hAD) (hne.mono hKL)
  have hbil : (∑ y : A, ∑ z : A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D L z) =
      1 / capacity D L := by
    rw [equilibriumWeight_bilinear_subtype]
    exact equilibriumWeight_bilinear_nested D A K L hKL hLA hAD hne
  unfold normalizedEquilibriumAverage
  rw [normalizedWeighted_covariance D A hAD α g u hα hg hu hcap k hk,
    weighted_covariance_algebra _ α g _ _ hw hv, hbil]
  simp only [hdis, Finset.sum_const_zero, zero_div, sub_zero]
  ring

theorem normalizedEquilibriumAverage_covariance_min (D A K L : Finset Site)
    (hKL : K ⊆ L) (hLA : L ⊆ A) (hAD : A ⊆ D) (hne : K.Nonempty)
    (hdis : ∀ x : Site, equilibriumWeight D K x * equilibriumWeight D L x = 0)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedEquilibriumAverage D A K k α g u)
      (normalizedEquilibriumAverage D A L k α g u) (markProductLaw D A α k) =
        min (1 / (g * capacity D K) - α / (2 * g))
          (1 / (g * capacity D L) - α / (2 * g)) := by
  rw [normalizedEquilibriumAverage_covariance_nested D A K L hKL hLA hAD hne hdis α g u hα hg hu hcap k hk]
  symm
  apply min_eq_right
  have hm := div_le_div_of_nonneg_right (capacity_inverse_mono_set D K L hKL (hLA.trans hAD) hne) hg.le
  have he (C : ℝ) : (1 / C) / g = 1 / (g * C) := by ring
  simp only [he] at hm
  linarith

theorem normalizedEquilibriumAverage_covariance_self (D A K : Finset Site)
    (hKA : K ⊆ A) (hAD : A ⊆ D) (hne : K.Nonempty)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    covariance (normalizedEquilibriumAverage D A K k α g u)
      (normalizedEquilibriumAverage D A K k α g u) (markProductLaw D A α k) =
        1 / (g * capacity D K) - α / (2 * g) -
          (∑ x ∈ K, equilibriumWeight D K x ^ 2) / (2 * g) := by
  have hw : (∑ x : A, equilibriumWeight D K x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over D A K hKA (hKA.trans hAD) hne
  have hbil : (∑ y : A, ∑ z : A, equilibriumWeight D K y * killedGreen D y z * equilibriumWeight D K z) =
      1 / capacity D K := by
    rw [equilibriumWeight_bilinear_subtype]
    exact equilibriumWeight_bilinear_self D A K hKA hAD hne
  have hs : (∑ x : A, equilibriumWeight D K x * equilibriumWeight D K x) =
      ∑ x ∈ K, equilibriumWeight D K x ^ 2 := by
    rw [Finset.sum_coe_sort A (fun x ↦ equilibriumWeight D K x * equilibriumWeight D K x)]
    simp only [← pow_two]
    symm
    exact Finset.sum_subset hKA (fun x _ hx ↦ by rw [equilibriumWeight_zero_of_not_mem D K x hx]; norm_num)
  unfold normalizedEquilibriumAverage
  rw [normalizedWeighted_covariance D A hAD α g u hα hg hu hcap k hk,
    weighted_covariance_algebra _ α g _ _ hw hw, hbil, hs]
  ring

end SRWTightness
