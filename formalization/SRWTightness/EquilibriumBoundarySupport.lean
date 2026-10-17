import SRWTightness.Capacity
import SRWTightness.LatticeNorm
import SRWTightness.DiskFiniteDomain

namespace SRWTightness

theorem equilibriumMeasure_eq_zero_of_all_neighbors (D K : Finset Site) (hKD : K ⊆ D)
    (x : Site) (hsteps : ∀ d : Direction, x + step d ∈ K) : equilibriumMeasure D K x = 0 := by
  rw [equilibriumMeasure_eq_charge D K hKD]
  unfold equilibriumCharge
  split_ifs with hx
  · have hh (d : Direction) : setHitProbability D K (x + step d) = 1 :=
      setHitProbability_one D K _ (hKD (hsteps d)) (hsteps d)
    simp only [hh, Finset.sum_const, Finset.card_univ, Direction, Fintype.card_fin]
    norm_num
  · rfl

theorem disk_equilibrium_inner_zero (D : Finset Site) (a : ℝ) (ha : 2 ≤ a)
    (hKD : diskFinset a ⊆ D) (x : Site) (hx : normSq x < (a - 1) ^ 2) :
    equilibriumMeasure D (diskFinset a) x = 0 := by
  apply equilibriumMeasure_eq_zero_of_all_neighbors D (diskFinset a) hKD x
  intro d
  rw [mem_diskFinset]
  change normSq (x + step d) < a ^ 2
  have hs := Real.sq_sqrt (normSq_nonneg x)
  have hr := Real.sqrt_nonneg (normSq x)
  have hlt : Real.sqrt (normSq x) < a - 1 := by nlinarith
  have hb := normSq_step_le x d hr hs.ge
  nlinarith

theorem disk_equilibrium_support_lower (D : Finset Site) (a : ℝ) (ha : 2 ≤ a)
    (hKD : diskFinset a ⊆ D) (x : Site) (hx : equilibriumMeasure D (diskFinset a) x ≠ 0) :
    (a - 1) ^ 2 ≤ normSq x := by
  by_contra h
  exact hx (disk_equilibrium_inner_zero D a ha hKD x (lt_of_not_ge h))

end SRWTightness
