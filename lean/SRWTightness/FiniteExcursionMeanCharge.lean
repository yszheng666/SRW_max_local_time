import SRWTightness.MaximumPrinciple
import SRWTightness.Capacity

namespace SRWTightness

/-- Finite excursion renewal and ordinary harmonicity determine the exact equilibrium mean. -/
theorem finite_excursion_mean_charge (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (f : Site → ℝ) (hzero : ∀ y, y ∉ D → f y = 0)
    (hstep : ∀ y ∈ D, y ∉ K → f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d))
    (hroot : ∀ y ∈ K, f y = 1 + exitPayoff C f y) (x : Site) :
    f x = ∑ y ∈ K, killedGreen D x y * equilibriumMeasure C K y := by
  classical
  let v := fun y : Site ↦ exitPayoff C f y + setHitProbability C K y
  have hboundary (y : Site) (hy : y ∉ C \ K) : f y = v y := by
    by_cases hyK : y ∈ K
    · have hh := hroot y hyK
      have hq := setHitProbability_one C K y (hKC hyK) hyK
      dsimp [v]
      rw [hq]
      linarith
    · have hyC : y ∉ C := by
        intro hh
        exact hy (Finset.mem_sdiff.mpr ⟨hh, hyK⟩)
      simp [v, exitPayoff_eq_of_not_mem C f y hyC,
        setHitProbability_zero_of_not_mem C K y hyC]
  have hf (y : Site) (hy : y ∈ C \ K) :
      f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) :=
    hstep y (hCD (Finset.mem_sdiff.mp hy).1) (Finset.mem_sdiff.mp hy).2
  have hv (y : Site) (hy : y ∈ C \ K) :
      v y = (1 / 4 : ℝ) * ∑ d : Direction, v (y + step d) := by
    have hyC := (Finset.mem_sdiff.mp hy).1
    have hyK := (Finset.mem_sdiff.mp hy).2
    dsimp [v]
    rw [Finset.sum_add_distrib, mul_add, ← exitPayoff_first_step C f y hyC,
      ← setHitProbability_harmonic C K y hyC hyK]
  have heq (y : Site) : f y = v y := by
    apply le_antisymm
    · exact finite_domain_comparison (C \ K) f v (fun z hz ↦ (hf z hz).le)
        (fun z hz ↦ (hv z hz).ge) (fun z hz ↦ (hboundary z hz).le) y
    · exact finite_domain_comparison (C \ K) v f (fun z hz ↦ (hv z hz).le)
        (fun z hz ↦ (hf z hz).ge) (fun z hz ↦ (hboundary z hz).ge) y
  have hcharge (y : Site) (hy : y ∈ D) :
      f y - (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d) = equilibriumMeasure C K y := by
    by_cases hyK : y ∈ K
    · have hn : (∑ d : Direction, f (y + step d)) =
          ∑ d : Direction, (exitPayoff C f (y + step d) +
            setHitProbability C K (y + step d)) :=
        Finset.sum_congr rfl (fun d _ ↦ heq (y + step d))
      rw [heq y, hn]
      dsimp only [v]
      rw [Finset.sum_add_distrib, mul_add, ← exitPayoff_first_step C f y (hKC hyK),
        setHitProbability_one C K y (hKC hyK) hyK,
        equilibriumMeasure_eq_charge C K hKC y]
      simp only [equilibriumCharge, if_pos hyK]
      ring
    · rw [hstep y hy hyK, sub_self]
      simp [equilibriumMeasure, hyK]
  rw [green_representation D f hzero x]
  calc
    _ = ∑ y ∈ D, killedGreen D x y * equilibriumMeasure C K y :=
      Finset.sum_congr rfl (fun y hy ↦ congrArg (fun q ↦ killedGreen D x y * q) (hcharge y hy))
    _ = _ := (Finset.sum_subset (hKC.trans hCD) (fun y hy hyK ↦ by
      simp [equilibriumMeasure, hyK])).symm

end SRWTightness
