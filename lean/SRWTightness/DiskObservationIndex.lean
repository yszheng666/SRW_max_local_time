import SRWTightness.GeometricDiskFamily
import SRWTightness.GeometricDiskPointTimes
import SRWTightness.GeometricDiskErrorSum
import SRWTightness.EquilibriumObservationMatrix
import SRWTightness.GreenTranslation
import Mathlib.Logic.Equiv.Fin.Basic

namespace SRWTightness

/-- The source order: outermost average first, innermost average next to last, center last. -/
def diskObservationIndex (n : ℕ) : Fin (n + 1) ≃ Option (Fin n) :=
  (finSuccEquiv' (Fin.last n)).trans (Equiv.optionCongr Fin.revPerm)

@[simp] theorem diskObservationIndex_last (n : ℕ) :
    diskObservationIndex n (Fin.last n) = none := by
  simp [diskObservationIndex]

@[simp] theorem diskObservationIndex_castSucc {n : ℕ} (i : Fin n) :
    diskObservationIndex n i.castSucc = some i.rev := by
  simp [diskObservationIndex, finSuccEquiv'_below (Fin.castSucc_lt_last i)]

theorem equilibriumEnergyTime_translate (b : Site) (D K : Finset Site) (α g : ℝ) :
    equilibriumEnergyTime (translateFinset b D) (translateFinset b K) α g =
      equilibriumEnergyTime D K α g := by
  simp only [equilibriumEnergyTime, capacity_translate]

/-- Exact agreement between the actual source observation times and the ordered Brownian times. -/
theorem diskObservationIndex_energy (b : Site) (R A q α : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    observationEnergyTime (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n)
      b α (2 / Real.pi) (diskObservationIndex n i) =
      geometricDiskPointTime R A q α n (i.val + 1) := by
  refine Fin.lastCases ?_ ?_ i
  · simp only [diskObservationIndex_last, observationEnergyTime, Fin.val_last,
      geometricDiskPointTime, Nat.not_succ_le_self, ↓reduceIte]
    unfold pointEnergyTime
    have hh := killedGreen_translate b (diskFinset R) 0 0
    simp only [add_zero] at hh
    rw [hh]
  · intro j
    have hle : j.val + 1 ≤ n := by omega
    have he : n - (j.val + 1) = j.rev.val := by rw [Fin.val_rev]
    simp only [diskObservationIndex_castSucc, observationEnergyTime, geometricDiskFamily,
      equilibriumEnergyTime_translate, Fin.val_castSucc, geometricDiskPointTime,
      hle, ↓reduceIte, geometricDiskEnergyTime, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, he]

theorem diskObservationIndex_error (b : Site) (R A q g : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    observationDiscreteError (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n)
      g (diskObservationIndex n i) = geometricDiskPointError b A R q g n i := by
  refine Fin.lastCases ?_ ?_ i
  · simp [geometricDiskPointError, observationDiscreteError]
  · intro j
    have he : n - 1 - j.val = j.rev.val := by rw [Fin.val_rev]; omega
    simp only [diskObservationIndex_castSucc, observationDiscreteError, geometricDiskFamily,
      geometricDiskPointError, Fin.val_castSucc, j.isLt, ↓reduceIte, he]

end SRWTightness
