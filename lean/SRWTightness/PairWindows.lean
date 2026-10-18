import SRWTightness.PairObservationWeights
import SRWTightness.PairInverseTiltWindow
import Mathlib.Analysis.Convex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory

namespace SRWTightness

/-- The deficit window includes the top boundary only for the first window. -/
def pairDeficitWindow (top : ℝ) (l : ℕ) : Set ℝ :=
  if l = 0 then Set.Icc (top - 1) top else Set.Ico (top - l - 1) (top - l)

/-- The two site excess windows and the final retained average deficit window. -/
def pairWindow {N : ℕ} (last : Fin N) (At top : ℝ) (n m l : ℕ) :
    Set (PairObservationIndex N → ℝ) :=
  {x | x (.inr false) ∈ Set.Ico (At + n) (At + n + 1) ∧
    x (.inr true) ∈ Set.Ico (At + m) (At + m + 1) ∧
    x (.inl last) ∈ pairDeficitWindow top l}

theorem pairDeficitWindow_convex (top : ℝ) (l : ℕ) : Convex ℝ (pairDeficitWindow top l) := by
  unfold pairDeficitWindow
  split
  · exact convex_Icc _ _
  · exact convex_Ico _ _

theorem pairDeficitWindow_measurable (top : ℝ) (l : ℕ) :
    MeasurableSet (pairDeficitWindow top l) := by
  unfold pairDeficitWindow
  split
  · exact measurableSet_Icc
  · exact measurableSet_Ico

theorem pairWindow_convex {N : ℕ} (last : Fin N) (At top : ℝ) (n m l : ℕ) :
    Convex ℝ (pairWindow last At top n m l) := by
  exact ((convex_Ico (At + n) (At + n + 1)).linear_preimage
    (LinearMap.proj (Sum.inr false : PairObservationIndex N) :
        (PairObservationIndex N → ℝ) →ₗ[ℝ] ℝ)).inter
    (((convex_Ico (At + m) (At + m + 1)).linear_preimage
      (LinearMap.proj (Sum.inr true : PairObservationIndex N) :
        (PairObservationIndex N → ℝ) →ₗ[ℝ] ℝ)).inter
      ((pairDeficitWindow_convex top l).linear_preimage (LinearMap.proj (Sum.inl last : PairObservationIndex N) :
        (PairObservationIndex N → ℝ) →ₗ[ℝ] ℝ)))

theorem pairWindow_measurable {N : ℕ} (last : Fin N) (At top : ℝ) (n m l : ℕ) :
    MeasurableSet (pairWindow last At top n m l) := by
  exact (measurableSet_Ico.preimage (measurable_pi_apply (Sum.inr false : PairObservationIndex N))).inter
    ((measurableSet_Ico.preimage (measurable_pi_apply (Sum.inr true : PairObservationIndex N))).inter
      ((pairDeficitWindow_measurable top l).preimage (measurable_pi_apply (Sum.inl last : PairObservationIndex N))))

theorem pairDeficitWindow_upper (top : ℝ) (l : ℕ) (s : ℝ)
    (hs : s ∈ pairDeficitWindow top l) : s ≤ top - l := by
  unfold pairDeficitWindow at hs
  split at hs
  · rename_i hl
    subst l
    simpa using hs.2
  · exact hs.2.le

/-- Each exact window supplies the inverse-tilt bound, including its top boundary. -/
theorem pairWindow_inverse_tilt {N : ℕ} (last : Fin N)
    (Λ At d v q f C ε : ℝ) (n m l : ℕ) (x : PairObservationIndex N → ℝ)
    (hx : x ∈ pairWindow last At (2 * v + q - f) n m l)
    (hΛ : Λ ≤ 4 * d - 2 * v + C) (hAt : 2 * d + q - ε ≤ At) :
    Real.exp (Λ - (2 * x (.inr false) + 2 * x (.inr true) - 2 * x (.inl last))) ≤
      Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f) *
        ((Real.exp (-2)) ^ n * (Real.exp (-2)) ^ m * (Real.exp (-2)) ^ l) := by
  exact pair_inverse_tilt_window_nat Λ _ _ _ At d v q f C ε n m l hΛ hAt
    hx.1.1 hx.2.1.1 (pairDeficitWindow_upper _ _ _ hx.2.2)

end SRWTightness
