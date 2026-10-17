import SRWTightness.ActualIntervalBridge
import SRWTightness.TimeGridInterpolation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A bridge on [a,b], extended by zero outside its interval using endpoint clamping. -/
noncomputable def localizedIntervalBridge (a b v : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  actualIntervalBridge (b - a) (max 0 (min (b - a) (v - a))) ω

theorem localizedIntervalBridge_left (a b v : ℝ) (hv : v ≤ a)
    (ω : GaussianCoefficientSpace) : localizedIntervalBridge a b v ω = 0 := by
  have h : min (b - a) (v - a) ≤ 0 := (min_le_right _ _).trans (by linarith)
  simp only [localizedIntervalBridge, max_eq_left h, actualIntervalBridge_zero]

theorem localizedIntervalBridge_right (a b v : ℝ) (hab : a < b) (hv : b ≤ v)
    (ω : GaussianCoefficientSpace) : localizedIntervalBridge a b v ω = 0 := by
  have h : b - a ≤ v - a := by linarith
  rw [localizedIntervalBridge, min_eq_left h, max_eq_right (by linarith)]
  exact actualIntervalBridge_terminal _ (by linarith) ω

theorem localizedIntervalBridge_inside (a b v : ℝ) (hl : a ≤ v) (hu : v ≤ b)
    (ω : GaussianCoefficientSpace) :
    localizedIntervalBridge a b v ω = actualIntervalBridge (b - a) (v - a) ω := by
  rw [localizedIntervalBridge, min_eq_right (by linarith), max_eq_right (by linarith)]

theorem localizedIntervalBridge_continuous (a b : ℝ) :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (fun v ↦ localizedIntervalBridge a b v ω) := by
  filter_upwards [actualIntervalBridge_continuous (b - a)] with ω hω
  exact hω.comp (continuous_const.max (continuous_const.min
    (continuous_id.sub continuous_const)))

theorem localizedIntervalBridge_measurable (a b v : ℝ) :
    Measurable (localizedIntervalBridge a b v) := actualIntervalBridge_measurable _ _

theorem localizedIntervalBridge_mean (a b v : ℝ) (hab : a < b) :
    (∫ ω, localizedIntervalBridge a b v ω ∂gaussianCoefficientLaw) = 0 := by
  apply actualIntervalBridge_mean _ _ (by linarith) (le_max_left _ _)
  exact max_le (by linarith) (min_le_left _ _)

noncomputable def timeGridBridge (T : ℕ → ℝ) (n : ℕ)
    (ω : ℕ → GaussianCoefficientSpace) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, localizedIntervalBridge (T j) (T (j + 1)) v (ω j)

theorem timeGridBridge_node (T : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k ≤ n)
    (ω : ℕ → GaussianCoefficientSpace) : timeGridBridge T n ω (T k) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hj' : j < n := Finset.mem_range.mp hj
  by_cases h : k ≤ j
  · exact localizedIntervalBridge_left _ _ _
      (timeGridTime_mono T n hgap h (Nat.le_of_lt hj')) _
  · exact localizedIntervalBridge_right _ _ _ (hgap j hj')
      (timeGridTime_mono T n hgap (Nat.succ_le_of_lt (Nat.lt_of_not_ge h)) hk) _

theorem timeGridBridge_measurable (T : ℕ → ℝ) (n : ℕ) (v : ℝ) :
    Measurable (fun ω ↦ timeGridBridge T n ω v) := by
  apply Finset.measurable_sum
  intro j hj
  exact (localizedIntervalBridge_measurable _ _ _).comp (measurable_pi_apply j)

theorem timeGridBridge_continuous (T : ℕ → ℝ) (n : ℕ)
    (ω : ℕ → GaussianCoefficientSpace)
    (hω : ∀ j < n, Continuous (fun v ↦ localizedIntervalBridge (T j) (T (j + 1)) v (ω j))) :
    Continuous (timeGridBridge T n ω) := by
  apply continuous_finsetSum
  intro j hj
  exact hω j (Finset.mem_range.mp hj)

theorem timeGridBridge_ae_continuous (T : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, Continuous (timeGridBridge T n ω) := by
  have h (j : ℕ) : ∀ᵐ ω ∂independentBridgeLaw ℕ,
      Continuous (fun v ↦ localizedIntervalBridge (T j) (T (j + 1)) v (ω j)) :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ gaussianCoefficientLaw) j).quasiMeasurePreserving.ae (localizedIntervalBridge_continuous (T j) (T (j + 1)))
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact timeGridBridge_continuous T n ω (fun j _ ↦ hω j)

end SRWTightness
