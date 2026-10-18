import SRWTightness.Path
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

instance : MeasurableSpace Direction := ⊤
instance : MeasurableSingletonClass Direction := ⟨fun _ ↦ trivial⟩

/-- Each of the four directions has mass one quarter. -/
noncomputable def directionLaw : Measure Direction :=
  (PMF.uniformOfFintype Direction).toMeasure

instance : IsProbabilityMeasure directionLaw := by
  unfold directionLaw
  infer_instance

/-- Canonical infinite sequence of independent uniform directions. -/
noncomputable def pathLaw : Measure Sample :=
  Measure.infinitePi (fun _ : ℕ ↦ directionLaw)

instance : IsProbabilityMeasure pathLaw := by
  unfold pathLaw
  infer_instance

 theorem directions_independent :
    iIndepFun (fun n (ω : Sample) ↦ ω n) pathLaw := by
  exact iIndepFun_infinitePi (X := fun _ x ↦ x) (fun _ ↦ measurable_id)

 theorem direction_marginal (n : ℕ) :
    pathLaw.map (fun ω ↦ ω n) = directionLaw := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ ↦ directionLaw) n

 theorem direction_mass (d : Direction) : directionLaw {d} = (4 : ℝ≥0∞)⁻¹ := by
  simp [directionLaw, PMF.toMeasure_uniformOfFintype_apply {d} (measurableSet_singleton d)]

 theorem measurable_position (n : ℕ) : Measurable (fun ω ↦ position ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun ω ↦ position ω n + step (ω n))
    exact (measurable_of_countable (fun p : Site × Direction ↦ p.1 + step p.2)).comp
      (ih.prodMk (measurable_pi_apply n))

 theorem measurable_localTime (n : ℕ) (x : Site) :
    Measurable (fun ω ↦ localTime ω n x) := by
  induction n with
  | zero => simpa using (measurable_const : Measurable (fun _ : Sample ↦ (0 : ℕ)))
  | succ n ih =>
    simp_rw [localTime_succ]
    exact ih.add ((measurable_of_countable
      (fun y : Site ↦ if y = x then (1 : ℕ) else 0)).comp (measurable_position n))

/-- Extend a finite direction word by eastward steps; only the prefix will be observed. -/
def extendWord {n : ℕ} (w : Fin n → Direction) : Sample :=
  fun k ↦ if h : k < n then w ⟨k, h⟩ else 0

 theorem maxLocalTime_prefix (ω : Sample) (n : ℕ) :
    maxLocalTime ω n = maxLocalTime (extendWord (fun k : Fin n ↦ ω k)) n := by
  apply maxLocalTime_congr
  intro k hk
  simp [extendWord, hk]

 theorem measurable_maxLocalTime (n : ℕ) : Measurable (fun ω ↦ maxLocalTime ω n) := by
  have h : Measurable (fun ω : Sample ↦ fun k : Fin n ↦ ω k) :=
    measurable_pi_lambda _ (fun k ↦ measurable_pi_apply (k : ℕ))
  have hm := (measurable_of_countable
    (fun w : Fin n → Direction ↦ maxLocalTime (extendWord w) n)).comp h
  convert hm using 1
  funext ω
  exact maxLocalTime_prefix ω n

end SRWTightness
