import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Covariance of two observation sums over the same independent sample. -/
theorem covariance_iid_sum {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H J : Ω → ℝ)
    (hmH : Measurable H) (hmJ : Measurable J) (hH : MemLp H 2 μ) (hJ : MemLp J 2 μ)
    (k : ℕ) :
    covariance (fun Y : Fin k → Ω ↦ ∑ i, H (Y i))
      (fun Y : Fin k → Ω ↦ ∑ i, J (Y i)) (Measure.pi (fun _ : Fin k ↦ μ)) =
      k * covariance H J μ := by
  let ν := Measure.pi (fun _ : Fin k ↦ μ)
  have hiH (i : Fin k) : MemLp (fun Y : Fin k → Ω ↦ H (Y i)) 2 ν :=
    hH.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ μ) i)
  have hiJ (i : Fin k) : MemLp (fun Y : Fin k → Ω ↦ J (Y i)) 2 ν :=
    hJ.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ μ) i)
  have hind : iIndepFun (fun i (Y : Fin k → Ω) ↦ Y i) ν :=
    iIndepFun_pi (X := fun _ Y ↦ Y) (fun _ ↦ measurable_id.aemeasurable)
  have hc (i j : Fin k) :
      covariance (fun Y : Fin k → Ω ↦ H (Y i)) (fun Y ↦ J (Y j)) ν =
        if i = j then covariance H J μ else 0 := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have he := covariance_map_fun (μ := ν) (Z := fun Y : Fin k → Ω ↦ Y i)
        hmH.aestronglyMeasurable hmJ.aestronglyMeasurable
        (measurable_pi_apply i).aemeasurable
      rw [(measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq] at he
      exact he.symm
    · rw [if_neg hij]
      exact ((hind.indepFun hij).comp hmH hmJ).covariance_eq_zero (hiH i) (hiJ j)
  rw [covariance_fun_sum_fun_sum hiH hiJ]
  simp_rw [hc]
  simp

end SRWTightness
