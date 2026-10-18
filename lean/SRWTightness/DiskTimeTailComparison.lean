import SRWTightness.ScaledDiskComparison
import SRWTightness.CenteringTimeScale

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem scaled_disk_comparison_error_tendsto (A : ℝ) (hA : 0 < A) :
    Tendsto (fun n : ℕ ↦ 2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / (n : ℝ))
      atTop (𝓝 (2 / A ^ 2)) := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hm := hs.const_mul_atTop hA
  have h₁ : Tendsto (fun n : ℕ ↦ 2 / (A * Real.sqrt n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hm
  have h₂ : Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa using (h₁.const_add (2 / A ^ 2)).add h₂

/-- Actual-walk tail comparison; the only discarded paths are in the proved null exit set. -/
theorem time_tail_le_disk_tails (A : ℝ) (hA : 1 < A) (n : ℕ) (hn : 1 ≤ n)
    (K C : ℝ)
    (hlo : |diskCenter (Real.sqrt n / A) - timeCenter n| ≤ C)
    (hhi : |diskCenter (A * Real.sqrt n) - timeCenter n| ≤ C) :
    pathLaw.real {ω | K + C < |timeFluctuation n ω|} ≤
      (2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / n) +
      pathLaw.real {ω | K < |diskFluctuation (Real.sqrt n / A) ω|} +
      pathLaw.real {ω | K < |diskFluctuation (A * Real.sqrt n) ω|} := by
  let E : Set Sample := {ω | ¬ (exitTime (Real.sqrt n / A) ω ≤ n ∧
    (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω)}
  let L : Set Sample := {ω | K < |diskFluctuation (Real.sqrt n / A) ω|}
  let U : Set Sample := {ω | K < |diskFluctuation (A * Real.sqrt n) ω|}
  have hsub : {ω | K + C < |timeFluctuation n ω|} ≤ᵐ[pathLaw] (((E ∪ L) ∪ U) : Set Sample) := by
    filter_upwards [ae_scaled_disk_time_sandwich A hA n] with ω hs
    intro ht
    by_contra hbad
    have he : ω ∉ E := fun he ↦ hbad (Or.inl (Or.inl he))
    have hl : ω ∉ L := fun hl ↦ hbad (Or.inl (Or.inr hl))
    have hu : ω ∉ U := fun hu ↦ hbad (Or.inr hu)
    have hg : exitTime (Real.sqrt n / A) ω ≤ n ∧
        (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω := by simpa [E] using he
    obtain ⟨hsl, hsu⟩ := hs hg
    have hsl' : Real.sqrt (diskMax (Real.sqrt n / A) ω) ≤ Real.sqrt (maxLocalTime ω n) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hsl)
    have hsu' : Real.sqrt (maxLocalTime ω n) ≤ Real.sqrt (diskMax (A * Real.sqrt n) ω) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hsu)
    have hl' : |diskFluctuation (Real.sqrt n / A) ω| ≤ K := le_of_not_gt hl
    have hu' : |diskFluctuation (A * Real.sqrt n) ω| ≤ K := le_of_not_gt hu
    obtain ⟨hll, hlu⟩ := abs_le.mp hl'
    obtain ⟨hul, huu⟩ := abs_le.mp hu'
    obtain ⟨hcl, hcu⟩ := abs_le.mp hlo
    obtain ⟨hdl, hdu⟩ := abs_le.mp hhi
    have hb : |timeFluctuation n ω| ≤ K + C := by
      apply abs_le.mpr
      dsimp [timeFluctuation, diskFluctuation] at *
      constructor <;> linarith
    exact (not_lt_of_ge hb) ht
  have hm : pathLaw.real {ω | K + C < |timeFluctuation n ω|} ≤ pathLaw.real ((E ∪ L) ∪ U) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := pathLaw) (E ∪ L) U
  have hl := measureReal_union_le (μ := pathLaw) E L
  have he := prob_scaled_disk_comparison_failure A hA n hn
  change pathLaw.real E ≤ _ at he
  change _ ≤ _ + pathLaw.real L + pathLaw.real U
  linarith

end SRWTightness
