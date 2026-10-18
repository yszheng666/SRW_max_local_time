import SRWTightness.SRWFourierExpectation
import SRWTightness.FourierBoxOrthogonality

open MeasureTheory ProbabilityTheory

namespace SRWTightness

noncomputable def transitionProbability (n : ℕ) (z : Site) : ℝ :=
  pathLaw.real {ω | position ω n = z}

theorem fourierPhase_neg (z : Site) (θ : ℝ × ℝ) :
    fourierPhase (-z) θ = -fourierPhase z θ := by
  simp only [fourierPhase, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_mul, neg_add]

theorem integrable_joint_cos_position (n : ℕ) (z : Site) :
    Integrable (fun p : Sample × (ℝ × ℝ) ↦ Real.cos (fourierPhase (z + position p.1 n) p.2))
      (pathLaw.prod fourierBoxMeasure) := by
  have hmpos : Measurable (fun p : Sample × (ℝ × ℝ) ↦ position p.1 n) :=
    (measurable_position n).comp measurable_fst
  have hm : Measurable (fun p : Sample × (ℝ × ℝ) ↦
      Real.cos (fourierPhase (z + position p.1 n) p.2)) := by
    unfold fourierPhase
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p ↦ by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one _)

/-- Exact Fourier inversion for the transition probabilities of the original SRW. -/
theorem transitionProbability_fourier (n : ℕ) (z : Site) :
    transitionProbability n z = (4 * Real.pi ^ 2)⁻¹ *
      ∫ θ, fourierCharacteristic θ ^ n * Real.cos (fourierPhase z θ) ∂fourierBoxMeasure := by
  have hp : (∫ ω, ∫ θ, Real.cos (fourierPhase (-z + position ω n) θ) ∂fourierBoxMeasure ∂pathLaw) =
      4 * Real.pi ^ 2 * transitionProbability n z := by
    simp_rw [fourierBox_integral_cos_phase, neg_add_eq_zero]
    have heq (ω : Sample) : (z = position ω n) = (position ω n = z) := propext eq_comm
    simp_rw [heq]
    have hE : MeasurableSet {ω | position ω n = z} :=
      (measurable_position n) (measurableSet_singleton z)
    have hval := integral_indicator_const (E := ℝ) (μ := pathLaw) (4 * Real.pi ^ 2) hE
    rw [smul_eq_mul] at hval
    simpa only [Set.indicator, Set.mem_setOf_eq, transitionProbability] using
      hval.trans (mul_comm _ _)
  have hs := integral_integral_swap
    (f := fun ω θ ↦ Real.cos (fourierPhase (-z + position ω n) θ))
    (integrable_joint_cos_position n (-z))
  rw [hp] at hs
  simp_rw [integral_cos_position, fourierPhase_neg, Real.cos_neg] at hs
  rw [← hs]
  have hn : 4 * Real.pi ^ 2 ≠ 0 := by positivity
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end SRWTightness
