import SRWTightness.MonomialDomination
import SRWTightness.ObservationGreen
import Mathlib.Topology.Instances.Matrix

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

 theorem exists_generating_radius (D A : Finset Site) (hAD : A ⊆ D) :
    ∃ b : ℝ, 1 < b ∧ ∀ z : A, (1 - 1 / killedGreen D z z) * b ^ Fintype.card A < 1 := by
  have he : ∀ᶠ b : ℝ in 𝓝 1,
      ∀ z : A, (1 - 1 / killedGreen D z z) * b ^ Fintype.card A < 1 := by
    apply Filter.eventually_all.mpr
    intro z
    have hg : 0 < killedGreen D z z := lt_of_lt_of_le zero_lt_one
      (killedGreen_diag_ge_one D z (hAD z.property))
    have hc : Continuous (fun b : ℝ ↦ (1 - 1 / killedGreen D z z) * b ^ Fintype.card A) := by
      fun_prop
    apply hc.continuousAt.eventually_lt continuousAt_const
    simp only [one_pow, mul_one]
    linarith [one_div_pos.mpr hg]
  obtain ⟨ε, hε, hs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1 + ε / 2, by linarith, hs ?_⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have hh : 0 ≤ ε / 2 := by positivity
  simpa [abs_of_nonneg hh] using (show ε / 2 < ε by linarith)

 theorem observationResolventMatrix_one (D A : Finset Site) :
    observationResolventMatrix D A (1 : A → ℝ) = 1 := by
  simp [observationResolventMatrix]

 theorem eventually_observationResolvent_isUnit (D A : Finset Site) :
    ∀ᶠ v : A → ℝ in 𝓝 1, IsUnit (observationResolventMatrix D A v) := by
  have hc : Continuous (fun v : A → ℝ ↦ (observationResolventMatrix D A v).det) := by
    apply Continuous.matrix_det
    unfold observationResolventMatrix
    fun_prop
  have hn : (observationResolventMatrix D A (1 : A → ℝ)).det ≠ 0 := by
    rw [observationResolventMatrix_one, Matrix.det_one]
    exact one_ne_zero
  filter_upwards [hc.continuousAt.eventually_ne hn] with v hv
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)

 theorem eventually_integrable_killedMonomial (D A : Finset Site) (hAD : A ⊆ D) :
    ∀ᶠ v : A → ℝ in 𝓝 1,
      ∀ x : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A x ω)) pathLaw := by
  obtain ⟨b, hb, hqb⟩ := exists_generating_radius D A hAD
  have hlo : ∀ᶠ v : A → ℝ in 𝓝 1, ∀ z : A, 0 < v z := by
    apply Filter.eventually_all.mpr
    intro z
    exact continuousAt_const.eventually_lt (continuous_apply z).continuousAt (by norm_num)
  have hup : ∀ᶠ v : A → ℝ in 𝓝 1, ∀ z : A, v z < b := by
    apply Filter.eventually_all.mpr
    intro z
    exact (continuous_apply z).continuousAt.eventually_lt continuousAt_const hb
  filter_upwards [hlo, hup] with v hv0 hvb
  exact integrable_killedMonomial D A v b (fun z ↦ (hv0 z).le) (fun z ↦ (hvb z).le)
    (by linarith) hqb

end SRWTightness
