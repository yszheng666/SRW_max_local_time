import SRWTightness.InverseTiltProduct
import SRWTightness.PairWindows

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A pair window transfers from its actual tilted law with the three geometric inverse weights. -/
theorem pair_window_inverse_probability {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {N : ℕ} (last : Fin N) (F : Ω → PairObservationIndex N → ℝ) (hF : Measurable F)
    (At d v q f C ε : ℝ) (n m l : ℕ)
    (hX : Integrable (fun Y ↦ Real.exp (∑ j, pairObservationTilt last j * F Y j)) μ)
    (hΛ : cgf (fun Y ↦ ∑ j, pairObservationTilt last j * F Y j) μ 1 ≤ 4 * d - 2 * v + C)
    (hAt : 2 * d + q - ε ≤ At)
    (E : Set ((PairObservationIndex N → ℝ) × Ξ)) (hE : MeasurableSet E)
    (hwindow : ∀ p ∈ E, p.1 ∈ pairWindow last At (2 * v + q - f) n m l) :
    ((μ.map F).prod ν).real E ≤
      (Real.exp (C + 4 * ε) * Real.exp (-2 * d - 2 * (d - v) - 2 * q - 2 * f) *
        ((Real.exp (-2)) ^ n * (Real.exp (-2)) ^ m * (Real.exp (-2)) ^ l)) *
      (((μ.tilted (fun Y ↦ ∑ j, pairObservationTilt last j * F Y j)).map F).prod ν).real E := by
  let X := fun Y ↦ ∑ j, pairObservationTilt last j * F Y j
  letI := isProbabilityMeasure_tilted hX
  have hmap (ρ : Measure Ω) [SFinite ρ] : ((ρ.map F).prod ν).real E =
      (ρ.prod ν).real ((fun p ↦ (F p.1, p.2)) ⁻¹' E) := by
    have hm := Measure.map_prod_map ρ ν hF measurable_id
    rw [Measure.map_id] at hm
    rw [hm, map_measureReal_apply (hF.prodMap measurable_id) hE]
    rfl
  rw [hmap μ, hmap (μ.tilted X)]
  apply (inverse_tilt_product_event_bounds μ ν X hX _
    (hE.preimage ((hF.comp measurable_fst).prodMk measurable_snd)) 0 _
    (fun _ _ ↦ Real.exp_nonneg _) ?_).2
  intro p hp
  have hstat : X p.1 = 2 * F p.1 (.inr false) + 2 * F p.1 (.inr true) -
      2 * F p.1 (.inl last) := by
    unfold X pairObservationTilt
    rw [pairTiltWeight_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hstat]
  exact pairWindow_inverse_tilt last _ At d v q f C ε n m l (F p.1)
    (hwindow (F p.1, p.2) hp) hΛ hAt

end SRWTightness
