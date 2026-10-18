import SRWTightness.SourcePairEventChernoff
import SRWTightness.SourcePairTiltIntegrable
import SRWTightness.SourcePairNodeCumulant

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- The source pair Chernoff bound without a Gaussian window prefactor or a late-node restriction. -/
theorem source_pair_reference_chernoff :
    ∀ᶠ t : ℝ in atTop, ∀ (A : ℝ) (b : Site),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      ∀ (i : ℕ), i ≤ I →
      ∀ (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (z : Site) = b → 1 ≤ Real.sqrt (normSq ((y : Site) - b)) →
      4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i →
      A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)) →
      ∀ (u : ℝ), t ≤ u → ∀ (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      ∀ (At q f ε : ℝ), 2 * sourceLowerTime (sourceLowerRadius t) + q - ε ≤ At →
      let m := sourceLowerRadius t
      let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
      let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
      let α := sourceReferenceIntensity m 14
      let F := fun Y j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
        (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
      let C := 1 + 4 * sourcePairVarianceError +
        4 * (2 * (diskGreenEnergyConstant / (2 / Real.pi)) + Real.log 2 +
          Real.log (4 * diskEnergyGapRatio)) + 1 / (2 / Real.pi)
      (((markProductLaw D M α k).map F).prod (independentBridgeLaw ℕ)).real
        (sourcePairUpperEvent t A I i At q f) ≤
        Real.exp (C + 4 * ε) * Real.exp (-2 * sourceLowerTime m -
          2 * (sourceLowerTime m - sourceObservationTime t A I (I - i + 1)) - 2 * q - 2 * f) := by
  filter_upwards [source_pair_node_cumulant, source_pair_tilt_integrable 1 (by norm_num)]
    with t hcgf hint
  intro A b hA ht I hI i hi z y hz hρ hlo hhi u hu k hk At q f ε hAt
  dsimp only
  let m := sourceLowerRadius t
  let D := translateFinset b (diskFinset (Real.exp 1 * m + 14))
  let M := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))
  let K := translateFinset b (diskFinset (A * diskEnergyGapRatio ^ i))
  let α := sourceReferenceIntensity m 14
  let μ := markProductLaw D M α k
  let F := fun Y j ↦ normalizedWeightedSum M k α (2 / Real.pi) u
    (pairObservationWeight D M (sourcePairAverageFamily b A I i) z y j) Y
  let X := fun Y ↦ 2 * F Y (.inr false) + 2 * F Y (.inr true) -
    2 * F Y (.inl (Fin.last (I - i)))
  have hgeom := source_pair_observation_geometry b t A hA ht I hI i hi
  have hs := sourceScaleThreshold_conditions t A
    (diskGaussianMinimumRadius_ge_four.trans (diskPointGaussianMinimumRadius_ge_base.trans hA))
    ((le_max_left _ _).trans ht)
  have hα := (sourceReferenceIntensity_bounds m 14
    (sourceLowerRadius_pos t) (by norm_num) (by linarith [hs.2.2.1])).1
  letI : IsProbabilityMeasure μ :=
    markProductLaw_isProbabilityMeasure D M α hα.le hgeom.2.2.2.2 k
  have hne : K.Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset _ (by linarith [hgeom.1])
  have hw1 : (∑ x : M, equilibriumWeight D K x) = 1 := by
    simpa only [Finset.sum_coe_sort] using equilibriumWeight_sum_over D M K
      hgeom.2.2.2.1 (hgeom.2.2.2.1.trans hgeom.2.2.1) hne
  have hiX := hint b M hgeom.2.2.1 hgeom.2.2.2.2 u (by simpa using hu) k hk z y
    (fun x ↦ equilibriumWeight D K x) (fun x ↦ equilibriumWeight_nonneg _ _ _) hw1
  have hstat : X = (2 : ℝ) • (normalizedMarkSum M k α (2 / Real.pi) u z +
      normalizedMarkSum M k α (2 / Real.pi) u y -
      normalizedEquilibriumAverage D M K k α (2 / Real.pi) u) := by
    funext Y
    dsimp [X, F, pairObservationWeight]
    simp only [normalizedWeightedSum_observationWeight, normalizedObservation,
      sourcePairAverageFamily_last b A I i hi]
    change 2 * _ + 2 * _ - 2 * _ = 2 * (_ + _ - _)
    ring
  have hX : Integrable (fun Y ↦ Real.exp (X Y)) μ := by
    rw [hstat]
    exact hiX
  have hc := (abs_le.mp (hcgf A b hA ht I hI i hi z y hz hρ hlo hhi u hu k hk)).2
  have hF : Measurable F := by
    dsimp [F]
    unfold normalizedWeightedSum normalizedMarkSum
    fun_prop
  apply source_pair_event_chernoff μ t A I i F hF At (sourceLowerTime m) q f _ ε hX
  · change cgf X μ 1 ≤ _
    rw [hstat]
    linarith
  · exact hAt

end SRWTightness
