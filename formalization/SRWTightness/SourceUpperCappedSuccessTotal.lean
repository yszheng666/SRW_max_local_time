import SRWTightness.SourceUpperSuccessPrincipal
import SRWTightness.SourceUpperPrincipalErrorDecay
import SRWTightness.SourceUpperAnnulusRootReduction

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual positive capped-root successes have the height tail and an exponentially vanishing error. -/
theorem source_upper_capped_success_total (hinput : PotentialKernelAsymptoticInput)
    (hReg : FiniteGaussianRegressionInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hSum : PositiveConvolutionInput) (hMoment : SubGaussianPositiveMomentInput)
    (hConv : GaussianPositiveConvolutionInput) (hMills : GaussianMillsInput)
    (hIntegral : WeightedGaussianIntegralInput) (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput) (hScale : ExponentialFloorScaleInput)
    (hCount : LatticeDiskCountInput) (hTranslation : ProjectedMarkTranslationInput)
    (hGW : GWBarrierUpperInput) :
    ∃ H E : ℝ, 0 < H ∧ 0 < E ∧ ∀ᶠ t : ℝ in atTop,
      (∀ b ∈ sourceUpperBlockCenters t, MarkedGWTreeInput (Mark (sourceUpperBlock t b))) →
      (∀ b ∈ sourceUpperBlockCenters t,
        ∀ [MeasurableSpace (List (Mark (sourceUpperBlock t b)))]
          [MeasurableSingletonClass (List (Mark (sourceUpperBlock t b)))],
          MarkedGWForestJointInput (Mark (sourceUpperBlock t b))) →
      ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
        pathLaw (sourceUpperFixedRootSuccess t s b J)) ≤
        ENNReal.ofReal (H * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s)) +
          E * Real.exp (-2 * t)) := by
  classical
  obtain ⟨A, W, K, C, κ, ρ, B, hA, hW, hK, hC, hκ, hρ, hB, hp⟩ :=
    source_upper_success_principal hinput hReg hBDZ hSup hSum hMoment hConv hMills
      hIntegral hGreen hEmbed hScale hCount hTranslation hGW
  obtain ⟨D, hD, hd⟩ := source_upper_principal_error_decay hScale K κ C ρ hK hκ hC.le hρ
  refine ⟨2 * D * B * C, 100 * C, by positivity, by positivity, ?_⟩
  filter_upwards [hp, hd,
    (tendsto_order.1 (source_upper_forest_comparison_factor_tendsto_one A W)).2
      2 (by norm_num)] with t hp hd hfactor
  intro htree hjoint s hs hslog
  let F := Real.exp ((3584 * A + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
    Real.exp (-3 * sourceUpperLogRadius t / 4))
  let P := fun b : Site ↦ fun J : ℕ ↦
    ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
      (sourceUpperSupportedPrincipalSum t s C κ B b J +
        ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ))
  have hpoint (b : Site) (hb : b ∈ sourceUpperBlockCenters t)
      (J : ℕ) (hJ : J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊) :
      pathLaw (sourceUpperFixedRootSuccess t s b J) ≤ ENNReal.ofReal 2 * P b J := by
    letI : MeasurableSpace (List (Mark (sourceUpperBlock t b))) := ⊤
    letI : MeasurableSingletonClass (List (Mark (sourceUpperBlock t b))) := ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b)) := ⊤
    letI : MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b)) := ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) := ⊤
    letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) := ⟨fun _ ↦ trivial⟩
    have hj := Finset.mem_Icc.mp hJ
    have hjcap : (J : ℝ) ≤ t ^ 2 := (Nat.le_floor_iff (sq_nonneg t)).mp hj.2
    have hh := hp b hb (htree b hb) (hjoint b hb) s hs hslog J hj.1 hjcap
    change pathLaw (sourceUpperFixedRootSuccess t s b J) ≤ _ at hh
    apply hh.trans
    change ENNReal.ofReal (_ * F) * _ ≤ _
    rw [ENNReal.ofReal_mul' (Real.exp_nonneg _)]
    calc
      _ = ENNReal.ofReal F * P b J := by dsimp [P, F]; ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfactor.le) bot_le
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
        ENNReal.ofReal 2 * P b J :=
      Finset.sum_le_sum (fun b hb ↦ Finset.sum_le_sum (fun J hJ ↦ hpoint b hb J hJ))
    _ = ENNReal.ofReal 2 * ∑ b ∈ sourceUpperBlockCenters t,
        ∑ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊, P b J := by simp only [Finset.mul_sum]
    _ ≤ ENNReal.ofReal 2 *
        (ENNReal.ofReal (D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) +
          ENNReal.ofReal (50 * C * Real.exp (-2 * t))) := by
      exact mul_le_mul_of_nonneg_left (hd s hs hslog B hB.le _) bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end SRWTightness
