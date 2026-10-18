import SRWTightness.SourceUpperLiteralIntegerProbability
import SRWTightness.SourceMainInternalMarkedForests
import SRWTightness.SourceUpperCappedSuccessTotal

open Filter MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual capped successes satisfy the literal root-level principal formula
with separated error. -/
theorem source_upper_literal_capped_root_success (hP : PotentialKernelAsymptoticInput)
    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)
    (hGreen : BufferedSquareGreenInput) (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput)
    (hTranslation : ProjectedMarkTranslationInput) (hGW : GWBarrierUpperInput) :
    ∃ K κ D E : ℝ, 1 ≤ K ∧ 0 < κ ∧ 0 < D ∧ 0 < E ∧
      ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t → ∀ k : ℕ,
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      (∑ b ∈ sourceUpperBlockRootFamily t k, ∑ J ∈ Finset.Icc 1 ⌊t ^ 2⌋₊,
        pathLaw (sourceUpperFixedRootSuccess t s b J)) ≤
        ENNReal.ofReal (D * (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (2 * t - 2 * d) / L ^ 2 *
            sourceUpperLiteralIntegerSeries t s (κ / 4) L + E * Real.exp (-2 * t)) := by
  classical
  obtain ⟨A, W, K, C, κ, ρ, B, hA, hW, hK, hC, hκ, hρ, hB, hp⟩ :=
    source_upper_success_principal hP finite_gaussian_regression_input_internal hBDZ hSup
      positive_convolution_input_internal sub_gaussian_positive_moment_input_internal
      gaussian_positive_convolution_input_internal gaussian_mills_input_internal
      weighted_gaussian_integral_input_internal hGreen hEmbed exponential_floor_scale_input
      lattice_disk_count_input_internal hTranslation hGW
  obtain ⟨D, hD, hprincipal⟩ := source_upper_literal_integer_probability K κ hK hκ
  refine ⟨K, κ, 2 * D * B * C, 100 * C, hK, hκ, by positivity, by positivity, ?_⟩
  filter_upwards [hp, hprincipal,
    source_upper_spatial_remainder_decay exponential_floor_scale_input K C ρ hK hC.le hρ,
    (tendsto_order.1 (source_upper_forest_comparison_factor_tendsto_one A W)).2
      2 (by norm_num), source_upper_terminal_sqrt_scale exponential_floor_scale_input,
    source_upper_terminal_quarter_depth_eventually] with t hp hprincipal he hfactor hd hr
  intro s hs hslog k
  dsimp only
  let I := sourceUpperBlockRootFamily t k
  let N := ⌊t ^ 2⌋₊
  let F := Real.exp ((3584 * A + 96 * W) * t ^ 2 * sourceUpperLogRadius t *
    Real.exp (-3 * sourceUpperLogRadius t / 4))
  let weight := fun b : Site ↦ fun J : ℕ ↦
    ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1))
  let error := sourceUpperTerminalRemainder t C ρ
  let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let principal := D * B * C * (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
    Real.exp (2 * t - 2 * d) / L ^ 2 * sourceUpperLiteralIntegerSeries t s (κ / 4) L
  have hd0 : 0 ≤ d := (Real.sqrt_pos.mp (by linarith [hd.1])).le
  have hseries := source_upper_literal_integer_series_nonneg t s (κ / 4) L hd0 hr
  have hprincipal0 : 0 ≤ principal := by dsimp [principal]; positivity
  have herror : 0 ≤ error := by dsimp [error, sourceUpperTerminalRemainder]; positivity
  have hpoint (b : Site) (hb : b ∈ I) (J : ℕ) (hJ : J ∈ Finset.Icc 1 N) :
      pathLaw (sourceUpperFixedRootSuccess t s b J) ≤
        ENNReal.ofReal 2 * (weight b J *
          (sourceUpperSupportedPrincipalSum t s C κ B b J + ENNReal.ofReal error)) := by
    have hb' := (Finset.mem_filter.mp hb).1
    letI : MeasurableSpace (List (Mark (sourceUpperBlock t b))) := ⊤
    letI : MeasurableSingletonClass (List (Mark (sourceUpperBlock t b))) :=
      ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b)) := ⊤
    letI : MeasurableSingletonClass (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b)) := ⟨fun _ ↦ trivial⟩
    letI : MeasurableSpace (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) := ⊤
    letI : MeasurableSingletonClass (List (FiniteExcursionRecord (Mark (sourceUpperBlock t b))
      (sourceUpperBlockForestDepth t b))) := ⟨fun _ ↦ trivial⟩
    have hj := Finset.mem_Icc.mp hJ
    have hcap : (J : ℝ) ≤ t ^ 2 := (Nat.le_floor_iff (sq_nonneg t)).mp hj.2
    have hh := hp b hb' marked_gw_tree_input_internal marked_gw_forest_joint_input_internal
      s hs hslog J hj.1 hcap
    change pathLaw (sourceUpperFixedRootSuccess t s b J) ≤ _ at hh
    apply hh.trans
    change ENNReal.ofReal (_ * F) * _ ≤ _
    rw [ENNReal.ofReal_mul' (Real.exp_nonneg _)]
    calc
      _ = ENNReal.ofReal F * (weight b J *
          (sourceUpperSupportedPrincipalSum t s C κ B b J + ENNReal.ofReal error)) := by
        dsimp [weight, error, F]
        ac_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hfactor.le) bot_le
  have hmain : (∑ b ∈ I, ∑ J ∈ Finset.Icc 1 N,
      weight b J * sourceUpperSupportedPrincipalSum t s C κ B b J) ≤
      ENNReal.ofReal principal := by
    apply le_trans _ (hprincipal s hs hslog B C hB.le hC.le (N + 1) k)
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum_of_subset
    intro J hJ
    have hj := (Finset.mem_Icc.mp hJ).2
    exact Finset.mem_range.mpr (by omega)
  have herr : (∑ b ∈ I, ∑ J ∈ Finset.Icc 1 N,
      weight b J * ENNReal.ofReal error) ≤ ENNReal.ofReal (50 * C * Real.exp (-2 * t)) := by
    calc
      _ ≤ ∑ b ∈ I, ENNReal.ofReal (((sourceUpperBlockRoot t b : ℝ) + K) * error) := by
        apply Finset.sum_le_sum
        intro b hb
        apply upper_positive_root_geometric_error _ error _ herror _
          (fun J hJ ↦ (Finset.mem_Icc.mp hJ).1)
        linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]
      _ ≤ ∑ b ∈ sourceUpperBlockCenters t,
          ENNReal.ofReal (((sourceUpperBlockRoot t b : ℝ) + K) * error) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ ↦
          mul_nonneg (by positivity : 0 ≤ (sourceUpperBlockRoot t b : ℝ) + K) herror)]
        exact ENNReal.ofReal_le_ofReal he
  calc
    _ ≤ ∑ b ∈ I, ∑ J ∈ Finset.Icc 1 N, ENNReal.ofReal 2 * (weight b J *
        (sourceUpperSupportedPrincipalSum t s C κ B b J + ENNReal.ofReal error)) :=
      Finset.sum_le_sum (fun b hb ↦ Finset.sum_le_sum (fun J hJ ↦ hpoint b hb J hJ))
    _ = ENNReal.ofReal 2 * ((∑ b ∈ I, ∑ J ∈ Finset.Icc 1 N,
        weight b J * sourceUpperSupportedPrincipalSum t s C κ B b J) +
        ∑ b ∈ I, ∑ J ∈ Finset.Icc 1 N, weight b J * ENNReal.ofReal error) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal principal +
        ENNReal.ofReal (50 * C * Real.exp (-2 * t))) :=
      mul_le_mul_of_nonneg_left (add_le_add hmain herr) bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_add hprincipal0 (by positivity),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      dsimp [principal, d, L]
      ring

end SRWTightness
