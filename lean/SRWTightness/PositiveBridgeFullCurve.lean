import SRWTightness.PositiveBridgeCurvedProbability
import SRWTightness.PositiveBridgeReversal

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Constant-level first-half crossing estimate, used after reversing the terminal half. -/
theorem positiveBridge_constant_first_half (hBridge : PositiveBridgeRestrictionInput)
    (hPositive : BesselThreePositiveInput) (hHit : BesselThreeHittingInput)
    (T x y b M : ℝ) (hT : 0 < T) (hx : 0 < x) (hy : 0 < y) (hb : 0 < b)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T / 2), positiveEndpointBridge T x y t ω < b} ≤
      (8 * Real.exp M) * (b / x) := by
  have hc := positiveBridge_crossing_comparison hBridge hPositive T x y (T / 2) M
    hT hx hy (by positivity) le_rfl hxy hM (fun _ ↦ b) continuous_const
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T / 2), actualBesselThree T x t ω < b} ⊆
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω ≤ b} := by
    rintro ω ⟨t, ht, hcross⟩
    exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, hcross.le⟩
  exact (measureReal_mono hsub).trans ((hHit T x b hT hx hb).trans (min_le_right _ _))

/-- The second half is bounded by a constant level and viewed from the other endpoint. -/
theorem positiveBridge_curved_second_half (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hHit : BesselThreeHittingInput) (T x y H γ M : ℝ)
    (hT : 0 < T) (hx : 0 < x) (hH : 0 ≤ H) (hy : Real.sqrt (H + T) ≤ y)
    (hγ : 0 ≤ γ) (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (T / 2) T, positiveEndpointBridge T x y t ω < (H + t) ^ γ} ≤
      (8 * Real.exp M) * (H + T) ^ (γ - 1 / 2) := by
  have hd : 0 < H + T := by linarith
  have hy0 : 0 < y := (Real.sqrt_pos.mpr hd).trans_le hy
  have hsub : {ω | ∃ t ∈ Set.Icc (T / 2) T,
      positiveEndpointBridge T x y t ω < (H + t) ^ γ} ⊆
      {ω | ∃ u ∈ Set.Icc (0 : ℝ) (T / 2),
        positiveEndpointBridge T x y (T - u) ω < (H + T) ^ γ} := by
    rintro ω ⟨t, ht, hcross⟩
    refine ⟨T - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    have he : T - (T - t) = t := by ring
    rw [he]
    exact hcross.trans_le (Real.rpow_le_rpow (by linarith [ht.1]) (by linarith [ht.2]) hγ)
  have hxy' : 2 * y * x / T ≤ 1 := by simpa [mul_comm, mul_left_comm, mul_assoc] using hxy
  have hM' : (y - x) ^ 2 / (2 * T) ≤ M := by rw [sub_sq_comm y x]; exact hM
  have hstart : (H + T) ^ γ / y ≤ (H + T) ^ (γ - 1 / 2) := by
    calc
      _ ≤ (H + T) ^ γ / Real.sqrt (H + T) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hd.le _) (Real.sqrt_pos.mpr hd) hy
      _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hd]
  calc
    _ ≤ (positiveBridgeCoefficientLaw T x y).real
        {ω | ∃ u ∈ Set.Icc (0 : ℝ) (T / 2),
          positiveEndpointBridge T x y (T - u) ω < (H + T) ^ γ} := measureReal_mono hsub
    _ = (positiveBridgeCoefficientLaw T y x).real
        {ω | ∃ u ∈ Set.Icc (0 : ℝ) (T / 2),
          positiveEndpointBridge T y x u ω < (H + T) ^ γ} :=
      positiveBridge_reversed_crossing hReverse T x y (T / 2) hT hx hy0
        (by linarith) (fun _ ↦ (H + T) ^ γ) continuous_const
    _ ≤ (8 * Real.exp M) * ((H + T) ^ γ / y) :=
      positiveBridge_constant_first_half hBridge hPositive hHit T y x ((H + T) ^ γ) M
        hT hy0 hx (by positivity) hxy' hM'
    _ ≤ _ := mul_le_mul_of_nonneg_left hstart (by positivity)

/-- The complete positive-bridge failure bound before the choice of large source parameters. -/
theorem positiveBridge_curved_failure_bound (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (T x y H γ M : ℝ) (hT : 0 < T) (hH : 0 < H) (hx : Real.sqrt H ≤ x)
    (hy : Real.sqrt (H + T) ≤ y) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    (positiveBridgeCoefficientLaw T x y).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, positiveEndpointBridge T x y t ω < (H + t) ^ γ} ≤
      (8 * Real.exp M) *
        ((((2 : ℝ) ^ γ + C * (3 : ℝ) ^ γ / (1 - (2 : ℝ) ^ (γ - 1 / 2))) *
          H ^ (γ - 1 / 2)) + (H + T) ^ (γ - 1 / 2)) := by
  have hx0 : 0 < x := (Real.sqrt_pos.mpr hH).trans_le hx
  have hy0 : 0 < y := (Real.sqrt_pos.mpr (by linarith : 0 < H + T)).trans_le hy
  have hsub : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
      positiveEndpointBridge T x y t ω < (H + t) ^ γ} ⊆
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) (T / 2),
        positiveEndpointBridge T x y t ω < (H + t) ^ γ} ∪
      {ω | ∃ t ∈ Set.Icc (T / 2) T,
        positiveEndpointBridge T x y t ω < (H + t) ^ γ} := by
    rintro ω ⟨t, ht, hcross⟩
    rcases le_total t (T / 2) with h | h
    · exact Or.inl ⟨t, ⟨ht.1, h⟩, hcross⟩
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, hcross⟩
  have hfirst := positiveBridge_curved_first_half hBridge hPositive hInitial hHit C hMoment
    T x y H γ M hT hH hx hy0 hγ hγhalf hxy hM
  have hsecond := positiveBridge_curved_second_half hBridge hReverse hPositive hInitial
    T x y H γ M hT hx0 hH.le hy hγ hxy hM
  have h := (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans
    (add_le_add hfirst hsecond))
  simpa only [mul_add] using h

end SRWTightness
