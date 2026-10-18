import SRWTightness.SourceBridgedConvex

open MeasureTheory

namespace SRWTightness

/-- The two source windows and the measurable version of the actual bridge barrier. -/
def sourceTerminalBridgeEvent (t A : ℝ) (I : ℕ) (At q aStar d γ : ℝ) :
    Set ((Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :=
  {p | At ≤ p.1 (Fin.last (I + 1)) ∧ p.1 (Fin.last (I + 1)) ≤ At + 1 ∧
    2 * sourceObservationTime t A I (I + 1) + q - aStar - 1 ≤ p.1 ⟨I, by omega⟩ ∧
    p.1 ⟨I, by omega⟩ ≤ 2 * sourceObservationTime t A I (I + 1) + q - aStar ∧
    p ∈ sourceBridgedBarrierEvent t A I (sourceObservationTime t A I (I + 1))
      (fun v ↦ q - (d - v) ^ γ)}

theorem sourceTerminalBridgeEvent_measurable (t A : ℝ) (I : ℕ) (At q aStar d γ : ℝ) :
    MeasurableSet (sourceTerminalBridgeEvent t A I At q aStar d γ) := by
  have hm (i : Fin ((I + 1) + 1)) :
      Measurable (fun p : (Fin ((I + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace) ↦ p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  simp only [sourceTerminalBridgeEvent, Set.setOf_and]
  exact (measurableSet_le measurable_const (hm _)).inter
    ((measurableSet_le (hm _) measurable_const).inter
      ((measurableSet_le measurable_const (hm _)).inter
        ((measurableSet_le (hm _) measurable_const).inter
          (sourceBridgedBarrierEvent_measurable t A I (sourceObservationTime t A I (I + 1))
            (fun v ↦ q - (d - v) ^ γ)))))

theorem sourceTerminalBridgeEvent_convex (t A : ℝ) (I : ℕ) (At q aStar d γ : ℝ)
    (ω : ℕ → GaussianCoefficientSpace) :
    Convex ℝ ((fun x ↦ (x, ω)) ⁻¹' sourceTerminalBridgeEvent t A I At q aStar d γ) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxl, hxu, hxl', hxu', hxp⟩ := hx
  obtain ⟨hyl, hyu, hyl', hyu', hyp⟩ := hy
  have hz (r : ℝ) : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  have hl (L X Y : ℝ) (hx : L ≤ X) (hy : L ≤ Y) : L ≤ a * X + b * Y := by
    nlinarith [hz L, mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]
  have hu (U X Y : ℝ) (hx : X ≤ U) (hy : Y ≤ U) : a * X + b * Y ≤ U := by
    nlinarith [hz U, mul_nonneg ha (sub_nonneg.mpr hx), mul_nonneg hb (sub_nonneg.mpr hy)]
  refine ⟨hl _ _ _ hxl hyl, hu _ _ _ hxu hyu, hl _ _ _ hxl' hyl', hu _ _ _ hxu' hyu', ?_⟩
  exact sourceBridgedBarrierEvent_convex t A I ω (sourceObservationTime t A I (I + 1))
    (fun v ↦ q - (d - v) ^ γ) hxp hyp ha hb hab

theorem sourceTerminalBridgeEvent_ae_iff (t A : ℝ) (I : ℕ) (At q aStar d γ : ℝ)
    (hγ : 0 ≤ γ) :
    ∀ᵐ ω ∂independentBridgeLaw ℕ, ∀ x : Fin ((I + 1) + 1) → ℝ,
      (x, ω) ∈ sourceTerminalBridgeEvent t A I At q aStar d γ ↔
        At ≤ x (Fin.last (I + 1)) ∧ x (Fin.last (I + 1)) ≤ At + 1 ∧
        q - aStar - 1 ≤ x ⟨I, by omega⟩ - 2 * sourceObservationTime t A I (I + 1) ∧
        x ⟨I, by omega⟩ - 2 * sourceObservationTime t A I (I + 1) ≤ q - aStar ∧
        ∀ v : ℝ, 0 ≤ v → v ≤ sourceObservationTime t A I (I + 1) →
          sourceBridgedPath t A I x ω v ≤ q - (d - v) ^ γ := by
  filter_upwards [sourceBridgedBarrierEvent_ae_rpow t A I
    (sourceObservationTime t A I (I + 1)) q d γ hγ] with ω hω
  intro x
  change (_ ∧ _ ∧ _ ∧ _ ∧ (x, ω) ∈ sourceBridgedBarrierEvent _ _ _ _ _) ↔ _
  rw [hω x]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, by linarith, by linarith, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, by linarith, by linarith, h5⟩

end SRWTightness
