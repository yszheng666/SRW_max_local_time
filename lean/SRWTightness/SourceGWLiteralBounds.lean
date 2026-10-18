import SRWTightness.ExternalGWBarrier

namespace SRWTightness

/-- Positive source lattice endpoints are exactly the square-root population coordinates. -/
theorem source_gw_start_height (k : ℕ) (x : ℝ) (hx : Real.sqrt 2 ≤ x)
    (hk : x ^ 2 / 2 = (k : ℝ)) :
    0 < k ∧ Real.sqrt (2 * (k : ℝ)) = x := by
  have hx0 : 0 < x := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).trans_le hx
  have hp : 2 * (k : ℝ) = x ^ 2 := by nlinarith
  constructor
  · by_contra h
    have hk0 : k = 0 := by omega
    rw [hk0] at hp
    norm_num at hp
    nlinarith
  · rw [hp, Real.sqrt_sq hx0.le]

/-- Source (3.1) with the real source endpoint and the complete literal prefactor. -/
theorem source_gw_literal_upper (hGW : GWBarrierUpperInput)
    (δ C η ε : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hη : 1 < η)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L k : ℕ) (x y a b : ℝ), 0 < L →
      Real.sqrt 2 ≤ x → x ^ 2 / 2 = (k : ℝ) → x ≤ η * L →
      Real.sqrt 2 ≤ y → y ≤ η * L → x ≤ a → y ≤ b →
      (geometricGWRecordLaw k L).real (gwUpperBarrierEvent L a b y δ C ε) ≤
        K * ((1 + a - x) * (1 + b - y) / (L : ℝ)) *
          Real.sqrt (x / (y * L)) * Real.exp (-((x - y) ^ 2 / (2 * (L : ℝ)))) := by
  obtain ⟨K, hK, hh⟩ := hGW δ C η ε hδ hC hη hε hε'
  refine ⟨K, hK, ?_⟩
  intro L k x y a b hL hx hk hxη hy hyη hxa hyb
  obtain ⟨hk0, he⟩ := source_gw_start_height k x hx hk
  have hb := hh L k a b y hL hk0
  dsimp only at hb
  rw [he] at hb
  have hp := hb hxη hy hyη hxa hyb
  unfold gwBarrierPrefactor at hp
  convert hp using 1 <;> ring

/-- Source (3.2) retains the two-sided tube, both lattice conditions and truncated prefactor. -/
theorem source_gw_literal_lower (hGW : GWBarrierLowerInput)
    (δ C Ctilde η ε : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C) (hCC : C < Ctilde)
    (hη : 1 < η) (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L k : ℕ) (x y a b : ℝ), 0 < L →
      Real.sqrt 2 ≤ x → x ^ 2 / 2 = (k : ℝ) → x ≤ η * L →
      Real.sqrt 2 ≤ y → y ≤ η * L → x ≤ a → y ≤ b →
      (1 + a - x) * (1 + b - y) ≤ η * L →
      (L : ℝ) / η ≤ max (x * y) |y - x| →
      gwPositiveLatticeIntersects y (y + δ) →
      (∀ j : ℕ, 0 < j → j < L → gwPositiveLatticeIntersects
        (gwBarrierLine x y j L - Ctilde * gwBarrierCurvature (1 / 2 + ε) j L)
        (gwBarrierLine a b j L - C * gwBarrierCurvature (1 / 2 - ε) j L)) →
      c * ((1 + a - x) * (1 + b - y) / (L : ℝ)) *
        min (Real.sqrt (x / (y * L))) 1 *
          Real.exp (-((x - y) ^ 2 / (2 * (L : ℝ)))) ≤
        (geometricGWRecordLaw k L).real (gwTubeEvent L x y a b δ C Ctilde ε) := by
  obtain ⟨c, hc, hh⟩ := hGW δ C Ctilde η ε hδ hC hCC hη hε hε'
  refine ⟨c, hc, ?_⟩
  intro L k x y a b hL hx hk hxη hy hyη hxa hyb hprod hmax hlattice htube
  obtain ⟨hk0, he⟩ := source_gw_start_height k x hx hk
  have hb := hh L k a b y hL hk0
  dsimp only at hb
  rw [he] at hb
  have hp := hb hxη hy hyη hxa hyb hprod hmax hlattice htube
  unfold gwBarrierPrefactor at hp
  convert hp using 1 <;> ring

end SRWTightness
