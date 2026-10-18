import SRWTightness.ExternalBesselThree
import SRWTightness.CurvedBarrierDyadicSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Failure of the reversed curved barrier on a specified time interval. -/
def besselCurvedCrossing (T x H γ l r : ℝ) : Set (Fin 3 → GaussianCoefficientSpace) :=
  {ω | ∃ t ∈ Set.Icc l r, actualBesselThree T x t ω < (H + t) ^ γ}

/-- The first interval is controlled using the starting-point hitting estimate. -/
theorem besselCurvedCrossing_initial (hHit : BesselThreeHittingInput)
    (T x H γ : ℝ) (hT : 0 < T) (hx : 0 < x) (hH : 0 < H) (hγ : 0 ≤ γ) :
    (independentBridgeLaw (Fin 3)).real (besselCurvedCrossing T x H γ 0 (min H T)) ≤
      (2 * H) ^ γ / x := by
  have hsub : besselCurvedCrossing T x H γ 0 (min H T) ⊆
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω ≤ (2 * H) ^ γ} := by
    rintro ω ⟨t, ht, hcross⟩
    refine ⟨t, ⟨ht.1, ht.2.trans (min_le_right _ _)⟩, hcross.le.trans ?_⟩
    exact Real.rpow_le_rpow (by linarith [ht.1])
      (by linarith [ht.2.trans (min_le_left H T)]) hγ
  exact (measureReal_mono hsub).trans
    ((hHit T x ((2 * H) ^ γ) hT hx (by positivity)).trans (min_le_right _ _))

/-- A dyadic interval is controlled by a standard delayed constant-level hitting bound. -/
theorem besselCurvedCrossing_dyadic (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (T x H γ L : ℝ) (hT : 0 < T) (hx : 0 < x) (hH : 0 < H)
    (hγ : 0 ≤ γ) (hHL : H ≤ L) (hLT : L ≤ T) :
    (independentBridgeLaw (Fin 3)).real
      (besselCurvedCrossing T x H γ L (min (2 * L) T)) ≤
      (3 * L) ^ γ * (C / Real.sqrt L) := by
  have hL : 0 < L := hH.trans_le hHL
  have hsub : besselCurvedCrossing T x H γ L (min (2 * L) T) ⊆
      {ω | ∃ t ∈ Set.Icc L T, actualBesselThree T x t ω ≤ (3 * L) ^ γ} := by
    rintro ω ⟨t, ht, hcross⟩
    refine ⟨t, ⟨ht.1, ht.2.trans (min_le_right _ _)⟩, hcross.le.trans ?_⟩
    exact Real.rpow_le_rpow (by linarith [ht.1])
      (by linarith [ht.2.trans (min_le_left (2 * L) T)]) hγ
  exact (measureReal_mono hsub).trans
    (besselThree_delayed_crossing_bound hHit C hMoment T x ((3 * L) ^ γ) L
      hT hx (by positivity) hL hLT)

/-- Dyadic estimates remain valid after the observation horizon, since the event is empty. -/
theorem besselCurvedCrossing_dyadic_all (hHit : BesselThreeDelayedHittingInput)
    (C : ℝ) (hMoment : BesselThreeInverseMomentInput C)
    (T x H γ L : ℝ) (hT : 0 < T) (hx : 0 < x) (hH : 0 < H)
    (hγ : 0 ≤ γ) (hHL : H ≤ L) :
    (independentBridgeLaw (Fin 3)).real
      (besselCurvedCrossing T x H γ L (min (2 * L) T)) ≤
      C * ((3 * L) ^ γ / Real.sqrt L) := by
  by_cases hLT : L ≤ T
  · have h := besselCurvedCrossing_dyadic hHit C hMoment T x H γ L hT hx hH hγ hHL hLT
    convert h using 1 <;> ring
  · have he : besselCurvedCrossing T x H γ L (min (2 * L) T) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨t, ht, _⟩
      exact hLT (ht.1.trans (ht.2.trans (min_le_right _ _)))
    rw [he]
    simp only [measureReal_empty]
    exact mul_nonneg hMoment.1.le (div_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.sqrt_nonneg _))

/-- Summing the initial and dyadic pieces gives the manuscript's unconditioned curved bound. -/
theorem besselCurvedCrossing_bound (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (T x H γ : ℝ) (hT : 0 < T) (hx : 0 < x) (hH : 0 < H)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) (n : ℕ) (hn : T ≤ (2 : ℝ) ^ n * H) :
    (independentBridgeLaw (Fin 3)).real (besselCurvedCrossing T x H γ 0 T) ≤
      (2 * H) ^ γ / x +
        C * (((3 : ℝ) ^ γ * H ^ (γ - 1 / 2)) / (1 - (2 : ℝ) ^ (γ - 1 / 2))) := by
  let E j := besselCurvedCrossing T x H γ ((2 : ℝ) ^ j * H)
    (min (2 * ((2 : ℝ) ^ j * H)) T)
  have hsub : besselCurvedCrossing T x H γ 0 T ⊆
      besselCurvedCrossing T x H γ 0 (min H T) ∪ ⋃ j ∈ Finset.range n, E j := by
    rintro ω ⟨t, ht, hcross⟩
    rcases curvedBarrier_dyadic_cover H t n (ht.2.trans hn) with h | ⟨j, hj, hlo, hhi⟩
    · exact Or.inl ⟨t, ⟨ht.1, le_min h ht.2⟩, hcross⟩
    · right
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hj, ⟨t, ⟨hlo, le_min hhi ht.2⟩, hcross⟩⟩⟩
  have he (j : ℕ) : (independentBridgeLaw (Fin 3)).real (E j) ≤
      C * ((3 * ((2 : ℝ) ^ j * H)) ^ γ / Real.sqrt ((2 : ℝ) ^ j * H)) := by
    apply besselCurvedCrossing_dyadic_all hHit C hMoment T x H γ _ hT hx hH hγ
    exact le_mul_of_one_le_left hH.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  calc
    _ ≤ (independentBridgeLaw (Fin 3)).real
        (besselCurvedCrossing T x H γ 0 (min H T) ∪ ⋃ j ∈ Finset.range n, E j) :=
      measureReal_mono hsub
    _ ≤ (independentBridgeLaw (Fin 3)).real (besselCurvedCrossing T x H γ 0 (min H T)) +
        ∑ j ∈ Finset.range n, (independentBridgeLaw (Fin 3)).real (E j) :=
      (measureReal_union_le _ _).trans
        (add_le_add le_rfl (measureReal_biUnion_finset_le _ _))
    _ ≤ (2 * H) ^ γ / x + ∑ j ∈ Finset.range n,
        C * ((3 * ((2 : ℝ) ^ j * H)) ^ γ / Real.sqrt ((2 : ℝ) ^ j * H)) :=
      add_le_add (besselCurvedCrossing_initial hInitial T x H γ hT hx hH hγ)
        (Finset.sum_le_sum (fun j _ ↦ he j))
    _ = (2 * H) ^ γ / x + C * ∑ j ∈ Finset.range n,
        (3 * ((2 : ℝ) ^ j * H)) ^ γ / Real.sqrt ((2 : ℝ) ^ j * H) := by
      rw [Finset.mul_sum]
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (curvedBarrier_dyadic_sum H γ hH hγhalf n) hMoment.1.le)

end SRWTightness
