import SRWTightness.GaussianSquareDyadicCover
import SRWTightness.GaussianShiftedTailEnvelope
import SRWTightness.GaussianDomainMaximum
import SRWTightness.ExternalBDZSquareMaximum
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The full maximum domain comparison is unchanged by a positive normalization. -/
theorem gaussian_normalized_full_maximum_comparison (D E : Finset Site) (hED : E ⊆ D)
    (σ t : ℝ) (hσ : 0 < σ) :
    (gaussianGreenLaw E E).real {φ | ∃ x : E, t ≤ φ x / σ} ≤
      2 * (gaussianGreenLaw D D).real {φ | ∃ x : D, t ≤ φ x / σ} := by
  have he (K : Finset Site) : {φ : EuclideanSpace ℝ K | ∃ x : K, t ≤ φ x / σ} =
      upperExceedance (t * σ) := by
    ext φ
    simp only [upperExceedance, Set.mem_setOf_eq, le_div_iff₀ hσ]
  rw [he E, he D]
  exact gaussian_maximum_le_larger_domain D E hED _

/-- A twofold side enlargement changes the square centering by at most2log2. -/
theorem gaussian_square_center_bounds (R S : ℝ) (hR : 4 ≤ R) (hRS : R ≤ S)
    (hSR : S ≤ 2 * R) :
    1 ≤ Real.log R ∧ 1 ≤ Real.log S ∧ Real.log S ≤ 2 * Real.log R ∧
      (2 * Real.log S - (3 / 4 : ℝ) * Real.log (Real.log S)) -
        (2 * Real.log R - (3 / 4 : ℝ) * Real.log (Real.log R)) ≤ 2 * Real.log 2 := by
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hfour : 1 ≤ Real.log (4 : ℝ) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  have hL : Real.log R ≤ Real.log S := Real.log_le_log hR0 hRS
  have hR1 : 1 ≤ Real.log R := hfour.trans (Real.log_le_log (by norm_num) hR)
  have hU : Real.log S ≤ Real.log R + Real.log 2 := by
    have hh := Real.log_le_log hS0 hSR
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hR0.ne'] at hh
    linarith
  have htwo : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) (by linarith)
  have hloglog := Real.log_le_log (by linarith : 0 < Real.log R) hL
  exact ⟨hR1, hR1.trans hL, by linarith, by linarith⟩

/-- The source BDZ tail extends to every integer square size, with one uniform pair of constants. -/
theorem source_bdz_all_square_sizes (hBDZ : BDZDyadicSquareMaximumInput) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (a : Site) (N : ℕ), 4 ≤ N → ∀ z : ℝ, 1 ≤ z →
      (gaussianGreenLaw (latticeSquareInterior a N) (latticeSquareInterior a N)).real
        {φ | ∃ x : latticeSquareInterior a N,
          2 * Real.log (N : ℝ) - (3 / 4 : ℝ) * Real.log (Real.log (N : ℝ)) + z ≤
            φ x / Real.sqrt (2 / Real.pi)} ≤
        C * (1 + z) * Real.exp (-2 * z - κ * z ^ 2 / Real.log (N : ℝ)) := by
  obtain ⟨P, c, hP, hc, hRaw⟩ := hBDZ
  let δ : ℝ := 2 * Real.log 2
  let κ : ℝ := c / 4
  let G : ℝ := (2 * P) * Real.exp (2 * δ + c * δ ^ 2 / 2)
  let K : ℝ := Real.exp (2 * (δ + 1) + κ * (δ + 1) ^ 2)
  let C : ℝ := G + K
  have hδ : 0 ≤ δ := mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  have hK : 0 < K := Real.exp_pos _
  refine ⟨C, κ, add_pos hG hK, hκ, ?_⟩
  intro a N hN z hz
  obtain ⟨n, hn, hNn, hnN, hsub⟩ := lattice_square_dyadic_cover N hN
  let E := latticeSquareInterior a N
  let D := latticeSquareInterior a (2 ^ n)
  let h := Real.log (N : ℝ)
  let H := Real.log ((2 : ℝ) ^ n)
  let m := 2 * h - (3 / 4 : ℝ) * Real.log h
  let M := 2 * H - (3 / 4 : ℝ) * Real.log H
  let q := z - δ
  have hbounds := gaussian_square_center_bounds (N : ℝ) ((2 : ℝ) ^ n)
    (by exact_mod_cast hN) (by exact_mod_cast hNn) (by exact_mod_cast hnN)
  have hh : 1 ≤ h := hbounds.1
  have hH : 0 < H := by have ht := hbounds.2.1; dsimp [H]; linarith
  have hHu : H ≤ 2 * h := hbounds.2.2.1
  have hcenter : M - m ≤ δ := hbounds.2.2.2
  change (gaussianGreenLaw E E).real
    {φ | ∃ x : E, m + z ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
      C * (1 + z) * Real.exp (-2 * z - κ * z ^ 2 / h)
  by_cases hq : 1 ≤ q
  · have hcomp := gaussian_normalized_full_maximum_comparison D E (hsub a)
      (Real.sqrt (2 / Real.pi)) (m + z) (by positivity)
    have hthreshold : M + q ≤ m + z := by dsimp [q]; linarith
    have hmono : (gaussianGreenLaw D D).real
        {φ | ∃ x : D, m + z ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        (gaussianGreenLaw D D).real
          {φ | ∃ x : D, M + q ≤ φ x / Real.sqrt (2 / Real.pi)} := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      rintro φ ⟨x, hx⟩
      exact ⟨x, hthreshold.trans hx⟩
    have htail : (gaussianGreenLaw D D).real
        {φ | ∃ x : D, M + q ≤ φ x / Real.sqrt (2 / Real.pi)} ≤
        P * (1 + q) * Real.exp (-2 * q - c * q ^ 2 / H) := hRaw a n hn q hq
    have henvelope := gaussian_shifted_tail_envelope (2 * P) c δ z h H
      (by positivity) hc.le hδ hh hH hHu hq
    have hGC : G ≤ C := le_add_of_nonneg_right hK.le
    calc
      _ ≤ 2 * (gaussianGreenLaw D D).real
          {φ | ∃ x : D, M + q ≤ φ x / Real.sqrt (2 / Real.pi)} :=
        hcomp.trans (mul_le_mul_of_nonneg_left hmono (by norm_num))
      _ ≤ 2 * (P * (1 + q) * Real.exp (-2 * q - c * q ^ 2 / H)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = (2 * P) * (1 + q) * Real.exp (-2 * q - c * q ^ 2 / H) := by ring
      _ ≤ G * (1 + z) * Real.exp (-2 * z - κ * z ^ 2 / h) := henvelope
      _ ≤ C * (1 + z) * Real.exp (-2 * z - κ * z ^ 2 / h) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hGC (by linarith)) (Real.exp_nonneg _)
  · have hcompact := gaussian_compact_tail_envelope κ (δ + 1) z h hκ.le
      (by linarith) (by linarith) (by dsimp [q] at hq; linarith) hh
    have hKC : K ≤ C := le_add_of_nonneg_left hG.le
    exact (measureReal_le_one (μ := gaussianGreenLaw E E)).trans
      (hcompact.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC (by linarith)) (Real.exp_nonneg _)))

end SRWTightness
