import SRWTightness.ExternalBDZSquareMaximum
import SRWTightness.GaussianGreenTranslation
import SRWTightness.GaussianShiftedTailEnvelope
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The unnormalized centering in Bramson--Ding--Zeitouni (1). -/
noncomputable def bdzLiteratureCenter (n : ℕ) : ℝ :=
  2 * Real.sqrt (2 / Real.pi) *
    (Real.log ((2 : ℝ) ^ n) - (3 / 8 : ℝ) * Real.log (Real.log ((2 : ℝ) ^ n)))

/-- The original discrete Gaussian field specified by its Dirichlet precision matrix.
The diagonal is one and each interior nearest-neighbor entry is -1/4. -/
noncomputable def bdzLiteratureFieldLaw (n : ℕ) :
    Measure (EuclideanSpace ℝ (latticeSquareInterior 0 (2 ^ n))) :=
  multivariateGaussian 0 (1 - killedTransition (latticeSquareInterior 0 (2 ^ n)))⁻¹

/-- The Dirichlet-precision field is exactly the actual killed-walk Green field. -/
theorem bdz_literature_field_eq_green (n : ℕ) :
    bdzLiteratureFieldLaw n =
      gaussianGreenLaw (latticeSquareInterior 0 (2 ^ n))
        (latticeSquareInterior 0 (2 ^ n)) := by
  unfold bdzLiteratureFieldLaw gaussianGreenLaw
  rw [← greenMatrix_eq_inverse]
  rfl

/-- Extend the interior field by the prescribed zero values on the box boundary. -/
noncomputable def bdzLiteratureValue (n : ℕ)
    (φ : EuclideanSpace ℝ (latticeSquareInterior 0 (2 ^ n))) (x : Site) : ℝ :=
  if hx : x ∈ latticeSquareInterior 0 (2 ^ n) then φ ⟨x, hx⟩ else 0

/-- BDZ Lemma 3.8 (39), in the original field units and at the origin.
Here n=log_2 N, N=2^n; the field has killed SRW Green covariance and zero
values on the boundary vertices of the N-by-N box; the maximum is over the
whole box, including those zero boundary values.
No translation, height rescaling or extension below z=1 is assumed. -/
def BDZLiteratureDyadicMaximumInput : Prop :=
  ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∀ n : ℕ, 2 ≤ n → ∀ z : ℝ, 1 ≤ z →
    (bdzLiteratureFieldLaw n).real
      {φ | ∃ x : latticeSquare 0 (2 ^ n),
        bdzLiteratureCenter n + z ≤ bdzLiteratureValue n φ x} ≤
      C' * z * Real.exp (-Real.sqrt (2 * Real.pi) * z) *
        Real.exp (-C⁻¹ * z ^ 2 / (n : ℝ))

/-- The interior with fixed-zero surrounding boundary translates literally. -/
theorem latticeSquareInterior_translate (a : Site) (N : ℕ) :
    translateFinset a (latticeSquareInterior 0 N) = latticeSquareInterior a N := by
  ext x
  simp only [mem_translateFinset_iff, mem_latticeSquareInterior, Prod.fst_sub,
    Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, zero_add]
  omega

/-- The source's original coefficient becomes exactly two in normalized units. -/
theorem bdz_sqrt_normalization :
    Real.sqrt (2 * Real.pi) * Real.sqrt (2 / Real.pi) = 2 := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have he : (2 * Real.pi) * (2 / Real.pi) = 4 := by
    field_simp
    ring
  rw [he, show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

set_option maxHeartbeats 1000000 in
/-- The original BDZ tail implies the normalized, translated interface used downstream. -/
theorem bdz_dyadic_square_maximum_of_literature
    (hBDZ : BDZLiteratureDyadicMaximumInput) : BDZDyadicSquareMaximumInput := by
  obtain ⟨C, P, hC, hP, hsource⟩ := hBDZ
  let σ := Real.sqrt (2 / Real.pi)
  let c := (2 / Real.pi) * Real.log 2 / C
  let a := 1 / σ
  let K := Real.exp (2 * a + c * a ^ 2)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσ2 : σ ^ 2 = 2 / Real.pi := Real.sq_sqrt (by positivity)
  have hσle : σ ≤ 1 := by
    have hg : 2 / Real.pi ≤ 1 := (div_le_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
    nlinarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hK : 0 < K := Real.exp_pos _
  refine ⟨P + K, c, add_pos hP hK, hc, ?_⟩
  intro b n hn u hu
  let D := latticeSquareInterior 0 (2 ^ n)
  let E := latticeSquareInterior b (2 ^ n)
  let H := Real.log ((2 : ℝ) ^ n)
  let m := 2 * H - (3 / 4 : ℝ) * Real.log H
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hH : 1 ≤ H := by
    dsimp [H]
    rw [Real.log_pow]
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [Real.log_two_gt_d9]
  have hHpos : 0 < H := by linarith
  have hcenter : bdzLiteratureCenter n = σ * m := by
    dsimp [bdzLiteratureCenter, σ, m, H]
    ring
  have hprob : (gaussianGreenLaw E E).real {φ | ∃ x : E, m + u ≤ φ x / σ} =
      (gaussianGreenLaw D D).real
        {φ | ∃ x : D, bdzLiteratureCenter n + σ * u ≤ φ x} := by
    have he (F : Finset Site) :
        {φ : EuclideanSpace ℝ F | ∃ x : F, m + u ≤ φ x / σ} =
          {φ | ∃ x : F, bdzLiteratureCenter n + σ * u ≤ φ x} := by
      ext φ
      have heq : (m + u) * σ = bdzLiteratureCenter n + σ * u := by
        rw [hcenter]
        ring
      simp only [Set.mem_setOf_eq, le_div_iff₀ hσ, heq]
    rw [he E]
    have ht := gaussian_green_maximum_translation b D (bdzLiteratureCenter n + σ * u)
    rw [show translateFinset b D = E by exact latticeSquareInterior_translate b (2 ^ n)] at ht
    exact ht
  change (gaussianGreenLaw E E).real {φ | ∃ x : E, m + u ≤ φ x / σ} ≤
    (P + K) * (1 + u) * Real.exp (-2 * u - c * u ^ 2 / H)
  by_cases hz : 1 ≤ σ * u
  · have ht := hsource n hn (σ * u) hz
    rw [bdz_literature_field_eq_green] at ht
    have hexp : Real.exp (-Real.sqrt (2 * Real.pi) * (σ * u)) *
        Real.exp (-C⁻¹ * (σ * u) ^ 2 / (n : ℝ)) =
          Real.exp (-2 * u - c * u ^ 2 / H) := by
      rw [← Real.exp_add]
      congr 1
      have hcoeff : Real.sqrt (2 * Real.pi) * σ = 2 := bdz_sqrt_normalization
      have hlog : H = (n : ℝ) * Real.log 2 := Real.log_pow _ _
      rw [show -Real.sqrt (2 * Real.pi) * (σ * u) = -2 * u by
        calc
          _ = -(Real.sqrt (2 * Real.pi) * σ) * u := by ring
          _ = _ := by rw [hcoeff]]
      rw [mul_pow, hσ2, hlog]
      dsimp [c]
      field_simp
      ring
    have hpref : P * (σ * u) ≤ (P + K) * (1 + u) := by
      have hu0 : 0 ≤ u := by linarith
      have hsu : σ * u ≤ u := (mul_le_mul_of_nonneg_right hσle hu0).trans_eq (one_mul u)
      nlinarith
    rw [hprob]
    have hmono : (gaussianGreenLaw D D).real
        {φ | ∃ x : D, bdzLiteratureCenter n + σ * u ≤ φ x} ≤
        (gaussianGreenLaw D D).real
          {φ | ∃ x : latticeSquare 0 (2 ^ n),
            bdzLiteratureCenter n + σ * u ≤ bdzLiteratureValue n φ x} := by
      apply measureReal_mono ?_ (measure_ne_top _ _)
      rintro φ ⟨x, hx⟩
      refine ⟨⟨x, latticeSquareInterior_subset 0 (2 ^ n) x.2⟩, ?_⟩
      have hxD : (x : Site) ∈ latticeSquareInterior 0 (2 ^ n) := x.2
      change bdzLiteratureCenter n + σ * u ≤ bdzLiteratureValue n φ (x : Site)
      rw [bdzLiteratureValue, dif_pos hxD]
      exact hx
    apply hmono.trans (ht.trans ?_)
    calc
      _ = P * (σ * u) *
          (Real.exp (-Real.sqrt (2 * Real.pi) * (σ * u)) *
            Real.exp (-C⁻¹ * (σ * u) ^ 2 / (n : ℝ))) := by ring
      _ = P * (σ * u) * Real.exp (-2 * u - c * u ^ 2 / H) := by rw [hexp]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _)
  · have hua : u ≤ a := by
      apply (le_div_iff₀ hσ).mpr
      nlinarith
    have hcompact := gaussian_compact_tail_envelope c a u H hc.le
      (by dsimp [a]; positivity) (by linarith) hua hH
    have hKP : K ≤ P + K := le_add_of_nonneg_left hP.le
    exact (measureReal_le_one (μ := gaussianGreenLaw E E)).trans
      (hcompact.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKP (by linarith)) (Real.exp_nonneg _)))

end SRWTightness
