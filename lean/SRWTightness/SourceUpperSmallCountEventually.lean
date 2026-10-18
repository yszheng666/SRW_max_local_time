import SRWTightness.SourceUpperSmallCountHeight
import SRWTightness.SourceUpperThresholdConditions
import SRWTightness.GaussianMarkThresholdNormalization

open Filter
open scoped Topology
namespace SRWTightness

/-- The small-count threshold estimate holds uniformly at all sufficiently large source scales. -/
theorem source_upper_small_count_eventually (hScale : ExponentialFloorScaleInput) :
    ∀ᶠ t : ℝ in atTop, ∀ s u : ℝ, 0 ≤ s → 0 ≤ u → u ≤ t - 1 →
      t / 10 ≤ Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ) / (2 / Real.pi)) -
        Real.sqrt (sourceUpperIntensity t / (2 / Real.pi)) * u := by
  obtain ⟨B, hB, hc⟩ := source_upper_threshold_conditions hScale
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 10))
  filter_upwards [hc, hl] with t ht hlog
  intro s u hs hu hsmall
  have hlog' : Real.log t ≤ t / 10 := by
    have hh := (div_lt_iff₀ ht.1).mp hlog
    linarith
  exact source_upper_small_count_height t s u ht.1 hs hlog' hu hsmall ht.2.2.1

/-- The raw positive Gaussian branch in the small-count range has quadratic exponential decay. -/
theorem source_upper_small_count_exponential (t s V d : ℝ) (k : ℕ)
    (ht : 0 < t) (hs : 0 ≤ s) (hlog : Real.log t ≤ t / 10)
    (hk : Real.sqrt (2 * (k : ℝ)) ≤ t - 1)
    (hsize : 5 * sourceUpperBuffer t ≤ sourceUpperRadius t)
    (hV : 0 < V) (hd : 0 < d) :
    Real.exp (-(Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) -
      Real.sqrt (2 * ((k : ℝ) * sourceUpperIntensity t))) ^ 2 / (2 * (V * d))) ≤
    Real.exp (-((2 / Real.pi) / (200 * V)) * t ^ 2 / d) := by
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  have hH : 0 ≤ sourceUpperBuffer t := by
    unfold sourceUpperBuffer upperTerminalFineRadius
    positivity
  have halpha := sourceReferenceIntensity_error (sourceUpperRadius t) (sourceUpperBuffer t)
    (Real.exp_pos _) hH hsize
  have hα : 0 ≤ sourceUpperIntensity t := by
    change 0 ≤ sourceReferenceIntensity (sourceUpperRadius t) (sourceUpperBuffer t)
    dsimp [g] at hg
    linarith [halpha.1]
  have hb := source_upper_small_count_height t s (Real.sqrt (2 * (k : ℝ)))
    ht hs hlog (Real.sqrt_nonneg _) hk hsize
  rw [← gaussian_mark_threshold_normalization k (sourceUpperVisitCutoff t s)
    (sourceUpperIntensity t) g hα] at hb
  have hraw := (le_div_iff₀ (Real.sqrt_pos.mpr hg)).mp hb
  have hbase : 0 ≤ t / 10 * Real.sqrt g := by positivity
  have hsq := mul_self_le_mul_self hbase hraw
  have hsqrt := Real.sq_sqrt hg.le
  have hheight : g * t ^ 2 / 100 ≤
      (Real.sqrt (2 * (sourceUpperVisitCutoff t s : ℝ)) -
        Real.sqrt (2 * ((k : ℝ) * sourceUpperIntensity t))) ^ 2 := by
    calc
      _ = (t / 10 * Real.sqrt g) * (t / 10 * Real.sqrt g) := by
        rw [show (t / 10 * Real.sqrt g) * (t / 10 * Real.sqrt g) =
          t ^ 2 / 100 * (Real.sqrt g) ^ 2 by ring, hsqrt]
        ring
      _ ≤ _ := by nlinarith only [hsq]
  apply Real.exp_le_exp.mpr
  have he := div_le_div_of_nonneg_right (neg_le_neg hheight)
    (show 0 ≤ 2 * (V * d) by positivity)
  calc
    _ ≤ -(g * t ^ 2 / 100) / (2 * (V * d)) := he
    _ = _ := by dsimp [g]; ring

end SRWTightness
