import SRWTightness.GeneratingNeighborhood
import SRWTightness.OccupationSum
import SRWTightness.FiniteKilledWalkMomentInput
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open MeasureTheory
namespace SRWTightness

/-- The actual finite-domain exit duration has a nontrivial integrable geometric moment. -/
theorem exists_integrable_domain_steps_pow (D : Finset Site) (x : Site) :
    ∃ b : ℝ, 1 < b ∧ Integrable (fun ω ↦ b ^ domainSteps D x ω) pathLaw := by
  obtain ⟨b, hb, hqb⟩ := exists_generating_radius D D (fun _ h ↦ h)
  refine ⟨b, hb, ?_⟩
  have hb0 : 0 ≤ b := le_trans zero_le_one hb.le
  have hi := integrable_killedMonomial D D (fun _ ↦ b) b (fun _ ↦ hb0)
    (fun _ ↦ le_rfl) hb0 hqb x
  have hsum (ω : Sample) : (∑ y : D, domainLocalTime D x y ω) = domainSteps D x ω :=
    (Finset.sum_coe_sort D (fun y ↦ domainLocalTime D x y ω)).trans
      (domainLocalTime_sum D x ω)
  simpa only [markMonomial, killedMark, Finset.prod_pow_eq_pow_sum, hsum] using hi

/-- Every square-root exponential is bounded by a constant times a larger-than-one power. -/
theorem sqrt_exp_le_geometric (b c : ℝ) (hb : 1 < b) (n : ℕ) :
    Real.exp (c * Real.sqrt ((n : ℝ) + 1)) ≤
      Real.exp (Real.log b + c ^ 2 / (4 * Real.log b)) * b ^ n := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have ha : 0 < Real.log b := Real.log_pos hb
  have h4 : 0 < 4 * Real.log b := by positivity
  have hu : 0 ≤ (n : ℝ) + 1 := by positivity
  have hs : (2 * Real.log b * Real.sqrt ((n : ℝ) + 1)) ^ 2 =
      4 * (Real.log b) ^ 2 * ((n : ℝ) + 1) := by
    rw [mul_pow, Real.sq_sqrt hu]
    ring
  have hm : (c * Real.sqrt ((n : ℝ) + 1) - Real.log b * ((n : ℝ) + 1)) *
      (4 * Real.log b) ≤ c ^ 2 := by
    nlinarith only [sq_nonneg (2 * Real.log b * Real.sqrt ((n : ℝ) + 1) - c), hs]
  have hd := (le_div_iff₀ h4).mpr hm
  have hbound : c * Real.sqrt ((n : ℝ) + 1) ≤
      Real.log b * ((n : ℝ) + 1) + c ^ 2 / (4 * Real.log b) := by linarith
  calc
    _ ≤ Real.exp (Real.log b * ((n : ℝ) + 1) + c ^ 2 / (4 * Real.log b)) :=
      Real.exp_le_exp.mpr hbound
    _ = _ := by
      rw [show Real.log b * ((n : ℝ) + 1) + c ^ 2 / (4 * Real.log b) =
        (Real.log b + c ^ 2 / (4 * Real.log b)) + (n : ℝ) * Real.log b by ring,
        Real.exp_add, Real.exp_nat_mul, Real.exp_log hb0]

/-- Every square-root exponential of the actual finite-domain exit duration is integrable. -/
theorem integrable_exp_sqrt_domain_steps (D : Finset Site) (x : Site) (c : ℝ) :
    Integrable (fun ω ↦ Real.exp (c * Real.sqrt ((domainSteps D x ω : ℝ) + 1))) pathLaw := by
  obtain ⟨b, hb, hi⟩ := exists_integrable_domain_steps_pow D x
  have hm : Measurable (fun ω ↦ Real.exp (c * Real.sqrt ((domainSteps D x ω : ℝ) + 1))) :=
    (measurable_of_countable (fun n : ℕ ↦ Real.exp (c * Real.sqrt ((n : ℝ) + 1)))).comp
      (measurable_domainSteps D x)
  apply (hi.const_mul (Real.exp (Real.log b + c ^ 2 / (4 * Real.log b)))).mono_nonneg
    hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω ↦ (Real.exp_pos _).le)
  · exact Filter.Eventually.of_forall (fun ω ↦ sqrt_exp_le_geometric b c hb _)

end SRWTightness
