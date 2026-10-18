import SRWTightness.SourceUpperNearOriginLogSum
import SRWTightness.SourceUpperOnePointBound

open Filter MeasureTheory

namespace SRWTightness

/-- The actual near-origin lattice sites, retaining the boundary at radius exp(t)/t. -/
noncomputable def sourceUpperNearOriginSites (t : ℝ) : Finset Site :=
  (diskFinset (Real.exp t)).filter (fun x ↦ Real.sqrt (normSq x) ≤ Real.exp t / t)

/-- A high local-time point in the near-origin region of the killed walk. -/
def sourceUpperNearOriginHighEvent (t s : ℝ) : Set Sample :=
  {ω | ∃ x ∈ sourceUpperNearOriginSites t, sourceUpperVisitCutoff t s ≤
    domainLocalTime (diskFinset (Real.exp t)) 0 x ω}

/-- The near-origin event has the source height factor and an explicit vanishing spatial factor. -/
theorem source_upper_near_origin_probability :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s →
      pathLaw.real (sourceUpperNearOriginHighEvent t s) ≤
        C * Real.exp (-(2 * Real.sqrt Real.pi * s)) *
          ((1 + 2 * Real.log t) / t + (1 + t) / t ^ 3) := by
  classical
  obtain ⟨K, hK, hp⟩ := source_upper_one_point_bound
  refine ⟨101 * K, by positivity, ?_⟩
  filter_upwards [hp, eventually_ge_atTop (2 : ℝ),
    (Real.tendsto_exp_div_pow_atTop 2).eventually (eventually_ge_atTop 1)] with t hp ht hr
  intro s hs
  have ht0 : 0 < t := by linarith
  have hsites (x : Site) (hx : x ∈ sourceUpperNearOriginSites t) :
      Real.sqrt (normSq x) ≤ Real.exp t / t := (Finset.mem_filter.mp hx).2
  have hhalf (x : Site) (hx : x ∈ sourceUpperNearOriginSites t) :
      normSq x ≤ (Real.exp t / 2) ^ 2 := by
    have hn := (hsites x hx).trans
      (div_le_div_of_nonneg_left (Real.exp_nonneg _) (by norm_num) ht)
    nlinarith [Real.sq_sqrt (normSq_nonneg x), Real.sqrt_nonneg (normSq x), Real.exp_pos t]
  have hevent : sourceUpperNearOriginHighEvent t s =
      ⋃ x ∈ sourceUpperNearOriginSites t,
        {ω | sourceUpperVisitCutoff t s ≤ domainLocalTime (diskFinset (Real.exp t)) 0 x ω} := by
    ext ω
    simp only [sourceUpperNearOriginHighEvent, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  let A := K * t * Real.exp (-2 * t) * Real.exp (-(2 * Real.sqrt Real.pi * s))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [hevent]
  calc
    _ ≤ ∑ x ∈ sourceUpperNearOriginSites t,
        pathLaw.real {ω | sourceUpperVisitCutoff t s ≤
          domainLocalTime (diskFinset (Real.exp t)) 0 x ω} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ sourceUpperNearOriginSites t,
        A * (1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1)) :=
      Finset.sum_le_sum (fun x hx ↦ hp s hs x (hhalf x hx))
    _ = A * ∑ x ∈ sourceUpperNearOriginSites t,
        (1 + Real.log (Real.exp t / max (Real.sqrt (normSq x)) 1)) := by rw [Finset.mul_sum]
    _ ≤ A * (101 * (Real.exp t / t) ^ 2 * (1 + 2 * Real.log t) +
        101 * (Real.exp t / t ^ 2) ^ 2 * (1 + t)) :=
      mul_le_mul_of_nonneg_left (source_upper_near_origin_log_sum t ht hr _ hsites) hA
    _ = _ := by
      have he : Real.exp (-2 * t) = ((Real.exp t) ^ 2)⁻¹ := by
        rw [show -2 * t = -(t + t) by ring, Real.exp_neg, Real.exp_add, pow_two]
      dsimp [A]
      rw [he]
      field_simp
      <;> ring

end SRWTightness
