import SRWTightness.DiskFiniteDomain
import SRWTightness.DomainFirstStep

open MeasureTheory

namespace SRWTightness

noncomputable def domainExitLocation (D : Finset Site) (x : Site) (ω : Sample) : Site :=
  x + position ω (domainSteps D x ω)

 theorem measurable_domainExitLocation (D : Finset Site) (x : Site) :
    Measurable (domainExitLocation D x) := by
  have hm : Measurable (fun p : Sample × ℕ ↦ position p.1 p.2) :=
    measurable_from_prod_countable_left (fun n ↦ measurable_position n)
  exact (measurable_of_countable (fun z : Site ↦ x + z)).comp
    (hm.comp (measurable_id.prodMk (measurable_domainSteps D x)))

noncomputable def domainExitRange (D : Finset Site) (x : Site) : Finset Site :=
  insert x (D.biUnion (fun y ↦ Finset.univ.image (fun d : Direction ↦ y + step d)))

 theorem domainExitLocation_mem_range (D : Finset Site) (x : Site) (ω : Sample) :
    domainExitLocation D x ω ∈ domainExitRange D x := by
  classical
  cases hn : domainSteps D x ω with
  | zero => simp [domainExitLocation, hn, domainExitRange]
  | succ n =>
    have hf : domainExit D x ω ≠ ⊤ := by
      intro h
      have hz : domainSteps D x ω = 0 := by simp [domainSteps, h]
      omega
    have hmem : x + position ω n ∈ D := by
      by_contra hout
      have he := (domainExit_le_iff D x ω n).mpr ⟨n, le_rfl, hout⟩
      rw [← coe_domainSteps D x ω hf] at he
      have hle : domainSteps D x ω ≤ n := WithTop.coe_le_coe.mp he
      omega
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨x + position ω n, hmem, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨ω n, Finset.mem_univ _, ?_⟩
    simp [domainExitLocation, hn, position, add_assoc]

 theorem integrable_domainExit_payoff (D : Finset Site) (x : Site) (f : Site → ℝ) :
    Integrable (fun ω ↦ f (domainExitLocation D x ω)) pathLaw := by
  refine ⟨((measurable_of_countable f).comp (measurable_domainExitLocation D x)).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := ∑ z ∈ domainExitRange D x, |f z|) ?_⟩
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun z _ ↦ abs_nonneg (f z)) (domainExitLocation_mem_range D x ω)

end SRWTightness
