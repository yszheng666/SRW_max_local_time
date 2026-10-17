import SRWTightness.SetOccupation

open MeasureTheory

namespace SRWTightness

noncomputable def setHittingTime (K : Finset Site) (x : Site) (start : ℕ) :
    Sample → WithTop ℕ := hittingAfter (fun n ω ↦ x + position ω n) (K : Set Site) start

 theorem localTime_pos_iff (ω : Sample) (n : ℕ) (y : Site) :
    0 < localTime ω n y ↔ ∃ i < n, position ω i = y := by
  simp [localTime, Finset.filter_nonempty_iff]

 theorem setOccupation_pos_iff (D K : Finset Site) (x : Site) (ω : Sample) :
    0 < setOccupation D K x ω ↔
      ∃ i < domainSteps D x ω, x + position ω i ∈ K := by
  simp only [setOccupation, Finset.sum_pos_iff, domainLocalTime, localTime_pos_iff]
  constructor
  · rintro ⟨y, hy, i, hi, he⟩
    refine ⟨i, hi, ?_⟩
    have hh : x + position ω i = y := by rw [he]; abel
    rwa [hh]
  · rintro ⟨i, hi, hm⟩
    refine ⟨x + position ω i, hm, i, hi, ?_⟩
    abel

 theorem setHittingTime_lt_exit_iff (D K : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) :
    setHittingTime K x 0 ω < domainExit D x ω ↔ 1 ≤ setOccupation D K x ω := by
  have hh := hittingAfter_lt_iff (u := fun n ω ↦ x + position ω n)
    (s := (K : Set Site)) (n := 0) (i := domainSteps D x ω) (ω := ω)
  change setHittingTime K x 0 ω < (domainSteps D x ω : WithTop ℕ) ↔
    ∃ j ∈ Set.Ico 0 (domainSteps D x ω), x + position ω j ∈ K at hh
  rw [coe_domainSteps D x ω hfin] at hh
  simpa only [Set.mem_Ico, Nat.zero_le, true_and, Finset.mem_coe,
    ← setOccupation_pos_iff, Nat.succ_le_iff] using hh


 theorem setHitProbability_eq_hitting (D K : Finset Site) (x : Site) :
    setHitProbability D K x = pathLaw.real {ω | setHittingTime K x 0 ω < domainExit D x ω} := by
  rw [setHitProbability_eq_probability]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [domainExit_ne_top_ae D x] with ω hω
  exact propext (setHittingTime_lt_exit_iff D K x ω hω).symm

 theorem position_domain_exit_not_mem (D : Finset Site) (x : Site) (ω : Sample)
    (hfin : domainExit D x ω ≠ ⊤) : x + position ω (domainSteps D x ω) ∉ D := by
  have he : domainExit D x ω ≤ (domainSteps D x ω : WithTop ℕ) :=
    (coe_domainSteps D x ω hfin).symm.le
  obtain ⟨k, hk, hout⟩ := (domainExit_le_iff D x ω _).mp he
  have hle : domainExit D x ω ≤ k := (domainExit_le_iff D x ω k).mpr ⟨k, le_rfl, hout⟩
  rw [← coe_domainSteps D x ω hfin] at hle
  have hge : domainSteps D x ω ≤ k := WithTop.coe_le_coe.mp hle
  have heq : k = domainSteps D x ω := Nat.le_antisymm hk hge
  simpa only [heq] using hout

 theorem setHittingTime_ne_exit (D K : Finset Site) (hKD : K ⊆ D) (x : Site)
    (start : ℕ) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    setHittingTime K x start ω ≠ domainExit D x ω := by
  intro heq
  have hle : setHittingTime K x start ω ≤ (domainSteps D x ω : WithTop ℕ) := by
    rw [heq, coe_domainSteps D x ω hfin]
  obtain ⟨k, hk, hmem⟩ := hittingAfter_le_iff.mp hle
  have he : domainExit D x ω ≤ k := by
    rw [← heq]
    exact hittingAfter_le_of_mem hk.1 hmem
  rw [← coe_domainSteps D x ω hfin] at he
  have hn : domainSteps D x ω ≤ k := WithTop.coe_le_coe.mp he
  have hke : k = domainSteps D x ω := Nat.le_antisymm hk.2 hn
  exact position_domain_exit_not_mem D x ω hfin (hKD (hke ▸ hmem))

 theorem exit_lt_setHittingTime_iff (D K : Finset Site) (hKD : K ⊆ D) (x : Site)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    domainExit D x ω < setHittingTime K x 0 ω ↔ setOccupation D K x ω = 0 := by
  have hne := setHittingTime_ne_exit D K hKD x 0 ω hfin
  have hh := setHittingTime_lt_exit_iff D K x ω hfin
  constructor
  · intro h
    have : ¬ 1 ≤ setOccupation D K x ω := fun hc ↦ (not_lt_of_ge h.le) (hh.mpr hc)
    omega
  · intro h
    apply lt_of_le_of_ne
    · apply le_of_not_gt
      intro hc
      have := hh.mp hc
      omega
    · exact hne.symm

end SRWTightness
