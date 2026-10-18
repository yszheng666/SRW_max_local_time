import SRWTightness.DiskObservable

open MeasureTheory

namespace SRWTightness

noncomputable def domainRadius (D : Finset Site) (x : Site) : ℝ :=
  (∑ z ∈ D, (normSq (z - x) + 1)) + 1

 theorem domainRadius_pos (D : Finset Site) (x : Site) : 0 < domainRadius D x := by
  have h : 0 ≤ ∑ z ∈ D, (normSq (z - x) + 1) :=
    Finset.sum_nonneg (fun z _ ↦ by linarith [normSq_nonneg (z - x)])
  unfold domainRadius
  linarith

 theorem normSq_sub_lt_domainRadius (D : Finset Site) (x z : Site) (hz : z ∈ D) :
    normSq (z - x) < (domainRadius D x) ^ 2 := by
  have h := Finset.single_le_sum (fun y (_ : y ∈ D) ↦
    (show 0 ≤ normSq (y - x) + 1 by linarith [normSq_nonneg (y - x)])) hz
  have hp := domainRadius_pos D x
  dsimp [domainRadius] at hp ⊢
  nlinarith [normSq_nonneg (z - x)]

/-- The original walk started at x and killed on first leaving the finite domain D. -/
noncomputable def domainExit (D : Finset Site) (x : Site) : Sample → WithTop ℕ :=
  hittingAfter (fun n ω ↦ x + position ω n) (D : Set Site)ᶜ 0

 theorem domainExit_isStoppingTime (D : Finset Site) (x : Site) :
    IsStoppingTime history (domainExit D x) := by
  have ha : Adapted history (fun n ω ↦ x + position ω n) := by
    intro n
    exact (measurable_of_countable (fun z : Site ↦ x + z)).comp (adapted_position n)
  exact ha.isStoppingTime_hittingAfter (Set.to_countable _).measurableSet

 theorem domainExit_le_iff (D : Finset Site) (x : Site) (ω : Sample) (n : ℕ) :
    domainExit D x ω ≤ n ↔ ∃ k ≤ n, x + position ω k ∉ D := by
  simpa [domainExit] using
    (hittingAfter_le_iff (u := fun k ω ↦ x + position ω k) (s := (D : Set Site)ᶜ)
      (n := 0) (i := n) (ω := ω))

 theorem domainExit_le_disk (D : Finset Site) (x : Site) (ω : Sample) :
    domainExit D x ω ≤ exitTime (domainRadius D x) ω := by
  by_cases ht : exitTime (domainRadius D x) ω = ⊤
  · rw [ht]
    exact le_top
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ht
    rw [← hn]
    apply (domainExit_le_iff D x ω n).mpr
    refine ⟨n, le_rfl, ?_⟩
    intro hmem
    have hb := normSq_sub_lt_domainRadius D x (x + position ω n) hmem
    have he := normSq_at_exit_ge (domainRadius D x) ω n hn.symm
    have hid : x + position ω n - x = position ω n := by simp
    rw [hid] at hb
    exact (not_lt_of_ge he) hb

 theorem domainExit_ne_top_ae (D : Finset Site) (x : Site) :
    ∀ᵐ ω ∂pathLaw, domainExit D x ω ≠ ⊤ := by
  filter_upwards [exitTime_ne_top_ae (domainRadius_pos D x).le] with ω hω
  exact ne_top_of_le_ne_top hω (domainExit_le_disk D x ω)

noncomputable def domainSteps (D : Finset Site) (x : Site) (ω : Sample) : ℕ :=
  (domainExit D x ω).untopD 0

 theorem measurable_domainSteps (D : Finset Site) (x : Site) : Measurable (domainSteps D x) :=
  (domainExit_isStoppingTime D x).measurable'.untopD 0

 theorem coe_domainSteps (D : Finset Site) (x : Site) (ω : Sample)
    (h : domainExit D x ω ≠ ⊤) : (domainSteps D x ω : WithTop ℕ) = domainExit D x ω := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h
  unfold domainSteps
  rw [← hn]
  rfl

 theorem integrable_domainSteps (D : Finset Site) (x : Site) :
    Integrable (fun ω ↦ (domainSteps D x ω : ℝ)) pathLaw := by
  apply (integrable_exitSteps (domainRadius_pos D x).le).mono_nonneg
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_domainSteps D x)).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun ω ↦ Nat.cast_nonneg _)
  · filter_upwards [domainExit_ne_top_ae D x,
      exitTime_ne_top_ae (domainRadius_pos D x).le] with ω hd he
    have hn : domainSteps D x ω ≤ exitSteps (domainRadius D x) ω := by
      suffices hh : (domainSteps D x ω : WithTop ℕ) ≤ exitSteps (domainRadius D x) ω by
        exact WithTop.coe_le_coe.mp hh
      rw [coe_domainSteps D x ω hd, coe_exitSteps _ ω he]
      exact domainExit_le_disk D x ω
    exact Nat.cast_le.mpr hn

end SRWTightness
