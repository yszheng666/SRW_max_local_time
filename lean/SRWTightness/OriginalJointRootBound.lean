import SRWTightness.CountableWeightedEventReal

open MeasureTheory
namespace SRWTightness

/-- Upper record and lower count comparisons eliminate the common reference mass. -/
theorem conditional_reference_elimination (a b d q w E F : ℝ) (hd : 0 < d) (hw : 0 ≤ w)
    (ha : a / d ≤ Real.exp E * (q * w))
    (hb : q ≤ Real.exp F * (b / d)) :
    a ≤ Real.exp (E + F) * (w * b) := by
  have hh : a / d ≤ (Real.exp (E + F) * (w * b)) / d := by
    calc
      a / d ≤ Real.exp E * (q * w) := ha
      _ ≤ Real.exp E * ((Real.exp F * (b / d)) * w) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb hw) (Real.exp_pos _).le
      _ = _ := by rw [Real.exp_add]; ring
  exact (div_le_div_iff_of_pos_right hd).mp hh

/-- Exterior-fiber comparisons yield the original joint-root expectation, without independence
of the two root counts and including zero-probability exterior atoms. -/
theorem original_joint_root_bound {Ω H : Type*} [MeasurableSpace Ω]
    [MeasurableSpace H] [MeasurableSingletonClass H] [Countable H]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → H) (X Y : Ω → ℕ) (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (A : Set Ω) (G : Set H) (N : ℕ) (p q : ℕ → ℝ)
    (hp : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1) (hq : ∀ k, q k ∈ Set.Icc (0 : ℝ) 1)
    (Q : H → ℕ → ℕ → ℝ) (E F : ℝ)
    (hupper : ∀ h, 0 < μ.real {ω | Z ω = h} → ∀ k l : ℕ, k ≤ N → l ≤ N →
      (μ.restrict A).real {ω | Z ω = h ∧ X ω = k ∧ Y ω = l} / μ.real {ω | Z ω = h} ≤
        Real.exp E * (Q h k l * (p k * q l)))
    (hlower : ∀ h, 0 < μ.real {ω | Z ω = h} → ∀ k l : ℕ, k ≤ N → l ≤ N →
      Q h k l ≤ Real.exp F *
        (μ.real {ω | Z ω = h ∧ X ω = k ∧ Y ω = l} / μ.real {ω | Z ω = h})) :
    μ.real {ω | ω ∈ A ∧ Z ω ∈ G ∧ X ω ≤ N ∧ Y ω ≤ N} ≤
      Real.exp (E + F) * ∫ ω,
        {v : Ω | Z v ∈ G ∧ X v ≤ N ∧ Y v ≤ N}.indicator
          (fun v ↦ p (X v) * q (Y v)) ω ∂μ := by
  classical
  let f : Ω → H × ℕ × ℕ := fun ω ↦ (Z ω, X ω, Y ω)
  have hf : Measurable f := hZ.prodMk (hX.prodMk hY)
  let s : Set (H × ℕ × ℕ) := {r | r.1 ∈ G ∧ r.2.1 ≤ N ∧ r.2.2 ≤ N}
  let w : H × ℕ × ℕ → ℝ := fun r ↦ p r.2.1 * q r.2.2
  have hw (r : H × ℕ × ℕ) : w r ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (hp _).1 (hq _).1, ?_⟩
    exact (mul_le_mul (hp _).2 (hq _).2 (hq _).1 (by norm_num)).trans_eq (by norm_num)
  have hb := countable_weighted_event_real μ (μ.restrict A) f hf w hw s
    (Real.exp (E + F)) (Real.exp_pos _).le (fun r hr ↦ ?_)
  · have hfun : (fun ω ↦ s.indicator w (f ω)) =
        (fun ω ↦ {v : Ω | Z v ∈ G ∧ X v ≤ N ∧ Y v ≤ N}.indicator
          (fun v ↦ p (X v) * q (Y v)) ω) := by
      funext ω
      by_cases hc : Z ω ∈ G ∧ X ω ≤ N ∧ Y ω ≤ N <;> simp [s, w, f, hc]
    have hevent : f ⁻¹' s ∩ A = {ω | ω ∈ A ∧ Z ω ∈ G ∧ X ω ≤ N ∧ Y ω ≤ N} := by
      ext ω
      simp [f, s, and_assoc, and_left_comm, and_comm]
    rwa [hfun, measureReal_restrict_apply (hf s.to_countable.measurableSet), hevent] at hb
  · have hmap : f ⁻¹' {r} = {ω | Z ω = r.1 ∧ X ω = r.2.1 ∧ Y ω = r.2.2} := by
      ext ω
      simp [f, Prod.ext_iff]
    by_cases hd : 0 < μ.real {ω | Z ω = r.1}
    · rw [hmap]
      exact conditional_reference_elimination _ _ _ _ _ E F hd (hw r).1
        (hupper r.1 hd r.2.1 r.2.2 hr.2.1 hr.2.2)
        (hlower r.1 hd r.2.1 r.2.2 hr.2.1 hr.2.2)
    · have hd0 : μ.real {ω | Z ω = r.1} = 0 :=
        le_antisymm (le_of_not_gt hd) measureReal_nonneg
      have hzero : (μ.restrict A).real (f ⁻¹' {r}) = 0 := by
        rw [measureReal_restrict_apply (hf (measurableSet_singleton r))]
        apply measureReal_mono_null _ hd0
        intro ω hω
        have he : f ω = r := hω.1
        exact congrArg Prod.fst he
      rw [hzero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw r).1 measureReal_nonneg)

end SRWTightness
