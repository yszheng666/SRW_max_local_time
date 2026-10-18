import SRWTightness.CenteredLatticeBlock
import SRWTightness.SourceUpperBlockScales
import SRWTightness.TranslatedDiskGeometry

open Filter

namespace SRWTightness

/-- Block membership bounds the change in distance to the origin by one side length. -/
theorem centeredLatticeBlock_radius_bounds (a : ℕ) (b x : Site)
    (hx : x ∈ centeredLatticeBlock a b) :
    Real.sqrt (normSq x) ≤ Real.sqrt (normSq b) + a ∧
      Real.sqrt (normSq b) ≤ Real.sqrt (normSq x) + a := by
  have bound (u v : Site) (h : normSq (u - v) ≤ (a : ℝ) ^ 2) :
      Real.sqrt (normSq u) ≤ Real.sqrt (normSq v) + a := by
    have hh := normSq_add_bound (u - v) v (Nat.cast_nonneg a) (Real.sqrt_nonneg _) h
      (le_of_eq (normSq_eq_sq_sqrt v))
    rw [sub_add_cancel] at hh
    have hs := Real.sqrt_le_sqrt hh
    rw [Real.sqrt_sq (by positivity)] at hs
    linarith
  have hn := centeredLatticeBlock_near a b x hx
  exact ⟨bound x b hn, bound b x (by
    rw [show b - x = -(x - b) by abel, normSq_neg]
    exact hn)⟩

/-- The actual upper block of the manuscript's exact integer side length. -/
noncomputable def sourceUpperBlock (t : ℝ) (b : Site) : Finset Site :=
  centeredLatticeBlock (sourceUpperBlockSide t) b

/-- Actual grid centers of blocks meeting R/t<|x|<=R/2, with a finite ambient disk. -/
noncomputable def sourceUpperBlockCenters (t : ℝ) : Finset Site := by
  classical
  exact (diskFinset (Real.exp t)).filter (fun b ↦
    (sourceUpperBlockSide t : ℤ) ∣ b.1 ∧ (sourceUpperBlockSide t : ℤ) ∣ b.2 ∧
      ∃ x ∈ sourceUpperBlock t b,
        Real.exp t / t < Real.sqrt (normSq x) ∧ Real.sqrt (normSq x) ≤ Real.exp t / 2)

/-- The actual half-open blocks cover the full source annulus, including its outer boundary. -/
theorem source_upper_block_cover :
    ∀ᶠ t : ℝ in atTop, ∀ x : Site,
      Real.exp t / t < Real.sqrt (normSq x) → Real.sqrt (normSq x) ≤ Real.exp t / 2 →
        ∃ b ∈ sourceUpperBlockCenters t, x ∈ sourceUpperBlock t b := by
  filter_upwards [source_upper_block_scale_conditions] with t ht
  intro x hxlo hxhi
  let a := sourceUpperBlockSide t
  let b := latticeBlockCenter a x
  have hx : x ∈ sourceUpperBlock t b := mem_centeredLatticeBlock_center a
    (sourceUpperBlockSide_pos t) x
  have hnear := (centeredLatticeBlock_radius_bounds a b x hx).2
  have hb : b ∈ diskFinset (Real.exp t) := by
    apply (mem_diskFinset _ _).mpr
    change normSq b < (Real.exp t) ^ 2
    have h : Real.sqrt (normSq b) < Real.exp t := by
      have ha := ht.2.2.2
      change (a : ℝ) ≤ Real.exp t / 4 at ha
      linarith [Real.exp_pos t]
    have he := Real.sq_sqrt (normSq_nonneg b)
    nlinarith [Real.sqrt_nonneg (normSq b), Real.exp_pos t]
  obtain ⟨h₁, h₂⟩ := latticeBlockCenter_divisible a x
  exact ⟨b, Finset.mem_filter.mpr ⟨hb, h₁, h₂, x, hx, hxlo, hxhi⟩, hx⟩

/-- Every selected center stays beyond R/(2t), so its root entrance ball can exclude the origin. -/
theorem source_upper_block_center_distance :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      Real.exp t / (2 * t) ≤ Real.sqrt (normSq b) ∧
        Real.sqrt (normSq b) ≤ 3 * Real.exp t / 4 := by
  filter_upwards [source_upper_block_scale_conditions] with t ht
  intro b hb
  obtain ⟨_, _, _, x, hx, hxlo, hxhi⟩ := Finset.mem_filter.mp hb
  have ht0 : 0 < t := by linarith [ht.1]
  have hn := centeredLatticeBlock_radius_bounds (sourceUpperBlockSide t) b x hx
  have hside : (sourceUpperBlockSide t : ℝ) ≤ sourceUpperBuffer t := by
    rw [sourceUpperBlockSide_cast]
    unfold sourceUpperBuffer
    have h : 0 ≤ upperTerminalFineRadius (sourceUpperLogRadius t) := by
      unfold upperTerminalFineRadius
      positivity
    linarith
  have hsmall := (mul_le_mul_of_nonneg_left hside ht0.le).trans ht.2.2.1
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < 2 * t)).mpr
    have hlo := (div_lt_iff₀ ht0).mp hxlo
    have hmul := mul_le_mul_of_nonneg_left hn.1 ht0.le
    nlinarith [Real.exp_pos t]
  · linarith [hn.2, ht.2.2.2]

end SRWTightness
