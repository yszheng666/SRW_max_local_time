import SRWTightness.SourceEarlyRootCap

open Filter
namespace SRWTightness

/-- Nonempty long segments are no more numerous than their short roots. -/
theorem nonempty_segments_length_le_flatten {α : Type*} (ss : List (List α))
    (hs : ∀ s ∈ ss, s ≠ []) : ss.length ≤ ss.flatten.length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have hp : 0 < s.length := List.length_pos_iff.mpr (hs s (by simp))
    have hi := ih (fun r hr ↦ hs r (by simp [hr]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- Sum the per-segment comparison error without losing its fine-record term. -/
theorem segment_error_sum {α : Type*} (ss : List (List α)) (η : α → ℝ) (δ ε : ℝ) :
    (ss.map (fun s ↦ δ + ε * (s.length : ℝ) + (s.map η).sum)).sum =
      δ * (ss.length : ℝ) + ε * (ss.flatten.length : ℝ) + (ss.flatten.map η).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatten_cons,
      List.length_append, List.map_append, List.sum_append, Nat.cast_add, Nat.cast_one, ih]
    ring

/-- Bound the coarse segment errors by the total number of short roots. -/
theorem segment_error_le_roots {α : Type*} (ss : List (List α)) (η : α → ℝ) (δ ε : ℝ)
    (hδ : 0 ≤ δ) (hs : ∀ s ∈ ss, s ≠ []) :
    (ss.map (fun s ↦ δ + ε * (s.length : ℝ) + (s.map η).sum)).sum ≤
      (δ + ε) * (ss.flatten.length : ℝ) + (ss.flatten.map η).sum := by
  rw [segment_error_sum]
  have hh : (ss.length : ℝ) ≤ ss.flatten.length :=
    Nat.cast_le.mpr (nonempty_segments_length_le_flatten ss hs)
  nlinarith [mul_le_mul_of_nonneg_left hh hδ]

/-- The source root cap gives the two-label coarse error in equation 8.5. Fine-error bounds
are local premises to be discharged using the source success population bounds. -/
theorem source_two_label_segment_error :
    ∀ᶠ t : ℝ in atTop, ∀ {α : Type} (ss₀ ss₁ : List (List α)) (η : α → ℝ)
      (ν : ℕ) (δ ε ηterm : ℝ), 0 ≤ δ → 0 ≤ ε →
      (∀ s ∈ ss₀, s ≠ []) → (∀ s ∈ ss₁, s ≠ []) →
      ss₀.flatten.length ≤ sourceEarlyRootCap t ν →
      ss₁.flatten.length ≤ sourceEarlyRootCap t ν →
      (ss₀.flatten.map η).sum ≤ ηterm → (ss₁.flatten.map η).sum ≤ ηterm →
      ((ss₀ ++ ss₁).map (fun s ↦ δ + ε * (s.length : ℝ) + (s.map η).sum)).sum ≤
        16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε) + 2 * ηterm := by
  filter_upwards [source_early_root_cap_quadratic] with t ht
  intro α ss₀ ss₁ η ν δ ε ηterm hδ hε hs₀ hs₁ hc₀ hc₁ he₀ he₁
  have hb₀ := segment_error_le_roots ss₀ η δ ε hδ hs₀
  have hb₁ := segment_error_le_roots ss₁ η δ ε hδ hs₁
  have hn₀ : (ss₀.flatten.length : ℝ) ≤ 8 * ((ν : ℝ) + 1) ^ 2 :=
    (Nat.cast_le.mpr hc₀).trans (ht ν)
  have hn₁ : (ss₁.flatten.length : ℝ) ≤ 8 * ((ν : ℝ) + 1) ^ 2 :=
    (Nat.cast_le.mpr hc₁).trans (ht ν)
  have hm₀ := mul_le_mul_of_nonneg_left hn₀ (add_nonneg hδ hε)
  have hm₁ := mul_le_mul_of_nonneg_left hn₁ (add_nonneg hδ hε)
  rw [List.map_append, List.sum_append]
  nlinarith

end SRWTightness
