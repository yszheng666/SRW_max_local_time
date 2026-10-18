import SRWTightness.EntranceEquilibriumSum
import SRWTightness.PuncturedGreenRelative

namespace SRWTightness

/-- Relative punctured Green control at incoming neighbors transfers to actual entrance atoms. -/
theorem entrance_atom_relative_comparison (D K : Finset Site) (hKD : K ⊆ D)
    (x v : Site) (hx : x ∉ K) (hv : v ∈ K)
    (hnear : ∀ d : Direction, v + step d ∈ D) (α δ : ℝ)
    (hgreen : ∀ y ∈ D \ K, (∃ d : Direction, y + step d = v) →
      |killedGreen (D \ K) x y - α * (1 - setHitProbability D K y)| ≤
        δ * (1 - setHitProbability D K y)) :
    |(competingEntranceLaw D K x).real {v} - α * equilibriumMeasure D K v| ≤
      δ * equilibriumMeasure D K v := by
  classical
  let w : Site → ℝ := fun y ↦ (1 / 4 : ℝ) *
    ∑ d : Direction, if y + step d = v then 1 else 0
  have hw (y : Site) : 0 ≤ w y := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> norm_num)
  have he : (∑ y ∈ D \ K, (1 - setHitProbability D K y) * w y) =
      equilibriumMeasure D K v := equilibrium_last_step_sum D K hKD v hv hnear
  have hb (y : Site) (hy : y ∈ D \ K) :
      |killedGreen (D \ K) x y * w y - α * ((1 - setHitProbability D K y) * w y)| ≤
        δ * ((1 - setHitProbability D K y) * w y) := by
    by_cases hn : ∃ d : Direction, y + step d = v
    · have hh := mul_le_mul_of_nonneg_right (hgreen y hy hn) (hw y)
      rw [show killedGreen (D \ K) x y * w y - α * ((1 - setHitProbability D K y) * w y) =
        (killedGreen (D \ K) x y - α * (1 - setHitProbability D K y)) * w y by ring,
        abs_mul, abs_of_nonneg (hw y)]
      simpa only [mul_assoc] using hh
    · have hz : w y = 0 := by
        have hh (d : Direction) : y + step d ≠ v := fun h ↦ hn ⟨d, h⟩
        simp [w, hh]
      simp [hz]
  rw [competingEntranceLaw_atom_green D K x v hx hv, ← he]
  change |(∑ y ∈ D \ K, killedGreen (D \ K) x y * w y) -
      α * ∑ y ∈ D \ K, (1 - setHitProbability D K y) * w y| ≤ _
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ y ∈ D \ K,
        |killedGreen (D \ K) x y * w y - α * ((1 - setHitProbability D K y) * w y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ D \ K, δ * ((1 - setHitProbability D K y) * w y) :=
      Finset.sum_le_sum hb
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Actual boundary Green control gives the entrance atom comparison through a local punctured domain. -/
theorem entrance_atom_comparison_from_boundary (D K A : Finset Site) (hKD : K ⊆ D)
    (hA : A ⊆ D \ K) (x v : Site) (hx : x ∈ D \ K) (hxA : x ∉ A)
    (hv : v ∈ K) (hnear : ∀ d : Direction, v + step d ∈ D)
    (hlocal : ∀ y ∈ D \ K, (∃ d : Direction, y + step d = v) → y ∈ A)
    (α δ : ℝ) (hb : ∀ y ∈ domainExitBoundary A,
      |killedGreen (D \ K) y x - α * (1 - setHitProbability D K y)| ≤
        δ * (1 - setHitProbability D K y)) :
    |(competingEntranceLaw D K x).real {v} - α * equilibriumMeasure D K v| ≤
      δ * equilibriumMeasure D K v := by
  apply entrance_atom_relative_comparison D K hKD x v (Finset.mem_sdiff.mp hx).2 hv hnear α δ
  intro y hy hn
  rw [killedGreen_symm (D \ K) x y hx hy]
  exact punctured_green_relative_error D K A hA x hxA α δ hb y (hlocal y hy hn)

end SRWTightness
