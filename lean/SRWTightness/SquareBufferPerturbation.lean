import SRWTightness.ExternalBufferedSquareGreen
import SRWTightness.CoordinateBounds

namespace SRWTightness

/-- A controlled displacement uses only the corresponding amount of coordinate buffer. -/
theorem square_buffer_displacement (δ ε r : ℝ) (a x z : Site) (N : ℕ)
    (hr : 0 ≤ r) (hb : squareProportionalBuffer δ a N x)
    (hz : normSq (z - x) ≤ r ^ 2) (hroom : r ≤ (δ - ε) * (N : ℝ)) :
    squareProportionalBuffer ε a N z := by
  have hf := abs_le.mp (abs_fst_le_normSq_bound (z - x) hr hz)
  have hs := abs_le.mp (abs_snd_le_normSq_bound (z - x) hr hz)
  simp only [Prod.fst_sub, Prod.snd_sub, Int.cast_sub] at hf hs
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  unfold squareProportionalBuffer
  constructor
  · nlinarith [hf.1]
  constructor
  · nlinarith [hf.2]
  constructor
  · nlinarith [hs.1]
  · nlinarith [hs.2]

/-- At least one lattice unit of proportional buffer puts a site in the killed square interior. -/
theorem square_buffer_mem_interior (δ : ℝ) (a x : Site) (N : ℕ)
    (hunit : 1 ≤ δ * (N : ℝ)) (hb : squareProportionalBuffer δ a N x) :
    x ∈ latticeSquareInterior a N := by
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  rw [mem_latticeSquareInterior]
  constructor
  · constructor
    · exact_mod_cast (show (a.1 : ℝ) + 1 ≤ x.1 by linarith)
    · exact_mod_cast (show (x.1 : ℝ) ≤ a.1 + N - 2 by linarith)
  · constructor
    · exact_mod_cast (show (a.2 : ℝ) + 1 ≤ x.2 by linarith)
    · exact_mod_cast (show (x.2 : ℝ) ≤ a.2 + N - 2 by linarith)

end SRWTightness
