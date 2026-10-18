import SRWTightness.LatticeSquare
import SRWTightness.NormalizedHarmonicReconstruction

namespace SRWTightness

/-- A coordinate buffer from each fixed-zero boundary of a lattice square. -/
def squareProportionalBuffer (δ : ℝ) (a : Site) (N : ℕ) (x : Site) : Prop :=
  δ * (N : ℝ) ≤ (x.1 : ℝ) - (a.1 : ℝ) ∧
  (x.1 : ℝ) - (a.1 : ℝ) ≤ (N : ℝ) - 1 - δ * (N : ℝ) ∧
  δ * (N : ℝ) ≤ (x.2 : ℝ) - (a.2 : ℝ) ∧
  (x.2 : ℝ) - (a.2 : ℝ) ≤ (N : ℝ) - 1 - δ * (N : ℝ)

/-- Explicit standard buffered-square Green estimates, including normalization and translation.
This is a packaged potential-theoretic input, not a proved citation reduction. -/
def BufferedSquareGreenInput : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
    ∃ C₀ L B : ℝ, 0 ≤ C₀ ∧ 0 < L ∧ 0 ≤ B ∧
      ∀ (D E : Finset Site) (a b : Site) (m n : ℕ),
        D = latticeSquareInterior b (2 ^ m) → E = latticeSquareInterior a (2 ^ n) →
        2 ≤ n → n ≤ m → E ⊆ D → ∀ x y : E,
        squareProportionalBuffer δ a (2 ^ n) x →
        squareProportionalBuffer δ a (2 ^ n) y →
        squareProportionalBuffer δ b (2 ^ m) x →
        squareProportionalBuffer δ b (2 ^ m) y →
        let S := normalizedHarmonicCov D E (Real.sqrt (2 / Real.pi))
        |S x x - S y y| ≤ C₀ ∧
        S x x + S y y - 2 * S x y ≤
          L * normSq ((x : Site) - (y : Site)) / ((2 : ℝ) ^ n) ^ 2 ∧
        |S x x - (Real.log ((2 : ℝ) ^ m) - Real.log ((2 : ℝ) ^ n))| ≤ B

end SRWTightness
