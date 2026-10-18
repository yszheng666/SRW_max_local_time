import SRWTightness.ExternalBufferedSquareGreen
import SRWTightness.DiskFiniteDomain

namespace SRWTightness

/-- Elementary dyadic enclosure geometry, retained as an explicit foundation input.
It contains no Green covariance or probability estimates. -/
def BufferedDyadicInteriorDiskEmbeddingInput : Prop :=
  ∀ (δ R r : ℝ) (A : Finset Site), 0 < δ → δ < 1 →
    1 ≤ r → 32 * r ≤ δ * R → A.Nonempty →
    (∀ x ∈ A, normSq x ≤ ((1 - δ) * R) ^ 2) →
    (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ r ^ 2) →
    ∃ (a b : Site) (m n : ℕ), 2 ≤ n ∧ n ≤ m ∧
      A ⊆ latticeSquareInterior a (2 ^ n) ∧
      latticeSquareInterior a (2 ^ n) ⊆ diskFinset R ∧
      diskFinset R ⊆ latticeSquareInterior b (2 ^ m) ∧
      r ≤ (2 : ℝ) ^ n ∧ (2 : ℝ) ^ n ≤ 64 * r ∧
      R ≤ (2 : ℝ) ^ m ∧ (2 : ℝ) ^ m ≤ 16 * R ∧
      (∀ x ∈ A, squareProportionalBuffer (1 / 16) a (2 ^ n) x) ∧
      (∀ x ∈ A, squareProportionalBuffer (1 / 16) b (2 ^ m) x)

end SRWTightness
