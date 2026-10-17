import SRWTightness.ExteriorRecordProductLaw
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
namespace SRWTightness

/-- The total roots assigned to one exterior label. -/
def labeledRootTotal {n : ℕ} (label : Fin n → Bool) (r : Fin n → ℕ) (c : Bool) : ℕ :=
  ∑ i, if label i = c then r i else 0

/-- Positive slot counts with prescribed two-site totals, in a finite ambient box. -/
noncomputable def positiveRootVectors {n : ℕ} (label : Fin n → Bool) (k l : ℕ) :
    Finset (Fin n → Fin (k + l + 1)) :=
  Finset.univ.filter (fun r ↦ (∀ i, 0 < (r i).val) ∧
    labeledRootTotal label (fun i ↦ (r i).val) false = k ∧
    labeledRootTotal label (fun i ↦ (r i).val) true = l)

/-- The shared reference count mixture; counts, not failures, are summed at each label. -/
noncomputable def referenceJointCountWeight {n : ℕ} (p : ℝ) (label : Fin n → Bool)
    (k l : ℕ) : ℝ :=
  ∑ r ∈ positiveRootVectors label k l, ∏ i, p * (1 - p) ^ ((r i).val - 1)

/-- The two label totals partition all roots. -/
theorem labeled_root_total_partition {n : ℕ} (label : Fin n → Bool) (r : Fin n → ℕ) :
    labeledRootTotal label r false + labeledRootTotal label r true = ∑ i, r i := by
  rw [labeledRootTotal, labeledRootTotal, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases label i <;> simp

/-- A positive count vector has at most as many slots as total roots. -/
theorem positive_root_vector_cost {n : ℕ} (label : Fin n → Bool) (r : Fin n → ℕ)
    (k l : ℕ) (hr : ∀ i, 0 < r i)
    (hk : labeledRootTotal label r false = k) (hl : labeledRootTotal label r true = l)
    (δ ε : ℝ) (hδ : 0 ≤ δ) :
    (∑ i, (δ + ε * (r i : ℝ))) ≤ (δ + ε) * ((k : ℝ) + l) := by
  have ht : ∑ i, r i = k + l := by rw [← labeled_root_total_partition label r, hk, hl]
  have hn : n ≤ k + l := by
    calc
      n = ∑ _ : Fin n, (1 : ℕ) := by simp
      _ ≤ ∑ i, r i := Finset.sum_le_sum (fun i _ ↦ hr i)
      _ = k + l := ht
  have htr : (∑ i, (r i : ℝ)) = (k : ℝ) + l := by exact_mod_cast ht
  have hnr : (n : ℝ) ≤ (k : ℝ) + l := by exact_mod_cast hn
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, htr]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hnr hδ]

/-- Distinct bounded count vectors give distinct complete chronological count lists. -/
theorem root_vector_list_injective {n K : ℕ} :
    Function.Injective (fun r : Fin n → Fin K ↦ List.ofFn (fun i ↦ (r i).val)) := by
  intro r s h
  have he := List.ofFn_inj.mp h
  funext i
  exact Fin.ext (congrFun he i)

end SRWTightness
