import SRWTightness.OrderedTaggedForestMixture

open scoped BigOperators

namespace SRWTightness

/-- Prepend a tagged block to its own ordered forest, leaving the other forest unchanged. -/
def taggedForestPrepend {α β : Type*} (r : Sum (List α) (List β))
    (q : List α × List β) : List α × List β :=
  r.elim (fun rs ↦ (rs ++ q.1, q.2)) (fun rs ↦ (q.1, rs ++ q.2))

/-- Chronological tagged concatenation splits into its first block and its ordered tail. -/
theorem ordered_tagged_forests_cons {α β : Type*} (n : ℕ)
    (r : Sum (List α) (List β)) (rs : Fin n → Sum (List α) (List β)) :
    orderedTaggedForests (Fin.cons r rs) = taggedForestPrepend r (orderedTaggedForests rs) := by
  cases r <;> simp [orderedTaggedForests, taggedForestPrepend, List.ofFn_succ,
    taggedForestLeft, taggedForestRight]

/-- A label's total splits into its first slot and the same label's tail total. -/
theorem labeled_root_total_cons (n : ℕ) (label : Fin (n + 1) → Bool)
    (r : Fin (n + 1) → ℕ) (c : Bool) :
    labeledRootTotal label r c = (if label 0 = c then r 0 else 0) +
      labeledRootTotal (fun i : Fin n ↦ label i.succ) (fun i ↦ r i.succ) c := by
  rw [labeledRootTotal, Fin.sum_univ_succ]
  rfl

end SRWTightness
