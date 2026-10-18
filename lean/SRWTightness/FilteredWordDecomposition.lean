import Mathlib.Data.List.Basic
import Mathlib.Logic.Equiv.Defs

namespace SRWTightness

/-- A finite word with a prescribed ordered list of marked letters. -/
def FilteredWordFiber {α : Type*} (p : α → Bool) (xs : List α) :=
  {w : List α // w.filter p = xs}

/-- The first marked letter determines a unique unmarked prefix and remaining word. -/
theorem unmarked_prefix_split_unique {α : Type*} (p : α → Bool) (a : α) (ha : p a)
    (u v u' v' : List α) (hu : u.filter p = []) (hu' : u'.filter p = [])
    (he : u ++ a :: v = u' ++ a :: v') : u = u' ∧ v = v' := by
  induction u generalizing u' with
  | nil =>
      cases u' with
      | nil => simpa using he
      | cons b bs =>
          have hab : a = b := (List.cons.inj he).1
          have hb := List.filter_eq_nil_iff.mp hu' b (by simp)
          exact (hb (hab ▸ ha)).elim
  | cons b bs ih =>
      cases u' with
      | nil =>
          have hba : b = a := (List.cons.inj he).1
          have hb := List.filter_eq_nil_iff.mp hu b (by simp)
          exact (hb (hba.symm ▸ ha)).elim
      | cons c cs =>
          obtain ⟨hbc, ht⟩ := List.cons.inj he
          subst c
          have hbs : bs.filter p = [] := List.filter_eq_nil_iff.mpr
            (fun x hx ↦ List.filter_eq_nil_iff.mp hu x (List.mem_cons_of_mem _ hx))
          have hcs : cs.filter p = [] := List.filter_eq_nil_iff.mpr
            (fun x hx ↦ List.filter_eq_nil_iff.mp hu' x (List.mem_cons_of_mem _ hx))
          obtain ⟨rfl, rfl⟩ := ih cs hbs hcs ht
          exact ⟨rfl, rfl⟩

/-- Concatenating an unmarked prefix and the next marker parametrizes its full word fiber. -/
noncomputable def filteredWordConsEquiv {α : Type*} (p : α → Bool)
    (a : α) (as : List α) (ha : p a) :
    (FilteredWordFiber p [] × FilteredWordFiber p as) ≃ FilteredWordFiber p (a :: as) := by
  let f : (FilteredWordFiber p [] × FilteredWordFiber p as) → FilteredWordFiber p (a :: as) :=
    fun q ↦ ⟨q.1.val ++ a :: q.2.val, by
      simp only [List.filter_append, List.filter_cons, ha, ↓reduceIte, q.1.property,
        q.2.property, List.nil_append]⟩
  apply Equiv.ofBijective f
  constructor
  · intro q r h
    have hh := unmarked_prefix_split_unique p a ha q.1.val q.2.val r.1.val r.2.val
      q.1.property r.1.property (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext hh.1) (Subtype.ext hh.2)
  · intro w
    obtain ⟨u, v, he, hu, _, hv⟩ := List.filter_eq_cons_iff.mp w.property
    refine ⟨(⟨u, List.filter_eq_nil_iff.mpr hu⟩, ⟨v, hv⟩), ?_⟩
    exact Subtype.ext he.symm

end SRWTightness
