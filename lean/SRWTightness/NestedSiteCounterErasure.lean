import SRWTightness.NestedSiteCounterInterior
import SRWTightness.NestedSiteCounterLength

namespace SRWTightness

/-- Consecutive observation lists compose their finite-state runs. -/
theorem nestedSiteCounterRun_append (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (pre tail : List Site) :
    nestedSiteCounterRun levels state (pre ++ tail) =
      nestedSiteCounterRun levels (nestedSiteCounterRun levels state pre) tail := by
  exact List.foldl_append

/-- Once all levels are active, observations interior to all levels leave the state unchanged. -/
theorem nestedSiteCounterRun_interior (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (sites : List Site) (hlen : state.length = levels.length)
    (hin : ∀ z ∈ sites, ∀ L ∈ levels, z ∈ L.1 ∧ z ∈ L.2) :
    nestedSiteCounterRun levels (nestedSiteCounterActivate state) sites =
      nestedSiteCounterActivate state := by
  induction sites with
  | nil => rfl
  | cons z sites ih =>
    change nestedSiteCounterRun levels
      (nestedSiteCounterStep levels (nestedSiteCounterActivate state) z) sites = _
    rw [nestedSiteCounterStep_interior levels _ z
      ((nestedSiteCounterActivate_length state).trans hlen)
      (hin z List.mem_cons_self), nestedSiteCounterActivate_idempotent]
    exact ih (fun w hw ↦ hin w (List.mem_cons_of_mem z hw))

/-- An arbitrary internal block can be erased after its retained common entrance. -/
theorem nestedSiteCounterRun_erase_block (levels : List (Finset Site × Finset Site))
    (state : NestedSiteCounter) (pre inside tail : List Site) (a : Site)
    (hlen : state.length = levels.length)
    (ha : ∀ L ∈ levels, a ∈ L.1 ∧ a ∈ L.2)
    (hin : ∀ z ∈ inside, ∀ L ∈ levels, z ∈ L.1 ∧ z ∈ L.2) :
    nestedSiteCounterRun levels state (pre ++ a :: (inside ++ tail)) =
      nestedSiteCounterRun levels state (pre ++ a :: tail) := by
  rw [nestedSiteCounterRun_append, nestedSiteCounterRun_append]
  change nestedSiteCounterRun levels
      (nestedSiteCounterStep levels (nestedSiteCounterRun levels state pre) a) (inside ++ tail) =
    nestedSiteCounterRun levels
      (nestedSiteCounterStep levels (nestedSiteCounterRun levels state pre) a) tail
  have hl := nestedSiteCounterRun_length levels state pre hlen
  rw [nestedSiteCounterStep_interior levels _ a hl ha, nestedSiteCounterRun_append,
    nestedSiteCounterRun_interior levels _ inside hl hin]

end SRWTightness
