import SRWTightness.NestedSiteCounter

namespace SRWTightness

/-- Sum weights of complete excursions in a site list; unfinished final pieces contribute zero. -/
def siteExcursionWeight (K C : Finset Site) (weight : List Site → ℕ) :
    Option (List Site) → List Site → ℕ
  | _, [] => 0
  | none, z :: sites =>
      if z ∈ K then siteExcursionWeight K C weight (some [z]) sites
      else siteExcursionWeight K C weight none sites
  | some pre, z :: sites =>
      if z ∈ C then siteExcursionWeight K C weight (some (pre ++ [z])) sites
      else weight (pre ++ [z]) + siteExcursionWeight K C weight none sites

/-- Recursive terminal excursion count expressed directly in observed sites. -/
def nestedSiteCount : List (Finset Site × Finset Site) → List Site → ℕ
  | [], _ => 1
  | (K, C) :: levels, sites => siteExcursionWeight K C (nestedSiteCount levels) none sites

end SRWTightness
