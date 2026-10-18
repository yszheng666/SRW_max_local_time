# Uniform entrance atoms from harmonic chains and equilibrium sweeping

Status: PASS. Full6514/Audit4957/4956distinct/26axiom-free/graph2688.
23 modules / 47 declarations uniquely registered and audited.
Standard axioms, placeholder scan, source SHA, 100 columns and whitespace PASS.
Logs: logs/build-uniform-entrance-gate.log, logs/axioms-uniform-entrance.log.

The purpose is to supply a nonvanishing entrance-atom lower comparison when the
existing small-relative-error estimate is too large to exponentiate on the lower
side. Only the original potential asymptotic and positive-harmonic relative inputs
are used; no new entrance comparison is assumed.

The harmonic input gives two-sided exponential bounds along a lattice chain whose
small balls lie in the harmonic domain. The actual entrance atom is the harmonic
exit payoff from the punctured domain, including atoms of arbitrarily small mass.
The chain bound therefore applies uniformly to every positive reference atom.

Explicit integer unit segments move toward their endpoint and remain fixed after
arrival. Five horizontal/vertical segments connect two annular points through an
integer square frame. Outward endpoint segments preserve the starting radius;
frame segments have a fixed coordinate of size M. All segments stay in a box of
radius at most 5m/4, have length at most 5m/2 each, and admit balls of radius m/16
inside the outer disk and outside the observation set. Applying the harmonic
comparison along the five segments gives a scale-independent bound between every
pair of actual terminal entrance states.

The existing equilibrium sweep identity is specialized to the actual singleton
entrance payoff. The enclosing disk equilibrium measure is supported on its inner
unit boundary layer, where the preceding comparison applies. Its capacity times
the literal terminal reference intensity is between one half and two, using the
existing buffered-annulus capacity estimate. Sweeping and normalization then give
uniform positive lower and finite upper constants for every actual entrance atom
relative to alpha times its equilibrium charge.

The zero mark has uniformly positive actual mass: avoiding the enclosing disk of
radius m/2 has positive probability from the terminal entrance layer, by the
existing annulus return estimate. Combining this with the positive entrance-atom
bound gives a fixed lower comparison for every nonnegative ordered test and every
ordered-word event, including its zero atom.

A general scalar lemma combines a fixed positive lower comparison with the
existing relative-error estimate. For small relative error it uses the previous
sharp exponential bound; for larger error the fixed positive bound is absorbed
by a larger universal exponent coefficient. Consequently the full two-sided
terminal exponential comparison no longer requires relative error at most one
half. It retains the old geometric condition 2a < m-H-2 and H <= m/8.

The full observation-radius range a<m/2 and the downstream ordered forest
statements are separate subsequent work. No source obligation is promoted by
this batch alone. All inputs remain the original potential and positive-harmonic
interfaces already included in the six-input main theorem.
