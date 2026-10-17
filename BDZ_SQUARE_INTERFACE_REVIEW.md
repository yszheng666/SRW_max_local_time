# Exact dyadic square fine-field interface

Source checked: [BDZ, arXiv:1301.6669v5](https://arxiv.org/pdf/1301.6669v5),
page1 domain convention and Lemma3.8(39), page12. The box boundary is fixed
at zero. Therefore the actual killed Green domain is the strict interior,
not the entire box. The new finite-set definitions retain that distinction.
Membership, inclusion and nonemptiness are proved for the interior.

The literature input explicitly packages translated dyadic boxes, normalization
by sqrt(2/pi), and closed-threshold tails starting at normalized height one.
These adjustments are part of the external assumption, not a claimed internal
source-to-interface proof. No terminal probability is assumed.

The Lean application bounds any observed subset by the full square event,
then applies the existing positive-maximum and small-height theorems. The
logarithmic scale is at least one for dyadic exponent at least two, proved
using mathlib's numerical log2 bound. Constants precede translations, scales,
observation subsets and heights.

General-side-length comparison, buffered tiling geometry and the harmonic
increment interface still need binding. Hence no new source obligation is
certified; coverage remains109/189=57.7%.

Validation passed:4929build jobs;2982audit entries/2981distinct, 5
axiom-free, all other dependencies only propext/Classical.choice/Quot.sound.
Three modules/eight declarations checked. No forbidden proof markers or
overlong lines. Source checksum and whitespace checks passed.
