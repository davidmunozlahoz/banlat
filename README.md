# banlat

The Banach lattices library in Lean.

## ToDo
- [ ] Create a third mode, the prune mode, where we go through the
    library removing unnecesary result, optimizing the existing ones, and
    removing superfluous comments written in the development process but
    which do not contribute to the library.
- [ ] State and prove that every disjoint sequence of non-zero vectors in a
    Banach lattice is a 1-unconditional basic sequence.
- [ ] Add Banach lattices induced by 1-unconditional bases (for this
  we will have to formalize first bases in Banach spaces).
  For these: Let X be a Banach sequence space. Closed sublattices of X are
    exactly the closed spans of (finite or infinite) disjoint positive sequences.
- [ ] Add all the necessary results to the files in examples.
- [ ] Decomposition lemma for order continuous Banach lattices

## Blueprinted

Progress tracker for adding files to the blueprint:

### Foundations
- [x] `BanLat/Basic.lean`
- [x] `BanLat/RieszDec.lean`
- [x] `BanLat/OrderComplete.lean`
- [x] `BanLat/Disjoint.lean`

### Substructures
- [x] `BanLat/Substructures/Sublattice.lean`
- [x] `BanLat/OrderDense.lean`
- [x] `BanLat/Substructures/Ideal.lean`
- [x] `BanLat/Atom.lean`
- [x] `BanLat/Quotient.lean`

### Operators
- [x] `BanLat/Operators/Hom.lean`
- [x] `BanLat/Operators/Positive.lean`
- [x] `BanLat/Operators/OrderBounded.lean`
- [x] `BanLat/Operators/RieszKantorovich.lean`
- [x] `BanLat/Operators/Regular.lean`

### Normed and Banach lattices
- [x] `BanLat/Normed.lean`
- [ ] `BanLat/OrderContinuous.lean`
- [x] `BanLat/Dual.lean`
- [x] `BanLat/Bidual.lean`
- [x] `BanLat/Pi.lean`

### Special classes and representation
- [ ] `BanLat/AMSpace.lean`
- [ ] `BanLat/ALSpace.lean`
- [ ] `BanLat/KakutaniAM.lean`
- [ ] `BanLat/KakutaniAL.lean`

### Examples
- [ ] `BanLat/Examples/Lp.lean`
- [ ] `BanLat/Examples/CofK.lean`
- [ ] `BanLat/Examples/MofK.lean`
- [ ] `BanLat/Examples/SignedMeasure.lean`

### Preliminaries
- [ ] `BanLat/Preliminaries/SignedMeasure.lean`
- [ ] `BanLat/Preliminaries/Regularity.lean`
- [ ] `BanLat/Preliminaries/Baire.lean`

## Overview

This is very likely outdated; I only update it once in a while.

### Foundations

- **`BanLat/Basic.lean`** — Lattice-ordered groups and vector lattices: positive
  and negative parts, absolute value, the Riesz decomposition theorem, and
  basic results on real scalar multiplication. The Archimedean property.
- **`BanLat/OrderComplete.lean`** — Order completeness (`IsOrderComplete`) and
  σ-order completeness as `Prop`-valued analogues of Mathlib's
  `ConditionallyCompleteLattice`, with their basic implications.
- **`BanLat/Disjoint.lean`** — Disjointness `IsVLDisjoint x y ↔ |x| ⊓ |y| = 0`:
  symmetry, zero rules, the Birkhoff identity `|x + y| = |x| + |y|`,
  compatibility with scalar multiplication, monotonicity, closure under finite
  suprema and sums, the finite-family identity
  `|∑ i, α i • x i| = ∑ i, |α i| • |x i|`, linear independence of pairwise
  disjoint non-zero families, and the vanishing of norm limits of pairwise
  disjoint sequences in a normed vector lattice.

### Substructures

- **`BanLat/Substructures/Sublattice.lean`** — Vector sublattices: linear subspaces closed
  under the lattice operations, characterised by closure under `|·|`.
- **`BanLat/OrderDense.lean`** — Order dense subsets of a vector lattice:
  a subset is order dense when every strictly positive element dominates a
  strictly positive element of the subset. Order dense vector sublattices.
- **`BanLat/Substructures/Ideal.lean`** — Order ideals as solid sublattices, with the basic
  characterisations. Principal ideals and the gauge norm.
- **`BanLat/Band.lean`** — Bands (order-closed ideals), disjoint complements,
  band generation, principal bands, and projection bands. The projection
  property (PP) and principal projection property (PPP). Maximal disjoint
  families (existence via Zorn), weak order units, principal band projections
  under PPP, and the decomposition lemma (`isLUB` of the family of principal
  band projections for a maximal disjoint family).
- **`BanLat/Atom.lean`** — Atoms, atomic vector lattices, and the
  decomposition into atomic and continuous parts.
- **`BanLat/Quotient.lean`** — Quotients of vector and Banach lattices by
  (closed) order ideals.

### Operators

- **`BanLat/Operators/Hom.lean`** — Vector lattice homomorphisms (`VecLatHom`),
  the predicate `IsVecLatHom`, and isomorphisms.
- **`BanLat/Operators/Positive.lean`** — Positive operators, their
  characterisation as monotone linear maps, and automatic continuity from a
  Banach lattice.
- **`BanLat/Operators/OrderBounded.lean`** — Order bounded operators and the
  bundled type `OrderBoundedHom`.
- **`BanLat/Operators/RieszKantorovich.lean`** — The Riesz–Kantorovich theorem:
  explicit lattice operations on `OrderBoundedHom X Y` when `Y` is order
  complete.
- **`BanLat/Operators/Regular.lean`** — Regular operators (differences of
  positive operators) and their relationship to order bounded operators.

### Normed and Banach lattices

- **`BanLat/Normed.lean`** — Normed vector lattices: continuity of the lattice
  operations, the Archimedean property, closedness of the positive cone, and
  monotone convergence.
- **`BanLat/Banach.lean`** — Banach lattices and Banach lattice isomorphisms.
- **`BanLat/OrderContinuous.lean`** — Order continuous norms. Nakano's theorem:
  a Banach lattice is order continuous and σ-order complete iff every monotone
  bounded sequence converges. One direction of Meyer–Nieberg: an order
  continuous norm forces order-bounded disjoint sequences to converge to zero.
  Countability of pairwise disjoint sets. The decomposition lemma
  (unconditional summability of principal band projections). One direction of
  Ando: an order continuous norm forces closed ideals to be projection bands.
- **`BanLat/Dual.lean`** — The order dual and the norm dual of a (Banach)
  lattice, and their coincidence in the Banach setting.
- **`BanLat/Bidual.lean`** — The bidual of a Banach lattice and the canonical
  isometric vector lattice embedding into it.
- **`BanLat/Pi.lean`** — Pointwise products and `ℓ^p` products of vector,
  normed, and Banach lattices.

### Special classes and representation

- **`BanLat/AMSpace.lean`** — AM-spaces and AM-spaces with unit; strong units.
- **`BanLat/ALSpace.lean`** — AL-spaces: the AL-axiom, norm identities, order
  continuity, closed sublattice inheritance. Duality: the norm dual of an
  AM-space is an AL-space, and vice versa. The dual of a non-trivial AL-space
  is an AM-space with unit via the canonical unit functional.
- **`BanLat/KakutaniAM.lean`** — Bohnenblust–Kakutani–Krein representation of
  an AM-space with unit as `C(K, ℝ)` via the Gelfand transform on lattice
  characters.

### Examples

- **`BanLat/Examples/Lp.lean`** — `Lp(μ)` as a Banach lattice; `L¹(μ)` as an
  AL-space.
- **`BanLat/Examples/CofK.lean`** — `C(K, ℝ)` for compact `K` as a Banach
  lattice and AM-space (with unit when `K` is nonempty).
- **`BanLat/Examples/MofK.lean`** — The space of finite signed measures as a
  Banach lattice via the Jordan decomposition and total variation norm.

### Preliminaries

- **`BanLat/Preliminaries/SignedMeasure.lean`** — Auxiliary measure-theoretic
  facts about `SignedMeasure.totalVariation` and the Jordan decomposition,
  used by `Examples/MofK.lean`.

## Future

- (M. T.) Once we finish the banach lattice library containing the “books” on Banach lattices and move to putting papers in the library, it probably makes sense to also collect the results in “advanced” books on Banach lattices as well. Can probably get LLMs to help us understand the Banach lattice literature in both lean-type encyclopaedic ways and simultaneously in human-readable, digestible, but still comprehensive books. We should not just record information in lean, but also learn a lot about our subject while doing it that will be super useful later for future research.
-
- I'm thinking something along the lines of: Finish putting the standard books in the library. After this, we organize papers into "categories", and start entering them into the library. We read the papers as we go, improve them, enter them both into the library and into new advanced books on Banach lattices, and at the same time generate new questions to either answer now or in the future. This makes several things advance simultaneously 1) The library (which is good for the LLMs) 2) Our knowledge of our field 3) Our ability to communicate our knowledge of the field to others (in the form of the book(s)) 4) We get to do a lot of research as we go 5) We generate a huge problem list to work on in the future.
-
- The problems should come from what is already in the literature, from how we were inspired while reading the literature, and our own personal taste. One can also ask the LLMs for natural followup directions or natural areas to pursue. Then it's just a matter of iterating this and eventually expanding to related fields like operator theory (Timur can help?), Banach spaces (Timur/Denny?), non-commutative stuff (Javi Parcet?), topology and general nonsense (Antonio?), etc., as well as fields like phase retrieval and valuations that use Banach lattices.

- We need a big list of problems we currently have open in Functional Analysis to see what the models are capable of. The sooner we can get it the better.

- We need effective ways to teach lean and how to build/structure a library so others can start on phase retrieval, time-frequency and harmonic analysis, etc.
