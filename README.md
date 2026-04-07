# banlat

The Banach lattices library in Lean.

## 👀 Overview

### Foundations

- **`BanLat/Basic.lean`** — Lattice-ordered groups and vector lattices: positive
  and negative parts, absolute value, the Riesz decomposition theorem, and
  basic results on real scalar multiplication. The Archimedean property.
- **`BanLat/OrderComplete.lean`** — Order completeness (`IsOrderComplete`) and
  σ-order completeness as `Prop`-valued analogues of Mathlib's
  `ConditionallyCompleteLattice`, with their basic implications.

### Substructures

- **`BanLat/Sublattice.lean`** — Vector sublattices: linear subspaces closed
  under the lattice operations, characterised by closure under `|·|`.
- **`BanLat/Ideal.lean`** — Order ideals as solid sublattices, with the basic
  characterisations.
- **`BanLat/Band.lean`** — Bands (order-closed ideals), disjoint complements,
  and projection bands.
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
- **`BanLat/OrderContinuous.lean`** — Order continuous norms; Nakano,
  Meyer–Nieberg, and Ando theorems.
- **`BanLat/Dual.lean`** — The order dual and the norm dual of a (Banach)
  lattice, and their coincidence in the Banach setting.
- **`BanLat/Bidual.lean`** — The bidual of a Banach lattice and the canonical
  isometric vector lattice embedding into it.
- **`BanLat/Pi.lean`** — Pointwise products and `ℓ^p` products of vector,
  normed, and Banach lattices.

### Special classes and representation

- **`BanLat/AMSpace.lean`** — AM-spaces and AM-spaces with unit; strong units.
- **`BanLat/ALSpace.lean`** — AL-spaces and their order continuity.
- **`BanLat/Kakutani.lean`** — Bohnenblust–Kakutani–Krein representation of an
  AM-space with unit as `C(K, ℝ)` via the Gelfand transform.

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
