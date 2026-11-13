# BanLat

BanLat is a [Lean 4](https://lean-lang.org/) library for vector lattices and Banach
lattices, built on [Mathlib](https://github.com/leanprover-community/mathlib4). Its
goal is to provide a reusable foundation for systematically formalizing contemporary
research in Banach lattice theory and nearby areas of functional analysis.

The [companion paper](https://arxiv.org/abs/2608.07388) gives the full motivation, explains the
development process, presents research-level case studies, and provides a
module-by-module account of version v0.1.0 of the library.

## Approach

BanLat is largely written by LLMs, but with close human supervision of the definitions, statements, docstrings and, more generally, of the implementation. Pull requests are critically reviewed by humans, and often changes are made to make the code understandable and coherent. In other words, it is a codebase largely written by LLMs, but understandable by humans.

The goal of the library is to serve as a research tool. It is this balance between human understanding and automation that makes the tool useful. On the one hand, automation accelerates the process of writing code so that current research can be formalized in a practical way (see [Use cases](#use-cases)). On the other hand, retaining human understanding of the library allows for a better understanding of the field of Banach lattices.

BanLat is research-driven rather than an attempt to formalize a monograph from start to
finish. The library grows by adding coherent, reusable prerequisites for concrete
research-level formalizations.

## Using BanLat

The Lean toolchain and Mathlib revision are pinned by the repository. To build the
library:

```bash
git clone https://github.com/davidmunozlahoz/banlat.git
cd banlat
lake exe cache get
lake build
```

## Contents of v4.35.0

A quick overview of the material available in the
[v4.35.0](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0) release.

**Foundations of vector and Banach lattices.**
- [`Basic.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Basic.lean), [`Normed.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Normed.lean): lattice-ordered groups,
  vector lattices, normed vector lattices and Banach lattices.
- [`Disjoint.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Disjoint.lean), [`RieszDec.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/RieszDec.lean),
  [`Atom.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Atom.lean), [`OrderUnit.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/OrderUnit.lean),
  [`QuasiInteriorPoint.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/QuasiInteriorPoint.lean),
  [`OrderDense.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/OrderDense.lean), [`Majorizing.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Majorizing.lean),
  [`OrderComplete.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/OrderComplete.lean),
  [`CountableSupProperty.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/CountableSupProperty.lean): disjointness, Riesz
  decomposition, atoms, order units, quasi-interior points, order dense and majorizing
  sublattices, σ-Dedekind completeness and the countable supremum property.
- [`Pi.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Pi.lean), [`Quotient.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Quotient.lean): products and quotients.
- [`Substructures/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Substructures): sublattices, order ideals, bands, disjoint
  complements, generated bands, projection bands and the (principal) projection property.
- [`Convergences/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Convergences): order, σ-order and uniform convergence; uniform
  completeness.
- [`FunctionalCalculus.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/FunctionalCalculus.lean): functional calculus for
  positively homogeneous continuous functions in uniformly complete vector lattices.
- [`LLexpr.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/LLexpr.lean), [`Tactic/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Tactic): formal lattice-linear
  expressions and the `llarith` tactic.

**Operators and duality.**
- [`Operators/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Operators): positive, regular, order bounded, (σ-)order continuous and
  strictly positive operators, lattice homomorphisms, and the Riesz–Kantorovich
  theorem.
- [`Dual.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Dual.lean), [`Bidual.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/Bidual.lean): order and strong duals,
  and the bidual of a Banach lattice.
- [`PConvexity.lean`](https://github.com/davidmunozlahoz/banlat/blob/v4.35.0/BanLat/PConvexity.lean): p-convex operators and Banach lattices.

**Completions and representations.**
- [`DedekindCompletion/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/DedekindCompletion): construction, existence and uniqueness
  of the Dedekind completion, and a Banach lattice structure on it.
- [`L1repr/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/L1repr): `L¹`-representations of vector lattices with a strictly
  positive functional.
- [`Free/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Free): free vector lattices and the free Banach lattice generated by a
  normed space.

**Classes of Banach lattices.**
- [`OrderContinuous/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/OrderContinuous): order continuous norms, lattice copies of
  `ℓ∞`, and the theorems of Nakano, Meyer-Nieberg and Ando.
- [`ALSpace/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/ALSpace), [`AMSpace/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/AMSpace), [`ALpSpace/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/ALpSpace):
  AL-, AM- and ALₚ-spaces, AL/AM duality, maximal ideals and characters, and Kakutani's
  representation theorems (including complex AM-spaces with unit).
- [`ComplexBanachLattice/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/ComplexBanachLattice): complex vector and Banach lattices,
  complexification, the complex modulus and complex functional calculus.
- [`QuasiNormed/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/QuasiNormed): quasi-normed spaces and quasi-Banach lattices.
- [`LocallySolid/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/LocallySolid): locally solid and locally convex-solid topologies,
  their completions and Lebesgue properties.

**Examples.**
- [`Examples/CofK/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Examples/CofK): `C(K)` (real and complex) and its dual `M(K)`.
- [`Examples/MofK/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Examples/MofK), [`Examples/SignedMeasure/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Examples/SignedMeasure):
  regular signed Borel measures as an AL-space and an `L¹` space, atoms, bands and
  decompositions; finite signed measures.
- [`Examples/Lp/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Examples/Lp): `Lᵖ` spaces as Banach lattices, atoms, weak units,
  closed sublattices, change of density, density character, Gaussian and stable
  subspaces, and the classification of atomic and homogeneous `Lᵖ` spaces.
- [`Examples/Ellp/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Examples/Ellp): `ℓᵖ`-sums of Banach lattices.

**Boolean and measure algebras.**
- [`BooleanAlgebras/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/BooleanAlgebras): Stone representation, σ-complete and atomless
  Boolean algebras, countably additive functionals and Hahn decomposition, measure
  algebras, and the Maharam and Carathéodory classification theorems.

**Auxiliary material.**
- [`Preliminaries/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Preliminaries): density character, the Eberlein–Šmulian theorem,
  and facts about atomless and signed measures.
- [`Probability/`](https://github.com/davidmunozlahoz/banlat/tree/v4.35.0/BanLat/Probability): convergence in measure, and symmetric stable
  distributions and random variables.

## Use cases

Research papers formalized using BanLat:

- *Order continuity of induced homomorphisms between free Banach lattices*, by
  R. E. Pariente-Martín and P. Tradacete —
  [pedrotradacete/FBLOrderContinuousLH](https://github.com/pedrotradacete/FBLOrderContinuousLH)
- *Coordinate systems and maximal order complexity in Banach lattices*, by A. Avilés,
  C. Rosendal, M. A. Taylor and P. Tradacete —
  [pedrotradacete/DSTBL3](https://github.com/pedrotradacete/DSTBL3)
- *Aliprantis's questions on locally solid topologies*, by D. Muñoz-Lahoz,
  M. A. Taylor and P. Tradacete —
  [davidmunozlahoz/Aliprantis](https://github.com/davidmunozlahoz/Aliprantis)
- *Order closure, order adherence and Fatou norms*, by A. Avilés, M. A. Taylor and
  P. Tradacete — [pedrotradacete/OrderClosures](https://github.com/pedrotradacete/OrderClosures)
- *Wickstead's conjecture on positive projections and non-representable Banach lattice
  algebras*, by D. Muñoz-Lahoz —
  [davidmunozlahoz/Wickstead](https://github.com/davidmunozlahoz/Wickstead)
