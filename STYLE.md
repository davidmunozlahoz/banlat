# BanLat Style Guide

This file collects naming conventions, documentation standards, and code-style
rules for the BanLat library. They follow the upstream
[Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
and [style guide](https://leanprover-community.github.io/contribute/style.html) closely,
with a few library-specific additions noted inline.

---

## Naming Conventions

### Capitalisation

| Kind | Convention | Example |
|------|-----------|---------|
| Theorems, lemmas, terms of `Prop` | `snake_case` | `abs_eq_zero_iff` |
| Types, structures, classes | `UpperCamelCase` | `VectorLattice` |
| Functions returning a value (non-`Prop`) | `lowerCamelCase` | `toFun` |
| Functions whose name is derived from a type | named like the type | `vectorLatticeOfFoo` |
| `UpperCamelCase` embedded in `snake_case` | convert to `lowerCamelCase` | `map_natCast` |
| Acronyms | treated as a single word | `Ne` not `NE` |

File names use `UpperCamelCase` (e.g. `Basic.lean`, `BanachLattice.lean`).

Use **American English** throughout: `factorization`, `Localization`, `FiberBundle`.

### Typeclass names

- Noun-style predicates take an `Is`-prefix: `IsOrderedAddMonoid`, `IsBanachLattice`.
- Adjective-style predicates do not: `Archimedean`, `Normal`.

### Variable conventions

Follow the standard Mathlib variable conventions:

| Symbol | Intended type |
|--------|--------------|
| `u, v, w` | universe levels |
| `α, β, γ` | generic types |
| `x, y, z` | elements of a generic type |
| `a, b, c` | propositions |
| `h, h₁, h₂` | hypotheses |
| `p, q, r` | predicates or relations |
| `s, t` | sets or lists |
| `m, n, k` | natural numbers |
| `i, j` | integers or indices |
| `G` | group; `R` ring; `K` or `𝕜` field; `E` vector/Banach space |

Prefer uppercase letters over Greek letters for structured mathematical objects
(e.g. `E : Type*` for a Banach lattice).

### Symbol spellings

When a symbol appears in a lemma name it is transcribed as follows.

**Logic**

| Symbol | Name |
|--------|------|
| `∨` | `or` |
| `∧` | `and` |
| `→` | `imp` (or `of` when the conclusion is stated first) |
| `↔` | `iff` |
| `¬` | `not` |
| `∃` | `exists` / `bex` (bounded) |
| `∀` | `forall` / `ball` (bounded) |

**Sets**

| Symbol | Name |
|--------|------|
| `∈` | `mem` |
| `∉` | `notMem` |
| `∪` | `union` |
| `∩` | `inter` |
| `⋃` | `iUnion` / `biUnion` |
| `⋂` | `iInter` / `biInter` |
| `\` | `sdiff` |
| `ᶜ` | `compl` |

**Algebra**

| Symbol | Name |
|--------|------|
| `0` | `zero` |
| `+` | `add` |
| `-` (unary) | `neg` |
| `-` (binary) | `sub` |
| `1` | `one` |
| `*` | `mul` |
| `^` | `pow` |
| `/` | `div` |
| `•` | `smul` |
| `⁻¹` | `inv` |

**Lattices**

| Symbol | Name |
|--------|------|
| `<` | `lt` / `gt` |
| `≤` | `le` / `ge` |
| `⊔` | `sup` |
| `⊓` | `inf` |
| `⨆` | `iSup` / `biSup` / `ciSup` |
| `⨅` | `iInf` / `biInf` / `ciInf` |

Use `ge`/`gt` instead of `le`/`lt` when arguments swap order or when the second
argument is more variable.

### Common name suffixes

| Suffix | Meaning |
|--------|---------|
| `_iff` | biconditional characterisation (`P ↔ Q`) |
| `_of_` | implication (`A → B → C` named `c_of_a_of_b`) |
| `_eq` | equational form |
| `_nonneg`, `_pos`, `_ne_zero` | sign conditions |
| `_nonpos`, `_neg` | negative sign conditions |
| `_injective`, `_surjective`, `_bijective` | `Function.Injective f` etc. |
| `_inj` | `f x = f y ↔ x = y` |
| `_mono`, `_antitone`, `_strictMono` | monotonicity |
| `_comm`, `_assoc` | commutativity / associativity |
| `_left`, `_right` | left / right variant of an operation |
| `_smul`, `_add`, `_neg` | operation suffixes |

Prefer `pos`, `neg`, `nonneg`, `nonpos` over `zero_lt`, `lt_zero`, etc.

### Theorem naming pattern

The name reflects the **conclusion** first, hypotheses follow after `_of_`:
```
C_of_A_of_B   -- theorem : A → B → C
```

For biconditionals use `_iff`; for extensionality lemmas use `.ext` marked with
`@[ext]`.

**Injectivity variants**: use `f_injective` for `Function.Injective f` and
`f_inj` for the bidirectional form `f x = f y ↔ x = y`.

### Namespace conventions

- Drop unambiguous namespaces from lemma names; prepend in `lowerCamelCase` if
  ambiguous (e.g. `map_natCast`).
- Logical connectives live in their own namespaces:
  `And.intro`, `Or.inl`, `Iff.mp`, `Eq.symm`, etc.

---

## Documentation Style

### Module docstrings

Every file begins with a module docstring (`/-! ... -/`) that:
- States the mathematical content and context (~1 short paragraph).
- Does **not** list every result or re-explain proofs.
- May highlight one key theorem the rest of the file builds toward.
- Stays within a soft cap of ~15 lines.

### Declaration doc-comments

Every `theorem`, `lemma`, `def`, or `instance` in the public API gets a
doc-comment (`/-- ... -/`) of at most 2–3 lines (4–5 only when genuinely
necessary).

- Do **not** reference monographs or external sources. References to Mathlib declarations are fine.
- `private` lemmas do not need a doc-comment unless the proof strategy is
  non-obvious.

### Inline comments

Use `--` for short, genuinely non-obvious remarks. Do **not** comment routine
tactics.

### Example

```lean
/-!
# Positive and negative parts in a lattice-ordered group

Basic lemmas about `x⁺`, `x⁻`, and `|x|` that do not require a vector lattice
structure.
-/

/-- An element of a lattice-ordered group is zero iff its absolute value is zero. -/
theorem abs_eq_zero_iff (x : X) : |x| = 0 ↔ x = 0 := ...
```

---

## Code Style

### Line length

Maximum **100 characters** per line.

### Indentation and spacing

- All top-level declarations (`def`, `lemma`, `theorem`, `class`, `structure`)
  are flush-left; opening a `namespace`/`section` does **not** trigger
  indentation.
- Proof tactics are indented **2 spaces** from `by`.
- Multi-line theorem statements are indented **4 spaces**.
- Use spaces around `:`, `:=`, and infix operators; place operators **before**
  line breaks, not after.
- Each `·` subgoal bullet sits at the same indent level as the parent tactic;
  subsequent tactics within the branch are indented 2 more spaces.

### `variable` blocks

Use `variable` blocks to avoid repeating typeclass assumptions across related
declarations.

### Proof style

- Prefer `calc` blocks for equational or inequality chains; align the relation
  symbols across lines.
- Prefer `constructor` + `·` for iff proofs.
- Prefer `fun x ↦ ...` over `fun x => ...`; never use `λ`.
- Prefer `<|` for right-associative grouping; avoid `$`.
- Require a space after `←` in `rw` / `simp`: `rw [← add_comm]`.

### `simp`

- Avoid bare `simp` or `simp only [*]` in **public** proof bodies when a more
  explicit proof is short.
- `simp` is acceptable inside `private` lemmas and for trivially dischargeable
  goals.
- Do **not** squeeze terminal `simp` calls unless there is a documented
  performance issue; unsqueezed calls remain readable and resilient to name
  changes.

### Arithmetic and coercions

Use `norm_cast` / `push_cast` / `norm_num` for numeric coercions and arithmetic.

### `have` statements

- Short justification: single line is fine.
- Long justification: place on the next line, indented 2 spaces.
- In tactic mode: place `by` on the same line as `have`.

### Anonymous constructors and functions

- For simple anonymous functions prefer centred-dot notation: `(· ^ 2)`.
- For named-argument lambdas use `fun (x : T) ↦ body`.

### Normal forms

Prefer `s.Nonempty` over `∃ x, x ∈ s`.

For bottom/top elements:
- In **assumptions**: use `x ≠ ⊥` (easier to verify).
- In **conclusions**: use `⊥ < x` (strictly more powerful).

### Empty lines inside declarations

Avoid empty lines inside a single declaration body (Mathlib linter enforces
this). Use a brief comment to separate logical blocks if needed.

### `sorry`

Do **not** leave stray `sorry`s in committed code (see `AGENTS.md` for the
*State mode* / *Prove mode* distinction that governs when `sorry` is
intentional).
