# BanLat — Lean 4 Vector and Banach Lattices Library

This project builds a library of vector lattices and Banach lattices in Lean 4,
extending Mathlib. The workflow is incremental: definitions and theorems are
added one at a time and verified before proceeding.

---

## Workflow

- Formalise only what is asked. Do not add speculative definitions, instances,
  or lemmas beyond the stated goal.
- The `Library/` directory contains reference monographs (currently
  `troitsky2022.pdf` and `aliprantis_burkinshaw2006.pdf`). Consult them when
  looking for results to formalise or to understand the mathematical context.
- Before writing any declaration, search Mathlib for it (use `lean_local_search`,
  `lean_loogle`, or `lean_leansearch`). If the result already exists in Mathlib,
  just import the right file and use it — do not reprove it or introduce an alias.
- Split long proofs into small private lemmas. Keep those lemmas `private` unless
  they are genuinely reusable across the library.
- After writing or modifying any declaration, use the Lean MCP
  (`lean_diagnostic_messages`) to confirm the file compiles before moving on.

There are two operating modes:

**State mode** — activated when asked to state (but not prove) a result.
- Fill every proof body with `sorry`.
- The file must compile modulo `sorry` (no other errors).
- Do not write any proof content; the signatures are what will be reviewed.

**Prove mode** — activated when asked to prove a result.
- The file must compile with no `sorry` whatsoever.
- **Do not alter any existing definition or theorem signature** — these have
  already been reviewed and approved. Treat them as frozen.
- If the proof needs an auxiliary result, introduce it as a `private lemma`
  with its own proof; do not touch public declarations.

*Workflow within prove mode:*

1. **Plan first.** Before writing any Lean, draft a proof outline (consult the
   monographs if helpful). Break the argument into steps and identify which
   steps need a separate lemma.
2. **Search before writing.** For each step, check whether it is already proved
   in this library or in Mathlib (`lean_local_search`, `lean_loogle`,
   `lean_leansearch`). Only introduce a new `private lemma` if the step is
   genuinely missing.
3. **Write the proof**, leaning on existing results as much as possible.
4. **Review after completion.** Re-read the finished proof critically: is there
   a shorter path using a result already in the file or in Mathlib? Can a long
   tactic block be replaced by a single lemma call? Aim for a soft cap of
   **~20 lines per proof body** (excluding `private` helpers). If a proof
   exceeds this, consider extracting the heavy step into a `private lemma`.

---

## Mathlib Naming Conventions

Follow the [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)
and [style guide](https://leanprover-community.github.io/contribute/style.html) throughout.

### Case rules

| Kind | Convention | Example |
|------|-----------|---------|
| Theorems / lemmas / definitions (terms of `Prop`) | `snake_case` | `abs_eq_zero_iff` |
| Types, structures, classes, `Prop`-valued types | `UpperCamelCase` | `VectorLattice` |
| Functions returning a type | named like the type | `vectorLatticeOfFoo` |

### Common name suffixes

- `_iff` — biconditional characterisation (`P ↔ Q`)
- `_of_` — implication (`h : P → Q` named `q_of_p`)
- `_eq` — equational form
- `_nonneg`, `_pos`, `_ne_zero` — sign conditions
- `_injective`, `_surjective`, `_bijective` — `Injective f` etc.
- `_mono`, `_antitone`, `_strictMono` — monotonicity
- `_comm`, `_assoc`, `_left`, `_right` — algebraic variants
- `_smul`, `_add`, `_neg` — operation suffixes

### Typeclass names

- Use `Is`-prefix for noun-style predicates: `IsOrderedAddMonoid`, `IsBanachLattice`.
- Adjective-style predicates do not need `Is`: `Archimedean`.

### File names

Files use `UpperCamelCase` (e.g. `Basic.lean`, `BanachLattice.lean`).

---

## Documentation Style

- Each file begins with a **module docstring** (`/-! ... -/`) describing the
  mathematical content of the file. Aim for a short paragraph; a soft cap of
  ~15 lines. Cover the general idea and mathematical context — do not list every
  result or re-explain proofs. You may single out a particularly important
  result (e.g. a key theorem the rest of the file builds toward).
- Each `theorem`, `lemma`, `def`, or `instance` that is part of the public API
  gets a **doc-comment** (`/-- ... -/`) of at most 2–3 lines (4–5 only when
  genuinely necessary to state the result clearly).
- This is a neutral mathematical library. Do **not** reference monographs or
  external sources (e.g. "Troitsky 1.3.7") in doc-comments or module docstrings.
  References to Mathlib declarations are fine. The `Library/` directory is for
  your own guidance only.
- Do **not** add inline comments explaining routine Lean tactics; reserve them
  for genuinely non-obvious steps.
- `private` lemmas do not need a doc-comment unless the proof strategy is
  non-obvious.

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

- Line length: 100 characters.
- Use `variable` blocks to avoid repeating typeclass assumptions.
- Prefer `calc` blocks for equational chains, `constructor`+`·` for iff proofs.
- Avoid `simp only [*]` or bare `simp` in final proofs when a more explicit
  proof is short; `simp` is fine inside `private` lemmas and for trivial goals.
- Use `norm_cast` / `push_cast` / `norm_num` for numeric coercions and
  arithmetic.
- Avoid `sorry`-free files: do not leave stray `sorry`s in committed code.
