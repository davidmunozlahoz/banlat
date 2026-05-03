# BanLat — Lean 4 Vector and Banach Lattices Library

This project builds a library of vector lattices and Banach lattices in Lean 4,
extending Mathlib. The workflow is incremental: definitions and theorems are
added one at a time and verified before proceeding.

---

## Workflow

- Formalise only what is asked. Do not add speculative definitions, instances,
  or lemmas beyond the stated goal.
- Check very carefully the definitions and results already available in the
  repository. Do not reprove things or redefine things already available.
- When creating a new file, build on the infrastructure already present in the
  repository. Reuse existing definitions, instances, notation, imports, helper
  lemmas, and file patterns before introducing anything new; never rebuild from
  scratch concepts that are already available.
- The `Library/` directory contains reference monographs (currently
  `troitsky2025.pdf` and `aliprantis_burkinshaw2006.pdf`). Consult them when
  looking for results to formalise or to understand the mathematical context.
- When needed, search the codebase and Mathlib (use `lean_local_search`,
  `lean_loogle`, or `lean_leansearch`) for relevant results and definitions. If the result already exists in Mathlib,
  just import the right file and use it — do not reprove it or introduce an alias.
- Split long proofs into small private lemmas. Keep those lemmas `private` unless
  they are genuinely reusable across the library.
- After writing or modifying any declaration, use the Lean MCP
  (`lean_diagnostic_messages`) to confirm the file compiles before moving on.

There are three operating modes:

**State mode** — activated when asked to state (but not prove) a result.
- Fill every proof body with `sorry`.
- The file must compile modulo `sorry` (no other errors).
- Do not write any proof content; the signatures are what will be reviewed.

**Prove mode** — activated when asked to prove a result.
- The file must compile with no `sorry` whatsoever.
- If the proof needs an auxiliary result, introduce it as a `private lemma`
  with its own proof; do not touch public declarations.
- The file must compile with no style or suggested `warning`.

*Workflow within prove mode:*

1. **Plan first.** Before writing any Lean, draft a proof outline (consult the
   monographs if helpful). Break the argument into steps and identify which
   steps need a separate lemma.
2. **Search before writing.**
   When needed, search the codebase and Mathlib (use `lean_local_search`,
  `lean_loogle`, or `lean_leansearch`) for relevant results and definitions.
   Only introduce a new `private lemma` if the step is
   genuinely missing.
3. **Write the proof**, leaning on existing results as much as possible.
4. **Review after completion.** Re-read the finished proof critically: is there
   a shorter path using a result already in the file or in Mathlib? Can a long
   tactic block be replaced by a single lemma call? Aim for a soft cap of
   **~20 lines per proof body** (excluding `private` helpers). If a proof
   exceeds this, consider extracting the heavy step into a `private lemma`.

**Blueprint mode** — activated when asked to write or extend the blueprint.
The blueprint lives under `blueprint/src/` and follows the
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) conventions.
Chapters are separate `.tex` files `\input`'d from `content.tex`; start a new
chapter only when explicitly instructed.

- **Faithfulness to the formal statement (CRITICAL — highest priority).** The
  informal statement in the blueprint must correspond **exactly** to the
  formal Lean declaration it points to via `\lean{…}`. Every hypothesis,
  typeclass assumption, side condition, and quantifier in the Lean signature
  must be stated explicitly in the prose — no implicit conventions, no
  "obvious" assumptions left out, no strengthening or weakening. The blueprint
  is a primary tool for catching misstated results; a mismatch here defeats
  its purpose. After writing each entry, re-read the Lean signature side by
  side with the prose to confirm they agree.
- **No proofs.** Never include `\begin{proof} … \end{proof}` blocks in the
  blueprint. Only statements (definitions, lemmas, theorems, etc.).
- **No private lemmas.** Only `public` Lean declarations appear in the
  blueprint. Conversely, every public declaration with genuine mathematical
  content in the scope of the chapter must have a corresponding blueprint
  entry. Purely technical plumbing is omitted: obvious coercion simp lemmas
  (e.g.\ `coe_foo` lemmas stating that the carrier agrees with the expected
  set), auto-generated or definitionally trivial typeclass instances that
  carry no mathematical content beyond a coercion (e.g.\ `SetLike`,
  `CoeHead`, `PartialOrder` lifted from set inclusion), tautological
  restatements of a definition (e.g.\ an `_mem` lemma asserting the defining
  closure condition of a substructure, such as `VectorSublattice.sup_mem`
  saying that a vector sublattice is closed under $\sqcup$), and similar
  definitional unfolding lemmas. When in doubt, ask: would a mathematician
  reading the blueprint learn something from this entry? If the entry would
  merely restate a coercion, a typeclass, or the defining condition of a
  structure the reader already takes for granted, skip it.
- **Environments.** Use `definition`, `lemma`, `proposition`, `theorem`,
  `corollary` from `macros/common.tex`. Add a `\label{type:short_name}` to
  every statement (e.g. `\label{def:vector-lattice}`,
  `\label{thm:riesz-decomp}`). The environment reflects the mathematical
  content of the statement, not the Lean keyword. A Lean `def` is a
  blueprint `\begin{definition}` only when it introduces a genuinely new
  concept or named object; when it merely records a fact about existing
  objects (e.g.\ `PointedCone.supClosure`, which observes that the
  already-defined sup-closure of a pointed cone is itself a pointed cone,
  or `VectorSublattice.ofAbsClosed`, which observes that a submodule
  closed under $\lvert \cdot \rvert$ is a vector sublattice), the
  blueprint entry is a `\begin{lemma}` (or theorem, proposition) and the
  label is prefixed `lem:` (or `thm:`, etc.).
- **Lean linkage.** On every statement, attach:
  - `\lean{Fully.Qualified.Name}` — fully qualified Lean name(s). Multiple
    names are comma-separated.
  - `\leanok` — **only** if the referenced Lean declaration currently
    compiles (verify with `lean_diagnostic_messages` or by inspecting the
    file). Omit `\leanok` when the Lean counterpart is still `sorry`-ed or
    does not yet exist.
  - `\uses{label1, label2, …}` — blueprint labels of statements this result
    depends on. This drives the dependency graph; keep it accurate.
- **Prose.** Statements should be self-contained mathematical English, not
  Lean syntax. Use the standard nomenclature and formulations a working
  mathematician would expect, not transliterations of the Lean definition:
  e.g.\ state "sigma Dedekind complete" in terms of countable bounded
  suprema/infima, not as the four-clause `sSup`/`sInf` typeclass; avoid
  talking about universes, `Nonempty` typeclass instances, or "extending
  the ambient lattice order". Consult the monographs in `Library/`
  (`troitsky2025.pdf`, `aliprantis_burkinshaw2006.pdf`) to pick natural
  phrasing, conventional terminology, **and standard mathematical
  notation**, even when the Lean name or notation suggests otherwise
  (but do not cite them — see the rule below). In particular, use the
  book notation for lattice operations ($x \vee y$, $x \wedge y$) rather
  than Lean's ($x \sqcup y$, $x \sqcap y$); similarly for any other
  symbol where Lean and the standard literature diverge. **Always
  identify a structure with its underlying set; never refer to the
  "underlying set", "underlying subset", "underlying submodule",
  "underlying subtype", or "carrier" of a substructure, even in
  statements that are formally about set- or submodule-level
  equalities.** Refer to a vector sublattice `Y` as "Y", not "the
  underlying subset of Y" or "the subtype of Y"; write "Y is a normed
  vector lattice" rather than "the underlying subtype of Y carries a
  normed vector lattice structure"; and write "the band generated by
  $A$ equals $A^{dd}$" rather than "the underlying set of the band
  generated by $A$ equals $A^{dd}$". An informal mathematician makes no
  distinction between a substructure and its underlying set; the
  blueprint must read the same way. Do not cite monographs (see the
  rule below).
- **Consistency.** Nomenclature and notation must remain consistent across the
  blueprint. It is a single coherent and cohesive document: the same concept
  gets the same name and symbol everywhere, and terminology introduced in one
  chapter is reused (not redefined) in later chapters.
- **Section intros.** Begin every `\section` (and `\subsection`, when
  non-trivial) with a short paragraph describing what the section covers, why
  it matters, and how it fits with neighbouring sections. This intro precedes
  the first formal environment and is plain prose (no `\label`, no `\lean`).
- **Workflow.**
  1. Identify the public Lean declarations in the relevant file(s).
  2. For each, search the existing blueprint to avoid duplicates.
  3. Write the entry with `\label`, `\lean`, `\uses`, and `\leanok` (if
     applicable).
  4. After editing, run `leanblueprint checkdecls` mentally: every `\lean{…}`
     name must exist in the project; every `\uses{…}` label must be defined
     somewhere in the blueprint.

---

## Style

See **[STYLE.md](STYLE.md)** for the full naming conventions, documentation
standards, and code-style rules.

**Never reference monographs or external sources in Lean files.** No
"Troitsky 8.5.5", "(Aliprantis–Burkinshaw 1.3.7)", "Corollary X.Y.Z" headings,
or similar citations in doc-comments, theorem names, section dividers, or
inline comments. Statements and proofs should stand on their own.
References to Mathlib declarations are fine.
