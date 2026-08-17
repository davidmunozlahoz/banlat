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
- The `Library/` directory contains reference monographs. Consult them when
  looking for results to formalise or to understand the mathematical context.
- When needed, search the codebase and Mathlib (use `lean_local_search`,
  `lean_loogle`, or `lean_leansearch`) for relevant results and definitions. If the result already exists in Mathlib,
  just import the right file and use it — do not reprove it or introduce an alias.
- Use the repository tactics from `BanLat/Tactic` whenever they are applicable
  and efficient.
- Split long proofs into small private lemmas. Keep those lemmas `private` unless
  they are genuinely reusable across the library.
- Custom axioms are completely banned. Do not introduce `axiom`, `constant`, or
  any declaration that adds a project-local assumption without a proof or
  definition. If a proof cannot be completed from existing assumptions, report
  the blocker instead of weakening this rule.
- After writing or modifying any declaration, use the Lean MCP
  (`lean_diagnostic_messages`) to confirm the file compiles before moving on.

There are two operating modes:

**State mode** — activated when asked to state (but not prove) a result.

- Fill every proof body with `sorry`.
- The file must compile modulo `sorry` (no other errors).
- Do not write any proof content; the signatures are what will be reviewed.
- Before editing any file, first show the proposed diff/patch and ask for
  permission. Do not apply the edit until explicitly approved.
- State-mode output is draft work only. It must not be committed or submitted
  in a pull request.

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

## Review

When reviewing a pull request, follow **[REVIEWING.md](REVIEWING.md)** as the
review guide, together with this file and `STYLE.md`. Use the base-branch copies
of these documents as the authority for the review.

## Style

See **[STYLE.md](STYLE.md)** for the full naming conventions, documentation
standards, and code-style rules.

**Never reference monographs or external sources in Lean files.** No named
monograph references, theorem-number citations, corollary labels, or similar
citations in doc-comments, theorem names, section dividers, or inline comments.
Statements and proofs should stand on their own.
References to Mathlib declarations are fine.
