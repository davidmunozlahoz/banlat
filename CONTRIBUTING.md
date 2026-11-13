# Contributing to BanLat

Contributions are welcome, by pull request against `master`.

## Before you start

- BanLat grows by adding material that research formalizations need.
- Check that the result is not already in BanLat or
  [Mathlib](https://github.com/leanprover-community/mathlib4). Reuse what exists rather
  than reproving it.
- LLM-assisted contributions are welcome, but you are responsible for understanding
  and checking every definition and statement you submit.

## Requirements

- Follow [STYLE.md](STYLE.md), which follows Mathlib's naming and style conventions.
  Every file starts with an author header.
- No `sorry` and no custom axioms.
- Import new files in [BanLat.lean](BanLat.lean).
- Check that the library builds without warnings:

  ```bash
  lake exe cache get
  lake build --wfail
  ```

  CI runs this build, the linter and an import check on every pull request.

## Pull requests

- Keep pull requests focused on one topic.
- Explain what is added and why in the description, and mention any change to existing
  declarations.
- Pull requests are reviewed by a human against [REVIEWING.md](REVIEWING.md). Expect
  requests for changes that make the code clearer.
