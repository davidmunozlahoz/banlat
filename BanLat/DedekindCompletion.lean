/-
Authors: Pedro Tradacete
-/

import BanLat.DedekindCompletion.Banach

/-!
# Dedekind completion of vector and Banach lattices

This module provides the bounded-cut construction, its order-dense majorizing
vector-lattice embedding, and a canonical equivalence between any two Dedekind
completions that agrees with the embeddings of the original lattice.
For a Banach lattice, the completion carries the norm
`‖y‖ = inf {‖x‖ : |y| ≤ inclusion x}`. This makes the completion a Banach
lattice and the inclusion isometric.
-/
