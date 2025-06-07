import Mathlib

/-- A type that can always generate a fresh name, for use as free variables -/
class Atom (X : Type) where
  fresh : Finset X → X
  fresh_unique (xs : Finset X) : fresh xs ∉ xs

/-- this can be used as a convienient API in Prop -/
theorem Atom.fresh_ext {X} [Atom X] (xs : Finset X) : ∃ x, x ∉ xs := by
  exists fresh xs
  exact fresh_unique xs
