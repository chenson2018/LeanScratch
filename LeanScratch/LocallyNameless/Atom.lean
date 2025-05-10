import Mathlib

/-- A type that can always generate a fresh name, for use as free variables -/
class Atom (atom : Type) [DecidableEq atom] where
  atom_fresh_for_list (xs : List atom) : ∃ x, x ∉ xs

lemma Nat.list_max (xs : List ℕ) : ∃ n, ∀ x, x ∈ xs → x ≤ n := by
  induction xs
  case nil =>
    exists 0
  case cons x xs ih =>
    obtain ⟨n', ih⟩ := ih 
    exists n' ⊔ x
    intros _ mem
    cases mem <;> aesop

instance Nat.instAtom : Atom ℕ where
  atom_fresh_for_list xs := by
    have ⟨x, h⟩ := Nat.list_max xs 
    exists x + 1
    intros J
    apply Nat.not_succ_le_self x $ h (x+1) J

lemma atom_fresh_for_set {X : Type} [DecidableEq X] [Atom X] (xs : Finset X) : ∃ x : X, x ∉ xs := by
  have ⟨a, H⟩ := Atom.atom_fresh_for_list xs.val.toList
  exists a
  aesop
