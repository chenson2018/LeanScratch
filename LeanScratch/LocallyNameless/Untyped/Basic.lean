import LeanScratch.LocallyNameless.Atom
import Mathlib

/-- lambda terms with free variables over `atom` and constants over `M` -/
inductive Term (atom : Type) (M : Type)
| const (m : M) : Term atom M
| unit : Term atom M
| bvar : ℕ → Term atom M
| fvar : atom → Term atom M
| lam  : Term atom M → Term atom M
| app  : Term atom M → Term atom M → Term atom M

variable {X : Type} [DecidableEq X] [Atom X] {M : Type}

/-- bound substitution of the ith index -/
@[simp]
def Term.open_rec (i : ℕ) (sub : Term X M) : Term X M → Term X M
| const m => const m
| unit => unit
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (open_rec i sub l) (open_rec i sub r)
| lam M   => lam $ open_rec (i+1) sub M

notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.open_rec i sub e 

--/-- bound substitution of the closest binding -/
@[simp]
def Term.open' {X M} (e u):= @Term.open_rec X M 0 u e

infixr:80 " ^ " => Term.open'

local instance : Coe X (Term X M) where
  coe x := Term.fvar x

local instance (i : ℕ) : OfNat (Term X M) i where
  ofNat := Term.bvar i

@[simp]
def Term.subst (x : X) (sub : Term X M) : Term X M → Term X M
| const m => const m
| unit => unit
| bvar i  => bvar i
| fvar x' => if x = x' then sub else fvar x'
| app l r => app (subst x sub l) (subst x sub r)
| lam M   => lam $ subst x sub M

notation:67 e "[" x ":=" sub "]" => Term.subst x sub e 

/-- free variables of a term -/
@[simp]
def Term.fv : Term X M → Finset X
| bvar _ | const _ | unit => {}
| fvar x => {x}
| lam e1 => e1.fv
| app l r => l.fv ∪ r.fv

/-- locally closed terms -/
inductive Term.LC : Term X M → Prop
| const (m) : LC (const m)
| unit : LC unit
| fvar (x)  : LC (fvar x)
| lam (L : Finset X) (e : Term X M) : (∀ x : X, x ∉ L → LC (e ^ fvar x)) → LC (lam e)
| app {l r} : l.LC → r.LC → LC (app l r)

/-- bind a free variable of a Term, so that the transformation `T` → `λ . T` makes sense -/
@[simp]
def Term.close_rec {atom M} [DecidableEq atom] (k : ℕ) (x : atom) : Term atom M → Term atom M
| fvar x' => if x = x' then bvar k else fvar x'
| unit => unit
| bvar i  => bvar i
| const m => const m
| app l r => app (close_rec k x l) (close_rec k x r)
| lam t   => lam $ close_rec (k+1) x t

notation:68 e "⟦" k " ↜ " x "⟧"=> Term.close_rec k x e 

--/-- bound substitution of the closest binding -/
@[simp]
def Term.close {X M} [DecidableEq X] (e u):= @Term.close_rec X M _ 0 u e

infixr:80 " ^* " => Term.close

section examples
open Term
variable (Y Z : X)
example : (lam (app 0 Y)) [Y := Z] = (lam (app 0 Z) : Term X ℕ) := by simp only [subst, ↓reduceIte]; rfl
example : (app (lam (app 1 0)) 0) ^ (Y : Term X ℕ) = (app (lam (app Y 0)) Y) := by simp; rfl
end examples
