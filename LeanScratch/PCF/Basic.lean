import LeanScratch.PCF.Atom

/-- definition 2.3, but for untyped terms -/
inductive Term (X : Type)
| bvar : ℕ → Term X
| fvar : X → Term X
| lam  : Term X → Term X
| app  : Term X → Term X → Term X
| zero : Term X
| succ : Term X → Term X
| pred : Term X → Term X
| fix  : Term X → Term X
| ifzero : Term X → Term X → Term X → Term X

open Term

variable {X : Type}

/-- bound substitution of the ith index -/
@[simp]
def Term.open_rec (i : ℕ) (sub : Term X) : Term X → Term X
| bvar i' => if i = i' then sub else bvar i'
| fvar x  => fvar x
| app l r => app (open_rec i sub l) (open_rec i sub r)
| lam M   => lam $ open_rec (i+1) sub M
| zero    => zero
| pred t  => pred (open_rec i sub t)
| succ t  => succ (open_rec i sub t)
| fix  t  => fix  (open_rec i sub t)
| ifzero t₁ t₂ t₃ => ifzero (open_rec i sub t₁) (open_rec i sub t₂) (open_rec i sub t₃)

notation:68 e "⟦" i " ↝ " sub "⟧"=> Term.open_rec i sub e 

--/-- bound substitution of the closest binding -/
@[simp]
def Term.open' (e u):= @Term.open_rec X 0 u e

infixr:80 " ^ " => Term.open'

@[simp]
def Term.subst [DecidableEq X] (x : X) (sub : Term X) : Term X → Term X
| bvar i  => bvar i
| fvar x' => if x = x' then sub else fvar x'
| app l r => app (subst x sub l) (subst x sub r)
| lam M   => lam $ subst x sub M
| zero    => zero
| pred t  => pred (subst x sub t)
| succ t  => succ (subst x sub t)
| fix  t  => fix  (subst x sub t)
| ifzero t₁ t₂ t₃ => ifzero (subst x sub t₁) (subst x sub t₂) (subst x sub t₃)

notation:67 e "[" x ":=" sub "]" => Term.subst x sub e 

/-- free variables of a term -/
@[simp]
def Term.fv [DecidableEq X] : Term X → Finset X
| bvar _ | zero => {}
| fvar x => {x}
| lam e1 | fix e1 | pred e1 | succ e1 => e1.fv
| app l r => l.fv ∪ r.fv
| ifzero t₁ t₂ t₃ => t₁.fv ∪ t₂.fv ∪ t₃.fv

/-- locally closed terms -/
inductive Term.LC : Term X → Prop
| zero : LC zero
| fvar (x)  : LC (fvar x)
| lam (L : Finset X) (e : Term X) : (∀ x : X, x ∉ L → LC (e ^ fvar x)) → LC (lam e)
| app {l r} : l.LC → r.LC → LC (app l r)
| pred {t} : t.LC → LC (pred t)
| succ {t} : t.LC → LC (succ t)
| fix {t} : t.LC → LC (fix t)
| ifzero {t₁ t₂ t₃} : t₁.LC → t₂.LC → t₃.LC → LC (ifzero t₁ t₂ t₃)

/-- bind a free variable of a Term, so that the transformation `T` → `λ . T` makes sense -/
@[simp]
def Term.close_rec [DecidableEq X] (k : ℕ) (x : X) : Term X → Term X
| fvar x' => if x = x' then bvar k else fvar x'
| bvar i  => bvar i
| app l r => app (close_rec k x l) (close_rec k x r)
| lam t   => lam $ close_rec (k+1) x t
| zero    => zero
| pred t  => pred (close_rec k x t)
| succ t  => succ (close_rec k x t)
| fix  t  => fix  (close_rec k x t)
| ifzero t₁ t₂ t₃ => ifzero (close_rec k x t₁) (close_rec k x t₂) (close_rec k x t₃)

notation:68 e "⟦" k " ↜ " x "⟧"=> Term.close_rec k x e 

/-- bound substitution of the closest binding -/
@[simp]
def Term.close [DecidableEq X] (e u):= @Term.close_rec X _ 0 u e

infixr:80 " ^* " => Term.close
