import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep
import LeanScratch.LocallyNameless.STLC.Context

/-- definition 2.1 -/
inductive Ty
| nat   : Ty
| arrow : Ty → Ty → Ty

open Ty
infixr:62 " ⤳ " => Ty.arrow

open Term Ty Atom

variable {X : Type} [DecidableEq X] [Atom X]

-- TODO: implicit args
/-- definition 2.3, the actual derivations -/
inductive Der : List (X × Ty) → Term X → Ty → Type
| zero (Γ)   : Der Γ zero nat
| succ (Γ M) : Der Γ M nat → Der Γ (succ M) nat
| pred (Γ M) : Der Γ M nat → Der Γ (pred M) nat
| ifzero (Γ M N₁ N₂) : Der Γ M nat → Der Γ N₁ nat → Der Γ N₂ nat → Der Γ (ifzero M N₁ N₂) nat
| fix (Γ M σ) : Der Γ M (σ ⤳ σ) → Der Γ (fix M) σ
| app (Γ M N σ τ) : Der Γ M (σ ⤳ τ) → Der Γ N σ → Der Γ (app M N) τ
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Der Γ (fvar x) T
| lam (L : Finset X) {Γ t σ τ} : (∀ x ∉ L, Der ((x,σ) :: Γ) (t ^ fvar x) τ) → Der Γ (lam t) (σ ⤳ τ) 

notation:50 Γ " ⊢ " t " ∶" T => Der Γ t T

omit [Atom X] in
theorem der_lc {t : Term X} {Γ σ} : (Γ ⊢ t ∶ σ) → LC t := by
  intros der
  induction der
  case lam xs _ _ _ _ _ ih => exact LC.lam xs _ (λ x a ↦ ih x a)
  case app ih_l ih_r => exact LC.app ih_l ih_r
  all_goals constructor <;> assumption  

def der_numeral {n : Term X} (num : Numeral n) {Γ} : Γ ⊢ n ∶ nat := sorry

def Der.size {M : Term X} {Γ σ} : (Γ ⊢ M ∶ σ) → ℕ 
| zero _ => 0
| succ _ _ a => a.size + 1
| pred _ _ a => a.size + 1
| ifzero _ _ _ _ a b c => a.size + b.size + c.size + 1
| app _ _ _ _ _ a b => a.size + b.size + 1
| @var _ _ _ _ _ _ _ => Γ.length
| lam xs a => (a (fresh xs) (fresh_unique xs)).size + 1
| fix _ _ _ a => a.size + 1
