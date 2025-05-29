import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep

import Mathlib.Order.OmegaCompletePartialOrder

open Term Ty

variable {X : Type}

/-- definition 2.3, the actual derivations -/
inductive Der [DecidableEq X] : List (X × Ty) → Term X → Ty → Prop
| zero (Γ)   : Der Γ zero nat
| succ (Γ M) : Der Γ M nat → Der Γ (succ M) nat
| pred (Γ M) : Der Γ M nat → Der Γ (pred M) nat
| ifzero (Γ M N₁ N₂) : Der Γ M nat → Der Γ N₁ nat → Der Γ N₂ nat → Der Γ (ifzero M N₁ N₂) nat
| fix (Γ M σ) : Der Γ M (σ ⤳ σ) → Der Γ (fix M) σ
| app (Γ M N σ τ) : Der Γ M (σ ⤳ τ) → Der Γ N σ → Der Γ (app M N) τ
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Der Γ (fvar x) T
| lam (L : Finset X) {Γ t σ τ} : (∀ x ∉ L, Der ((x,σ) :: Γ) (t ^ fvar x) τ) → Der Γ (lam t) (σ ⤳ τ) 

notation:50 Γ " ⊢ " t " ∶" T => Der Γ t T

-- We'll be using the "flat" ω-cpo ℕ_⊥, so for clarity remove these instances that also inherit the order of ℕ
attribute [-instance] WithBot.le
attribute [-instance] WithBot.lt
attribute [-instance] WithBot.preorder
attribute [-instance] WithBot.partialOrder
attribute [-instance] WithBot.semilatticeInf
attribute [-instance] WithBot.lattice
attribute [-instance] WithBot.conditionallyCompleteLattice
attribute [-instance] WithBot.distribLattice
attribute [-instance] WithBot.linearOrder
attribute [-instance] WithBot.semilatticeSup

@[simp]
instance instWithBot.le_flat (α : Type) : LE (WithBot α) where
  le a₁ a₂ := a₁ = ⊥ ∨ a₁ = a₂

@[simp]
instance instWithBot.lt_flat (α : Type) : LT (WithBot α) where
  lt a₁ a₂ := a₁ = ⊥ ∧ a₂ ≠ ⊥

-- if the underlying type is decideable, it is with ≤ with bot
instance {α : Type} [dec : DecidableEq α] : DecidableLE (WithBot α) := by
  simp [DecidableLE, DecidableRel]
  intros a₁ a₂
  cases a₁
  simp only [true_or]
  exact instDecidableTrue
  cases a₂
  simp
  exact instDecidableFalse
  simp
  apply dec

instance WithBot.preorder_flat (α : Type) : Preorder (WithBot α) where
  le_refl a := by aesop
  le_trans a b c ab bc := by aesop
  lt_iff_le_not_le := by aesop

instance WithBot.partialOrder_flat (α : Type) : PartialOrder (WithBot α) where
  le_antisymm a b ab ba := by cases ab <;> cases ba <;> aesop

open OmegaCompletePartialOrder

theorem WithBot.bot_le {α : Type} (a : WithBot α) : ⊥ ≤ a := by
  left
  rfl

instance WithBot.ωcpo_flat (α : Type) [DecidableEq α] : OmegaCompletePartialOrder (WithBot α) where
  ωSup chain := if chain 0 = ⊥ ∧ chain 1 ≠ ⊥ then chain 1 else chain 0
  le_ωSup chain i := by
    by_cases c₀ : chain 0 = ⊥ <;> by_cases c₁ : chain 1 = ⊥ <;> simp [c₀, c₁]
    all_goals sorry
  ωSup_le chain x bound := sorry

-- product examples work as expected
-- TODO: the exercises on continuity here...
inductive Y | y deriving DecidableEq, Repr
inductive Z | z deriving DecidableEq, Repr

open Y Z

#synth OmegaCompletePartialOrder (WithBot Z × WithBot Y)

#eval ((⊥ , ⊥) : WithBot Z × WithBot Y) ≤ (↑z, ⊥)
#eval ((⊥ , ⊥) : WithBot Z × WithBot Y) ≤ (⊥, ↑y)
#eval ((⊥, ↑y) : WithBot Z × WithBot Y) ≤ (↑z, ↑y)
#eval ((↑z, ⊥) : WithBot Z × WithBot Y) ≤ (↑z, ↑y)


#synth LE (ℕ × ℕ)
#eval (0, 98) ≤ (0, 99)
#eval (1 : WithBot ℕ) ≤ ⊥ 

-- this is for exponents?
#synth OmegaCompletePartialOrder (WithBot Z → WithBot Y)

def brack (x y : Fin 2) : Fin 2 → Fin 2
| 0 => x
| 1 => y

#synth LE (Fin 2 → Fin 2)

def g_3_16 : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥ 
| some n => some (n + 1)

lemma g_3_16_cont : ωScottContinuous g_3_16 := sorry

@[simp]
def Ty.interp : Ty → Σ T, OmegaCompletePartialOrder T
| nat => ⟨WithBot ℕ, WithBot.ωcpo_flat ℕ⟩
| arrow σ τ => by
    have ⟨σ_ty, σ_cpo⟩ := σ.interp
    have ⟨τ_ty, τ_cpo⟩ := τ.interp
    exists (σ_ty → τ_ty)
    exact instOmegaCompletePartialOrderForall

@[simp]
def List.interp : List (X × Ty) → Σ T, OmegaCompletePartialOrder T
| [] => ⟨WithBot Empty, WithBot.ωcpo_flat Empty⟩
| (_,σ) :: tl => by
    have ⟨σ_ty, σ_cpo⟩ := σ.interp
    have ⟨tl_ty, tl_cpo⟩ := tl.interp
    exists (σ_ty × tl_ty)
    exact Prod.instOmegaCompletePartialOrder

-- I am astounded this worked so easily
instance (ty : Ty) : OmegaCompletePartialOrder (ty.interp.fst) := ty.interp.snd
instance (Γ : List (X × Ty)) : OmegaCompletePartialOrder (Γ.interp.fst) := Γ.interp.snd

def bot_s : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| n => n + 1

-- alternate ways to write if I hit issues...
#eval (· + 1) <$> some 1
#check (Nat.add 1 <$> ·)

notation "⟦" Γ "⟧" => Sigma.fst (List.interp Γ)
notation "⟦" σ "⟧" => Sigma.fst (Ty.interp σ)

-- TODO: instance wrangling
def Der.interp 
    [DecidableEq X] {Γ : List (X × Ty)} {σ : Ty} {M : Term X} 
    : (Γ ⊢ M ∶ σ) → (∃ f : ⟦Γ⟧ → ⟦σ⟧, ωScottContinuous f)
    := by
    intros der
    induction der
    case zero Γ =>
      simp only [Ty.interp]
      refine ⟨λ _ => 0, ?_⟩
      intros _ _ _ _ _ _
      simp_all only [Set.Nonempty.image_const, isLUB_singleton]
    case succ Γ _ _ ih =>
      have ⟨f, fcon⟩ := ih
      -- TODO: get notation to work here
      simp only [Ty.interp] at f
      exists (bot_s ∘ f)
      refine ωScottContinuous.comp ?_ fcon
      unfold bot_s
      simp [ωScottContinuous, ScottContinuousOn]
      intros chain nonempty dir G lub
      simp_all [IsLUB, IsLeast, DirectedOn, upperBounds, lowerBounds]
      sorry
    case pred => sorry
    case ifzero => sorry
    case fix  => sorry
    case app => sorry
    case var => sorry
    case lam => sorry
