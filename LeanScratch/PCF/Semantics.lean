import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep
import LeanScratch.PCF.SmallStep
import LeanScratch.PCF.FlatCPO
import LeanScratch.PCF.Continuity
import LeanScratch.LocallyNameless.STLC.Context

import Mathlib.Order.OmegaCompletePartialOrder
open OmegaCompletePartialOrder

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

@[simp]
def Ty.interp : Ty → Type
| nat => WithBot ℕ
| arrow σ τ => σ.interp → τ.interp

@[simp]
def List.interp : List (X × Ty) → Type
| [] => WithBot Empty
| (_,σ) :: tl => tl.interp × σ.interp

noncomputable instance TyCPO (ty : Ty) : OmegaCompletePartialOrder ty.interp := by
  induction ty <;> simp [Ty.interp] <;> infer_instance

noncomputable instance ListCPO (Γ : List (X × Ty)) : OmegaCompletePartialOrder Γ.interp := by
  induction Γ <;> simp [List.interp] <;> infer_instance

noncomputable instance TySupSet (ty : Ty) : SupSet ty.interp := by
   induction ty <;> simp [Ty.interp] <;> infer_instance

noncomputable instance TyBot (ty : Ty) : Bot ty.interp := by
  induction ty <;> simp [Ty.interp] <;> infer_instance 

noncomputable def Der.interp {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : Γ.interp → σ.interp := 
  match Γ, der with
  | _, zero _ => λ _ => some 0
  | _, succ _ _ f => bot_s ∘ f.interp
  | _, pred _ _ f => bot_p ∘ f.interp
  | _, ifzero _ _ _ _ fa fb fc => bot_cond ∘ (λ Γ ↦ (fa.interp Γ, fb.interp Γ, fc.interp Γ))
  | _, fix _ _ _ f => (λ f ↦ ⨆ (n : ℕ), f^[n] ⊥) ∘ f.interp
  | _, app _ _ _ _ _ fl fr => (λ (f, a) ↦ f a) ∘ (λ γ ↦ (fl.interp γ, fr.interp γ))
  | (x',σ') ::Γ', @var _ _ _ x _ ok mem => by
        simp only [List.interp]
        refine if h : x = x' then ?_ else ?_
        · have eq : σ' = σ := by
            rw [h] at mem
            exact Ok.mem_head_eq ok mem
          rw [eq]
          exact Prod.snd
        · refine (Der.var ?ok $ Ok.mem_head_neq ok mem h).interp ∘ Prod.fst
          cases ok
          assumption
  | _, @lam _ _ xs Γ' M σ τ ih => by
      have i := (ih (fresh xs) (fresh_unique xs)).interp
      exact (λ Γ σ ↦  i (Γ, σ))
  termination_by 
    der.size
  decreasing_by
    all_goals simp only [List.length, Der.size]; linarith

noncomputable def Der.hom {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : Γ.interp →𝒄 σ.interp where
  toFun := der.interp
  monotone' := sorry
  map_ωSup' := sorry

theorem soundness_hom {M N: Term X} {Γ σ} (der_M : Γ ⊢ M ∶ σ) (der_N : Γ ⊢ N ∶ σ) (step : M ⇓ N) : der_M.hom = der_N.hom := by
  induction step
  case fix ih =>
    cases der_M
    next M =>
      simp [Der.hom, Der.interp]
      have Mi := ih (Der.app _ _ _ _ _ M (Der.fix _ _ _ M)) der_N
      simp [Der.hom, Der.interp] at Mi
      rw [←Mi]
      ext
      next γ =>
        rw [Function.comp_apply, Function.comp_def]
        simp
        have h : ∃ f : σ.interp →𝒄 σ.interp, M.interp γ = ⇑f := sorry
        have ⟨f, eq⟩ := h
        rw [eq]
        -- TODO: this is really close, but not the right ωCPO instance...
        --#check cpo_fix f
        sorry
  case zero =>
    cases der_M
    cases der_N
    rfl
  all_goals  sorry

-- TODO: keeping this for reference, some of the bundling is weird above
theorem soundness {M N: Term X} {Γ σ} (der_M : Γ ⊢ M ∶ σ) (der_N : Γ ⊢ N ∶ σ) (step : M ⇓ N) : der_M.interp = der_N.interp := by
  induction step
  case zero =>
    cases der_M
    cases der_N
    rfl
  case succ ih =>
    cases der_M
    cases der_N
    simp [Der.interp]
    rw [ih]
  case pred_zero step ih => 
    cases der_M
    cases der_N
    simp [Der.interp]
    rw [ih]
    case pred.zero.der_N => constructor
    simp [Der.interp]
    rfl
  case pred_succ ih => 
    cases der_M
    simp [Der.interp]
    rw [ih]
    case pred.der_N =>
      constructor
      exact der_N
    simp [Der.interp]
    rw [←Function.comp_assoc, bot_s_p]
    rfl
  case ifzero_zero ih ih' => 
    cases der_M
    simp [Der.interp]
    rw [ih]
    case ifzero.der_N => constructor
    rw [ih']
    case ifzero.der_N => assumption
    simp [Der.interp]
    rfl    
  case ifzero_succ ih ih' => 
    cases der_M
    simp [Der.interp]
    rw [ih]
    case ifzero.der_N => 
      constructor
      apply der_numeral
      assumption
    simp [Der.interp]
    unfold bot_cond
    rw [ih']
    case ifzero.der_N => assumption
    -- TODO: should be fine, as bot_s of numeral goes to last branch
    sorry
  case β ih ih' => 
    cases der_M
    simp [Der.interp]
    sorry
  case lam => 
    cases der_M
    cases der_N
    simp [Der.interp]
    ext
    sorry
  case fix ih => 
    cases der_M
    next M =>
    simp only [Der.interp]
    rw [←ih]
    case der_M =>
      constructor
      exact M
      constructor
      exact M
    simp [Der.interp]
    rw [@Function.comp_def]
    sorry
--    rw [←cpo_fix _]
--    ext
--    next step γ =>
--      rw [Function.comp_apply, ←μ_fix (M.interp γ)]
--      have ih := ih ?a der_N
--      case a =>
--        constructor
--        exact M
--        constructor
--        exact M
--      rw [←ih]
--      simp [Der.interp]
--      -- TODO: this doesn't quite work with interp_cont
--      sorry

def Nat.toTerm : ℕ → Term X
| 0 => Term.zero
| n+1 => Term.succ n.toTerm

def Term.toNat : Term X → WithBot ℕ 
| zero => 0
| succ n => n.toNat + 1
| _ => ⊥ 

theorem numeral_intep {n : ℕ} (der : [] ⊢ (n.toTerm : Term X) ∶ nat) : der.interp = (λ _ ↦ some n) := by
  induction n
  case zero =>
    simp [Nat.toTerm] at der
    ext
    case h Γ_int =>
      cases der
      simp only [Der.interp]
  case succ n ih =>
    cases der
    case succ der =>
    simp only [Der.interp]
    rw [ih]
    simp_all only [List.interp, interp]
    rfl

theorem adequacy {M : Term X} {Γ} {n : ℕ} (der : Γ ⊢ M ∶ nat) : der.interp = (λ _ ↦ some n) → (M ⇓ M) := sorry
