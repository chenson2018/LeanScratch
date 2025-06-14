import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep
import LeanScratch.PCF.SmallStep
import LeanScratch.PCF.FlatCPO
import LeanScratch.LocallyNameless.STLC.Context

import Mathlib.Order.OmegaCompletePartialOrder

/-- definition 2.1 -/
inductive Ty
| nat   : Ty
| arrow : Ty → Ty → Ty

open Ty
infixr:62 " ⤳ " => Ty.arrow

open Term Ty Atom

variable {X : Type} [DecidableEq X] [Atom X]

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

def bot_s : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| n => n + 1

def bot_p : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| some n => some (n - 1)

theorem bot_s_p : bot_p ∘ bot_s = id := by
  ext
  case h x => induction x <;> aesop

def bot_cond : (WithBot ℕ × WithBot ℕ × WithBot ℕ) → WithBot ℕ
| (⊥,_,_) => ⊥
| (0,ret,_) => ret
| (some (_ + 1),_,ret) => ret

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

-- TODO: version of this w/o lattice condition??
#check fixedPoints.lfp_eq_sSup_iterate
def μ {α} [OmegaCompletePartialOrder α] : (α → α) → α := sorry

def Der.interp {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : Γ.interp → σ.interp := 
  match Γ, der with
  | _, zero _ => λ _ => some 0
  | _, succ _ _ f => bot_s ∘ f.interp
  | _, pred _ _ f => bot_p ∘ f.interp
  | _, ifzero _ _ _ _ fa fb fc => bot_cond ∘ (λ Γ ↦ (fa.interp Γ, fb.interp Γ, fc.interp Γ))
  | _, fix _ _ _ f => μ ∘ f.interp
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
  case fix => sorry

/-
@[simp]
noncomputable def Ty.interp : Ty → Σ T, OmegaCompletePartialOrder T
| nat => ⟨WithBot ℕ, @CompletePartialOrder.toOmegaCompletePartialOrder _ (@WithBot.instCompletePartialOrder ℕ)⟩
| arrow σ τ => by
    have ⟨σ_ty, σ_cpo⟩ := σ.interp
    have ⟨τ_ty, τ_cpo⟩ := τ.interp
    exists (σ_ty → τ_ty)
    exact instOmegaCompletePartialOrderForall

@[simp]
noncomputable def List.interp : List (X × Ty) → Σ T, OmegaCompletePartialOrder T
| [] => ⟨WithBot Empty, @CompletePartialOrder.toOmegaCompletePartialOrder _ (@WithBot.instCompletePartialOrder Empty) ⟩
| (_,σ) :: tl => by
    have ⟨σ_ty, σ_cpo⟩ := σ.interp
    have ⟨tl_ty, tl_cpo⟩ := tl.interp
    exists (tl_ty × σ_ty)
    exact Prod.instOmegaCompletePartialOrder

-- I am astounded this worked so easily
noncomputable instance (ty : Ty) : OmegaCompletePartialOrder (ty.interp.fst) := ty.interp.snd
noncomputable instance (Γ : List (X × Ty)) : OmegaCompletePartialOrder (Γ.interp.fst) := Γ.interp.snd

open OmegaCompletePartialOrder

theorem bot_s_cont : ωScottContinuous bot_s := by
  intros D im nonemp dir d' lub
  simp_all [DirectedOn, IsLUB, IsLeast, upperBounds, lowerBounds, bot_s]
  obtain ⟨chain, chain_im⟩ := im
  obtain ⟨bound, low⟩ := lub
  constructor
  · intros d mem
    subst chain_im
    simp_all only [Set.mem_range, exists_exists_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    obtain ⟨i, deq⟩ := mem
    have leq := bound i
    rw [deq] at leq
    induction d <;> simp
    left; rfl
    next v =>
      induction d' <;> simp
      case bot => 
        exfalso
        exact WithBot.coe_nle_bot v leq
      case coe v' => 
        rw [(WithBot.coe_le_coe_iff_eq v v').mpr leq]
  · intros d h
    subst chain_im
    simp_all only [Set.mem_range, exists_exists_eq_and, forall_exists_index, forall_apply_eq_imp_iff]
    sorry

def bot_p : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| some n => some (n - 1)

theorem bot_p_cont : ωScottContinuous bot_p := sorry

-- TODO: get notation to work here
notation "⟦" Γ "⟧" => Sigma.fst (List.interp Γ)
notation "⟦" σ "⟧" => Sigma.fst (Ty.interp σ)

def bot_cond : (WithBot ℕ × WithBot ℕ × WithBot ℕ) → WithBot ℕ
| (⊥,_,_) => ⊥
| (0,ret,_) => ret
| (some (_ + 1),_,ret) => ret

theorem bot_cond_cont : ωScottContinuous bot_cond := sorry

section cont_lemmas

-- TODO: I think most (all?) of these exist already in Mathlib, but I can't get
-- the dependent Sigma versions to work...

variable {α β γ : Type} 
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β] [OmegaCompletePartialOrder γ]

theorem π₁_cont : ωScottContinuous (@Prod.fst α β) := by
  intros D range nonempty dir p lub
  simp [IsLUB, IsLeast, upperBounds, lowerBounds, DirectedOn, Set.range] at *
  obtain ⟨a, b⟩ := p
  obtain ⟨lub_l, lub_r⟩ := lub
  constructor
  · intros a' b' mem
    cases (lub_l a' b' mem)
    assumption
  · intros a' h
    have ⟨res, _⟩ := lub_r a' b ?_
    exact res
    intros a'' b'' mem
    constructor
    exact h _ mem
    have ⟨_, res⟩ := lub_l a'' b'' mem
    exact res

theorem π₂_cont : ωScottContinuous (@Prod.snd α β) := by
  intros D range nonempty dir p lub
  simp [IsLUB, IsLeast, upperBounds, lowerBounds, DirectedOn, Set.range] at *
  obtain ⟨a, b⟩ := p
  obtain ⟨lub_l, lub_r⟩ := lub
  constructor
  · intros b' a' mem
    cases (lub_l a' b' mem)
    assumption
  · intros b' h
    have ⟨_, res⟩ := lub_r a b' ?_
    exact res
    intros a'' b'' mem
    constructor
    have ⟨res, _⟩ := lub_l a'' b'' mem
    exact res
    exact h _ mem

theorem eval_cont : ωScottContinuous (λ ((f, a) : ((α → β) × α)) ↦ f a) := sorry

theorem curry_cont
  {f : (γ × α) → β}
  (hf : ωScottContinuous f)
  : ωScottContinuous (λ c a ↦ f (c, a))
  := sorry

theorem prod_cont
  {f : γ → α} {g : γ → β}
  (hf : ωScottContinuous f) (hg : ωScottContinuous g)
  : ωScottContinuous (λ c ↦ (f c, g c)) := by
  intros D range nonempty dir c lub
  simp [IsLUB, IsLeast, upperBounds, lowerBounds, DirectedOn, Set.range] at *
  obtain ⟨lub_l, lub_r⟩ := lub
  constructor
  · intros c' mem
    constructor <;> [apply hf.monotone; apply hg.monotone] <;> apply lub_l mem
  · intros a b h
    sorry

-- TODO: weirdness about using the direct statement... leaving a placeholder for now
#check fixedPoints.lfp_eq_sSup_iterate
def μ : (α → α) → α := sorry
theorem μ_cont : ωScottContinuous (@μ α) := sorry

end cont_lemmas

variable [DecidableEq X] [Atom X]

@[simp]
def Ty.size : Ty → ℕ
| nat => 0
| arrow l r => l.size + r.size + 1

@[simp]
def Term.size : Term X → ℕ 
| bvar _ => 1
| fvar _ | zero => 0
| lam e1 | fix e1 | pred e1 | succ e1 => e1.size + 1
| app l r => l.size + r.size + 1
| ifzero t₁ t₂ t₃ => t₁.size + t₂.size + t₃.size + 1

-- TODO: might be more helpful to have a version of this with strict inequality under side conditions
omit [DecidableEq X] [Atom X] in
theorem Term.open_size (M : Term X) (k x) : M⟦k ↝ fvar x⟧.size ≤ M.size := by
  revert k
  induction M <;> intros k <;> simp
  case app l r =>
    have := l k
    have := r k
    linarith
  case ifzero a b c =>
    have := @a k
    have := @b k
    have := @c k
    linarith
  all_goals aesop

/-
TODO: I have no idea what this error means!

Could just go away after removing sorry from data...

or maybe because of taking Sigma projections

Cannot derive Der.interp._unary.eq_def
  function expected
    f a
-/

def Der.interp {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : ⟦Γ⟧ → ⟦σ⟧ := 
  match Γ, der with
  | _, zero _ => λ _ => some 0
  | _, succ _ _ f => bot_s ∘ f.interp
  | _, pred _ _ f => bot_p ∘ f.interp
  | _, ifzero _ _ _ _ fa fb fc => bot_cond ∘ (λ Γ ↦ (fa.interp Γ, fb.interp Γ, fc.interp Γ))
  | _, fix _ _ _ f => μ ∘ f.interp
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
    all_goals simp only [open', Term.size, List.length, Ty.size, Der.size] <;> linarith

theorem interp_cont {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : ωScottContinuous der.interp := by
  induction der <;> simp [Der.interp]
  case zero =>
    intros _ _ _ _ _ _
    simp_all only [Set.mem_range, Set.Nonempty.image_const, isLUB_singleton]
  case succ con =>
    exact ωScottContinuous.comp bot_s_cont con 
  case pred con =>
    exact ωScottContinuous.comp bot_p_cont con 
  case ifzero con_a con_b con_c =>
    exact ωScottContinuous.comp bot_cond_cont $ prod_cont con_a (prod_cont con_b con_c)
  case fix con =>
    exact ωScottContinuous.comp μ_cont con  
  case app fl_con fr_con =>
    exact ωScottContinuous.comp eval_cont (prod_cont fl_con fr_con)
  case var => 
    sorry
  case lam xs _ _ _ _ _ ih => 
    apply curry_cont
    exact ih (fresh xs) (fresh_unique xs)

def Nat.toTerm : ℕ → Term X
| 0 => Term.zero
| n+1 => Term.succ n.toTerm

def Term.toNat : Term X → WithBot ℕ 
| zero => 0
| succ n => n.toNat + 1
| _ => ⊥ 

-- TODO: there's weirdness about the contexts, end up with (λ _ ↦ ...), is that right???

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

theorem soundness {M N: Term X} {Γ σ} (der_M : Γ ⊢ M ∶ σ) (der_N : Γ ⊢ N ∶ σ) : der_M.interp = der_N.interp := sorry

theorem adequacy {M : Term X} {Γ} {n : ℕ} (der : Γ ⊢ M ∶ nat) : der.interp = (λ _ ↦ some n) → (M ⇓ M) := sorry
-/
