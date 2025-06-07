import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep
import LeanScratch.PCF.SmallStep
import LeanScratch.LocallyNameless.STLC.Context

import Mathlib.Order.OmegaCompletePartialOrder

open Term Ty Atom

variable {X : Type}

/-- definition 2.3, the actual derivations -/
inductive Der [DecidableEq X] : List (X × Ty) → Term X → Ty → Type
| zero (Γ)   : Der Γ zero nat
| succ (Γ M) : Der Γ M nat → Der Γ (succ M) nat
| pred (Γ M) : Der Γ M nat → Der Γ (pred M) nat
| ifzero (Γ M N₁ N₂) : Der Γ M nat → Der Γ N₁ nat → Der Γ N₂ nat → Der Γ (ifzero M N₁ N₂) nat
| fix (Γ M σ) : Der Γ M (σ ⤳ σ) → Der Γ (fix M) σ
| app (Γ M N σ τ) : Der Γ M (σ ⤳ τ) → Der Γ N σ → Der Γ (app M N) τ
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Der Γ (fvar x) T
| lam (L : Finset X) {Γ t σ τ} : (∀ x ∉ L, Der ((x,σ) :: Γ) (t ^ fvar x) τ) → Der Γ (lam t) (σ ⤳ τ) 

notation:50 Γ " ⊢ " t " ∶" T => Der Γ t T

/-
theorem add_n_type (n : Term X) (num : Numeral n) [DecidableEq X] : [] ⊢ add_n n ∶ nat ⤳ nat := by
  simp only [add_n]  
  apply Der.fix
  apply Der.lam ∅
  intros f f_mem
  apply Der.lam {f}
  intros y y_mem
  simp
  have ok : Ok [(y, nat), (f, nat ⤳ nat)] := by
    repeat constructor
    all_goals aesop
  constructor
  constructor
  exact ok
  aesop
  · induction num <;> simp
    exact Der.zero [(y, nat), (f, nat ⤳ nat)]
    case a.a.succ m _ ih => exact Der.succ [(y, nat), (f, nat ⤳ nat)] (m⟦1 ↝ fvar f⟧⟦0 ↝ fvar y⟧) ih
  · constructor
    refine Der.app [(y, nat), (f, nat ⤳ nat)] (fvar f) (fvar y).pred nat nat ?_ ?_
    constructor
    exact ok
    aesop
    constructor
    constructor
    exact ok
    aesop
-/

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

theorem WithBot.coe_nle_bot {α : Type} (a : α) : ¬ a ≤ (⊥ : WithBot α) := by
  simp_all only [instWithBot.le_flat, coe_ne_bot, or_self, not_false_eq_true]

theorem WithBot.coe_nle_coe {α : Type} (a₁ a₂ : α) (h : a₁ ≠ a₂) : ¬ a₁ ≤ (a₂ : WithBot α) := by
  simp_all only [ne_eq, instWithBot.le_flat, coe_ne_bot, coe_inj, or_self, not_false_eq_true]

theorem WithBot.coe_le_coe_iff_eq {α : Type} (a₁ a₂ : α) : a₁ = a₂ ↔ a₁ ≤ (a₂ : WithBot α) := by
  simp_all only [instWithBot.le_flat, coe_ne_bot, coe_inj, false_or]

theorem WithBot.coe_le_iff_eq {α : Type} (a₁ : α) (a₂ : WithBot α) : a₁ = a₂ ↔ a₁ ≤ a₂ := by
  simp_all only [instWithBot.le_flat, coe_ne_bot, false_or]

theorem WithBot.neq_bot_ex_coe {α : Type} {a : WithBot α} : a ≠ ⊥ → ∃ val, a = some val := by
  intros neq
  induction a <;> aesop

theorem Withbot.coe_nle {α : Type} (a : α) (a' : WithBot α) : ¬ a ≤ a' ∨ a = a' := by
  cases a'
  case bot =>
    left
    exact WithBot.coe_nle_bot a
  case coe a' =>
    by_cases h : (a = a')
    · subst h
      simp_all only [instWithBot.le_flat, le_refl, not_true_eq_false, or_true]
    · left
      exact WithBot.coe_nle_coe a a' h

/-- once a chain has a non-⊥ value, that must be terminal -/
theorem WithBot.chain_terminal_val {α} {chain : Chain (WithBot α)} {i : ℕ} {a : α} : 
    chain i = ↑a → (∀ i', i ≤ i' → chain i' = ↑a) := by
  intros eq i' leq
  have mono := chain.monotone leq
  cases (Withbot.coe_nle a (chain i')) <;> aesop

def const_chain {α} : Chain (WithBot α) where
  toFun _ := ⊥
  monotone' := monotone_const

def nonconst_chain {α} (val : α) (sup_i : ℕ) : Chain (WithBot α) where
  toFun i := if i < sup_i then ⊥ else ↑val
  monotone' := by
    simp [Monotone]
    intros
    split
    apply WithBot.bot_le
    split
    linarith
    rfl

-- TODO: I need to prove that these are the only options.... maybe a better way to state this
theorem chain_const? {α} (chain : Chain (WithBot α)) : chain = const_chain ∨ ∃ val switch, chain = nonconst_chain val switch := sorry

instance WithBot.ωcpo_flat (α : Type) [DecidableEq α] : OmegaCompletePartialOrder (WithBot α) where
  ωSup chain := sorry
  le_ωSup chain i := sorry
  ωSup_le chain x bound := sorry
--  ωSup chain := if chain 0 = ⊥ ∧ chain 1 ≠ ⊥ then chain 1 else chain 0
--  le_ωSup chain i := by
--    by_cases c₀ : chain 0 = ⊥ <;> simp [c₀]
--    · by_cases c₁ : chain 1 = ⊥ <;> simp [c₁]
--      · sorry
--      · cases i
--        case neg.zero =>
--          rw [c₀]
--          apply WithBot.bot_le
--        case neg.succ i' =>
--          have ⟨n, eq⟩ :=  WithBot.neq_bot_ex_coe c₁
--          rw [eq,  WithBot.chain_terminal_val eq (i'+1) (by aesop)]
--    · have ⟨n, eq⟩ :=  WithBot.neq_bot_ex_coe c₀
--      have const := WithBot.chain_terminal_val eq
--      simp_all only [coe_ne_bot, not_false_eq_true, zero_le, le_refl, forall_const]

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
    --exists (σ_ty × tl_ty)
    exists (tl_ty × σ_ty)
    exact Prod.instOmegaCompletePartialOrder

-- I am astounded this worked so easily
instance (ty : Ty) : OmegaCompletePartialOrder (ty.interp.fst) := ty.interp.snd
instance (Γ : List (X × Ty)) : OmegaCompletePartialOrder (Γ.interp.fst) := Γ.interp.snd

def bot_s : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| n => n + 1

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
    apply WithBot.bot_le
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
def Term.size : Term X → ℕ 
| bvar _ => 1
| fvar _ | zero => 0
| lam e1 | fix e1 | pred e1 | succ e1 => e1.size + 1
| app l r => l.size + r.size + 1
| ifzero t₁ t₂ t₃ => t₁.size + t₂.size + t₃.size + 1

theorem Term.open_size {M : Term X} {x} : M⟦0 ↝ fvar x⟧.size < M.size := sorry    

def Der.interp {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : (⟦Γ⟧ → ⟦σ⟧) := 
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
  -- TODO: this is problematic for termination
  | _, @lam _ _ xs _ M _ _ ih => by
      have der_ih := ih (fresh xs) (fresh_unique xs)
      sorry
    --(λ Γ σ ↦  (ih (fresh xs) (fresh_unique xs)).interp (Γ, σ))
--  termination_by 
--    Γ.length + M.size
--  decreasing_by
--    all_goals simp only [Term.size, List.length]
--    linarith
--    linarith
--    linarith
--    linarith
--    linarith
--    linarith
--    linarith
--    linarith
--    linarith
    
    
--    match Γ with
--    | (x',σ') ::tl => by
--        simp only [List.interp]
--        refine if h : x = x' then ?_ else ?_
--        · have eq : σ' = σ := by
--            rw [h] at mem
--            exact Ok.mem_head_eq ok mem
--          rw [eq]
--          exact Prod.snd
--        · refine (Der.var ?ok $ Ok.mem_head_neq ok mem h).interp ∘ Prod.fst
--          cases ok
--          assumption

/-
    case var Γ x σ ok mem => 
      induction mem
      case head => refine ⟨Prod.snd, π₂_cont⟩
      case tail Γ p Γ' mem' ih=>
        obtain ⟨x', σ'⟩ := p
        have ok' : Ok Γ' := by cases ok; assumption
        have ⟨f, fcon⟩ := ih ok'
        exact ⟨f ∘ Prod.fst, ωScottContinuous.comp fcon π₁_cont⟩
-/

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
