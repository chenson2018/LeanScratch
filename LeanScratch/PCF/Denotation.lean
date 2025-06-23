import LeanScratch.PCF.Typing
import LeanScratch.PCF.FlatCPO
import LeanScratch.PCF.Continuity

open OmegaCompletePartialOrder

-- check that we ark picking up the right instances
#synth LE (WithBot ℕ)
#synth LT (WithBot ℕ)
#synth OrderBot (WithBot ℕ)
#synth Preorder (WithBot ℕ)
#synth PartialOrder (WithBot ℕ)

-- weird that this is added back in...
attribute [-instance] WithBot.conditionallyCompleteLattice
attribute [-instance] WithBot.instSupSet
--#synth SupSet (WithBot ℕ)

set_option trace.Meta.synthInstance true in
#synth OmegaCompletePartialOrder (WithBot ℕ)


open Term Ty Atom

variable {X : Type} [DecidableEq X] [Atom X]


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

/-
noncomputable instance TySupSet (ty : Ty) : SupSet ty.interp := by
   induction ty <;> simp [Ty.interp] <;> infer_instance
-/

noncomputable instance TyOrderBot (ty : Ty) : OrderBot ty.interp := by
  induction ty <;> simp [Ty.interp] <;> infer_instance 

noncomputable def Der.interp {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : Γ.interp → σ.interp := 
  match Γ, der with
  | _, zero _ => λ _ => some 0
  | _, succ _ _ f => bot_s ∘ f.interp
  | _, pred _ _ f => bot_p ∘ f.interp
  | _, ifzero _ _ _ _ fa fb fc => bot_cond ∘ (λ Γ ↦ (fa.interp Γ, fb.interp Γ, fc.interp Γ))
  | _, fix _ _ _ f => sorry
      -- TODO: this is the old version when I was deriving from CPO
      -- I'd like to use `OmegaCompletePartialOrder.fixedPoints.iterateChain`
      -- but this also needs a monotone proof?
      -- how do I seperate out the data now???
      --exact (λ f ↦ ⨆ (n : ℕ), f^[n] ⊥) ∘ f.interp
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

-- TODO: not sure where to place termination_by ...
-- TODO: maybe make the continuity an argument in order to seperate this?
noncomputable def Der.hom {M : Term X} {Γ σ} (der : Γ ⊢ M ∶ σ) : Γ.interp →𝒄 σ.interp where
  toFun := 
    match Γ, der with
    -- TODO: I think I have to bundle like this to do the fix case...
    | _, fix Γ _ _ f => by
        refine ?_ ∘ (hom f).toFun
        intros g
        refine ωSup ?_
        refine fixedPoints.iterateChain {toFun := g, monotone' := ?_} ⊥ (by apply OrderBot.bot_le)
        -- TODO: need to prove the type and list interpretations are monotone???
        sorry
    | _, zero _ => λ _ => some 0
    | _, succ _ _ f => bot_s ∘ f.hom
    | _, pred _ _ f => bot_p ∘ f.hom
    | _, ifzero _ _ _ _ fa fb fc => bot_cond ∘ (λ Γ ↦ (fa.hom Γ, fb.hom Γ, fc.hom Γ))
    | _, app _ _ _ _ _ fl fr => (λ (f, a) ↦ f a) ∘ (λ γ ↦ (fl.hom γ, fr.hom γ))
    | (x',σ') ::Γ', @var _ _ _ x _ ok mem => by
          simp only [List.interp]
          refine if h : x = x' then ?_ else ?_
          · have eq : σ' = σ := by
              rw [h] at mem
              exact Ok.mem_head_eq ok mem
            rw [eq]
            exact Prod.snd
          · refine (Der.var ?ok $ Ok.mem_head_neq ok mem h).hom ∘ Prod.fst
            cases ok
            assumption
    | _, @lam _ _ xs Γ' M σ τ ih => by
        have i := (ih (fresh xs) (fresh_unique xs)).hom
        exact (λ Γ σ ↦  i (Γ, σ))
  monotone' := sorry
  map_ωSup' := sorry

theorem soundness_hom {M N: Term X} {Γ σ} (der_M : Γ ⊢ M ∶ σ) (der_N : Γ ⊢ N ∶ σ) (step : M ⇓ N) : der_M.hom = der_N.hom := by
  induction step
  case fix ih => sorry
    --cases der_M
    --next M =>
    --  simp [Der.hom, Der.interp]
    --  have Mi := ih (Der.app _ _ _ _ _ M (Der.fix _ _ _ M)) der_N
    --  simp [Der.hom, Der.interp] at Mi
    --  rw [←Mi]
    --  ext
    --  next γ =>
    --    rw [Function.comp_apply, Function.comp_def]
    --    simp
    --    have h : ∃ f : σ.interp →𝒄 σ.interp, M.interp γ = ⇑f := sorry
    --    have ⟨f, eq⟩ := h
    --    rw [eq]
    --    -- TODO: this is really close, but not the right ωCPO instance...
    --    --#check cpo_fix f
    --    sorry
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
