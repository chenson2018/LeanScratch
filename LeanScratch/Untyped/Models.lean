import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Shifting
import LeanScratch.Untyped.Reduction
import LeanScratch.Untyped.Beta

def val_shift {M} (ρ : ℕ → M) (x' : ℕ) (a : M) : ℕ → M := λ x ↦ if x' = x then a else ρ x

class SyntaxAppStruct (M : Type) [Mul M] where
  interp : Term M → (ℕ → M) → M

notation:90 "⟦" t "⟧" ρ:arg => SyntaxAppStruct.interp t ρ

-- TODO: did I quantify ρ correctly here???
open Term in
class SyntaxApp (M : Type) [Mul M] extends SyntaxAppStruct M where
  interp_var   (ρ : ℕ → M) (x : ℕ) : ⟦var x⟧ρ = ρ x
  interp_const (ρ : ℕ → M) (m : M) : ⟦const m⟧ρ = m
  interp_app   (ρ : ℕ → M) (P Q)   : ⟦app P Q⟧ρ = ⟦P⟧ρ * ⟦Q⟧ρ
  -- TODO: not sure about shifting
  interp_abs   (ρ : ℕ → M) (P m)   : ⟦{{{ λ . ~P }}}⟧ρ * m = ⟦P⟧(val_shift ρ 0 m)
  -- TODO a condition about free variables...
  interp_free  (ρ ρ' : ℕ → M) (P)  : ρ = ρ' → ⟦P⟧ρ = ⟦P⟧ρ'

def Term.sat_under (M) [Mul M] [SyntaxApp M] (A B : Term M) (ρ : ℕ → M) := ⟦ A ⟧ ρ = ⟦ B ⟧ ρ 
def Term.sat (M) [Mul M] [SyntaxApp M] (A B : Term M) := ∀ ρ, ⟦ A ⟧ ρ = ⟦ B ⟧ ρ

notation:100 M ",," ρ:arg " ⊨ " A " ~ " B => Term.sat_under M A B ρ
notation:100 M " ⊨ " A " ~ " B:arg => Term.sat M A B

class SyntaxAlg (M : Type) [Mul M] extends SyntaxApp M where
  beta_sat (P Q : Term M) : P ≈β Q → M ⊨ P ~ Q

class SyntaxModel (M : Type) [Mul M] extends SyntaxApp M where
  -- TODO : shifting!
  ξ (P Q : Term M) (m : M) (ρ) : ⟦P⟧ρ = ⟦Q⟧ρ → ⟦{{{ λ . ~P}}}⟧ρ  = ⟦{{{ λ . ~Q}}}⟧ρ

class CPO_Reflexive (D: Type) [OmegaCompletePartialOrder D] (F : D → (D →𝒄 D)) (G : (D →𝒄 D) → D) where
  reflexive : G ∘ F = id

def Term.to_cpo 
  {D : Type}
  [OmegaCompletePartialOrder D]
  (F : D → (D →𝒄 D))
  (G : (D →𝒄 D) → D)
  [CPO_Reflexive D F G]
  [Mul D]
  (t : Term D)
  (ρ : ℕ → D)
  : D
  := 
  match t with
  | const d => d
  | var x => ρ x
  | app l r => (l.to_cpo F G ρ) * (r.to_cpo F G ρ)
  | abs M => (G {toFun := (λ d ↦ M.to_cpo F G (val_shift ρ 0 d)), monotone' := sorry, map_ωSup' := sorry})

set_option synthInstance.checkSynthOrder false in
instance (D : Type) [OmegaCompletePartialOrder D] (F G) [CPO_Reflexive D F G] [Mul D] : SyntaxModel D where
  interp := Term.to_cpo F G
  interp_var := sorry
  interp_const := sorry
  interp_app := sorry
  interp_abs := sorry
  interp_free := sorry
  ξ := sorry

-- below is the combinator approach earlier in the chapter I did first the above
-- "syntactical" approach seems cleaner, so I might just delete it eventually
-- the above still does not cover the general ccc construction
-------------------------------------------------------------------------
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- inductive AppTerm (M : Type)
-- | const (m : M) : AppTerm M
-- | var (x : ℕ) : AppTerm M
-- | app (l r : AppTerm M) : AppTerm M
-- 
-- open AppTerm
-- 
-- instance (M : Type) : Mul (AppTerm M) where
--   mul l r := app l r

/-
-- should try the new binding change to implicit here...
def AppTerm.val {M} [Mul M] (t : AppTerm M) (ρ : ℕ → M) : M := 
  match t with
  | const m => m
  | app A B => (A.val ρ) * (B.val ρ)
  | var x => ρ x

def AppTerm.atrue_under (M) [Mul M] (A B : AppTerm M) (ρ : ℕ → M) := (A.val ρ) = (B.val ρ)
notation:39 M ",," ρ:arg "⊨" A "~" B => AppTerm.atrue_under M A B ρ

@[simp]
def AppTerm.atrue (M) [Mul M] (A B : AppTerm M) := ∀ ρ, (M ,, ρ ⊨ A ~ B)
notation:39 M "⊨" A "~" B => AppTerm.atrue M A B

-- A [x := B]
-- I write the args in a weird order to make the dot notation less confusing
def AppTerm.sub {M} (A : AppTerm M) (x : ℕ) (B : AppTerm M) : AppTerm M := 
  match A with
  | var x' => if x = x' then B else var x'
  | app l r => (l.sub x B) * (r.sub x B)
  | const m => const m

notation:min A "[" x ":=" B "]" => AppTerm.sub A x B

def val_shift {M} (ρ : ℕ → M) (x' : ℕ) (a : M) : ℕ → M := λ x ↦ if x' = x then a else ρ x

lemma AppTerm.sub_val {M} [Mul M] (x : ℕ) (A B : AppTerm M) (ρ : ℕ → M) 
  : (A [x := B]).val ρ = A.val (val_shift ρ x (B.val ρ)) := by
  induction A <;> simp [sub, val]
  case var x' => by_cases h : x = x' <;> simp [h, val_shift, val]
  case app l r ih_l ih_r => rw [ih_l, ih_r]
    
lemma AppTerm.sub_atrue {M A A' B B'} [Mul M] (x : ℕ) (ta : M ⊨ A ~ A') (tb : M ⊨ B ~ B') 
  : atrue M (A [x := B]) (A' [x := B']) := by
  simp [atrue, atrue_under] at *
  intros ρ
  rw [sub_val, sub_val, ta, tb]

-- TODO: these classes should probably all extend each other, would be more readable...
class CombAlg (M : Type) [Mul M] where
  k : M
  s : M
  k_reduce (x y : M) : k * x * y  = x
  s_reduce (x y z : M) : s*x*y*z = x*z*(y*z)

open CombAlg

def AppTerm.K {M : Type} [Mul M] [CombAlg M] : AppTerm M := const k
def AppTerm.S {M : Type} [Mul M] [CombAlg M] : AppTerm M := const s
def AppTerm.I {M : Type} [Mul M] [CombAlg M] : AppTerm M := S * K * K

def AppTerm.I_id {M : Type} [Mul M] [CombAlg M] (x : AppTerm M) : M ⊨ I * x ~ x := by
  intros ρ
  simp [I, S, K, val, atrue_under]
  rw [s_reduce, k_reduce]

-- TODO: shifting here???
def AppTerm.abs {M : Type} [Mul M] [CombAlg M] (A : AppTerm M) : AppTerm M := 
  match A with
  | var _ => I
  | P * Q => S * P.abs * Q.abs
  | P => K * P

class CombAlgHomo {M₁ M₂} [Mul M₁] [Mul M₂] [CombAlg M₁] [CombAlg M₂] (φ : M₁ → M₂) where
  preserve_app (x y) : φ (x * y) = φ x * φ y
  preserve_s : φ s = s
  preserve_k : φ k = k

open CombAlgHomo

def AppTerm.homo {M₁ M₂} (φ : M₁ → M₂) : AppTerm M₁ → AppTerm M₂
| var x => var x
| l * r => (l.homo φ) * (r.homo φ)
| const m => const (φ m)

theorem AppTerm.homo_val {M₁ M₂} [Mul M₁] [Mul M₂] [CombAlg M₁] [CombAlg M₂] (φ : M₁ → M₂) [CombAlgHomo φ] (P Q : AppTerm M₁)
  : ∀ ρ, φ (P.val ρ) = (P.homo φ).val (φ ∘ ρ) := by
  induction P <;> simp [val, homo]
  case app l r ih_l ih_r =>
    intros ρ
    -- odd metavariable thing here...
    have eq : φ (l.val ρ * r.val ρ) = φ (l.val ρ) * φ (r.val ρ) := preserve_app (l.val ρ) (r.val ρ)
    rw [eq, ih_l, ih_r]

-- TODO: need to also state this in term of no variables
theorem AppTerm.homo_entail 
  {M₁ M₂} [Mul M₁] [Mul M₂] [CombAlg M₁] [CombAlg M₂] 
  {φ : M₁ → M₂} [CombAlgHomo φ] (sur : Function.Surjective φ)
  {P Q : AppTerm M₁}
  : (M₁ ⊨ P ~ Q) → (M₂ ⊨ (P.homo φ) ~ (Q.homo φ)) := by
  simp [Function.Surjective] at sur
  simp [atrue]
  intros entail_M₁ ρ'
  have homo_entail := AppTerm.homo_val φ P Q
  sorry

open Term

-- TODO: shifting here???
-- I don't want to replicate all that, plus intrinsic is maybe better if I want to relate to simple types
def Term.to_app {M} [Mul M] [CombAlg M] : Term M → AppTerm M
| var x => AppTerm.var x
| const m => AppTerm.const m
| app l r => l.to_app * r.to_app
| abs M => M.to_app.abs

-- TODO: shifting here???
-- TODO: notation or non-conflicting names
def AppTerm.to_lam {M} [Mul M] [DecidableEq M] [CombAlg M] : AppTerm M → Term M
| var x => Term.var x
| const m => if m = k then 
               Term.abs (Term.abs (Term.var 1))
             else if m = s then
               Term.abs $
               Term.abs $
               Term.abs $
               
               Term.app
                (Term.app (Term.var 2) (Term.var 0))
                (Term.app (Term.var 1) (Term.var 0))
             else 
               Term.const m
| app l r => Term.app (l.to_lam) (r.to_lam)

def Term.val {M} [Mul M] [DecidableEq M] [CombAlg M] (t : Term M) (ρ : ℕ → M) : M := t.to_app.val ρ

def Term.atrue_under (M) [Mul M] [DecidableEq M] [CombAlg M] (t t' : Term M) (ρ : ℕ → M) := (t.val ρ) = (t'.val ρ)
notation:39 M ",," ρ:arg "⊨'" A "~" B => Term.atrue_under M A B ρ

@[simp]
def Term.atrue (M) [Mul M] [DecidableEq M] [CombAlg M] (t t' : Term M) := ∀ ρ, Term.atrue_under M t t' ρ
notation:39 M "⊨'" A "~" B => Term.atrue M A B

-- TODO: I think this should be using =β
class LambdaAlgebra (M) [Mul M] [DecidableEq M] [CombAlg M] where
  transfer {A B : AppTerm M} : (A.to_lam = B.to_lam) → (M ⊨ A ~ B)

-- TODO: lemma 5.2.3 seems like a good test of the definitions...
lemma lem_5_2_3 {M : Type} [Mul M] [DecidableEq M] [CombAlg M] : 
  ((∀ t t', t = t' → M ⊨' t ~ t') ∧ (M ⊨ K.to_lam.to_app ~ K) ∧ (M ⊨ S.to_lam.to_app ~ S)) ↔ LambdaAlgebra M
  := sorry

class LambdaModel (M) [Mul M] [DecidableEq M] [CombAlg M] [LambdaAlgebra M] where
  meyer_scott (A B : AppTerm M) : (∀ x, (M ⊨ A * x ~ B * x)) → (M ⊨ (S * (K * I)) * A ~ (S * (K * I)) * B)

-- TODO: there's some more here until the category theory part, but I'll wait until the above is solid..
-- I think OmegaCompletePartialOrder picks up equivalents to the Scott topology we want

-- TODO not being very thoughtful here about API, just want to get it down first...
class CPO_Reflexive (D: Type) [OmegaCompletePartialOrder D] (F : D → (D →𝒄 D)) (G : (D →𝒄 D) → D) where
  reflexive : G ∘ F = id

-- chosing constants over D so I don't have to redefine terms...
-- TODO: where exactly is this used below???
-- I think maybe he means this is the function described in 5.3
-- but how does this syntactical model fit in with the above definitions??
def Term.to_cpo 
  {D : Type} [OmegaCompletePartialOrder D] (F G) [CPO_Reflexive D F G] [Mul D] [DecidableEq D] [CombAlg D]
  (t : Term D)
  (ρ : ℕ → D)
  : D
  := 
  match t with
  | const d => d
  | var x => ρ x
  | app l r => (l.to_cpo F G ρ) * (r.to_cpo F G ρ)
  | abs M => (G {toFun := (λ d ↦ M.val (val_shift ρ 0 d)), monotone' := sorry, map_ωSup' := sorry})

set_option synthInstance.checkSynthOrder false in
instance {D : Type} [cpo : OmegaCompletePartialOrder D] (F G) [CPO_Reflexive D F G] : Mul D where 
  mul x y := F x y

instance {D : Type} [cpo : OmegaCompletePartialOrder D] (F G) [CPO_Reflexive D F G] : CombAlg D where
  k := sorry
  s := sorry
  k_reduce := sorry
  s_reduce := sorry

instance {D : Type} [cpo : OmegaCompletePartialOrder D] (F G) [CPO_Reflexive D F G] [DecidableEq D] : LambdaAlgebra D where
  transfer := sorry

-- TODO: the last part here is "arbitrary" CCCs with reflexive objects
-- going to wait until the above is settled to try stating it
-/
