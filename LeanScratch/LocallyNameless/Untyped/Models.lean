import LeanScratch.LocallyNameless.Untyped.Basic
import LeanScratch.LocallyNameless.Untyped.Reduction
import LeanScratch.LocallyNameless.Untyped.Beta

open Term

/-- notation typeclass for syntactic interpretation -/
class SyntaxAppStruct (atom : Type) (M : Type) [Mul M] where
  interp : Term atom M → (atom → M) → M

notation:90 "⟦" t "⟧" ρ:arg => SyntaxAppStruct.interp t ρ

/-- remap some free variable of a valuation `atom → M` -/
def fv_remap {M atom : Type} [DecidableEq atom] (ρ : atom → M) (x' : atom) (a : M) : atom → M := λ x ↦ if x' = x then a else ρ x

class SyntaxApp (atom : Type) [DecidableEq atom] [Atom atom] (M : Type) [Mul M] extends SyntaxAppStruct atom M where
  -- doesn't make sense to interpret bound variables, they should sink to the same value
  interp_bvar : ∃ m, ∀ (ρ : atom → M) i, ⟦bvar i⟧ρ = m
  interp_fvar  (ρ : atom → M) (x : atom) : ⟦fvar x⟧ρ = ρ x
  interp_const (ρ : atom → M) (m : M) : ⟦const m⟧ρ = m
  interp_app   (ρ : atom → M) (P Q)   : ⟦app P Q⟧ρ = ⟦P⟧ρ * ⟦Q⟧ρ
  interp_free  (ρ ρ' : atom → M) (P : Term atom M) : (∀ x ∈ P.fv, ρ x = ρ' x) → ⟦P⟧ρ = ⟦P⟧ρ'
  interp_lam   (ρ : atom → M) (P m) :
    let fresh := atom_fresh_for_set P.fv |>.choose;
    ⟦lam P⟧ρ * m = ⟦open' P (fvar fresh)⟧ (fv_remap ρ fresh m)


def Term.sat {X M} [Mul M] [DecidableEq X] [Atom X] [SyntaxApp X M] (A B : Term X M) := ∀ ρ, ⟦ A ⟧ ρ = ⟦ B ⟧ ρ 
notation:100 M " ⊨ " A " ~ " B:arg => @Term.sat _ M _ _ _ _ A B

class SyntaxAlgebra (atom : Type) [DecidableEq atom] [Atom atom] (M : Type) [Mul M] extends SyntaxApp atom M where
  interp_eq (P Q : Term atom M) : (P ≈β Q) → (M ⊨ P ~ Q)

class SyntaxModel (atom : Type) [DecidableEq atom] [Atom atom] (M : Type) [Mul M] extends SyntaxApp atom M where
  interp_ext (P Q : Term atom M) (a : M) (x : atom) (ρ : atom → M): 
    ⟦P⟧(fv_remap ρ x a) = ⟦Q⟧(fv_remap ρ x a) → 
    ⟦lam $ bind_free 0 x P⟧ρ = ⟦lam $ bind_free 0 x Q⟧ρ

open SyntaxApp SyntaxAlgebra SyntaxModel

section model_to_algrbra

variable {atom M : Type} [DecidableEq atom] [Atom atom] [Mul M] [SyntaxModel atom M]
variable (ρ : atom → M)

@[simp]
def φ (P Q : Term atom M) := ∀ x, ⟦P [x := Q]⟧ρ = ⟦P⟧(fv_remap ρ x (⟦Q⟧ρ))

lemma i (z : atom) (P : Term atom M) (h : z ∉ P.fv) : φ ρ P (fvar z)
  := sorry

lemma ii (P Q : Term atom M) : φ ρ P Q → φ ρ (lam P) Q := sorry

lemma iii (P Q : Term atom M) : φ ρ P Q := by
  simp
  revert Q
  induction P <;> intros Q x
  case const m =>
    simp [subst]
    rw [interp_const, interp_const]
  case bvar i =>
    simp [subst]
    have ⟨m, h⟩ := @interp_bvar atom _ _ M _ _
    aesop
  case fvar i =>
    simp [subst]
    by_cases h : x = i <;> simp [h]
    · rw [interp_fvar]
      simp [fv_remap]
    · rw [interp_fvar]
      rw [interp_fvar]
      simp [fv_remap]
      simp [h]
  case app l r ih_l ih_r =>
    simp [subst]
    repeat rw [interp_app]
    aesop
  case lam T ih =>
    simp [subst]
    have h := interp_lam ρ T (⟦Q⟧ρ)
    simp at h
    sorry

end model_to_algrbra
