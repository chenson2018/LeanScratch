import LeanScratch.LocallyNameless.Untyped.Basic
import LeanScratch.LocallyNameless.Untyped.Reduction
import LeanScratch.LocallyNameless.Untyped.Properties
import LeanScratch.LocallyNameless.Untyped.ConfluenceBeta

inductive Ty (K : Type)
  | const : Ty K
  | base : K → Ty K
  | arr : Ty K → Ty K → Ty K
  deriving Repr, DecidableEq

@[simp]
def dom {α β : Type} [DecidableEq α] : List (α × β) → Finset α := λ xs ↦ xs.map Prod.fst |>.toFinset

inductive Ok {α β : Type} [DecidableEq α] : List (α × β) → Prop
| nill : Ok []
| cons (xs : List (α × β)) (a : α) (b : β) : Ok xs → a ∉ dom xs → Ok ((a,b) :: xs)

open Term Ty

inductive Typing {X C K : Type} [DecidableEq X] : List (X × Ty K) → Term X C → Ty K → Prop
| const {Γ c} : Typing Γ (const c) const
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Typing Γ (fvar x) T
| lam (L : Finset X) {Γ t T1 T2} : (∀ x ∉ L, Typing ((x,T1) :: Γ) (t ^ fvar x) T2) → Typing Γ (lam t) (arr T1 T2) 
| app {Γ t t' T1 T2} : Typing Γ t (arr T1 T2) → Typing Γ t' T1 → Typing Γ (app t t') T2

notation:50 Γ " ⊢ " t " ∶" T:arg => Typing Γ t T

variable {X : Type} [DecidableEq X] [Atom X] {M : Type}
variable {C K : Type}

@[simp]
abbrev Ctx (X K) :=  List (X × Ty K)

lemma weakening_strengthened {Γ Δ Γ_Δ Φ : Ctx X K} {t : Term X C} {T} (eq : Γ_Δ  = Γ ++ Δ ) :
  Γ_Δ  ⊢ t ∶ T ->
  Ok (Γ ++ Φ ++ Δ ) ->
  (Γ ++ Φ ++ Δ ) ⊢ t ∶ T := by
  intros h
  revert Γ Δ Φ
  induction h <;> intros Γ Δ Φ eq ok_Γ_Φ_Δ 
  case const => constructor
  case var Γ' x T Γ_ok mem => 
    constructor
    exact ok_Γ_Φ_Δ
    aesop
  case app ih_l ih_r =>
    constructor
    exact ih_l eq ok_Γ_Φ_Δ
    exact ih_r eq ok_Γ_Φ_Δ
  case lam xs _ _ T1 T2 q ih =>
    sorry      

lemma weakening {Γ Δ : Ctx X K} {t : Term X C} {T} :
  Γ ⊢ t ∶ T → 
  Ok (Γ ++ Δ) → 
  Γ ++ Δ ⊢ t ∶ T := by
  intros der ok
  rw [←List.append_nil (Γ ++ Δ)] at *
  exact weakening_strengthened (by aesop) der ok

omit [Atom X] in
lemma typing_lc {Γ : Ctx X K} {t : Term X C} {T} : Γ ⊢ t ∶ T → t.LC := by
  intros h
  induction' h
  case var => constructor
  case lam xs _ _ _ _ _ ih => exact LC.lam xs _ (λ x a ↦ ih x a)
  case app ih_l ih_r => exact LC.app ih_l ih_r
  case const => constructor

lemma typing_subst_strengthened {Γ Δ : Ctx X K} {t s : Term X C} {S T z} :
  (Δ ++ (z, S) :: Γ) ⊢ t ∶ T →
  Γ ⊢ s ∶ S → 
  (Δ ++ Γ) ⊢ (t [z := s]) ∶ T
  := by
  revert T
  induction t <;> intros T weak der <;> simp 
  case app l r ih_l ih_r =>
    cases weak
    case app T1 weak_l weak_r =>
    exact Typing.app (ih_l weak_r der) (ih_r weak_l der)
  case bvar => cases weak
  case fvar z' => 
    cases weak
    case var ok bind =>
      by_cases h : z = z' <;> simp [h]
      · sorry
      · sorry
  case lam t ih =>
    cases weak
    case lam xs T1 T2 mem =>
    apply Typing.lam xs
    intros x free
    sorry
  case const => 
    cases weak
    constructor

lemma typing_subst {Γ : Ctx X K} {t s : Term X C} {S T z} :
  (z, S) :: Γ ⊢ t ∶ T → 
  Γ ⊢ s ∶ S → 
  Γ ⊢ (t [z := s]) ∶ T := by
  intros weak der
  rw [←List.nil_append Γ]
  exact typing_subst_strengthened weak der

theorem preservation_var {Γ : Ctx X K} {xs : Finset X} {m n : Term X C} {T1 T2} :
  (∀ x ∉ xs, (x, T1) :: Γ ⊢ m ^ fvar x ∶ T2) → 
  Γ ⊢ n ∶ T1 → Γ ⊢ m ^ n ∶ T2
  := by
  intros mem der
  have ⟨fresh, free⟩ := atom_fresh_for_set $ xs ∪ m.fv
  simp at free
  obtain ⟨f1, f2⟩ := free
  rw [subst_intro fresh] 
  exact typing_subst (mem fresh f1) der
  aesop
  exact typing_lc der

theorem preservation {Γ : Ctx X K} {t t' : Term X C} {T} : Γ ⊢ t ∶ T → (t ⇢β t') → Γ ⊢ t' ∶ T := by
  intros der
  revert t'
  induction der <;> intros t' step
  case var => cases step
  case const => cases step
  case lam xs Γ t T1 T2 mem ih =>
    cases step
    case ξ xs' t' mem' =>
      apply Typing.lam (xs ∪ xs')
      intros x union
      simp at union
      obtain ⟨u1, u2⟩ := union
      exact ih x u1 (mem' x u2)
  case app Γ s s' T1 T2 der_l der_r ih_l ih_r =>
    cases step
    case ξₗ step => exact Typing.app der_l (ih_r step)
    case ξᵣ step _ => exact Typing.app (ih_l step) der_r
    case β t t_lam lc_s' =>
      cases der_l
      case lam xs mem => exact preservation_var mem der_r

theorem preservation_redex {Γ : Ctx X K} {t t' : Term X C} {T} : Γ ⊢ t ∶ T → (t ↠β t') → Γ ⊢ t' ∶ T := by
  intros der redex
  induction redex using Relation.ReflTransGen.trans_induction_on
  case ih₁ => exact der
  case ih₂ ih => exact preservation der ih
  case ih₃ ih ih' => exact ih' (ih der)

-- TODO: nice way to write this in terms of Confluence??
theorem preservation_confluence {Γ : Ctx X K} {a b c : Term X C} {T} :
  Γ ⊢ a ∶ T → (a ↠β b) → (a ↠β c) → 
  ∃ d, (b ↠β d) ∧ (c ↠β d) ∧ Γ ⊢ d ∶ T := by
  intros der ab ac
  have ⟨d, bd, cd⟩ := confluence_beta ab ac
  exists d
  refine ⟨bd, cd, ?_⟩
  apply preservation_redex
  exact der
  trans
  exact ab
  exact bd

-- TODO: maybe bundling like this works???
def to_ty : Ctx X K → Ty K := sorry

inductive ty_morphism : Ty K → Ty K → Prop
| der {t : Term X C} {Γ T} : Γ ⊢ t ∶ T → ty_morphism (to_ty Γ) T
