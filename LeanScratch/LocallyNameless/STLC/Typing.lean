import LeanScratch.LocallyNameless.Untyped.Basic
import LeanScratch.LocallyNameless.Untyped.Reduction
import LeanScratch.LocallyNameless.Untyped.Properties
import LeanScratch.LocallyNameless.Untyped.ConfluenceBeta

inductive Ty (K : Type)
  | const : Ty K
  | unit : Ty K
  | base : K → Ty K
  | arr : Ty K → Ty K → Ty K
  | prod : Ty K → Ty K → Ty K
  deriving Repr, DecidableEq

section ok

variable {α β : Type} [DecidableEq α]

@[simp]
def dom : List (α × β) → Finset α := λ xs ↦ xs.map Prod.fst |>.toFinset

inductive Ok : List (α × β) → Prop
| nil : Ok []
| cons (xs : List (α × β)) (a : α) (b : β) : Ok xs → a ∉ dom xs → Ok ((a,b) :: xs)

theorem List.perm_dom  {xs ys : List (α × β)} (h : xs.Perm ys) (a : α) : a ∉ dom xs → a ∉ dom ys := by 
  induction h <;> aesop

theorem Ok.perm  {xs ys : List (α × β)} (h : xs.Perm ys) : Ok xs → Ok ys := by
  induction h <;> intros ok_xs
  case nil => exact Ok.nil
  case cons pair xs' ys' perm ih =>
    cases ok_xs
    case cons a b ok_xs' mem =>
      observe ok_ys' : Ok ys'
      constructor
      exact ih ok_xs'
      exact List.perm_dom perm a mem
  case swap p1 p2 xs' =>
    cases ok_xs
    case cons a1 b1 ok_xs dom_a1 =>
    cases ok_xs
    case cons a2 b2 ok_xs dom_a2 =>
      constructor
      constructor
      exact ok_xs
      aesop
      aesop
  case trans a b c p_ab p_bc ih_ab ih_bc => exact ih_bc (ih_ab ok_xs)

end ok

open Term Ty

inductive Typing {X C K : Type} [DecidableEq X] : List (X × Ty K) → Term X C → Ty K → Prop
| const {Γ c} : Typing Γ (const c) const
| unit {Γ} : Typing Γ unit unit
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Typing Γ (fvar x) T
| lam (L : Finset X) {Γ t T1 T2} : (∀ x ∉ L, Typing ((x,T1) :: Γ) (t ^ fvar x) T2) → Typing Γ (lam t) (arr T1 T2) 
| app {Γ t t' T1 T2} : Typing Γ t (arr T1 T2) → Typing Γ t' T1 → Typing Γ (app t t') T2
| prod {Γ t t' T1 T2} : Typing Γ t T1 → Typing Γ t' T2 → Typing Γ (pair t t') (prod T1 T2)
| proj {Γ t T1 T2 p} : Typing Γ t (prod T1 T2) → Typing Γ (proj p t) (if p = Proj.L then T1 else T2)

notation:50 Γ " ⊢ " t " ∶" T:arg => Typing Γ t T

variable {X : Type} [DecidableEq X] [Atom X] {M : Type}
variable {C K : Type}

@[simp]
abbrev Ctx (X K) :=  List (X × Ty K)

omit [Atom X] in
theorem Typing.perm {Γ Δ : Ctx X K} {t : Term X C} {T} (perm : Γ.Perm Δ) : (Γ ⊢ t ∶ T) → (Δ ⊢ t ∶ T) := by
  intros der
  revert Δ
  induction der <;> intros Δ perm
  case var Γ_ok mem =>
    constructor
    exact Ok.perm perm Γ_ok
    exact (List.Perm.mem_iff perm).mp mem
  case const => constructor
  case unit => constructor
  case lam xs Γ t T1 T2 o ih =>
    apply Typing.lam xs
    intros x mem
    apply ih 
    exact mem
    exact List.Perm.cons (x, T1) perm
  case app ih_l ih_r => exact app (ih_l perm) (ih_r perm)
  case prod ih_l ih_r => exact prod (ih_l perm) (ih_r perm)
  case proj ih_r => exact proj (ih_r perm)

-- TODO: Colin suggested mentioned things like this in a paper???
-- I should talk to him again to understand better
omit [Atom X] in
private lemma weakening_strengthened_eq {Γ Δ Γ_Δ Φ : Ctx X K} {t : Term X C} {T} (eq : Γ_Δ  = Γ ++ Δ ) :
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
  case lam xs Γ' t T1 T2 ext ih =>
    apply Typing.lam (xs ∪ dom (Γ ++ Φ ++ Δ))
    intros x mem
    simp at mem
    have ⟨_, _, _, _⟩ := mem
    have h :  (x, T1) :: Γ' = (x, T1) :: Γ ++ Δ := by aesop
    refine @ih x (by assumption) _ _ Φ h ?_
    constructor
    exact ok_Γ_Φ_Δ
    aesop
  case unit => exact Typing.unit
  case prod ih_l ih_r => exact Typing.prod (ih_l eq ok_Γ_Φ_Δ) (ih_r eq ok_Γ_Φ_Δ)
  case proj ih => exact Typing.proj (ih eq ok_Γ_Φ_Δ)

omit [Atom X] in
lemma weakening_strengthened {Γ Δ Φ : Ctx X K} {t : Term X C} {T} :
  Γ ++ Δ ⊢ t ∶ T ->
  Ok (Γ ++ Φ ++ Δ ) ->
  (Γ ++ Φ ++ Δ ) ⊢ t ∶ T := weakening_strengthened_eq rfl

omit [Atom X] in
lemma weakening {Γ Δ : Ctx X K} {t : Term X C} {T} :
  Γ ⊢ t ∶ T → 
  Ok (Γ ++ Δ) → 
  Γ ++ Δ ⊢ t ∶ T := by
  intros der ok
  rw [←List.append_nil (Γ ++ Δ)] at *
  refine weakening_strengthened ?_ ok
  rw [List.append_nil]
  exact der

omit [Atom X] in
lemma typing_lc {Γ : Ctx X K} {t : Term X C} {T} : Γ ⊢ t ∶ T → t.LC := by
  intros h
  induction' h
  case lam xs _ _ _ _ _ ih => exact LC.lam xs _ (λ x a ↦ ih x a)
  case app ih_l ih_r => exact LC.app ih_l ih_r
  all_goals constructor <;> assumption

private lemma typing_subst_strengthened_eq {Γ Δ Φ : Ctx X K} {t s : Term X C} {S T z} (eq : Φ = Δ ++ (z, S) :: Γ) :
  Φ ⊢ t ∶ T →
  Γ ⊢ s ∶ S → 
  (Δ ++ Γ) ⊢ (t [z := s]) ∶ T
  := by
  intros h
  revert Γ Δ
  induction h <;> intros Γ Δ eq der <;> simp only [subst]
  case const => exact Typing.const
  case unit => exact Typing.unit
  case var z' T ok mem =>
    rw [eq] at mem
    rw [eq] at ok
    cases (Ok.perm (by aesop) ok : Ok ((z, S) :: Δ ++ Γ))
    case cons ok_weak _ =>
    simp at ok_weak
    observe perm : (Γ ++ Δ).Perm (Δ ++ Γ)
    by_cases h :  z = z' <;> simp [h]
    · rw [h] at mem
      have dom_Δ : z ∉ dom Δ := by aesop
      have dom_Γ : z ∉ dom Γ := by aesop
      have h' : T = S := by aesop
      rw [h']
      apply Typing.perm perm
      apply weakening
      exact der
      exact Ok.perm (id (List.Perm.symm perm)) ok_weak
    · constructor
      exact ok_weak
      aesop
  case app ih_l ih_r => exact Typing.app (ih_l eq der) (ih_r eq der)
  case prod ih_l ih_r => exact Typing.prod (ih_l eq der) (ih_r eq der)
  case proj ih => exact Typing.proj (ih eq der)
  case lam xs Γ' t T1 T2 ih' ih =>
    apply Typing.lam (xs ∪ {z} ∪ dom (Δ ++ Γ))
    intros x fresh
    simp at fresh
    push_neg at fresh
    have ⟨f1, f2, f3, f4⟩ := fresh
    rw [subst_open_var _ _ _ _ _ ?lc]
    case lc => exact typing_lc der
    have assoc : (x, T1) :: (Δ ++ Γ) = ((x, T1) :: Δ) ++ Γ := by aesop 
    rw [assoc]
    apply ih 
    all_goals aesop

lemma typing_subst_strengthened {Γ Δ : Ctx X K} {t s : Term X C} {S T z} :
  (Δ ++ (z, S) :: Γ) ⊢ t ∶ T →
  Γ ⊢ s ∶ S → 
  (Δ ++ Γ) ⊢ (t [z := s]) ∶ T
  := typing_subst_strengthened_eq rfl

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
  case const => cases step
  case unit => cases step
  case var => cases step
  case prod => 
    cases step
    case ξₗ_pair der_l _ _ ih_r _ _ step_r => exact Typing.prod der_l (ih_r step_r)
    case ξᵣ_pair _ der_r ih_l _ _ step_l _ => exact Typing.prod (ih_l step_l) der_r
  case proj p der_prod _ =>
    cases step 
    case β_proj => 
      cases der_prod
      cases p <;> assumption
    case ξ_proj ih _ step => exact Typing.proj (ih step)

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
