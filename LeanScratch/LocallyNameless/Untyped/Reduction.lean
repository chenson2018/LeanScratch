import LeanScratch.LocallyNameless.Untyped.Basic
import LeanScratch.LocallyNameless.Untyped.Properties

open Term

variable {X C : Type} [DecidableEq X] [Atom X]

/-- Term reduction step -/
inductive Step : Term X C → Term X C → Prop
| β  {M N}    : LC (lam M) → LC N → Step (app (lam M) N) (M ^ N)
| ξₗ {M N Z}  : LC Z → Step M N → Step (app Z M) (app Z N)
| ξᵣ {M N Z}  : LC Z → Step M N → Step (app M Z) (app N Z)
| ξ  (xs : Finset X) {M N} : (∀ x ∉ xs, Step (M ^ fvar x) (N ^ fvar x)) → Step (lam M) (lam N) 
| β_proj {l r p} : l.LC → r.LC → Step (proj p $ pair l r) (if p = Proj.L then l else r)
| ξₗ_pair {M N Z}  : LC Z → Step M N → Step (pair Z M) (pair Z N)
| ξᵣ_pair {M N Z}  : LC Z → Step M N → Step (pair M Z) (pair N Z)
| ξ_proj {M N p} : Step M N → Step (proj p M) (proj p N)

notation:39 t " ⇢β " t' => Step t t'
notation:39 t " ↠β " t' => Relation.ReflTransGen Step t t'
notation:39 t " ≈β " t' => Relation.EqvGen t t'

open Step

-- a few lemmas that reductions imply local closure
omit [DecidableEq X] [Atom X] in
lemma Term.step_lc_l {M M' : Term X C} (step : M ⇢β M') : LC M := by
  induction step <;> constructor
  case' β_proj => constructor
  all_goals assumption

lemma Term.step_lc_r {M M' : Term X C} (step : M ⇢β M') : LC M' := by
  induction step
  case β => apply beta_lc <;> assumption
  case β_proj p _ _ => cases p <;> simp <;> assumption
  all_goals try constructor <;> assumption 

-- some congruence lemmas about reduction
omit [DecidableEq X] [Atom X] in
theorem redex_app_l_cong {M M' N : Term X C} : (M ↠β M') → LC N → (app M N ↠β app M' N) := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξᵣ lc_N ih)

omit [DecidableEq X] [Atom X] in
theorem redex_app_r_cong {M M' N : Term X C} : (M ↠β M') → LC N → (app N M ↠β app N M') := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξₗ lc_N ih)

omit [DecidableEq X] [Atom X] in
theorem redex_pair_l_cong {M M' N : Term X C} : (M ↠β M') → LC N → (pair M N ↠β pair M' N) := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξᵣ_pair lc_N ih)

omit [DecidableEq X] [Atom X] in
theorem redex_pair_r_cong {M M' N : Term X C} : (M ↠β M') → LC N → (pair N M ↠β pair N M') := by
  intros redex lc_N 
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξₗ_pair lc_N ih)

omit [DecidableEq X] [Atom X] in
theorem redex_proj_cong {M M' : Term X C} (p) : (M ↠β M') → (proj p M ↠β proj p M') := by
  intros redex
  induction' redex
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (ξ_proj ih)

lemma redex_subst_cong (s s' : Term X C) (x y) : (s ⇢β s') -> (s [ x := fvar y ]) ⇢β (s' [ x := fvar y ]) := by
  intros step
  induction step
  case ξₗ ih =>
    refine ξₗ ?_ ih
    apply subst_lc
    assumption
    constructor
  case ξᵣ ih =>
    refine ξᵣ ?_ ih
    apply subst_lc
    assumption
    constructor
  case β m n lam_lc n_lc => 
    cases lam_lc with | lam xs _ mem =>
    simp
    rw [subst_open x (fvar y) 0 n m (by constructor)]
    refine β ?_ (subst_lc n_lc (by constructor))
    -- TODO: this works, but is weird....
    exact subst_lc (LC.lam xs m mem) (LC.fvar y)
  case ξ xs m' m mem ih => 
    apply ξ ({x} ∪ xs)
    intros z z_mem
    simp at *
    rw [
      ←subst_fresh x (fvar z) (fvar y), ←subst_open x (fvar y) 0 (fvar z) m (by constructor),
      subst_fresh x (fvar z) (fvar y), ←subst_fresh x (fvar z) (fvar y),
      ←subst_open x (fvar y) 0 (fvar z) m' (by constructor), subst_fresh x (fvar z) (fvar y) 
    ] 
    apply ih
    all_goals aesop
  case β_proj l r p _ _ => 
    cases p <;> simp <;> apply β_proj <;> exact subst_lc (by assumption) (by constructor)
  case ξₗ_pair ih =>
    refine ξₗ_pair ?_ ih
    apply subst_lc
    assumption
    constructor
  case ξᵣ_pair ih =>
    refine ξᵣ_pair ?_ ih
    apply subst_lc
    assumption
    constructor
  case ξ_proj ih => exact ξ_proj ih

lemma step_lam_close {M M' : Term X C} {x : X} : (M ⇢β M') → (lam (M⟦0 ↜ x⟧) ⇢β lam (M'⟦0 ↜ x⟧)) := by
  intros step
  have M_lc := step_lc_l step
  have M'_lc := step_lc_r step
  apply ξ ∅
  intros y _
  simp
  repeat rw [open_close_to_subst]
  exact redex_subst_cong M M' x y step
  exact step_lc_r step
  exact step_lc_l step

lemma redex_lam_close {M M' : Term X C} {x : X} : (M ↠β M') → (lam (M⟦0 ↜ x⟧) ↠β lam (M'⟦0 ↜ x⟧)) :=  by
  intros step
  induction step using Relation.ReflTransGen.trans_induction_on
  case ih₁ => rfl
  case ih₂ ih => exact Relation.ReflTransGen.single (step_lam_close ih)
  case ih₃ l r => trans; exact l; exact r

theorem redex_lam_cong {M M' : Term X C} (xs : Finset X) : (∀ x ∉ xs, (M ^ fvar x) ↠β (M' ^ fvar x)) → lam M ↠β lam M' := by
  intros mem
  have ⟨fresh, union⟩ := atom_fresh_for_set (xs ∪ M.fv ∪ M'.fv)
  simp at union
  obtain ⟨_, _, _⟩ := union
  rw [←open_close fresh M 0 ?_, ←open_close fresh M' 0 ?_]
  refine redex_lam_close (mem fresh ?_)
  all_goals assumption
