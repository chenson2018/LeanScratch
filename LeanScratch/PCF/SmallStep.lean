import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties
import LeanScratch.PCF.BigStep

open Term

variable {X : Type}

/-- definition 2.5 -/
inductive Step : Term X → Term X → Prop
| β {M N} : LC (lam M) → LC N → Step (app (lam M) N) (M ^ N)
| ξ_app_l {M M' N} : LC N → Step M M' → Step (app M N) (app M' N)
| fix {M} : M.LC → Step (fix M) (app M (fix M))
| pred_zero : Step (pred zero) zero
| pred_succ {n} : Numeral n → Step (pred (succ n)) n
| ifzero_zero {M N} : M.LC → N.LC → Step (ifzero zero M N) M
| ifzero_succ {n M N} : Numeral n → M.LC → N.LC → Step (ifzero (succ n) M N) N
| ξ_succ {M₁ M₂} : Step M₁ M₂ → Step (succ M₁) (succ M₂)
| ξ_pred {M₁ M₂} : Step M₁ M₂ → Step (pred M₁) (pred M₂)
| ξ_ifzero {M₁ M₂} (N₁ N₂) :  Step M₁ M₂ → N₁.LC → N₂.LC → Step (ifzero M₁ N₁ N₂) (ifzero M₂ N₁ N₂)

notation:39 t " ▷ " t' => Step t t'
notation:39 t " ▷* " t' => Relation.ReflTransGen Step t t'

theorem Step_lc_l {M N : Term X} (step : M ▷ N) : LC M := by
  induction step <;> constructor
  case pred_zero => constructor
  case pred_succ num => constructor; exact numeral_lc num
  case ifzero_zero =>
    constructor
  case ifzero_succ num _ _ =>
    constructor
    exact numeral_lc num
  all_goals aesop

theorem Step_lc_r {M N : Term X} (step : M ▷ N) [DecidableEq X] [Atom X] : LC N := by
  induction step
  case β => apply beta_lc <;> aesop
  case pred_succ num => exact numeral_lc num
  case fix => repeat (constructor; assumption)
  all_goals (try constructor <;> aesop)
  assumption
  assumption

/-- lemma 2.16 (i) -/
lemma value_no_step {V : Term X} : Value V → ¬(∃N, V ▷ N) := by
  intros val
  induction val
  case num n num =>
    intros step
    obtain ⟨n', step⟩ := step
    revert n'
    induction num <;> intros n' step
    case intro.zero =>
      cases step
    case intro.succ m num ih =>
      cases step
      case ξ_succ m' step => exact ih m' step
  case lam t t_lc =>
    intros step
    obtain ⟨t', step⟩ := step
    cases step

theorem step_app_l_cong {M M' N : Term X} : (M ▷* M') → LC N → (app M N ▷* app M' N) := by
  intros step lc_N 
  induction' step
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (Step.ξ_app_l lc_N ih)

theorem step_succ_cong {M M' : Term X} : (M ▷* M') → (succ M ▷* succ M') := by
  intros step
  induction' step
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (Step.ξ_succ ih)

theorem step_pred_cong {M M' : Term X} : (M ▷* M') → (pred M ▷* pred M') := by
  intros step
  induction' step
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (Step.ξ_pred ih)

theorem step_ifzero_cong {M M' N₁ N₂ : Term X} : (M ▷* M') → LC N₁ → LC N₂ → (ifzero M N₁ N₂ ▷* ifzero M' N₁ N₂) := by
  intros step lc_N₁ lc_N₂
  induction' step
  case refl => rfl
  case tail r => refine Relation.ReflTransGen.tail r (Step.ξ_ifzero _ _ ?_ ?_ ?_) <;> assumption

open Relation.ReflTransGen in
/-- exercise 2.18 (i) -/
theorem big_to_many_small {M V : Term X} : (M ⇓ V) → (M ▷* V) := by
  intros h
  induction h
  case lam => rfl
  case zero => rfl
  case succ ih => exact step_succ_cong ih
  case pred_zero ih =>
    apply tail
    apply step_pred_cong ih
    exact Step.pred_zero
  case pred_succ ih =>
    apply tail
    apply step_pred_cong ih
    apply Step.pred_succ
    assumption
  case ifzero_zero ih ih' =>
    trans
    apply step_ifzero_cong ih <;> assumption
    apply head
    apply Step.ifzero_zero <;> assumption
    exact ih'
  case ifzero_succ ih ih' =>
    trans
    apply step_ifzero_cong ih <;> assumption
    apply head
    apply Step.ifzero_succ <;> assumption
    assumption
  case fix M _ big ih =>
    apply head
    constructor
    cases (BigStep_lc_l big)
    all_goals assumption    
  case β E V M N lc_N big_lam big_open ih_lam ih_open =>
    trans
    apply step_app_l_cong ih_lam lc_N
    apply head
    apply Step.β $ value_lc (BigStep_value big_lam)
    all_goals assumption

/-- exercise 2.18 (ii) -/
theorem small_to_big {M N V : Term X} : (M ▷ N) → (N ⇓ V) → (M ⇓ V) := by
  intros rt rt'
  have vv : Value V := BigStep_value rt'
  revert V
  induction rt <;> intros V big val
  case β M N lc_lam_M lc_N =>
    refine @BigStep.β _ M _ _ _ (by assumption) ?_ (by assumption)
    apply BigStep_value_refl
    constructor
    assumption
  case ξ_app_l ih => 
    cases big
    cases val
    case β.lam => 
      apply BigStep.β
      assumption
      apply ih
      assumption
      apply BigStep_value
      assumption
      assumption
    case β.num => 
      apply BigStep.β
      assumption
      apply ih
      assumption
      apply BigStep_value
      assumption
      assumption
  case pred_zero =>
    cases val
    cases big
    case num num =>
      cases num
      case zero => exact BigStep.pred_zero big
      case succ => cases big
  case pred_succ n num =>
    cases val
    cases num
    cases big
    cases big
    case num num' =>
    exact BigStep.pred_succ num' (BigStep.succ num' big)
  case fix M lc_M =>
    cases big
    case β t3 v2 h2 lc_fix h3 =>
    exact BigStep.fix (BigStep.β lc_fix h2 h3)
  case ifzero_zero =>
    constructor
    assumption
    assumption
    constructor
    assumption
  case ifzero_succ =>
    apply BigStep.ifzero_succ
    assumption
    assumption
    assumption
    constructor
    assumption
    apply BigStep_value_refl
    apply Value.num
    assumption
    assumption
  case ξ_succ step ih => 
    cases big
    cases val
    constructor
    assumption
    apply ih
    assumption
    apply Value.num
    assumption
  case ξ_pred ih => 
    cases big
    case pred_zero =>
      constructor
      apply ih
      assumption
      assumption
    case pred_succ =>
      apply BigStep.pred_succ
      assumption
      cases val
      apply ih
      assumption
      constructor
      constructor
      assumption
      apply ih
      assumption
      constructor
      constructor
      assumption
  case ξ_ifzero ih => 
    cases big
    case ifzero_zero =>
      apply BigStep.ifzero_zero
      assumption
      assumption
      apply ih
      assumption
      constructor
      constructor
      assumption
    case ifzero_succ =>
      apply BigStep.ifzero_succ
      assumption
      assumption
      assumption
      apply ih
      assumption
      constructor
      constructor
      assumption
      assumption

--/-- exercise 2.18 (iii) -/
theorem many_small_to_big {M N V : Term X} : (M ▷* N) → (N ⇓ V) → (M ⇓ V) := by
  intros closure
  induction closure <;> intros bigstep
  case refl => assumption
  case tail step ih => exact ih (small_to_big step bigstep)

theorem many_small_value_to_big {M V : Term X} : Value V → (M ▷* V) → (M ⇓ V) := by
  intros val steps
  apply many_small_to_big steps
  exact BigStep_value_refl val

/-- a nice way to state this as one theorem -/
theorem BigStep_Equivalence {t v : Term X} : (t ⇓ v) ↔ (t ▷* v) ∧ Value v := by
  constructor
  · intros big
    constructor
    exact big_to_many_small big
    exact BigStep_value big
  · intros h
    exact many_small_value_to_big h.2 h.1

/-- exercise 2.9 -/
def add_n (n : Term X) : Term X := fix $ lam $ lam $ ifzero (bvar 0) n (succ $ app (bvar 1) (pred (bvar 0)))

theorem add_n_zero (n : Term X) (num : Numeral n) [DecidableEq X] : app (add_n n) zero ▷*  n := by
  simp only [add_n]
  have body_lc : ((bvar 0).ifzero n ((bvar 1).app (bvar 0).pred).succ).lam.lam.LC := by
    apply LC.lam ∅
    intros f _
    apply LC.lam {f}
    intros
    constructor
    constructor
    repeat rw [numeral_open num]
    exact numeral_lc num
    constructor
    constructor
    constructor
    constructor
    constructor
  trans
  · apply Relation.ReflTransGen.head
    apply Step.ξ_app_l LC.zero
    apply Step.fix body_lc
    rfl
  trans
  · apply Relation.ReflTransGen.head
    apply Step.ξ_app_l LC.zero
    apply Step.β
    exact body_lc
    exact LC.fix body_lc
    rfl
  trans
  · apply Relation.ReflTransGen.head
    apply Step.β
    apply LC.lam ∅
    intros f _
    constructor
    constructor
    repeat rw [numeral_open num]
    exact numeral_lc num
    constructor
    constructor
    constructor
    apply LC.lam {f}
    intros y _
    constructor
    intros y' mem
    constructor
    constructor
    repeat rw [numeral_open num]
    exact numeral_lc num
    simp
    constructor
    constructor
    constructor
    constructor
    constructor
    exact {}
    constructor
    constructor
    constructor
    rfl
  simp
  trans
  · apply Relation.ReflTransGen.head
    apply Step.ifzero_zero
    repeat rw [numeral_open num]
    exact numeral_lc num
    constructor
    constructor
    constructor
    apply LC.lam ∅
    intros x1 _
    apply LC.lam {x1}
    intros x2 _
    constructor
    constructor
    repeat rw [numeral_open num]
    exact numeral_lc num
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    constructor
    rfl
  repeat rw [numeral_open num]
