import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties

open Term

variable {X : Type}

/-- definition 2.4 -/
inductive Numeral : Term X → Prop
| zero : Numeral zero
| succ {m} : Numeral m → Numeral (succ m)

-- Numerals are locally closed
theorem numeral_lc {m : Term X} : Numeral m → LC m := by
  intros num
  induction num <;> constructor
  assumption

theorem numeral_open {m : Term X} {k x} : Numeral m → m⟦k ↝ x⟧ = m := by
  intros num
  induction num <;> simp
  assumption

/-- definition 2.14 -/
inductive Value : Term X → Prop
| lam (t) : LC (lam t) → Value (lam t)
| num {n} : Numeral n → Value n

-- Values are locally closed
@[aesop safe]
theorem value_lc {V : Term X} : Value V → LC V := by 
  intros val
  induction val
  case lam => assumption
  case num num => exact numeral_lc num

/-- definition 2.12 -/
inductive BigStep : Term X → Term X → Prop
| lam  (t) : LC (lam t) → BigStep (lam t) (lam t)
| β {E V M N} : LC N → BigStep M (lam E) → BigStep (E ^ N) V → BigStep (app M N) V
| fix {M V} : BigStep (app M (fix M)) V → BigStep (fix M) V
| zero : BigStep zero zero
| succ {M n} : Numeral n → BigStep M n → BigStep (succ M) (succ n)
| pred_zero {M} : BigStep M zero → BigStep (pred M) zero
| pred_succ {M n} : Numeral n → BigStep M (succ n) → BigStep (pred M) n
| ifzero_zero {M N₁} N₂ {V} : N₁.LC → N₂.LC → BigStep M zero → BigStep N₁ V → BigStep (ifzero M N₁ N₂) V
| ifzero_succ {M} N₁ {N₂ V n} : N₁.LC → N₂.LC → Numeral n → BigStep M (succ n) → BigStep N₂ V → BigStep (ifzero M N₁ N₂) V

notation:39 t " ⇓ " t' => BigStep t t'

lemma BigStep_lc_l {M N : Term X} : (M ⇓ N) → LC M := by
  intros big
  induction big
  case' fix ih => cases ih
  case lam => assumption
  all_goals constructor <;> assumption

/-- big step semantics are reflexive on values -/
lemma BigStep_value_refl {V : Term X} : Value V → BigStep V V := by
  intros val
  induction val
  case lam => constructor; assumption
  case num num => induction num <;> constructor <;> assumption

/-- lemma 2.15 -/
lemma BigStep_value {M V : Term X} : (M ⇓ V) → Value V := by
  intros bigstep
  induction bigstep
  case lam t => 
    apply Value.lam
    assumption
  case fix => assumption
  case zero => repeat constructor
  case succ num _ _ => 
    constructor
    exact Numeral.succ num
  case pred_zero => repeat constructor
  case pred_succ num _ _ => constructor; assumption
  case ifzero_zero => assumption
  case ifzero_succ => assumption
  case β => assumption

/-- lemma 2.16 (ii) -/
lemma bigstep_unique (V N : Term X) : Value V → (V ⇓ N) → V = N := by
  intros val
  revert N
  induction val <;> intros N step
  case num n num =>
    revert N V
    induction num <;> intros V N step
    case zero =>
      cases step
      rfl
    case succ m num_m ih =>
      cases step
      case succ m' _ _ =>
      simp
      apply ih m'
      assumption
  case lam t lc_t =>
    cases step
    rfl

/-- lemma 2.17 -/
lemma BigStep_deterministic {M V W : Term X} : (M ⇓ V) → (M ⇓ W) → V = W := by
  intros vstep
  revert W
  induction vstep <;> intros W wstep
  case β ih' ih'' ih =>
    apply ih
    cases wstep
    case a.β s s' _ _ =>
    cases (ih'' s')
    assumption
  case fix A B step_B ih =>
    cases wstep
    apply ih
    assumption
  case succ ih => cases wstep; aesop
  case zero => cases wstep; aesop
  case lam => cases wstep; aesop
  case pred_zero ih =>   
    cases wstep
    rfl
    apply ih
    case pred_succ.a M step' => cases (ih step')
  case pred_succ ih => 
    cases wstep
    case pred_zero step' => cases (ih step')
    case pred_succ step' => cases (ih step'); rfl
  case ifzero_zero A B C D step_zero setp_D ih_l ih_r => 
    cases wstep
    case ifzero_zero => apply ih_r; assumption
    case ifzero_succ contra _ _ _ => cases (ih_l contra)
  case ifzero_succ step_succ n _ _ _ ih_l ih_r => 
    cases wstep
    case ifzero_zero step_zero _ _ _ => cases (ih_l step_zero)
    case ifzero_succ =>
      apply ih_r
      assumption
