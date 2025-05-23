import LeanScratch.PCF.Basic
import LeanScratch.PCF.Properties

open Term Ty

variable {X : Type}

/-- definition 2.3, the actual derivations -/
inductive Der [DecidableEq X] : List (X × Ty) → Term X → Ty → Prop
| zero (Γ)   : Der Γ zero nat
| succ (Γ M) : Der Γ M nat → Der Γ (succ M) nat
| pred (Γ M) : Der Γ M nat → Der Γ (pred M) nat
| ifzero (Γ M N₁ N₂) : Der Γ M nat → Der Γ N₁ nat → Der Γ N₂ nat → Der Γ (ifzero M N₁ N₂) nat
| fix (Γ M σ) : Der Γ M (σ ⤳ σ) → Der Γ (fix M) σ
| app (Γ M N σ τ) : Der Γ M (σ ⤳ τ) → Der Γ N σ → Der Γ (app M N) τ
| var {Γ x T} : Ok Γ → (x,T) ∈ Γ → Der Γ (fvar x) T
| lam (L : Finset X) {Γ t σ τ} : (∀ x ∉ L, Der ((x,σ) :: Γ) (t ^ fvar x) τ) → Der Γ (lam t) (σ ⤳ τ) 

notation:50 Γ " ⊢ " t " ∶" T => Der Γ t T

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

/-- definition 2.5 -/
inductive Step : Term X → Term X → Prop
| β {M N} : LC (lam M) → Value N → Step (app (lam M) N) (M ^ N)
| ξ_app_l {M M' N} : LC N → Step M M' → Step (app M N) (app M' N)
| ξ_app_r {M N N'} : Value M → Step N N' → Step (app M N) (app M N')
| fix {M} : M.LC → Step (fix M) (app M (fix M))
| pred_zero : Step (pred zero) zero
| pred_succ {n} : Numeral n → Step (pred (succ n)) n
| ifzero_zero {M N} : M.LC → N.LC → Step (ifzero zero M N) M
| ifzero_succ {n M N} : Numeral n → M.LC → N.LC → Step (ifzero (succ n) M N) N
| ξ_succ {M₁ M₂} : Step M₁ M₂ → Step (succ M₁) (succ M₂)
| ξ_pred {M₁ M₂} : Step M₁ M₂ → Step (pred M₁) (pred M₂)
| ξ_ifzero {M₁ M₂} (N₁ N₂) :  Step M₁ M₂ → N₁.LC → N₂.LC → Step (ifzero M₁ N₁ N₂) (ifzero M₁ N₁ N₂)

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
  case ξ_ifzero step _ _ _ => 
    constructor
    exact Step_lc_l step
    all_goals assumption
  all_goals (try constructor <;> aesop)
  assumption
  assumption

-- TODO: free conditions
/-- definition 2.12 -/
inductive BigStep : Term X → Term X → Prop
| lam  (t) : LC (lam t) → BigStep (lam t) (lam t)
| β {t3 v2 v3 t1 t2} : BigStep t1 (lam t3) → BigStep t2 v2 → BigStep (t3 ^ v2) v3 → BigStep (app t1 t2) v3
| fix {M V} : BigStep (app M (fix M)) V → BigStep (fix M) V
| zero : BigStep zero zero
| succ {M n} : Numeral n → BigStep M n → BigStep (succ M) (succ n)
| pred_zero {M} : BigStep M zero → BigStep (pred M) zero
| pred_succ {M n} : Numeral n → BigStep M (succ n) → BigStep (pred M) n
| ifzero_zero {M N₁} N₂ {V} : N₂.LC → BigStep M zero → BigStep N₁ V → BigStep (ifzero M N₁ N₂) V
| ifzero_succ {M} N₁ {N₂ V n} : N₁.LC → Numeral n → BigStep M (succ n) → BigStep N₂ V → BigStep (ifzero M N₁ N₂) V

notation:39 t " ⇓ " t' => BigStep t t'

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
    case a.β s s' _ =>
    cases (ih' s)
    rw [ih'' s']
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
    case ifzero_succ contra _ _ => cases (ih_l contra)
  case ifzero_succ step_succ n _ _ _ ih_l ih_r => 
    cases wstep
    case ifzero_zero step_zero _ _  => cases (ih_l step_zero)
    case ifzero_succ =>
      apply ih_r
      assumption


theorem step_app_l_cong {M M' N : Term X} : (M ▷* M') → LC N → (app M N ▷* app M' N) := by
  intros step lc_N 
  induction' step
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (Step.ξ_app_l lc_N ih)

theorem step_app_r_cong {M M' N : Term X} : (M ▷* M') → Value N → (app N M ▷* app N M') := by
  intros step val 
  induction' step
  case refl => rfl
  case tail ih r => exact Relation.ReflTransGen.tail r (Step.ξ_app_r val ih)

open Relation.ReflTransGen in
/-- exercise 2.18 (i) -/
theorem big_to_many_small {M V : Term X} : (M ⇓ V) → (M ▷* V) := by
  intros h
  induction h
  case lam => rfl
  case zero => rfl
  case succ M n num big ih => sorry
  all_goals sorry

lemma big_open_val (t1 v2 r : Term X) :
  (∃ L, ∀ x ∉ (L : Finset X), LC (t1 ^ fvar x)) → 
  Value v2 → 
  (t1 ^ v2 ⇓ r) → 
  (app (lam t1) v2 ⇓ r) 
  := by
  intros cond lc op
  constructor
  constructor
  have ⟨L, cond⟩ := cond
  exact LC.lam L t1 cond
  case v2 => exact v2
  exact BigStep_value_refl lc
  exact op

/-- exercise 2.18 (ii) -/
theorem small_to_big {M N V : Term X} : (M ▷ N) → (N ⇓ V) → (M ⇓ V) := by
  intros rt rt'
  have vv : Value V := BigStep_value rt'
  revert V
  induction rt <;> intros V big val
  case β lc_lam _ => 
    apply big_open_val
    cases lc_lam
    case a.lam xs _ =>
      exists xs
    assumption
    assumption
  case ξ_app_l ih => 
    cases big
    cases val
    case β.lam => 
      apply BigStep.β
      apply ih
      assumption
      apply BigStep_value
      assumption
      assumption
      assumption
    case β.num => 
      apply BigStep.β
      apply ih
      assumption
      apply BigStep_value
      assumption
      assumption
      assumption
  case ξ_app_r ih => 
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
    case β t3 v2 h1 h2 h3 =>
    exact BigStep.fix (BigStep.β h1 h2 h3)
  case ifzero_zero =>
    constructor
    assumption
    constructor
    assumption
  case ifzero_succ =>
    apply BigStep.ifzero_succ
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
  case ξ_ifzero => exact big

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

-- TODO: revist after finishing the above proofs
theorem add_n_zero (n : Term X) (num : Numeral n) [DecidableEq X] : app (add_n n) zero ▷*  n := sorry
/-
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
-/
