import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Reduction

open Term

inductive β : Term → Term → Prop
| reduce {M N} : β {{{ (λ . ~M) ~N }}} (M [0 := N.shift]).unshift

-- follows PLFA (sorta...)
mutual
  inductive Neutral : Term → Prop
  | of_var (x : ℕ) : Neutral (var x)
  | app_norm {L M : Term} : Neutral L → Normalized M → Neutral {{{ ~L ~M }}}

  inductive Normalized : Term → Prop
  | of_neutral {M} : Neutral M → Normalized M
  | of_abs {N} : Normalized N → Normalized {{{ λ . ~N }}}
end

inductive Progress (M : Term) : Prop
| step {N} : (M →β N) → Progress M
| done     : Normalized M → Progress M

open Progress Normalized Neutral Step_R in
theorem progress (M : Term) : Progress M := by
  induction M
  case var x => exact done (of_neutral (of_var x))
  case abs N prog_N => 
      exact match prog_N with
      | step N_N' => step (ξ N_N')
      | done norm_N => done (of_abs norm_N)
  case app l r prog_l prog_r => 
       cases l with
       | var x =>
           exact match prog_r with
           | step r_r' => step (ξₗ r_r')
           | done norm_r => done (of_neutral (app_norm (of_var x) norm_r))
       | abs N => exact step (reduce β.reduce)
       | app ll lr => 
           exact match prog_l, prog_r with
           | step L_r, _ => step (ξᵣ L_r)
           | done (of_neutral neut_L), done norm_r => done (of_neutral (app_norm neut_L norm_r))
           | _, step r_r' => step (ξₗ r_r')

-- equivalent to the way it's stated in Software Foundations
theorem progress' (M : Term) : Normalized M ∨ (∃ M', M →β M') := by
  induction (progress M)
  case done norm =>
    left
    exact norm
  case step M' M_M' =>
    right
    exists M'

-- some congruence lemmas about beta reduction
theorem app_l_cong {L L' R} : (L ↠β L') → (app L R ↠β app L' R) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξᵣ r)

theorem app_r_cong {R R' L} : (R ↠β R') → (app L R ↠β app L R') := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξₗ r)

theorem abs_cong {N N'} : ( N ↠β N') → (N.abs ↠β N'.abs) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξ r)
