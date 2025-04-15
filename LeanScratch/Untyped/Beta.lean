import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Reduction

open Term

variable {T : Type}

inductive β : Term T → Term T → Prop
| reduce {M N} : β {{{ (λ . ~M) ~N }}} (M [0 := N.shift]).unshift

-- follows PLFA (sorta...)
mutual
  inductive Neutral : Term T → Prop
  | of_var (x : ℕ) : Neutral (var x)
  | of_const (t : T) : Neutral (const t)
  | app_norm {L M : Term T} : Neutral L → Normalized M → Neutral {{{ ~L ~M }}}

  inductive Normalized : Term T → Prop
  | of_neutral {M} : Neutral M → Normalized M
  | of_abs {N} : Normalized N → Normalized {{{ λ . ~N }}}
end

inductive Progress (M : Term T) : Prop
| step {N} : (M ⇢β N) → Progress M
| done     : Normalized M → Progress M

open Progress Normalized Neutral Step_R in
theorem progress (M : Term T) : Progress M := by
  induction M
  case const t => exact done $ of_neutral (of_const t)
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
       | const m =>
           exact match prog_r with
           | step r_r' => step (ξₗ r_r')
           | done norm_r => done (of_neutral (app_norm (of_const m) norm_r))

-- equivalent to the way it's stated in Software Foundations
theorem progress' (M : Term T) : Normalized M ∨ (∃ M', M ⇢β M') := by
  induction (progress M)
  case done norm =>
    left
    exact norm
  case step M' M_M' =>
    right
    exists M'
