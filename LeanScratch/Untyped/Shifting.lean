import LeanScratch.Untyped.Basic

open Term

-- Pierce definition 6.1.2
inductive Term.free : Term → ℕ → Prop where
| var {k n: ℕ} : k < n → free (var k) n
| abs {n' : ℕ} {t₁ : Term} : free t₁ (n'+1) → free (abs t₁) n'
| app {n : ℕ} {t₁ t₂ : Term} : free t₁ n → free t₂ n → free (app t₁ t₂) n

-- Pierce exercise 6.2.6
theorem Term.free_shiftₙ (t : Term) (n c d: ℕ) (h : free t n) : free (t.shiftₙ c d) (n+d) := by
  revert c
  revert n
  induction t <;> intros n h c <;> simp [shiftₙ]

  case var x =>
    cases h with | var h => 
    by_cases h' : x < c <;> simp [h'] <;> apply free.var 
    · exact Nat.lt_add_right d h
    · exact Nat.add_lt_add_right h d 

  case app l r l_ih r_ih =>
    cases h with | app hl hr =>
    apply free.app
    · exact l_ih n hl c
    · exact r_ih n hr c

  case abs body ih =>
    apply free.abs
    induction body <;> rw [←Nat.add_right_comm n 1 d]
    case a.var x' =>
      simp [shiftₙ]
      sorry
--      by_cases h' : x' < c + 1 
--      <;> simp [h'] 
--      <;> apply free.var
--      <;> cases h
--      <;> rename_i h
--      <;> cases ih (n+1) h (c+1)
--      <;> rename_i h''
--      <;> simp [h'] at h''
--      · exact h''
--      · exact Nat.add_lt_add_right h'' d
    case a.abs body ih' =>
       apply free.abs
       cases h with | abs h' =>
       cases ih (n+1) h' (c+1) with | abs h'' =>
       exact h''
    case a.app l' r' lih' rih' =>
       apply free.app
       <;> cases h
       <;> rename_i h
       <;> cases ih (n+1) h (c+1)
       <;> rename_i l r
       · exact l
       · exact r

-- much thanks to https://github.com/pi8027/lambda-calculus/blob/master/agda/Lambda/Confluence.agda
-- TODO: some of these need some additional conditions about free variables, I'd like to use what I defined above
lemma sub_comm (m n : ℕ) (t1 t2 t3 : Term)
  : (t1 [m := t2.shiftₙ 0 (m+1)] [(m+1)+n := t3.shiftₙ 0 (m+1)]) = 
    (t1 [(m+1)+n := t3.shiftₙ 0 (m+1)] [m := (t2 [n := t3]).shiftₙ 0 (m+1)])
  := sorry

theorem shiftAdd {d d' c} (t : Term) : (t.shiftₙ c d').shiftₙ c d = t.shiftₙ c (d + d') := by
  revert c
  induction t <;> intros c
  case var x => 
    simp [Term.shiftₙ]
    by_cases h : x < c <;> simp [Term.shiftₙ, h]
    have h' : ¬ x + d' < c := by simp_all; exact Nat.le_add_right_of_le h
    simp [h']
    ring
  case app l r ih_l ih_r => exact congrArg₂ Term.app (by apply ih_l) (by apply ih_r)
  case abs body ih => exact congrArg Term.abs (by apply ih)

theorem unshiftSubstSwap {n : ℕ} (t1 t2 : Term) : (t1 [n+1 := t2.shift]).unshift = (t1.unshift [n := t2]) := by
  induction t1
  case var => sorry
  case app l r ih_l ih_r => exact congrArg₂ Term.app ih_l ih_r
  case abs body ih => 
    refine congrArg Term.abs ?_
    simp [unshiftₙ]
    -- is this the correct rewrite? not sure...
    rw [shiftAdd t2]
    sorry
