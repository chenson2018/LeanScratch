import LeanScratch.Untyped.Basic

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
      by_cases h' : x' < c + 1 
      <;> simp [h'] 
      <;> apply free.var
      <;> cases h
      <;> rename_i h
      <;> cases ih (n+1) h (c+1)
      <;> rename_i h''
      <;> simp [h'] at h''
      · exact h''
      · exact Nat.add_lt_add_right h'' d
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
