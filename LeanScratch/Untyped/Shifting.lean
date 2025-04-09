import LeanScratch.Untyped.Basic

open Term

-- directly translated from: https://github.com/pi8027/lambda-calculus/blob/master/agda/Lambda/Confluence.agda
inductive Shifted : ℕ → ℕ → Term → Prop where
| svar1 {d c n} : n < c → Shifted d c (var n)
| svar2 {d c n} : c + d ≤ n → d ≤ n → Shifted d c (var n)
| sapp {d c t1 t2} : Shifted d c t1 → Shifted d c t2 → Shifted d c (app t1 t2)
| sabs {d c t} : Shifted d (c+1) t → Shifted d c (abs t)

open Shifted

theorem shiftAdd (d d' c) (t : Term) : (t.shiftₙ c d').shiftₙ c d = t.shiftₙ c (d + d') := by
  revert c
  induction t <;> intros c
  case var x => 
    simp [Term.shiftₙ]
    by_cases h : x < c <;> simp [Term.shiftₙ, h]
    have h' : ¬ x + d' < c := by simp_all; exact Nat.le_add_right_of_le h
    simp [h']
    linarith
  case app l r ih_l ih_r => exact congrArg₂ Term.app (by apply ih_l) (by apply ih_r)
  case abs body ih => exact congrArg Term.abs (by apply ih)

theorem shiftUnshiftSwap {d c d' c' t} : 
  c' ≤ c → Shifted d' c' t → shiftₙ c d (t.unshiftₙ c' d') = unshiftₙ c' d' (t.shiftₙ (c + d') d) := by
    intros p1 p2
    match t, p2 with
    | _, sapp p2 p3 => exact congrArg₂ Term.app (shiftUnshiftSwap p1 p2) (shiftUnshiftSwap p1 p3)
    | _, sabs p2 => 
       simp [shiftₙ, unshiftₙ]
       rw [shiftUnshiftSwap (Nat.add_le_add_right p1 1) p2]
       have eq : c + 1 + d' = c + d' + 1 := by linarith
       rw [eq]
    | var n, p => 
       simp [shiftₙ, unshiftₙ]
       by_cases h₁ : n < c' <;> simp [h₁]
       ·   by_cases h₂ : n < c 
       <;> by_cases h₃ : n < c + d' 
       <;> by_cases h₄ : n + d < c'
       <;> simp [h₁, h₂, h₃, h₄]
       <;> linarith
       · cases p
         case neg.svar1 p =>
           exfalso
           apply h₁
           exact p
         case neg.svar2 p₁ p₂ =>
           by_cases h₂ : n - d' < c <;> by_cases h₃ : n < c + d' <;> simp [h₁, h₂, h₃]
           case pos =>
              exfalso
              apply h₂
              exact Nat.sub_lt_right_of_lt_add p₁ h₃
           all_goals by_cases h₄ : n + d < c' <;> simp [h₄]
           · linarith
           · exfalso
             apply h₃
             exact (Nat.sub_lt_iff_lt_add' p₁).mp h₂
           · linarith
           · rw [Nat.sub_add_comm p₁]

theorem shiftSubstSwap : ∀ {d c n}, n < c → ∀ t1 t2,
                 shiftₙ c d (t1 [ n := t2 ]) = ((shiftₙ c d t1) [ n := shiftₙ c d t2 ]) := sorry

theorem shiftShiftSwap : ∀ d c d' c' t, c ≤ c' → shiftₙ c d (t.shiftₙ c' d') = shiftₙ (c' + d) d' (shiftₙ c d t) := by
  intros d c d' c' t p
  match t with
  | app l r => exact congrArg₂ Term.app (shiftShiftSwap d c d' c' l p) (shiftShiftSwap d c d' c' r p)
  | Term.abs body =>
      simp [shiftₙ]
      rw [shiftShiftSwap d (c+1) d' (c'+1) body (Nat.add_le_add_right p 1)]
      have eq : c' + 1 + d = c' + d + 1 := by linarith
      rw [eq]
  | var x => 
      simp [shiftₙ]
      by_cases h₁ : x < c' 
  <;> by_cases h₂ : x < c 
  <;> simp [h₁, h₂]
      · have h₃ : x < c' + d := by linarith
        simp [h₃]
      all_goals by_cases h₃ : x + d' < c <;> simp [h₃]
      · by_cases h₄ : x < c' + d <;> simp [h₄]
        linarith
      · by_cases h₄ : x < c' + d <;> simp [h₄] <;> linarith
      · exfalso
        apply h₂
        exact Nat.lt_of_add_right_lt h₃
      · linarith
  
theorem betaShifted' (n t1 t2) : Shifted 1 n (t1 [ n := shiftₙ 0 (n+1) t2 ]) := 
  match t1 with
  | app l r => sapp (betaShifted' n l t2) (betaShifted' n r t2)
  | Term.abs t1 => by
      simp [sub]
      rw [shiftAdd, Nat.add_comm 1 (n + 1)] 
      exact sabs $ betaShifted' (n+1) t1 t2
  | var n' => by
      simp [sub]
      by_cases h : n' = n <;> simp [h]
      · sorry
      · sorry

theorem unshiftUnshiftSwap :
  ∀ {d c d' c' t}, c' ≤ c → Shifted d' c' t → Shifted d c (unshiftₙ c' d' t) →
  unshiftₙ c d (unshiftₙ c' d' t) = unshiftₙ c' d' (unshiftₙ (c + d') d t) := sorry

theorem unshiftSubstSwap2 :
  ∀ {d c n t1 t2}, n < c → Shifted d c t1 → Shifted d c t2 →
  unshiftₙ c d (t1 [ n := t2 ]) = ((unshiftₙ c d t1) [ n := unshiftₙ c d t2 ]) := sorry

theorem unshiftShiftSwap : ∀ {d c d' c' t}, c' ≤ c → Shifted d c t →
                   shiftₙ c' d' (unshiftₙ c d t) = unshiftₙ (c + d') d (shiftₙ c' d' t) := sorry

theorem shiftShifted' :
  ∀ {d c d' c' t}, c' ≤ d + c → Shifted d c t → Shifted d (d' + c) (shiftₙ c' d' t) := sorry

theorem betaShifted2 : ∀ {d c n t1 t2}, Shifted d ((n+1)+c) t1 → Shifted d c t2 →
               Shifted d (n + c) (unshiftₙ n 1 (t1 [ n := shiftₙ 0 (n+1) t2 ])) := sorry

theorem unshiftSubstSwap :
  ∀ {c n} t1 t2, c ≤ n → Shifted 1 c t1 →
  unshiftₙ c 1 (t1 [ n+1 := shiftₙ 0 (c+1) t2 ]) = ((unshiftₙ c 1 t1) [ n := shiftₙ 0 c t2 ]) := sorry

theorem unshiftSubstSwap' :
  ∀ {n} t1 t2, Shifted 1 0 t1 → unshiftₙ 0 1 (t1 [ n+1 := shiftₙ 0 1 t2 ]) = ((unshiftₙ 0 1 t1) [ n := t2 ]) := sorry

theorem shiftSubstSwap' : ∀ {d c n}, c ≤ n → ∀ t1 t2,
                  shiftₙ c d (t1 [ n := t2 ]) = ((shiftₙ c d t1) [ n + d := shiftₙ c d t2 ]) := sorry

theorem shiftShifted (d c t) : Shifted d c (shiftₙ c d t) := by
  revert c
  induction t <;> intros c <;> simp [shiftₙ]
  case var x =>
    by_cases h : x < c <;> simp [h]
    · exact svar1 h
    · apply svar2 <;> linarith
  all_goals constructor <;> aesop

theorem substShiftedCancel :
  ∀ {d c n t1 t2}, c ≤ n → n < c + d → Shifted d c t1 → t1 = (t1 [ n := t2 ]) := sorry

theorem substSubstSwap :
  ∀ n m t1 t2 t3,
  (t1 [ m := shiftₙ 0 (m+1) t2 ] [ (m+1) + n := shiftₙ 0 (m+1) t3 ]) =
  (t1 [ (m + 1) + n := shiftₙ 0 (m+1) t3 ] [ m := shiftₙ 0 (m+1) (t2 [ n := t3 ])]) := by
  intros n m t1 t2 t3
  match t1 with
  | var x => 
      simp [sub]
      by_cases h₁ : x = m <;> simp [h₁]
      · have h₂ : ¬ m = m + 1 + n := by linarith
        simp [sub, h₂]
        rw [shiftSubstSwap' (by linarith), Nat.add_comm n (m + 1)]
      · by_cases h₂ : x = m + 1 + n <;> simp [h₁, h₂, sub]
        refine substShiftedCancel ?_ ?_ (shiftShifted (m+1) 0 t3) <;> linarith
  | app l r => simp [sub, congrArg₂ Term.app (substSubstSwap n m l t2 t3) (substSubstSwap n m r t2 t3)]
  | Term.abs t1 =>
      have eq := congrArg Term.abs $ substSubstSwap n (m+1) t1 t2 t3
      simp [sub] at *
      rw [shiftAdd 1 (m+1) 0 t2, shiftAdd 1 (m+1) 0 t3, shiftAdd 1 (m+1) 0 (t2 [ n := t3 ])]
      rw [Nat.add_comm 1 (m + 1), Nat.add_right_comm (m + 1) n 1]
      exact eq 

-- the below are not used, partially equivalent to the above however
-- Pierce definition 6.1.2
inductive Term.free : Term → ℕ → Prop where
| var {k n: ℕ} : k < n → free (var k) n
| abs {n' : ℕ} {t₁ : Term} : free t₁ (n'+1) → free (abs t₁) n'
| app {n : ℕ} {t₁ t₂ : Term} : free t₁ n → free t₂ n → free (app t₁ t₂) n

-- Pierce exercise 6.2.3
theorem Term.free_shiftₙ (t : Term) (n c d: ℕ) (h : free t n) : free (t.shiftₙ c d) (n+d) := by
  revert c n
  induction t <;> intros n c h <;> cases h <;> constructor <;> try aesop <;> try linarith
  case abs body ih body_free =>
    have eq : n + d + 1 = n + 1 + d := by linarith
    rw [eq]
    exact ih (n+1) (c+1) body_free

-- Pierce exercise 6.2.6
theorem Term.free_sub {j n s t} : j ≤ n → free s n → free t n → free (t [j := s]) n := by
  revert j n s
  induction t <;> intros j n s h free_s free_t <;> simp [sub, shift]
  case var x => aesop
  all_goals (cases free_t; constructor; try aesop)
  case app => aesop
  case abs body ih body_free =>
    refine ih ?_ ?_ ?_
    · linarith
    · exact free_shiftₙ s n 0 1 free_s
    · assumption
