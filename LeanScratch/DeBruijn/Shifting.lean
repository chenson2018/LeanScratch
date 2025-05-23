import LeanScratch.DeBruijn.Basic

open Term

theorem if_lt_le (n c: ℕ) {X : Type} (x x' : X) : (if n < c then x else x') = (if c ≤ n then x' else x) := by 
  by_cases h : c = n
  · simp [h]
  · by_cases h' : n < c <;> simp [h']
    · have h'' : ¬c ≤ n := by linarith
      simp [h'']
    · have h'' : c ≤ n := by linarith 
      simp [h'']

variable {T : Type}

-- directly translated from: https://github.com/pi8027/lambda-calculus/blob/master/agda/Lambda/Confluence.agda
inductive Shifted : ℕ → ℕ → Term T → Prop where
| sconst {d c m} : Shifted d c (const m)
| svar1 {d c n} : n < c → Shifted d c (var n)
| svar2 {d c n} : c + d ≤ n → d ≤ n → Shifted d c (var n)
| sapp {d c t1 t2} : Shifted d c t1 → Shifted d c t2 → Shifted d c (app t1 t2)
| sabs {d c t} : Shifted d (c+1) t → Shifted d c (abs t)

open Shifted

theorem shiftShifted (d c) (t : Term T) : Shifted d c (shiftₙ c d t) := by
  revert c
  induction t <;> intros c <;> simp [shiftₙ]
  case var x =>
    by_cases h : x < c <;> simp [h]
    · exact svar1 h
    · apply svar2 <;> linarith
  all_goals constructor <;> aesop

theorem shiftAdd (d d' c) (t : Term T) : (t.shiftₙ c d').shiftₙ c d = t.shiftₙ c (d + d') := by
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
  case const _ => rfl

theorem shiftUnshiftSwap {d c d' c'} {t : Term T} : 
  c' ≤ c → Shifted d' c' t → shiftₙ c d (t.unshiftₙ c' d') = unshiftₙ c' d' (t.shiftₙ (c + d') d) := by
    intros p1 p2
    match t, p2 with
    | const _, _ => rfl
    | _, sapp p2 p3 => exact congrArg₂ Term.app (shiftUnshiftSwap p1 p2) (shiftUnshiftSwap p1 p3)
    | _, sabs p2 => 
       simp [shiftₙ, unshiftₙ]
       rw [shiftUnshiftSwap (Nat.add_le_add_right p1 1) p2, Nat.add_right_comm c 1 d']
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
           exact h₁ p
         case neg.svar2 p₁ p₂ =>
           by_cases h₂ : n - d' < c <;> by_cases h₃ : n < c + d' <;> simp [h₁, h₂, h₃]
           case pos =>
              exfalso
              exact h₂ $ Nat.sub_lt_right_of_lt_add p₁ h₃
           all_goals by_cases h₄ : n + d < c' <;> simp [h₄]
           · linarith
           · exfalso
             exact h₃ $ (Nat.sub_lt_iff_lt_add' p₁).mp h₂
           · linarith
           · rw [Nat.sub_add_comm p₁]

theorem weakShifted {d c} {t : Term T} (n) : Shifted (d + n) c t → Shifted d (c + n) t := by
  intros h
  match n, h with
  | 0, s => exact s
  | _, sconst => constructor
  | _, svar1 p => constructor; linarith
  | _, svar2 p1 p2 => apply svar2 <;> linarith
  | _, sapp p1 p2 => exact sapp (weakShifted _ p1) (weakShifted _ p2)
  | n+1, sabs p => 
      refine sabs ?_
      rw [Nat.add_right_comm c (n + 1) 1]
      exact weakShifted _ p

theorem betaShifted' (n) (t1 t2 : Term T) : Shifted 1 n (t1 [ n := shiftₙ 0 (n+1) t2 ]) := 
  match t1 with
  | const _ => by constructor
  | app l r => sapp (betaShifted' n l t2) (betaShifted' n r t2)
  | Term.abs t1 => by
      simp [sub]
      rw [shiftAdd, Nat.add_comm 1 (n + 1)] 
      exact sabs $ betaShifted' (n+1) t1 t2
  | var n' => by
      simp [sub]
      by_cases h : n' = n <;> simp [h]
      · nth_rw 1 [←Nat.zero_add n]
        nth_rw 2 [Nat.add_comm]
        exact weakShifted _ $ shiftShifted (1+n) 0 t2
      · by_cases h' : n < n'
        · refine svar2 h' ?_
          exact Nat.one_le_of_lt h'
        · cases Nat.lt_or_gt.mp h <;> rename_i h''
          · exact svar1 h'' 
          · exact False.elim (h' h'')

theorem shiftShiftSwap (d c d' c') (t : Term T) : c ≤ c' → shiftₙ c d (t.shiftₙ c' d') = shiftₙ (c' + d) d' (shiftₙ c d t) := by
  intros p
  match t with
  | const _ => rfl
  | app l r => exact congrArg₂ Term.app (shiftShiftSwap d c d' c' l p) (shiftShiftSwap d c d' c' r p)
  | Term.abs body =>
      simp [shiftₙ]
      rw [shiftShiftSwap d (c+1) d' (c'+1) body (Nat.add_le_add_right p 1), Nat.add_right_comm c' 1 d]
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

theorem shiftSubstSwap' {d c n} (p1 : c ≤ n) (t1 t2 : Term T) : 
  shiftₙ c d (t1 [ n := t2 ]) = ((shiftₙ c d t1) [ n + d := shiftₙ c d t2 ]) := by
  match t1 with
  | const _ => rfl
  | var n' => 
      simp [shiftₙ, sub]
      by_cases h₁ : n' = n
  <;> by_cases h₂ : n' < c
  <;> by_cases h₃ : d = 0
  <;> simp [p1, h₁, h₂, h₃, shiftₙ]
      by_cases h₄ : n' = n + d <;> simp [h₄]
      cases t2 <;> simp [shiftₙ]
      case pos.var x => by_cases h₅ : x < c <;> simp [h₅] <;> linarith
      all_goals (apply h₁; linarith)
  | Term.abs t => 
      refine congrArg Term.abs ?_
      simp [sub]
      rw [shiftShiftSwap 1 0 d c t2 (Nat.zero_le c), shiftSubstSwap' _ t (shiftₙ 0 1 t2), Nat.add_right_comm n 1 d]
      linarith
  | app l r => exact congrArg₂ app (shiftSubstSwap' p1 l t2) (shiftSubstSwap' p1 r t2)

theorem substShiftedCancel {d c n} {t1 t2 : Term T} : c ≤ n → n < c + d → Shifted d c t1 → t1 = (t1 [ n := t2 ]) := by
  intros p1 p2 p3
  match t1, p3 with
  | var n', svar1 _ | var n', svar2 _ _ => by_cases p₄ : n' = n <;> simp [sub, p₄]; linarith
  | _, sapp p3 p4 => 
      simp [sub]
      exact ⟨substShiftedCancel p1 p2 p3, substShiftedCancel p1 p2 p4⟩
  | const _, _ => rfl
  | _, sabs p3 =>
      simp [sub]
      refine substShiftedCancel ?_ ?_ p3 <;> linarith

theorem substSubstSwap (n m) (t1 t2 t3 : Term T) :
  (t1 [ m := shiftₙ 0 (m+1) t2 ] [ (m+1) + n := shiftₙ 0 (m+1) t3 ]) =
  (t1 [ (m + 1) + n := shiftₙ 0 (m+1) t3 ] [ m := shiftₙ 0 (m+1) (t2 [ n := t3 ])]) := by
  match t1 with
  | const _ => rfl
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

theorem shiftSubstSwap {d c n} (p : n < c) (t1 t2 : Term T) :
  shiftₙ c d (t1 [ n := t2 ]) = ((shiftₙ c d t1) [ n := shiftₙ c d t2 ]) := by
  match t1 with
  | const _ => rfl
  | app l r => 
      simp [sub, shiftₙ]
      exact ⟨shiftSubstSwap p l t2, shiftSubstSwap p r t2⟩
  | Term.abs t1 =>
      simp [sub, shiftₙ]
      rw [shiftShiftSwap _ _ _ _ _ (by linarith)]
      exact shiftSubstSwap (by linarith) t1 (shiftₙ 0 1 t2)
  | var n' =>
      simp [sub, shiftₙ]
      by_cases p₁ : n' = n <;> simp [p₁, shiftₙ]
      · by_cases p₂ : n < c <;> simp [p₁, p₂]
        simp_all
      · by_cases p₂ : n' < c 
    <;> by_cases p₃ : n' + d = n
    <;> cases t2
    <;> simp [p₁, p₂, p₃, shiftₙ]
        case pos.var x => by_cases p₄ : x < c <;> simp [p₄] <;> linarith
        all_goals (apply p₂; linarith)

theorem unshiftUnshiftSwap {d c d' c'} {t : Term T} : c' ≤ c → Shifted d' c' t → Shifted d c (unshiftₙ c' d' t) →
  unshiftₙ c d (unshiftₙ c' d' t) = unshiftₙ c' d' (unshiftₙ (c + d') d t) := by
  intros p1 p2 p3
  match t, p2, p3 with
  | var n, s, s' => 
      simp [unshiftₙ] at *
      rw [if_lt_le n c', if_lt_le n (c + d')]
      rw [if_lt_le n c'] at s'
      by_cases p4 : c' ≤ n <;> by_cases p5 : c + d' ≤  n <;> simp [p4] at s' <;> simp [p4, p5]
      · rw [if_lt_le (n - d') c, if_lt_le (n - d) c']
        by_cases p6 : c ≤ n - d' <;> by_cases p7 : c' ≤ n - d <;> simp [p6, p7]
        · exact Nat.sub_right_comm n d' d
        · cases s' <;> exfalso
          case neg.svar1 => linarith
          case neg.svar2 p8 p9 =>
            apply p7
            calc
              c' ≤ c           := p1
              _  ≤ n - d' - d  := Nat.le_sub_of_add_le p9
              _  ≤ n - d  - d' := by rw [Nat.sub_right_comm n d' d ]
              _  ≤ n - d       := Nat.sub_le (n - d) d'
        all_goals exfalso; apply p6; exact Nat.le_sub_of_add_le p5
      · rw [if_lt_le, if_lt_le]
        by_cases p6 : c' ≤ n <;> by_cases p7 : c ≤ n - d' <;> simp [p6, p7] <;> exfalso
        · cases s
          case pos.svar1 => linarith
          case pos.svar2 p8 p9 => 
            apply p5
            exact Nat.add_le_of_le_sub p8 p7
        all_goals exact p6 p4
      · by_cases p6 :  n < c <;> by_cases p7 : n - d < c' <;> simp [p6, p7] <;> exfalso <;> linarith
      · by_cases p6 :  n < c <;> by_cases p7 :  n < c' <;> simp [p6, p7] <;> linarith
  | const _, _, _ => rfl
  | _, sapp l r, sapp l' r' => exact congrArg₂ app (unshiftUnshiftSwap p1 l l') (unshiftUnshiftSwap p1 r r')
  | _, sabs t, sabs t' => 
      refine congrArg Term.abs ?_
      rw [Nat.add_right_comm c d' 1]
      exact unshiftUnshiftSwap (by linarith) t t'

theorem unshiftShiftSwap {d c d' c'} {t : Term T} : c' ≤ c → Shifted d c t →
  shiftₙ c' d' (unshiftₙ c d t) = unshiftₙ (c + d') d (shiftₙ c' d' t) := by
  intros p s 
  match t, s with
  | var n, s => 
      simp [unshiftₙ, shiftₙ]
      rw [if_lt_le n c, if_lt_le n c']
      by_cases p1 : c ≤ n <;> by_cases p2 : c' ≤ n <;> simp [p1, p2]
      · rw [if_lt_le (n - d) c']
        cases s
        case pos.svar1 => exfalso; linarith
        case pos.svar2 p5 p6 => 
        by_cases p3 : c' ≤ n - d <;> by_cases p4 : c + d' ≤ n + d' <;> rw [if_lt_le n c] <;> simp [p1, p3]
        · symm
          exact Nat.sub_add_comm p5
        · linarith
        · exfalso; apply p3
          trans
          exact p
          exact Nat.le_sub_of_add_le p6
        · linarith
      · linarith
      · rw [if_lt_le n c, if_lt_le n c']
        simp [p1, p2]
      · have h : n < c + d' := by linarith
        simp [p2, h]
  | _, sabs s1 => 
      refine congrArg Term.abs ?_
      rw [Nat.add_right_comm c d' 1]
      refine unshiftShiftSwap (by linarith) s1
  | _, sapp s1 s2 => exact congrArg₂ app (unshiftShiftSwap p s1) (unshiftShiftSwap p s2)
  | const _, _ => rfl

theorem shiftShifted' {d c d' c'} {t : Term T} : c' ≤ d + c → Shifted d c t → Shifted d (d' + c) (shiftₙ c' d' t) := by
  intros p s
  match t, s with
  | const _, _ => simp [shiftₙ]; constructor
  | var n, svar1 p2 => 
      by_cases p1 : n < c' <;> apply svar1 <;> simp [p1]
      · exact Nat.lt_add_left d' p2
      · linarith
  | var n, svar2 p2 p3 =>
      by_cases p1 : c' ≤ n
      · refine svar2 ?_ ?_ <;> rw [if_lt_le n c'] <;> simp [p1] <;> linarith
      · linarith
  | _, sapp s1 s2 => exact sapp (shiftShifted' p s1) (shiftShifted' p s2)
  | Term.abs t1, sabs s1 =>
      refine sabs ?_
      rw [Nat.add_assoc]
      exact shiftShifted' (by linarith) s1

theorem unshiftSubstSwap2 {d c n} {t1 t2 : Term T} :
  n < c → Shifted d c t1 → Shifted d c t2 →
  unshiftₙ c d (t1 [ n := t2 ]) = ((unshiftₙ c d t1) [ n := unshiftₙ c d t2 ]) := by
  intros p s1 s2
  match t1, s1 with
  | var n', s => 
      simp [sub, unshiftₙ]
      rw [if_lt_le n' c]  
      by_cases p1 : n' = n <;> by_cases p2 : c ≤ n' <;> simp [p1, p2, unshiftₙ]
      · linarith
      · aesop
      · rw [if_lt_le n' c]
        simp [p2]
        by_cases p3 : c ≤ n' <;> by_cases p4 : n' - d = n <;> simp [p3, p4]
        · cases s <;> exfalso
          case pos.svar1 => linarith
          case pos.svar2 p5 p6 =>
            apply Nat.not_succ_le_self n'
            calc
              n' + 1 ≤ (n+d)+1 := by rw [(Nat.sub_eq_iff_eq_add p5).mp p4 ]
              _      ≤ c + d   := by linarith
              _      ≤ n'      := p6
        · linarith
  | _, sapp l r => exact congrArg₂ app (unshiftSubstSwap2 p l s2) (unshiftSubstSwap2 p r s2)
  | _, sabs s1 =>
      refine congrArg Term.abs ?_
      simp [sub, unshiftₙ]
      rw [unshiftShiftSwap (Nat.zero_le c) s2]
      refine unshiftSubstSwap2 (Nat.add_lt_add_right p 1) s1 ?_ 
      rw [Nat.add_comm]
      refine shiftShifted' (by linarith) s2
  | const _, _ => rfl

theorem unshiftShiftSetoff {d c d' c'} (t : Term T) : 
  c ≤ c' → c' ≤ d' + d + c → unshiftₙ c' d' (shiftₙ c (d' + d) t) = shiftₙ c d t := by
  intros p1 p2
  match t with
  | var n => 
      simp [shiftₙ, unshiftₙ]
      rw [if_lt_le n c]
      by_cases p3 : c ≤ n <;> simp [p3]
      · rw [if_lt_le]
        by_cases p4 : c' ≤ (n + (d' + d)) <;> simp [p4]
        · rw [if_lt_le]
          simp [p3]
          omega
        · omega
      · rw [if_lt_le n c]
        simp [p3]
        intros
        linarith
  | const _ => rfl
  | app t1 t2 => exact congrArg₂ app (unshiftShiftSetoff t1 p1 p2) (unshiftShiftSetoff t2 p1 p2)
  | Term.abs t => exact congrArg Term.abs $ unshiftShiftSetoff t (by linarith) (by linarith)

theorem betaShifted2 {d c n} {t1 t2 : Term T} : 
  Shifted d ((n+1)+c) t1 → 
  Shifted d c t2 →
  Shifted d (n + c) (unshiftₙ n 1 (t1 [ n := shiftₙ 0 (n+1) t2 ])) := by
  intros s1 s2
  match t1, s1 with
  | const _, _ => constructor
  | var n', s =>
      simp [sub]
      by_cases p₁ : n' = n <;> simp [p₁]
      · nth_rw 2 [Nat.add_comm]
        rw [unshiftShiftSetoff t2 (by linarith) (by linarith)]
        exact shiftShifted' (by linarith) s2
      · simp [unshiftₙ]
        by_cases p₂ : n' < n <;> simp [p₂]
        · exact svar1 $ Nat.lt_add_right c p₂
        · cases n' <;> cases n <;> cases s <;> simp
          case neg.succ.zero.svar2 => exact svar2 (by linarith) (by linarith)
          case neg.succ.succ.svar2 => exact svar2 (by linarith) (by linarith)
          exact False.elim (p₁ rfl)
          exact False.elim (p₁ rfl)
          all_goals exact svar1 (by linarith)
  | _, sapp sl sr => exact sapp (betaShifted2 sl s2) (betaShifted2 sr s2)
  | _, sabs s => 
      simp [sub, unshiftₙ]
      apply sabs
      rw [Nat.add_right_comm (n + 1) c 1] at s
      rw [shiftAdd 1 (n+1) 0 t2, Nat.add_right_comm n c 1, Nat.add_comm 1 (n + 1)]
      exact betaShifted2 s s2

theorem unshiftSubstSwap {c n} (t1 t2 : Term T) : c ≤ n → Shifted 1 c t1 →
  unshiftₙ c 1 (t1 [ n+1 := shiftₙ 0 (c+1) t2 ]) = ((unshiftₙ c 1 t1) [ n := shiftₙ 0 c t2 ]) := by
  intros p1 p2
  match t1, p2 with
  | var n', s => 
      simp [unshiftₙ, sub]
      rw [if_lt_le]
      by_cases p3 : n' = n + 1 <;> by_cases p4 : c ≤ n' <;> simp [p3, p4] 
      · by_cases p5 : n = n' - 1
        · have h : c ≤ n + 1 := by linarith
          simp [h]
          rw [Nat.add_comm]
          refine unshiftShiftSetoff t2 ?_ ?_ <;> linarith
        · exfalso; apply p5; exact Nat.eq_sub_of_add_eq (id (Eq.symm p3))
      · have h : c ≤ n + 1 := by linarith
        aesop
      · simp [unshiftₙ]
        rw [if_lt_le]
        simp [p4]
        by_cases p6 : n' - 1 = n <;> simp [p6]
        cases s <;> exfalso
        · apply Nat.not_succ_le_self n' 
          linarith
        · apply p3
          refine (Nat.sub_eq_iff_eq_add ?_).mp p6
          assumption
      · simp [unshiftₙ]
        rw [if_lt_le]
        simp [p4]
        by_cases p6 : n' = n <;> simp [p6]
        linarith
  | const _, _ => rfl
  | Term.abs t1, sabs p2 => 
      refine congrArg Term.abs ?_
      simp [shift]
      rw [shiftAdd 1 (c+1) 0 t2, shiftAdd 1 c 0 t2, Nat.add_comm 1 (c + 1), Nat.add_comm 1 c]
      exact unshiftSubstSwap t1 t2 (by linarith) p2
  | app l r, sapp p2 p3 => 
      simp [sub, unshiftₙ]
      exact ⟨unshiftSubstSwap l t2 p1 p2, unshiftSubstSwap r t2 p1 p3⟩

theorem shiftZero (c) (t : Term T) : t = shiftₙ c 0 t := by
  revert c
  induction t <;> simp [shiftₙ] <;> intros c
  case abs t ih => exact ih (c + 1)
  case app l r ih_l ih_r => exact ⟨ih_l c, ih_r c⟩

theorem unshiftSubstSwap' {n} (t1 t2 : Term T) :
  Shifted 1 0 t1 → unshiftₙ 0 1 (t1 [ n+1 := shiftₙ 0 1 t2 ]) = ((unshiftₙ 0 1 t1) [ n := t2 ]) := by
  intros p
  rw [congrArg ((unshiftₙ 0 1 t1) [ n := · ]) (shiftZero 0 t2)]
  exact unshiftSubstSwap t1 t2 (Nat.zero_le n) p

-- the below are not used, partially equivalent to the above however
-- Pierce definition 6.1.2
inductive Term.free : Term T → ℕ → Prop where
| var {k n: ℕ} : k < n → free (var k) n
| abs {n' : ℕ} {t₁ : Term T} : free t₁ (n'+1) → free (abs t₁) n'
| app {n : ℕ} {t₁ t₂ : Term T} : free t₁ n → free t₂ n → free (app t₁ t₂) n

-- Pierce exercise 6.2.3
theorem Term.free_shiftₙ (t : Term T) (n c d: ℕ) (h : free t n) : free (t.shiftₙ c d) (n+d) := by
  revert c n
  induction t <;> intros n c h <;> cases h <;> constructor
  case abs body ih body_free =>
    rw [Nat.add_right_comm n d 1]
    exact ih (n + 1) (c + 1) body_free
  case var.var.a => split <;> linarith
  all_goals aesop

-- Pierce exercise 6.2.6
theorem Term.free_sub {j n} {s t : Term T} : j ≤ n → free s n → free t n → free (t [j := s]) n := by
  revert j n s
  induction t <;> intros j n s h free_s free_t <;> simp [sub, shift]
  case var x => aesop
  case const => aesop
  all_goals (cases free_t; constructor; try aesop)
  case app => aesop
  case abs body ih body_free =>
    refine ih ?_ ?_ ?_
    · linarith
    · exact free_shiftₙ s n 0 1 free_s
    · assumption
