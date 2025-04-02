import Mathlib
open Std (Format)
open Lean.Parser (maxPrec argPrec minPrec)

inductive Term
| var (x : ℕ) : Term
| abs (body : Term) : Term
| app (left right : Term) : Term

open Term

-- adapted from https://lean-lang.org/blog/2024-3-21-quasiquotation-with-binders-a-lean-metaprogramming-example/
def Term.format (prec : Nat) : Term → Format
| var x => x.repr
| app e1 e2 => fmtApp <| e1.format argPrec ++ .line ++ e2.format maxPrec
| abs body => Format.paren <| "λ" ++ .nest 2 (.line ++ body.format minPrec)
  where
    fmtApp (elts : Format) : Format :=
      Repr.addAppParen (.group (.nest 2 elts)) prec

instance Term.instRepr : Repr Term where
  reprPrec tm _ := .group <| .nest 2 (tm.format minPrec)

/-- Embedded language expression -/
declare_syntax_cat embedded
/-- A variable reference -/
syntax:max num : embedded
/-- Grouping of expressions -/
syntax "(" embedded ")" : embedded
/-- Function application -/
syntax:arg embedded:arg embedded:max : embedded
/-- A function -/
syntax:max "λ" "."? embedded:arg : embedded
/-- quasiquotation -/
syntax:max "~" term:max : embedded

syntax "{{{ " embedded " }}}" : term
open Lean in
macro_rules
  | `({{{ ( $e ) }}}) => `({{{ $e }}})
  | `({{{ $x:num }}}) => `(Term.var $x)
  | `({{{ $e1 $e2 }}}) => `(Term.app {{{ $e1 }}} {{{ $e2 }}})
  | `({{{ λ $body }}}) => `(Term.abs {{{ $body }}})
  | `({{{ λ . $body }}}) => `(Term.abs {{{ $body }}})
  | `({{{ ~$e }}}) => pure e

-- Pierce definition 6.2.1
def Term.shiftₙ (c d : ℕ) : Term → Term
| var k     => var $ if k < c then k else (k + d)
| abs t₁    => abs $ shiftₙ (c+1) d t₁
| app t₁ t₂ => app (shiftₙ c d t₁) (shiftₙ c d t₂)

@[simp]
def Term.shift := Term.shiftₙ 0

def Term.unshiftₙ (c d : ℕ) : Term → Term
| var k     => var $ if k < c then k else (k - d)
| abs t₁    => abs $ unshiftₙ (c+1) d t₁
| app t₁ t₂ => app (unshiftₙ c d t₁) (unshiftₙ c d t₂)

@[simp]
def Term.unshift := Term.unshiftₙ 0

def Term.sub (t : Term) (j : ℕ) (s : Term) : Term := 
  match t with
  | var k     => if k = j then s else var k
  | abs t₁    => abs $ sub t₁ (j+1) (s.shift 1)
  | app t₁ t₂ => app (sub t₁ j s) (sub t₂ j s)

notation:39 M "[" i ":=" N "]" => Term.sub M i N

-- definition 6.1.2
inductive free : Term → ℕ → Prop where
| var {k n: ℕ} : k < n → free (var k) n
| abs {n' : ℕ} {t₁ : Term} : free t₁ (n'+1) → free (abs t₁) n'
| app {n : ℕ} {t₁ t₂ : Term} : free t₁ n → free t₂ n → free (app t₁ t₂) n

-- exercise 6.2.6
theorem free_shiftₙ (t : Term) (n c d: ℕ) (h : free t n) : free (t.shiftₙ c d) (n+d) := by
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

theorem free_shift (t : Term) (n d: ℕ) (h : free t n) : free (t.shift d) (n+d) := free_shiftₙ t n 0 d h

-- TODO: I think this might work?
-- I have seen Agda examples where they carry it with the Term type, but I prefer it seperate...
lemma substitution_comm 
  {n : ℕ} 
  {M N L : Term} 
  (M_free : free M (n+2))
  (N_free : free N (n+1))
  (L_free : free L n)
  : (M [0 := N] [0 := L]) = (M [1 := L] [0 := N [0 := L]])
  := by sorry

-- Barendregt chapter 3
inductive Step_R (R : Term → Term → Prop) : Term → Term → Prop
| reduce {M N}   : R M N → Step_R R M N
| ξₗ     {M N Z} : Step_R R M N → Step_R R (app Z M) (app Z N)
| ξᵣ     {M N Z} : Step_R R M N → Step_R R (app M Z) (app N Z)
| ξ      {M N}   : Step_R R M N → Step_R R (abs M)   (abs N) 

@[simp]
def Reduction_R (R : Term → Term → Prop) := Relation.ReflTransGen (Step_R R)

@[simp]
def Equality_R  (R : Term → Term → Prop) := Relation.EqvGen (Step_R R)

notation:39 t " →" R:arg t' => Step_R      R t t'
notation:39 t " ↠" R:arg t' => Reduction_R R t t'
notation:39 t " =" R:arg t' => Equality_R  R t t'

-- we can say some things generally without setting a notion of reduction
-- TODO: should the index here be zero??
theorem sub_reduction (M N N' : Term) (R : Term → Term → Prop) (h :N ↠R N') 
  : (M [0 := N]) ↠R (M [0 := N']) := by
  induction M
  case var x' =>
    simp [sub]
    by_cases eq : x' = 0 <;> simp [eq]
    · exact h
    · apply Relation.ReflTransGen.refl
  case abs body ih =>
    sorry    
  case app l r ih_l ih_r =>
    sorry

@[simp]
abbrev Diamond {α} (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

@[simp]
abbrev Church_Rosser (R : Term → Term → Prop) := Diamond (Reduction_R R)

-- a couple of general lemmas
theorem diamond_ReflTrans {α} (R : α → α → Prop) (diamond : Diamond R) : Diamond (Relation.ReflTransGen R) := sorry

theorem equality_descendant 
  {R : Term → Term → Prop}
  (cr : Church_Rosser R) 
  {M N : Term}
  (eq : M =R N)
  : ∃ Z : Term, ((M ↠R Z) ∧ (N ↠R Z))
  := by
  induction eq
  case refl x =>
    exists x
    split_ands <;> exact Relation.ReflTransGen.refl
  case symm x y x_eq_y ih =>
    have ⟨Z, ⟨l, r⟩⟩ := ih
    exact ⟨Z, ⟨r, l⟩⟩
  case trans M L N M_L L_N ih_ML ih_LN =>
    have ⟨Z₁, ⟨l₁, r₁⟩⟩ := ih_ML
    have ⟨Z₂, ⟨l₂, r₂⟩⟩ := ih_LN
    have ⟨Z, ⟨l, r⟩⟩ := cr r₁ l₂
    exists Z
    and_intros
    · exact Relation.ReflTransGen.trans l₁ l
    · exact Relation.ReflTransGen.trans r₂ r
  case rel x y x_y =>
    exists y
    and_intros
    · apply Relation.ReflTransGen.single
      exact x_y
    · apply Relation.ReflTransGen.refl

-- now on to β-reduction specifically
inductive β : Term → Term → Prop
| reduce {M N} : β {{{ (λ . ~M) ~N }}} (M [0 := N.shift 1] |>.unshift 1) 

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
theorem progress' (M : Term) : Normalized M ∨ (∃ M', M =β M') := by
  induction (progress M)
  case done norm =>
    left
    exact norm
  case step M' M_M' =>
    right
    exists M'
    apply Relation.EqvGen.rel
    exact M_M'

-- mixing in the PLFA approach
inductive Parallel : Term → Term → Prop
| var (x : ℕ) : Parallel (var x) (var x)
| abs {N N'} : Parallel N N' →  Parallel (abs N) (abs N')
| app {L L' M M'} : Parallel L L' → Parallel M M' → Parallel {{{ ~L ~M }}} {{{ ~L' ~M' }}}
| beta {N N' M M'} : Parallel N N' → Parallel M M' → Parallel {{{ (λ . ~M) ~N }}} (M' [0 := N'.shift 1] |>.unshift 1)

-- TODO: is this not also a closure??? check at end
inductive ParallelChain : Term → Term → Prop
| refl (M) : ParallelChain M M
| seq  {M N : Term} (L : Term) : Parallel L M → ParallelChain M N → ParallelChain L N

notation:39 t " ⇉ "  t' => Parallel       t t'
notation:39 t " ⇉* " t' => ParallelChain t t'

theorem Parallel_refl : Reflexive (· ⇉ ·) := by
  simp [Reflexive]
  intros t
  induction t
  case var x => exact Parallel.var x
  case abs body ih => exact Parallel.abs ih
  case app l r l_ih r_ih => exact Parallel.app l_ih r_ih

theorem redex_iff_chain {M N} : (M ↠β N) ↔ M ⇉* N := sorry

theorem sub_para {x : ℕ} {N N' M M'} : (N ⇉ N') → (M ⇉ M') → (N [x := M] ⇉ N' [x := M']) := by
  intros N_N' M_M'
  induction N_N'
  case var x' =>
    simp [sub]
    by_cases eq : x' = x <;> simp [eq]
    · exact M_M'
    · exact Parallel.var x'
  case app _ _ _ _ _ _ s s' => exact Parallel.app s s'
  case abs body body' bp s => sorry
  case beta => sorry

def Term.plus (t : Term) : Term :=
  match t with
  | var x => var x
  | abs N => abs N.plus
  | app (abs N) M => N.plus [0 := M.plus]
  | app L M => app L.plus M.plus

theorem para_triangle {M N} : (M ⇉ N) → (N ⇉ M.plus) := by
  intros M_N
  induction M_N
  case var x =>
    exact Parallel.var x
  case abs _ _ _ ρ =>
    exact Parallel.abs ρ 
  case beta => sorry
  case app => sorry

theorem para_diamond : Diamond (· ⇉ · ) := by
  simp [Diamond]
  intros M N N' p1 p2
  exact ⟨M.plus, ⟨para_triangle p1, para_triangle p2⟩⟩

-- TOTO: having trouble with termination here...
theorem strip {M N N'} (MN : M ⇉ N) (MN' : M ⇉* N') : ∃L, ((N ⇉* L) ∧ (N' ⇉ L)):= sorry

-- the shadowing here is annoying, did my best to dfollow the PLFA names
theorem chain_diamond : Diamond (· ⇉* ·) := by
  simp [Diamond]
  intros L M₂ M₁ L_M₂
  revert M₁
  induction L_M₂
  case refl N =>
    intros M₁ L_M₁
    exact ⟨M₁, ⟨L_M₁, ParallelChain.refl M₁⟩⟩
  case seq L M₁ M₁' L_M₁_s M₁_M₁' ih =>
    intros M₂ L_M₁_c
    have ⟨N,  ⟨M₁_N_c, M₂_N_p⟩⟩ := strip L_M₁_s L_M₁_c
    have ⟨N', ⟨M₁'_N', N_N'⟩⟩ := ih M₁_N_c
    exact ⟨N', ⟨M₁'_N', ParallelChain.seq M₂ M₂_N_p N_N'⟩⟩

theorem confluence : Diamond (· ↠β ·) := by
  simp only [Diamond]
  intros L M₁ M₂ L_M₁ L_M₂
  have ⟨N, ⟨M₁_chain_N, M₂_chain_N⟩⟩ := chain_diamond (redex_iff_chain.mp L_M₁) (redex_iff_chain.mp L_M₂)
  exists N
  exact ⟨redex_iff_chain.mpr M₁_chain_N, redex_iff_chain.mpr M₂_chain_N⟩

-- some example for sanity checks
-- Pierce exercise 6.2.2
example : {{{ (λ.λ. 1 (0 2)) }}}.shift 2 = {{{ λ. λ. 1 (0 4) }}} := by simp [shift, shiftₙ]
example : {{{ λ. 0 1 (λ. 0 1 2) }}}.shift 2 = {{{ λ. 0 3 (λ. 0 1 4) }}} := by simp [shift, shiftₙ]

-- Pierce exercise 6.2.5
example : sub {{{ (0 (λ.λ.2)) }}} 0 {{{ 1 }}} = {{{ 1 (λ. λ. 3) }}}:= by simp [sub, shift, shiftₙ]
example : sub {{{ (0 (λ.1)) }}} 0 {{{ 1 (λ.2) }}} = {{{ (1 (λ.2)) (λ. (2 (λ.3))) }}} := by simp [sub, shift, shiftₙ] 
example : sub {{{ (λ. 0 2) }}} 0  {{{1}}} = {{{ λ. 0 2 }}} := by simp [sub, shift, shiftₙ]
example : sub {{{ (λ. 1 0) }}} 0 {{{1}}} = {{{ λ. 2 0 }}} := by simp [sub, shift, shiftₙ]

example : {{{ 0 }}} ↠β {{{ 0 }}} := by simp [Relation.ReflTransGen.refl]

example : {{{ (λ.0) 1 }}} ↠β {{{ 1 }}} := by
  simp
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce

example : {{{ (λ.1 0 2) (λ.0) }}} ↠β {{{ 0 (λ.0) 1 }}} := by
  simp
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce
