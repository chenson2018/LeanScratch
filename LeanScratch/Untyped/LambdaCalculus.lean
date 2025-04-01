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

syntax "{{{ " embedded " }}}" : term
open Lean in
macro_rules
  | `({{{ ( $e ) }}}) => `({{{ $e }}})
  | `({{{ $x:num }}}) => `(Term.var $x)
  | `({{{ $e1 $e2 }}}) => `(Term.app {{{ $e1 }}} {{{ $e2 }}})
  | `({{{ λ $body }}}) => `(Term.abs {{{ $body }}})
  | `({{{ λ . $body }}}) => `(Term.abs {{{ $body }}})

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

-- Pierce exercise 6.2.2
example : {{{ (λ.λ. 1 (0 2)) }}}.shift 2 = {{{ λ. λ. 1 (0 4) }}} := by simp [shift, shiftₙ]
example : {{{ λ. 0 1 (λ. 0 1 2) }}}.shift 2 = {{{ λ. 0 3 (λ. 0 1 4) }}} := by simp [shift, shiftₙ]

def Term.sub (t : Term) (j : ℕ) (s : Term) : Term := 
  match t with
  | var k     => if k = j then s else var k
  | abs t₁    => abs $ sub t₁ (j+1) (s.shift 1)
  | app t₁ t₂ => app (sub t₁ j s) (sub t₂ j s)

-- Pierce exercise 6.2.5
example : sub {{{ (0 (λ.λ.2)) }}} 0 {{{ 1 }}} = {{{ 1 (λ. λ. 3) }}}:= by simp [sub, shift, shiftₙ]
example : sub {{{ (0 (λ.1)) }}} 0 {{{ 1 (λ.2) }}} = {{{ (1 (λ.2)) (λ. (2 (λ.3))) }}} := by simp [sub, shift, shiftₙ] 
example : sub {{{ (λ. 0 2) }}} 0  {{{1}}} = {{{ λ. 0 2 }}} := by simp [sub, shift, shiftₙ]
example : sub {{{ (λ. 1 0) }}} 0 {{{1}}} = {{{ λ. 2 0 }}} := by simp [sub, shift, shiftₙ]

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

inductive Conv : Term → Term → Prop
| app_r {M N Z} : Conv M N → Conv (app M Z) (app N Z)
| app_l {M N Z} : Conv M N → Conv (app Z M) (app Z N)
| beta  {t v}   : Conv (app (abs t) v) ((t.sub 0 (v.shift 1)).unshift 1)
-- TODO: shifting here, and do I want eta??
-- | eta   {M N}   : Conv M N → Conv (abs M) (abs N)

@[simp]
def ConvEquiv := Relation.EqvGen Conv

notation:39 t " =β " t' => ConvEquiv t t'

example : {{{ 0 }}} =β {{{ 0 }}} := by
  simp
  apply Relation.EqvGen.refl

example : {{{ (λ.0) 1 }}} =β {{{ 1 }}} := by
  simp
  apply Relation.EqvGen.rel
  · apply Conv.beta

example : {{{ (λ.1 0 2) (λ.0) }}} =β {{{ 0 (λ.0) 1 }}} := by
  simp
  apply Relation.EqvGen.rel
  apply Conv.beta
