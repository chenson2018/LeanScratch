import Mathlib

inductive Term
| var (x : ℕ) : Term
| abs (body : Term) : Term
| app (left right : Term) : Term

open Term

-- Pierce definition 6.2.1
def Term.shiftₙ (c d : ℕ) : Term → Term
| var k     => var (if k < c then k else k + d)
| abs t₁    => abs $ shiftₙ (c+1) d t₁
| app t₁ t₂ => app (shiftₙ c d t₁) (shiftₙ c d t₂)

@[simp]
def Term.shift := Term.shiftₙ 0 1

def Term.unshiftₙ (c d : ℕ) : Term → Term
| var k     => var $ if k < c then k else (k - d)
| abs t₁    => abs $ unshiftₙ (c+1) d t₁
| app t₁ t₂ => app (unshiftₙ c d t₁) (unshiftₙ c d t₂)

@[simp]
def Term.unshift := Term.unshiftₙ 0 1

def Term.sub (t : Term) (j : ℕ) (s : Term) : Term := 
  match t with
  | var k     => if k = j then s else var k
  | abs t₁    => abs $ sub t₁ (j+1) s.shift
  | app t₁ t₂ => app (sub t₁ j s) (sub t₂ j s)

notation:39 M "[" i ":=" N "]" => Term.sub M i N

-- the remainder of this file is for notation
-- adapted from https://lean-lang.org/blog/2024-3-21-quasiquotation-with-binders-a-lean-metaprogramming-example/

open Std (Format)
open Lean.Parser (maxPrec argPrec minPrec)

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
