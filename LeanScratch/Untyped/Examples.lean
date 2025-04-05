import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Reduction
import LeanScratch.Untyped.Beta

open Term

-- some example for sanity checks
-- Pierce exercise 6.2.2
example : {{{ (λ.λ. 1 (0 2)) }}}.shiftₙ 0 2 = {{{ λ. λ. 1 (0 4) }}} := by simp [shift, shiftₙ]
example : {{{ λ. 0 1 (λ. 0 1 2) }}}.shiftₙ 0 2 = {{{ λ. 0 3 (λ. 0 1 4) }}} := by simp [shift, shiftₙ]

-- Pierce exercise 6.2.5
example : sub {{{ (0 (λ.λ.2)) }}} 0 {{{ 1 }}} = {{{ 1 (λ. λ. 3) }}}:= by simp [sub, shift, shiftₙ]
example : sub {{{ (0 (λ.1)) }}} 0 {{{ 1 (λ.2) }}} = {{{ (1 (λ.2)) (λ. (2 (λ.3))) }}} := by simp [sub, shift, shiftₙ] 
example : sub {{{ (λ. 0 2) }}} 0  {{{1}}} = {{{ λ. 0 2 }}} := by simp [sub, shift, shiftₙ]
example : sub {{{ (λ. 1 0) }}} 0 {{{1}}} = {{{ λ. 2 0 }}} := by simp [sub, shift, shiftₙ]

example : {{{ 0 }}} ↠β {{{ 0 }}} := by rfl

example : {{{ (λ.0) 1 }}} ↠β {{{ 1 }}} := by
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce

example : {{{ (λ.1 0 2) (λ.0) }}} ↠β {{{ 0 (λ.0) 1 }}} := by
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce
