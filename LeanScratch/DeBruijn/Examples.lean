import LeanScratch.DeBruijn.Basic
import LeanScratch.DeBruijn.Reduction
import LeanScratch.DeBruijn.Beta

open Term

variable (T : Type)

-- some example for sanity checks
-- Pierce exercise 6.2.2
example : ({{{ (λ.λ. 1 (0 2)) }}} : Term T).shiftₙ 0 2 = {{{ λ. λ. 1 (0 4) }}} := by simp [shift, shiftₙ]
example : ({{{ λ. 0 1 (λ. 0 1 2) }}} : Term T).shiftₙ 0 2 = {{{ λ. 0 3 (λ. 0 1 4) }}} := by simp [shift, shiftₙ]

-- Pierce exercise 6.2.5
example : sub ({{{ (0 (λ.λ.2)) }}} : Term T) 0 {{{ 1 }}} = {{{ 1 (λ. λ. 3) }}}:= by simp [sub, shift, shiftₙ]
example : sub ({{{ (0 (λ.1)) }}} : Term T) 0 {{{ 1 (λ.2) }}} = {{{ (1 (λ.2)) (λ. (2 (λ.3))) }}} := by simp [sub, shift, shiftₙ] 
example : sub ({{{ (λ. 0 2) }}} : Term T) 0  {{{1}}} = {{{ λ. 0 2 }}} := by simp [sub, shift, shiftₙ]
example : sub ({{{ (λ. 1 0) }}} : Term T) 0 {{{1}}} = {{{ λ. 2 0 }}} := by simp [sub, shift, shiftₙ]

example : ({{{ 0 }}} : Term T) ↠β {{{ 0 }}} := by rfl

example : ({{{ (λ.0) 1 }}} : Term T) ↠β {{{ 1 }}} := by
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce

example : ({{{ (λ.1 0 2) (λ.0) }}} : Term T) ↠β {{{ 0 (λ.0) 1 }}} := by
  apply Relation.ReflTransGen.single
  apply Step_R.reduce
  apply β.reduce
