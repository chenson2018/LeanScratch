import LeanScratch.Untyped.Basic

-- much thanks to https://github.com/pi8027/lambda-calculus/blob/master/agda/Lambda/Confluence.agda

-- TODO: these all need some additional conditions about free variables, I'd like to use what I defined above
lemma sub_comm (m n : ℕ) (t1 t2 t3 : Term)
  : (t1 [m := t2.shiftₙ 0 (m+1)] [(m+1)+n := t3.shiftₙ 0 (m+1)]) = 
    (t1 [(m+1)+n := t3.shiftₙ 0 (m+1)] [m := (t2 [n := t3]).shiftₙ 0 (m+1)])
  := sorry

theorem unshiftSubstSwap {n : ℕ} (t1 t2 : Term) : (t1 [n+1 := t2.shift]).unshift = (t1.unshift [n := t2]) := sorry

