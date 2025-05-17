import LeanScratch.DeBruijn.Basic

open Term

variable {T : Type}

-- Barendregt chapter 3
inductive Step_R (R : Term T → Term T → Prop) : Term T → Term T → Prop
| reduce {M N}   : R M N → Step_R R M N
| ξₗ     {M N Z} : Step_R R M N → Step_R R (app Z M) (app Z N)
| ξᵣ     {M N Z} : Step_R R M N → Step_R R (app M Z) (app N Z)
| ξ      {M N}   : Step_R R M N → Step_R R (abs M)   (abs N) 

notation:39 t " ⇢" R:arg t' => Step_R                        R  t t'
notation:39 t " ↠" R:arg t' => Relation.ReflTransGen (Step_R R) t t'

-- leaving this one for notation purposes...
@[simp]
def Equality_R  (R : Term T → Term T → Prop) := Relation.EqvGen (Step_R R)
notation:39 t " ≈" R:arg t':arg => Equality_R  R t t'

-- some congruence lemmas about reduction
theorem app_l_cong {M M' N} {R : Term T → Term T → Prop} : (M ↠R M') → (app M N ↠R app M' N) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξᵣ r)

theorem app_r_cong {N N' M} {R : Term T → Term T → Prop} : (N ↠R N') → (app M N ↠R app M N') := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξₗ r)

theorem abs_cong {N N'} {R : Term T → Term T → Prop} : ( N ↠R N') → (N.abs ↠R N'.abs) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξ r)

-- (not used anywhere else, but interesting)
theorem sub_reduction 
  (i : ℕ) (M N N' : Term T) (R : Term T → Term T → Prop) (h :N ↠R N') 
  (shift_reduction : ∀ t t', (t ↠R t') → shiftₙ 0 1 t ↠R shiftₙ 0 1 t')
  : (M [i := N]) ↠R (M [i := N']) := by
  revert i N N'
  induction M <;> intros i N N' h
  case var x' => by_cases eq : x' = 0 <;> simp [sub, eq] <;> aesop
  case abs body ih =>
    apply abs_cong
    simp [sub]
    refine ih (i + 1) (shiftₙ 0 1 N) (shiftₙ 0 1 N') ?_
    exact shift_reduction N N' h
  case app l r ih_l ih_r =>
    calc
      app (l[i:=N]) (r[i:=N]) ↠R app (l [i := N']) (r [i :=N ]) := app_l_cong (ih_l _ _ _ h)
      _                       ↠R app (l [i := N']) (r [i :=N']) := app_r_cong (ih_r _ _ _ h)
  case const m => rfl
