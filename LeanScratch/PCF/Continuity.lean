import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.CompletePartialOrder
import LeanScratch.PCF.FlatCPO

open OmegaCompletePartialOrder

-- TODO: propogate this to the interpretations of types/contexts...
-- or consider Mathlib.Control.LawfulFix again? (I doubt it, but leving this comment anyway)
theorem cpo_fix {α} [cpo : CompletePartialOrder α] [OrderBot α] (f : α →𝒄 α) : 
  f (⨆ (n : ℕ), f^[n] ⊥) = ⨆ (n : ℕ), f^[n] ⊥ := fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ (OrderBot.bot_le (f ⊥))

def bot_s : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| n => n + 1

def bot_p : WithBot ℕ → WithBot ℕ
| ⊥ => ⊥
| some n => some (n - 1)

theorem bot_s_p : bot_p ∘ bot_s = id := by
  ext
  case h x => induction x <;> aesop

def bot_cond : (WithBot ℕ × WithBot ℕ × WithBot ℕ) → WithBot ℕ
| (⊥,_,_) => ⊥
| (0,ret,_) => ret
| (some (_ + 1),_,ret) => ret

noncomputable def bot_s_hom : WithBot ℕ  →𝒄 WithBot ℕ where
  toFun := bot_s
  monotone' := by
    intros a b le
    induction a <;> simp [bot_s]
    case coe a =>
      induction b <;> simp [bot_s]
      case bot => aesop
      case coe b =>
        by_cases h : a = b
        case pos => aesop
        case neg =>
          exfalso
          exact WithBot.coe_nle_coe _ _ h le
  map_ωSup' c := by
    simp [ωSup]
    -- TODO: need a lemma to unfold the ⨆ on chains (as a set??) into the WithBot ⨆
    -- I think this is better than ω continuity
    sorry    
