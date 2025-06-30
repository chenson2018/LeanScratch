import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Order.CompletePartialOrder
import LeanScratch.PCF.FlatCPO

open OmegaCompletePartialOrder Function

-- TODO: propogate this to the interpretations of types/contexts...
-- or consider Mathlib.Control.LawfulFix again? (I doubt it, but leving this comment anyway)
theorem cpo_fix {α} [cpo : CompletePartialOrder α] [OrderBot α] (f : α →𝒄 α) : 
  f (⨆ (n : ℕ), f^[n] ⊥) = ⨆ (n : ℕ), f^[n] ⊥ := fixedPoints.ωSup_iterate_mem_fixedPoint f ⊥ (OrderBot.bot_le (f ⊥))

-- if a function maintains ⊥, it is monotone
theorem map_bot_mono {α} (f : WithBot α → WithBot α) (h : f ⊥ = ⊥) : Monotone f := by
  intros a b le
  cases a <;> cases le <;> aesop

def lift {α} (f : α → α) : WithBot α → WithBot α 
| ⊥ => ⊥ 
| some a => some (f a)

theorem lift_mono {α} (f : α → α) : Monotone (lift f) := map_bot_mono (lift f) rfl

theorem lift_left_inverse {α} {f g : α → α} : LeftInverse f g → LeftInverse (lift f) (lift g) := by
  simp [LeftInverse]
  intros inv a
  induction a <;> simp [lift]
  aesop

theorem succ_pred_inv : LeftInverse (· - 1) (· + 1) := by simp [LeftInverse]

def bot_s := lift (· + 1)
def bot_p := lift (· - 1)

theorem bot_s_p : bot_p ∘ bot_s = id := by
  have inv := lift_left_inverse succ_pred_inv
  aesop

-- TODO: I think needed for ωSup
theorem mono_ext {α} {c : Chain (WithBot α)} (mono : WithBot α →o WithBot α) 
  : (∃ a : α, ↑a ∈ c) ↔ (∃ a : α, ↑a ∈ c.map mono) := sorry

theorem ωSup_bot {α} {c : Chain (WithBot α)} (f : WithBot α →o WithBot α) : ωSup c = ⊥ → ωSup (c.map f) = ⊥ := by
  simp only [ωSup]
  intros h
  simp only [dite_eq_right_iff] at h
  split
  case isTrue h' =>
    obtain ⟨a_im, mem⟩ := h'
    exfalso
    refine WithBot.coe_ne_bot (h ?_)
    sorry
  case isFalse => rfl

theorem ωSup_coe {α} {c : Chain (WithBot α)} (f : WithBot α →o WithBot α) {a : α} : ωSup c = ↑a → ωSup (c.map f) = f ↑a := 
  sorry

noncomputable def bot_s_hom : WithBot ℕ  →𝒄 WithBot ℕ where
  toFun := bot_s
  monotone' := lift_mono (· + 1)
  map_ωSup' c := sorry

noncomputable def bot_p_hom : WithBot ℕ  →𝒄 WithBot ℕ where
  toFun := bot_p
  monotone' := lift_mono (· - 1)
  map_ωSup' c := sorry

def bot_cond : (WithBot ℕ × WithBot ℕ × WithBot ℕ) → WithBot ℕ
| (⊥,_,_) => ⊥
| (0,ret,_) => ret
| (some (_ + 1),_,ret) => ret

theorem bot_cond_mono : Monotone bot_cond := by
  intros p₁ p₂ le
  obtain ⟨c₁, i₁, e₁⟩ := p₁
  obtain ⟨c₂, i₂, e₂⟩ := p₂ 
  simp [bot_cond]
  cases le
  next le_c le =>
    cases le
    next le_i le_e =>
      simp_all
      cases le_c
      case inl => simp_all
      case inr eq₁ =>
        subst eq₁
        induction c₁
        case bot => simp
        case coe n =>
          cases n <;> simp <;> assumption

noncomputable def bot_cond_hom : (WithBot ℕ × WithBot ℕ × WithBot ℕ) →𝒄 WithBot ℕ where
  toFun := bot_cond
  monotone' := bot_cond_mono
  map_ωSup' c := sorry
