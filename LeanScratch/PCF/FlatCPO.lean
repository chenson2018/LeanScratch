import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.TypeTags
import Mathlib.Order.SetNotation
import Mathlib.Order.WithBot

-- sanity check that we didn't imoprt another instance
-- #synth OmegaCompletePartialOrder (WithBot ℕ)

variable {α : Type}

namespace WithBot

@[simp]
instance le_flat : LE (WithBot α) where
  le a₁ a₂ := a₁ = ⊥ ∨ a₁ = a₂

@[simp]
instance lt_flat : LT (WithBot α) where
  lt a₁ a₂ := a₁ = ⊥ ∧ a₂ ≠ ⊥

instance preorder_flat : Preorder (WithBot α) where
  le_refl a := by aesop
  le_trans a b c ab bc := by aesop
  lt_iff_le_not_le := by aesop

instance partialOrder_flat : PartialOrder (WithBot α) where
  le_antisymm a b ab ba := by cases ab <;> cases ba <;> aesop

/-- two non-⊥ elements of a directed set must be equal -/
theorem directed_coe_unique {S : Set (WithBot α)} (dir : DirectedOn WithBot.le_flat.le S) {a₁ a₂ : α}
  : ↑a₁ ∈ S → ↑a₂ ∈ S → a₁ = a₂ := by
  intros mem₁ mem₂ 
  simp [DirectedOn] at dir
  have ⟨a₃, mem₃, h₁, h₂⟩ := dir _ mem₁ _ mem₂  
  simp_all only [coe_ne_bot, false_or]
  subst h₁
  simp_all only [coe_inj]

-- TODO: is this inherently classical?? 
open scoped Classical in
noncomputable instance instSupSet : SupSet (WithBot α) where
  sSup s := if h : ∃ v : α, ↑v ∈ s then h.choose else ⊥ 

noncomputable instance instCompletePartialOrder : CompletePartialOrder (WithBot α) where
  lubOfDirected s dir := by
    constructor <;> intros a mem <;> simp [sSup]
    · induction a
      case left.bot => left; rfl
      case left.coe a =>
        split
        case isTrue h =>
          rw [directed_coe_unique dir mem h.choose_spec]
        case isFalse h =>
          simp_all only [not_exists]
    · simp [upperBounds] at mem
      induction a
      · split
        case right.bot.isTrue h => exact mem h.choose_spec
        case right.bot.isFalse => rfl
      · split
        case right.coe.isTrue h => exact mem h.choose_spec
        case right.coe.isFalse => left; rfl

end WithBot

#synth CompletePartialOrder (WithBot ℕ)
#synth OmegaCompletePartialOrder (WithBot ℕ)
