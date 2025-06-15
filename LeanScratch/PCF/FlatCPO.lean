import Mathlib
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.TypeTags
import Mathlib.Order.SetNotation
import Mathlib.Order.WithBot

attribute [-instance] WithBot.le
attribute [-instance] WithBot.lt
attribute [-instance] WithBot.preorder
attribute [-instance] WithBot.partialOrder
attribute [-instance] WithBot.semilatticeInf
attribute [-instance] WithBot.lattice
attribute [-instance] WithBot.conditionallyCompleteLattice
attribute [-instance] WithBot.distribLattice
attribute [-instance] WithBot.linearOrder
attribute [-instance] WithBot.semilatticeSup
attribute [-instance] WithBot.instSupSet

/-
-- sanity check that we didn't imoprt another instance
#synth LE (WithBot ℕ)
#synth LT (WithBot ℕ)
#synth Preorder (WithBot ℕ)
#synth PartialOrder (WithBot ℕ)
#synth SupSet (WithBot ℕ)
#synth OmegaCompletePartialOrder (WithBot ℕ)
-/

variable {α : Type}

namespace WithBot

@[simp]
instance le_flat : LE (WithBot α) where
  le a₁ a₂ := a₁ = ⊥ ∨ a₁ = a₂

@[simp]
instance lt_flat : LT (WithBot α) where
  lt a₁ a₂ := a₁ = ⊥ ∧ a₂ ≠ ⊥

instance instOrderBot : OrderBot (WithBot α) where
  bot_le := by aesop

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
noncomputable instance instSupSet_flat : SupSet (WithBot α) where
  sSup s := if h : ∃ v : α, ↑v ∈ s then h.choose else ⊥ 

noncomputable instance instCompletePartialOrder : CompletePartialOrder (WithBot α) where
  lubOfDirected s dir := by
    constructor <;> intros a mem <;> simp [sSup] <;> induction a
    · apply bot_le
    all_goals split <;> rename_i h
    · rw [directed_coe_unique dir mem h.choose_spec]
    · simp_all only [not_exists]
    · exact mem h.choose_spec
    · rfl
    · exact mem h.choose_spec
    · apply bot_le

theorem coe_nle_bot (a : α) : ¬ a ≤ (⊥ : WithBot α) := by
  simp_all only [le_flat, coe_ne_bot, or_self, not_false_eq_true]

theorem coe_nle_coe (a₁ a₂ : α) (h : a₁ ≠ a₂) : ¬ a₁ ≤ (a₂ : WithBot α) := by
  simp_all only [ne_eq, le_flat, coe_ne_bot, coe_inj, or_self, not_false_eq_true]

theorem coe_le_coe_iff_eq (a₁ a₂ : α) : a₁ = a₂ ↔ a₁ ≤ (a₂ : WithBot α) := by
  simp_all only [le_flat, coe_ne_bot, coe_inj, false_or]

theorem coe_le_iff_eq (a₁ : α) (a₂ : WithBot α) : a₁ = a₂ ↔ a₁ ≤ a₂ := by
  simp_all only [le_flat, coe_ne_bot, false_or]

theorem neq_bot_ex_coe {a : WithBot α} : a ≠ ⊥ → ∃ val, a = some val := by
  intros neq
  induction a <;> aesop

theorem coe_nle (a : α) (a' : WithBot α) : ¬ a ≤ a' ∨ a = a' := by
  cases a'
  case bot =>
    left
    exact WithBot.coe_nle_bot a
  case coe a' =>
    by_cases h : (a = a')
    · subst h
      simp_all only [le_flat, le_refl, not_true_eq_false, or_true]
    · left
      exact WithBot.coe_nle_coe a a' h

end WithBot
