import Mathlib
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.TypeTags
import Mathlib.Order.SetNotation
import Mathlib.Order.WithBot

import Mathlib.Order.OmegaCompletePartialOrder
open OmegaCompletePartialOrder

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

theorem chain_terminal_val {chain : Chain (WithBot α)} {i : ℕ} {a : α} : 
    chain i = ↑a → (∀ i', i ≤ i' → chain i' = ↑a) := by
  intros eq i' leq
  have mono := chain.monotone leq
  cases (coe_nle a (chain i')) <;> aesop

theorem chain_coe_eq {c : Chain (WithBot α)} {i i'} {a a' : α} (eq : c i = ↑a) (eq' : c i' = ↑a') : a = a' := by
  have mono := c.monotone
  by_cases le : i ≤ i'
  case pos =>
    have le := mono le
    simp_all only
    exact (coe_le_coe_iff_eq a a').mpr le
  case neg =>
    have le := mono (Nat.le_of_not_ge le)
    simp_all
    symm
    exact (coe_le_coe_iff_eq a' a).mpr le

-- such a pain working with these
theorem chain_coe_neq {c : Chain (WithBot α)} {i} (neq : ¬∃ a : α, c i = ↑a) : c i = ⊥ := by
  by_cases h : c i = ⊥
  case pos => exact h
  case neg =>
    exfalso
    apply neq
    exact neq_bot_ex_coe h

theorem chain_coe_nmem_eq {c : Chain (WithBot α)} (nmem : ¬∃ a : α, ↑a ∈ c) (i : ℕ) : c i = ⊥ := by
  have h : ¬∃ (a : α) (i : ℕ), c i = ↑a := by
    simp_all
    intros a i eq
    apply nmem a
    rw [←eq]
    simp [Chain.instMembership]
  apply chain_coe_neq
  aesop

open scoped Classical in
noncomputable instance instOmegaCompletePartialOrder : OmegaCompletePartialOrder (WithBot α) where
  ωSup c := if h : ∃ a : α, ↑a ∈ c then h.choose else ⊥
  le_ωSup c i := by
    split
    case isFalse ex =>
      rw [chain_coe_nmem_eq ex i]
    case isTrue ex =>
      have ⟨i', eq⟩ : ∃ i', ex.choose = c i' := ex.choose_spec
      by_cases ex' : ∃ a' : α, c i = a'
      case neg =>
        rw [chain_coe_neq ex']
        apply bot_le
      case pos =>
        have e := chain_coe_eq ex'.choose_spec (Eq.symm eq)
        aesop
  ωSup_le c a h := by
    split
    case' isTrue ex => have : ∃ i', ex.choose = c i' := ex.choose_spec
    all_goals induction a <;> aesop

/-
-- TODO: is this inherently classical?? 
-- TODO: decide if this or the above instance is easier to work with
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
-/

end WithBot
