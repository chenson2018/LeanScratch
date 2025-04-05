import LeanScratch.Untyped.Basic

open Term

-- Barendregt chapter 3
inductive Step_R (R : Term → Term → Prop) : Term → Term → Prop
| reduce {M N}   : R M N → Step_R R M N
| ξₗ     {M N Z} : Step_R R M N → Step_R R (app Z M) (app Z N)
| ξᵣ     {M N Z} : Step_R R M N → Step_R R (app M Z) (app N Z)
| ξ      {M N}   : Step_R R M N → Step_R R (abs M)   (abs N) 

notation:39 t " →" R:arg t' => Step_R                        R    t t'
notation:39 t " ↠" R:arg t' => Relation.ReflTransGen (Step_R R)   t t'

-- leaving this one for notation purposes...
@[simp]
def Equality_R  (R : Term → Term → Prop) := Relation.EqvGen (Step_R R)
notation:39 t " =" R:arg t' => Equality_R  R t t'

-- some congruence lemmas about beta reduction
theorem app_l_cong {M M' N} {R : Term → Term → Prop} : (M ↠R M') → (app M N ↠R app M' N) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξᵣ r)

theorem app_r_cong {N N' M} {R : Term → Term → Prop} : (N ↠R N') → (app M N ↠R app M N') := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξₗ r)

theorem abs_cong {N N'} {R : Term → Term → Prop} : ( N ↠R N') → (N.abs ↠R N'.abs) := by
  intros redex
  induction' redex
  case refl => rfl
  case tail r ih => exact Relation.ReflTransGen.tail ih (Step_R.ξ r)

-- we can say some things generally without setting a notion of reduction
-- TODO: should the index here be zero??
theorem sub_reduction (M N N' : Term) (R : Term → Term → Prop) (h :N ↠R N') 
  : (M [0 := N]) ↠R (M [0 := N']) := by
  induction M
  case var x' =>
    simp [sub]
    by_cases eq : x' = 0 <;> simp [eq]
    · exact h
    · rfl
  case abs body ih =>
    sorry    
  case app l r ih_l ih_r =>
    sorry

@[simp]
abbrev Diamond {α} (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

@[simp]
abbrev Confluence {α} (R : α → α → Prop) := Diamond (Relation.ReflTransGen R)

-- a couple of general lemmas
theorem diamond_ReflTrans {α} (R : α → α → Prop) (diamond : Diamond R) : Confluence R := sorry

theorem equality_descendant 
  {R : Term → Term → Prop}
  (confluence : Confluence (· →R ·)) 
  {M N : Term}
  (eq : M =R N)
  : ∃ Z : Term, ((M ↠R Z) ∧ (N ↠R Z))
  := by
  induction eq
  case refl x => exists x
  case symm x y x_eq_y ih =>
    have ⟨Z, ⟨l, r⟩⟩ := ih
    exact ⟨Z, ⟨r, l⟩⟩
  case trans M L N M_L L_N ih_ML ih_LN =>
    have ⟨Z₁, ⟨l₁, r₁⟩⟩ := ih_ML
    have ⟨Z₂, ⟨l₂, r₂⟩⟩ := ih_LN
    have ⟨Z, ⟨l, r⟩⟩ := confluence r₁ l₂
    exists Z
    and_intros
    · exact Relation.ReflTransGen.trans l₁ l
    · exact Relation.ReflTransGen.trans r₂ r
  case rel x y x_y =>
    exists y
    and_intros
    · apply Relation.ReflTransGen.single
      exact x_y
    · rfl

theorem confluence_sim {R R'} (sim : ∀ {M N}, (M ↠R N) ↔ R' M N) (diamond : Diamond R') : Confluence (· →R ·) := by
  intros L M₁ M₂ L_M₁ L_M₂
  have ⟨N, ⟨M₁_chain_N, M₂_chain_N⟩⟩ := diamond (sim.mp L_M₁) (sim.mp L_M₂)
  exact ⟨N, ⟨sim.mpr M₁_chain_N, sim.mpr M₂_chain_N⟩⟩
