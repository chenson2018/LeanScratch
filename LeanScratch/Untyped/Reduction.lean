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

-- some congruence lemmas about reduction
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

-- TODO: is this true as stated, without conditions on R???
-- might want to generalize over shifting parameters
theorem shift_reduction (N N' : Term) (R : Term → Term → Prop) (h :N ↠R N') : shiftₙ 0 1 N ↠R shiftₙ 0 1 N' := sorry

theorem sub_reduction (i : ℕ) (M N N' : Term) (R : Term → Term → Prop) (h :N ↠R N') 
  : (M [i := N]) ↠R (M [i := N']) := by
  revert i
  revert N
  revert N'
  induction M <;> intros N' N h i
  case var x' => by_cases eq : x' = 0 <;> simp [sub, eq] <;> aesop
  case abs body ih =>
    apply abs_cong
    simp [sub]
    refine ih (shiftₙ 0 1 N') (shiftₙ 0 1 N) ?_ (i + 1)
    exact shift_reduction N N' R h
  case app l r ih_l ih_r =>
    calc
      app (l[i:=N]) (r[i:=N]) ↠R app (l [i := N']) (r [i :=N ]) := app_l_cong (ih_l _ _ h _)
      _                       ↠R app (l [i := N']) (r [i :=N']) := app_r_cong (ih_r _ _ h _)

@[simp]
abbrev Diamond {α} (R : α → α → Prop) := ∀ {A B C : α}, R A B → R A C → (∃ D, R B D ∧ R C D)

@[simp]
abbrev Confluence {α} (R : α → α → Prop) := Diamond (Relation.ReflTransGen R)

-- thanks to https://gist.github.com/siraben/ee3f16bf501ab7ecb49d63ecd3a2d2b1
lemma Relation.ReflTransGen.diamond_extend {α} {A B C} {R : α → α → Prop} (h : Diamond R) : 
  Relation.ReflTransGen R A B → 
  R A C → 
  ∃ D, Relation.ReflTransGen R B D ∧ Relation.ReflTransGen R C D := by
  intros AB _
  revert C
  induction' AB using Relation.ReflTransGen.head_induction_on <;> intros C AC
  case refl => exact ⟨C, ⟨single AC, by rfl⟩⟩
  case head A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := h AC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', head CD D_D'⟩⟩

-- the diamond on a relation implies diamond on reflexive transitive closure
theorem Relation.ReflTransGen.diamond {α} {R : α → α → Prop} (h : Diamond R) : Confluence R := by
  intros A B C AB BC
  revert C
  induction AB using Relation.ReflTransGen.head_induction_on <;> intros C BC
  case refl => exists C
  case head _ _ A'_C' _ ih =>
    obtain ⟨D, ⟨CD, C'_D⟩⟩ := diamond_extend h BC A'_C'
    obtain ⟨D', ⟨B_D', D_D'⟩⟩ := ih C'_D
    exact ⟨D', ⟨B_D', trans CD D_D'⟩⟩

theorem equality_descendant 
  {α : Type}
  {R : α → α → Prop}
  (confluence : Confluence R) 
  {M N : α}
  (eq : Relation.EqvGen R M N)
  : ∃ Z, ((Relation.ReflTransGen R M Z) ∧ (Relation.ReflTransGen R N Z))
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

theorem diamond_bisim {α} {R R'} (sim : ∀ {M N : α}, R M N ↔ R' M N) (h : Diamond R) : Diamond R' := by
  intros L M₁ M₂ L_M₁ L_M₂
  have ⟨N, ⟨M₁_chain_N, M₂_chain_N⟩⟩ := h (sim.mpr L_M₁) (sim.mpr L_M₂)
  exact ⟨N, ⟨sim.mp M₁_chain_N, sim.mp M₂_chain_N⟩⟩
