import LeanScratch.LocallyNameless.Untyped.Basic
import LeanScratch.LocallyNameless.Untyped.Reduction
import LeanScratch.LocallyNameless.Untyped.Properties
import LeanScratch.Confluence.Basic

open Term

variable {X C : Type} [DecidableEq X] [Atom X]

inductive Parallel : Term X C → Term X C → Prop
| const (t : C) : Parallel (const t) (const t)
| fvar (x : X) : Parallel (fvar x) (fvar x)
| app {L L' M M'} : Parallel L L' → Parallel M M' → Parallel (app L M) (app L' M')
| lam (xs) {m m'} : (∀ x ∉ (xs : Finset X), Parallel (m ^ fvar x) (m' ^ fvar x)) → Parallel (lam m) (lam m')
| beta (xs) {m m' n n'} : 
    (∀ x ∉ (xs : Finset X), Parallel (m ^ fvar x) (m' ^ fvar x) ) →
    Parallel n n' → 
    Parallel (app (lam m) n) (m' ^ n')

notation:39 t " ⇉ "  t' =>                       Parallel t t'
notation:39 t " ⇉* " t' => Relation.ReflTransGen Parallel t t'

-- TODO: clean this up...
lemma para_lc_l {M M' : Term X C} (step : M ⇉ M') : LC M  := by
  induction step
  case lam xs _ _ _ _ => 
    constructor
    case L => exact xs
    assumption
  case beta xs _ _ _ _ _ _ _ _ =>
    constructor
    apply LC.lam
    case a.L => exact xs
    all_goals assumption
  all_goals constructor <;> assumption

lemma para_lc_r {M M' : Term X C} (step : M ⇉ M') : LC M' := by
  induction step
  case lam xs _ _ _ _ => 
    apply LC.lam xs
    assumption
  case beta xs _ _ _ _ _ _ _ _ => 
    apply beta_lc
    apply LC.lam xs
    all_goals assumption
  all_goals constructor <;> assumption

def Parallel.lc_refl (M : Term X C) : LC M → M ⇉ M := by
  intros lc
  induction lc
  case lam xs _ _ _ =>
    apply Parallel.lam xs
    assumption
  all_goals constructor <;> assumption

lemma step_to_para {M N : Term X C} (step : M ⇢β N) : (M ⇉ N) := by
  induction step
  case ξₗ =>
    constructor
    apply Parallel.lc_refl
    all_goals assumption
  case ξᵣ =>
    constructor
    assumption
    apply Parallel.lc_refl
    assumption
  case ξ xs _ _ _ _ =>
    apply Parallel.lam xs
    assumption
  case β _ lam_lc _ =>
    cases lam_lc with | lam xs _ =>
      apply Parallel.beta xs <;> intros <;> apply Parallel.lc_refl <;> aesop

lemma para_to_redex {M N : Term X C} (para : M ⇉ N) : (M ↠β N) := by
  induction para
  case const => constructor
  case fvar  => constructor
  case app _ _ _ _ l_para m_para redex_l redex_m =>
    trans
    exact redex_app_l_cong redex_l (para_lc_l m_para)
    exact redex_app_r_cong redex_m (para_lc_r l_para)
  case lam xs t t' _ ih =>
    apply redex_lam_cong xs
    intros x mem
    exact ih x mem
  case beta xs m m' n n' para_ih para_n redex_ih redex_n =>
    have m'_lam_lc : LC m'.lam := by
      apply LC.lam xs
      intros _ mem
      exact para_lc_r (para_ih _ mem)
    calc
      m.lam.app n ↠β m'.lam.app n  := redex_app_l_cong (redex_lam_cong xs (λ _ mem ↦ redex_ih _ mem)) (para_lc_l para_n)
      _           ↠β m'.lam.app n' := redex_app_r_cong redex_n m'_lam_lc
      _           ↠β m' ^ n'       := Relation.ReflTransGen.single (Step.β m'_lam_lc (para_lc_r para_n))

theorem parachain_iff_redex {M N : Term X C} : (M ⇉* N) ↔ (M ↠β N) := by
  refine Iff.intro ?chain_to_redex ?redex_to_chain <;> intros h <;> induction' h <;> try rfl
  case redex_to_chain.tail redex chain => exact Relation.ReflTransGen.tail chain (step_to_para redex)
  case chain_to_redex.tail para  redex => exact Relation.ReflTransGen.trans redex (para_to_redex para)

lemma para_subst {M M' N N': Term X C} (x) : (M ⇉ M') → (N ⇉ N') → (M[x := N] ⇉ M'[x := N']) := by
  intros pm pn
  induction pm <;> simp
  case const => constructor
  case fvar x' =>
    by_cases h : x = x' <;> simp [h]
    assumption
    constructor
  case beta xs _ _ _ _ _ _ ih _ => 
    rw [subst_open _ _ _ _ _ (para_lc_r pn)]
    apply Parallel.beta (xs ∪ {x})
    intros y ymem
    simp at ymem
    push_neg at ymem
    rw [subst_open_var _ _ _ _ _ (para_lc_r pn), subst_open_var _ _ _ _ _ (para_lc_l pn)]
    apply ih
    all_goals aesop
  case app => constructor <;> assumption
  case lam xs u u' mem ih => 
    apply Parallel.lam (xs ∪ {x})
    intros y ymem
    simp at ymem
    rw [subst_open_var _ _ _ _ ?_ (para_lc_l pn), subst_open_var _ _ _ _ ?_ (para_lc_r pn)]
    push_neg at ymem
    apply ih
    all_goals aesop
  
lemma para_open_close {M M' : Term X C} (x y z) : 
  (M ⇉ M') → 
  y ∉ (M.fv ∪ M'.fv ∪ {x}) → 
  M⟦z ↜ x⟧⟦z ↝ fvar y⟧ ⇉ M'⟦z ↜ x⟧⟦z ↝ fvar y⟧ 
  := by
  intros para vars
  simp at vars
  rw [open_close_to_subst, open_close_to_subst] 
  apply para_subst
  exact para
  constructor
  exact para_lc_r para
  exact para_lc_l para

lemma para_open_out {t t' u u' : Term X C} (L : Finset X) :
    (∀ x, x ∉ L → (t ^ fvar x) ⇉ (u ^ fvar x))
    → (t' ⇉ u') → (t ^ t') ⇉ (u ^ u') := by
    intros mem para
    let ⟨x, qx⟩ := atom_fresh_for_set (L ∪ u.fv ∪ t.fv)
    simp at qx
    obtain ⟨q1, q2, q3⟩ := qx
    rw [subst_intro x t' _ q3 (para_lc_l para), subst_intro x u' _ q2 (para_lc_r para)]
    exact para_subst x (mem x q1) para

-- thanks to https://github.com/ElifUskuplu/Stlc_deBruijn/blob/main/Stlc/confluence.lean
theorem para_diamond : Diamond (@Parallel X C) := by
  simp [Diamond]
  intros t t1 t2 tpt1
  revert t2
  induction tpt1 <;> intros t2 tpt2
  case const m =>
    exists t2
    and_intros
    · assumption
    · apply Parallel.lc_refl
      exact para_lc_r tpt2
  case fvar x =>
    exists t2
    and_intros
    · assumption
    · apply Parallel.lc_refl
      exact para_lc_r tpt2
  case lam xs s1 s2' mem ih => 
    cases tpt2
    case lam xs' t2' mem' =>
      have ⟨x, qx⟩ := atom_fresh_for_set (xs ∪ xs' ∪ t2'.fv ∪ s2'.fv)
      simp at qx
      have ⟨q1, q2, q3, q4⟩ := qx
      have ⟨t', qt'_l, qt'_r⟩ := ih x q1 (mem' _ q2)
      exists lam (t' ^* x)
      constructor
      · apply Parallel.lam ((s2' ^ fvar x).fv ∪ t'.fv ∪ {x})
        intros y qy
        simp
        rw [←open_close x s2' 0 q4]
        exact para_open_close x y 0 qt'_l qy
      · apply Parallel.lam ((t2' ^ fvar x).fv ∪ t'.fv ∪ {x})
        intros y qy
        simp
        rw [←open_close x t2' 0 q3]
        exact para_open_close x y 0 qt'_r qy 
  case beta xs s1 s1' s2 s2' mem ps ih1 ih2 => 
    cases tpt2
    case app u2 u2' s1pu2 s2pu2' => 
      cases s1pu2
      case lam xs' s1'' mem' =>
        have ⟨x, qx⟩ := atom_fresh_for_set (xs ∪ xs' ∪ s1''.fv ∪ s1'.fv)
        simp at qx
        obtain ⟨q1, q2, q3, q4⟩ := qx
        have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
        have ⟨t'', qt''_l, qt''_r⟩ := @ih1 x q1 _ (mem' _ q2)
        exists (t'' ^* x) ^ t'
        constructor
        · rw [subst_intro x s2' _ q4 (para_lc_l qt'_l), subst_intro x t' _ (close_var_not_fvar x t'') (para_lc_r qt'_l)]
          simp
          rw [close_open _ _ _ (para_lc_r qt''_l)]
          exact para_subst x qt''_l qt'_l
        · apply Parallel.beta ((s1'' ^ fvar x).fv ∪ t''.fv ∪ {x})
          intros y qy
          rw [←open_close x s1'' 0]
          apply para_open_close
          all_goals aesop
    case beta xs' u1' u2' mem' s2pu2' => 
      have ⟨x, qx⟩ := atom_fresh_for_set (xs ∪ xs' ∪ u1'.fv ∪ s1'.fv ∪ s2'.fv ∪ u2'.fv)
      simp at qx
      have ⟨q1, q2, q3, q4, q5, q6⟩ := qx
      have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
      have ⟨t'', qt''_l, qt''_r⟩ := @ih1 x q1 _ (mem' _ q2)
      rw [subst_intro x u2' u1' _ (para_lc_l qt'_r), subst_intro x s2' s1' _ (para_lc_l qt'_l)]
      exists t'' [x := t']
      exact ⟨para_subst x qt''_l qt'_l, para_subst x qt''_r qt'_r⟩
      all_goals aesop
  case app s1 s1' s2 s2' s1ps1' _ ih1 ih2  =>
    cases tpt2
    case app u1 u2' s1 s2 =>
      have ⟨l, _, _⟩ := ih1 s1
      have ⟨r, _, _⟩ := ih2 s2
      exists app l r
      and_intros <;> constructor <;> assumption
    case beta xs t1' u1' u2' mem s2pu2' => 
      cases s1ps1'
      case lam xs' s1'' mem' =>
        have ⟨x, qx⟩ := atom_fresh_for_set (xs ∪ xs' ∪ s1''.fv ∪ u1'.fv)
        simp at qx
        obtain ⟨q1, q2, q3, q4⟩ := qx
        have ⟨t', qt'_l, qt'_r⟩ := ih2 s2pu2'
        have ⟨t'', qt''_l, qt''_r⟩ := @ih1 (lam u1') (Parallel.lam xs mem)
        cases qt''_l
        next xs'' w1 mem'' =>
        cases qt''_r
        case lam xs''' mem''' =>
          exists w1 ^ t'
          constructor
          · apply Parallel.beta xs''
            exact fun x a ↦ mem'' x a
            exact qt'_l
          · exact para_open_out xs''' mem''' qt'_r

theorem para_confluence : Confluence (@Parallel X C) := Relation.ReflTransGen.diamond para_diamond

theorem confluence_beta : Confluence (@Step X C) := diamond_bisim parachain_iff_redex (@para_confluence X C _ _)
