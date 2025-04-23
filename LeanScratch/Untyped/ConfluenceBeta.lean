import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Reduction
import LeanScratch.Untyped.Shifting
import LeanScratch.Untyped.Beta

open Term

variable {T : Type}

inductive Parallel : Term T → Term T → Prop
| const (t : T) : Parallel (const t) (const t)
| var (x : ℕ) : Parallel (var x) (var x)
| abs {N N'} : Parallel N N' →  Parallel (abs N) (abs N')
| app {L L' M M'} : Parallel L L' → Parallel M M' → Parallel {{{ ~L ~M }}} {{{ ~L' ~M' }}}
| beta {N N' M M'} : Parallel N N' → Parallel M M' → Parallel {{{ (λ . ~M) ~N }}} (M' [0 := N'.shift]).unshift

notation:39 t " ⇉ "  t' =>                       Parallel t t'
notation:39 t " ⇉* " t' => Relation.ReflTransGen Parallel t t'

@[refl]
theorem Parallel.refl (M : Term T) : (M ⇉ M) := by
  induction M
  case var x => exact Parallel.var x
  case abs body ih => exact Parallel.abs ih
  case app l r l_ih r_ih => exact Parallel.app l_ih r_ih
  case const _ => constructor

theorem para_shift {c d : ℕ} {M M' : Term T} : (M ⇉ M') → (M.shiftₙ c d ⇉ M'.shiftₙ c d) := by
  intros para
  revert c d
  induction para <;> intros c d
  case var x => rfl
  case app => constructor <;> aesop
  case abs => constructor; aesop
  case beta t2 t2' t1 t1' t1p t2p ih₁ ih₂ =>
    simp [shiftₙ]
    rw [shiftUnshiftSwap ?_ (betaShifted' 0 t1' t2'), shiftSubstSwap, ←shiftShiftSwap]
    exact Parallel.beta ih₁ ih₂
    all_goals linarith
  case const m => rfl

lemma step_to_para {M N : Term T} (step : M ⇢β N) : (M ⇉ N) := by
  induction step 
  case' reduce => rename_i r; cases r
  all_goals apply_rules [Parallel.app, Parallel.abs, Parallel.beta, Parallel.refl, step_to_para] 

lemma para_to_redex {M N : Term T} (para : M ⇉ N) : (M ↠β N) := by
  match M, para with
  | Term.const _, Parallel.const _ => rfl
  | Term.var _, Parallel.var _ => rfl
  | Term.abs _, Parallel.abs _ => 
      apply abs_cong
      apply para_to_redex
      assumption
  | Term.app L R, Parallel.app p₁ p₂ => 
      rename_i L' R'
      calc
        (L.app R ) ↠β (L'.app R ) := app_l_cong (para_to_redex p₁)
        _          ↠β (L'.app R') := app_r_cong (para_to_redex p₂)
  | Term.app (Term.abs N) M, Parallel.beta p₁ p₂ =>
      rename_i _ _ M' N'
      calc
        (N.abs.app M) ↠β (N'.abs.app M)  := app_l_cong (abs_cong (para_to_redex p₂))
        _             ↠β (N'.abs.app M') := app_r_cong (para_to_redex (p₁))
        _             ↠β (N'[0:= M'.shift]).unshift := by
          apply Relation.ReflTransGen.single
          apply Step_R.reduce
          apply β.reduce

theorem parachain_iff_redex {M N : Term T} : (M ⇉* N) ↔ (M ↠β N) := by
  refine Iff.intro ?chain_to_redex ?redex_to_chain <;> intros h <;> induction' h <;> try rfl
  case redex_to_chain.tail redex chain => exact Relation.ReflTransGen.tail chain (step_to_para redex)
  case chain_to_redex.tail para  redex => exact Relation.ReflTransGen.trans redex (para_to_redex para)

open Shifted Step_R in
theorem beta_shift_conserve  : ∀ {d c} {t1 t2 : Term T}, (t1 ⇢β t2) → Shifted d c t1 → Shifted d c t2 := by
  intros d c t1 t2 step s
  match step, s with
  | ξ  p, sabs s1 => exact sabs (beta_shift_conserve p s1)
  | ξₗ p, sapp s1 s2 => exact sapp s1 (beta_shift_conserve p s2)
  | ξᵣ p, sapp s1 s2 => exact sapp (beta_shift_conserve p s1) s2
  | reduce (β.reduce), (sapp (sabs s1) s2) => 
      have bs := @betaShifted2 T d c 0
      simp_rw [Nat.add_comm] at bs
      exact bs s1 s2

theorem redex_shift_conserve : ∀ {d c} {t1 t2 : Term T}, (t1 ↠β t2) → Shifted d c t1 → Shifted d c t2 := by
  intros d c t1 t2 redex s
  induction' redex
  case refl => assumption
  case tail a a_ih => exact beta_shift_conserve a a_ih

theorem para_shift_conserve  : ∀ {d c} {t1 t2 : Term T}, (t1 ⇉  t2) → Shifted d c t1 → Shifted d c t2 := by
  intros d c t1 t2 para s
  exact redex_shift_conserve (para_to_redex para) s

theorem para_unshift {c d} {M M' : Term T} : (M ⇉ M') → Shifted d c M → (M.unshiftₙ c d ⇉ M'.unshiftₙ c d) := by
  intros para sM
  match para, sM with
  | Parallel.const _, _ => rfl
  | Parallel.var _, _ => rfl
  | Parallel.app l r, Shifted.sapp sl sr => exact Parallel.app (para_unshift l sl) (para_unshift r sr)
  | Parallel.abs body, Shifted.sabs sbody => exact Parallel.abs (para_unshift body sbody)
  | Parallel.beta r2 r1, Shifted.sapp (Shifted.sabs s1) s2 => 
      simp [shiftₙ]
      rename_i X Y Z W
      have s1' := para_shift_conserve r1 s1
      have s2' := para_shift_conserve r2 s2

      rw [unshiftUnshiftSwap (by linarith) (betaShifted' 0 W Y) ?com_shift]
      case com_shift =>
        have bshift := @betaShifted2 T d c 0
        rw [Nat.zero_add, Nat.zero_add, Nat.add_comm] at bshift
        exact bshift s1' s2'

      rw [unshiftSubstSwap2 (by linarith) s1' ?com_shift]
      case com_shift =>
        rw [Nat.add_comm]
        refine shiftShifted' (by linarith) s2'        

      rw [←unshiftShiftSwap (by linarith) s2']

      exact Parallel.beta (para_unshift r2 s2) (para_unshift r1 s1)  

theorem sub_para {x : ℕ} {N N' M M' : Term T} : (N ⇉ N') → (M ⇉ M') → (N [x := M] ⇉ N' [x := M']) := by
  intros N_N' M_M'
  match N_N' with
  | Parallel.const _ => rfl
  | Parallel.abs r1 => exact Parallel.abs (sub_para r1 (para_shift M_M'))
  | Parallel.var x =>
      simp [sub]
      rename_i x'
      by_cases eq : x = x' <;> simp [eq]
      · exact M_M'
      · rfl
  | Parallel.app l r => exact Parallel.app (sub_para l M_M') (sub_para r M_M')
  | @Parallel.beta _ X W Y Z r2 r1 => 
      simp_rw [shift, unshift, ←unshiftSubstSwap' _ _ (betaShifted' 0 Z W), Nat.add_comm x 1, substSubstSwap x 0 Z W M']
      refine Parallel.beta (sub_para r2 M_M') ?_
      simp_rw [Nat.add_comm]
      exact sub_para r1 (para_shift M_M')

def Term.plus (t : Term T) : Term T :=
  match t with
  | const m => const m
  | var x => var x
  | abs N => abs N.plus
  | app (abs N) M => (N.plus [0 := M.plus.shift]).unshift
  | app L M => app L.plus M.plus

theorem para_tri {M N : Term T} (para : M ⇉ N) : (N ⇉ M.plus) := 
  match para with
  | Parallel.const _ => by rfl
  | Parallel.var x => Parallel.var x
  | Parallel.abs ρ => Parallel.abs (para_tri ρ)
  | Parallel.beta p1 p2 => para_unshift (sub_para (para_tri p2) (para_shift (para_tri p1))) (betaShifted' _ _ _)
  | @Parallel.app T (Term.abs _) _ _ _ (Parallel.abs p1) p2 => Parallel.beta (para_tri p2) (para_tri p1)
  | @Parallel.app T (var _) _ _ _ p1 p2 => Parallel.app (para_tri p1) (para_tri p2)
  | @Parallel.app T (app _ _) _ _ _ p1 p2 => Parallel.app (para_tri p1) (para_tri p2)
  | @Parallel.app T (Term.const _) _ _ _ p1 p2 => Parallel.app (para_tri p1) (para_tri p2)

theorem para_diamond : Diamond (@Parallel T) := by
  simp [Diamond]
  intros M N N' p1 p2
  exact ⟨M.plus, ⟨para_tri p1, para_tri p2⟩⟩

theorem para_confluence : Confluence (@Parallel T) := Relation.ReflTransGen.diamond para_diamond

theorem confluence_beta : Confluence (@Step_R T β) := diamond_bisim parachain_iff_redex (@para_confluence T)
