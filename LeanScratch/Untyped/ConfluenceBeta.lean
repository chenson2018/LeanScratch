import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Parallel
import LeanScratch.Untyped.Reduction
import LeanScratch.Untyped.Beta

lemma step_to_para {M N} (step : M →β N) : (M ⇉ N) := by
  induction step 
  case' reduce => rename_i r; cases r
  all_goals apply_rules [Parallel.app, Parallel.abs, Parallel.beta, Parallel.refl, step_to_para] 

lemma para_to_redex {M N} (para : M ⇉ N) : (M ↠β N) := by
  match M, para with
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

theorem parachain_iff_redex {M N} : (M ⇉* N) ↔ (M ↠β N) := by
  refine Iff.intro ?chain_to_redex ?redex_to_chain <;> intros h <;> induction' h <;> try rfl
  case redex_to_chain.tail redex chain => exact Relation.ReflTransGen.tail chain (step_to_para redex)
  case chain_to_redex.tail para  redex => exact Relation.ReflTransGen.trans redex (para_to_redex para)

theorem confluence_beta : Confluence (· →β ·) := diamond_bisim parachain_iff_redex @para_confluence
