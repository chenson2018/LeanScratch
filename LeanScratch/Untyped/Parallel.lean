import LeanScratch.Untyped.Basic
import LeanScratch.Untyped.Shifting
import LeanScratch.Untyped.Reduction

open Term

inductive Parallel : Term → Term → Prop
| var (x : ℕ) : Parallel (var x) (var x)
| abs {N N'} : Parallel N N' →  Parallel (abs N) (abs N')
| app {L L' M M'} : Parallel L L' → Parallel M M' → Parallel {{{ ~L ~M }}} {{{ ~L' ~M' }}}
| beta {N N' M M'} : Parallel N N' → Parallel M M' → Parallel {{{ (λ . ~M) ~N }}} (M' [0 := N'.shift]).unshift

notation:39 t " ⇉ "  t' =>                       Parallel t t'
notation:39 t " ⇉* " t' => Relation.ReflTransGen Parallel t t'

@[refl]
theorem Parallel.refl (M : Term) : (M ⇉ M) := by
  induction M
  case var x => exact Parallel.var x
  case abs body ih => exact Parallel.abs ih
  case app l r l_ih r_ih => exact Parallel.app l_ih r_ih

theorem para_shift {c d : ℕ} {M M'} : (M ⇉ M') → (M.shiftₙ c d ⇉ M'.shiftₙ c d) := sorry
theorem para_unshift {c d : ℕ} {M M'} : (M ⇉ M') → (M.unshiftₙ c d ⇉ M'.unshiftₙ c d) := sorry

theorem sub_para {x : ℕ} {N N' M M'} : (N ⇉ N') → (M ⇉ M') → (N [x := M] ⇉ N' [x := M']) := by
  intros N_N' M_M'
  match N_N' with
  | Parallel.abs r1 => exact Parallel.abs (sub_para r1 (para_shift M_M'))
  | Parallel.var x =>
      simp [sub]
      rename_i x'
      by_cases eq : x = x' <;> simp [eq]
      · exact M_M'
      · rfl
  | Parallel.app l r =>
      apply Parallel.app
      apply sub_para l
      exact M_M'
      apply sub_para
      exact r
      exact M_M'
  | @Parallel.beta W X Y Z WX YZ => 
      have h₁ : (Z[0:=X.shift].unshift[x:=M']) = ((Z [ x+1 := M'.shift ]) [ 0 := (X [ x := M' ]).shift ]).unshift := 
      calc Z[0:=X.shift].unshift[x:=M']
       _ = (Z[0:=X.shift][x+1:=M'.shift]).unshift := by rw [unshiftSubstSwap]
       _ = (Z [ x+1 := M'.shift ] [ 0 := (X [ x := M' ]).shift ]).unshift := by
            have eq := sub_comm 0 x Z X M'
            rw [Nat.zero_add, Nat.add_comm 1 x] at eq
            simp [shift, unshift]
            rw [eq]
      rw [h₁]
      exact Parallel.beta (sub_para WX M_M') (sub_para YZ (para_shift M_M'))

def Term.plus (t : Term) : Term :=
  match t with
  | var x => var x
  | abs N => abs N.plus
  | app (abs N) M => (N.plus [0 := M.plus.shift]).unshift
  | app L M => app L.plus M.plus

theorem para_tri {M N} (para : M ⇉ N) : (N ⇉ M.plus) := 
  match para with
  | Parallel.var x => Parallel.var x
  | Parallel.abs ρ => Parallel.abs (para_tri ρ)
  | Parallel.beta p1 p2 => para_unshift (sub_para (para_tri p2) (para_shift (para_tri p1)))
  | @Parallel.app (Term.abs _) _ _ _ (Parallel.abs p1) p2 => Parallel.beta (para_tri p2) (para_tri p1)
  | @Parallel.app (var _) _ _ _ p1 p2 => Parallel.app (para_tri p1) (para_tri p2)
  | @Parallel.app (app _ _) _ _ _ p1 p2 => Parallel.app (para_tri p1) (para_tri p2)

theorem para_diamond : Diamond Parallel := by
  simp [Diamond]
  intros M N N' p1 p2
  exact ⟨M.plus, ⟨para_tri p1, para_tri p2⟩⟩

-- https://github.com/iwilare/church-rosser/blob/main/ConfluenceParallel.agda was helpful here
theorem strip {M N N'} (MN : M ⇉ N) (MN' : M ⇉* N') : ∃L, ((N ⇉* L) ∧ (N' ⇉ L)):= by
  revert N
  induction MN' using Relation.ReflTransGen.head_induction_on
  case refl => 
    intros N _
    exists N
  case head M M' M_M' M'_N' ih =>
    intros N MN
    have ⟨L, ⟨N_L, M'_L⟩⟩ := para_diamond MN M_M'
    have ⟨L', ⟨L_L', N'_L'⟩⟩ := ih M'_L
    refine ⟨L', ⟨Relation.ReflTransGen.head N_L L_L', N'_L'⟩⟩

theorem chain_diamond : Diamond (· ⇉* ·) := by
  simp [Diamond]
  intros L M₂ M₁ L_M₂
  revert M₁
  -- PLFA defines the transitive closure with head instead of tail, but we can
  -- specify to induct that way if we want, Mathlib even has it already!
  induction L_M₂ using Relation.ReflTransGen.head_induction_on
  case refl =>
    intros M₁ L_M₁
    exact ⟨M₁, ⟨L_M₁, by rfl⟩⟩
  case head M₁ M₁' L_M₁_s M₁_M₁' ih =>
    intros M₂ L_M₁_c
    have ⟨N,  ⟨M₁_N_c, M₂_N_p⟩⟩ := strip L_M₁_s L_M₁_c
    have ⟨N', ⟨M₁'_N', N_N'⟩⟩ := ih M₁_N_c
    refine ⟨N', ⟨M₁'_N', Relation.ReflTransGen.head M₂_N_p N_N'⟩⟩    
