import LeanScratch.PCF.Basic

variable {X: Type} [DecidableEq X] [Atom X]

open Atom

namespace Term

omit [DecidableEq X] [Atom X] in
lemma open_lc_aux (e : Term X) : ∀ (j v i u),
  i ≠ j ->
  e ⟦j ↝ v⟧ = (e ⟦j ↝ v⟧) ⟦i ↝ u⟧ ->
  e = e ⟦i ↝ u⟧ := by
  induction' e <;> intros j v i u neq h <;> simp <;> simp at h
  case bvar => aesop
  case app ih_l ih_r => 
    obtain ⟨hl, hr⟩ := h
    exact ⟨ih_l j v i u neq hl, ih_r j v i u neq hr⟩
  case lam ih => 
    refine ih (j+1) v (i+1) u (by aesop) h
  case succ ih => exact ih j v i u neq h
  case pred ih => exact ih j v i u neq h
  case fix ih => exact ih j v i u neq h
  case ifzero ih_a ih_b ih_c =>
    obtain ⟨ha, hb, hc⟩ := h
    exact ⟨ih_a j v i u neq ha, ih_b j v i u neq hb, ih_c j v i u neq hc⟩
 
omit [DecidableEq X] in
lemma open_lc (k t) (e : Term X) : LC e → e = e⟦k ↝ t⟧ := by
  intros e_lc
  revert k
  induction e_lc <;> intros k <;> simp
  case lam xs e _ ih =>
    simp at *
    have ⟨y, ymem⟩ := fresh_ext xs
    apply open_lc_aux e 0 (fvar y) (k+1) t <;> aesop
  all_goals aesop

omit [Atom X] in
theorem subst_fresh (x : X) (t : Term X) : ∀ u, x ∉ t.fv → (t [x := u]) = t := by
  induction t <;> intros <;> simp at * <;> aesop

lemma subst_open (x) (t : Term X) (k u e) :
  LC t → 
  (e ⟦ k ↝ u ⟧) [ x := t ] = (e [ x := t ]) ⟦k ↝  u [ x := t ]⟧ := by
  revert k
  induction' e <;> intros k t_lv <;> simp
  case bvar k' => aesop
  case fvar x' => 
    split <;> simp_all
    exact open_lc k (u[x':=t]) t t_lv
  case lam ih => exact ih (k + 1) t_lv
  case app ih_l ih_r => exact ⟨ih_l k t_lv, ih_r k t_lv⟩
  case ifzero ih_a ih_b ih_c => exact ⟨ih_a k t_lv, ih_b k t_lv, ih_c k t_lv⟩
  all_goals aesop

theorem subst_open_var (x y) (u e : Term X) : y ≠ x → LC u → (e [y := u]) ^ fvar x = (e ^ fvar x) [y := u] := by
  intros neq u_lc
  simp [neq, subst_open y u 0 (fvar x) e u_lc]

/-- substitution of locally closed terms is locally closed -/
theorem subst_lc {x : X} {e u : Term X} : LC e → LC u → LC (e [x := u]) := by
  intros lc_e lc_u
  induction lc_e <;> simp
  case fvar => split <;> [assumption; constructor] 
  case app ih_l ih_r => exact LC.app ih_l ih_r
  case lam xs e _ ih =>
    refine LC.lam ({x} ∪ xs) _ ?_
    intros y mem
    rw [subst_open_var y x u e ?_ lc_u]
    apply ih
    all_goals aesop
  case zero => exact LC.zero
  case pred ih => exact LC.pred ih
  case succ ih => exact LC.succ ih
  case fix  ih => exact LC.fix ih
  case ifzero ih_a ih_b ih_c => exact LC.ifzero ih_a ih_b ih_c

lemma subst_intro (x) (t e : Term X) : x ∉ e.fv → LC t → e ^ t = (e ^ fvar x) [ x := t ] := by
  intros mem t_lc
  simp
  rw [subst_open x t 0 (fvar x) e t_lc]
  simp
  rw [subst_fresh]
  exact mem

theorem beta_lc {M N : Term X} : LC (lam M) → LC N → LC (M ^ N) := by
  intros m_lc
  cases m_lc
  case lam xs mem =>
    intros n_lc
    have ⟨y, ymem⟩ := fresh_ext (xs ∪ M.fv)
    simp at ymem
    cases ymem
    rw [subst_intro y N M]
    apply subst_lc
    apply mem
    all_goals aesop    

/- opening and closing are inverses -/
omit [Atom X] in
lemma open_close (x : X) (t : Term X) (k : ℕ) : x ∉ t.fv → t⟦k ↝ fvar x⟧⟦k ↜ x⟧ = t := by
  intros mem
  revert k
  induction t <;> intros k <;> simp
  case bvar n => split <;> simp_all
  case lam t ih => exact ih mem (k + 1)
  all_goals aesop

omit [Atom X] in
lemma open_injective (x) (M M' : Term X) : x ∉ M.fv → x ∉ M'.fv → M ^ fvar x = M' ^ fvar x → M = M' := by
  intros free_M free_M' eq
  rw [←open_close x M 0 free_M, ←open_close x M' 0 free_M']
  exact congrArg (close_rec 0 x) eq

omit [DecidableEq X] [Atom X] in
lemma swap_open_fvars (k n x y) (m : Term X) : k ≠ n → x ≠ y → m⟦n ↝ fvar y⟧⟦k ↝ fvar x⟧ = m⟦k ↝ fvar x⟧⟦n ↝ fvar y⟧ := by
  revert k n
  induction' m <;> intros k n ne_kn ne_xy <;> simp
  case bvar n' => aesop
  case lam ih => apply ih <;> aesop
  all_goals aesop

omit [Atom X] in
lemma swap_open_fvar_close (k n x y) (m : Term X) : k ≠ n → x ≠ y → m⟦n ↝ fvar y⟧⟦k ↜ x⟧ = m⟦k ↜ x⟧⟦n ↝ fvar y⟧ := by
  revert k n
  induction' m <;> intros k n ne_kn ne_xy <;> simp
  case bvar n'  => split <;> aesop
  case fvar x'  => split <;> aesop
  case lam ih => apply ih <;> aesop
  all_goals aesop

omit [Atom X] in
lemma close_preserve_not_fvar {k x y} (m : Term X) : x ∉ m.fv → x ∉ (m⟦k ↜ y⟧).fv := by
  intros mem
  revert k
  induction m <;> intros k <;> simp
  case fvar y' => split <;> aesop
  case lam ih => exact ih mem
  all_goals aesop

omit [Atom X] in
lemma open_fresh_preserve_not_fvar {k x y} (m : Term X) : x ∉ m.fv → x ≠ y → x ∉ (m⟦k ↝ fvar y⟧).fv := by
  intros mem neq
  revert k
  induction m <;> intros k <;> simp
  case bvar n'  => split <;> aesop
  case fvar => aesop
  case lam ih => exact ih mem
  all_goals aesop

omit [Atom X] in
lemma subst_preserve_not_fvar {x y} (m n : Term X) : x ∉ m.fv ∪ n.fv → x ∉ (m [y := n]).fv := by
  intros mem
  simp at mem
  induction m <;> simp
  case fvar y' => split <;> simp [mem]; aesop
  case lam ih => exact ih mem
  all_goals aesop

lemma open_close_to_subst (m : Term X) (x y : X) (k : ℕ) : LC m → m ⟦k ↜ x⟧⟦k ↝ fvar y⟧ = m [x := fvar y] := by
  intros m_lc
  revert k
  induction' m_lc <;> intros k <;> simp
  case fvar x' => split <;> simp
  case app ih_l ih_r => exact ⟨ih_l _, ih_r _⟩
  case lam xs t x_mem ih =>
    have ⟨x', x'_mem⟩ := fresh_ext ({x} ∪ {y} ∪ t.fv ∪ xs)
    have s := subst_open_var x' x (fvar y) t ?_ (by constructor)
    simp at *
    rw [←open_close x' (t⟦k+1 ↜ x⟧⟦k+1 ↝ fvar y⟧) 0 ?f₁, ←open_close x' (t[x := fvar y]) 0 ?f₂]
    rw [swap_open_fvars, ←swap_open_fvar_close, s, ih]
    case f₁ =>
      apply open_fresh_preserve_not_fvar
      apply close_preserve_not_fvar
      all_goals simp [x'_mem]
    case f₂ =>
      apply subst_preserve_not_fvar
      simp [x'_mem]
    all_goals aesop
  all_goals aesop
  
omit [Atom X] in
lemma close_var_not_fvar_rec (x) (k) (t : Term X) : x ∉ (t⟦k ↜ x⟧).fv := by
  revert k
  induction t <;> intros k <;> simp
  case fvar x' => split <;> simp_all
  case lam ih => exact ih (k + 1)
  all_goals aesop

omit [Atom X] in
lemma close_var_not_fvar (x) (t : Term X) : x ∉ (t ^* x).fv := by
  simp
  exact close_var_not_fvar_rec x 0 t

lemma close_open (x : X) (t : Term X) (k : ℕ) : LC t → t⟦k ↜ x⟧⟦k ↝ fvar x⟧ = t := by
  intros lc_t
  revert k
  induction lc_t <;> intros k <;> simp
  case fvar x' => split <;> simp_all
  case lam xs t t_open_lc ih => 
    have ⟨y, hy⟩ := fresh_ext (xs ∪ t.fv ∪ (t⟦k + 1 ↜ x⟧⟦k + 1 ↝ fvar x⟧).fv ∪ {x})
    simp at hy
    obtain ⟨q1, q2, q3, q4⟩ := hy
    refine open_injective y _ _ q3 q2 ?_
    rw [←ih y q1 (k+1)]
    simp
    rw [swap_open_fvar_close, swap_open_fvars]
    all_goals aesop
  all_goals aesop
