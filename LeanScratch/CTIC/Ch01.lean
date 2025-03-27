import Mathlib
import Mathlib.CategoryTheory.Iso
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.Category.Ring.Basic

open CategoryTheory CategoryTheory.Functor Function Category

universe u v u' v' u'' v''

variable {C : Type u} {D : Type u'} {E : Type u''} 
variable [Category.{v} C] [Category.{v'} D] [Category.{v''} E]

-- example 1.1.1
-- outside the above variables for universe reasons
lemma bijective_iff_iso {X Y : Type u} (f : X → Y) : Bijective f ↔ @IsIso (Type u) _ _ _ f := by
  apply Iff.intro <;> intros h 
  case mp =>
    -- there's weirdness about the defeq of the bundling, but this is the idea...
    exists (Equiv.ofBijective f h).invFun
    apply And.intro
    case left =>
      have left_inv := (Equiv.ofBijective f h).left_inv
      exact types_ext (f ≫ (Equiv.ofBijective f h).invFun) (𝟙 X) left_inv
    case right =>
      have right_inv := (Equiv.ofBijective f h).right_inv
      exact types_ext ((Equiv.ofBijective f h).invFun ≫ f) (𝟙 Y) right_inv
  case mpr =>
    obtain ⟨finv, ⟨l, r⟩⟩ := h.out
    constructor
    case left =>
      apply HasLeftInverse.injective
      exists finv
      exact congrFun l
    case right =>
      apply HasRightInverse.surjective
      exists finv
      exact congrFun r

-- exercise 1.1.i.i
lemma iso_unique {x y : C} (α α' : Iso x y) (h : α.hom = α'.hom) : α.inv = α'.inv := by
  obtain ⟨f , g , l , r ⟩ := α
  obtain ⟨f', g', l', r'⟩ := α'
  simp_all
  calc
    g = g ≫  𝟙 x      := Eq.symm (comp_id g)
    _ = g ≫  f' ≫ g'  := congrArg (g ≫  ·) (id (Eq.symm l'))
    _ = g ≫  f ≫ g'   := by rw [h]
    _ = (g ≫  f) ≫ g' := Eq.symm (assoc g f g')
    _ = (𝟙 y) ≫ g'    := by rw [r]
    _ = g'            := id_comp g'

-- exercise 1.1.i.ii
lemma inverses_eq {x y : C} {f : x ⟶  y} {g h : y ⟶  x} (H : f ≫  g = 𝟙 x) (H' : h ≫ f = 𝟙 y) : g = h := by
  calc
    g = 𝟙 y ≫ g     := Eq.symm (id_comp g)
    _ = (h ≫ f) ≫ g := by rw [H']
    _ = h ≫ f ≫ g   := assoc h f g
    _ = h ≫ 𝟙 x     := by rw [H]
    _ = h           := comp_id h

lemma inverses_iso {x y : C} {f : x ⟶  y} {g h : y ⟶  x} (H : f ≫  g = 𝟙 x) (H' : h ≫ f = 𝟙 y) : IsIso f := by
  exists h
  rw [inverses_eq H H'] at H
  exact ⟨H, H'⟩

-- lemma 1.2.3
-- chance to try duality....
lemma iso_postcomp {x y : C} (f : x ⟶  y) : IsIso f ↔ (∀ c, @IsIso (Type v) _ _ _ (λ h : c ⟶  x ↦ h ≫ f)) := by
  apply Iff.intro <;> intros h
  case mp =>
    have ⟨g, ⟨l, r⟩⟩ := h
    intros c
    exists (· ≫ g)
    apply And.intro <;> ext <;> simp [l, r, comp_id]
  case mpr => 
    sorry

lemma iso_precomp {x y : C} (f : x ⟶  y) : IsIso f ↔ (∀ c, @IsIso (Type v) _ _ _ (λ g : y ⟶  c ↦ f ≫ g)) := sorry

-- exercise 1.2.ii
-- book states this as surjective, but I think easier (since in Set/Type) to use equivalent Epi
lemma split_epi_postcomp  {x y : C} (f : x ⟶  y) : IsSplitEpi  f ↔  (∀ c, @Epi (Type v) _ _ _ (λ g : c ⟶  x ↦ g ≫ f)) := sorry
lemma split_mono_postcomp {x y : C} (f : x ⟶  y) : IsSplitMono f ↔  (∀ c, @Epi (Type v) _ _ _ (λ g : y ⟶  c ↦ f ≫ g)) := sorry

-- exercise 1.2.v
-- pain in the ass bundling, meta here???
lemma mono_int_cast_rat : Mono (RingCat.ofHom (Int.castRingHom ℚ)) := sorry
lemma epi_int_cat_cat   : Epi  (RingCat.ofHom (Int.castRingHom ℚ)) := sorry

-- lemma 1.3.8
lemma iso_functor (F : C ⥤ D) {x y : C} (f : x ⟶  y) : IsIso f → IsIso (F.map f) := by
  intros h
  have ⟨g, ⟨l, r⟩⟩ := h
  exists F.map g
  apply And.intro <;> rw [←CategoryTheory.Functor.map_id]
  case left =>
    rw [←l,CategoryTheory.Functor.map_comp]
  case right =>
    rw [←r, CategoryTheory.Functor.map_comp]

-- definition 1.3.11
def postcomp (c : C) : C ⥤ Type v where
  obj (x : C) := c ⟶  x
  map {x y} (f : x ⟶  y) := (· ≫ f)

def precomp (c : C) : Cᵒᵖ ⥤ Type v where
  obj (x : Cᵒᵖ) := x.unop ⟶  c
  map {x y} (f : x ⟶  y) := (f.unop ≫ ·)

-- definition 1.3.13
-- same as `CategoryTheory.Functor.hom`, but with some annotations (that might cause defeq issues?)
def two_sided_rep : Cᵒᵖ × C ⥤ Type v where
  obj := λ (x, y) ↦ x.unop ⟶  y
  map {X Y : Cᵒᵖ × C} := 
    let (w, y) := X
    let (x, z) := Y
    λ ((f : w ⟶  x), (h : y ⟶  z)) (g : w.unop ⟶  y) ↦ f.unop ≫ g ≫ h

-- easier versions (in one direction) of iso_{pre,post}comp from above
lemma iso_postcomp_forward {x y : C} (f : x ⟶  y) (h : IsIso f) (c : C) 
  : @IsIso (Type v) _ _ _ (λ h : c ⟶  x ↦ h ≫ f) := iso_functor (postcomp c) f h

lemma iso_precomp_forward {x y : Cᵒᵖ} (f : x ⟶  y) (h : IsIso f.op) (c : Cᵒᵖ) 
  : @IsIso (Type v) _ _ _ (λ g : y ⟶  c ↦ f ≫ g) := iso_functor (precomp c) _ h

-- example 1.4.7
def postcomp_trans {w x: C} (f : w ⟶  x) : NatTrans (postcomp x) (postcomp w) where
  app (c : C) := precomp c |>.map f.op
  naturality:= by
    simp [postcomp, precomp]
    intros
    ext
    simp  

def precomp_trans {y z: C} (h : y ⟶  z) : NatTrans (precomp y) (precomp z) where
  app (c : Cᵒᵖ) := postcomp c.unop |>.map h
  naturality := by
    simp [postcomp, precomp]
    intros
    ext
    simp

-- lemma 1.5.10
lemma four_iso {a b a' b': C} (f : a ⟶  b) (ha : a ≅ a') (hb : b ≅ b') : ∃! (f' : a' ⟶  b'), f' = ha.inv ≫ f ≫ hb.hom := by
  aesop

lemma four_iso' {a b a' b': C} (ha : a ≅ a') (hb : b ≅ b') (f : a ⟶  b) (f' : a' ⟶  b') :
    List.TFAE [f' = ha.inv ≫ f ≫ hb.hom, ha.hom ≫ f' = f ≫ hb.hom, ha.inv ≫ f = f' ≫ hb.inv, f = ha.hom ≫ f' ≫ hb.inv] := by
  refine List.tfae_of_cycle ?cycle ?tail
  case cycle =>
    simp
    and_intros
    all_goals intros h
    · rw [h, ←assoc, ha.hom_inv_id, Category.id_comp]
    · (calc
          ha.inv ≫ f = ha.inv ≫ f ≫ 𝟙 _                := by rw [Category.comp_id]
          _          = ha.inv ≫ f ≫  (hb.hom ≫ hb.inv) := by rw [hb.hom_inv_id]
          _          = ha.inv ≫ (f ≫  hb.hom) ≫ hb.inv := by rw [assoc]
          _          = ha.inv ≫ (ha.hom ≫ f') ≫ hb.inv := by rw [h]
          _          = (ha.inv ≫ ha.hom) ≫ f' ≫ hb.inv := by simp [Category.assoc]
          _          = 𝟙 _ ≫ f' ≫ hb.inv               := by rw [ha.inv_hom_id]
          _          = f' ≫ hb.inv                     := by rw [Category.id_comp])
    · rw [←h, ←assoc, ha.hom_inv_id, Category.id_comp]
  case tail =>
    simp
    intros h
    rw [h, assoc, assoc, hb.inv_hom_id, Category.comp_id, ←assoc, ha.inv_hom_id, Category.id_comp]

-- theorem 1.5.9 
theorem cat_iso_full_faithful_esssurj (eq : C ≌ D) 
  : Full eq.functor ∧ Faithful eq.functor ∧ EssSurj eq.functor := sorry

-- exercise 1.5.iv
-- TODO: not sure how to state the object version
theorem full_faithful_iso_morphism (F : C ⥤ D) [Full F] [Faithful F] {x y : C} (f : x ⟶  y) 
  : IsIso (F.map f) ↔ IsIso f := by
  constructor
  case mp => sorry
  case mpr => exact fun a ↦ iso_functor F f a

-- exercise 1.7.vii
def bifunctor_curry : C × D ⥤ E → C ⥤ D ⥤ E := sorry
theorem bifunctor_bijective : Bijective (@bifunctor_curry C D E _ _ _) := sorry
