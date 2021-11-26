/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import category_theory.sites.compatible_plus

/-!

In this file, we prove that sheafification is compatible with functors which
preserve the correct limits and colimits.

-/

namespace category_theory.grothendieck_topology

open category_theory
open category_theory.limits
open opposite

universes w₁ w₂ v u
variables {C : Type u} [category.{v} C] (J : grothendieck_topology C)
variables {D : Type w₁} [category.{max v u} D]
variables {E : Type w₂} [category.{max v u} E]
variables (F : D ⥤ E)

noncomputable theory

variables [∀ (α β) (fst snd : β → α), has_limits_of_shape (walking_multicospan fst snd) D]
variables [∀ (α β) (fst snd : β → α), has_limits_of_shape (walking_multicospan fst snd) E]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ E]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
variables [∀ (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D), preserves_limit (W.index P).multicospan F]

variables (P : Cᵒᵖ ⥤ D)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`. -/
def sheafify_comp_iso : J.sheafify P ⋙ F ≅ J.sheafify (P ⋙ F) :=
J.plus_comp_iso _ _ ≪≫ (J.plus_functor _).map_iso (J.plus_comp_iso _ _)

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `F`. -/
def sheafification_whisker_left_iso (P : Cᵒᵖ ⥤ D)
  [∀ (F : D ⥤ E) (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ F]
  [∀ (F : D ⥤ E) (X : C) (W : J.cover X) (P : Cᵒᵖ ⥤ D),
    preserves_limit (W.index P).multicospan F] :
  (whiskering_left _ _ E).obj (J.sheafify P) ≅
  (whiskering_left _ _ _).obj P ⋙ J.sheafification E :=
begin
  refine J.plus_functor_whisker_left_iso _ ≪≫ _ ≪≫ functor.associator _ _ _,
  refine iso_whisker_right _ _,
  refine J.plus_functor_whisker_left_iso _,
end

/-- The isomorphism between the sheafification of `P` composed with `F` and
the sheafification of `P ⋙ F`, functorially in `P`. -/
def sheafification_whisker_right_iso :
  J.sheafification D ⋙ (whiskering_right _ _ _).obj F ≅
  (whiskering_right _ _ _).obj F ⋙ J.sheafification E :=
begin
  refine functor.associator _ _ _ ≪≫ _,
  refine iso_whisker_left (J.plus_functor D) (J.plus_functor_whisker_right_iso _) ≪≫ _,
  refine _ ≪≫ functor.associator _ _ _,
  refine (functor.associator _ _ _).symm ≪≫ _,
  exact iso_whisker_right (J.plus_functor_whisker_right_iso _) (J.plus_functor E),
end

end category_theory.grothendieck_topology
