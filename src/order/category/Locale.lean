/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Frame
import topology.category.Top.basic
import topology.opens

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

universes u

open category_theory opposite order topological_space

/-- The category of locales. -/
@[derive large_category] def Locale := Frameᵒᵖ

namespace Locale

instance : has_coe_to_sort Locale Type* := ⟨λ X, X.unop⟩
instance (X : Locale) : frame X := X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type*) [frame α] : Locale := op $ Frame.of α

@[simp] lemma coe_of (α : Type*) [frame α] : ↥(of α) = α := rfl

instance : inhabited Locale := ⟨of punit⟩

end Locale

section
variables {α β : Type*} {l : α → β} {u : β → α}

/-- The galois coinsertion between sets and opens. -/
def gi' [topological_space α] : galois_coinsertion subtype.val (@opens.interior α _) :=
{ choice := λ s hs, ⟨s, interior_eq_iff_open.mp $ le_antisymm interior_subset hs⟩,
  gc := opens.gc,
  u_l_le := λ _, interior_subset,
  choice_eq := λ s hs, le_antisymm hs interior_subset  }

instance {α : Type*} [topological_space α] : frame (opens α) :=
{ Sup := Sup,
  inf_Sup_le_supr_inf := λ a s, (opens.ext $ by simp only [opens.coe_inf, set.inf_eq_inter,
    opens.supr_s, opens.coe_Sup, set.inter_Union₂]).le,
  ..opens.complete_lattice }


/-- Strengthening of `topological_space.opens.comap`. -/
def comap' {α β : Type*} [topological_space α] [topological_space β] (f : C(α, β)) :
  frame_hom (opens β) (opens α) :=
{ to_fun := λ s, ⟨f ⁻¹' s, s.2.preimage f.continuous⟩,
  map_Sup' := λ s, opens.ext $ by simp only [opens.Sup_s, set.sUnion_image, set.preimage_Union,
    subtype.coe_mk, set.mem_image, set.Union_exists, set.bUnion_and', set.Union_Union_eq_right],
  map_inf' := λ a b, opens.ext $
    by simp only [opens.coe_inf, set.inf_eq_inter, set.preimage_inter, opens.mk_inf_mk] }

@[simp] lemma comap'_id {α : Type*} [topological_space α] :
  comap' (continuous_map.id α) = frame_hom.id _ :=
frame_hom.ext $ λ a, opens.ext rfl

end

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
def Top_to_Locale : Top ⥤ Locale :=
{ obj := λ X, Locale.of (opens X),
  map := λ X Y f, quiver.hom.op (comap' f),
  map_id' := λ X, quiver.hom.unop_inj comap'_id,
  map_comp' := λ X Y Z f g, rfl }
