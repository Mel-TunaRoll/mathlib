/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Lattice
import order.hom.complete_lattice

/-!
# The category of frames

This file defines `Frame`, the category of frames.

## References

* [nLab, *Frm*](https://ncatlab.org/nlab/show/Frm)
-/

universes u

open category_theory order

/-- The category of frames. -/
def Frame := bundled frame

namespace Frame

instance : has_coe_to_sort Frame Type* := bundled.has_coe_to_sort
instance (X : Frame) : frame X := X.str

/-- Construct a bundled `Frame` from a `frame`. -/
def of (α : Type*) [frame α] : Frame := bundled.of α

instance : inhabited Frame := ⟨of punit⟩

/-- An abbreviation of `frame_hom` that assumes `frame` instead of the weaker `complete_lattice`.
Necessary for the category theory machinery. -/
abbreviation hom (α β : Type*) [frame α] [frame β] : Type* := frame_hom α β

instance bundled_hom : bundled_hom hom :=
⟨λ α β [frame α] [frame β], by exactI (coe_fn : frame_hom α β → α → β),
 λ α [frame α], by exactI frame_hom.id α,
 λ α β γ [frame α] [frame β] [frame γ], by exactI frame_hom.comp,
 λ α β [frame α] [frame β], by exactI fun_like.coe_injective⟩

attribute [derive [large_category, concrete_category]] Frame

instance has_forget_to_Lattice : has_forget₂ Frame Lattice :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y, frame_hom.to_lattice_hom } }

/-- Constructs an isomorphism of frames from an order isomorphism between them. -/
@[simps] def iso.mk {α β : Frame.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply _ },
  inv_hom_id' := by { ext, exact e.apply_symm_apply _ } }

end Frame
