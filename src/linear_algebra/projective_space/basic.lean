/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import linear_algebra.finite_dimensional

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Constructing terms of `projectivization K V`.
We have three ways to construct terms of `projectivization K V`:
- `projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `projectivization.mk'' H h` where `H : submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : projectivization K V`, `v.submodule` gives the corresponding submodule of `V`.
- `projectivization.equiv_submodule` is the equivalence between `projectivization K V`
  and `{ H : submodule K V // finrank H = 1 }`.
- For `v : projectivization K V`, `v.rep : V` is a representative of `v`.

-/

variables (K V : Type*) [field K] [add_comm_group V] [module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
def projectivization_setoid : setoid { v : V // v ≠ 0 } :=
{ r := λ u v, ∃ a : K, a • (u : V) = v,
  iseqv := begin
    refine ⟨λ u, ⟨1, by simp⟩, _, λ u v w ⟨a,ha⟩ ⟨b,hb⟩, ⟨b * a, by simp [ha, hb, mul_smul]⟩⟩,
    rintros u v ⟨a,ha⟩,
    use a⁻¹,
    rw [← ha, ← mul_smul, inv_mul_cancel, one_smul],
    intros c, apply v.2,
    simpa [c] using ha.symm,
  end }


/-- The projectivization of the `K`-vector space `V`. -/
def projectivization := quotient (projectivization_setoid K V)

namespace projectivization

variables {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
def mk (v : V) (hv : v ≠ 0) : projectivization K V := quotient.mk' ⟨v,hv⟩

/-- A variant of `projectivization.mk` in terms of a subtype. `mk` is preferred. -/
def mk' (v : { v : V // v ≠ 0 }) : projectivization K V := quotient.mk' v

@[simp] lemma mk'_eq_mk (v : { v : V // v ≠ 0}) :
  mk' K v = mk K v v.2 :=
by { dsimp [mk, mk'], congr' 1, simp }

noncomputable instance [nontrivial V] : inhabited (projectivization K V) :=
let e := exists_ne (0 : V) in ⟨mk K e.some e.some_spec⟩

variable {K}

/-- Choose a representative of `v : projectivization K V` in `V`. -/
protected noncomputable def rep (v : projectivization K V) : V := v.out'.1

lemma rep_nonzero (v : projectivization K V) : v.rep ≠ 0 := v.out'.2

@[simp]
lemma mk_rep (v : projectivization K V) :
  mk K v.rep v.rep_nonzero = v :=
by { dsimp [mk, projectivization.rep], simp }

open finite_dimensional

/-- Consider an element of the projectivization as a submodule of `V`. -/
protected def submodule (v : projectivization K V) : submodule K V := K ∙ v.rep

variable (K)

lemma exists_of_mk_eq_mk  (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) (h : mk K v hv = mk K w hw) :
  ∃ (a : K) (ha : a ≠ 0), a • v = w :=
begin
  obtain ⟨a,h⟩ := quotient.exact' h,
  refine ⟨a,_,h⟩,
  intros c, refine hw _,
  simpa [c] using h.symm,
end

lemma exists_smul_eq_mk_rep
  (v : V) (hv : v ≠ 0) : ∃ (a : K) (ha : a ≠ 0), a • v = (mk K v hv).rep :=
exists_of_mk_eq_mk _ _ _ hv (rep_nonzero _) (by simp)

variable {K}

@[simp]
lemma submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v :=
begin
  dsimp only [projectivization.submodule],
  obtain ⟨a, ha, h⟩ := exists_smul_eq_mk_rep K v hv,
  rw ← h,
  apply submodule.span_singleton_smul_eq _ ha,
end

lemma finrank_submodule (v : projectivization K V) : finrank K v.submodule = 1 :=
finrank_span_singleton v.rep_nonzero

instance (v : projectivization K V) : finite_dimensional K v.submodule :=
by { dsimp [projectivization.submodule], apply_instance }

lemma submodule_injective : function.injective
  (projectivization.submodule : projectivization K V → submodule K V) :=
begin
  intros u v h, replace h := le_of_eq h,
  erw submodule.le_span_singleton_iff at h,
  rw [← mk_rep v, ← mk_rep u],
  symmetry,
  exact quotient.sound' (h u.rep (submodule.mem_span_singleton_self _))
end

variables (K V)
/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
noncomputable
def equiv_submodule : projectivization K V ≃ { H : submodule K V // finrank K H = 1 } :=
equiv.of_bijective (λ v, ⟨v.submodule, v.finrank_submodule⟩)
begin
  split,
  { intros u v h, apply_fun (λ e, e.val) at h,
    apply submodule_injective h },
  { rintros ⟨H, h⟩,
    rw finrank_eq_one_iff' at h,
    obtain ⟨v, hv, h⟩ := h,
    have : (v : V) ≠ 0 := λ c, hv (subtype.coe_injective c),
    use mk K v this,
    symmetry,
    ext x, revert x, erw ← set.ext_iff, ext x,
    dsimp,
    rw [submodule_mk, submodule.span_singleton_eq_range],
    refine ⟨λ hh, _, _⟩,
    { obtain ⟨c,hc⟩ := h ⟨x,hh⟩,
      exact ⟨c, congr_arg coe hc⟩ },
    { rintros ⟨c,rfl⟩,
      refine submodule.smul_mem _ _ v.2 } }
end
variables {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
noncomputable
def mk'' (H : _root_.submodule K V) (h : finrank K H = 1) : projectivization K V :=
(equiv_submodule K V).symm ⟨H,h⟩

@[simp]
lemma submodule_mk'' (H : _root_.submodule K V) (h : finrank K H = 1) :
  (mk'' H h).submodule = H :=
begin
  suffices : (equiv_submodule K V) (mk'' H h) = ⟨H,h⟩, by exact congr_arg coe this,
  dsimp [mk''],
  simp
end

@[simp]
lemma mk''_submodule (v : projectivization K V) : mk'' v.submodule v.finrank_submodule = v :=
show (equiv_submodule K V).symm (equiv_submodule K V _) = _, by simp

section map

variables {L W : Type*} [field L] [add_comm_group W] [module L W]

/-- A semilinear map of vector spaces induces a map on projective spaces. -/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : function.injective f) :
  projectivization K V → projectivization L W :=
quotient.map' (λ v, ⟨f v, λ c, v.2 (hf (by simp [c]))⟩)
begin
  rintros ⟨u,hu⟩ ⟨v,hv⟩ ⟨a,ha⟩,
  use σ a,
  dsimp at ⊢ ha,
  rw [← f.map_smulₛₗ, ha],
end

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
lemma map_injective {σ : K ≃+* L} (f : V →ₛₗ[σ.to_ring_hom] W) (hf : function.injective f) :
  function.injective (map f hf) :=
begin
  intros u v h,
  rw [← u.mk_rep, ← v.mk_rep] at *,
  apply quotient.sound',
  dsimp [map, mk] at h,
  simp only [quotient.eq'] at h,
  obtain ⟨a,ha⟩ := h,
  use σ.symm a,
  dsimp at ⊢ ha,
  erw [← σ.apply_symm_apply a, ← f.map_smulₛₗ] at ha,
  exact hf ha,
end

@[simp]
lemma map_id : map
  (linear_map.id : V →ₗ[K] V)
  (linear_equiv.refl K V).injective = id :=
begin
  ext v,
  rw ← v.mk_rep,
  dsimp [mk, map],
  simp only [quotient.eq'],
  use 1,
  rw one_smul,
  refl,
end

@[simp]
lemma map_comp {F U : Type*} [field F] [add_comm_group U] [module F U]
  {σ : K →+* L} {τ : L →+* F} {γ : K →+* F} [ring_hom_comp_triple σ τ γ]
  (f : V →ₛₗ[σ] W) (hf : function.injective f)
  (g : W →ₛₗ[τ] U) (hg : function.injective g) :
  map (g.comp f) (hg.comp hf) = map g hg ∘ map f hf :=
begin
  ext v,
  rw ← v.mk_rep,
  dsimp [mk, map],
  simp only [quotient.eq'],
  use 1,
  simp,
end

end map

end projectivization
