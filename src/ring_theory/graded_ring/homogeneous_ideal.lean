/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/

import ring_theory.ideal.basic
import ring_theory.ideal.operations
import linear_algebra.finsupp
import ring_theory.graded_ring.basic

/-!

# Homogeneous ideal of a graded commutative ring

This file defines homogeneous ideals of `graded_ring R A` and operations on them:
- `mul`, `inf`, `Inf` of homogeneous ideals are homogeneous;
- `⊤`, `⊥`, i.e. the trivial ring and `R` are homogeneous;
- `radical` of a homogeneous ideal is homogeneous.
-/

noncomputable theory

section defs

open_locale direct_sum classical big_operators
open set direct_sum

variables (R : Type*) [ring R] {ι : Type*}
  (A : ι → add_subgroup R)

/--A homogeneous ideal is an `I : ideal R` such that `I` is generated by
homogeneous elements in `I`.-/
def is_homogeneous_ideal' (I : ideal R) : Prop :=
  I = ideal.span {x | x ∈ I ∧ is_homogeneous R A x}

/-- Given any ideal `I : R`, there is a homogeneous ideal generated by
the homogeneous elements of `I`-/
def homogeneous_ideal_of_ideal (I : ideal R) :
  ideal R := ideal.span (set_of (is_homogeneous R A) ∩ I)

lemma homogeneous_ideal_of_ideal_le_ideal
  (I : ideal R) :
  homogeneous_ideal_of_ideal R A I ≤ I :=
begin
  rw homogeneous_ideal_of_ideal,
  conv_rhs { rw ←ideal.span_eq I },
  apply ideal.span_mono, exact (set_of (is_homogeneous R A)).inter_subset_right ↑I,
end

variables [add_comm_monoid ι] [decidable_eq ι] [graded_ring R A]

/--Equivalently, homogeneous ideal is an `I : ideal R` such that `I` is generated by a set of homogeneous
elements.-/
def is_homogeneous_ideal (I : ideal R) : Prop :=
  ∃ S : set (homogeneous_element R A), I = ideal.span ↑S

lemma is_homogeneous_ideal_iff_is_homogeneous_ideal' (I : ideal R) :
  is_homogeneous_ideal R A I ↔ is_homogeneous_ideal' R A I :=
⟨λ hI, begin
  obtain ⟨S, hS⟩ := hI,
  rw [is_homogeneous_ideal'], ext r, split; intro hr,
  { rw hS at hr,
    suffices : ↑S ⊆ {x | x ∈ I ∧ is_homogeneous R A x},
    exact (ideal.span_mono this) hr,
    intros s hs, split, rw hS,
    refine ideal.subset_span hs,
    obtain ⟨⟨s', homs'⟩, hs₁, hs₂⟩ := hs,
    convert homs', rw ←hs₂, refl },
  { obtain ⟨l, hl⟩ := (finsupp.mem_span_iff_total R _ _).mp hr,
    rw ←hl, apply ideal.sum_mem, rintros ⟨x, hx₁, hx₂⟩ hx₃,
    simp only [linear_map.id_coe, id.def, finsupp.mem_support_iff, linear_map.coe_smul_right,
      ne.def, smul_eq_mul, subtype.coe_mk] at hx₁ hx₂ hx₃ ⊢,
    exact ideal.mul_mem_left _ _ hx₁, }
end, λ hI, begin
  rw is_homogeneous_ideal' at hI,
  rw is_homogeneous_ideal,
  use {x : homogeneous_element R A | ↑x ∈ I},
  rw hI, congr, ext r, split; intros hr,
  { rcases hr with ⟨r_mem, ⟨i, r_eq⟩⟩,
    use r, exact ⟨i, r_eq⟩, refine ⟨_, rfl⟩,
    simp only [mem_set_of_eq, subtype.coe_mk], convert ←r_mem, },
  { rcases hr with ⟨⟨r', hr'⟩, hr₁, hr₂⟩,
    simp only [mem_set_of_eq, subtype.coe_mk] at hr₁,
    rw ←hr₂, rw ←hI at hr₁, refine ⟨hr₁, hr'⟩, }
end⟩

/--Equivalently, an `I : ideal R` is homogeneous iff for every element `r : I` and `i : ι`, the
degree `i` component of `r` is in `I`.-/
def is_homogeneous_ideal'' (I : ideal R) : Prop :=
  ∀ r : R, r ∈ I → ∀ i : ι, graded_ring.proj R A i r ∈ I

private lemma is_homogeneous_ideal.mul_homogeneous_element
  {I : ideal R} (HI : is_homogeneous_ideal R A I) (r x : R)
  (hx₁ : is_homogeneous R A x) (hx₂ : x ∈ I) (j : ι) :
  graded_ring.proj R A j (r * x) ∈ I :=
begin
  rw [graded_ring.as_sum R A r, finset.sum_mul, add_monoid_hom.map_sum],
  apply ideal.sum_mem,
  intros k hk,
  obtain ⟨i, hi⟩ := hx₁,
  have mem₁ : (graded_ring.proj R A k) r * x ∈ A (k + i) := graded_ring.mul_respect_grading
   (graded_ring.proj_mem R A k _) hi,
  by_cases k + i = j,
  { rw ←h,
    rw graded_ring.proj_homogeneous_element,
    apply I.mul_mem_left _ hx₂, exact mem₁, },
  { rw [graded_ring.proj_homogeneous_element_of_ne],
    exact I.zero_mem, exact mem₁, intro rid, apply h rid, }
end

lemma is_homogeneous_ideal.mem_iff (I : ideal R) (hI : is_homogeneous_ideal R A I) (r : R) :
  r ∈ I ↔ ∀ i : ι, graded_ring.proj R A i r ∈ I :=
⟨λ hr i, begin
  have hI' := hI,
  rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal', ideal.span,
    finsupp.span_eq_range_total] at hI', rw hI' at hr,
  obtain ⟨s, rfl⟩ := hr,
  rw [finsupp.total_apply, finsupp.sum, add_monoid_hom.map_sum],
  apply ideal.sum_mem, rintros ⟨a, ha₁, ⟨j, ha₂⟩⟩ ha₃,
  rw [smul_eq_mul],
  apply is_homogeneous_ideal.mul_homogeneous_element, exact hI, use j, exact ha₂, exact ha₁,
end, λ hr, begin
  rw graded_ring.as_sum R A r,
  apply ideal.sum_mem, intros c _, apply hr,
end⟩

private lemma is_homogeneous_ideal.homogeneous_component
  {I : ideal R} (HI : is_homogeneous_ideal R A I) (x : R) (hx : x ∈ I) (i : ι) :
  graded_ring.proj R A i x ∈ I :=
begin
  have HI' := HI,
  rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal', ideal.span,
      finsupp.span_eq_range_total] at HI',
  rw HI' at hx,
  obtain ⟨s, rfl⟩ := hx,
  rw [finsupp.total_apply, finsupp.sum, add_monoid_hom.map_sum],
  apply ideal.sum_mem,
  rintros ⟨j, ⟨hj₁, hj₂⟩⟩ hj₃,
  simp only [algebra.id.smul_eq_mul, subtype.coe_mk, smul_eq_mul],
  apply is_homogeneous_ideal.mul_homogeneous_element, exact HI, exact hj₂, exact hj₁,
end

lemma is_homogeneous_ideal_iff_is_homogeneous_ideal''
  (I : ideal R) :
  is_homogeneous_ideal R A I ↔ is_homogeneous_ideal'' R A I :=
⟨λ HI, begin
  intros x hx i,
  apply is_homogeneous_ideal.homogeneous_component R A HI x hx,
end, λ HI, begin
  rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal'],
  ext, split; intro hx,
  { rw graded_ring.as_sum R A x,
    refine ideal.sum_mem _ _,
    intros j hj, specialize HI x hx j,
    rw ideal.mem_span, intros J HJ,
    refine HJ _,
    simp only [mem_set_of_eq],
    refine ⟨HI, _⟩, refine ⟨j, _⟩, apply graded_ring.proj_mem, },
  { rw [ideal.mem_span] at hx,
    apply hx,
    intros y hy,
    exact hy.1,  },
end⟩

/--The three definitions above are all equivalent.-/
lemma is_homogeneous_ideal.equivalent (I : ideal R) :
  tfae [is_homogeneous_ideal R A I, is_homogeneous_ideal' R A I, is_homogeneous_ideal'' R A I] :=
begin
  tfae_have : 1↔2, exact is_homogeneous_ideal_iff_is_homogeneous_ideal' R A I,
  tfae_have : 1↔3, exact is_homogeneous_ideal_iff_is_homogeneous_ideal'' R A I,
  tfae_finish,
end

lemma is_homogeneous_ideal.homogeneous_ideal_of_ideal
  (I : ideal R) :
  is_homogeneous_ideal R A (homogeneous_ideal_of_ideal R A I) :=
begin
  use ({x | ↑x ∈ I}),
  rw homogeneous_ideal_of_ideal, congr, ext, split; intro hx;
  simp only [mem_inter_eq, mem_set_of_eq, set_like.mem_coe] at hx ⊢,
  use x, exact hx.1, refine ⟨hx.2, rfl⟩,
  obtain ⟨y, hy₁, hy₂⟩ := hx, simp only [mem_set_of_eq] at hy₁, split, rw ←hy₂,
  rcases y with ⟨y, ⟨i, hy₃⟩⟩, use i, refine hy₃,
  rw ←hy₂, refine hy₁,
end

end defs

section homogeneous_ideal


section defs
variables (R : Type*) [ring R] {ι : Type*} [add_comm_monoid ι] [decidable_eq ι]
  (A : ι → add_subgroup R) [graded_ring R A]

/--We collect all homogeneous ideal into a type.-/
def homogeneous_ideal : Type* := { I : ideal R // is_homogeneous_ideal R A I }

instance homogeneous_ideal.inhabited : inhabited (homogeneous_ideal R A) :=
{ default := ⟨⊥, begin use ∅, unfold_coes, rw [set.image_empty, ideal.span_empty], end⟩ }

instance homogeneous_ideal.has_bot : has_bot (homogeneous_ideal R A) :=
{ bot := ⟨⊥, begin use ∅, unfold_coes, rw [set.image_empty, ideal.span_empty], end⟩ }

instance homogeneous_ideal.has_top : has_top (homogeneous_ideal R A) :=
{ top := ⟨⊤, begin rw is_homogeneous_ideal_iff_is_homogeneous_ideal'',
  intros r _ i, simp only [submodule.mem_top],
end⟩ }

@[simp] lemma homogeneous_ideal.eq_top_iff (I : homogeneous_ideal R A) : I = ⊤ ↔ I.1 = ⊤ :=
⟨λ h, begin
  unfold has_top.top at h,
  rw h, refl,
end, λ h, begin
  have h' : I.val = (⊤ : homogeneous_ideal R A).val,
  unfold has_top.top, rw h, refl,
  apply subtype.val_injective h',
end⟩

instance homogeneous_ideal.has_mem : has_mem R (homogeneous_ideal R A) :=
{ mem := λ r I, r ∈ I.1 }

end defs

section comm_ring
open_locale pointwise

variables (R : Type*) [comm_ring R] {ι : Type*} (A : ι → add_subgroup R)  [add_comm_monoid ι]
  [decidable_eq ι] [graded_ring R A]

instance homogeneous_ideal.has_mul :
  has_mul (homogeneous_ideal R A) :=
{ mul := λ I J, begin
    obtain ⟨I, HI⟩ := I,
    obtain ⟨J, HJ⟩ := J,
    choose s₁ hI using HI,
    choose s₂ hJ using HJ,
    refine ⟨I * J, ⟨s₁ * s₂, _⟩⟩,
    rw [hI, hJ, ideal.span_mul_span'],
    apply congr_arg,
    convert (@set.image_mul _ _ s₁ s₂ _ _ (homogeneous_element.coe_mul_hom R A)).symm,
  end }

instance homogeneous_ideal.has_sup : has_sup (homogeneous_ideal R A) :=
{ sup := λ I J, begin
   obtain ⟨I, HI⟩ := I,
    obtain ⟨J, HJ⟩ := J,
    choose s₁ hI using HI,
    choose s₂ hJ using HJ,
    refine ⟨I ⊔ J, ⟨s₁ ∪ s₂, _⟩⟩,
    unfold_coes,
    rw [set.image_union, ideal.span, hI, hJ],
    exact (submodule.span_union _ _).symm,
end }

instance homogeneous_ideal.has_add : has_add (homogeneous_ideal R A) := ⟨(⊔)⟩


private lemma homogeneous_ideal.subset_inf
  (I : homogeneous_ideal R A) (J : homogeneous_ideal R A) :
  ideal.span {x | x ∈ I.1 ⊓ J.1 ∧ is_homogeneous R A x} ≤ I.1 ⊓ J.1 :=
begin
  intros x hx,
  { split,
    { simp only [set_like.mem_coe],
      have HI := I.2,
      rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal'] at HI,
      rw [HI, ideal.mem_span], intros K HK,
      replace HK := ideal.span_mono HK,
      rw [ideal.span_eq] at HK,
      have eq₁ : ideal.span {x | x ∈ I.1 ⊓ J.1 ∧ is_homogeneous R A x}
        ≤ ideal.span {x | x ∈ I ∧ is_homogeneous R A x},
      { apply ideal.span_mono, rintros y ⟨⟨hy₁, _⟩, hy₂⟩, refine ⟨hy₁, hy₂⟩, },
      refine HK _, refine eq₁ hx, },
    { simp only [set_like.mem_coe],
      have HJ := J.2,
      rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal'] at HJ,
      rw [HJ, ideal.mem_span], intros K HK,
      replace HK := ideal.span_mono HK,
      rw [ideal.span_eq] at HK,
      have eq₁ : ideal.span {x | x ∈ I.1 ⊓ J.1 ∧ is_homogeneous R A x}
        ≤ ideal.span {x | x ∈ J ∧ is_homogeneous R A x},
      { apply ideal.span_mono, rintros y ⟨⟨_, hy₁⟩, hy₂⟩, refine ⟨hy₁, hy₂⟩, },
      refine HK _, refine eq₁ hx, },
  },
end

private lemma homogeneous_ideal.inf_subset
  [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  (I : homogeneous_ideal R A) (J : homogeneous_ideal R A) :
  I.1 ⊓ J.1 ≤ ideal.span {x | x ∈ I.1 ⊓ J.1 ∧ is_homogeneous R A x} :=
begin
  rintro x ⟨hxi, hxj⟩,
  have hx : ∀ i, graded_ring.proj R A i x ∈ I.1 ⊓ J.1,
  { intro j, split; refine (is_homogeneous_ideal.mem_iff R A _ _ x).mp _ _,
    exact I.2,
    assumption, exact J.2, assumption, },

  rw [graded_ring.as_sum R A x],
  refine ideal.sum_mem _ _,
  intros i hi, refine ideal.subset_span _, refine ⟨hx _, _⟩, refine ⟨i, _⟩,
  apply graded_ring.proj_mem,
end

instance homogeneous_ideal.has_inf
  [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)] : has_inf (homogeneous_ideal R A) :=
{ inf := λ I J, begin
  refine ⟨I.1 ⊓ J.1, _⟩,
  rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal'],
  exact le_antisymm (homogeneous_ideal.inf_subset R A I J) (homogeneous_ideal.subset_inf R A I J),
end }

instance homogeneous_ideal.has_Inf : has_Inf (homogeneous_ideal R A) :=
{ Inf := λ ℐ, begin
  use Inf (set.image (λ x : homogeneous_ideal R A, x.val) ℐ),
  rw is_homogeneous_ideal_iff_is_homogeneous_ideal'',
  intros x Hx i, simp only [submodule.mem_Inf] at Hx ⊢,
  intros J HJ, simp only [set.mem_image, subtype.val_eq_coe] at HJ,
  obtain ⟨K, HK₁, HK₂⟩ := HJ, rw ←HK₂,
  have HK₃ := K.2,
  rw is_homogeneous_ideal_iff_is_homogeneous_ideal'' at HK₃,
  apply HK₃, apply Hx, simp only [set.mem_image, subtype.val_eq_coe], use K, exact ⟨HK₁, rfl⟩,
end }

end comm_ring

section linear_ordered_cancel_add_comm_monoid
open_locale big_operators

variables(R : Type*) [comm_ring R] {ι : Type*} (A : ι → add_subgroup R)
  [linear_ordered_cancel_add_comm_monoid ι] [decidable_eq ι] [graded_ring R A]
  [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  [Π (I : homogeneous_ideal R A) (x : R), decidable_pred (λ (i : ι), graded_ring.proj R A i x ∉ I)]

lemma homogeneous_ideal.is_prime_iff
  (I : homogeneous_ideal R A)
  (I_ne_top : I ≠ ⊤)
  (homogeneous_mem_or_mem : ∀ {x y : R},
    is_homogeneous R A x → is_homogeneous R A y
    → (x * y ∈ I.1 → x ∈ I.1 ∨ y ∈ I.1)) : ideal.is_prime I.1 :=
⟨λ rid, begin
  have rid' : I.val = (⊤ : homogeneous_ideal R A).val,
  unfold has_top.top, simp only [rid], refl,
  apply I_ne_top, exact subtype.val_injective rid',
end, begin
  intros x y hxy, by_contradiction rid,
  obtain ⟨rid₁, rid₂⟩ := not_or_distrib.mp rid,
  set set₁ := (graded_ring.support R A x).filter (λ i, graded_ring.proj R A i x ∉ I) with set₁_eq,
  set set₂ := (graded_ring.support R A y).filter (λ i, graded_ring.proj R A i y ∉ I) with set₂_eq,
  have set₁_nonempty : set₁.nonempty,
  { rw [is_homogeneous_ideal.mem_iff R A I.1 I.2, not_forall] at rid₁,
    obtain ⟨i, h⟩ := rid₁,
    refine ⟨i, _⟩, rw set₁_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_ring.mem_support_iff, intro rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  have set₂_nonempty : set₂.nonempty,
  { rw [is_homogeneous_ideal.mem_iff R A I.1 I.2, not_forall] at rid₂,
    obtain ⟨i, h⟩ := rid₂,
    refine ⟨i, _⟩, rw set₂_eq, simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter],
    refine ⟨_, h⟩, rw graded_ring.mem_support_iff, intro rid₃, rw rid₃ at h,
    simp only [not_true, submodule.zero_mem, add_monoid_hom.map_zero] at h, exact h, },
  set max₁ := set₁.max' set₁_nonempty with max₁_eq,
  set max₂ := set₂.max' set₂_nonempty with max₂_eq,
  have mem_max₁ := finset.max'_mem set₁ set₁_nonempty,
  rw [←max₁_eq, set₁_eq] at mem_max₁,
  have mem_max₂ := finset.max'_mem set₂ set₂_nonempty,
  rw [←max₂_eq, set₂_eq] at mem_max₂,
  rw is_homogeneous_ideal.mem_iff R A I.1 I.2 at hxy,
  specialize hxy (max₁ + max₂),
  have eq :=
    calc  graded_ring.proj R A (max₁ + max₂) (x * y)
        = ∑ ij in ((graded_ring.support R A x).product (graded_ring.support R A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂),
            (graded_ring.proj R A ij.1 x) * (graded_ring.proj R A ij.2 y)
        : by rw graded_ring.mul_proj
    ... = ∑ ij in ((graded_ring.support R A x).product (graded_ring.support R A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)} ∪ {(max₁, max₂)},
            (graded_ring.proj R A ij.1 x) * (graded_ring.proj R A ij.2 y)
        : _ -- (1),
    ... = ∑ (ij : ι × ι) in ((graded_ring.support R A x).product (graded_ring.support R A y)).filter
            (λ (z : ι × ι), prod.fst z + z.snd = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_ring.proj R A (prod.fst ij) x) * (graded_ring.proj R A ij.snd y)
        + ∑ ij in {(max₁, max₂)}, (graded_ring.proj R A (prod.fst ij) x)
            * (graded_ring.proj R A ij.snd y)
        : _ -- (2)
    ... = ∑ ij in ((graded_ring.support R A x).product (graded_ring.support R A y)).filter
            (λ (z : ι × ι), z.1 + z.2 = max₁ + max₂)
                    \ {(max₁, max₂)},
            (graded_ring.proj R A ij.1 x) * (graded_ring.proj R A ij.2 y)
        + _
        : by rw finset.sum_singleton,

  have eq₂ :
    (graded_ring.proj R A (max₁, max₂).fst) x * (graded_ring.proj R A (max₁, max₂).snd) y
          = graded_ring.proj R A (max₁ + max₂) (x * y)
          - ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_ring.support R A x).product (graded_ring.support R A y)) \ {(max₁, max₂)},
              (graded_ring.proj R A ij.fst) x * (graded_ring.proj R A ij.snd) y,
  { rw eq, ring },

  have mem_I₂ : ∑ (ij : ι × ι) in finset.filter (λ (z : ι × ι), z.fst + z.snd = max₁ + max₂)
              ((graded_ring.support R A x).product (graded_ring.support R A y)) \ {(max₁, max₂)},
              (graded_ring.proj R A ij.fst) x * (graded_ring.proj R A ij.snd) y ∈ I,
  { apply ideal.sum_mem, rintros ⟨i, j⟩ H,
    simp only [not_and, prod.mk.inj_iff, finset.mem_sdiff, ne.def, dfinsupp.mem_support_to_fun,
       finset.mem_singleton, finset.mem_filter, finset.mem_product] at H,
    obtain ⟨⟨⟨H₁, H₂⟩, H₃⟩, H₄⟩ := H,
    cases lt_trichotomy i max₁,
    { -- in this case `i < max₁`, so `max₂ < j`, so `of A j (y j) ∈ I`
      have ineq : max₂ < j,
      { by_contra rid₂, rw not_lt at rid₂,
        have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
        conv_lhs at rid₃ { rw add_comm },
        conv_rhs at rid₃ { rw add_comm },
        rw H₃ at rid₃, exact lt_irrefl _ rid₃, },
      have not_mem_j : j ∉ set₂,
      { intro rid₂,
        rw max₂_eq at ineq,
        have rid₃ := (finset.max'_lt_iff set₂ set₂_nonempty).mp ineq j rid₂,
        exact lt_irrefl _ rid₃, },
      rw set₂_eq at not_mem_j,
      simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
        finset.mem_filter] at not_mem_j,
      specialize not_mem_j H₂,
      apply ideal.mul_mem_left,
      convert not_mem_j, },
    { cases h,
      { -- in this case `i = max₁`, so `max₂ = j`, contradictory
        have : j = max₂,
        { rw h at H₃,
          exact linear_ordered_cancel_add_comm_monoid.add_left_cancel _ _ _ H₃, },
        exfalso,
        exact H₄ h this, },
      { -- in this case `i > max₁`, so `i < max₁`, so `of A i (x i) ∈ I`
        have ineq : max₁ < i,
        { by_contra rid₂, rw not_lt at rid₂,
          have rid₃ := add_lt_add_of_le_of_lt rid₂ h,
          conv_lhs at rid₃ { rw add_comm }, exact lt_irrefl _ rid₃, },
        have not_mem_i : i ∉ set₁,
        { intro rid₂,
          rw max₁_eq at ineq,
          have rid₃ := (finset.max'_lt_iff set₁ set₁_nonempty).mp ineq i rid₂,
          exact lt_irrefl _ rid₃,},
        rw set₁_eq at not_mem_i,
        simp only [not_and, not_not, ne.def, dfinsupp.mem_support_to_fun,
          finset.mem_filter] at not_mem_i,
        specialize not_mem_i H₁,
        apply ideal.mul_mem_right,
        convert not_mem_i, }, } },
  have mem_I₃ :
    (graded_ring.proj R A (max₁, max₂).fst) x * (graded_ring.proj R A (max₁, max₂).snd) y ∈ I,
  { rw eq₂, apply ideal.sub_mem,
    have HI := I.2,
    rw [is_homogeneous_ideal_iff_is_homogeneous_ideal'', is_homogeneous_ideal''] at HI,
    specialize HI _ hxy (max₁ + max₂), exact hxy, exact mem_I₂, },
  specialize homogeneous_mem_or_mem ⟨max₁, graded_ring.proj_mem R A max₁ x⟩
    ⟨max₂, graded_ring.proj_mem R A max₂ y⟩ mem_I₃,
  cases homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
  refine mem_max₁.2 homogeneous_mem_or_mem,
  simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
  refine mem_max₂.2 homogeneous_mem_or_mem,

  -- (1)
  congr, ext, split; intros H,
  { simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product] at H,
    rw finset.mem_union,
    by_cases a = (max₁, max₂),
    right, rw h, exact finset.mem_singleton_self (max₁, max₂),
    left, rw finset.mem_sdiff, split,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    exact H, intro rid, simp only [finset.mem_singleton] at rid, exact h rid, },
  { rw finset.mem_union at H, cases H,
    rw finset.mem_sdiff at H, exact H.1,
    simp only [finset.mem_filter, ne.def, dfinsupp.mem_support_to_fun, finset.mem_product],
    simp only [finset.mem_singleton] at H, rw H,
    refine ⟨⟨_, _⟩, rfl⟩,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₁,
    exact mem_max₁.1,
    simp only [ne.def, dfinsupp.mem_support_to_fun, finset.mem_filter] at mem_max₂,
    exact mem_max₂.1, },

  -- (2)
  rw [finset.sum_union],
  apply finset.disjoint_iff_inter_eq_empty.mpr,
  rw finset.eq_empty_iff_forall_not_mem, rintros ⟨i, j⟩ Hij,
  rw [finset.mem_inter, finset.mem_sdiff, finset.mem_filter] at Hij,
  simp only [not_and, prod.mk.inj_iff, ne.def, dfinsupp.mem_support_to_fun, finset.mem_singleton,
    finset.mem_product] at Hij,
  exact Hij.1.2 Hij.2.1 Hij.2.2,
end⟩

lemma homogeneous_ideal.rad_eq (I : homogeneous_ideal R A) :
  I.1.radical = Inf {J | I.1 ≤ J ∧ is_homogeneous_ideal R A J ∧ J.is_prime} :=
begin
  have subset₁ : I.1.radical ≤ Inf {J | I.1 ≤ J ∧ is_homogeneous_ideal R A J ∧ J.is_prime},
  { rw ideal.radical_eq_Inf, intros x hx,
    rw [submodule.mem_Inf] at hx ⊢, intros J HJ, apply hx,
    obtain ⟨HJ₁, _, HJ₂⟩ := HJ,
    refine ⟨HJ₁, HJ₂⟩, },
  have subset₂ : Inf {J | I.1 ≤ J ∧ is_homogeneous_ideal R A J ∧ J.is_prime} ≤ I.1.radical,
  { intros x hx,
    rw ideal.radical_eq_Inf,
    rw [submodule.mem_Inf] at hx ⊢,
    intros J HJ,
    specialize hx (homogeneous_ideal_of_ideal R A J) _,
    obtain ⟨HJ₁, HJ₂⟩ := HJ,
    refine ⟨_, is_homogeneous_ideal.homogeneous_ideal_of_ideal R A _, _⟩,
    { have HI := I.2,
      rw [is_homogeneous_ideal_iff_is_homogeneous_ideal', is_homogeneous_ideal'] at HI,
      rw HI, apply ideal.span_mono, intros y hy,
      obtain ⟨hy₁, ⟨z, hz⟩⟩ := hy,
      specialize HJ₁ hy₁, refine ⟨⟨z, hz⟩, HJ₁⟩, },
    { set J' := homogeneous_ideal_of_ideal R A J with eq_J',
      have homogeneity₀ : is_homogeneous_ideal R A J' :=
        is_homogeneous_ideal.homogeneous_ideal_of_ideal R A J,
      apply homogeneous_ideal.is_prime_iff R A ⟨J', homogeneity₀⟩,
      intro rid,
      have rid' : J = ⊤,
      { have : J' ≤ J := homogeneous_ideal_of_ideal_le_ideal R A J,
        simp only [homogeneous_ideal.eq_top_iff] at rid,
        rw rid at this, rw top_le_iff at this, exact this, },
      apply HJ₂.1, exact rid',
      rintros x y hx hy hxy,
      have H := HJ₂.mem_or_mem (homogeneous_ideal_of_ideal_le_ideal R A J hxy),
      cases H,
      { left, rw is_homogeneous_ideal.mem_iff R A, intros j,
        suffices : (graded_ring.proj R A j) x ∈ J', exact this,
        obtain ⟨i, z⟩ := hx,
        by_cases i = j,
        { rw [←h, eq_J', homogeneous_ideal_of_ideal],
          refine ideal.subset_span _, split,
          simp only [set.mem_set_of_eq], use i, apply graded_ring.proj_mem,
          rw graded_ring.proj_homogeneous_element, exact H, exact z, },
        { rw graded_ring.proj_homogeneous_element_of_ne,
          simp only [submodule.zero_mem, add_monoid_hom.map_zero], exact z, intro rid,
          exact h rid, },
          exact is_homogeneous_ideal.homogeneous_ideal_of_ideal R A _, },
      { right, rw is_homogeneous_ideal.mem_iff R A, intros j,
        suffices : (graded_ring.proj R A j) y ∈ J', exact this,
        obtain ⟨i, z⟩ := hy,
        by_cases i = j,
        { rw [←h, eq_J', homogeneous_ideal_of_ideal],
          refine ideal.subset_span _, split,
          simp only [set.mem_set_of_eq], use i, apply graded_ring.proj_mem,
          rw graded_ring.proj_homogeneous_element, exact H, exact z, },
        { rw graded_ring.proj_homogeneous_element_of_ne,
          simp only [submodule.zero_mem, add_monoid_hom.map_zero], exact z, intro rid,
          exact h rid, },
          exact is_homogeneous_ideal.homogeneous_ideal_of_ideal R A _, }, },
      refine (homogeneous_ideal_of_ideal_le_ideal R A J) hx, },

  ext x, split; intro hx,
  exact subset₁ hx, exact subset₂ hx,
end

end linear_ordered_cancel_add_comm_monoid

section radical

variables (R : Type*) [comm_ring R] {ι : Type*} (A : ι → add_subgroup R)
  [linear_ordered_cancel_add_comm_monoid ι] [decidable_eq ι] [graded_ring R A]
  [Π (i : ι) (x : (λ (i : ι), ↥(A i)) i), decidable (x ≠ 0)]
  [Π (I : homogeneous_ideal R A) (x : R),
    decidable_pred (λ (i : ι), (graded_ring.proj R A i) x ∉ I)]


lemma homogeneous_ideal.rad (I : homogeneous_ideal R A)  :
  is_homogeneous_ideal R A I.1.radical :=
begin
  have radI_eq := homogeneous_ideal.rad_eq R A I,
  rw radI_eq,
  have : Inf {J : ideal R | I.val ≤ J ∧ is_homogeneous_ideal R A J ∧ J.is_prime} =
  (Inf {J : homogeneous_ideal R A | I.1 ≤ J.1 ∧ J.1.is_prime }).1,
  simp only [subtype.coe_le_coe, subtype.val_eq_coe], congr, ext J, split; intro H,
  { use ⟨J, H.2.1⟩, split, refine ⟨H.1, H.2.2⟩, refl, },
  { obtain ⟨K, ⟨⟨HK₁, HK₂⟩, HK₃⟩⟩ := H,
    split, convert HK₁, rw ←HK₃, refl, split,
    rw ←HK₃, exact K.2, rw ←HK₃, exact HK₂, },

  rw this,
  refine (Inf {J : homogeneous_ideal R A | I.val ≤ J.val ∧ J.val.is_prime}).2,
end
end radical

end homogeneous_ideal
