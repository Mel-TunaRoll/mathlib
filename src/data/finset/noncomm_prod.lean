/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import algebra.big_operators.basic
import group_theory.submonoid.basic
import group_theory.subgroup.basic

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/

variables {α β : Type*} (f : α → β → β) (op : α → α → α)

namespace multiset

/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncomm_foldr (s : multiset α) (comm : ∀ (x ∈ s) (y ∈ s) b, f x (f y b) = f y (f x b)) (b : β) :
  β :=
s.attach.foldr (f ∘ subtype.val) (λ ⟨x, hx⟩ ⟨y, hy⟩, comm x hx y hy) b

@[simp] lemma noncomm_foldr_coe (l : list α)
  (comm : ∀ (x ∈ (l : multiset α)) (y ∈ (l : multiset α)) b, f x (f y b) = f y (f x b)) (b : β) :
  noncomm_foldr f (l : multiset α) comm b = l.foldr f b :=
begin
  simp only [noncomm_foldr, coe_foldr, coe_attach, list.attach],
  rw ←list.foldr_map,
  simp [list.map_pmap, list.pmap_eq_map]
end

@[simp] lemma noncomm_foldr_empty
  (h : ∀ (x ∈ (0 : multiset α)) (y ∈ (0 : multiset α)) b, f x (f y b) = f y (f x b)) (b : β) :
  noncomm_foldr f (0 : multiset α) h b = b := rfl

lemma noncomm_foldr_cons (s : multiset α) (a : α)
  (h : ∀ (x ∈ (a ::ₘ s)) (y ∈ (a ::ₘ s)) b, f x (f y b) = f y (f x b))
  (h' : ∀ (x ∈ s) (y ∈ s) b, f x (f y b) = f y (f x b))
  (b : β) :
  noncomm_foldr f (a ::ₘ s) h b = f a (noncomm_foldr f s h' b) :=
begin
  induction s using quotient.induction_on,
  simp
end

lemma noncomm_foldr_eq_foldr (s : multiset α) (h : left_commutative f) (b : β) :
  noncomm_foldr f s (λ x _ y _, h x y) b = foldr f h b s :=
begin
  induction s using quotient.induction_on,
  simp
end

variables [assoc : is_associative α op]
include assoc

/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncomm_fold (s : multiset α)
  (comm : ∀ (x ∈ s) (y ∈ s), op x y = op y x)
  (a : α) : α :=
noncomm_foldr op s (λ x hx y hy b, by rw [←assoc.assoc, comm _ hx _ hy, assoc.assoc]) a

@[simp] lemma noncomm_fold_coe (l : list α)
  (comm : ∀ (x ∈ (l : multiset α)) (y ∈ (l : multiset α)), op x y = op y x)
  (a : α) :
  noncomm_fold op (l : multiset α) comm a = l.foldr op a :=
by simp [noncomm_fold]

@[simp] lemma noncomm_fold_empty
  (h : ∀ (x ∈ (0 : multiset α)) (y ∈ (0 : multiset α)), op x y = op y x) (a : α) :
  noncomm_fold op (0 : multiset α) h a = a := rfl

lemma noncomm_fold_cons (s : multiset α) (a : α)
  (h : ∀ (x ∈ a ::ₘ s) (y ∈ a ::ₘ s), op x y = op y x)
  (h' : ∀ (x ∈ s) (y ∈ s), op x y = op y x)
  (x : α) :
  noncomm_fold op (a ::ₘ s) h x = op a (noncomm_fold op s h' x) :=
begin
  induction s using quotient.induction_on,
  simp
end

lemma noncomm_fold_eq_fold (s : multiset α) [is_commutative α op]
  (a : α) :
  noncomm_fold op s (λ x _ y _, is_commutative.comm x y) a = fold op a s :=
begin
  induction s using quotient.induction_on,
  simp
end

omit assoc
variables [monoid α]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes
on all elements `x ∈ s`." ]
def noncomm_prod (s : multiset α) (comm : ∀ (x ∈ s) (y ∈ s), commute x y) : α :=
s.noncomm_fold (*) comm 1

@[simp, to_additive] lemma noncomm_prod_coe (l : list α)
  (comm : ∀ (x ∈ (l : multiset α)) (y ∈ (l : multiset α)), commute x y) :
  noncomm_prod (l : multiset α) comm = l.prod :=
begin
  rw [noncomm_prod],
  simp only [noncomm_fold_coe],
  induction l with hd tl hl,
  { simp },
  { rw [list.prod_cons, list.foldr, hl],
    intros x hx y hy,
    exact comm x (list.mem_cons_of_mem _ hx) y (list.mem_cons_of_mem _ hy) }
end

@[simp, to_additive] lemma noncomm_prod_empty
  (h : ∀ (x ∈ (0 : multiset α)) (y ∈ (0 : multiset α)), commute x y) :
  noncomm_prod (0 : multiset α) h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_cons (s : multiset α) (a : α)
  (comm : ∀ (x ∈ a ::ₘ s) (y ∈ a ::ₘ s), commute x y) :
  noncomm_prod (a ::ₘ s) comm = a * noncomm_prod s
    (λ x hx y hy, comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) :=
begin
  induction s using quotient.induction_on,
  simp
end

@[to_additive] lemma noncomm_prod_cons' (s : multiset α) (a : α)
  (comm : ∀ (x ∈ a ::ₘ s) (y ∈ a ::ₘ s), commute x y) :
  noncomm_prod (a ::ₘ s) comm = noncomm_prod s
    (λ x hx y hy, comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) * a :=
begin
  induction s using quotient.induction_on with s,
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, list.prod_cons],
  induction s with hd tl IH,
  { simp },
  { rw [list.prod_cons, mul_assoc, ←IH, ←mul_assoc, ←mul_assoc],
    { congr' 1,
      apply comm;
      simp },
    { intros x hx y hy,
      simp only [quot_mk_to_coe, list.mem_cons_iff, mem_coe, cons_coe] at hx hy,
      apply comm,
      { cases hx;
        simp [hx] },
      { cases hy;
        simp [hy] } } }
end

@[to_additive] lemma noncomm_prod_eq_prod {α : Type*} [comm_monoid α] (s : multiset α) :
  noncomm_prod s (λ _ _ _ _, commute.all _ _) = prod s :=
begin
  induction s using quotient.induction_on,
  simp
end

end multiset

namespace finset

variables [monoid β]

/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,
given a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncomm_prod (s : finset α) (f : α → β) (comm : ∀ (x ∈ s) (y ∈ s), commute (f x) (f y)) : β :=
(s.1.map f).noncomm_prod (by simpa [multiset.mem_map, ←finset.mem_def] using comm)

@[to_additive]
lemma noncomm_prod_congr
  {s₁ s₂ : finset α} (h : s₁ = s₂) (f : α → β)
  (comm : ∀ (x ∈ s₁) (y ∈ s₁), commute (f x) (f y)) :
  noncomm_prod s₁ f comm = noncomm_prod s₂ f (by simpa [h] using comm) := by subst h

@[simp, to_additive] lemma noncomm_prod_to_finset [decidable_eq α] (l : list α) (f : α → β)
  (comm : ∀ (x ∈ l.to_finset) (y ∈ l.to_finset), commute (f x) (f y))
  (hl : l.nodup) :
  noncomm_prod l.to_finset f comm = (l.map f).prod :=
begin
  rw ←list.dedup_eq_self at hl,
  simp [noncomm_prod, hl]
end

@[simp, to_additive] lemma noncomm_prod_empty (f : α → β)
  (h : ∀ (x ∈ (∅ : finset α)) (y ∈ (∅ : finset α)), commute (f x) (f y)) :
  noncomm_prod (∅ : finset α) f h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_insert_of_not_mem [decidable_eq α] (s : finset α) (a : α)
  (f : α → β)
  (comm : ∀ (x ∈ insert a s) (y ∈ insert a s), commute (f x) (f y))
  (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm = f a * noncomm_prod s f
    (λ x hx y hy, comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) :=
by simp [insert_val_of_not_mem ha, noncomm_prod]

@[to_additive] lemma noncomm_prod_insert_of_not_mem' [decidable_eq α] (s : finset α) (a : α)
  (f : α → β)
  (comm : ∀ (x ∈ insert a s) (y ∈ insert a s), commute (f x) (f y))
  (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm = noncomm_prod s f
    (λ x hx y hy, comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) * f a :=
by simp [noncomm_prod, insert_val_of_not_mem ha, multiset.noncomm_prod_cons']

@[simp, to_additive] lemma noncomm_prod_singleton (a : α) (f : α → β) :
  noncomm_prod ({a} : finset α) f
    (λ x hx y hy, by rw [mem_singleton.mp hx, mem_singleton.mp hy]) = f a :=
by simp [noncomm_prod, multiset.singleton_eq_cons]


@[to_additive]
lemma noncomm_prod_commute (s : finset α) (f : α → β)
  (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  (y : β) (h : ∀ (x : α), x ∈ s → commute y (f x)) : commute y (s.noncomm_prod f comm) :=
begin
  classical,
  induction s using finset.induction_on with x s hnmem ih,
  { simp },
  { specialize ih (λ x hx y hy, comm x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx, h x (mem_insert_of_mem hx)),
    rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem,
    exact commute.mul_right (h x (finset.mem_insert_self _ _)) ih, }
end

@[to_additive]
lemma noncomm_prod_mem_submonoid (s : finset α) (f : α → β)
  (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  (m : submonoid β) (h : ∀ (x : α), x ∈ s → f x ∈ m) : s.noncomm_prod f comm ∈ m :=
begin
  classical,
  induction s using finset.induction_on with x s hnmem ih,
  { exact submonoid.one_mem m, },
  { specialize ih (λ x hx y hy, comm x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx, h x (mem_insert_of_mem hx)),
    rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem,
    apply submonoid.mul_mem _ (h x (finset.mem_insert_self _ _)) ih, }
end

@[to_additive]
lemma noncomm_prod_mem_subgroup {β : Type*} [group β] (s : finset α) (f : α → β)
  (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  (m : subgroup β) (h : ∀ (x : α), x ∈ s → f x ∈ m) : s.noncomm_prod f comm ∈ m :=
begin
  classical,
  induction s using finset.induction_on with x s hnmem ih,
  { exact subgroup.one_mem m, },
  { specialize ih (λ x hx y hy, comm x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx, h x (mem_insert_of_mem hx)),
    rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem,
    apply subgroup.mul_mem _ (h x (finset.mem_insert_self _ _)) ih, }
end

@[to_additive] lemma noncomm_prod_eq_prod {β : Type*} [comm_monoid β] (s : finset α) (f : α → β) :
  noncomm_prod s f (λ _ _ _ _, commute.all _ _) = s.prod f :=
begin
  classical,
  induction s using finset.induction_on with a s ha IH,
  { simp },
  { simp [ha, IH] }
end

/- The non-commutative version of `finset.prod_union` -/
@[to_additive "The non-commutative version of `finset.sum_union`"]
lemma noncomm_prod_union_of_disjoint [decidable_eq α] {s t : finset α}
  (h : disjoint s t) (f : α → β)
  (comm : ∀ (x ∈ s ∪ t) (y ∈ s ∪ t), commute (f x) (f y))
  (scomm : ∀ (x ∈ s) (y ∈ s), commute (f x) (f y) :=
    λ _ hx _ hy, comm _ (mem_union_left _ hx) _ (mem_union_left _ hy))
  (tcomm : ∀ (x ∈ t) (y ∈ t), commute (f x) (f y) :=
    λ _ hx _ hy, comm _ (mem_union_right _ hx) _ (mem_union_right _ hy)) :
  noncomm_prod (s ∪ t) f comm = noncomm_prod s f scomm * noncomm_prod t f tcomm :=
begin
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s,
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t,
  rw list.disjoint_to_finset_iff_disjoint at h,
  simp [sl', tl', noncomm_prod_to_finset, ←list.prod_append, ←list.to_finset_append,
        list.nodup_append_of_nodup sl' tl' h]
end

/- The non-commutative version of `finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `finset.sum_add_distrib`"]
lemma noncomm_prod_mul_distrib [decidable_eq α] {s : finset α}
  (f : α → β) (g : α → β)
  (comm_fgfg : ∀ (x ∈ s) (y ∈ s), commute (f x * g x) (f y * g y))
  (comm_ff : ∀ (x ∈ s) (y ∈ s), commute (f x) (f y))
  (comm_gg : ∀ (x ∈ s) (y ∈ s), commute (g x) (g y))
  (comm_gf : ∀ (x ∈ s) (y ∈ s), x ≠ y → commute (g x) (f y)) :
  noncomm_prod s (f * g) comm_fgfg
    = noncomm_prod s f comm_ff * noncomm_prod s g comm_gg :=
begin
  induction s using finset.induction_on with x s hnmem ih,
  { simp, },
  { simp only [finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem, pi.mul_apply],
    specialize ih
      (λ x hx y hy, comm_fgfg x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx y hy, comm_ff x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx y hy, comm_gg x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx y hy hne, comm_gf x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hne),
    rw ih,
    simp only [mul_assoc],
    congr' 1,
    simp only [← mul_assoc],
    congr' 1,
    apply noncomm_prod_commute,
    intros y hy,
    have : x ≠ y, by {rintro rfl, contradiction},
    exact comm_gf x (mem_insert_self x s) y (mem_insert_of_mem hy) this, }
end

/-- `finset.noncomm_prod` is injective in `f` if `f` maps into independent subgroups.  -/
@[to_additive "`finset.noncomm_sum` is injective in `f` if `f` maps into independent subgroups"]
lemma eq_one_of_noncomm_prod_eq_one_of_independent {β : Type*} [group β]
  (s : finset α) (f : α → β) (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  (γ : α → subgroup β) (hind : complete_lattice.independent γ) (hmem : ∀ (x ∈ s), f x ∈ γ x)
  (heq1 : s.noncomm_prod f comm = 1) : ∀ (i ∈ s), f i = 1 :=
begin
  classical,
  revert heq1,
  induction s using finset.induction_on with i s hnmem ih,
  { simp, },
  { specialize ih (λ x hx y hy, comm x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
      (λ x hx, hmem x (mem_insert_of_mem hx)),
    have hmem_bsupr: s.noncomm_prod f
      (λ x hx y hy, comm x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)) ∈
      ⨆ (i : α) (_x : i ∈ (s : set α)), γ i,
    { refine noncomm_prod_mem_subgroup s f _ _ _,
      intros x hx,
      have : γ x ≤ ⨆ (i ∈ (s : set α)), γ i := le_bsupr x hx,
      exact this (hmem x (mem_insert_of_mem hx)), },
    intro heq1,
    rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem at heq1,
    have hnmem' : i ∉ (s : set α), by simpa,
    have heq1' : f i = 1 ∧ s.noncomm_prod f _ = 1 := subgroup.disjoint_iff_mul_eq_one.mp
      (hind.disjoint_bsupr hnmem') (hmem i (mem_insert_self _ _)) hmem_bsupr heq1,
    rcases heq1' with ⟨ heq1i, heq1S ⟩,
    specialize ih heq1S,
    intros i h,
    simp only [finset.mem_insert] at h,
    rcases h with ⟨rfl | _⟩,
    { exact heq1i },
    { exact (ih _ h), } }
end

end finset
