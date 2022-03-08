/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import analysis.seminorm
import order.closure

/-!
# Balanced

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/


open set
open_locale pointwise

variables {𝕜 E ι : Type*}

section balanced_hull

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_scalar
variables [has_scalar 𝕜 E]

variables (𝕜)

def balanced_core (s : set E) := ⋃₀ {t : set E | balanced 𝕜 t ∧ t ⊆ s}

def balanced_core_aux (s : set E) := ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s

def balanced_hull (s : set E) := ⋃ (r : 𝕜) (hr : ∥r∥ ≤ 1), r • s

variables {𝕜}

-- Begin of lemmas to be moved

lemma balanced_mem {s : set E} (hs : balanced 𝕜 s) {x : E} (hx : x ∈ s) {a : 𝕜} (ha : ∥a∥ ≤ 1) :
  a • x ∈ s :=
mem_of_subset_of_mem (hs a ha) (smul_mem_smul_set hx)


-- End of lemmas to be moved

lemma balanced_core_subset (s : set E) : balanced_core 𝕜 s ⊆ s :=
begin
  refine sUnion_subset (λ t ht, _),
  simp only [mem_set_of_eq] at ht,
  exact ht.2,
end

lemma balanced_core_mem_iff {s : set E} {x : E} : x ∈ balanced_core 𝕜 s ↔
  ∃ t : set E, balanced 𝕜 t ∧ t ⊆ s ∧ x ∈ t :=
by simp_rw [balanced_core, mem_sUnion, mem_set_of_eq, exists_prop, and_assoc]

lemma smul_balanced_core_subset (s : set E) {a : 𝕜} (ha : ∥a∥ ≤ 1) :
  a • balanced_core 𝕜 s ⊆ balanced_core 𝕜 s :=
begin
  rw subset_def,
  intros x hx,
  rw mem_smul_set at hx,
  rcases hx with ⟨y, hy, hx⟩,
  rw balanced_core_mem_iff at hy,
  rcases hy with ⟨t, ht1, ht2, hy⟩,
  rw ←hx,
  refine ⟨t, _, ht1 a ha (smul_mem_smul_set hy)⟩,
  rw mem_set_of_eq,
  exact ⟨ht1, ht2⟩,
end

lemma balanced_core_balanced (s : set E) : balanced 𝕜 (balanced_core 𝕜 s) :=
λ _, smul_balanced_core_subset s

lemma balanced.core_maximal {s t : set E} (hs : balanced 𝕜 s) (h : s ⊆ t): s ⊆ balanced_core 𝕜 t :=
begin
  refine subset_sUnion_of_mem _,
  rw [mem_set_of_eq],
  exact ⟨hs, h⟩,
end

lemma balanced_core_aux_mem_iff (s : set E) (x : E) : x ∈ balanced_core_aux 𝕜 s ↔
  ∀ (r : 𝕜) (hr : 1 ≤ ∥r∥), x ∈ r • s :=
by rw [balanced_core_aux, set.mem_Inter₂]


lemma balanced_hull_mem_iff (s : set E) (x : E) : x ∈ balanced_hull 𝕜 s ↔
  ∃ (r : 𝕜) (hr : ∥r∥ ≤ 1), x ∈ r • s :=
by rw [balanced_hull, set.mem_Union₂]

lemma balanced.hull_minimal {s t : set E} (ht : balanced 𝕜 t) (h : s ⊆ t) : balanced_hull 𝕜 s ⊆ t :=
begin
  intros x hx,
  rcases (balanced_hull_mem_iff _ _).mp hx with ⟨r, hr, hx⟩,
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩,
  rw ←hx,
  exact balanced_mem ht (h hy) hr,
end

end has_scalar

section add_comm_monoid

variables [add_comm_monoid E] [module 𝕜 E]

-- Begin of lemmas to be moved

--variables (𝕜 E)

lemma zero_singleton_balanced : balanced 𝕜 ({0} : set E) :=
λ a ha, by simp only [smul_set_singleton, smul_zero]

--variables {𝕜 E}

-- End of lemmas to be moved

lemma balanced_core_nonempty_iff {s : set E} : (balanced_core 𝕜 s).nonempty ↔ (0 : E) ∈ s :=
begin
  split; intro h,
  { cases h with x hx,
    have h' : balanced 𝕜 (balanced_core 𝕜 s) := balanced_core_balanced s,
    have h'' := h' 0 (has_le.le.trans norm_zero.le zero_le_one),
    refine mem_of_subset_of_mem (subset.trans h'' (balanced_core_subset s)) _,
    exact mem_smul_set.mpr ⟨x, hx, zero_smul _ _⟩ },
  refine nonempty_of_mem (mem_of_subset_of_mem _ (mem_singleton 0)),
  exact balanced.core_maximal zero_singleton_balanced (singleton_subset_iff.mpr h),
end

lemma balanced_core_zero {s : set E} (hs: (0 : E) ∈ s) : (0 : E) ∈ balanced_core 𝕜 s :=
balanced_core_mem_iff.mpr
  ⟨{0}, zero_singleton_balanced, singleton_subset_iff.mpr hs, mem_singleton 0⟩

lemma subset_balanced_hull [norm_one_class 𝕜] (s : set E) : s ⊆ balanced_hull 𝕜 s :=
λ _ hx, (balanced_hull_mem_iff _ _).mpr ⟨1, norm_one.le, mem_smul_set.mp ⟨_, hx, one_smul _ _⟩⟩

lemma balanced_hull.balanced (s : set E) : balanced 𝕜 (balanced_hull 𝕜 s) :=
begin
  intros a ha,
  simp_rw [balanced_hull, smul_set_Union₂, subset_def, mem_Union₂],
  intros x hx,
  rcases hx with ⟨r, hr, hx⟩,
  use [a • r],
  split,
  { rw smul_eq_mul,
    refine has_le.le.trans (semi_normed_ring.norm_mul _ _) _,
    refine mul_le_one ha (norm_nonneg r) hr },
  rw smul_assoc,
  exact hx,
end

end add_comm_monoid

end semi_normed_ring

section normed_field

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

@[simp] lemma balanced_core_aux_empty : balanced_core_aux 𝕜 (∅ : set E) = ∅ :=
begin
  rw [balanced_core_aux, set.Inter₂_eq_empty_iff],
  intros _,
  simp only [smul_set_empty, mem_empty_eq, not_false_iff, exists_prop, and_true],
  exact ⟨1, norm_one.ge⟩,
end

lemma balanced_core_aux_subset (s : set E) : balanced_core_aux 𝕜 s ⊆ s :=
begin
  rw subset_def,
  intros x hx,
  rw balanced_core_aux_mem_iff at hx,
  have h := hx 1 norm_one.ge,
  rw one_smul at h,
  exact h,
end

lemma balanced_core_aux_balanced (s : set E) (h0 : (0 : E) ∈ balanced_core_aux 𝕜 s):
  balanced 𝕜 (balanced_core_aux 𝕜 s) :=
begin
  intros a ha x hx,
  rcases mem_smul_set.mp hx with ⟨y, hy, hx⟩,
  by_cases (a = 0),
  {
    simp[h] at hx,
    rw ←hx,
    exact h0,
  },
  rw [←hx, balanced_core_aux_mem_iff],
  rw balanced_core_aux_mem_iff at hy,
  intros r hr,
  have h'' : 1 ≤ ∥a⁻¹ • r∥ :=
  begin
    rw smul_eq_mul,
    simp only [norm_mul, norm_inv],
    exact one_le_mul_of_one_le_of_one_le (one_le_inv (norm_pos_iff.mpr h) ha) hr,
  end,
  have h' := hy (a⁻¹ • r) h'',
  rw smul_assoc at h',
  exact (mem_inv_smul_set_iff₀ h _ _).mp h',
end

lemma balanced_core_aux_maximal {s t : set E} (h : t ⊆ s) (ht : balanced 𝕜 t) :
  t ⊆ balanced_core_aux 𝕜 s :=
begin
  intros x hx,
  rw balanced_core_aux_mem_iff,
  intros r hr,
  rw mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hr)),
  refine h (balanced_mem ht hx _),
  rw norm_inv,
  exact inv_le_one hr,
end

lemma balanced_core_subset_balanced_core_aux {s : set E} :
  balanced_core 𝕜 s ⊆ balanced_core_aux 𝕜 s :=
balanced_core_aux_maximal (balanced_core_subset s) (balanced_core_balanced s)

lemma balanced_core_eq_Inter {s : set E} (hs : (0 : E) ∈ s) :
  balanced_core 𝕜 s = ⋂ (r : 𝕜) (hr : 1 ≤ ∥r∥), r • s :=
begin
  rw ←balanced_core_aux,
  refine subset_antisymm balanced_core_subset_balanced_core_aux _,
  refine balanced.core_maximal (balanced_core_aux_balanced s _) (balanced_core_aux_subset s),
  refine mem_of_subset_of_mem balanced_core_subset_balanced_core_aux (balanced_core_zero hs),
end

end normed_field

end balanced_hull
