/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.complex.cauchy_integral
import analysis.calculus.fderiv_analytic

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `differentiable.apply_eq_apply_of_bounded`,
`differentiable.exists_const_forall_eq_of_bounded`, and
`differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`complex.deriv_eq_smul_circle_integral`.
-/

open topological_space metric set filter asymptotics function measure_theory
open_locale topological_space filter nnreal real

universes u v
variables {E : Type u} [normed_group E] [normed_space ℂ E]
  {F : Type v} [normed_group F] [normed_space ℂ F] [measurable_space F] [borel_space F]
    [second_countable_topology F] [complete_space F]

namespace complex

/-- If `f` is complex differentiable on a closed disc with center `c` and radius `R > 0`, then
`f' c` can be represented as an integral over the corresponding circle.

TODO: add a version for `w ∈ metric.ball c R`.

TODO: add a version for higher derivatives. -/
lemma deriv_eq_smul_circle_integral {R : ℝ} {c : ℂ} {f : ℂ → F} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R)) :
  deriv f c = (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z :=
begin
  lift R to ℝ≥0 using hR.le,
  refine (has_fpower_series_on_ball_of_continuous_on_of_differentiable_on
    hc hd hR).has_fpower_series_at.deriv.trans _,
  simp only [cauchy_power_series_apply, one_div, zpow_neg₀, pow_one, smul_smul,
    zpow_two, mul_inv₀]
end

/-- If `f` is continuous on a closed disc of radius `R`, is complex differentiable on its interior,
and its values on the boundary circle of this disc are bounded from above by `C`, then the norm of
its derivative at the center is at most `C / R`.

TODO: drop unneeded assumptions `[complete_space F] [second_countable_topology F]`.  -/
lemma norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
  (hc : continuous_on f (closed_ball c R)) (hd : differentiable_on ℂ f (ball c R))
  (hC : ∀ z ∈ sphere c R, ∥f z∥ ≤ C) :
  ∥deriv f c∥ ≤ C / R :=
have ∀ z ∈ sphere c R, ∥(z - c) ^ (-2 : ℤ) • f z∥ ≤ C / (R * R),
  from λ z (hz : abs (z - c) = R), by simpa [norm_smul, hz, zpow_two, ← div_eq_inv_mul]
    using (div_le_div_right (mul_pos hR hR)).2 (hC z hz),
calc ∥deriv f c∥ = ∥(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - c) ^ (-2 : ℤ) • f z∥ :
  congr_arg norm (deriv_eq_smul_circle_integral hR hc hd)
... ≤ R * (C / (R * R)) :
  circle_integral.norm_two_pi_I_inv_smul_integral_le_of_norm_le_const hR.le this
... = C / R : by rw [mul_div_comm, div_self_mul_self', div_eq_mul_inv]

/-- An auxiliary lemma for Liouville's theorem `differentiable.apply_eq_apply_of_bounded`. -/
lemma liouville_theorem_aux {f : ℂ → F} (hf : differentiable ℂ f)
  (hb : bounded (range f)) (z w : ℂ) : f z = f w :=
begin
  suffices : ∀ c, deriv f c = 0, from is_const_of_deriv_eq_zero hf this z w,
  clear z w, intro c,
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ∥f z∥ ≤ C,
  { rcases bounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩,
    exact ⟨max C 1, lt_max_iff.2 (or.inr zero_lt_one),
      λ z, (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩ },
  refine norm_le_zero_iff.1 (le_of_forall_le_of_dense $ λ ε ε₀, _),
  calc ∥deriv f c∥ ≤ C / (C / ε) :
    norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.continuous.continuous_on
      hf.differentiable_on (λ z _, hC z)
  ... = ε : div_div_cancel' C₀.lt.ne'
end

end complex

namespace differentiable

open complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
lemma apply_eq_apply_of_bounded {f : E → F} (hf : differentiable ℂ f) (hb : bounded (range f))
  (z w : E) : f z = f w :=
begin
  set g : ℂ → F := f ∘ (λ t : ℂ, t • (w - z) + z),
  suffices : g 0 = g 1, by simpa [g],
  apply liouville_theorem_aux,
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.mono (range_comp_subset_range _ _)]
end

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
lemma exists_const_forall_eq_of_bounded {f : E → F} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, ∀ z, f z = c :=
⟨f 0, λ z, hf.apply_eq_apply_of_bounded hb _ _⟩

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
lemma exists_eq_const_of_bounded {f : E → F} (hf : differentiable ℂ f)
  (hb : bounded (range f)) : ∃ c, f = const E c :=
(hf.exists_const_forall_eq_of_bounded hb).imp $ λ c, funext

end differentiable
