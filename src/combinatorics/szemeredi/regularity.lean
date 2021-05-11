import data.finset.basic
import data.real.basic

variables {V : Type*} {G : finset V → Prop} {k n : ℕ}

def is_uniform_hypergraph (G : finset V → Prop) (k : ℕ) : Prop :=
∀ x : finset V, G x → x.card = k

def is_partite (G : finset V → Prop) (k : ℕ) : Prop :=
∃ (ι : Type*) (X : ι → finset (finset V)), ∀ x₁ x₂, G x₁ → G x₂ →
  ∀ i₁ i₂, x₁ ∈ X i₁ → x₂ ∈ X i₂ → i₁ = i₂

--def is_partite_function

--def is_quasi_random :

--lemma szemeredi_regularity {G : finset V → Prop} (hG : is_partite G 2) {ε : ℝ} (ε_pos : 0 < ε) :
