import tactic
import formally_smooth
import formally_unramified

/-!

# Formally etale morphisms

A ring morphism `A →+* B` between commutative rings `A` and `B` is
*formally étale* if for every surjective square-zero extension of
A-algebras `R' →+* R`(meaning that the kernel I satisties I² = 0),
the natural map Hom_A(B,R') → Hom_A(B,R) is bijective.

In other words, being formally etale is equivalent to being both
formally smooth and formally unramified.  That is how we define it.

-/

-- Let A and B be commutative rings
variables {A B : Type} [comm_ring A] [comm_ring B]

def is_formally_etale (f : A →+* B) : Prop := is_formally_smooth f ∧ is_formally_unramified f

lemma is_formally_etale_id : is_formally_etale (ring_hom.id A : A →+* A) :=
begin
  split, 
  apply is_formally_smooth_id, 
  apply is_formally_unramified_id,
end

variables {C : Type} [comm_ring C]

lemma is_formally_etale_comp {φ : A →+* B} (hφ : is_formally_etale φ)
  {ψ : B →+* C} (hψ : is_formally_etale ψ) : is_formally_etale (ψ.comp φ) :=
begin
  cases hφ, --with hφsm hφur,
  cases hψ,-- with hψsm hψur,
  split,
  { apply is_formally_smooth_comp,
    { intros _ _ _ _ _ _ f,
      apply hφ_left, },
    sorry,    
  },
  { sorry },
end

-- composition of formally etale is formally etale
