import tactic
import for_mathlib -- gives us new theorem `alg_hom.eq_of_id`

/-!

# Formally smooth morphisms

A ring morphism `A →+* B` between commutative rings `A` and `B` is *formally smooth*
if for every square-zero extension of A-algebras `R' →+* R`
(meaning that the kernel I satisties I² = 0)
the natural map Hom_A(B,R') → Hom_A(B,R) is surjective.

-/

-- Let A and B be commutative rings
variables {A B : Type} [comm_ring A] [comm_ring B]

--set_option pp.notation false

/-- A ring homomorphism `f : A → B` is *formally smooth* if for every equare zero
morphism `φ : R → R'` of A-algebras, the natural map Hom_A(B,R') → Hom_A(B, R) is
a surjection. -/
def is_formally_smooth {A B : Type} [comm_ring A] [comm_ring B] (f : A →+* B) : Prop :=
-- First let's make B into an A-algebra in the obvious way via f
let h : algebra A B := f.to_algebra in
-- The condition is: For all A-algebras R and R'
∀ {R R' : Type} [comm_ring R] [comm_ring R'], by exactI
∀ [algebra A R] [algebra A R'], by exactI
-- and for all A-algebra morphisms φ : R' → R with square zero
∀ {φ : R' →ₐ[A] R} (hφ1 : ∀ r : R, ∃ r' : R', φ r' = r) 
  (hφ2 : ∀ x y : R', φ x = 0 → φ y = 0 → x * y = 0),
-- composing with φ is a bijection Hom_A(B,R') → Hom_A(B, R)
function.surjective (φ.comp : (B →ₐ[A] R') → (B →ₐ[A] R))

lemma is_formally_smooth_id : is_formally_smooth (ring_hom.id A : A →+* A) :=
begin
  intros R R' _ _ _ _ φ _ _ ψ,
  resetI,
  use algebra.of_id A R',
  apply subsingleton.elim,
end

variables {C : Type} [comm_ring C]

lemma is_formally_smooth_comp {φ : A →+* B} (hφ : is_formally_smooth φ)
  {ψ : B →+* C} (hψ : is_formally_smooth ψ) : is_formally_smooth (ψ.comp φ) :=
begin
  sorry
end
