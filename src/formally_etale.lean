import tactic

/-!

# Formally etale, formally smooth and formally unramified morphisms

A ring morphism `A →+* B` between commutative rings `A` and `B` is
  * formally étale;
  * resp formally smooth;
  * resp formally unramified

if for every square-zero extension of A-algebras `R' →+* R`
(meaning that the kernel I satisties I² = 0)
the natural map Hom_A(B,R') → Hom_A(B,R)

is

* bijective;
* resp. surjective;
* resp. injective.

-/

-- Let A and B be commutative rings
variables {A B : Type} [comm_ring A] [comm_ring B]

/-- A ring homomorphism `f : A → B` is *formally etale* if for every equare zero
morphism `φ : R → R'` of A-algebras, the natural map Hom_A(B,R') → Hom_A(B, R) is
a bijection. -/
def is_formally_etale (f : A →+* B) : Prop :=
-- First let's make B into an A-algebra in the obvious way via f
let h : algebra A B := f.to_algebra in
-- The condition is: For all A-algebras R and R'
∀ {R R' : Type} [comm_ring R] [comm_ring R'], by exactI
∀ [algebra A R] [algebra A R'], by exactI
-- and for all A-algebra morphisms φ : R' → R with square zero
∀ {φ : R' →ₐ[A] R} (hφ1 : ∀ r : R, ∃ r' : R', φ r' = r) (hφ2 : ∀ x : R', φ x = 0 → x^2 = 0),
-- composing with φ is a bijection Hom_A(B,R') → Hom_A(B, R)
function.bijective (φ.comp : (B →ₐ[A] R') → (B →ₐ[A] R))

lemma is_formally_etale_id : is_formally_etale (ring_hom.id A : A →+* A) :=
begin
  sorry
end

-- TODO: formally smooth and formally unramified definitions
-- Change definition of `is_formally_etale` to be `is_formally_smooth ∧ is_formally_unramified`?
-- identity is formally etale/smooth/unram
-- composition of formally etale/smooth/unram is formally etale/smooth/unram
