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
-- composing with φ is a surjection Hom_A(B,R') → Hom_A(B, R)
function.surjective (φ.comp : (B →ₐ[A] R') → (B →ₐ[A] R))

lemma is_formally_smooth_id : is_formally_smooth (ring_hom.id A : A →+* A) :=
λ R R' _ _ _ _ φ _ _ ψ, by resetI; exact ⟨algebra.of_id A R', subsingleton.elim _ _⟩

variables {C : Type} [comm_ring C]

lemma is_formally_smooth_comp {φ : A →+* B} (hφ : is_formally_smooth φ)
  {ψ : B →+* C} (hψ : is_formally_smooth ψ) : is_formally_smooth (ψ.comp φ) :=
begin
  intros R R' _ _ _ _ f hf1 hf2 g,
  resetI,
  specialize hφ hf1 hf2,
  letI : algebra A B := φ.to_algebra,
  letI : algebra A C := (ψ.comp φ).to_algebra,
  let ψ' : B →ₐ[A] C := 
  { commutes' := λ r, rfl, -- definitional abuse!
    ..ψ },
  let ρ := g.comp ψ',
  unfold function.surjective at hφ,
  specialize hφ ρ,
  cases hφ with σ hσ,
  -- last four lines can be done  with 
  --  obtain ⟨σ, hσ⟩ := hφ (g.comp ψ'),
  -- use σ to make R' into a B-algebra
  letI : algebra B R' := σ.to_ring_hom.to_algebra,
  letI : algebra B R := ρ.to_ring_hom.to_algebra,
  let f' : R' →ₐ[B] R :=
  { commutes' := begin 
-- alternate proof:
--      rw alg_hom.ext_iff at hσ,
--      exact hσ,
      intro r,
      change _ = ρ r,
      rw ← hσ,
      refl,
    end,
    ..f.to_ring_hom, },
  have hf1' : ∀ (r : R), ∃ (r' : R'), f' r' = r,
  exact hf1,
  have hf2' : ∀ (x y : R'), f x = 0 → f y = 0 → x * y = 0,
  exact hf2,
  specialize hψ hf1' hf2',
  letI : algebra B C := ψ.to_algebra,
  let g' : C →ₐ[B] R :=
  { commutes' := begin 
    intro,
    refl, end,
    ..g },
  obtain ⟨τ, hτ⟩ := hψ g',
  let τ' : C →ₐ[A] R' :=
  { commutes' := begin intro r,
      convert τ.commutes (φ r),
      suffices : algebra.of_id A R' = σ.comp (algebra.of_id A B),
      { rw alg_hom.ext_iff at this,
        apply this, },
      apply subsingleton.elim,
    end,
    ..τ, },
  use τ',
  ext,
  change _ = g' x,
  rw ← hτ,
  refl,
end
