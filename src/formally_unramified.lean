import tactic
import for_mathlib -- gives us new theorem `alg_hom.eq_of_id`

/-!

# Formally unramified morphisms

A ring morphism `A →+* B` between commutative rings `A` and `B` is *formally unramified*
if for every square-zero extension of A-algebras `R' →+* R`
(meaning that the kernel I satisties I² = 0)
the natural map Hom_A(B,R') → Hom_A(B,R) is injective.

-/

-- Let A and B be commutative rings
variables {A B : Type} [comm_ring A] [comm_ring B]

--set_option pp.notation false

/-- A ring homomorphism `f : A → B` is *formally unramified* if for every equare zero
morphism `φ : R → R'` of A-algebras, the natural map Hom_A(B,R') → Hom_A(B, R) is
an injection. -/
def is_formally_unramified {A B : Type} [comm_ring A] [comm_ring B] (f : A →+* B) : Prop :=
-- First let's make B into an A-algebra in the obvious way via f
let h : algebra A B := f.to_algebra in
-- The condition is: For all A-algebras R and R'
∀ {R R' : Type} [comm_ring R] [comm_ring R'], by exactI
∀ [algebra A R] [algebra A R'], by exactI
-- and for all A-algebra morphisms φ : R' → R with square zero
∀ {φ : R' →ₐ[A] R} (hφ1 : ∀ r : R, ∃ r' : R', φ r' = r) 
  (hφ2 : ∀ x y : R', φ x = 0 → φ y = 0 → x * y = 0),
-- composing with φ is an injection Hom_A(B,R') → Hom_A(B, R)
function.injective (φ.comp : (B →ₐ[A] R') → (B →ₐ[A] R))

lemma is_formally_unramified_id : is_formally_unramified (ring_hom.id A: A →+* A) :=
begin
  intros R R',
  intro _,
  intro _,
  intros _ _,
  intro φ,
  intro hφ,
  intro hφ',
  unfold function.injective,
  intros a₁ a₂,
  resetI,
  intro h,
  rw a₁.eq_of_id,
  rw a₂.eq_of_id,
  -- the last two lines can be replaced by
  -- apply subsingleton.elim,
  -- then lean does more work (see zulip chat)
end


variables {C : Type} [comm_ring C]

lemma is_formally_unramified_comp {φ : A →+* B} (hφ : is_formally_unramified φ)
  {ψ : B →+* C} (hψ : is_formally_unramified ψ) : is_formally_unramified (ψ.comp φ) :=
begin
 intros R R' _ _ _ _ f,
 intros hf1 hf2,
  unfold function.injective,
  intros a₁ a₂ hyp, --We had failed to introduce the hypothesis here before!
  letI : algebra A B := φ.to_algebra,
  letI : algebra A C := (ψ.comp φ).to_algebra,
  let ψ' : B →ₐ[A] C :=
  { commutes' := λ r, rfl, -- definitional abuse!
    ..ψ },
have h_5: f.comp (a₁.comp ψ') =  f.comp (a₂.comp ψ'),
  begin --I can prove this now because we introduced hyp!
  rw ← alg_hom.comp_assoc,
  rw ← alg_hom.comp_assoc,
  rw hyp, 
  end,
 --unfold function.injective at hφ,
 have h_6: a₁.comp ψ' =  a₂.comp ψ', -- as phi is formally unramified
  begin
  apply hφ hf1 hf2,
  apply h_5
  end,
 let σ := a₁.comp ψ',
 let ρ := f.comp (a₁.comp ψ'),
 letI : algebra B R' := σ.to_ring_hom.to_algebra,
 letI : algebra B R := ρ.to_ring_hom.to_algebra,
 let f' : R' →ₐ[B] R :=
  { commutes' := λ r, rfl,
    ..f },
-- now I want to tell lean that a₁ and a₂ are in fact B algbera maps using h_6.
letI : algebra B C := ψ.to_algebra,
let a₁' : C →ₐ[B] R' :=
{ commutes' :=  λ r, rfl,
   ..a₁ },
let a₂' : C →ₐ[B] R' :=
{ commutes' := begin intro r, change (a₂.comp ψ') r = _, rw ← h_6, refl,
end, ..a₂ },
have h_7 : f'.comp a₁' = f'.comp a₂',
  begin
  ext r,
  rw alg_hom.ext_iff at hyp,
  specialize hyp r,
  exact hyp,
  end,
have hf1' : ∀ (r : R), ∃ (r' : R'), f' r' = r,
  exact hf1,
have hf2' : ∀ (x y : R'), f' x = 0 → f' y = 0 → x * y = 0,
  exact hf2,
have h_8 : a₁' = a₂', 
  begin 
  specialize hψ hf1' hf2',
  apply hψ h_7,
  end,
ext r,
rw alg_hom.ext_iff at h_8,
specialize h_8 r,
exact h_8,
end

