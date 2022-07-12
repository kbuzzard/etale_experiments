import tactic

-- I couldn't find this in mathlib

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

lemma alg_hom.eq_of_id (f : R →ₐ[R] A) : f = algebra.of_id R A :=
alg_hom.ext $ f.commutes

instance : subsingleton (R →ₐ[R] A) :=
subsingleton.intro $ λ f g, by { rw [alg_hom.eq_of_id f, alg_hom.eq_of_id g] }