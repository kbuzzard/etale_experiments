import tactic

variables {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]

-- I couldn't find this in mathlib

lemma alg_hom.eq_of_id (f : R →ₐ[R] A) : f = algebra.of_id R A :=
alg_hom.ext $ f.commutes

instance alg_hom.subsingleton : subsingleton (R →ₐ[R] A) :=
subsingleton.intro $ λ f g, by { rw [alg_hom.eq_of_id f, alg_hom.eq_of_id g] }