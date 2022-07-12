import tactic -- all the tactics
import ring_theory.flat -- flat modules
import ring_theory.tensor_product -- tensor product of A-algebras

-- We have flat modules, but we don't have flat ring homomorphisms, so let's make them
/-- A morphism of rings `A →+* B` is flat precisely when the induced `A`-module structure on `B` makes
`B` into a flat `A`-module. -/
def ring_hom.flat {A B : Type*} [comm_ring A] [comm_ring B] (f : A →+* B) : Prop :=
-- make B into an A-algebra from f, and put this fact into the type class inference system 
by letI : algebra A B := f.to_algebra; exact
-- now the type class inference system will figure out that B is an A-module
-- so we can use the concept of being flat as a module, which is already in Lean
module.flat A B 

-- notation for tensor products
open_locale tensor_product

/-- A morphism f: A → B of commutative rings is weakly etale (sometimes called "absolutely flat" if 
f is flat and the induced map B ⊗_[A] B → B is also flat. )-/
def is_weakly_etale {A B : Type*} [comm_ring A] [comm_ring B] (f : A →+* B) :=
by letI : algebra A B := f.to_algebra; exact
f.flat ∧ (algebra.tensor_product.lmul' A : B ⊗[A] B →ₐ[A] B).to_ring_hom.flat

-- Identity is weakly etale, composite of weakly etale is weakly etale, base change of weakly etale
-- is weakly etale.

-- Is the following true: weakly etale can be checked locally: A → B is weakly etale iff for all prime
-- ideals P of A and prime ideals Q of B whose pullback to A is P, the induced map A_P -> B_Q is
-- weakly etale.
