import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Nat.Bitwise

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Basic

/- Given integers `m` and `i` this computes monomial exponents
   ( σ(0), ..., σ(m) ) = ( bit₀(i), ..., bitₘ₋₁(i) )
   such that we can do X_0^σ(0)⬝  ⋯  ⬝ X_(m-1)^σ(m) -/
noncomputable def bitExpo
 (m i : ℕ ): (Fin m) →₀ ℕ :=
      Finsupp.onFinset Finset.univ
        (fun j => if Nat.testBit i j.1 then 1 else 0)
        (by
          intro j hj; simpa using hj)   -- trivially discharges the support proof

/-- `linMvExt m p` rewrites the univariate polynomial `p : F^(<2^m)[X]`
     as a degree wise linear multivariate polynomial in the variables
     `X₀ … Xₘ₋₁`, sending `aᵢ Xᶦ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))`,
     where `bitⱼ(i)` is the `j`-th binary digit of `i`. -/
noncomputable def linMvExt {F : Type*} [Field F]
  (m : ℕ)
  (p : ↥(Polynomial.degreeLT F (2^m))) : MvPolynomial (Fin m) F :=
    (p : Polynomial F).sum fun i a =>
      -- aᵢ Xⁱ ↦ aᵢ ∏ⱼ Xⱼ^(bitⱼ(i))
      MvPolynomial.monomial (bitExpo m i)  a

/- x → (x^(2⁰),x^(2¹),...,x^(2⁽ᵐ⁻¹⁾) -/
noncomputable def pow {F : Type*} [Field F] (m : ℕ) : Fin m → Polynomial F :=
  fun j : Fin m => (Polynomial.X : Polynomial F) ^ (2 ^ (j : ℕ))

/- Maps m-variate polynomials onto an univariate polynomial by
   invLinMvExt[p](x) := p(x^(2⁰),x^(2¹),...,x^(2⁽ᵐ⁻¹⁾))  -/
noncomputable def leftInvLinMvExt  {F : Type*} [Field F]
  {m : ℕ} (p: MvPolynomial (Fin m) F) : Polynomial F :=
    (MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (pow m) p
    )

/- For an univariate polynomial of degree < 2ᵐ, leftInvLinMvExt is a left inverse to
   linMvExt -/
lemma is_left_inverse
    {F : Type*} [Field F] {m : ℕ}
    (p : ↥(Polynomial.degreeLT F (2^m))) :
      leftInvLinMvExt (linMvExt m p) = p := by sorry
