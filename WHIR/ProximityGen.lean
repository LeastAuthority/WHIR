/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import WHIR.ErrCorrCodes

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

structure Generator
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type*} [Fintype ι]
  (C : LinearCode F ι)
  (l : ℕ) where
    Smpl   : F → (Fin l → F)
    BStar  : ℝ
    err    : {δ : ℝ // 0 < δ ∧ δ < 1 - BStar} → ENNReal


namespace Gen

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι] [DecidableEq ι]

/- A generator `G`is a `proximity generator` if for every list of functions
   `f₁,…,f_ℓ : ι → F` and every admissible radius `δ` the following holds true:

   if a linear combination `\sum rᵢ·fᵢ` with random coefficients `rᵢ` drawn according
   to `G.Smpl` lands within fractional Hamming distance `δ` of the code `C`
   more frequently than the error bound `G.err δ`, then each function `fᵢ` coincides with
   some codeword on at least a `(1 - δ)` fraction of the evaluaton points. -/
def isProximityGenerator
    {l : ℕ}
    {C : LinearCode F ι}
    (G : Generator C l) : Prop :=
      ∀ (f : Fin l → ι → F) (δ : {δ : ℝ // 0 < δ ∧ δ < 1 - G.BStar}),
      ((PMF.uniformOfFintype F).toOuterMeasure
        { r | fractionalHammingDistSet
          (λ x ↦ ∑ j : Fin l, (G.Smpl r) j • (f j x))
          C.words
          C.toErrCorrCode.nonempty ≤ δ.val} ) >
        G.err δ →
        ∃ S : Finset ι,
          (S.card ≥ (1 - (δ : ℝ)) * (Fintype.card ι)) ∧
          ∀ i : Fin l, ∃ u ∈ C.words, ∀ x ∈ S, f i x = u x

end Gen


-- EXAMPLE USAGE:

/-- The generic *monomial sampler*
    `x ↦ (1, x, x², … , x^(l-1))` realised as a function
    `Fin l → F`. -/
def monomialSmpl
    {F : Type*} [Field F] (l : ℕ) (x : F) : Fin l → F :=
  fun i => x ^ (i : ℕ)        -- `i` coerces to a natural number

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

/-- **Proximity generator with monomial sampling**
    * `l` is kept abstract;
    * `Smpl` is `monomialSmpl l`;
    * `BStar = 0.1`;
    * `err δ = δ²`. -/
noncomputable def ProximityGen.monomial
    (C : LinearCode F ι) (l : ℕ) : Generator C l where
  Smpl  := monomialSmpl l
  BStar := (1 : ℝ) / 10        -- 0.1
  err   := fun δ => ((δ.1) ^ 2).toNNReal  -- square the underlying real number


/-
\begin{definition}[Proximity generator]\label{def:proximity-generator}
Let $\mathcal{C}\subseteq\mathbb{F}^{n}$ be a linear code.
We say that $\operatorname{Gen}$ is a \emph{proximity generator} for $\mathcal{C}$
with proximity bound $B$ and error $\operatorname{err}$ if the following implication
holds for every tuple of functions $f_{1},\dots ,f_{\ell}:[n]\to\mathbb{F}$ and every
$\delta\in (0,1-B(\mathcal{C},\ell))$.
If
\[
  \Pr_{(r_{1},\dots ,r_{\ell})\;\gets\;\operatorname{Gen}(\ell)}
  \!\Bigl[
      \Delta\!\Bigl(\textstyle\sum_{i\in[\ell]} r_{i}\cdot f_{i},\; \mathcal{C}\Bigr)
      \le \delta
  \Bigr]
  > \operatorname{err}(\mathcal{C},\ell,\delta),
\]
then there exists a set $S\subseteq[n]$ with $|S|\ge (1-\delta)\,n$ such that
\[
  \forall i\in[\ell]\; \exists\,u\in\mathcal{C}\;\text{ with }\;
        \forall x\in S,\; f_{i}(x)=u(x).
\]
\end{definition}


-/
