/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import WHIR.ProximityGen
import WHIR.ReedSolomonCodes

/-- `Fin l → F: α ↦ (1, α, α², … , α^(l-1))` -/
def RSSmpl
    {F : Type*} [Field F]
    (l : ℕ)
    (x : F) : Fin l → F := fun i => x ^ (i : ℕ)

noncomputable def RSGenerator
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {m : ℕ }
  (C : ReedSolomonCode F L (2^m : ℕ ))
  (l : ℕ) : Generator C.toLinearCode l where
    Smpl  := RSSmpl l
    BStar := Real.sqrt C.rate
    err   := fun δ => ENNReal.ofReal (
      if δ ≤ (1 - C.rate) / 2 then
        ((m - 1) * 2^m) / (C.rate * Fintype.card F )
      else
        let min_val := min (1 - (Real.sqrt C.rate) - δ ) ((Real.sqrt C.rate) / 20)
        ((m - 1) * (2^m)^2) / ((Fintype.card F) * (2 * min_val)^7)
      )

lemma proximity_gap
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {m : ℕ }
  (C : ReedSolomonCode F L (2^m : ℕ))
  (l :ℕ) : Generator.isProximityGenerator (RSGenerator C l) := sorry
