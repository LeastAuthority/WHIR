import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic


/-!  ###  Error–correcting codes over an alphabet  -/


/-- An error correcting code of length `|ι|` over some alphabet. -/
structure ErrorCorrectingCode (Alphabet : Type*) (ι : Type*) [Fintype ι] where
  words : Set (ι → Alphabet)

structure LinearCode
    (F : Type*) [Field F]
    (ι : Type*) [Fintype ι]
    extends ErrorCorrectingCode F ι where
      (toSubmodule : Submodule F (ι → F))
      (carrier_eq  : (toSubmodule : Set (ι → F)) = words)

/-- Coerce a `Finset` of words into an `ErrorCorrectingCode` -/
def ofFinset
  (Alphabet : Type*)
  (ι : Type*) [Fintype ι]
  (C : Finset (ι → Alphabet)) : ErrorCorrectingCode Alphabet ι :=
    { words := (C : Set _) }
