import Poseidon.RoundConstants
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Poseidon

/-! # Poseidon hash function specification

Poseidon is an arithmetic-friendly hash function designed for efficient
use inside zero-knowledge proof systems. In Zcash's Orchard protocol it
is instantiated over the Pallas base field `Fp` and used for:

- Nullifier derivation (`PRF^nf_Orchard`)
- Note commitment randomness
- Halo 2 transcript hashing

## Parameters (Orchard instantiation)

- **Field**: `Fp` (Pallas base field, ≈ 2²⁵⁴)
- **Width (t)**: 3 field elements
- **Rate**: 2 field elements
- **Capacity**: 1 field element
- **S-box**: `x → x⁵` (alpha = 5)
- **Full rounds (R_F)**: 8 (4 before + 4 after partial rounds)
- **Partial rounds (R_P)**: 56
- **Total rounds**: 64

## Round structure

Each round applies three operations in sequence:
1. **AddRoundConstants**: add per-round constants to each state word
2. **S-box (SubWords)**: apply `x → x⁵` to all words (full round)
   or only the first word (partial round)
3. **MixLayer**: multiply state by the 3×3 MDS matrix

See §5.4.1.10 of the Zcash protocol specification.
-/

open Pasta Finset

noncomputable section

/-! ## State and round components -/

/-- The Poseidon state: a vector of `t = 3` field elements. -/
abbrev State := Fin t → Pasta.Fp

/-- The S-box: `x → x⁵`.

The exponent 5 is the smallest integer `α` such that `gcd(α, p-1) = 1`,
ensuring `x → x^α` is a permutation of `Fp`. -/
def sbox (x : Pasta.Fp) : Pasta.Fp := x ^ 5

/-- The 3×3 MDS (Maximum Distance Separable) matrix over `Fp`.

Generated as a Cauchy matrix to guarantee maximal branch number.
Values from the Zcash Orchard Poseidon instantiation. -/
def mdsMatrix : Fin t → Fin t → Pasta.Fp := fun i j =>
  if i.val = 0 then
    if j.val = 0 then 4844513277385895547578596669280046666372576567380472439333234012806535256931
    else if j.val = 1 then 22420227485671588580194914215361958133919537309433003325602272145024023440222
    else 3505906565384614297249013623188452104971681200991017471148427242055139865693
  else if i.val = 1 then
    if j.val = 0 then 15918204248318370126242808206081613758525089148509539575126649371340283647612
    else if j.val = 1 then 17094040714843518372934853765548613673798971581804674915582475057795168500270
    else 15812769689003694604229247543370933348074043003262912834067271177893884949626
  else
    if j.val = 0 then 20880359470746774736726481852287259022559450533689220298394450009637377072100
    else if j.val = 1 then 13164192954509875252051728398669721690665762613581286296450591265062029506148
    else 27123552791154096240274588421608257979835967097480491934880175221940903501553

/-! ## Round function components -/

/-- Add round constants to the state. -/
def addRoundConstants (r : Fin totalRounds) (s : State) : State :=
  fun i => s i + roundConstants r i

/-- Apply the S-box to all state elements (full round). -/
def sboxFull (s : State) : State :=
  fun i => sbox (s i)

/-- Apply the S-box to only the first state element (partial round). -/
def sboxPartial (s : State) : State :=
  fun i => if i.val = 0 then sbox (s i) else s i

/-- Multiply the state by the MDS matrix. -/
def mixLayer (s : State) : State :=
  fun i => ∑ j : Fin t, mdsMatrix i j * s j

/-! ## Round functions -/

/-- A full round: AddRoundConstants → S-box (all) → MDS. -/
def fullRound (r : Fin totalRounds) (s : State) : State :=
  mixLayer (sboxFull (addRoundConstants r s))

/-- A partial round: AddRoundConstants → S-box (first only) → MDS. -/
def partialRound (r : Fin totalRounds) (s : State) : State :=
  mixLayer (sboxPartial (addRoundConstants r s))

/-! ## Permutation -/

/-- Apply a sequence of rounds, given a round function and starting index. -/
def applyRounds (roundFn : Fin totalRounds → State → State)
    (start count : ℕ) (s : State) : State :=
  match count with
  | 0 => s
  | n + 1 =>
    if h : start < totalRounds then
      applyRounds roundFn (start + 1) n (roundFn ⟨start, h⟩ s)
    else s

/-- The Poseidon permutation `f : Fp³ → Fp³`.

Applies 4 full rounds, then 56 partial rounds, then 4 full rounds. -/
def permutation (s : State) : State :=
  let s₁ := applyRounds fullRound 0 (R_F / 2) s
  let s₂ := applyRounds partialRound (R_F / 2) R_P s₁
  applyRounds fullRound (R_F / 2 + R_P) (R_F / 2) s₂

/-! ## Sponge construction -/

/-- Initial capacity element for constant-input-length mode.

For 2-element input and 1-element output: `2 · 2⁶⁴ + 0 = 2⁶⁵`. -/
def initialCapacity : Pasta.Fp := (2 : Pasta.Fp) ^ 65

/-- `PoseidonHash(x, y)`: hash two field elements to one.

Initializes the sponge state as `[x, y, 2⁶⁵]` (rate ‖ capacity),
applies the permutation, and extracts the first element. -/
def poseidonHash (x y : Pasta.Fp) : Pasta.Fp :=
  let s : State := fun i =>
    if i.val = 0 then x
    else if i.val = 1 then y
    else initialCapacity
  permutation s ⟨0, by unfold t; omega⟩

end

end Poseidon
