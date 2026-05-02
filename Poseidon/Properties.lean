import Poseidon.Spec
import Mathlib.Data.Fintype.BigOperators
import Mathlib.FieldTheory.Finite.Basic

namespace Poseidon

/-! # Properties of the Poseidon permutation

The key structural properties:

1. **S-box bijectivity**: `x → x⁵` is a permutation of `Fp`, since
   `gcd(5, p-1) = 1`.

2. **Round bijectivity**: each round function (full or partial) is a
   bijection on the state space `Fp³`.

3. **Permutation bijectivity**: the full Poseidon permutation is a
   bijection, as a composition of bijective rounds.

These properties are necessary for the sponge construction's security:
a non-bijective permutation would leak information about the capacity.

See §5.4.1.10 of the Zcash protocol specification.
-/

open Pasta Finset

noncomputable section

/-! ## S-box properties -/

/-- The S-box exponent 5 is coprime to `p - 1`.

This ensures `x → x⁵` is a permutation of `Fp`. The factorization of
`p - 1 = 2³² × 3 × 463 × 539204044132271846773 × ...` contains no
factor of 5. -/
theorem alpha_coprime : Nat.Coprime 5 (Fp.p - 1) := by native_decide

/-- The inverse exponent for `x → x⁵`: the unique `d` with `5d ≡ 1 (mod p-1)`. -/
private def sboxInvExp : ℕ :=
  23158417847463239084714197001737581570690445185553248572763741411479974104269

private theorem five_mul_sboxInvExp :
    5 * sboxInvExp = (Fp.p - 1) * 4 + 1 := by native_decide

private theorem pow_five_mul_sboxInvExp (x : Pasta.Fp) :
    x ^ (5 * sboxInvExp) = x := by
  by_cases hx : x = 0
  · subst hx; simp [five_mul_sboxInvExp]
  · rw [five_mul_sboxInvExp, pow_add, pow_mul,
        ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul, pow_one]

/-- `x → x⁵` is a bijection on `Fp`.

Proven via Fermat's little theorem: the inverse map is `x → x^d`
where `5d ≡ 1 (mod p-1)`. -/
theorem sbox_bijective : Function.Bijective sbox := by
  rw [Function.bijective_iff_has_inverse]
  exact ⟨fun x => x ^ sboxInvExp, fun x => by
    simp only [sbox, ← pow_mul, pow_five_mul_sboxInvExp],
  fun x => by
    simp only [sbox, ← pow_mul]
    rw [show sboxInvExp * 5 = 5 * sboxInvExp from Nat.mul_comm ..]
    exact pow_five_mul_sboxInvExp x⟩

/-- The S-box maps zero to zero. -/
@[simp]
theorem sbox_zero : sbox 0 = 0 := by simp [sbox]

/-- The S-box is injective (corollary of bijectivity). -/
theorem sbox_injective : Function.Injective sbox := sbox_bijective.1

/-- The S-box is surjective (corollary of bijectivity). -/
theorem sbox_surjective : Function.Surjective sbox := sbox_bijective.2

/-! ## Round component bijectivity -/

/-- Adding round constants is a bijection (translation). -/
theorem addRoundConstants_bijective (r : Fin totalRounds) :
    Function.Bijective (addRoundConstants r) := by
  constructor
  · intro a b hab
    ext i
    have := congr_fun hab i
    simp only [addRoundConstants] at this
    exact add_right_cancel this
  · intro s
    exact ⟨fun i => s i - roundConstants r i, by
      ext i; simp [addRoundConstants]⟩

/-- Applying the S-box to all components is a bijection. -/
theorem sboxFull_bijective : Function.Bijective sboxFull := by
  constructor
  · intro a b hab
    ext i
    exact sbox_injective (congr_fun hab i)
  · intro s
    choose inv hinv using sbox_surjective
    exact ⟨fun i => inv (s i), by ext i; simp [sboxFull, hinv]⟩

/-- Applying the S-box to only the first component is a bijection. -/
theorem sboxPartial_bijective : Function.Bijective sboxPartial := by
  constructor
  · intro a b hab
    ext i
    have := congr_fun hab i
    simp only [sboxPartial] at this
    split at this
    · exact sbox_injective this
    · exact this
  · intro s
    choose inv hinv using sbox_surjective
    exact ⟨fun i => if i.val = 0 then inv (s i) else s i, by
      ext i; simp only [sboxPartial]
      split <;> simp_all⟩

/-- The inverse MDS matrix. -/
private def mdsInvMatrix : Fin t → Fin t → Pasta.Fp := fun i j =>
  if i.val = 0 then
    if j.val = 0 then 20241607003636850108660836115940502736811498405161200570689148677571525758571
    else if j.val = 1 then 23025138405716231373797697921576452089394779832936284534415647586071677203830
    else 21114470993121751666622391512824860651712966646298666275694910489305939207392
  else if i.val = 1 then
    if j.val = 0 then 3504033996059159311740309710248240756957113985486095525011622326035730769568
    else if j.val = 1 then 19414840413788828401816890242172608374848052910344543636209619190950790406233
    else 4217244064506252798101134783726078418056517622403921972441329684677055612801
  else
    if j.val = 0 then 21618660570245270623069891679058806165723984266207336981665295036319267277064
    else if j.val = 1 then 13921368629272394430455146883034263447975556794517869272975033952323006867723
    else 5901593508136776399775545089468732924270234646759139436179418386042074198766

private def mixLayerInv (s : State) : State :=
  fun i => ∑ j : Fin t, mdsInvMatrix i j * s j

private theorem mds_inv_mul (i j : Fin t) :
    ∑ k : Fin t, mdsInvMatrix i k * mdsMatrix k j =
    if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [mdsInvMatrix, mdsMatrix, t] <;>
    native_decide

private theorem mds_mul_inv (i j : Fin t) :
    ∑ k : Fin t, mdsMatrix i k * mdsInvMatrix k j =
    if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [mdsMatrix, mdsInvMatrix, t] <;>
    native_decide

/-- The MDS matrix multiplication is a bijection.

Proven by exhibiting the inverse matrix and verifying
`MDS_INV × MDS = I` and `MDS × MDS_INV = I` via `native_decide`. -/
theorem mixLayer_bijective : Function.Bijective mixLayer := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨mixLayerInv, fun s => ?_, fun s => ?_⟩
  · ext i
    simp only [mixLayerInv, mixLayer]
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, mds_inv_mul, ite_mul, one_mul, zero_mul,
             Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  · ext i
    simp only [mixLayer, mixLayerInv]
    simp_rw [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, mds_mul_inv, ite_mul, one_mul, zero_mul,
             Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ## Round bijectivity -/

/-- Each full round is a bijection. -/
theorem fullRound_bijective (r : Fin totalRounds) :
    Function.Bijective (fullRound r) :=
  mixLayer_bijective.comp (sboxFull_bijective.comp (addRoundConstants_bijective r))

/-- Each partial round is a bijection. -/
theorem partialRound_bijective (r : Fin totalRounds) :
    Function.Bijective (partialRound r) :=
  mixLayer_bijective.comp (sboxPartial_bijective.comp (addRoundConstants_bijective r))

/-! ## Permutation bijectivity -/

/-- Applying a sequence of bijective rounds preserves bijectivity. -/
theorem applyRounds_bijective
    (roundFn : Fin totalRounds → State → State)
    (hbij : ∀ r, Function.Bijective (roundFn r))
    (start count : ℕ) :
    Function.Bijective (applyRounds roundFn start count) := by
  induction count generalizing start with
  | zero => exact Function.bijective_id
  | succ n ih =>
    simp only [applyRounds]
    split
    · exact (ih (start + 1)).comp (hbij _)
    · exact Function.bijective_id

/-- **The Poseidon permutation is a bijection.**

This is essential for the sponge construction's security: a bijective
permutation on `Fp³` ensures the capacity element cannot be recovered
from the rate output alone. -/
theorem permutation_bijective : Function.Bijective permutation := by
  unfold permutation
  exact (applyRounds_bijective fullRound fullRound_bijective _ _).comp
    ((applyRounds_bijective partialRound partialRound_bijective _ _).comp
      (applyRounds_bijective fullRound fullRound_bijective _ _))

end

end Poseidon
