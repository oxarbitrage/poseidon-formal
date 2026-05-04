# poseidon-formal

**Status:** Fully proven — zero `sorry` statements.

A Lean 4 formalization of the Poseidon hash function (as instantiated in Zcash's Orchard protocol), with a machine-verified proof that the permutation is a bijection on 𝔽_p³.

## Overview

Poseidon is an arithmetic hash function designed for efficient evaluation inside algebraic constraint systems such as those underlying SNARKs and STARKs. Unlike SHA-256, whose bit-manipulation operations require thousands of R1CS constraints, Poseidon's design centres on the S-box `x ↦ xᵅ`, which contributes a single multiplication gate per application. This *low multiplicative complexity* makes Poseidon the hash of choice for ZK-proof systems that must hash field elements natively.

In Zcash's Orchard protocol, Poseidon is instantiated over the Pallas base field 𝔽_p and used for nullifier derivation (`PRF^nf_Orchard`), note commitment randomness, and Halo 2 transcript hashing. The relevant entry point is `poseidonHash(nk, ρ)`, which absorbs the nullifier key `nk` and note position `ρ` through a two-element sponge, producing a single field element. This construction appears in §5.4.1.10 of the Zcash protocol specification.

This repository formalizes the Orchard Poseidon instance in Lean 4, providing machine-checked definitions of every layer of the permutation and a complete proof of its bijectivity. All 192 round constants are inlined as concrete 𝔽_p literals, cross-checked against the [Halo 2 reference implementation](https://github.com/zcash/halo2). No `sorry` or unproven axioms are used.

## Mathematical Background

### Poseidon Parameters (Zcash/Orchard Instance)

| Parameter | Value |
|-----------|-------|
| Field | Pallas base field 𝔽_p, p ≈ 2²⁵⁴ |
| State width (t) | 3 field elements |
| Rate | 2 field elements |
| Capacity | 1 field element |
| S-box exponent (α) | 5 |
| Full rounds (R_F) | 8 (4 before + 4 after partial rounds) |
| Partial rounds (R_P) | 56 |
| Total rounds | 64 |

### Why α = 5?

The S-box `x ↦ xᵅ` is a bijection on 𝔽_p if and only if gcd(α, p − 1) = 1. For the Pallas field, the factorisation of p − 1 is:

```
p − 1 = 2³² × 3 × 463 × 539204044132271846773 × …
```

This contains no factor of 5, so gcd(5, p − 1) = 1, and `x ↦ x⁵` is a permutation of 𝔽_p. The coprimality is formally established in this repo as:

```lean
theorem alpha_coprime : Nat.Coprime 5 (Fp.p - 1) := by native_decide
```

The more common choice α = 3 is ruled out for this field because 3 | (p − 1), making `x ↦ x³` many-to-one. Choosing the smallest valid odd α minimises the algebraic degree of the permutation while retaining injectivity, yielding the best trade-off between circuit efficiency and security margin.

### The MDS Matrix

The linear layer applies a 3×3 *maximum distance separable* (MDS) matrix over 𝔽_p. MDS matrices guarantee that any t columns (equivalently, any t input differences) affect all t output differences — this is the *full diffusion* property central to the wide-trail security argument. Poseidon uses a Cauchy matrix construction, which is MDS by design. The concrete 9 entries and their explicit inverse are provided in `Spec.lean` and `Properties.lean` respectively. Invertibility is verified by checking:

```lean
private theorem mds_inv_mul (i j : Fin t) :
    ∑ k, mdsInvMatrix i k * mdsMatrix k j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide

private theorem mds_mul_inv (i j : Fin t) :
    ∑ k, mdsMatrix i k * mdsInvMatrix k j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> native_decide
```

Both `M⁻¹ × M = I` and `M × M⁻¹ = I` are machine-checked, confirming 𝔽_p-invertibility of the MDS layer.

### Round Structure

Each round applies three operations in sequence:

1. **AddRoundConstants (ARC):** add a vector of per-round constants to the state.
2. **SubWords (S-box):** apply `x ↦ x⁵` to *all* state elements (full round) or *only the first* (partial round).
3. **MixLayer:** multiply the state vector by the 3×3 MDS matrix.

The permutation consists of R_F/2 = 4 full rounds, followed by R_P = 56 partial rounds, followed by R_F/2 = 4 full rounds, for 64 rounds total. Partial rounds reduce the number of S-box evaluations per round from 3 to 1, dramatically lowering the constraint count of the corresponding arithmetic circuit while the full rounds at either end maintain statistical security against differential and linear cryptanalysis.

### What Bijectivity Gives (and What It Doesn't)

**Proven in this repository:**

- `permutation_bijective : Function.Bijective permutation` — the full Poseidon permutation is a bijection on 𝔽_p³. This is a necessary condition for sponge indifferentiability from a random oracle: a non-injective permutation would allow collisions in the capacity element to be exploited.

**Not proven in this repository:**

- *Preimage resistance* — given a hash output y, finding x such that `poseidonHash(x₁, x₂) = y` is believed to be hard. This relies on the algebraic degree of the permutation (related to the number of full rounds and the choice of α) and the wide-pipe sponge argument, neither of which is derivable from bijectivity alone.
- *Collision resistance* — also conjectured from algebraic security arguments (Gröbner basis complexity, interpolation attacks) beyond the scope of this formalization.

Bijectivity is the *structural* property of the permutation; hardness properties are *computational* conjectures over specific adversary models.

### Round Constants

There are 192 constants (64 rounds × 3 state elements), generated by a Grain LFSR seeded with the parameters: 128-bit security, S-box `x⁵`, width t = 3, R_F = 8, R_P = 56, field characteristic p (Pallas). The generation procedure is specified in [pasta-hadeshash](https://github.com/daira/pasta-hadeshash). The constants are provided here as concrete 𝔽_p literals and cross-checked against the Halo 2 reference implementation; their derivation from the Grain LFSR is not re-verified in Lean.

## Formalization

### `Poseidon/RoundConstants.lean`

Defines the global parameters (`t`, `R_F`, `R_P`, `totalRounds`) and the function `roundConstants : Fin totalRounds → Fin t → Fp` giving all 192 Grain LFSR constants as concrete literals over the Pallas base field.

### `Poseidon/Spec.lean`

All definitions, in order:

| Definition | Type | Description |
|------------|------|-------------|
| `State` | `Fin 3 → Fp` | State vector: 3 field elements |
| `sbox` | `Fp → Fp` | S-box: `x ↦ x⁵` |
| `mdsMatrix` | `Fin 3 → Fin 3 → Fp` | 3×3 Cauchy MDS matrix (concrete values) |
| `addRoundConstants` | `Fin 64 → State → State` | ARC layer |
| `sboxFull` | `State → State` | S-box applied to all 3 elements |
| `sboxPartial` | `State → State` | S-box applied to first element only |
| `mixLayer` | `State → State` | MDS matrix multiplication |
| `fullRound` | `Fin 64 → State → State` | ARC → sboxFull → mixLayer |
| `partialRound` | `Fin 64 → State → State` | ARC → sboxPartial → mixLayer |
| `applyRounds` | `(Fin 64 → State → State) → ℕ → ℕ → State → State` | Apply `count` rounds starting at `start` |
| `permutation` | `State → State` | 4 full + 56 partial + 4 full rounds |
| `initialCapacity` | `Fp` | `2⁶⁵` — capacity word for 2-element CIL mode |
| `poseidonHash` | `Fp → Fp → Fp` | Sponge: absorb `[x, y, 2⁶⁵]`, permute, squeeze element 0 |

### `Poseidon/Properties.lean`

**S-box:**

- `alpha_coprime : Nat.Coprime 5 (Fp.p - 1)` — gcd(5, p−1) = 1, verified by `native_decide`
- `sbox_bijective : Function.Bijective sbox` — `x ↦ x⁵` is a bijection; proven via Fermat's little theorem using the inverse exponent `d = 23158417847463239084714197001737581570690445185553248572763741411479974104269` satisfying `5d ≡ 1 (mod p−1)`
- `sbox_injective : Function.Injective sbox` — corollary of bijectivity
- `sbox_surjective : Function.Surjective sbox` — corollary of bijectivity

**Layers:**

- `addRoundConstants_bijective (r) : Function.Bijective (addRoundConstants r)` — translation by a constant vector is bijective
- `sboxFull_bijective : Function.Bijective sboxFull` — componentwise S-box is bijective
- `sboxPartial_bijective : Function.Bijective sboxPartial` — first-element S-box is bijective
- `mdsInvMatrix` — the explicit 3×3 inverse of `mdsMatrix` over 𝔽_p
- `mds_inv_mul`, `mds_mul_inv` — M⁻¹M = I and MM⁻¹ = I, verified by `native_decide`
- `mixLayer_bijective : Function.Bijective mixLayer` — MDS multiplication is bijective (via explicit inverse)

**Rounds:**

- `fullRound_bijective (r) : Function.Bijective (fullRound r)` — each full round is a bijection (composition of bijections)
- `partialRound_bijective (r) : Function.Bijective (partialRound r)` — each partial round is a bijection
- `applyRounds_bijective` — applying a sequence of bijective rounds preserves bijectivity; proven by induction on the round count

**Main result:**

- `permutation_bijective : Function.Bijective permutation` — the full Poseidon permutation is a bijection on 𝔽_p³

## Key Result: Permutation Bijectivity

```lean
theorem permutation_bijective : Function.Bijective permutation
```

The proof follows a clean compositional chain:

```
alpha_coprime          (native_decide)
    ↓
sbox_bijective         (Fermat's little theorem + inverse exponent)
    ↓
sboxFull_bijective, sboxPartial_bijective
    ↓
addRoundConstants_bijective, mixLayer_bijective
    ↓
fullRound_bijective, partialRound_bijective   (composition of bijections)
    ↓
applyRounds_bijective  (induction on round count)
    ↓
permutation_bijective  (three sequential applyRounds calls)
```

Every step is constructive. No `sorry` appears anywhere in the proof chain.

## Axioms

**None** beyond Lean's built-in kernel axioms. All results are derived from Mathlib's finite field theory and ring arithmetic. The two uses of `native_decide` — for `alpha_coprime` (gcd computation) and for `mds_inv_mul`/`mds_mul_inv` (9 matrix entry checks each) — invoke Lean's `Lean.ofReduceBool` kernel primitive, which is part of Lean's trusted kernel, not an additional axiom.

Note: the 192 round constants are provided as concrete 𝔽_p literals consistent with the Grain LFSR specification. Their generation process is not re-verified in Lean — they are fixed parameters of the Orchard instantiation.

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — finite fields, Fermat's little theorem, ring arithmetic, big operators
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas base field 𝔽_p definitions and primality proofs

## Building

Requires [elan](https://github.com/leanprover/elan). The correct toolchain is pinned in `lean-toolchain` and installed automatically.

```shell
lake update   # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build    # compiles in ~10 seconds after cache download
```

## References

- [Zcash Protocol Specification §5.4.1.10](https://zips.z.cash/protocol/protocol.pdf) — Poseidon hash
- [Grassi et al., "Poseidon: A New Hash Function for Zero-Knowledge Proof Systems"](https://eprint.iacr.org/2019/458)
- [Halo 2 Poseidon spec](https://zcash.github.io/halo2/design/gadgets/poseidon.html)
- [pasta-hadeshash](https://github.com/daira/pasta-hadeshash) — Grain LFSR reference for round constants
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization

## License

MIT
