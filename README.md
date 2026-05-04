# poseidon-formal

Lean 4 formalization of the [Poseidon](https://zips.z.cash/protocol/protocol.pdf#poseidonhash) hash function as instantiated in Zcash's [Orchard](https://zcash.github.io/orchard/) protocol.

**Status: fully proven — zero `sorry`.**

## What's formalized

All definitions and theorems live under the `Poseidon` namespace. Built on top of [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

| Component | File | Description |
|-----------|------|-------------|
| Parameters | `Poseidon/RoundConstants.lean` | Width t=3, R_F=8 full rounds, R_P=56 partial rounds |
| State type | `Poseidon/Spec.lean` | `Fin 3 → Fp` — vector of 3 field elements |
| S-box | `Poseidon/Spec.lean` | `x → x⁵` (alpha = 5) |
| Round constants | `Poseidon/RoundConstants.lean` | 192 concrete constants over Fp from the Grain LFSR |
| MDS matrix | `Poseidon/Spec.lean` | 3×3 Cauchy matrix over Fp, concrete values from Orchard spec |
| AddRoundConstants | `Poseidon/Spec.lean` | Add per-round constants to state |
| S-box application | `Poseidon/Spec.lean` | Full (all words) and partial (first word only) |
| MixLayer | `Poseidon/Spec.lean` | MDS matrix multiplication |
| Full/partial rounds | `Poseidon/Spec.lean` | ARC → S-box → MDS composition |
| Permutation | `Poseidon/Spec.lean` | 4 full + 56 partial + 4 full rounds |
| PoseidonHash | `Poseidon/Spec.lean` | Sponge construction: `[x, y, 2⁶⁵] → permute → extract` |
| alpha coprimality | `Poseidon/Properties.lean` | `gcd(5, p-1) = 1` — proven by `native_decide` |
| S-box bijectivity | `Poseidon/Properties.lean` | `x → x⁵` is a permutation of Fp — proven via Fermat's little theorem |
| AddRC bijectivity | `Poseidon/Properties.lean` | Translation is bijective — proven |
| S-box full/partial bijectivity | `Poseidon/Properties.lean` | Componentwise S-box is bijective — proven |
| MDS invertibility | `Poseidon/Properties.lean` | MDS matrix is invertible — proven via explicit inverse |
| **Round bijectivity** | `Poseidon/Properties.lean` | Each full/partial round is a bijection — proven |
| **Permutation bijectivity** | `Poseidon/Properties.lean` | The full Poseidon permutation is a bijection — proven |

## Axiom-free

This formalization has **zero axioms** (beyond Lean's kernel axioms). The 192 round constants from the Grain LFSR are provided as concrete values, cross-checked against the [Halo 2 implementation](https://github.com/zcash/halo2). All security-relevant properties are fully proven:

- **S-box bijectivity** via Fermat's little theorem: computing the inverse exponent `d` with `5d ≡ 1 (mod p-1)` and showing `x^(5d) = x`.
- **MDS invertibility** by exhibiting the explicit inverse matrix and verifying `M⁻¹ × M = I` and `M × M⁻¹ = I` via `native_decide`.

## Security argument

The Poseidon permutation's bijectivity is essential for the sponge construction's security:

1. **Permutation bijectivity** (proven): the full permutation is a bijection on `Fp³`, composed from bijective rounds.
2. **Sponge indifferentiability** (not formalized): with a bijective permutation, the sponge construction is indifferentiable from a random oracle (Bertoni et al.).
3. **Algebraic security** (not formalized): the mix of full/partial rounds provides resistance against algebraic attacks (Gröbner basis, interpolation).

See [§5.4.1.10 of the Zcash protocol specification](https://zips.z.cash/protocol/protocol.pdf#poseidonhash).

## Building

Requires [elan](https://github.com/leanprover/elan). The correct Lean toolchain is installed automatically.

```sh
lake update    # fetch Mathlib + pasta-formal (~3 GB of cached oleans)
lake build     # builds in ~10 seconds after cache download
```

## Dependencies

- **Lean 4** (v4.30.0-rc2)
- **Mathlib4** — finite field theory, big operators, tactics
- **[pasta-formal](https://github.com/oxarbitrage/pasta-formal)** — Pallas/Vesta curve definitions and primality proofs

## References

- [Zcash Protocol Specification §5.4.1.10](https://zips.z.cash/protocol/protocol.pdf#poseidonhash) — PoseidonHash specification
- [Poseidon: A New Hash Function for Zero-Knowledge Proof Systems](https://eprint.iacr.org/2019/458) — original paper
- [pasta-hadeshash](https://github.com/daira/pasta-hadeshash) — Sage script for generating round constants
- [zcash/orchard](https://github.com/zcash/orchard) — Rust implementation
- [pasta-formal](https://github.com/oxarbitrage/pasta-formal) — Pallas/Vesta Lean 4 formalization

## License

MIT
