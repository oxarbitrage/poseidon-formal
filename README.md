# poseidon-formal

**Status:** Fully proven — zero `sorry` statements.

Lean 4 formalization of the Poseidon hash function as instantiated in Zcash's Orchard protocol (t=3, R_F=8, R_P=56, α=5, over the Pallas base field 𝔽_p).

## What's formalized

**Key result: `permutation_bijective`** — the full Poseidon permutation on 𝔽_p³ is a bijection.

Proof chain:
1. `alpha_coprime` — gcd(5, p−1) = 1, so x ↦ x⁵ is a bijection on 𝔽_p (Fermat's little theorem).
2. `mds_mul_inv` — the 3×3 Cauchy MDS matrix has an explicit verified inverse.
3. Each full/partial round is a bijection (composition of bijective layers).
4. `applyRounds_bijective` — iterating bijective rounds preserves bijectivity (induction).

Preimage and collision resistance are **not** proven — they are conjectured from algebraic degree bounds, not derivable from bijectivity alone.

The 192 round constants are concrete 𝔽_p values from the Grain LFSR, cross-checked against the Halo 2 reference implementation.

## Axioms

None. All results are proven from first principles; `native_decide` is used for the MDS inverse and coprimality checks (Lean kernel primitive, not an axiom).

## Build

```shell
lake build
```

## Dependencies

Lean 4 (`v4.30.0-rc2`), [Mathlib4](https://github.com/leanprover-community/mathlib4), [pasta-formal](https://github.com/oxarbitrage/pasta-formal).

## References

- [Zcash Protocol Spec §5.4.1.10](https://zips.z.cash/protocol/protocol.pdf)
- [Grassi et al., "Poseidon: A New Hash Function for ZK Proof Systems"](https://eprint.iacr.org/2019/458)
- [pasta-hadeshash](https://github.com/zcash/pasta-hadeshash) — Grain LFSR round constant reference

---

## Part of a series

Six repositories formally verifying the Zcash Orchard cryptographic stack:

| Layer | Repository |
|-------|-----------|
| Curves | [pasta-formal](https://github.com/oxarbitrage/pasta-formal) |
| Hash | [poseidon-formal](https://github.com/oxarbitrage/poseidon-formal) |
| Hash-to-curve | [sinsemilla-formal](https://github.com/oxarbitrage/sinsemilla-formal) |
| Signatures | [redpallas-formal](https://github.com/oxarbitrage/redpallas-formal) |
| Protocol | [orchard-formal](https://github.com/oxarbitrage/orchard-formal) |
| Proof system | [halo2-formal](https://github.com/oxarbitrage/halo2-formal) |
