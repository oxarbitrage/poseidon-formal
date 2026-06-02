import Poseidon.Properties
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.ComputeDegree

namespace Poseidon

open Pasta Polynomial Finset

noncomputable section

/-! # S-box differential uniformity

The S-box `x ↦ x⁵` has differential uniformity ≤ 4: for any nonzero
input difference `a`, the equation `(x+a)⁵ - x⁵ = b` has at most 4
solutions. This is the primary defense against differential cryptanalysis.

Proof: the equation is a degree-4 polynomial in x (the x⁵ terms cancel),
and a polynomial of degree d over a field has at most d roots.
-/

private def diffPoly (a b : Pasta.Fp) : Polynomial Pasta.Fp :=
  C (5 * a) * X ^ 4 + C (10 * a ^ 2) * X ^ 3 +
  C (10 * a ^ 3) * X ^ 2 + C (5 * a ^ 4) * X + C (a ^ 5 - b)

private theorem diffPoly_eval (a b x : Pasta.Fp) :
    (diffPoly a b).eval x = (x + a) ^ 5 - x ^ 5 - b := by
  simp [diffPoly]; ring

private theorem diffPoly_natDegree (a b : Pasta.Fp) :
    (diffPoly a b).natDegree ≤ 4 := by
  unfold diffPoly; compute_degree!

private theorem diffPoly_ne_zero (a b : Pasta.Fp) (ha : a ≠ 0) :
    diffPoly a b ≠ 0 := by
  intro hp
  have h0 := diffPoly_eval a b 0
  have ha' := diffPoly_eval a b a
  rw [hp, eval_zero] at h0 ha'
  have hb : b = a ^ 5 := by linear_combination h0
  have h30 : (30 : Pasta.Fp) * a ^ 5 = 0 := by linear_combination -ha' + hb
  exact absurd h30 (mul_ne_zero (by native_decide : (30 : Pasta.Fp) ≠ 0) (pow_ne_zero 5 ha))

/-- **S-box differential uniformity ≤ 4.**
    For any nonzero difference `a` and any target `b`, the equation
    `sbox(x + a) - sbox(x) = b` has at most 4 solutions over Fp. -/
theorem sbox_differential_uniformity (a : Pasta.Fp) (ha : a ≠ 0) (b : Pasta.Fp) :
    (univ.filter (fun x : Pasta.Fp => sbox (x + a) - sbox x = b)).card ≤ 4 := by
  have hne := diffPoly_ne_zero a b ha
  have hsub : univ.filter (fun x => sbox (x + a) - sbox x = b) ⊆
      (diffPoly a b).roots.toFinset := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, sbox] at hx
    have hroot : (diffPoly a b).IsRoot x := by
      show (diffPoly a b).eval x = 0
      rw [diffPoly_eval]; linear_combination hx
    exact Multiset.mem_toFinset.mpr ((mem_roots hne).mpr hroot)
  calc (univ.filter _).card
      ≤ (diffPoly a b).roots.toFinset.card := card_le_card hsub
    _ ≤ Multiset.card (diffPoly a b).roots :=
        Multiset.card_le_card (Multiset.dedup_le _)
    _ ≤ (diffPoly a b).natDegree := card_roots' _
    _ ≤ 4 := diffPoly_natDegree a b

end

end Poseidon
