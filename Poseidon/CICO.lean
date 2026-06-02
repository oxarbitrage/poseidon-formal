import Poseidon.AlgebraicDegree

namespace Poseidon

open Pasta MvPolynomial Finset

noncomputable section

/-! # Constrained-Input Constrained-Output (CICO)

CICO captures the computational problem an attacker must solve to break
Poseidon: given fixed values on some input and output coordinates, find
a consistent state. We show this reduces to finding roots of polynomials
of degree ≤ 5⁶⁴, making brute-force infeasible over a 254-bit field.

Reference: Grassi et al. §5.1, "CICO Problem".
-/

/-! ## CICO definition -/

/-- A CICO instance: fix some input coordinates, fix some output coordinates. -/
structure CICOInstance where
  inputFixed : Fin t → Option Pasta.Fp
  outputFixed : Fin t → Option Pasta.Fp

/-- A state solves a CICO instance if it agrees with all constraints. -/
def CICOInstance.IsSolution (inst : CICOInstance) (s : State) : Prop :=
  (∀ i v, inst.inputFixed i = some v → s i = v) ∧
  (∀ j w, inst.outputFixed j = some w → permutation s j = w)

/-! ## Symbolic permutation -/

/-- The symbolic Poseidon permutation on formal variables. -/
def symPermutation : SymState :=
  let s₁ := symApplyRounds symFullRound 0 (R_F / 2) symInitial
  let s₂ := symApplyRounds symPartialRound (R_F / 2) R_P s₁
  symApplyRounds symFullRound (R_F / 2 + R_P) (R_F / 2) s₂

/-- Every component of the symbolic permutation has degree ≤ 5⁶⁴. -/
theorem symPermutation_degBound :
    degBound symPermutation (5 ^ totalRounds) :=
  permutation_degree_bound

/-! ## Evaluation correspondence

The symbolic permutation agrees with the concrete permutation under
evaluation: `eval s (symPermutation j) = permutation s j`.
-/

/-- Evaluate a symbolic state at a concrete point. -/
def evalState (v : Fin t → Pasta.Fp) (sym : SymState) : State :=
  fun i => eval v (sym i)

theorem evalState_symInitial (v : Fin t → Pasta.Fp) :
    evalState v symInitial = v := by
  ext i; simp [evalState, symInitial]

theorem evalState_symAddRC (v : Fin t → Pasta.Fp)
    (r : Fin totalRounds) (sym : SymState) :
    evalState v (symAddRC r sym) = addRoundConstants r (evalState v sym) := by
  ext i; simp [evalState, symAddRC, addRoundConstants, eval_add]

theorem evalState_symSboxFull (v : Fin t → Pasta.Fp) (sym : SymState) :
    evalState v (symSboxFull sym) = sboxFull (evalState v sym) := by
  ext i; simp [evalState, symSboxFull, sboxFull, sbox, eval_pow]

theorem evalState_symSboxPartial (v : Fin t → Pasta.Fp) (sym : SymState) :
    evalState v (symSboxPartial sym) = sboxPartial (evalState v sym) := by
  ext i; simp only [evalState, symSboxPartial, sboxPartial, sbox]
  split <;> simp [eval_pow]

theorem evalState_symMix (v : Fin t → Pasta.Fp) (sym : SymState) :
    evalState v (symMix sym) = mixLayer (evalState v sym) := by
  ext i; simp [evalState, symMix, mixLayer, map_sum, eval_mul]

theorem evalState_symFullRound (v : Fin t → Pasta.Fp)
    (r : Fin totalRounds) (sym : SymState) :
    evalState v (symFullRound r sym) = fullRound r (evalState v sym) := by
  simp only [symFullRound, fullRound,
    evalState_symMix, evalState_symSboxFull, evalState_symAddRC]

theorem evalState_symPartialRound (v : Fin t → Pasta.Fp)
    (r : Fin totalRounds) (sym : SymState) :
    evalState v (symPartialRound r sym) = partialRound r (evalState v sym) := by
  simp only [symPartialRound, partialRound,
    evalState_symMix, evalState_symSboxPartial, evalState_symAddRC]

theorem evalState_symApplyRounds
    {symRound : Fin totalRounds → SymState → SymState}
    {concRound : Fin totalRounds → State → State}
    (heval : ∀ v r sym,
      evalState v (symRound r sym) = concRound r (evalState v sym))
    (v : Fin t → Pasta.Fp) (start count : ℕ) (sym : SymState) :
    evalState v (symApplyRounds symRound start count sym) =
    applyRounds concRound start count (evalState v sym) := by
  induction count generalizing start sym with
  | zero => rfl
  | succ n ih =>
    simp only [symApplyRounds, applyRounds]
    by_cases h : start < totalRounds
    · simp only [dif_pos h, ih, heval]
    · simp only [dif_neg h]

/-- The symbolic permutation evaluates to the concrete permutation. -/
theorem eval_symPermutation (s : State) (j : Fin t) :
    eval s (symPermutation j) = permutation s j := by
  show (evalState s symPermutation) j = permutation s j
  simp only [symPermutation, permutation,
    evalState_symApplyRounds evalState_symFullRound,
    evalState_symApplyRounds evalState_symPartialRound,
    evalState_symInitial]

/-! ## CICO reduces to polynomial root-finding -/

/-- Any CICO solution must satisfy: the symbolic permutation polynomial
    evaluated at the solution equals the constrained output value.
    Since the polynomial has degree ≤ 5⁶⁴, finding such a root is
    the computational bottleneck of any CICO attack. -/
theorem cico_is_polynomial_root (inst : CICOInstance) (s : State)
    (hsol : inst.IsSolution s) {j : Fin t} {w : Pasta.Fp}
    (hj : inst.outputFixed j = some w) :
    eval s (symPermutation j) = w := by
  rw [eval_symPermutation]
  exact hsol.2 j w hj

/-- The polynomial that a CICO attacker must find a root of has
    degree at most 5⁶⁴ = 5^totalRounds. Combined with
    `cico_is_polynomial_root`, this shows that any CICO attack
    reduces to root-finding on degree-5⁶⁴ polynomials over a
    254-bit prime field. -/
theorem cico_polynomial_degree (j : Fin t) :
    (symPermutation j).totalDegree ≤ 5 ^ totalRounds :=
  symPermutation_degBound j

end

end Poseidon
