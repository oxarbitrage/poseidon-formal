import Poseidon.Spec
import Mathlib.Algebra.MvPolynomial.Degrees

namespace Poseidon

open Pasta MvPolynomial Finset

noncomputable section

/-! # Algebraic degree growth

Each component of the Poseidon state, viewed as a multivariate polynomial
in the input variables, has its total degree multiplied by at most 5 each
round (the S-box exponent). After k rounds the degree is at most 5ᵏ.
This exponential growth is the primary defense against interpolation
attacks, which require ≥ degree + 1 evaluation queries.

Reference: Grassi et al. §5.2, "Interpolation Attacks".
-/

/-- A symbolic state: each component is a multivariate polynomial
    in t = 3 input variables over Fp. -/
abbrev SymState := Fin t → MvPolynomial (Fin t) Pasta.Fp

/-- The initial symbolic state: formal variables X₀, X₁, X₂. -/
def symInitial : SymState := fun i => X i

/-- Symbolic add-round-constants. -/
def symAddRC (r : Fin totalRounds) (s : SymState) : SymState :=
  fun i => s i + C (roundConstants r i)

/-- Symbolic full S-box layer. -/
def symSboxFull (s : SymState) : SymState := fun i => s i ^ 5

/-- Symbolic partial S-box layer. -/
def symSboxPartial (s : SymState) : SymState :=
  fun i => if i.val = 0 then s i ^ 5 else s i

/-- Symbolic MDS layer. -/
def symMix (s : SymState) : SymState :=
  fun i => ∑ j : Fin t, C (mdsMatrix i j) * s j

/-- Symbolic full round. -/
def symFullRound (r : Fin totalRounds) (s : SymState) : SymState :=
  symMix (symSboxFull (symAddRC r s))

/-- Symbolic partial round. -/
def symPartialRound (r : Fin totalRounds) (s : SymState) : SymState :=
  symMix (symSboxPartial (symAddRC r s))

/-- Iterate symbolic rounds (mirrors `applyRounds`). -/
def symApplyRounds (roundFn : Fin totalRounds → SymState → SymState)
    (start count : ℕ) (s : SymState) : SymState :=
  match count with
  | 0 => s
  | n + 1 =>
    if h : start < totalRounds then
      symApplyRounds roundFn (start + 1) n (roundFn ⟨start, h⟩ s)
    else s

/-! ## Component degree bounds -/

/-- Every component has total degree ≤ d. -/
def degBound (s : SymState) (d : ℕ) : Prop :=
  ∀ i : Fin t, (s i).totalDegree ≤ d

theorem symInitial_degBound : degBound symInitial 1 := by
  intro i; simp [symInitial]

theorem symAddRC_degBound (r : Fin totalRounds) {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symAddRC r s) d := by
  intro i; simp only [symAddRC]
  exact (totalDegree_add _ _).trans (max_le (hd i) (by simp [totalDegree_C]))

private theorem totalDegree_C_mul_le (a : Pasta.Fp)
    (p : MvPolynomial (Fin t) Pasta.Fp) :
    (C a * p).totalDegree ≤ p.totalDegree :=
  (totalDegree_mul _ _).trans (by simp [totalDegree_C])

theorem symSboxFull_degBound {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symSboxFull s) (5 * d) := by
  intro i; simp only [symSboxFull]
  exact (totalDegree_pow _ 5).trans (Nat.mul_le_mul_left 5 (hd i))

theorem symSboxPartial_degBound {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symSboxPartial s) (5 * d) := by
  intro i; simp only [symSboxPartial]
  split
  · exact (totalDegree_pow _ 5).trans (Nat.mul_le_mul_left 5 (hd i))
  · exact (hd i).trans (Nat.le_mul_of_pos_left d (by omega))

theorem symMix_degBound {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symMix s) d := by
  intro i; simp only [symMix]
  exact (totalDegree_finsetSum _ _).trans
    (Finset.sup_le fun j _ => (totalDegree_C_mul_le _ _).trans (hd j))

/-! ## Round degree bounds -/

theorem symFullRound_degBound (r : Fin totalRounds) {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symFullRound r s) (5 * d) :=
  symMix_degBound (symSboxFull_degBound (symAddRC_degBound r hd))

theorem symPartialRound_degBound (r : Fin totalRounds) {s : SymState} {d : ℕ}
    (hd : degBound s d) : degBound (symPartialRound r s) (5 * d) :=
  symMix_degBound (symSboxPartial_degBound (symAddRC_degBound r hd))

/-! ## Iterated degree growth -/

theorem symApplyRounds_degBound
    {roundFn : Fin totalRounds → SymState → SymState}
    (hround : ∀ (r : Fin totalRounds) {s d}, degBound s d → degBound (roundFn r s) (5 * d))
    (start count : ℕ) {s : SymState} {d : ℕ} (hd : degBound s d) :
    degBound (symApplyRounds roundFn start count s) (5 ^ count * d) := by
  induction count generalizing start s d with
  | zero => simpa [symApplyRounds] using hd
  | succ n ih =>
    simp only [symApplyRounds]
    split
    · convert ih (start + 1) (hround _ hd) using 1; ring
    · intro i; exact (hd i).trans (Nat.le_mul_of_pos_left d (by positivity))

/-! ## Main theorems -/

/-- After k full rounds starting from initial variables, degree ≤ 5ᵏ. -/
theorem degree_after_full_rounds (k : ℕ) :
    degBound (symApplyRounds symFullRound 0 k symInitial) (5 ^ k) := by
  have := symApplyRounds_degBound symFullRound_degBound 0 k symInitial_degBound
  simpa using this

/-- After k partial rounds starting from initial variables, degree ≤ 5ᵏ. -/
theorem degree_after_partial_rounds (k : ℕ) :
    degBound (symApplyRounds symPartialRound 0 k symInitial) (5 ^ k) := by
  have := symApplyRounds_degBound symPartialRound_degBound 0 k symInitial_degBound
  simpa using this

/-- The full Poseidon permutation (4 full + 56 partial + 4 full rounds)
    has algebraic degree ≤ 5⁶⁴ in every output component.
    Interpolation attacks therefore require ≥ 5⁶⁴ + 1 evaluation queries. -/
theorem permutation_degree_bound :
    degBound
      (let s₁ := symApplyRounds symFullRound 0 (R_F / 2) symInitial
       let s₂ := symApplyRounds symPartialRound (R_F / 2) R_P s₁
       symApplyRounds symFullRound (R_F / 2 + R_P) (R_F / 2) s₂)
      (5 ^ totalRounds) := by
  have h1 := symApplyRounds_degBound symFullRound_degBound
    0 (R_F / 2) symInitial_degBound
  have h2 := symApplyRounds_degBound symPartialRound_degBound
    (R_F / 2) R_P h1
  have h3 := symApplyRounds_degBound symFullRound_degBound
    (R_F / 2 + R_P) (R_F / 2) h2
  convert h3 using 1

end

end Poseidon
