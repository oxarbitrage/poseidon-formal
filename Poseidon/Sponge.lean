import Poseidon.Properties

namespace Poseidon

open Pasta Finset

noncomputable section

/-! # Sponge-level properties

We decompose `poseidonHash` into the standard sponge phases —
absorb, permute, squeeze — and prove properties connecting
`permutation_bijective` to hash-level security guarantees:

1. **Absorption injectivity**: distinct inputs yield distinct internal states
2. **Domain separation**: different capacity values yield different states
3. **Capacity hiding**: the rate output does not determine the full state
-/

/-! ## Sponge decomposition -/

/-- Embed two field elements into the sponge state with a given capacity value. -/
def absorbWith (c : Pasta.Fp) (x y : Pasta.Fp) : State :=
  fun i => if i.val = 0 then x else if i.val = 1 then y else c

/-- Absorb: embed inputs into the sponge state with the standard Orchard capacity. -/
def absorb (x y : Pasta.Fp) : State := absorbWith initialCapacity x y

/-- Squeeze: extract the rate output (first element) from the post-permutation state. -/
def squeeze (s : State) : Pasta.Fp := s ⟨0, by unfold t; omega⟩

/-- `poseidonHash` decomposes as squeeze ∘ permutation ∘ absorb. -/
theorem poseidonHash_eq (x y : Pasta.Fp) :
    poseidonHash x y = squeeze (permutation (absorb x y)) := by
  unfold poseidonHash absorb absorbWith squeeze
  rfl

/-! ## Absorption injectivity -/

/-- Absorption with any fixed capacity is injective:
    distinct input pairs produce distinct sponge states. -/
theorem absorbWith_injective (c : Pasta.Fp) :
    Function.Injective (fun p : Pasta.Fp × Pasta.Fp => absorbWith c p.1 p.2) := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
  have hx : x₁ = x₂ := by
    have := congr_fun h ⟨0, by unfold t; omega⟩
    simp only [absorbWith] at this
    simpa using this
  have hy : y₁ = y₂ := by
    have := congr_fun h ⟨1, by unfold t; omega⟩
    simp only [absorbWith] at this
    simpa using this
  exact Prod.ext hx hy

/-- Absorption with the standard capacity is injective. -/
theorem absorb_injective :
    Function.Injective (fun p : Pasta.Fp × Pasta.Fp => absorb p.1 p.2) :=
  absorbWith_injective initialCapacity

/-- The absorb → permute pipeline is injective: distinct inputs produce
    distinct post-permutation states. This is the formal content of
    "determinism" — no information is lost during absorption and permutation. -/
theorem absorb_permute_injective :
    Function.Injective (fun p : Pasta.Fp × Pasta.Fp =>
      permutation (absorb p.1 p.2)) :=
  permutation_bijective.1.comp absorb_injective

/-! ## Domain separation -/

/-- Different capacity values produce different post-permutation states,
    even for identical rate inputs. This is the formal basis for
    constant-input-length domain separation in the Poseidon sponge:
    hashing a 2-element message (capacity = 2⁶⁵) can never collide with
    a hypothetical 3-element variant that uses a different capacity. -/
theorem domain_separation {c₁ c₂ : Pasta.Fp} (hc : c₁ ≠ c₂)
    (x y : Pasta.Fp) :
    permutation (absorbWith c₁ x y) ≠ permutation (absorbWith c₂ x y) := by
  intro h
  apply hc
  have := congr_fun (permutation_bijective.1 h) ⟨2, by unfold t; omega⟩
  simp [absorbWith] at this
  exact this

/-! ## Capacity hiding -/

/-- For any rate output value `z`, there exist at least two distinct
    internal states whose post-permutation rate output equals `z`.
    This means observing the hash output does not uniquely determine
    the full internal state — the capacity portion remains hidden.

    Proof: construct two target states that agree on index 0 (= z) but
    differ on index 1. Since the permutation is bijective, their
    distinct preimages both map to rate output `z`. -/
theorem capacity_hiding (z : Pasta.Fp) :
    ∃ s₁ s₂ : State, s₁ ≠ s₂ ∧
      squeeze (permutation s₁) = z ∧ squeeze (permutation s₂) = z := by
  obtain ⟨s₁, hs₁⟩ := permutation_bijective.2
    (show State from fun i => if i.val = 0 then z else 0)
  obtain ⟨s₂, hs₂⟩ := permutation_bijective.2
    (show State from fun i => if i.val = 0 then z else 1)
  refine ⟨s₁, s₂, ?_, ?_, ?_⟩
  · intro heq
    have hperm : permutation s₁ = permutation s₂ := congrArg permutation heq
    rw [hs₁, hs₂] at hperm
    have h1 := congr_fun hperm ⟨1, by unfold t; omega⟩
    simp at h1
  · simp only [squeeze, hs₁]; simp
  · simp only [squeeze, hs₂]; simp

end

end Poseidon
