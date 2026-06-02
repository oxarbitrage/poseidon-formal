import Poseidon.Properties

namespace Poseidon

open Pasta Finset

noncomputable section

/-! # MDS branch number

The branch number of a linear map M is min_{v≠0} (hw(v) + hw(Mv)),
where hw is the Hamming weight (number of nonzero components).
For a t×t MDS matrix, the branch number achieves the maximum t+1.

We prove the Poseidon 3×3 MDS matrix has branch number 4 by showing
all entries and all 2×2 minors are nonzero, then deriving the bound.
-/

/-- Hamming weight: number of nonzero components. -/
def hammingWeight (v : Fin t → Pasta.Fp) : ℕ :=
  (univ.filter (fun i => v i ≠ 0)).card

/-! ## Matrix conditions verified by native_decide -/

theorem mds_entries_ne_zero (i j : Fin t) : mdsMatrix i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp only [mdsMatrix, t] <;> native_decide

theorem mds_minor_ne_zero (i₁ i₂ j₁ j₂ : Fin t)
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    mdsMatrix i₁ j₁ * mdsMatrix i₂ j₂ - mdsMatrix i₁ j₂ * mdsMatrix i₂ j₁ ≠ 0 := by
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp_all [mdsMatrix, t] <;> native_decide

/-! ## Algebraic lemma -/

private theorem det_zero_of_kernel {a b c d x y : Pasta.Fp}
    (hx : x ≠ 0) (h1 : a * x + b * y = 0) (h2 : c * x + d * y = 0) :
    a * d - b * c = 0 := by
  have key : (a * d - b * c) * (x * x) = 0 := by
    linear_combination d * x * h1 - b * x * h2
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · rcases mul_eq_zero.mp h with h | h <;> exact absurd h hx

/-! ## Weight-case helpers -/

private theorem hw1_full_image (v : State) (j : Fin t)
    (hj : v j ≠ 0) (hz : ∀ k, k ≠ j → v k = 0) (i : Fin t) :
    mixLayer v i ≠ 0 := by
  simp only [mixLayer]
  have : ∑ k : Fin t, mdsMatrix i k * v k = mdsMatrix i j * v j := by
    apply Finset.sum_eq_single j
    · intro k _ hk; simp [hz k hk]
    · intro h; exact absurd (mem_univ j) h
  rw [this]
  exact mul_ne_zero (mds_entries_ne_zero i j) hj

private theorem mix_eq_two_terms (v : State) (j₃ j₁ j₂ : Fin t)
    (hv3 : v j₃ = 0) (hj12 : j₁ ≠ j₂) (hj13 : j₁ ≠ j₃) (hj23 : j₂ ≠ j₃)
    (i : Fin t) :
    mixLayer v i = mdsMatrix i j₁ * v j₁ + mdsMatrix i j₂ * v j₂ := by
  simp only [mixLayer]
  have hzero : ∀ k : Fin t, k ≠ j₁ → k ≠ j₂ → mdsMatrix i k * v k = 0 := by
    intro k hk1 hk2
    have : k = j₃ := by
      fin_cases k <;> fin_cases j₁ <;> fin_cases j₂ <;> fin_cases j₃ <;> simp_all
    rw [this, hv3, mul_zero]
  rw [show (∑ k, mdsMatrix i k * v k) =
    mdsMatrix i j₁ * v j₁ + (mdsMatrix i j₂ * v j₂ +
      ∑ k ∈ (univ.erase j₁).erase j₂, mdsMatrix i k * v k) from ?_]
  · congr 1
    rw [show ∑ k ∈ (univ.erase j₁).erase j₂, mdsMatrix i k * v k = 0 from ?_]
    · ring
    · apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_erase] at hk
      have hk2 := hk.1
      rw [Finset.mem_erase] at hk
      exact hzero k hk.2.1 hk2
  · rw [← Finset.add_sum_erase _ _ (mem_univ j₁)]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hj12.symm, mem_univ j₂⟩)]

private theorem hw2_at_most_one_zero (v : State) (j₃ : Fin t) (hv3 : v j₃ = 0)
    (hnz : ∀ k, k ≠ j₃ → v k ≠ 0)
    (i₁ i₂ : Fin t) (hi : i₁ ≠ i₂)
    (hm1 : mixLayer v i₁ = 0) (hm2 : mixLayer v i₂ = 0) : False := by
  -- Find the two nonzero positions j₁, j₂
  obtain ⟨j₁, j₂, hj13, hj23, hj12⟩ : ∃ j₁ j₂ : Fin t, j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧ j₁ ≠ j₂ := by
    fin_cases j₃
    · exact ⟨⟨1, by unfold t; omega⟩, ⟨2, by unfold t; omega⟩, by decide, by decide, by decide⟩
    · exact ⟨⟨0, by unfold t; omega⟩, ⟨2, by unfold t; omega⟩, by decide, by decide, by decide⟩
    · exact ⟨⟨0, by unfold t; omega⟩, ⟨1, by unfold t; omega⟩, by decide, by decide, by decide⟩
  -- Extract the 2×2 equations from the mixLayer = 0 conditions
  have eq1 : mdsMatrix i₁ j₁ * v j₁ + mdsMatrix i₁ j₂ * v j₂ = 0 :=
    (mix_eq_two_terms v j₃ j₁ j₂ hv3 hj12 hj13 hj23 i₁).symm.trans hm1
  have eq2 : mdsMatrix i₂ j₁ * v j₁ + mdsMatrix i₂ j₂ * v j₂ = 0 :=
    (mix_eq_two_terms v j₃ j₁ j₂ hv3 hj12 hj13 hj23 i₂).symm.trans hm2
  -- The 2×2 minor must be zero — contradiction
  exact absurd (det_zero_of_kernel (hnz j₁ hj13) eq1 eq2) (mds_minor_ne_zero _ _ _ _ hi hj12)

/-! ## Main theorem -/

private theorem mixLayer_ne_zero_of_ne_zero (v : State) (hv : v ≠ 0) :
    mixLayer v ≠ 0 := by
  intro hmv
  have h0 : mixLayer (0 : State) = 0 := by ext i; simp [mixLayer]
  exact hv (mixLayer_bijective.1 (hmv.trans h0.symm))

private theorem hw_pos_of_ne_zero (v : Fin t → Pasta.Fp) (hv : v ≠ 0) :
    0 < hammingWeight v := by
  rw [hammingWeight, Finset.card_pos, filter_nonempty_iff]
  by_contra h
  push Not at h
  simp only [Finset.mem_univ, forall_const] at h
  exact hv (funext h)

/-- **The MDS matrix has maximal branch number (t + 1 = 4).**
    For any nonzero input, the sum of nonzero positions in
    input and output is at least 4. -/
theorem mds_branch_number (v : State) (hv : v ≠ 0) :
    hammingWeight v + hammingWeight (mixLayer v) ≥ t + 1 := by
  by_contra hlt
  push Not at hlt
  have hlt3 : hammingWeight v + hammingWeight (mixLayer v) ≤ 3 := by unfold t at hlt; omega
  have hv_pos := hw_pos_of_ne_zero v hv
  have hv_le : hammingWeight v ≤ 3 :=
    (card_filter_le _ _).trans (by decide)
  have hmv_ne := mixLayer_ne_zero_of_ne_zero v hv
  have hmv_pos := hw_pos_of_ne_zero (mixLayer v) hmv_ne
  -- Branch on Hamming weight: hw(v) ∈ {1, 2, 3}
  have cases : hammingWeight v = 1 ∨ hammingWeight v = 2 ∨ hammingWeight v = 3 := by omega
  rcases cases with h1 | h2 | h3
  · -- hw(v) = 1: single nonzero entry → all Mv entries nonzero → hw(Mv) = 3
    have hcard : (univ.filter (fun i => v i ≠ 0)).card = 1 := by
      simp only [hammingWeight] at h1; exact h1
    rw [card_eq_one] at hcard
    obtain ⟨j, hj_eq⟩ := hcard
    have hj : v j ≠ 0 := by
      have := (eq_singleton_iff_unique_mem.mp hj_eq).1
      exact (mem_filter.mp this).2
    have hz : ∀ k, k ≠ j → v k = 0 := by
      intro k hk; by_contra hk'
      have hmem : k ∈ filter (fun i => v i ≠ 0) univ := mem_filter.mpr ⟨mem_univ k, hk'⟩
      rw [hj_eq] at hmem
      exact hk (mem_singleton.mp hmem)
    have hmv3 : hammingWeight (mixLayer v) = 3 := by
      simp only [hammingWeight]
      have h : filter (fun i => mixLayer v i ≠ 0) univ = univ := by
        ext i; simp [hw1_full_image v j hj hz i]
      rw [h, card_univ]; decide
    omega
  · -- hw(v) = 2: one zero entry → at most 1 zero in Mv → hw(Mv) ≥ 2
    have hfilt_eq : (univ.filter (fun i : Fin t => v i = 0)).card = 1 := by
      have hcf := @card_filter_add_card_filter_not (Fin t) univ (fun i => v i ≠ 0) _ _
      simp only [not_not] at hcf
      have huniv : (univ : Finset (Fin t)).card = 3 := by decide
      rw [huniv] at hcf
      simp only [hammingWeight] at h2
      omega
    rw [card_eq_one] at hfilt_eq
    obtain ⟨j₃, hj3_eq⟩ := hfilt_eq
    have hj3 : v j₃ = 0 := by
      have := (eq_singleton_iff_unique_mem.mp hj3_eq).1
      exact (mem_filter.mp this).2
    have hnz : ∀ k, k ≠ j₃ → v k ≠ 0 := by
      intro k hk hk'
      have hmem : k ∈ filter (fun i => v i = 0) univ := mem_filter.mpr ⟨mem_univ k, hk'⟩
      rw [hj3_eq] at hmem
      exact hk (mem_singleton.mp hmem)
    have hmv_card : 1 < (univ.filter (fun i : Fin t => mixLayer v i = 0)).card := by
      have hcf := @card_filter_add_card_filter_not (Fin t) univ (fun i => mixLayer v i ≠ 0) _ _
      simp only [not_not] at hcf
      have huniv : (univ : Finset (Fin t)).card = 3 := by decide
      rw [huniv] at hcf
      simp only [hammingWeight] at h2 hlt3
      omega
    rw [one_lt_card] at hmv_card
    obtain ⟨i₁, hi1, i₂, hi2, hne⟩ := hmv_card
    exact hw2_at_most_one_zero v j₃ hj3 hnz i₁ i₂ hne (mem_filter.mp hi1).2 (mem_filter.mp hi2).2
  · -- hw(v) = 3: sum ≥ 3 + 1 = 4
    omega

end

end Poseidon
