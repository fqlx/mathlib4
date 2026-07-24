/-
Copyright (c) 2026 Alexander Benjamin Worth Burns. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Benjamin Worth Burns
-/
module

public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Private prime divisors of affine forms

This file shows that a finite family of pairwise nonproportional affine forms with positive
leading coefficients admits arbitrarily many pairwise distinct private prime divisors.

The main result, `Nat.exists_private_prime_divisors_affine`, chooses one prime for each member of
an arbitrary finite label type. Each prime divides the form selected by its label and none of the
other forms. The same primes work for arbitrarily large values of the common parameter.
-/

@[expose] public section

open scoped BigOperators
open scoped Function

namespace Nat

/-- A finite family of pairwise nonproportional affine forms with positive leading coefficients
can simultaneously be given any finite collection of pairwise distinct private prime divisors.

The forms are `t ↦ c i * t + d i`, with natural coefficients. The hypothesis `hdet` says that the
determinant `c i * d j - c j * d i` is nonzero whenever `i ≠ j`.

The map `index` assigns each prime label to an affine form. The resulting primes exceed `N`, avoid
`F`, and the same primes work for arbitrarily large parameters `t`. Taking
`κ := Σ i, Fin (m i)` and `index := Sigma.fst` requests `m i` primes for each form `i`. -/
theorem exists_private_prime_divisors_affine
    {ι κ : Type*} [Finite ι] [Finite κ]
    (c d : ι → ℕ) (hc : ∀ i, 0 < c i)
    (hdet : ∀ i j, i ≠ j →
      (c i : ℤ) * d j - (c j : ℤ) * d i ≠ 0)
    (index : κ → ι) (N : ℕ) (F : Finset ℕ) :
    ∃ q : κ → ℕ,
      Function.Injective q ∧
      (∀ b, (q b).Prime ∧ N < q b ∧ q b ∉ F) ∧
      ∀ B, ∃ t, B < t ∧
        ∀ b, q b ∣ c (index b) * t + d (index b) ∧
          ∀ j, j ≠ index b → ¬q b ∣ c j * t + d j := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  let det (i j : ι) : ℤ := (c i : ℤ) * d j - (c j : ℤ) * d i
  let K :=
    max N <| max (F.sup id) <|
      max (Finset.univ.sup c) (Finset.univ.sup fun i ↦ Finset.univ.sup fun j ↦ (det i j).natAbs)
  let e := Fintype.equivFin κ
  let q : κ → ℕ := fun b ↦ nth Prime (K + e b)
  have hq_prime (b : κ) : (q b).Prime := by
    simp [q, prime_nth_prime]
  have hKq (b : κ) : K < q b := by
    have h := add_two_le_nth_prime (K + e b)
    dsimp only [q]
    omega
  have hq_injective : Function.Injective q := by
    intro b₁ b₂ h
    apply e.injective
    apply Fin.ext
    exact Nat.add_left_cancel <| (nth_strictMono infinite_setOfPred_prime).injective h
  have hq_pairwise : Set.Pairwise (↑(Finset.univ : Finset κ) : Set κ) (Coprime on q) := by
    intro b₁ _ b₂ _ hne
    change (q b₁).Coprime (q b₂)
    rw [coprime_primes (hq_prime b₁) (hq_prime b₂)]
    exact hq_injective.ne hne
  have hq_ne_zero (b : κ) : q b ≠ 0 := (hq_prime b).ne_zero
  let r : κ → ℕ := fun b ↦
    (-(d (index b) : ZMod (q b)) * (c (index b) : ZMod (q b))⁻¹).val
  have hr (b : κ) : q b ∣ c (index b) * r b + d (index b) := by
    have hc_lt : c (index b) < q b := by
      apply lt_of_le_of_lt _ (hKq b)
      exact (Finset.le_sup (f := c) (Finset.mem_univ (index b))).trans
        (le_max_left _ _ |>.trans <| le_max_right _ _ |>.trans <| le_max_right _ _)
    have hcq : (c (index b)).Coprime (q b) :=
      (coprime_of_lt_prime (hc (index b)).ne' hc_lt (hq_prime b)).symm
    letI : NeZero (q b) := ⟨hq_ne_zero b⟩
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [show (r b : ZMod (q b)) =
        -(d (index b) : ZMod (q b)) * (c (index b) : ZMod (q b))⁻¹ by
      simp [r]]
    calc
      (c (index b) : ZMod (q b)) *
            (-(d (index b) : ZMod (q b)) * (c (index b) : ZMod (q b))⁻¹) +
          d (index b) =
          -(d (index b) : ZMod (q b)) *
            ((c (index b) : ZMod (q b)) * (c (index b) : ZMod (q b))⁻¹) +
              d (index b) := by ring
      _ = 0 := by rw [ZMod.coe_mul_inv_eq_one _ hcq]; simp
  let z := chineseRemainderOfFinset r q Finset.univ
    (fun b _ ↦ hq_ne_zero b) hq_pairwise
  refine ⟨q, hq_injective, ?_, ?_⟩
  · intro b
    refine ⟨hq_prime b, ?_, ?_⟩
    · exact (le_max_left N _).trans_lt (hKq b)
    · intro hbF
      have hb_le : q b ≤ K := (Finset.le_sup (f := id) hbF).trans <|
        (le_max_left _ _).trans (le_max_right _ _)
      exact (Nat.not_le_of_lt (hKq b)) hb_le
  · intro B
    let Q := ∏ b : κ, q b
    let t := z + (B + 1) * Q
    have hQ_pos : 0 < Q := Finset.prod_pos fun b _ ↦ (hq_prime b).pos
    have hB_mul : B + 1 ≤ (B + 1) * Q := Nat.le_mul_of_pos_right _ hQ_pos
    refine ⟨t, by dsimp only [t]; omega, ?_⟩
    intro b
    have hqQ : q b ∣ Q := Finset.dvd_prod_of_mem q (Finset.mem_univ b)
    have htz : t ≡ z [MOD q b] := by
      apply Nat.add_modEq_left_iff.mpr
      exact dvd_mul_of_dvd_right hqQ (B + 1)
    have htr : t ≡ r b [MOD q b] :=
      htz.trans (z.property b (Finset.mem_univ b))
    constructor
    · exact modEq_zero_iff_dvd.mp <|
        (htr.mul_left (c (index b))).add_right (d (index b)) |>.trans
          (hr b).modEq_zero_nat
    · intro j hji hj
      have hb : q b ∣ c (index b) * t + d (index b) := modEq_zero_iff_dvd.mp <|
        (htr.mul_left (c (index b))).add_right (d (index b)) |>.trans
          (hr b).modEq_zero_nat
      have hb_int :
          (q b : ℤ) ∣ (c (index b) : ℤ) * t + d (index b) := by
        exact_mod_cast hb
      have hj_int :
          (q b : ℤ) ∣ (c j : ℤ) * t + d j := by
        exact_mod_cast hj
      have hdet_dvd : (q b : ℤ) ∣ det (index b) j := by
        have h₁ := dvd_mul_of_dvd_right hj_int (c (index b) : ℤ)
        have h₂ := dvd_mul_of_dvd_right hb_int (c j : ℤ)
        change (q b : ℤ) ∣
          (c (index b) : ℤ) * d j - (c j : ℤ) * d (index b)
        rw [show (c (index b) : ℤ) * d j - (c j : ℤ) * d (index b) =
          (c (index b) : ℤ) * ((c j : ℤ) * t + d j) -
            (c j : ℤ) * ((c (index b) : ℤ) * t + d (index b)) by ring]
        exact Int.dvd_sub h₁ h₂
      have hdet_le : (det (index b) j).natAbs ≤ K := by
        have h₁ : (det (index b) j).natAbs ≤
            Finset.univ.sup fun j ↦ (det (index b) j).natAbs :=
          Finset.le_sup (f := fun j ↦ (det (index b) j).natAbs) (Finset.mem_univ j)
        have h₂ : (Finset.univ.sup fun j ↦ (det (index b) j).natAbs) ≤
            Finset.univ.sup fun i ↦ Finset.univ.sup fun j ↦ (det i j).natAbs :=
          Finset.le_sup (f := fun i ↦ Finset.univ.sup fun j ↦ (det i j).natAbs)
            (Finset.mem_univ (index b))
        exact (h₁.trans h₂).trans <|
          (le_max_right _ _).trans <| (le_max_right _ _).trans (le_max_right _ _)
      have hq_le :=
        Int.natAbs_le_of_dvd_ne_zero hdet_dvd (hdet (index b) j hji.symm)
      simp only [Int.natAbs_natCast] at hq_le
      exact (Nat.not_le_of_lt (hKq b)) (hq_le.trans hdet_le)

end Nat
