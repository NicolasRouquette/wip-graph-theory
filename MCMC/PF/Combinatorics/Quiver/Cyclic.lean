/-
Copyright (c) 2024 or4nge19. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: or4nge19

Source: https://github.com/or4nge19/MCMC
Commit: 19016763bafc712c840940ed878ff3abfd41e8bb
File: MCMC/PF/Combinatorics/Quiver/Cyclic.lean

This file is adapted from the MCMC project. It contains definitions and theorems
about periodicity, aperiodicity, and cyclic structure in strongly connected quivers.

Note: This is a partial adaptation focusing on the key definitions. The full file
contains more extensive proofs about cyclic partitions and the index of imprimitivity.
-/

import MCMC.PF.Combinatorics.Quiver.Path

namespace Quiver

variable {V : Type*} [Quiver V]

/-!
# Periodicity and Aperiodicity in Quivers

This section defines the concepts of periodicity, the index of imprimitivity,
and aperiodicity for strongly connected quivers, which are essential for
understanding the cyclic structure of irreducible matrices.
-/

/-- A quiver is strongly connected if there is a path between any two vertices.
    Note: Standard graph theory definition allows length 0 paths, but we work
    with nonnegative matrices and require positive length paths. -/
def IsStronglyConnected (G : Quiver V) : Prop :=
  ∀ i j : V, Nonempty { p : Path i j // p.length > 0 }

/-- The set of lengths of cycles at a vertex i.
    We require positive length for cycles relevant to periodicity. -/
def CycleLengths (i : V) : Set ℕ := {k | k > 0 ∧ ∃ p : Path i i, p.length = k}

/-- The period of a vertex i, defined as the greatest common divisor (GCD)
    of the lengths of all cycles passing through i.
    If there are no cycles, the period is defined as 0 (conventionally). -/
noncomputable def period (i : V) : ℕ :=
  sInf {d | ∀ k ∈ CycleLengths i, d ∣ k}

/-- The set of common divisors of all cycle lengths at `i`. -/
def commonDivisorsSet (i : V) : Set ℕ := {d | ∀ k ∈ CycleLengths i, d ∣ k}

lemma one_mem_commonDivisorsSet (i : V) :
    1 ∈ commonDivisorsSet i := by
  intro k _; exact one_dvd _

lemma period_def (i : V) :
    period i = sInf (commonDivisorsSet i) := rfl

/-- `period i` is the least element of the set of common divisors of all cycle lengths at `i`. -/
lemma period_min (i : V) :
    period i ∈ commonDivisorsSet i ∧
      ∀ m ∈ commonDivisorsSet i, period i ≤ m := by
  classical
  let S := commonDivisorsSet i
  have hS_nonempty : S.Nonempty := ⟨1, one_mem_commonDivisorsSet i⟩
  refine ⟨?mem, ?least⟩
  · have : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    simpa [period_def] using this
  · intro m hm
    have : sInf S ≤ m := Nat.sInf_le hm
    simpa [period_def] using this

/-- Basic characterization of `period`: divisibility plus minimality. -/
lemma period_spec (i : V) :
    (∀ k ∈ CycleLengths i, period i ∣ k) ∧
    (∀ m, (∀ k ∈ CycleLengths i, m ∣ k) → period i ≤ m) := by
  classical
  have h := period_min i
  refine ⟨?div, ?min⟩
  · intro k hk
    exact h.1 k hk
  · intro m hm
    exact h.2 m hm

lemma period_mem_commonDivisorsSet (i : V) :
    period i ∈ commonDivisorsSet i :=
  (period_min i).1

lemma period_le_of_commonDivisor (i : V) {m : ℕ}
    (hm : ∀ k ∈ CycleLengths i, m ∣ k) :
    period i ≤ m :=
  (period_spec i).2 _ hm

lemma divides_cycle_length {i : V} {k : ℕ}
    (hk : k ∈ CycleLengths i) :
    period i ∣ k :=
  (period_spec i).1 _ hk

/-- The period divides every cycle length. -/
lemma period_divides_cycle_lengths (i : V) :
    ∀ {k}, k ∈ CycleLengths i → period i ∣ k := by
  intro k hk
  exact (period_spec i).1 k hk

/-- If the set of cycle lengths is non-empty, the period is positive. -/
lemma period_pos_of_nonempty_cycles (i : V) (h_nonempty : (CycleLengths i).Nonempty) :
    period i > 0 := by
  rcases h_nonempty with ⟨k, hk⟩
  have hk_pos : k > 0 := hk.1
  have hdiv : period i ∣ k := (period_spec i).1 k hk
  have hk_ne_zero : k ≠ 0 := (Nat.pos_iff_ne_zero.mp hk_pos)
  rcases hdiv with ⟨t, ht⟩
  have hper_ne_zero : period i ≠ 0 := by
    intro hzero
    have : k = 0 := by simpa [hzero] using ht
    exact hk_ne_zero this
  exact Nat.pos_of_ne_zero hper_ne_zero

/-- The index of imprimitivity (h) of a strongly connected quiver,
    defined as the common period of its vertices. Requires Fintype and Nonempty
    to select an arbitrary vertex. -/
noncomputable def index_of_imprimitivity [Fintype V] [Nonempty V] (G : Quiver V) : ℕ :=
  period (Classical.arbitrary V)

/-- A strongly connected quiver is aperiodic if its index of imprimitivity is 1. -/
def IsAperiodic [Fintype V] [Nonempty V] (G : Quiver V) : Prop :=
  index_of_imprimitivity G = 1

/-! # Cyclic Structure and Frobenius Normal Form -/

/-- A cyclic partition of the vertices with period h.
    The partition is represented by a map from V to Fin h.
    Edges only go from one class to the next one cyclically.
    We define the successor within `Fin h` by modular addition of 1 (staying in `Fin h`). -/
def IsCyclicPartition {h : ℕ} (h_pos : h > 0) (partition : V → Fin h) : Prop :=
  let succMod : Fin h → Fin h := fun x => ⟨(x.val + 1) % h, Nat.mod_lt _ h_pos⟩
  ∀ i j : V, Nonempty (i ⟶ j) → partition j = succMod (partition i)

/-- If the right factor of a composed path has positive length, the composed cycle at `i`
    belongs to `CycleLengths i`. -/
lemma mem_CycleLengths_of_comp_right {i v : V}
    (p : Path i v) (s : Path v i) (hs_pos : 0 < s.length) :
    (p.comp s).length ∈ CycleLengths i := by
  have hpos : 0 < (p.comp s).length := by
    have hle : s.length ≤ p.length + s.length := by
      have := Nat.le_add_left s.length p.length
      simp
    exact lt_of_lt_of_le hs_pos (by simp [Path.length_comp])
  exact ⟨hpos, ⟨p.comp s, rfl⟩⟩

/-- Variant: if we first extend a path by a single edge using `cons` and then compose on the right
    with a positive-length path back to the base, we still get a cycle length in `CycleLengths`. -/
lemma mem_CycleLengths_of_cons_comp_right {i v w : V}
    (p : Path i v) (e : v ⟶ w) (s : Path w i) (hs_pos : 0 < s.length) :
    (((p.cons e).comp s).length) ∈ CycleLengths i :=
  mem_CycleLengths_of_comp_right (p := p.cons e) (s := s) hs_pos

end Quiver
