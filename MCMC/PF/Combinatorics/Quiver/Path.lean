/-
Copyright (c) 2024 or4nge19. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: or4nge19

Source: https://github.com/or4nge19/MCMC
Commit: 19016763bafc712c840940ed878ff3abfd41e8bb
File: MCMC/PF/Combinatorics/Quiver/Path.lean

This file is adapted from the MCMC project for use in proving graph-theoretic
properties about Quiver paths. The original file contains extensive utilities
for path manipulation, decomposition, and simplicity proofs.

Key lemmas used:
- `length_lt_card_of_isStrictlySimple`: Simple paths have length < vertex count
- `isStrictlySimple_of_shortest`: Shortest paths are simple
- Various path decomposition and cycle extraction lemmas
-/

import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

set_option maxHeartbeats 400000

open List

namespace Quiver.Path

variable {V : Type*} [Quiver V]

/-! ## Vertex utilities -/

/-- Vertices of a path are always non-empty -/
lemma vertices_nonempty' {a b : V} (p : Path a b) : p.vertices.length > 0 := by
  rw [vertices_length]; omega

lemma vertices_nonempty {a b : V} (p : Path a b) : p.vertices ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, vertices_length]; omega

/-- The head of the vertices list is the start vertex. -/
@[simp]
lemma vertices_head_eq_start {a b : V} (p : Path a b) :
    p.vertices.head (vertices_nonempty p) = a := by
  induction p with
  | nil => simp only [vertices_nil, List.head_cons]
  | cons p' _ ih =>
    simp only [vertices_cons, List.concat_eq_append]
    have : p'.vertices ≠ [] := vertices_nonempty p'
    simp only [List.head_append_of_ne_nil this]
    exact ih

/-- The last element of the vertices list is the end vertex. -/
@[simp]
lemma vertices_getLast_eq_end {a b : V} (p : Path a b) :
    p.vertices.getLast (vertices_nonempty p) = b :=
  vertices_getLast p (vertices_nonempty p)

/-! ## Path decomposition -/

lemma cons_eq_comp_toPath {a b c : V} (p : Path a b) (e : b ⟶ c) :
    p.cons e = p.comp e.toPath := rfl

/-- Every non-empty path can be decomposed as an initial path plus a final edge. -/
lemma path_decomposition_last_edge {a b : V} (p : Path a b) (h : p.length > 0) :
    ∃ (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e := by
  cases p with | nil => simp at h | cons p' e => exact ⟨_, p', e, rfl⟩

/-- Given a path `p : Path a b` and an index `n ≤ p.length`,
    we can split `p = p₁.comp p₂` with `p₁.length = n`. -/
theorem exists_decomp_at_length {a b : V} (p : Path a b) {n : ℕ} (hn : n ≤ p.length) :
    ∃ (c : V) (p₁ : Path a c) (p₂ : Path c b),
      p = p₁.comp p₂ ∧ p₁.length = n := by
  induction p generalizing n with
  | nil =>
      have h : n = 0 := by simp_all only [length_nil, nonpos_iff_eq_zero]
      subst h
      exact ⟨a, Path.nil, Path.nil, by simp only [comp_nil], rfl⟩
  | cons p' e ih =>
      rename_i c
      rw [length_cons] at hn
      rcases (Nat.le_succ_iff).1 hn with h | h
      · rcases ih h with ⟨d, p₁, p₂, hp, hl⟩
        refine ⟨d, p₁, p₂.cons e, ?_, hl⟩
        simp only [hp, cons_eq_comp_toPath, comp_assoc]
      · subst h
        refine ⟨c, p'.cons e, Path.nil, ?_, ?_⟩
        · simp only [cons_eq_comp_toPath, comp_nil]
        · simp only [cons_eq_comp_toPath, length_comp, length_toPath, Nat.succ_eq_add_one]

theorem exists_decomp_of_mem_vertices {a b v : V} (p : Path a b)
    (h : v ∈ p.vertices) : ∃ (p₁ : Path a v) (p₂ : Path v b), p = p₁.comp p₂ := by
  obtain ⟨l₁, l₂, hv⟩ := List.exists_mem_split h
  have h_len : l₁.length ≤ p.length := by
    have : p.vertices.length = p.length + 1 := vertices_length p
    have : l₁.length < p.vertices.length := by
      rw [hv, List.length_append, List.length_cons]
      omega
    omega
  obtain ⟨c, p₁, p₂, hp, hl⟩ := exists_decomp_at_length p h_len
  suffices hvc : v = c by
    subst hvc
    exact ⟨p₁, p₂, hp⟩
  have h_verts : p.vertices = p₁.vertices.dropLast ++ p₂.vertices := by
    rw [hp, vertices_comp]
  have h_l1_len : l₁.length = p₁.vertices.dropLast.length := by
    have : p₁.vertices.length = p₁.length + 1 := vertices_length p₁
    simp only [List.length_dropLast, this, hl, add_tsub_cancel_right]
  have h_l1_eq : l₁ = p₁.vertices.dropLast := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    exact List.append_inj_left this h_l1_len
  have h_v_l2 : v :: l₂ = p₂.vertices := by
    have : l₁ ++ v :: l₂ = p₁.vertices.dropLast ++ p₂.vertices := by
      rw [← hv, h_verts]
    rw [h_l1_eq] at this
    exact List.append_cancel_left this
  have : p₂.vertices.head? = some c := by
    cases p₂ with
    | nil => simp only [vertices_nil, List.head?_cons]
    | cons _ _ => exact vertices_head? _
  rw [← h_v_l2] at this
  simp only [List.head?_cons, Option.some.injEq] at this
  exact this

lemma end_prefix_eq_get_vertices {a b c : V} (p₁ : Path a c) (p₂ : Path c b) :
    c = (p₁.comp p₂).vertices.get
        ⟨p₁.length, by
  simp only [vertices_comp, List.length_append, List.length_dropLast,
    vertices_length, add_tsub_cancel_right, lt_add_iff_pos_right, add_pos_iff,
    Nat.lt_one_iff, pos_of_gt, or_true]⟩ := by
  simp only [List.get_eq_getElem, vertices_comp, List.length_dropLast, vertices_length,
    add_tsub_cancel_right, le_refl, List.getElem_append_right, tsub_self, List.getElem_zero,
    vertices_head_eq_start]

/-- `split_at_vertex` decomposes a path `p` at the vertex sitting in
    position `i` of its `vertices` list. -/
theorem split_at_vertex {a b : V} (p : Path a b) (i : ℕ)
    (hi : i < p.vertices.length) :
    ∃ (v : V) (p₁ : Path a v) (p₂ : Path v b),
      p = p₁.comp p₂ ∧
      p₁.length = i ∧
      v = p.vertices.get ⟨i, hi⟩ := by
  have hi_le_len : i ≤ p.length := by
    rw [vertices_length] at hi
    exact Nat.le_of_lt_succ hi
  obtain ⟨v, p₁, p₂, hp, hlen⟩ := exists_decomp_at_length p hi_le_len
  subst hp
  refine ⟨v, p₁, p₂, rfl, hlen, ?_⟩
  have h_eq := end_prefix_eq_get_vertices p₁ p₂
  simp [hlen]

/-! ## Strictly simple paths -/

/-- A path is simple if it does not contain any vertex more than once.
    This is a strict definition; a cycle `a ⟶ ... ⟶ a` of non-zero length is not simple. -/
@[simp]
def IsStrictlySimple {a b : V} (p : Path a b) : Prop := p.vertices.Nodup

lemma isStrictlySimple_nil {a : V} : IsStrictlySimple (nil : Path a a) := by
  simp only [IsStrictlySimple, vertices_nil, List.nodup_cons, List.not_mem_nil, not_false_eq_true,
    List.nodup_nil, and_self]

@[simp]
lemma isStrictlySimple_cons [DecidableEq V] {a b c : V} (p : Path a b) (e : b ⟶ c) :
    IsStrictlySimple (p.cons e) ↔ IsStrictlySimple p ∧ c ∉ p.vertices := by
  simp only [IsStrictlySimple, vertices_cons]
  rw [List.nodup_concat]; aesop

/-- The finset of vertices in a path. -/
def vertexFinset [DecidableEq V] {a b : V} (p : Path a b) : Finset V :=
  p.vertices.toFinset

/-- The set of vertices of a simple path has cardinality `p.length + 1`. -/
lemma card_vertexFinset_of_isStrictlySimple [DecidableEq V] {a b : V} {p : Path a b}
    (hp : IsStrictlySimple p) :
    p.vertexFinset.card = p.length + 1 := by
  simp [vertexFinset, List.toFinset_card_of_nodup hp, vertices_length]

/-- **Key Lemma**: Simple paths have length strictly less than the number of vertices. -/
lemma length_lt_card_of_isStrictlySimple [DecidableEq V] [Fintype V]
    {a b : V} {p : Path a b} (hp : IsStrictlySimple p) :
    p.length < Fintype.card V := by
  simpa [card_vertexFinset_of_isStrictlySimple hp, Nat.succ_eq_add_one] using
    (Finset.card_le_univ p.vertexFinset)

/-- If a path is not strictly simple, then there exists a vertex that occurs at least twice. -/
lemma not_strictly_simple_iff_exists_repeated_vertex [DecidableEq V] {a b : V} {p : Path a b} :
    ¬IsStrictlySimple p ↔ ∃ v, v ∈ p.vertices ∧ p.vertices.count v ≥ 2 := by
  rw [IsStrictlySimple]
  constructor
  · intro h
    rw [List.nodup_iff_count_le_one] at h
    push_neg at h
    obtain ⟨v, hv⟩ := h
    exact ⟨v, List.count_pos_iff.mp (by omega), hv⟩
  · intro ⟨v, _, hv⟩
    rw [List.nodup_iff_count_le_one]
    push_neg
    exact ⟨v, hv⟩

/-- Removing a positive-length cycle from a path gives a strictly shorter path. -/
lemma remove_cycle_gives_shorter_path [DecidableEq V] {a v b : V}
    {p_prefix : Path a v} {p_cycle : Path v v} {p_rest : Path v b}
    (h_cycle_pos : p_cycle.length > 0) :
    (p_prefix.comp p_rest).length < (p_prefix.comp (p_cycle.comp p_rest)).length := by
  simp only [length_comp]
  omega

/-! ## Path splitting with properties -/

/-- Split a path at the **last** occurrence of a vertex. -/
theorem exists_decomp_of_mem_vertices_prop
    [DecidableEq V] {a b x : V} (p : Path a b) (hx : x ∈ p.vertices) :
    ∃ (p₁ : Path a x) (p₂ : Path x b),
      p = p₁.comp p₂ ∧ x ∉ p₂.vertices.tail := by
  classical
  induction p with
  | nil =>
      have hxa : x = a := by
        simpa [vertices_nil, List.mem_singleton] using hx
      subst hxa
      exact ⟨Path.nil, Path.nil, by simp only [comp_nil],
        by simp only [vertices_nil, List.tail_cons, List.not_mem_nil, not_false_eq_true]⟩
  | cons pPrev e ih =>
      have hx' : x ∈ pPrev.vertices ∨ x = (pPrev.cons e).end := by
        simpa using (mem_vertices_cons pPrev e).1 hx
      -- Case 1 : `x` is the final vertex.
      have h_case₁ :
          x = (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxe; subst hxe
        exact ⟨pPrev.cons e, Path.nil, by simp only [cons_eq_comp_toPath, comp_nil],
          by simp only [vertices_nil, List.tail_cons, List.not_mem_nil, not_false_eq_true]⟩
      -- Case 2 : `x` occurs in the prefix (and **is not** the final vertex).
      have h_case₂ :
          x ∈ pPrev.vertices → x ≠ (pPrev.cons e).end →
          ∃ (p₁ : Path a x) (p₂ : Path x (pPrev.cons e).end),
            pPrev.cons e = p₁.comp p₂ ∧
            x ∉ p₂.vertices.tail := by
        intro hxPrev hxe_ne
        rcases ih hxPrev with ⟨q₁, q₂, h_prev, h_not_tail⟩
        let q₂' : Path x (pPrev.cons e).end := q₂.comp e.toPath
        have h_eq : pPrev.cons e = q₁.comp q₂' := by
          dsimp [q₂']; simp only [h_prev, cons_eq_comp_toPath, Path.comp_assoc]
        have h_no_tail : x ∉ q₂'.vertices.tail := by
          intro hmem
          have hmem' : x ∈ (q₂.vertices.dropLast ++ (e.toPath).vertices).tail := by
            have hq₂' : q₂'.vertices = q₂.vertices.dropLast ++ (e.toPath).vertices := by
              simp_rw [q₂']; exact vertices_comp q₂ e.toPath
            simpa [hq₂'] using hmem
          by_cases h_nil : q₂.vertices.dropLast = []
          · have h_tail_toPath : x ∈ (e.toPath).vertices.tail := by
              simpa [h_nil] using hmem'
            have hx_end : x = (pPrev.comp e.toPath).end := by
              have : e.toPath.vertices.tail = [(pPrev.cons e).end] := by
                simp only [cons_eq_comp_toPath]
                rfl
              rw [this] at h_tail_toPath
              exact List.mem_singleton.mp h_tail_toPath
            exact hxe_ne hx_end
          · -- Complex case: q₂ has length > 0
            cases q₂ with
            | nil =>
              simp at h_nil
            | cons q₂' e' =>
              simp only [vertices_cons, List.concat_eq_append, List.dropLast_append_singleton,
                List.tail_append_of_ne_nil (vertices_nonempty q₂')] at hmem'
              cases hmem' with
              | inl h_in_q2_tail =>
                have : x ∈ q₂'.vertices.tail ∨ x = q₂'.vertices.getLast (vertices_nonempty q₂') := by
                  cases q₂'.vertices with
                  | nil => simp at h_in_q2_tail
                  | cons hd tl =>
                    simp only [List.tail_cons] at h_in_q2_tail
                    by_cases h_last : x = (hd :: tl).getLast (by simp)
                    · right; exact h_last
                    · left
                      have : x ∈ tl := h_in_q2_tail
                      exact this
                cases this with
                | inl h_tail => exact h_not_tail (List.mem_of_mem_tail h_tail)
                | inr h_last =>
                  have : x = q₂'.end := by
                    simp only [← vertices_getLast_eq_end q₂'] at h_last
                    exact h_last
                  have hx_in : x ∈ (q₂'.cons e').vertices.tail := by
                    simp only [vertices_cons, List.concat_eq_append, List.tail_append_of_ne_nil (vertices_nonempty q₂')]
                    left
                    rw [this]
                    exact List.getLast_mem (vertices_nonempty q₂')
                  exact h_not_tail hx_in
              | inr h_in_toPath =>
                have : e.toPath.vertices = [pPrev.end, (pPrev.cons e).end] := rfl
                rw [this] at h_in_toPath
                cases h_in_toPath with
                | inl h_eq_prev_end =>
                  have : x ∈ (q₂'.cons e').vertices := by
                    simp only [vertices_cons, List.concat_eq_append, List.mem_append,
                      List.mem_singleton]
                    right; exact h_eq_prev_end
                  have : x ∈ (q₂'.cons e').vertices.tail := by
                    simp only [vertices_cons, List.concat_eq_append] at this ⊢
                    cases (q₂'.cons e').vertices with
                    | nil => simp at this
                    | cons hd tl =>
                      simp only [List.tail_cons]
                      -- x is the end of q₂'.cons e', which is in the tail
                      have h_end : (q₂'.cons e').end = pPrev.end := by
                        have := h_prev
                        simp only [cons_eq_comp_toPath] at this
                        have h_comp_end : (q₁.comp (q₂'.cons e')).end = pPrev.end := by
                          rw [this]
                        simp at h_comp_end
                        exact h_comp_end
                      rw [← h_eq_prev_end, h_end]
                      have h_len : (q₂'.cons e').vertices.length ≥ 2 := by
                        simp [vertices_cons, vertices_length]
                        omega
                      have h_last_mem : (hd :: tl).getLast (by simp) ∈ tl := by
                        exact List.getLast_mem_tail h_len
                      convert h_last_mem
                      simp only [vertices_getLast_eq_end]
                  exact h_not_tail this
                | inr h_eq_end =>
                  exact hxe_ne h_eq_end
        exact ⟨q₁, q₂', h_eq, h_no_tail⟩
      cases hx' with
      | inl h_in_prefix =>
          by_cases h_eq_end : x = (pPrev.cons e).end
          · rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
          · rcases h_case₂ h_in_prefix h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
            exact ⟨p₁, p₂, h_eq, h_tail⟩
      | inr h_eq_end =>
          rcases h_case₁ h_eq_end with ⟨p₁, p₂, h_eq, h_tail⟩
          exact ⟨p₁, p₂, h_eq, h_tail⟩

/-! ## Shortest paths are simple -/

/-- Helper: dropLast is a prefix -/
lemma dropLast_prefix {α : Type*} (l : List α) : l.dropLast.IsPrefix l := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x =>
    simp only [List.dropLast_append_singleton]
    exact List.prefix_append xs [x]

/-- Helper for idxOf with prefix -/
lemma idxOf_eq_idxOf_of_isPrefix [DecidableEq V] {v : V} {l₁ l₂ : List V}
    (hpref : List.IsPrefix l₁ l₂) (hv : v ∈ l₁) :
    List.idxOf v l₂ = List.idxOf v l₁ := by
  rcases hpref with ⟨t, rfl⟩
  induction l₁ with
  | nil => cases hv
  | cons x xs ih =>
    by_cases h : v = x
    · simp only [h, List.cons_append, List.idxOf_cons_self]
    · have hvxs : v ∈ xs := by simpa [h] using hv
      simp only [List.cons_append, List.idxOf_cons_eq_add_one_idxOf_of_ne (Ne.symm h)]
      rw [ih hvxs]

/-- **Key Theorem**: A shortest path is strictly simple. -/
theorem isStrictlySimple_of_shortest [DecidableEq V]
    {a b : V} (p : Path a b)
    (h_min : ∀ q : Path a b, p.length ≤ q.length) :
    IsStrictlySimple p := by
  classical
  by_contra h_dup
  obtain ⟨v, hv_in, hv_ge₂⟩ := not_strictly_simple_iff_exists_repeated_vertex.mp h_dup
  obtain ⟨p₁, p₂, hp, hv_not_tail⟩ := exists_decomp_of_mem_vertices_prop p hv_in
  have hv_in_p1_dropLast : v ∈ p₁.vertices.dropLast := by
    have h_count_p : p.vertices.count v =
        (p₁.vertices.dropLast ++ p₂.vertices).count v := by
      rw [← vertices_comp, ← hp]
    rw [h_count_p] at hv_ge₂
    rw [List.count_append] at hv_ge₂
    have h_count_p2 : p₂.vertices.count v = 1 := by
      have h_head : p₂.vertices.head? = some v := by
        cases p₂ with
        | nil => simp [vertices_nil]
        | cons p' e =>
          simp only [vertices_cons]
          have h := vertices_head? p'
          simp [List.concat_eq_append]
      have hne : p₂.vertices ≠ [] := by
        apply List.ne_nil_of_head?_eq_some h_head
      have h_shape : p₂.vertices = v :: p₂.vertices.tail := by
        have h_first : p₂.vertices.head? = some v := h_head
        have h_decomp : ∃ h t, p₂.vertices = h :: t := List.exists_cons_of_ne_nil hne
        rcases h_decomp with ⟨h, t, heq⟩
        rw [heq]
        have h_eq : h = v := by
          rw [heq] at h_first
          simp only [List.head?_cons] at h_first
          exact Option.some.inj h_first
        rw [h_eq]
        have t_eq : t = p₂.vertices.tail := by rw [heq, List.tail_cons]
        rw [t_eq]
        exact rfl
      rw [h_shape]
      have h_not_in_tail : v ∉ p₂.vertices.tail := hv_not_tail
      simp only [List.count_cons_self, List.count_eq_zero_of_not_mem h_not_in_tail]
    have : (p₁.vertices.dropLast).count v ≥ 1 := by
      have : 1 + (p₁.vertices.dropLast).count v ≥ 2 := by
        rw [add_comm]
        simpa [h_count_p2] using hv_ge₂
      omega
    exact (List.count_pos_iff).1 (by omega)
  -- Extract cycle from p₁
  obtain ⟨q, c, h_p1_split⟩ := exists_decomp_of_mem_vertices p₁ (List.mem_of_mem_dropLast hv_in_p1_dropLast)
  have hc_pos : c.length > 0 := by
    by_cases h_len_zero : c.length = 0
    · have hc_nil : c = Path.nil := by
        apply (length_eq_zero_iff c).mp h_len_zero
      have : p₁ = q := by
        simpa [hc_nil, comp_nil] using h_p1_split
      have h_mem : v ∈ q.vertices.dropLast := by
        simpa [this] using hv_in_p1_dropLast
      have h_last : v = q.vertices.getLast (vertices_nonempty q) := by simp
      let i := q.vertices.idxOf v
      have hi_verts : i < q.vertices.length := by
        rw [List.idxOf_lt_length_iff]
        exact List.mem_of_mem_dropLast h_mem
      have hi : i < q.length := by
        have h_idx_lt_dropLast_len : i < q.vertices.dropLast.length := by
          have h_lt : List.idxOf v q.vertices.dropLast < q.vertices.dropLast.length :=
            List.idxOf_lt_length_of_mem h_mem
          have h_prefix : (q.vertices.dropLast).IsPrefix q.vertices := by
            exact dropLast_prefix q.vertices
          have h_eq : List.idxOf v q.vertices = List.idxOf v q.vertices.dropLast :=
            idxOf_eq_idxOf_of_isPrefix h_prefix h_mem
          simpa [i, h_eq] using h_lt
        rw [List.length_dropLast, vertices_length] at h_idx_lt_dropLast_len
        exact h_idx_lt_dropLast_len
      obtain ⟨split_v, shorter_q, _, h_comp_q, h_len_shorter, h_v_eq⟩ := split_at_vertex q i hi_verts
      have h_split_v_eq_v : split_v = v := by
        rw [h_v_eq]
        exact List.get_idxOf_of_mem (List.mem_of_mem_dropLast h_mem)
      subst h_split_v_eq_v
      let shorter_path := shorter_q.comp p₂
      have h_shorter_total : shorter_path.length < p.length := by
        have h_p1_eq : p₁ = q := by simpa [hc_nil, comp_nil] using h_p1_split
        have h_q_len : q.length > shorter_q.length := by
          rw [h_len_shorter]
          exact hi
        have h_decomp : p = p₁.comp p₂ := hp
        rw [h_p1_eq] at h_decomp
        have h_len : p.length = q.length + p₂.length := by
          rw [h_decomp, length_comp]
        have h_shorter_len : shorter_path.length = shorter_q.length + p₂.length := by
          rw [length_comp]
        rw [h_len, h_shorter_len]
        exact Nat.add_lt_add_right h_q_len p₂.length
      exact absurd (h_min shorter_path) (not_le.mpr h_shorter_total)
    · exact Nat.pos_of_ne_zero h_len_zero
  let p' : Path a b := q.comp p₂
  have h_shorter : p'.length < p.length := by
    have h_len_p : p.length = q.length + c.length + p₂.length := by
      rw [hp, h_p1_split]
      rw [length_comp, length_comp]
    have h_len_p' : p'.length = q.length + p₂.length := by
      rw [length_comp]
    rw [h_len_p, h_len_p']
    have : 0 < c.length := hc_pos
    apply Nat.add_lt_add_of_lt_of_le
    · exact Nat.lt_add_of_pos_right this
    · exact le_refl p₂.length
  exact (not_le.mpr h_shorter) (h_min p')

/-- The length of a strictly simple path is at most one less than the number of vertices. -/
lemma length_le_card_minus_one_of_isSimple {n : Type*} [Fintype n] [DecidableEq n] [Quiver n]
    {a b : n} (p : Path a b) (hp : p.IsStrictlySimple) :
    p.length ≤ Fintype.card n - 1 := by
  have h_card_verts : p.vertexFinset.card = p.length + 1 := by
    exact card_vertexFinset_of_isStrictlySimple hp
  have h_card_le_univ : p.vertexFinset.card ≤ Fintype.card n := by
    exact Finset.card_le_univ p.vertexFinset
  rw [h_card_verts] at h_card_le_univ
  exact Nat.le_sub_one_of_lt h_card_le_univ

end Quiver.Path
