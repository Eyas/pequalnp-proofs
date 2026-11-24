import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1658

lemma main_proof : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  k0 < gates.length →
  (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
  k0 ∈ Kc →
  (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
    (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
  (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
    (∀ bK : Set ℕ, k0 ∈ bK →
      (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
    gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
    ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
  Bd.card ≤ 2 * Kc.card := by
  intro n gates S k0 Bd Kc hnorm _ _ _ hk0 hclosed hBd
  let F : ℕ → Finset ℕ := fun k =>
    match gates[k]? with
    | some g => g.inputs.toFinset
    | none => ∅
  have hsub : Bd ⊆ Kc.biUnion F := by
    intro bw hbw
    rcases hBd bw hbw with ⟨bk, bg, hbk_min, hget, _, hbw_in, _⟩
    have hbk_mem : bk ∈ Kc := hbk_min (Kc : Set ℕ) hk0 hclosed
    rw [Finset.mem_biUnion]
    refine ⟨bk, hbk_mem, ?_⟩
    dsimp [F]
    rw [hget]
    exact List.mem_toFinset.mpr hbw_in
  have hcardF : ∀ k ∈ Kc, (F k).card ≤ 2 := by
    intro k _
    dsimp [F]
    cases hget : gates[k]? with
    | none => simp
    | some g =>
      have hg_mem : g ∈ gates := List.mem_of_getElem? hget
      have hlen : g.inputs.length ≤ 2 := (hnorm g hg_mem).2
      exact le_trans (List.toFinset_card_le g.inputs) hlen
  calc Bd.card ≤ (Kc.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Kc, (F k).card := Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Kc, 2 := Finset.sum_le_sum hcardF
    _ = Kc.card * 2 := by simp
    _ = 2 * Kc.card := Nat.mul_comm _ _

end PEqualNP.Outside.L_meta_1658

theorem PEqualNP.Outside.L_meta_1658 : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (S : Finset (Fin n)) (k0 : ℕ) (Bd : Finset ℕ) (Kc : Finset ℕ),
  (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) →
  (∀ k : ℕ, ∀ g : PEqualNP.CircuitLowerBounds.Gate, gates[k]? = some g → ∀ i ∈ g.inputs, i < n + k) →
  k0 < gates.length →
  (∀ u : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun uk : Fin n => decide (uk = u)))).getD (n + k0) false = true ↔ u ∈ S) →
  k0 ∈ Kc →
  (∀ k1 ∈ Kc, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
    (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ Kc) →
  (∀ bw ∈ Bd, ∃ (bk : ℕ) (bg : PEqualNP.CircuitLowerBounds.Gate),
    (∀ bK : Set ℕ, k0 ∈ bK →
      (∀ k1 ∈ bK, ∀ (g1 : PEqualNP.CircuitLowerBounds.Gate) (k2 : ℕ), gates[k1]? = some g1 → n + k2 ∈ g1.inputs → k2 < k1 →
        (∀ u1 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u1k : Fin n => decide (u1k = u1)))).getD (n + k2) false = true → u1 ∈ S) → k2 ∈ bK) → bk ∈ bK) ∧
    gates[bk]? = some bg ∧ bg.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ bw ∈ bg.inputs ∧
    ¬ (∀ u2 : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun u2k : Fin n => decide (u2k = u2)))).getD bw false = true → u2 ∈ S)) →
  Bd.card ≤ 2 * Kc.card := by
  exact PEqualNP.Outside.L_meta_1658.main_proof
