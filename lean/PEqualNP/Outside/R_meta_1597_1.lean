import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Split the 2+-junk case on G11 by how junk AND gates sit relative to each other:
-- (1) one junk AND lies strictly inside the cone of another (nested junk),
-- (2) junk ANDs form an antichain and some top reaches two distinct junk ANDs via OR gates,
-- (3) junk ANDs form an antichain and every top reaches at most one junk AND via OR gates.
theorem PEqualNP.Outside.R_meta_1597_1 :
    (let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
     ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
       (∃ g1 ∈ junk G D, ∃ g2 ∈ junk G D, InCone 11 D g1 g2) → 22 ≤ D.size) →
    (let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
     ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
       (∀ g1 ∈ junk G D, ∀ g2 ∈ junk G D, ¬ InCone 11 D g1 g2) →
       (∃ a ∈ tops G D, ∃ g1 ∈ junk G D, ∃ g2 ∈ junk G D, g1 ≠ g2 ∧
         (∃ b1 : Fin 2, OrReaches 11 D (opnd D a b1) g1) ∧
         (∃ b2 : Fin 2, OrReaches 11 D (opnd D a b2) g2)) → 22 ≤ D.size) →
    (let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
     ∀ D : Circuit, IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
       (∀ g1 ∈ junk G D, ∀ g2 ∈ junk G D, ¬ InCone 11 D g1 g2) →
       (∀ a ∈ tops G D, ∀ g1 ∈ junk G D, ∀ g2 ∈ junk G D,
         (∃ b1 : Fin 2, OrReaches 11 D (opnd D a b1) g1) →
         (∃ b2 : Fin 2, OrReaches 11 D (opnd D a b2) g2) → g1 = g2) → 22 ≤ D.size) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  classical
  intro hnested hshared hdisjoint _ _ D hL hTF hjunk
  by_cases hn : ∃ g1 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
      ∃ g2 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
      InCone 11 D g1 g2
  · exact hnested D hL hTF hjunk hn
  · have hanti : ∀ g1 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
        ∀ g2 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
        ¬ InCone 11 D g1 g2 := by
      intro g1 hg1 g2 hg2 hcone
      exact hn ⟨g1, hg1, g2, hg2, hcone⟩
    by_cases hs : ∃ a ∈ tops (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
        ∃ g1 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
        ∃ g2 ∈ junk (edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D,
        g1 ≠ g2 ∧ (∃ b1 : Fin 2, OrReaches 11 D (opnd D a b1) g1) ∧ (∃ b2 : Fin 2, OrReaches 11 D (opnd D a b2) g2)
    · exact hshared D hL hTF hjunk hanti hs
    · apply hdisjoint D hL hTF hjunk hanti
      intro a ha g1 hg1 g2 hg2 hr1 hr2
      by_contra hne
      exact hs ⟨a, ha, g1, hg1, g2, hg2, hne, hr1, hr2⟩
