import FormalConjectures.ErdosProblems.«934»

/-!
Proof of Erdos934.erdos_934.variants.h_two (Chung, Gyarfas, Tuza, Trotter 1990):
Every 2K2-free graph with maximum degree at most d has at most 5 * d^2 / 4 edges,
with equality attained for even d by the balanced blow-up of C5.
-/

open SimpleGraph Finset

namespace Erdos934Proof

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Is2K2Free G` means any two edges share a vertex or have an edge between them. -/
private def Is2K2Free (G : SimpleGraph V) : Prop :=
  ∀ u v w x : V, G.Adj u v → G.Adj w x →
    u = w ∨ u = x ∨ v = w ∨ v = x ∨
    G.Adj u w ∨ G.Adj u x ∨ G.Adj v w ∨ G.Adj v x

omit [Fintype V] [DecidableEq V] in
/-- `¬ HasFarEdges G 2` implies `Is2K2Free G`. -/
private lemma is2K2Free_of_not_hasFarEdges {G : SimpleGraph V}
    (h : ¬ Erdos934.HasFarEdges G 2) : Is2K2Free G := by
  intro u v w x huv hwx
  by_contra hno
  push Not at hno
  rcases hno with ⟨huw, hux, hvw, hvx, hauw, haux, havw, havx⟩
  apply h
  refine ⟨u, v, w, x, huv, hwx, ?_⟩
  intro a ha b hb
  have hne : a ≠ b := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  have hnadj : ¬ G.Adj a b := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
  by_contra hlt
  push Not at hlt
  cases hd : G.edist a b with
  | top => rw [hd] at hlt; simp at hlt
  | coe k =>
    rw [hd] at hlt
    have hk : k < 2 := by exact_mod_cast hlt
    interval_cases k
    · exact hne (SimpleGraph.edist_eq_zero_iff.1 hd)
    · exact hnadj (SimpleGraph.edist_eq_one_iff_adj.1 hd)

omit [Fintype V] [DecidableEq V] in
/-- Conversely, `Is2K2Free G` implies `¬ HasFarEdges G 2`. -/
private lemma not_hasFarEdges_of_is2K2Free {G : SimpleGraph V}
    (h : Is2K2Free G) : ¬ Erdos934.HasFarEdges G 2 := by
  rintro ⟨u, v, w, x, huv, hwx, hdist⟩
  have hlt2 : ∀ a b : V, (a = b ∨ G.Adj a b) → ¬ ((2 : ℕ∞) ≤ G.edist a b) := by
    intro a b hab hle
    rcases hab with rfl | hadj
    · rw [SimpleGraph.edist_self] at hle; exact absurd hle (by decide)
    · have : G.edist a b = 1 := SimpleGraph.edist_eq_one_iff_adj.2 hadj
      rw [this] at hle; exact absurd hle (by decide)
  rcases h u v w x huv hwx with rfl | rfl | rfl | rfl | h1 | h1 | h1 | h1
  · exact hlt2 u u (Or.inl rfl) (hdist u (by simp) u (by simp))
  · exact hlt2 u u (Or.inl rfl) (hdist u (by simp) u (by simp))
  · exact hlt2 v v (Or.inl rfl) (hdist v (by simp) v (by simp))
  · exact hlt2 v v (Or.inl rfl) (hdist v (by simp) v (by simp))
  · exact hlt2 u w (Or.inr h1) (hdist u (by simp) w (by simp))
  · exact hlt2 u x (Or.inr h1) (hdist u (by simp) x (by simp))
  · exact hlt2 v w (Or.inr h1) (hdist v (by simp) w (by simp))
  · exact hlt2 v x (Or.inr h1) (hdist v (by simp) x (by simp))

/-- Edges of `G` with both endpoints in `S`. -/
private def edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- Edges of `G` with one endpoint in `A` and one in `B`. -/
private def edgesBetween (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => (∃ a ∈ A, a ∈ e) ∧ (∃ b ∈ B, b ∈ e))

/-- Handshaking lemma on a subset: `2 * |E(S)| = ∑ v ∈ S, |N(v) ∩ S|`. -/
private lemma two_mul_card_edgesIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    2 * (edgesIn G S).card = ∑ v ∈ S, (S.filter (G.Adj v)).card := by
  have h1 : ∑ v ∈ S, (S.filter (G.Adj v)).card =
      ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v _
    rw [Finset.card_filter]
  rw [h1]
  have h2 : ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card =
      ∑ e ∈ edgesIn G S, ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) = e)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, edgesIn,
        SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨⟨hu, hv⟩, hadj⟩
        refine ⟨s(u, v), ⟨hadj, fun w hw => ?_⟩, ⟨⟨hu, hv⟩, hadj, rfl⟩⟩
        rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
      · rintro ⟨_, _, ⟨⟨hu, hv⟩, hadj, _⟩⟩
        exact ⟨⟨hu, hv⟩, hadj⟩
    · intro e₁ _ e₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  rw [h2]
  have hcard2 : ∀ e ∈ edgesIn G S,
      ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) = e)).card = 2 := by
    intro e he
    simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := he.1
      have hu : u ∈ S := he.2 u (by simp)
      have hv : v ∈ S := he.2 v (by simp)
      have hset : (S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) = s(u, v)) =
          {(u, v), (v, u)} := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
        constructor
        · rintro ⟨_, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨⟨hu, hv⟩, huv, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨⟨hv, hu⟩, huv.symm, Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h; exact huv.ne (congrArg Prod.fst h)
  rw [Finset.sum_congr rfl hcard2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- For disjoint `A, B`, `|E(A, B)| = ∑ a ∈ A, |N(a) ∩ B|`. -/
private lemma card_edgesBetween_left (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hdisj : Disjoint A B) :
    (edgesBetween G A B).card = ∑ a ∈ A, (B.filter (G.Adj a)).card := by
  have h1 : ∑ a ∈ A, (B.filter (G.Adj a)).card =
      ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl; intro a _; rw [Finset.card_filter]
  rw [h1]
  symm
  refine Finset.card_bij (fun p _ => s(p.1, p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    simp only [edgesBetween, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    exact ⟨hp.2, ⟨p.1, hp.1.1, by simp⟩, ⟨p.2, hp.1.2, by simp⟩⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    simp only [Finset.mem_filter, Finset.mem_product] at hp₁ hp₂
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      exact Finset.disjoint_left.1 hdisj hp₁.1.1 (h1 ▸ hp₂.1.2)
  · intro e he
    simp only [edgesBetween, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rcases he with ⟨huv, ⟨a, ha, hae⟩, ⟨b, hb, hbe⟩⟩
      rw [Sym2.mem_iff] at hae hbe
      rcases hae with rfl | rfl <;> rcases hbe with rfl | rfl
      · exact absurd hb (Finset.disjoint_left.1 hdisj ha)
      · exact ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, huv⟩, rfl⟩
      · exact ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, huv.symm⟩, Sym2.eq_swap⟩
      · exact absurd hb (Finset.disjoint_left.1 hdisj ha)

private lemma edgesBetween_comm (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    edgesBetween G A B = edgesBetween G B A := by
  ext e; simp only [edgesBetween, Finset.mem_filter]; tauto

private lemma card_edgesBetween_right (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hdisj : Disjoint A B) :
    (edgesBetween G A B).card = ∑ b ∈ B, (A.filter (G.Adj b)).card := by
  rw [edgesBetween_comm, card_edgesBetween_left G hdisj.symm]

/-- Partition of `G.edgeFinset` across `S` and `univ \ S`. -/
private lemma card_edgeFinset_partition (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card =
      (edgesIn G S).card + (edgesBetween G S (Finset.univ \ S)).card +
      (edgesIn G (Finset.univ \ S)).card := by
  set T := Finset.univ \ S
  have h1 : G.edgeFinset = edgesIn G S ∪ edgesBetween G S T ∪ edgesIn G T := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_union, edgesIn, edgesBetween, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, T, Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · intro huv
        by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
        · left; left; refine ⟨huv, fun w hw => ?_⟩
          rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
        · left; right; exact ⟨huv, ⟨u, hu, by simp⟩, ⟨v, hv, by simp⟩⟩
        · left; right; exact ⟨huv, ⟨v, hv, by simp⟩, ⟨u, hu, by simp⟩⟩
        · right; refine ⟨huv, fun w hw => ?_⟩
          rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
  have hd1 : Disjoint (edgesIn G S) (edgesBetween G S T) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [edgesIn, edgesBetween, Finset.mem_filter] at he1 he2
    rcases he2.2.2 with ⟨b, hbT, hbe⟩
    exact (Finset.mem_sdiff.1 hbT).2 (he1.2 b hbe)
  have hd2 : Disjoint (edgesIn G S ∪ edgesBetween G S T) (edgesIn G T) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_union, edgesIn, edgesBetween, Finset.mem_filter] at he1 he2
    rcases he1 with he1 | he1
    · induction e using Sym2.ind with
      | _ u v =>
        exact (Finset.mem_sdiff.1 (he2.2 u (by simp))).2 (he1.2 u (by simp))
    · rcases he1.2.1 with ⟨a, haS, hae⟩
      exact (Finset.mem_sdiff.1 (he2.2 a hae)).2 haS
  rw [h1, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]

/-- Covering bound for a set of edges `E ⊆ edgesIn G S`:
    if every edge in `E` has an endpoint in `C`, and every `c ∈ C` has `≤ k` neighbors in `S`,
    then `E.card ≤ C.card * k`. -/
private lemma card_edges_le_of_cover (G : SimpleGraph V) [DecidableRel G.Adj]
    {E : Finset (Sym2 V)} {S C : Finset V} {k : ℕ}
    (hES : E ⊆ edgesIn G S)
    (hcov : ∀ e ∈ E, ∃ c ∈ C, c ∈ e)
    (hdeg : ∀ c ∈ C, (S.filter (G.Adj c)).card ≤ k) :
    E.card ≤ C.card * k := by
  have hsub : E ⊆ C.biUnion (fun c => (S.filter (G.Adj c)).image (fun w => s(c, w))) := by
    intro e he
    rcases hcov e he with ⟨c, hcC, hce⟩
    have heS := hES he
    simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at heS
    induction e using Sym2.ind with
    | _ u v =>
      rw [Finset.mem_biUnion]
      refine ⟨c, hcC, ?_⟩
      rw [Sym2.mem_iff] at hce
      rw [Finset.mem_image]
      rcases hce with rfl | rfl
      · exact ⟨v, Finset.mem_filter.2 ⟨heS.2 v (by simp), heS.1⟩, rfl⟩
      · exact ⟨u, Finset.mem_filter.2 ⟨heS.2 u (by simp), heS.1.symm⟩, Sym2.eq_swap⟩
  calc E.card
      ≤ (C.biUnion (fun c => (S.filter (G.Adj c)).image (fun w => s(c, w)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ c ∈ C, ((S.filter (G.Adj c)).image (fun w => s(c, w))).card := Finset.card_biUnion_le
    _ ≤ ∑ c ∈ C, (S.filter (G.Adj c)).card :=
        Finset.sum_le_sum (fun c _ => Finset.card_image_le)
    _ ≤ ∑ _c ∈ C, k := Finset.sum_le_sum (fun c hc => hdeg c hc)
    _ = C.card * k := by rw [Finset.sum_const, smul_eq_mul]

/-- Weighted handshaking on `Y`:
    `∑ e ∈ edgesIn G Y, (f u + f v) = ∑ y ∈ Y, f y * |N(y) ∩ Y|`. -/
private lemma sum_edge_weights (G : SimpleGraph V) [DecidableRel G.Adj]
    (Y : Finset V) (f : V → ℕ) :
    ∑ e ∈ edgesIn G Y, (Sym2.lift ⟨fun u v => f u + f v, fun _ _ => add_comm _ _⟩ e) =
      ∑ y ∈ Y, f y * (Y.filter (G.Adj y)).card := by
  have h1 : ∑ y ∈ Y, f y * (Y.filter (G.Adj y)).card =
      ∑ p ∈ (Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2), f p.1 := by
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, smul_eq_mul, mul_comm]
  rw [h1]
  have h2 : ∑ p ∈ (Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2), f p.1 =
      ∑ e ∈ edgesIn G Y,
        ∑ p ∈ (Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) = e), f p.1 := by
    rw [← Finset.sum_biUnion]
    · congr 1; ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, edgesIn,
        SimpleGraph.mem_edgeFinset]
      constructor
      · rintro ⟨⟨hu, hv⟩, hadj⟩
        refine ⟨s(u, v), ⟨hadj, fun w hw => ?_⟩, ⟨⟨hu, hv⟩, hadj, rfl⟩⟩
        rw [Sym2.mem_iff] at hw; rcases hw with rfl | rfl <;> assumption
      · rintro ⟨_, _, ⟨⟨hu, hv⟩, hadj, _⟩⟩
        exact ⟨⟨hu, hv⟩, hadj⟩
    · intro e₁ _ e₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter] at hp1 hp2
      exact hne (hp1.2.2.symm.trans hp2.2.2)
  rw [h2]
  apply Finset.sum_congr rfl
  intro e he
  simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
    have huv : G.Adj u v := he.1
    have hu : u ∈ Y := he.2 u (by simp)
    have hv : v ∈ Y := he.2 v (by simp)
    have hset : (Y ×ˢ Y).filter (fun p => G.Adj p.1 p.2 ∧ s(p.1, p.2) = s(u, v)) =
        {(u, v), (v, u)} := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq, Sym2.eq_iff]
      constructor
      · rintro ⟨_, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨⟨hu, hv⟩, huv, Or.inl ⟨rfl, rfl⟩⟩
        · exact ⟨⟨hv, hu⟩, huv.symm, Or.inr ⟨rfl, rfl⟩⟩
    rw [hset, Finset.sum_pair]
    · simp
    · intro h; exact huv.ne (congrArg Prod.fst h)

omit [Fintype V] [DecidableEq V] in
/-- Theorem 1 (CGTT90): For disjoint `A, B` with `A` independent and `B` nonempty in a
    `2K2`-free graph, some `x ∈ B` has `N(x)` meeting every edge between `A` and `B`. -/
private lemma theorem1_edge_cover {G : SimpleGraph V} [DecidableRel G.Adj]
    (h2k2 : Is2K2Free G) {A B : Finset V} (hdisj : Disjoint A B)
    (hind : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v) (hB : B.Nonempty) :
    ∃ x ∈ B, ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → G.Adj x a ∨ G.Adj x b := by
  obtain ⟨x, hxB, hxmax⟩ := Finset.exists_max_image B (fun v => (A.filter (G.Adj v)).card) hB
  refine ⟨x, hxB, fun a ha b hb hab => ?_⟩
  by_contra hno
  push Not at hno
  rcases hno with ⟨hnxa, hnxb⟩
  have hxb : x ≠ b := by rintro rfl; exact hnxa hab.symm
  have hnsub : ¬ (A.filter (G.Adj x) ⊆ A.filter (G.Adj b)) := by
    intro hsub
    have hssub : A.filter (G.Adj x) ⊂ A.filter (G.Adj b) :=
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => by
        have : a ∈ A.filter (G.Adj b) := by simp [ha, hab.symm]
        rw [← heq] at this
        exact hnxa (Finset.mem_filter.1 this).2⟩
    exact absurd (Finset.card_lt_card hssub) (not_lt.2 (hxmax b hb))
  rw [Finset.not_subset] at hnsub
  rcases hnsub with ⟨w, hwx, hnwb⟩
  simp only [Finset.mem_filter] at hwx hnwb
  rcases hwx with ⟨hwA, hxw⟩
  have hnbw : ¬ G.Adj b w := fun h => hnwb ⟨hwA, h⟩
  have hwa : w ≠ a := by rintro rfl; exact hnxa hxw
  have hxa : x ≠ a := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hxB)
  have hwb : w ≠ b := fun h => Finset.disjoint_left.1 hdisj hwA (h ▸ hb)
  rcases h2k2 x w a b hxw hab with h | h | h | h | h | h | h | h
  · exact hxa h
  · exact hxb h
  · exact hwa h
  · exact hwb h
  · exact hnxa h
  · exact hnxb h
  · exact hind w hwA a ha h
  · exact hnbw h.symm

end Helpers

/- Case (i): Bipartite graphs -/

section CaseBipartite

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma case_bipartite {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    (hcol : G.Colorable 2) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  rcases hcol with ⟨c⟩
  set A := Finset.univ.filter (fun v => c v = 0)
  set B := Finset.univ.filter (fun v => c v = 1)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]; intro v hvA hvB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hvA hvB
    rw [hvA] at hvB; exact absurd hvB (by decide)
  have hAB : A ∪ B = Finset.univ := by
    ext v; simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    have hcv : c v = 0 ∨ c v = 1 := by
      have hlt := (c v).isLt
      by_cases h0 : (c v).1 = 0
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Fin.ext (by omega))
    exact hcv
  have hindA : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact c.valid huv (hu.trans hv.symm)
  have hindB : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact c.valid huv (hu.trans hv.symm)
  by_cases hB : B.Nonempty
  · obtain ⟨x, hxB, hcov⟩ := theorem1_edge_cover h2k2 hdisj hindA hB
    set C := A.filter (G.Adj x)
    have hCcard : C.card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hdeg x)
    have hE : G.edgeFinset.card ≤ C.card * d := by
      refine card_edges_le_of_cover G (S := Finset.univ) (by intro e he; simp [edgesIn, he]) ?_ ?_
      · intro e he
        rw [SimpleGraph.mem_edgeFinset] at he
        induction e using Sym2.ind with
        | _ u v =>
          have huAB : u ∈ A ∨ u ∈ B := by rw [← Finset.mem_union, hAB]; exact Finset.mem_univ u
          have hvAB : v ∈ A ∨ v ∈ B := by rw [← Finset.mem_union, hAB]; exact Finset.mem_univ v
          rcases huAB with hu | hu <;> rcases hvAB with hv | hv
          · exact absurd he (hindA u hu v hv)
          · rcases hcov u hu v hv he with hxu | hxv
            · exact ⟨u, by simp [C, hu, hxu], by simp⟩
            · exact absurd hxv (hindB x hxB v hv)
          · rcases hcov v hv u hu he.symm with hxv | hxu
            · exact ⟨v, by simp [C, hv, hxv], by simp⟩
            · exact absurd hxu (hindB x hxB u hu)
          · exact absurd he (hindB u hu v hv)
      · intro c _; exact hdeg c
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hB
    have hA : A = Finset.univ := by rw [← hAB, hB, Finset.union_empty]
    have hE0 : G.edgeFinset = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset, Finset.notMem_empty, iff_false]
        exact hindA u (hA ▸ Finset.mem_univ u) v (hA ▸ Finset.mem_univ v)
    rw [hE0, Finset.card_empty]; positivity

end CaseBipartite

/- Case (ii): Triangle-free non-bipartite graphs (C5 blow-up) -/

section CaseTriangleFree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Algebraic inequality for C5 blow-ups. -/
private lemma c5_blowup_ineq {a0 a1 a2 a3 a4 d : ℕ}
    (h0 : a4 + a1 ≤ d) (h1 : a0 + a2 ≤ d) (h2 : a1 + a3 ≤ d)
    (h3 : a2 + a4 ≤ d) (h4 : a3 + a0 ≤ d) :
    4 * (a0 * a1 + a1 * a2 + a2 * a3 + a3 * a4 + a4 * a0) ≤ 5 * d ^ 2 := by
  have hmin : ∀ b0 b1 b2 b3 b4 : ℕ,
      b4 + b1 ≤ d → b0 + b2 ≤ d → b1 + b3 ≤ d → b2 + b4 ≤ d → b3 + b0 ≤ d →
      b0 ≤ b1 → b0 ≤ b2 → b0 ≤ b3 → b0 ≤ b4 →
      4 * (b0 * b1 + b1 * b2 + b2 * b3 + b3 * b4 + b4 * b0) ≤ 5 * d ^ 2 := by
    intro b0 b1 b2 b3 b4 k0 k1 k2 k3 k4 m1 m2 m3 m4
    by_cases c2 : 2 * b2 ≤ d
    · by_cases c3 : 2 * b3 ≤ d
      · nlinarith
      · have : 2 * b0 ≤ d := by omega
        have : 2 * b1 ≤ d := by omega
        nlinarith
    · have : 2 * b0 ≤ d := by omega
      have : 2 * b4 ≤ d := by omega
      nlinarith
  by_cases m0 : a0 ≤ a1 ∧ a0 ≤ a2 ∧ a0 ≤ a3 ∧ a0 ≤ a4
  · exact hmin a0 a1 a2 a3 a4 h0 h1 h2 h3 h4 m0.1 m0.2.1 m0.2.2.1 m0.2.2.2
  · by_cases m1 : a1 ≤ a2 ∧ a1 ≤ a3 ∧ a1 ≤ a4 ∧ a1 ≤ a0
    · have := hmin a1 a2 a3 a4 a0 h1 h2 h3 h4 h0 m1.1 m1.2.1 m1.2.2.1 m1.2.2.2
      linarith
    · by_cases m2 : a2 ≤ a3 ∧ a2 ≤ a4 ∧ a2 ≤ a0 ∧ a2 ≤ a1
      · have := hmin a2 a3 a4 a0 a1 h2 h3 h4 h0 h1 m2.1 m2.2.1 m2.2.2.1 m2.2.2.2
        linarith
      · by_cases m3 : a3 ≤ a4 ∧ a3 ≤ a0 ∧ a3 ≤ a1 ∧ a3 ≤ a2
        · have := hmin a3 a4 a0 a1 a2 h3 h4 h0 h1 h2 m3.1 m3.2.1 m3.2.2.1 m3.2.2.2
          linarith
        · have m4 : a4 ≤ a0 ∧ a4 ≤ a1 ∧ a4 ≤ a2 ∧ a4 ≤ a3 := by omega
          have := hmin a4 a0 a1 a2 a3 h4 h0 h1 h2 h3 m4.1 m4.2.1 m4.2.2.1 m4.2.2.2
          linarith

omit [Fintype V] [DecidableEq V] in
/-- Non-2-colorable graphs contain an odd closed walk. -/
private lemma exists_odd_closed_walk_of_not_colorable {G : SimpleGraph V}
    (hnc : ¬ G.Colorable 2) : ∃ v : V, ∃ p : G.Walk v v, Odd p.length := by
  classical
  by_contra hno
  push Not at hno
  apply hnc
  let rep : G.ConnectedComponent → V := fun C => C.exists_rep.choose
  have hrep : ∀ v : V, G.Reachable (rep (G.connectedComponentMk v)) v := fun v => by
    have h := (G.connectedComponentMk v).exists_rep.choose_spec
    exact SimpleGraph.ConnectedComponent.exact h
  let col : V → Fin 2 := fun v =>
    if ∃ p : G.Walk (rep (G.connectedComponentMk v)) v, Even p.length then 0 else 1
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro u v huv
  have hcc : G.connectedComponentMk u = G.connectedComponentMk v :=
    SimpleGraph.ConnectedComponent.sound (SimpleGraph.Adj.reachable huv)
  set r := rep (G.connectedComponentMk u)
  have hr_eq : rep (G.connectedComponentMk v) = r := congrArg rep hcc.symm
  have hru : G.Reachable r u := hrep u
  have hrv : G.Reachable r v := hr_eq ▸ hrep v
  dsimp only [col]
  rw [hr_eq]
  split_ifs with hu hv hv
  · exfalso
    rcases hu with ⟨pu, hpu⟩
    rcases hv with ⟨pv, hpv⟩
    let hclosed : G.Walk r r := pu.append (SimpleGraph.Walk.cons huv pv.reverse)
    have hlen : hclosed.length = pu.length + 1 + pv.length := by
      simp [hclosed]; omega
    have hodd : Odd hclosed.length := by
      rw [hlen]
      rcases hpu with ⟨a, ha⟩; rcases hpv with ⟨b, hb⟩
      exact ⟨a + b, by omega⟩
    exact hno r hclosed hodd
  · decide
  · decide
  · exfalso
    obtain ⟨pu⟩ := hru
    obtain ⟨pv⟩ := hrv
    have hpu_odd : Odd pu.length := Nat.not_even_iff_odd.1 (fun h => hu ⟨pu, h⟩)
    have hpv_odd : Odd pv.length := Nat.not_even_iff_odd.1 (fun h => hv ⟨pv, h⟩)
    let hclosed : G.Walk r r := pu.append (SimpleGraph.Walk.cons huv pv.reverse)
    have hlen : hclosed.length = pu.length + 1 + pv.length := by
      simp [hclosed]; omega
    have hodd : Odd hclosed.length := by
      rw [hlen]
      rcases hpu_odd with ⟨a, ha⟩; rcases hpv_odd with ⟨b, hb⟩
      exact ⟨a + b + 1, by omega⟩
    exact hno r hclosed hodd

omit [Fintype V] in
/-- A triangle-free, non-bipartite, `2K2`-free graph contains a 5-cycle `x : ZMod 5 → V`. -/
private lemma exists_c5_of_triangleFree_not_colorable {G : SimpleGraph V}
    (h2k2 : Is2K2Free G) (htf : G.CliqueFree 3) (hnc : ¬ G.Colorable 2) :
    ∃ x : ZMod 5 → V, ∀ i : ZMod 5, G.Adj (x i) (x (i + 1)) := by
  classical
  have hex : ∃ n : ℕ, Odd n ∧ ∃ v : V, ∃ p : G.Walk v v, p.length = n := by
    obtain ⟨v, p, hp⟩ := exists_odd_closed_walk_of_not_colorable hnc
    exact ⟨p.length, hp, v, p, rfl⟩
  let L := Nat.find hex
  have hL : Odd L ∧ ∃ v : V, ∃ p : G.Walk v v, p.length = L := Nat.find_spec hex
  have hLmin : ∀ n < L, Odd n → ¬ ∃ v : V, ∃ p : G.Walk v v, p.length = n :=
    fun n hn hodd => fun h => Nat.find_min hex hn ⟨hodd, h⟩
  rcases hL with ⟨hLodd, v₀, p, hpL⟩
  have hL_ne1 : L ≠ 1 := by
    intro h1
    rw [h1] at hpL
    cases p with
    | nil => simp at hpL
    | cons hadj q =>
      simp only [SimpleGraph.Walk.length_cons, Nat.add_eq_right] at hpL
      cases q with
      | nil => exact hadj.ne rfl
      | cons _ _ => simp at hpL
  have hL_ne3 : L ≠ 3 := by
    intro h3
    rw [h3] at hpL
    cases p with
    | nil => simp at hpL
    | cons h1 q1 =>
      cases q1 with
      | nil => simp at hpL
      | cons h2 q2 =>
        cases q2 with
        | nil => simp at hpL
        | cons h3' q3 =>
          cases q3 with
          | nil =>
            rename_i u1 u2
            have hne1 : v₀ ≠ u1 := h1.ne
            have hne2 : u1 ≠ u2 := h2.ne
            have hne3 : v₀ ≠ u2 := h3'.ne.symm
            have hcl : G.IsNClique 3 ({v₀, u1, u2} : Finset V) := by
              refine ⟨?_, ?_⟩
              · intro a ha b hb hab
                simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
                  Set.mem_singleton_iff] at ha hb
                rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
                · exact absurd rfl hab
                · exact h1
                · exact h3'.symm
                · exact h1.symm
                · exact absurd rfl hab
                · exact h2
                · exact h3'
                · exact h2.symm
                · exact absurd rfl hab
              · rw [Finset.card_insert_of_notMem (by simp [hne1, hne3]),
                  Finset.card_insert_of_notMem (by simp [hne2]), Finset.card_singleton]
            exact htf {v₀, u1, u2} hcl
          | cons _ _ => simp at hpL
  -- Helper: subwalk between getVert a and getVert b of length b - a
  have hwalk : ∀ a b : ℕ, a ≤ b → b ≤ L →
      ∃ q : G.Walk (p.getVert a) (p.getVert b), q.length = b - a := by
    intro a b hab hbL
    induction b with
    | zero =>
      have ha : a = 0 := Nat.eq_zero_of_le_zero hab
      subst ha; exact ⟨SimpleGraph.Walk.nil, rfl⟩
    | succ b ih =>
      by_cases h : a = b + 1
      · subst h; exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · have hab' : a ≤ b := by omega
        obtain ⟨q, hq⟩ := ih hab' (by omega)
        have hadj : G.Adj (p.getVert b) (p.getVert (b + 1)) :=
          p.adj_getVert_succ (by omega)
        exact ⟨q.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil), by simp [hq]; omega⟩
  have hget0 : p.getVert 0 = v₀ := p.getVert_zero
  have hgetL : p.getVert L = v₀ := by rw [← hpL]; exact p.getVert_length
  have hno_eq : ∀ i j : ℕ, i < j → j < L → p.getVert i ≠ p.getVert j := by
    intro i j hij hjL heq
    obtain ⟨q1, hq1⟩ := hwalk 0 i (Nat.zero_le _) (by omega)
    obtain ⟨q2, hq2⟩ := hwalk i j (le_of_lt hij) (le_of_lt hjL)
    obtain ⟨q3, hq3⟩ := hwalk j L (le_of_lt hjL) (le_refl L)
    by_cases hodd : Odd (j - i)
    · let hloop : G.Walk (p.getVert i) (p.getVert i) := q2.copy rfl heq.symm
      have hlen : hloop.length = j - i := by simp [hloop, hq2]
      exact hLmin (j - i) (by omega) hodd ⟨p.getVert i, hloop, hlen⟩
    · have heven : Even (j - i) := Nat.not_odd_iff_even.1 hodd
      let hloop : G.Walk v₀ v₀ := (q1.copy hget0 rfl).append (q3.copy heq.symm hgetL)
      have hlen : hloop.length = i + (L - j) := by
        simp [hloop, hq1, hq3]
      have hodd2 : Odd (i + (L - j)) := by
        rcases hLodd with ⟨a, ha⟩; rcases heven with ⟨b, hb⟩
        exact ⟨a - b, by omega⟩
      exact hLmin (i + (L - j)) (by omega) hodd2 ⟨v₀, hloop, hlen⟩
  have hno_chord : ∀ i j : ℕ, i + 2 ≤ j → j < L → ¬ (i = 0 ∧ j + 1 = L) →
      ¬ G.Adj (p.getVert i) (p.getVert j) := by
    intro i j hij hjL hnotend hadj
    obtain ⟨q1, hq1⟩ := hwalk 0 i (Nat.zero_le _) (by omega)
    obtain ⟨q2, hq2⟩ := hwalk i j (by omega) (le_of_lt hjL)
    obtain ⟨q3, hq3⟩ := hwalk j L (le_of_lt hjL) (le_refl L)
    by_cases hodd : Odd (j - i + 1)
    · let hloop : G.Walk (p.getVert i) (p.getVert i) :=
        q2.append (SimpleGraph.Walk.cons hadj.symm SimpleGraph.Walk.nil)
      have hlen : hloop.length = j - i + 1 := by simp [hloop, hq2]
      exact hLmin (j - i + 1) (by omega) hodd ⟨p.getVert i, hloop, hlen⟩
    · have heven : Even (j - i + 1) := Nat.not_odd_iff_even.1 hodd
      let hloop : G.Walk v₀ v₀ :=
        (q1.copy hget0 rfl).append (SimpleGraph.Walk.cons hadj (q3.copy rfl hgetL))
      have hlen : hloop.length = i + 1 + (L - j) := by
        simp [hloop, hq1, hq3]; omega
      have hodd2 : Odd (i + 1 + (L - j)) := by
        rcases hLodd with ⟨a, ha⟩; rcases heven with ⟨b, hb⟩
        exact ⟨a + 1 - b, by omega⟩
      exact hLmin (i + 1 + (L - j)) (by omega) hodd2 ⟨v₀, hloop, hlen⟩
  have hL5 : L = 5 := by
    by_contra hne5
    have hL7 : 7 ≤ L := by
      rcases hLodd with ⟨k, hk⟩; omega
    have h01 : G.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (by omega)
    have h34 : G.Adj (p.getVert 3) (p.getVert 4) := p.adj_getVert_succ (by omega)
    rcases h2k2 _ _ _ _ h01 h34 with h | h | h | h | h | h | h | h
    · exact hno_eq 0 3 (by omega) (by omega) h
    · exact hno_eq 0 4 (by omega) (by omega) h
    · exact hno_eq 1 3 (by omega) (by omega) h
    · exact hno_eq 1 4 (by omega) (by omega) h
    · exact hno_chord 0 3 (by omega) (by omega) (by omega) h
    · exact hno_chord 0 4 (by omega) (by omega) (by omega) h
    · exact hno_chord 1 3 (by omega) (by omega) (by omega) h
    · exact hno_chord 1 4 (by omega) (by omega) (by omega) h
  have hp5 : p.length = 5 := hpL.trans hL5
  refine ⟨fun i => p.getVert i.val, fun i => ?_⟩
  fin_cases i
  · change G.Adj (p.getVert 0) (p.getVert 1); exact p.adj_getVert_succ (by omega)
  · change G.Adj (p.getVert 1) (p.getVert 2); exact p.adj_getVert_succ (by omega)
  · change G.Adj (p.getVert 2) (p.getVert 3); exact p.adj_getVert_succ (by omega)
  · change G.Adj (p.getVert 3) (p.getVert 4); exact p.adj_getVert_succ (by omega)
  · change G.Adj (p.getVert 4) (p.getVert 0)
    have h45 : G.Adj (p.getVert 4) (p.getVert 5) := p.adj_getVert_succ (by omega)
    have h50 : p.getVert 5 = p.getVert 0 := by rw [← hp5, p.getVert_length, p.getVert_zero]
    rwa [h50] at h45

private lemma case_triangleFree_not_bipartite {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    (hnoiso : ∀ v : V, ∃ w : V, G.Adj v w)
    (htf : G.CliqueFree 3) (hnc : ¬ G.Colorable 2) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  obtain ⟨x, hx⟩ := exists_c5_of_triangleFree_not_colorable h2k2 htf hnc
  have hnotri : ∀ u v w : V, G.Adj u v → G.Adj v w → ¬ G.Adj u w := by
    intro u v w huv hvw huw
    have hcl : G.IsNClique 3 ({u, v, w} : Finset V) := by
      refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
        · exact absurd rfl hab
        · exact huv
        · exact huw
        · exact huv.symm
        · exact absurd rfl hab
        · exact hvw
        · exact huw.symm
        · exact hvw.symm
        · exact absurd rfl hab
      · rw [Finset.card_insert_of_notMem (by simp [huv.ne, huw.ne]),
          Finset.card_insert_of_notMem (by simp [hvw.ne]), Finset.card_singleton]
    exact htf {u, v, w} hcl
  have hno_adj_pair : ∀ v : V, ∀ i : ZMod 5, ¬ (G.Adj v (x i) ∧ G.Adj v (x (i + 1))) := by
    intro v i ⟨h1, h2⟩
    exact hnotri v (x i) (x (i + 1)) h1 (hx i) h2
  have hx_step : ∀ i : ZMod 5, G.Adj (x (i + 1)) (x (i + 2)) := by
    intro i; have h := hx (i + 1); rwa [show (i + 1 : ZMod 5) + 1 = i + 2 by ring] at h
  have hx_step2 : ∀ i : ZMod 5, G.Adj (x (i + 2)) (x (i + 3)) := by
    intro i; have h := hx (i + 2); rwa [show (i + 2 : ZMod 5) + 1 = i + 3 by ring] at h
  have hx_nonadj2 : ∀ i : ZMod 5, ¬ G.Adj (x i) (x (i + 2)) :=
    fun i h => hnotri _ _ _ (hx i) (hx_step i) h
  have hx_nonadj3 : ∀ i : ZMod 5, ¬ G.Adj (x i) (x (i + 3)) := by
    intro i h
    have h2 : (i + 3 : ZMod 5) + 2 = i := by
      have : (5 : ZMod 5) = 0 := by decide
      linear_combination this
    exact hx_nonadj2 (i + 3) (by rw [h2]; exact h.symm)
  have hx_inj : Function.Injective x := by
    intro i j hij
    have hcases : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨ j - i = 4 := by
      have : ∀ k : ZMod 5, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by decide
      exact this (j - i)
    rcases hcases with h | h | h | h | h
    · exact (sub_eq_zero.1 h).symm
    · exfalso
      have hj : j = i + 1 := eq_add_of_sub_eq' h
      rw [hj] at hij; exact (hx i).ne hij
    · exfalso
      have hj : j = i + 2 := eq_add_of_sub_eq' h
      rw [hj] at hij
      have h1 := hx_step2 i; rw [← hij] at h1; exact hx_nonadj3 i h1
    · exfalso
      have hj : j = i + 3 := eq_add_of_sub_eq' h
      rw [hj] at hij
      have h1 := hx_step2 i; rw [← hij] at h1; exact hx_nonadj2 i h1.symm
    · exfalso
      have hj : j = i + 4 := eq_add_of_sub_eq' h
      rw [hj] at hij
      have h1 : G.Adj (x (i + 4)) (x i) := by
        have h' := hx (i + 4)
        have h5 : (i + 4 : ZMod 5) + 1 = i := by
          have : (5 : ZMod 5) = 0 := by decide
          linear_combination this
        rwa [h5] at h'
      exact h1.ne hij.symm
  have hex_nbr : ∀ v : V, ∃ i : ZMod 5, G.Adj v (x i) := by
    intro v
    by_contra hno
    push Not at hno
    obtain ⟨w, hvw⟩ := hnoiso v
    have hw_cov : ∀ i : ZMod 5, G.Adj w (x i) ∨ G.Adj w (x (i + 1)) := by
      intro i
      have hv_ne : ∀ j : ZMod 5, v ≠ x j := by
        intro j rfl; exact hno (j + 1) (hx j)
      have hw_ne : ∀ j : ZMod 5, w ≠ x j := by
        intro j rfl; exact hno j hvw
      rcases h2k2 v w (x i) (x (i + 1)) hvw (hx i) with h | h | h | h | h | h | h | h
      · exact absurd h (hv_ne i)
      · exact absurd h (hv_ne (i + 1))
      · exact absurd h (hw_ne i)
      · exact absurd h (hw_ne (i + 1))
      · exact absurd h (hno i)
      · exact absurd h (hno (i + 1))
      · exact Or.inl h
      · exact Or.inr h
    have h0 : G.Adj w (x 0) ∨ G.Adj w (x 1) := by simpa using hw_cov 0
    have h1 : G.Adj w (x 1) ∨ G.Adj w (x 2) := by
      have := hw_cov 1; rwa [show (1 : ZMod 5) + 1 = 2 by decide] at this
    have h2 : G.Adj w (x 2) ∨ G.Adj w (x 3) := by
      have := hw_cov 2; rwa [show (2 : ZMod 5) + 1 = 3 by decide] at this
    have h3 : G.Adj w (x 3) ∨ G.Adj w (x 4) := by
      have := hw_cov 3; rwa [show (3 : ZMod 5) + 1 = 4 by decide] at this
    have h4 : G.Adj w (x 4) ∨ G.Adj w (x 0) := by
      have := hw_cov 4; rwa [show (4 : ZMod 5) + 1 = 0 by decide] at this
    have hc : ∀ i : ZMod 5, G.Adj w (x i) → ¬ G.Adj w (x (i + 1)) :=
      fun i hi h1' => hno_adj_pair w i ⟨hi, h1'⟩
    have hc0 : G.Adj w (x 0) → ¬ G.Adj w (x 1) := by simpa using hc 0
    have hc1 : G.Adj w (x 1) → ¬ G.Adj w (x 2) := by
      have := hc 1; rwa [show (1 : ZMod 5) + 1 = 2 by decide] at this
    have hc2 : G.Adj w (x 2) → ¬ G.Adj w (x 3) := by
      have := hc 2; rwa [show (2 : ZMod 5) + 1 = 3 by decide] at this
    have hc3 : G.Adj w (x 3) → ¬ G.Adj w (x 4) := by
      have := hc 3; rwa [show (3 : ZMod 5) + 1 = 4 by decide] at this
    have hc4 : G.Adj w (x 4) → ¬ G.Adj w (x 0) := by
      have := hc 4; rwa [show (4 : ZMod 5) + 1 = 0 by decide] at this
    tauto
  have hex_pair : ∀ v : V, ∃ j : ZMod 5, G.Adj v (x (j - 1)) ∧ G.Adj v (x (j + 1)) := by
    intro v
    obtain ⟨i, hi⟩ := hex_nbr v
    have h23 : G.Adj (x (i + 2)) (x (i + 3)) := hx_step2 i
    have hne2 : v ≠ x (i + 2) := by rintro rfl; exact hx_nonadj2 i hi.symm
    have hne3 : v ≠ x (i + 3) := by rintro rfl; exact hx_nonadj3 i hi.symm
    have hi2 : i ≠ i + 2 := by
      intro h; have : (2 : ZMod 5) = 0 := by linear_combination -h
      exact absurd this (by decide)
    have hi3 : i ≠ i + 3 := by
      intro h; have : (3 : ZMod 5) = 0 := by linear_combination -h
      exact absurd this (by decide)
    rcases h2k2 v (x i) (x (i + 2)) (x (i + 3)) hi h23 with h | h | h | h | h | h | h | h
    · exact absurd h hne2
    · exact absurd h hne3
    · exact absurd (hx_inj h) hi2
    · exact absurd (hx_inj h) hi3
    · refine ⟨i + 1, ?_, ?_⟩
      · rwa [show (i + 1 : ZMod 5) - 1 = i by ring]
      · rwa [show (i + 1 : ZMod 5) + 1 = i + 2 by ring]
    · refine ⟨i - 1, ?_, ?_⟩
      · have heq : (i - 1 : ZMod 5) - 1 = i + 3 := by
          have : (5 : ZMod 5) = 0 := by decide
          linear_combination -this
        rwa [heq]
      · rwa [show (i - 1 : ZMod 5) + 1 = i by ring]
    · exact absurd h (hx_nonadj2 i)
    · exact absurd h (hx_nonadj3 i)
  let A : ZMod 5 → Finset V :=
    fun j => Finset.univ.filter (fun v => G.Adj v (x (j - 1)) ∧ G.Adj v (x (j + 1)))
  have hA_disj : ∀ j k : ZMod 5, j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro v hvj hvk
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hvj hvk
    have h5 : (5 : ZMod 5) = 0 := by decide
    have hk : k - j ≠ 0 := sub_ne_zero.2 hjk.symm
    have hcases : k - j = 0 ∨ k - j = 1 ∨ k - j = 2 ∨ k - j = 3 ∨ k - j = 4 := by
      have : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
      exact this (k - j)
    rcases hcases with h | h | h | h | h
    · exact hk h
    · have hk' : k = j + 1 := eq_add_of_sub_eq' h
      subst hk'
      exact hno_adj_pair v (j + 1) ⟨hvj.2, hvk.2⟩
    · have hk' : k = j + 2 := eq_add_of_sub_eq' h
      subst hk'
      have hvk2 : G.Adj v (x (j + 3)) := by
        have h' := hvk.2; rwa [show (j + 2 : ZMod 5) + 1 = j + 3 by ring] at h'
      have hvj1 : G.Adj v (x ((j + 3) + 1)) := by
        have heq : (j + 3 : ZMod 5) + 1 = j - 1 := by linear_combination h5
        rw [heq]; exact hvj.1
      exact hno_adj_pair v (j + 3) ⟨hvk2, hvj1⟩
    · have hk' : k = j + 3 := eq_add_of_sub_eq' h
      subst hk'
      have hvk1 : G.Adj v (x ((j + 1) + 1)) := by
        have h' := hvk.1; rwa [show (j + 3 : ZMod 5) - 1 = (j + 1) + 1 by ring] at h'
      exact hno_adj_pair v (j + 1) ⟨hvj.2, hvk1⟩
    · have hk' : k = j + 4 := eq_add_of_sub_eq' h
      subst hk'
      have hvk1 : G.Adj v (x (j + 3)) := by
        have h' := hvk.1; rwa [show (j + 4 : ZMod 5) - 1 = j + 3 by ring] at h'
      have hvj1 : G.Adj v (x ((j + 3) + 1)) := by
        have heq : (j + 3 : ZMod 5) + 1 = j - 1 := by linear_combination h5
        rw [heq]; exact hvj.1
      exact hno_adj_pair v (j + 3) ⟨hvk1, hvj1⟩
  have hA_ind : ∀ j : ZMod 5, ∀ u ∈ A j, ∀ v ∈ A j, ¬ G.Adj u v := by
    intro j u hu v hv huv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    exact hnotri u v (x (j - 1)) huv hv.1 hu.1
  have hA_no2 : ∀ j : ZMod 5, ∀ u ∈ A j, ∀ v ∈ A (j + 2), ¬ G.Adj u v := by
    intro j u hu v hv huv
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
    have hv1 : G.Adj v (x (j + 1)) := by
      have h' := hv.1; rwa [show (j + 2 : ZMod 5) - 1 = j + 1 by ring] at h'
    exact hnotri u v (x (j + 1)) huv hv1 hu.2
  have hdeg_sum : ∀ j : ZMod 5, (A (j - 1)).card + (A (j + 1)).card ≤ d := by
    intro j
    have hd : Disjoint (A (j - 1)) (A (j + 1)) := hA_disj _ _ (by
      intro h; have : (2 : ZMod 5) = 0 := by linear_combination -h
      exact absurd this (by decide))
    rw [← Finset.card_union_of_disjoint hd]
    refine (Finset.card_le_card ?_).trans (hdeg (x j))
    intro v hv
    simp only [Finset.mem_union, A, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨_, h2⟩ | ⟨h1, _⟩
    · rw [show (j - 1 : ZMod 5) + 1 = j by ring] at h2; exact h2.symm
    · rw [show (j + 1 : ZMod 5) - 1 = j by ring] at h1; exact h1.symm
  have hE_cov : G.edgeFinset ⊆ Finset.univ.biUnion (fun j : ZMod 5 =>
      edgesBetween G (A j) (A (j + 1))) := by
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨ju, hju⟩ := hex_pair u
      obtain ⟨jv, hjv⟩ := hex_pair v
      have huA : u ∈ A ju := by simp [A, hju]
      have hvA : v ∈ A jv := by simp [A, hjv]
      rw [Finset.mem_biUnion]
      have h5 : (5 : ZMod 5) = 0 := by decide
      have hcases : jv - ju = 0 ∨ jv - ju = 1 ∨ jv - ju = 2 ∨ jv - ju = 3 ∨ jv - ju = 4 := by
        have : ∀ t : ZMod 5, t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by decide
        exact this (jv - ju)
      rcases hcases with h | h | h | h | h
      · have hjeq : jv = ju := eq_of_sub_eq_zero h
        subst hjeq; exact absurd he (hA_ind jv u huA v hvA)
      · have : jv = ju + 1 := eq_add_of_sub_eq' h
        subst this
        exact ⟨ju, Finset.mem_univ _, by
          simp only [edgesBetween, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
          exact ⟨he, ⟨u, huA, by simp⟩, ⟨v, hvA, by simp⟩⟩⟩
      · have : jv = ju + 2 := eq_add_of_sub_eq' h
        subst this; exact absurd he (hA_no2 ju u huA v hvA)
      · have : ju = jv + 2 := by
          have : jv = ju + 3 := eq_add_of_sub_eq' h
          linear_combination -this - h5
        subst this; exact absurd he.symm (hA_no2 jv v hvA u huA)
      · have : ju = jv + 1 := by
          have : jv = ju + 4 := eq_add_of_sub_eq' h
          linear_combination -this - h5
        subst this
        exact ⟨jv, Finset.mem_univ _, by
          simp only [edgesBetween, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
          exact ⟨he, ⟨v, hvA, by simp⟩, ⟨u, huA, by simp⟩⟩⟩
  have hE_le : G.edgeFinset.card ≤ ∑ j : ZMod 5, (A j).card * (A (j + 1)).card := by
    calc G.edgeFinset.card
        ≤ (Finset.univ.biUnion (fun j : ZMod 5 => edgesBetween G (A j) (A (j + 1)))).card :=
          Finset.card_le_card hE_cov
      _ ≤ ∑ j : ZMod 5, (edgesBetween G (A j) (A (j + 1))).card := Finset.card_biUnion_le
      _ ≤ ∑ j : ZMod 5, (A j).card * (A (j + 1)).card := by
          apply Finset.sum_le_sum
          intro j _
          have hd : Disjoint (A j) (A (j + 1)) := hA_disj j (j + 1) (by
            intro h; have : (1 : ZMod 5) = 0 := by linear_combination -h
            exact absurd this (by decide))
          rw [card_edgesBetween_left G hd]
          calc ∑ a ∈ A j, ((A (j + 1)).filter (G.Adj a)).card
              ≤ ∑ _a ∈ A j, (A (j + 1)).card :=
                Finset.sum_le_sum (fun a _ => Finset.card_filter_le _ _)
            _ = (A j).card * (A (j + 1)).card := by rw [Finset.sum_const, smul_eq_mul]
  have hsum_eq : ∑ j : ZMod 5, (A j).card * (A (j + 1)).card =
      (A 0).card * (A 1).card + (A 1).card * (A 2).card +
      (A 2).card * (A 3).card + (A 3).card * (A 4).card +
      (A 4).card * (A 0).card := by
    have hu5 : (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
    rw [hu5]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have e0 : (0 : ZMod 5) + 1 = 1 := by decide
    have e1 : (1 : ZMod 5) + 1 = 2 := by decide
    have e2 : (2 : ZMod 5) + 1 = 3 := by decide
    have e3 : (3 : ZMod 5) + 1 = 4 := by decide
    have e4 : (4 : ZMod 5) + 1 = 0 := by decide
    rw [e0, e1, e2, e3, e4]
    ring
  have h0 : (A 4).card + (A 1).card ≤ d := by
    have := hdeg_sum 0
    rwa [show (0 : ZMod 5) - 1 = 4 by decide, show (0 : ZMod 5) + 1 = 1 by decide] at this
  have h1 : (A 0).card + (A 2).card ≤ d := by
    have := hdeg_sum 1
    rwa [show (1 : ZMod 5) - 1 = 0 by decide, show (1 : ZMod 5) + 1 = 2 by decide] at this
  have h2 : (A 1).card + (A 3).card ≤ d := by
    have := hdeg_sum 2
    rwa [show (2 : ZMod 5) - 1 = 1 by decide, show (2 : ZMod 5) + 1 = 3 by decide] at this
  have h3 : (A 2).card + (A 4).card ≤ d := by
    have := hdeg_sum 3
    rwa [show (3 : ZMod 5) - 1 = 2 by decide, show (3 : ZMod 5) + 1 = 4 by decide] at this
  have h4 : (A 3).card + (A 0).card ≤ d := by
    have := hdeg_sum 4
    rwa [show (4 : ZMod 5) - 1 = 3 by decide, show (4 : ZMod 5) + 1 = 0 by decide] at this
  have hineq := c5_blowup_ineq h0 h1 h2 h3 h4
  linarith

end CaseTriangleFree

/- Theorem 3: Dominating Maximum Clique (`p ≥ 3`) -/

section DominatingClique

variable {V : Type*} [Fintype V] [DecidableEq V]

private def IsMaxClique (G : SimpleGraph V) (K : Finset V) : Prop :=
  G.IsClique (K : Set V) ∧ ∀ K' : Finset V, G.IsClique (K' : Set V) → K'.card ≤ K.card

/-- Theorem 3 (CGTT90): If `G` is `2K2`-free with no isolated vertices and `¬ G.CliqueFree 3`,
    then `G` has a maximum clique `K` of size `p ≥ 3` that dominates every vertex of `G`. -/
private lemma exists_dominating_maxClique {G : SimpleGraph V} [DecidableRel G.Adj]
    (h2k2 : Is2K2Free G) (hnoiso : ∀ v : V, ∃ w : V, G.Adj v w)
    (htri : ¬ G.CliqueFree 3) :
    ∃ K : Finset V, IsMaxClique G K ∧ 3 ≤ K.card ∧
      ∀ v : V, v ∉ K → ∃ u ∈ K, G.Adj v u := by
  classical
  have hcl3 : ∃ K : Finset V, G.IsClique (K : Set V) ∧ 3 ≤ K.card := by
    rw [SimpleGraph.CliqueFree] at htri
    push Not at htri
    rcases htri with ⟨K, hK⟩
    exact ⟨K, hK.1, by rw [hK.2]⟩
  let allCliques : Finset (Finset V) := Finset.univ.filter (fun K => G.IsClique (K : Set V))
  have hall_ne : allCliques.Nonempty := by
    rcases hcl3 with ⟨K, hK, _⟩
    exact ⟨K, by simp [allCliques, hK]⟩
  obtain ⟨Kmax, hKmax_mem, hKmax⟩ := Finset.exists_max_image allCliques Finset.card hall_ne
  set p := Kmax.card
  have hp3 : 3 ≤ p := by
    rcases hcl3 with ⟨K, hK, hK3⟩
    exact hK3.trans (hKmax K (by simp [allCliques, hK]))
  let maxCliques : Finset (Finset V) := allCliques.filter (fun K => K.card = p)
  have hmax_ne : maxCliques.Nonempty := ⟨Kmax, by simp [maxCliques, hKmax_mem, p]⟩
  let dom (K : Finset V) : Finset V :=
    Finset.univ.filter (fun v => v ∈ K ∨ ∃ u ∈ K, G.Adj v u)
  obtain ⟨K, hKmem, hKdom_max⟩ := Finset.exists_max_image maxCliques (fun K => (dom K).card) hmax_ne
  simp only [maxCliques, allCliques, Finset.mem_filter, Finset.mem_univ, true_and] at hKmem
  rcases hKmem with ⟨hKcl, hKcard⟩
  have hKisMax : IsMaxClique G K := by
    refine ⟨hKcl, fun K' hK' => ?_⟩
    rw [hKcard]
    exact hKmax K' (by simp [allCliques, hK'])
  refine ⟨K, hKisMax, by omega, ?_⟩
  by_contra hnotdom
  push Not at hnotdom
  rcases hnotdom with ⟨z₀, hz₀K, hz₀no⟩
  obtain ⟨y₀, hy₀adj⟩ := hnoiso z₀
  have hy₀K : y₀ ∉ K := fun h => hz₀no y₀ h hy₀adj
  have huniq_nonnbr : ∃ x₁ ∈ K, ¬ G.Adj y₀ x₁ ∧ ∀ x ∈ K, x ≠ x₁ → G.Adj y₀ x := by
    have hex_non : ∃ x₁ ∈ K, ¬ G.Adj y₀ x₁ := by
      by_contra hall
      push Not at hall
      have hcl' : G.IsClique ((insert y₀ K : Finset V) : Set V) := by
        intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact hall b hb
        · exact (hall a ha).symm
        · exact hKcl ha hb hab
      have hle := hKisMax.2 (insert y₀ K) hcl'
      rw [Finset.card_insert_of_notMem hy₀K] at hle
      omega
    rcases hex_non with ⟨x₁, hx₁K, hny₀x₁⟩
    refine ⟨x₁, hx₁K, hny₀x₁, fun x hxK hxx₁ => ?_⟩
    by_contra hny₀x
    have hx₁x : G.Adj x₁ x := hKcl hx₁K hxK hxx₁.symm
    rcases h2k2 z₀ y₀ x₁ x hy₀adj hx₁x with h | h | h | h | h | h | h | h
    · exact hz₀K (h ▸ hx₁K)
    · exact hz₀K (h ▸ hxK)
    · exact hy₀K (h ▸ hx₁K)
    · exact hy₀K (h ▸ hxK)
    · exact hz₀no x₁ hx₁K h
    · exact hz₀no x hxK h
    · exact hny₀x₁ h
    · exact hny₀x h
  rcases huniq_nonnbr with ⟨x₁, hx₁K, hny₀x₁, hy₀rest⟩
  let K' : Finset V := insert y₀ (K.erase x₁)
  have hK'cl : G.IsClique (K' : Set V) := by
    intro a ha b hb hab
    simp only [K', Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_sdiff,
      Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | ⟨haK, hax₁⟩ <;> rcases hb with rfl | ⟨hbK, hbx₁⟩
    · exact absurd rfl hab
    · exact hy₀rest b hbK hbx₁
    · exact (hy₀rest a haK hax₁).symm
    · exact hKcl haK hbK hab
  have hK'card : K'.card = p := by
    have hy₀e : y₀ ∉ K.erase x₁ := fun h => hy₀K (Finset.mem_of_mem_erase h)
    rw [Finset.card_insert_of_notMem hy₀e, Finset.card_erase_of_mem hx₁K, hKcard]
    omega
  have hK'mem : K' ∈ maxCliques := by simp [maxCliques, allCliques, hK'cl, hK'card]
  have hdom_le : (dom K').card ≤ (dom K).card := hKdom_max K' hK'mem
  have hz₀_in_K' : z₀ ∈ dom K' := by
    simp only [dom, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Or.inr ⟨y₀, Finset.mem_insert_self _ _, hy₀adj⟩
  have hz₀_not_K : z₀ ∉ dom K := by
    simp only [dom, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and]
    exact ⟨hz₀K, hz₀no⟩
  have hnsub : ¬ (dom K ⊆ dom K') := by
    intro hsub
    have hssub : dom K ⊂ dom K' :=
      Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => hz₀_not_K (heq ▸ hz₀_in_K')⟩
    exact absurd (Finset.card_lt_card hssub) (not_lt.2 hdom_le)
  rw [Finset.not_subset] at hnsub
  rcases hnsub with ⟨y₁, hy₁domK, hy₁ndomK'⟩
  simp only [dom, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁domK hy₁ndomK'
  push Not at hy₁ndomK'
  rcases hy₁ndomK' with ⟨hy₁nK', hy₁nadjK'⟩
  have hcard_erase : 2 ≤ (K.erase x₁).card := by
    rw [Finset.card_erase_of_mem hx₁K, hKcard]; omega
  obtain ⟨x₂, hx₂e, x₃, hx₃e, hx₂₃⟩ := Finset.one_lt_card.1 (by omega : 1 < (K.erase x₁).card)
  have hx₂K' : x₂ ∈ K' := Finset.mem_insert_of_mem hx₂e
  have hx₃K' : x₃ ∈ K' := Finset.mem_insert_of_mem hx₃e
  have hx₂K : x₂ ∈ K := Finset.mem_of_mem_erase hx₂e
  have hx₃K : x₃ ∈ K := Finset.mem_of_mem_erase hx₃e
  have hx₂x₁ : x₂ ≠ x₁ := Finset.ne_of_mem_erase hx₂e
  have hy₁x₁ : y₁ ≠ x₁ := by
    rintro rfl
    exact hy₁nadjK' x₂ hx₂K' (hKcl hx₁K hx₂K hx₂x₁.symm)
  have hy₁K : y₁ ∉ K := by
    intro hy₁K
    exact hy₁nK' (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hy₁x₁, hy₁K⟩))
  have hy₁adjx₁ : G.Adj y₁ x₁ := by
    rcases hy₁domK with h | ⟨u, huK, huadj⟩
    · exact absurd h hy₁K
    · by_cases hux₁ : u = x₁
      · exact hux₁ ▸ huadj
      · exact absurd huadj (hy₁nadjK' u (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hux₁, huK⟩)))
  have hy₁y₀ : y₁ ≠ y₀ := fun h => hy₁nK' (h ▸ Finset.mem_insert_self _ _)
  have hny₁y₀ : ¬ G.Adj y₁ y₀ := hy₁nadjK' y₀ (Finset.mem_insert_self _ _)
  have hz₀y₁ : G.Adj z₀ y₁ := by
    rcases h2k2 z₀ y₀ x₁ y₁ hy₀adj hy₁adjx₁.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => hz₀K (h' ▸ hx₁K))
    · exact absurd h (fun h' => hz₀_not_K (h' ▸ by simp [dom, hy₁domK]))
    · exact absurd h (fun h' => hy₀K (h' ▸ hx₁K))
    · exact absurd h hy₁y₀.symm
    · exact absurd h (hz₀no x₁ hx₁K)
    · exact h
    · exact absurd h hny₀x₁
    · exact absurd h.symm hny₁y₀
  have hx₂x₃adj : G.Adj x₂ x₃ := hKcl hx₂K hx₃K hx₂₃
  rcases h2k2 z₀ y₁ x₂ x₃ hz₀y₁ hx₂x₃adj with h | h | h | h | h | h | h | h
  · exact hz₀K (h ▸ hx₂K)
  · exact hz₀K (h ▸ hx₃K)
  · exact hy₁nK' (h ▸ hx₂K')
  · exact hy₁nK' (h ▸ hx₃K')
  · exact hz₀no x₂ hx₂K h
  · exact hz₀no x₃ hx₃K h
  · exact hy₁nadjK' x₂ hx₂K' h
  · exact hy₁nadjK' x₃ hx₃K' h

end DominatingClique

/- Cases (iii), (iv), (v): Dominating Maximum Clique of size `p ≥ 5`, `p = 4`, `p = 3` -/

section CaseClique

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Common properties of a dominating max clique `K` of size `p ≥ 3`. -/
private lemma dominating_clique_bounds {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    {K : Finset V} (hmax : IsMaxClique G K)
    (hdom : ∀ v : V, v ∉ K → ∃ u ∈ K, G.Adj v u) :
    2 * (edgesIn G K).card = K.card * (K.card - 1) ∧
    (∀ y ∈ Finset.univ \ K, 1 ≤ (K.filter (G.Adj y)).card ∧ (K.filter (G.Adj y)).card ≤ K.card - 1) ∧
    (∀ y ∈ Finset.univ \ K, ((Finset.univ \ K).filter (G.Adj y)).card + (K.filter (G.Adj y)).card ≤ d) ∧
    (edgesBetween G K (Finset.univ \ K)).card ≤ K.card * (d - (K.card - 1)) ∧
    (∀ e ∈ edgesIn G (Finset.univ \ K),
      K.card - 1 ≤ Sym2.lift ⟨fun u v => (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card,
        fun _ _ => add_comm _ _⟩ e) ∧
    ∑ e ∈ edgesIn G (Finset.univ \ K),
      Sym2.lift ⟨fun u v => (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card,
        fun _ _ => add_comm _ _⟩ e ≤
      (d - 1) * (edgesBetween G K (Finset.univ \ K)).card := by
  set Y := Finset.univ \ K
  set w : V → ℕ := fun y => (K.filter (G.Adj y)).card
  have hdisj : Disjoint K Y := disjoint_sdiff_self_right
  have hEK : 2 * (edgesIn G K).card = K.card * (K.card - 1) := by
    rw [two_mul_card_edgesIn]
    have hsum : ∀ u ∈ K, (K.filter (G.Adj u)).card = K.card - 1 := by
      intro u hu
      have heq : K.filter (G.Adj u) = K.erase u := by
        ext v; simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hvK, huv⟩; exact ⟨huv.ne.symm, hvK⟩
        · rintro ⟨hvu, hvK⟩; exact ⟨hvK, hmax.1 hu hvK hvu.symm⟩
      rw [heq, Finset.card_erase_of_mem hu]
    rw [Finset.sum_congr rfl hsum, Finset.sum_const, smul_eq_mul]
  have hw_bounds : ∀ y ∈ Y, 1 ≤ w y ∧ w y ≤ K.card - 1 := by
    intro y hy
    have hyK : y ∉ K := (Finset.mem_sdiff.1 hy).2
    constructor
    · obtain ⟨u, huK, hyu⟩ := hdom y hyK
      exact Finset.card_pos.2 ⟨u, by simp [huK, hyu]⟩
    · have hlt : w y < K.card := by
        by_contra hge
        push Not at hge
        have heq : K.filter (G.Adj y) = K :=
          Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) hge
        have hcl' : G.IsClique ((insert y K : Finset V) : Set V) := by
          intro a ha b hb hab
          simp only [Finset.coe_insert, Set.mem_insert_iff] at ha hb
          rcases ha with rfl | ha <;> rcases hb with rfl | hb
          · exact absurd rfl hab
          · exact (Finset.mem_filter.1 (heq ▸ hb)).2
          · exact (Finset.mem_filter.1 (heq ▸ ha)).2.symm
          · exact hmax.1 ha hb hab
        have hle := hmax.2 (insert y K) hcl'
        rw [Finset.card_insert_of_notMem hyK] at hle
        omega
      omega
  have hdegY : ∀ y ∈ Y, (Y.filter (G.Adj y)).card + w y ≤ d := by
    intro y _
    have hd : Disjoint (Y.filter (G.Adj y)) (K.filter (G.Adj y)) :=
      Finset.disjoint_filter_filter hdisj.symm
    rw [← Finset.card_union_of_disjoint hd]
    refine (Finset.card_le_card ?_).trans (hdeg y)
    intro z hz
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
  have hEKY : (edgesBetween G K Y).card ≤ K.card * (d - (K.card - 1)) := by
    rw [card_edgesBetween_left G hdisj]
    calc ∑ x ∈ K, (Y.filter (G.Adj x)).card
        ≤ ∑ _x ∈ K, (d - (K.card - 1)) := by
          apply Finset.sum_le_sum
          intro x hxK
          have h1 : (K.filter (G.Adj x)).card = K.card - 1 := by
            have heq : K.filter (G.Adj x) = K.erase x := by
              ext v; simp only [Finset.mem_filter, Finset.mem_erase]
              constructor
              · rintro ⟨hvK, hxv⟩; exact ⟨hxv.ne.symm, hvK⟩
              · rintro ⟨hvx, hvK⟩; exact ⟨hvK, hmax.1 hxK hvK hvx.symm⟩
            rw [heq, Finset.card_erase_of_mem hxK]
          have hd : Disjoint (Y.filter (G.Adj x)) (K.filter (G.Adj x)) :=
            Finset.disjoint_filter_filter hdisj.symm
          have hsum : (Y.filter (G.Adj x)).card + (K.filter (G.Adj x)).card ≤ d := by
            rw [← Finset.card_union_of_disjoint hd]
            refine (Finset.card_le_card ?_).trans (hdeg x)
            intro z hz
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
            rcases hz with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
          omega
      _ = K.card * (d - (K.card - 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have hweight_ge : ∀ e ∈ edgesIn G Y,
      K.card - 1 ≤ Sym2.lift ⟨fun u v => w u + w v, fun _ _ => add_comm _ _⟩ e := by
    intro e he
    simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Sym2.lift_mk]
      by_contra hlt
      push Not at hlt
      have huK : u ∉ K := (Finset.mem_sdiff.1 (he.2 u (by simp))).2
      have hvK : v ∉ K := (Finset.mem_sdiff.1 (he.2 v (by simp))).2
      set U := K.filter (G.Adj u) ∪ K.filter (G.Adj v)
      have hUle : U.card ≤ w u + w v := Finset.card_union_le _ _
      have hUsub : U ⊆ K := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have hdiff : 2 ≤ (K \ U).card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.2 hUsub]; omega
      obtain ⟨x₁, hx₁, x₂, hx₂, hx₁₂⟩ := Finset.one_lt_card.1 (by omega : 1 < (K \ U).card)
      simp only [Finset.mem_sdiff, U, Finset.mem_union, Finset.mem_filter, not_or, not_and] at hx₁ hx₂
      have hx₁₂adj : G.Adj x₁ x₂ := hmax.1 hx₁.1 hx₂.1 hx₁₂
      rcases h2k2 u v x₁ x₂ he.1 hx₁₂adj with h | h | h | h | h | h | h | h
      · exact huK (h ▸ hx₁.1)
      · exact huK (h ▸ hx₂.1)
      · exact hvK (h ▸ hx₁.1)
      · exact hvK (h ▸ hx₂.1)
      · exact hx₁.2.1 hx₁.1 h
      · exact hx₂.2.1 hx₂.1 h
      · exact hx₁.2.2 hx₁.1 h
      · exact hx₂.2.2 hx₂.1 h
  have hsum_w : ∑ e ∈ edgesIn G Y, Sym2.lift ⟨fun u v => w u + w v, fun _ _ => add_comm _ _⟩ e ≤
      (d - 1) * (edgesBetween G K Y).card := by
    rw [sum_edge_weights, card_edgesBetween_right G hdisj]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro y hy
    have h1 := (hw_bounds y hy).1
    have h2 := hdegY y hy
    have hle : (Y.filter (G.Adj y)).card ≤ d - 1 := by omega
    calc w y * (Y.filter (G.Adj y)).card
        ≤ w y * (d - 1) := Nat.mul_le_mul_left _ hle
      _ = (d - 1) * w y := Nat.mul_comm _ _
  exact ⟨hEK, hw_bounds, hdegY, hEKY, hweight_ge, hsum_w⟩

/-- Case (iii): `p ≥ 5`. -/
private lemma case_p_ge_5 {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    {K : Finset V} (hmax : IsMaxClique G K)
    (hdom : ∀ v : V, v ∉ K → ∃ u ∈ K, G.Adj v u) (hp5 : 5 ≤ K.card) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  set p := K.card
  set Y := Finset.univ \ K
  obtain ⟨hEK, _, _, hEKY, hweight_ge, hsum_w⟩ := dominating_clique_bounds h2k2 hdeg hmax hdom
  have hpart := card_edgeFinset_partition G K
  have hpd : p - 1 ≤ d := by
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < K.card)
    have heq : K.filter (G.Adj x) = K.erase x := by
      ext v; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hvK, hxv⟩; exact ⟨hxv.ne.symm, hvK⟩
      · rintro ⟨hvx, hvK⟩; exact ⟨hvK, hmax.1 hx hvK hvx.symm⟩
    have hle : (K.filter (G.Adj x)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hdeg x)
    rw [heq, Finset.card_erase_of_mem hx] at hle; exact hle
  have hEY : (p - 1) * (edgesIn G Y).card ≤ (d - 1) * (edgesBetween G K Y).card := by
    calc (p - 1) * (edgesIn G Y).card
        = ∑ _e ∈ edgesIn G Y, (p - 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ e ∈ edgesIn G Y,
            Sym2.lift ⟨fun u v => (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card,
              fun _ _ => add_comm _ _⟩ e :=
          Finset.sum_le_sum (fun e he => hweight_ge e he)
      _ ≤ (d - 1) * (edgesBetween G K Y).card := hsum_w
  have hgoal_nat : 4 * (p - 1) * G.edgeFinset.card ≤ 5 * (p - 1) * d ^ 2 := by
    have hgoal : (4 * ((p : ℤ) - 1) * G.edgeFinset.card) ≤ 5 * ((p : ℤ) - 1) * (d : ℤ) ^ 2 := by
      have hp5z : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      have hpdz : (p : ℤ) - 1 ≤ d := by omega
      have hEK' : 2 * (edgesIn G K).card = p * (p - 1) := hEK
      have hEKz : (2 * (edgesIn G K).card : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
        zify [show 1 ≤ p by omega] at hEK'; exact hEK'
      have hEKY' : (edgesBetween G K Y).card ≤ p * (d - (p - 1)) := hEKY
      have hEKYz : ((edgesBetween G K Y).card : ℤ) ≤ (p : ℤ) * ((d : ℤ) - ((p : ℤ) - 1)) := by
        zify [show 1 ≤ p by omega, show p - 1 ≤ d by omega] at hEKY'; exact hEKY'
      have hEYz : ((p : ℤ) - 1) * (edgesIn G Y).card ≤ ((d : ℤ) - 1) * (edgesBetween G K Y).card := by
        zify [show 1 ≤ p by omega, show 1 ≤ d by omega] at hEY; exact hEY
      have hpartz : (G.edgeFinset.card : ℤ) =
          (edgesIn G K).card + (edgesBetween G K Y).card + (edgesIn G Y).card := by
        exact_mod_cast hpart
      nlinarith
    zify [show 1 ≤ p by omega]
    exact hgoal
  have hpos : 0 < p - 1 := by omega
  nlinarith

/-- Case (iv): `p = 4`. -/
private lemma case_p_eq_4 {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    {K : Finset V} (hmax : IsMaxClique G K)
    (hdom : ∀ v : V, v ∉ K → ∃ u ∈ K, G.Adj v u) (hp4 : K.card = 4) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  set Y := Finset.univ \ K
  obtain ⟨hEK, hw_bounds, hdegY, hEKY, hweight_ge, hsum_w⟩ :=
    dominating_clique_bounds h2k2 hdeg hmax hdom
  have hpart := card_edgeFinset_partition G K
  have hd3 : 3 ≤ d := by
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by omega : 0 < K.card)
    have heq : K.filter (G.Adj x) = K.erase x := by
      ext v; simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hvK, hxv⟩; exact ⟨hxv.ne.symm, hvK⟩
      · rintro ⟨hvx, hvK⟩; exact ⟨hvK, hmax.1 hx hvK hvx.symm⟩
    have hle : (K.filter (G.Adj x)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans (hdeg x)
    rw [heq, Finset.card_erase_of_mem hx, hp4] at hle; exact hle
  let wt : Sym2 V → ℕ :=
    Sym2.lift ⟨fun u v => (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card,
      fun _ _ => add_comm _ _⟩
  set E3 := (edgesIn G Y).filter (fun e => wt e = 3)
  set E4 := (edgesIn G Y).filter (fun e => wt e ≠ 3)
  have hE34 : (edgesIn G Y).card = E3.card + E4.card := by
    rw [← Finset.card_filter_add_card_filter_not (s := edgesIn G Y) (p := fun e => wt e = 3)]
  have hsum_split : 3 * E3.card + 4 * E4.card ≤ ∑ e ∈ edgesIn G Y, wt e := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := edgesIn G Y) (p := fun e => wt e = 3)]
    have h1 : 3 * E3.card = ∑ e ∈ E3, wt e := by
      rw [Finset.sum_congr rfl (fun e he => (Finset.mem_filter.1 he).2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have h2 : 4 * E4.card ≤ ∑ e ∈ E4, wt e := by
      calc 4 * E4.card = ∑ _e ∈ E4, 4 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ e ∈ E4, wt e := by
          apply Finset.sum_le_sum
          intro e he
          simp only [E4, Finset.mem_filter] at he
          have h3 : 3 ≤ wt e := by
            have := hweight_ge e he.1; rwa [hp4] at this
          have hne : wt e ≠ 3 := he.2
          omega
    exact Nat.add_le_add (le_of_eq h1) h2
  set A1 := Y.filter (fun y => (K.filter (G.Adj y)).card = 1)
  set A2 := Y.filter (fun y => (K.filter (G.Adj y)).card = 2)
  have hdisj12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro y h1 h2
    simp only [A1, A2, Finset.mem_filter] at h1 h2; omega
  have hindA1 : ∀ u ∈ A1, ∀ v ∈ A1, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [A1, Finset.mem_filter] at hu hv
    have he : s(u, v) ∈ edgesIn G Y := by
      simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
      refine ⟨huv, fun z hz => ?_⟩
      rw [Sym2.mem_iff] at hz; rcases hz with rfl | rfl <;> [exact hu.1; exact hv.1]
    have h3 := hweight_ge s(u, v) he
    rw [hp4] at h3; simp only [Sym2.lift_mk] at h3; omega
  have hE3_le : E3.card ≤ (d - 2) * (d - 1) := by
    by_cases hA2 : A2.Nonempty
    · obtain ⟨x, hxA2, hcov⟩ := theorem1_edge_cover h2k2 hdisj12 hindA1 hA2
      set C := Y.filter (G.Adj x)
      have hCcard : C.card ≤ d - 2 := by
        have hxY : x ∈ Y := (Finset.mem_filter.1 hxA2).1
        have hwx : (K.filter (G.Adj x)).card = 2 := (Finset.mem_filter.1 hxA2).2
        have hdx : C.card + (K.filter (G.Adj x)).card ≤ d := hdegY x hxY
        omega
      have hcovE3 : ∀ e ∈ E3, ∃ c ∈ C, c ∈ e := by
        intro e he
        simp only [E3, Finset.mem_filter] at he
        have heY := he.1
        simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at heY
        induction e using Sym2.ind with
        | _ u v =>
          have huY : u ∈ Y := heY.2 u (by simp)
          have hvY : v ∈ Y := heY.2 v (by simp)
          have hwu := hw_bounds u huY
          have hwv := hw_bounds v hvY
          have hwt : (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card = 3 := he.2
          have hcases : ((K.filter (G.Adj u)).card = 1 ∧ (K.filter (G.Adj v)).card = 2) ∨
              ((K.filter (G.Adj u)).card = 2 ∧ (K.filter (G.Adj v)).card = 1) := by omega
          rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rcases hcov u (Finset.mem_filter.2 ⟨huY, h1⟩) v (Finset.mem_filter.2 ⟨hvY, h2⟩) heY.1 with h | h
            · exact ⟨u, Finset.mem_filter.2 ⟨huY, h⟩, by simp⟩
            · exact ⟨v, Finset.mem_filter.2 ⟨hvY, h⟩, by simp⟩
          · rcases hcov v (Finset.mem_filter.2 ⟨hvY, h2⟩) u (Finset.mem_filter.2 ⟨huY, h1⟩) heY.1.symm with h | h
            · exact ⟨v, Finset.mem_filter.2 ⟨hvY, h⟩, by simp⟩
            · exact ⟨u, Finset.mem_filter.2 ⟨huY, h⟩, by simp⟩
      have hdegC : ∀ c ∈ C, (Y.filter (G.Adj c)).card ≤ d - 1 := by
        intro c hc
        have hcY : c ∈ Y := (Finset.mem_filter.1 hc).1
        have h1 : 1 ≤ (K.filter (G.Adj c)).card := (hw_bounds c hcY).1
        have h2 : (Y.filter (G.Adj c)).card + (K.filter (G.Adj c)).card ≤ d := hdegY c hcY
        omega
      calc E3.card ≤ C.card * (d - 1) :=
            card_edges_le_of_cover G (Finset.filter_subset _ _) hcovE3 hdegC
        _ ≤ (d - 2) * (d - 1) := Nat.mul_le_mul_right _ hCcard
    · rw [Finset.not_nonempty_iff_eq_empty] at hA2
      have hE3_0 : E3 = ∅ := by
        ext e; simp only [E3, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro heY hwt
        simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at heY
        induction e using Sym2.ind with
        | _ u v =>
          have huY : u ∈ Y := heY.2 u (by simp)
          have hvY : v ∈ Y := heY.2 v (by simp)
          have hwu := hw_bounds u huY
          have hwv := hw_bounds v hvY
          have hwt' : (K.filter (G.Adj u)).card + (K.filter (G.Adj v)).card = 3 := hwt
          have h2 : (K.filter (G.Adj u)).card = 2 ∨ (K.filter (G.Adj v)).card = 2 := by omega
          rcases h2 with h | h
          · have : u ∈ A2 := Finset.mem_filter.2 ⟨huY, h⟩
            rw [hA2] at this; exact Finset.notMem_empty _ this
          · have : v ∈ A2 := Finset.mem_filter.2 ⟨hvY, h⟩
            rw [hA2] at this; exact Finset.notMem_empty _ this
      rw [hE3_0, Finset.card_empty]; exact Nat.zero_le _
  have hgoal : (4 * G.edgeFinset.card : ℤ) ≤ (5 * d ^ 2 : ℤ) := by
    have hd3z : (3 : ℤ) ≤ d := by exact_mod_cast hd3
    have hEKz : (edgesIn G K).card = 6 := by rw [hp4] at hEK; omega
    have hEKYz : ((edgesBetween G K Y).card : ℤ) ≤ 4 * ((d : ℤ) - 3) := by
      rw [hp4] at hEKY; zify [show 3 ≤ d by omega] at hEKY; exact hEKY
    have hsum_wz : (3 * E3.card + 4 * E4.card : ℤ) ≤ ((d : ℤ) - 1) * (edgesBetween G K Y).card := by
      have := hsum_split.trans hsum_w
      zify [show 1 ≤ d by omega] at this; exact this
    have hE3z : (E3.card : ℤ) ≤ ((d : ℤ) - 2) * ((d : ℤ) - 1) := by
      zify [show 2 ≤ d by omega, show 1 ≤ d by omega] at hE3_le; exact hE3_le
    have hpartz : (G.edgeFinset.card : ℤ) =
        6 + (edgesBetween G K Y).card + (E3.card + E4.card) := by
      rw [hpart, hEKz, hE34]; push_cast; ring
    nlinarith
  exact_mod_cast hgoal

/- Modular helpers for Case (v) (`p = 3`) -/

private lemma p3_claim5_aux {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {K P Q R : Finset V} {xp xq xr : V}
    (h2k2 : Is2K2Free G)
    (hdegY : ∀ y ∈ Finset.univ \ K, ((Finset.univ \ K).filter (G.Adj y)).card ≤ d - 1)
    (hPY : P ⊆ Finset.univ \ K) (hQY : Q ⊆ Finset.univ \ K) (hRY : R ⊆ Finset.univ \ K)
    (hxpK : xp ∈ K) (hxqK : xq ∈ K)
    (hP : ∀ u ∈ P, G.Adj u xp ∧ ¬ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hQ : ∀ u ∈ Q, ¬ G.Adj u xp ∧ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hR : ∀ u ∈ R, ¬ G.Adj u xp ∧ ¬ G.Adj u xq ∧ G.Adj u xr)
    (hPQcard : d < P.card + Q.card) (hQpos : 0 < Q.card)
    (hPR : ∃ u ∈ P, ∃ z ∈ R, G.Adj u z) :
    ∃ u ∈ P, ∃ v ∈ Q, G.Adj u v := by
  rcases hPR with ⟨u0, hu0P, z, hzR, hu0z⟩
  by_contra hno
  push Not at hno
  have hzQ : ∀ y ∈ Q, G.Adj z y := by
    intro y hyQ
    rcases h2k2 u0 z xq y hu0z (hQ y hyQ).2.1.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hPY hu0P)).2 (h' ▸ hxqK))
    · exact absurd (h ▸ (hP u0 hu0P).1) (hQ y hyQ).1
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hRY hzR)).2 (h' ▸ hxqK))
    · exact absurd (h ▸ (hR z hzR).2.2) (hQ y hyQ).2.2
    · exact absurd h (hP u0 hu0P).2.1
    · exact absurd h (hno u0 hu0P y hyQ)
    · exact absurd h (hR z hzR).2.1
    · exact h
  obtain ⟨y0, hy0Q⟩ := Finset.card_pos.1 hQpos
  have hzy0 : G.Adj z y0 := hzQ y0 hy0Q
  have hzP : ∀ u ∈ P, G.Adj z u := by
    intro u huP
    rcases h2k2 z y0 xp u hzy0 (hP u huP).1.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hRY hzR)).2 (h' ▸ hxpK))
    · exact absurd (h ▸ (hR z hzR).2.2) (hP u huP).2.2
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hQY hy0Q)).2 (h' ▸ hxpK))
    · exact absurd (h ▸ (hQ y0 hy0Q).2.1) (hP u huP).2.1
    · exact absurd h (hR z hzR).1
    · exact h
    · exact absurd h (hQ y0 hy0Q).1
    · exact absurd h.symm (hno u huP y0 hy0Q)
  have hdisjPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]; intro v hvP hvQ
    exact (hQ v hvQ).1 (hP v hvP).1
  have hsub : P ∪ Q ⊆ (Finset.univ \ K).filter (G.Adj z) := by
    intro v hv
    simp only [Finset.mem_union, Finset.mem_filter] at hv ⊢
    rcases hv with h | h
    · exact ⟨hPY h, hzP v h⟩
    · exact ⟨hQY h, hzQ v h⟩
  have hle : P.card + Q.card ≤ d - 1 := by
    rw [← Finset.card_union_of_disjoint hdisjPQ]
    exact (Finset.card_le_card hsub).trans (hdegY z (hRY hzR))
  omega

omit [Fintype V] [DecidableEq V] in
private lemma p3_claim6 {G : SimpleGraph V} [DecidableRel G.Adj]
    (h2k2 : Is2K2Free G) {P Q : Finset V} (hdisjPQ : Disjoint P Q) (hPne : P.Nonempty)
    (hindP : ∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v) (hindQ : ∀ u ∈ Q, ∀ v ∈ Q, ¬ G.Adj u v) :
    (∃ x ∈ P, ∀ y ∈ Q, G.Adj x y) ∨ (∃ y ∈ Q, ∀ x ∈ P, ¬ G.Adj x y) := by
  by_cases hanti : ∃ y ∈ Q, ∀ x ∈ P, ¬ G.Adj x y
  · exact Or.inr hanti
  · left
    push Not at hanti
    obtain ⟨x, hxP, hxmax⟩ := Finset.exists_max_image P (fun v => (Q.filter (G.Adj v)).card) hPne
    refine ⟨x, hxP, fun y hyQ => ?_⟩
    by_contra hnxy
    obtain ⟨x', hx'P, hx'y⟩ := hanti y hyQ
    have hxx' : x ≠ x' := by rintro rfl; exact hnxy hx'y
    have hnsub : ¬ (Q.filter (G.Adj x) ⊆ Q.filter (G.Adj x')) := by
      intro hsub
      have hssub : Q.filter (G.Adj x) ⊂ Q.filter (G.Adj x') :=
        Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => by
          have : y ∈ Q.filter (G.Adj x') := by simp [hyQ, hx'y]
          rw [← heq] at this; exact hnxy (Finset.mem_filter.1 this).2⟩
      exact absurd (Finset.card_lt_card hssub) (not_lt.2 (hxmax x' hx'P))
    rw [Finset.not_subset] at hnsub
    rcases hnsub with ⟨y', hy'x, hny'x'⟩
    simp only [Finset.mem_filter] at hy'x hny'x'
    have hy'y : y' ≠ y := by rintro rfl; exact hnxy hy'x.2
    rcases h2k2 x y' x' y hy'x.2 hx'y with h | h | h | h | h | h | h | h
    · exact hxx' h
    · exact Finset.disjoint_left.1 hdisjPQ hxP (h ▸ hyQ)
    · exact Finset.disjoint_left.1 hdisjPQ hx'P (h ▸ hy'x.1)
    · exact hy'y h
    · exact hindP x hxP x' hx'P h
    · exact hnxy h
    · exact hny'x' ⟨hy'x.1, h.symm⟩
    · exact hindQ y' hy'x.1 y hyQ h

private lemma p3_claim7_step {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    {K P Q R : Finset V} {xp xq xr : V}
    (h2k2 : Is2K2Free G)
    (hdegY : ∀ y ∈ Finset.univ \ K, ((Finset.univ \ K).filter (G.Adj y)).card ≤ d - 1)
    (hPY : P ⊆ Finset.univ \ K) (hQY : Q ⊆ Finset.univ \ K) (hRY : R ⊆ Finset.univ \ K)
    (hxpK : xp ∈ K) (hxqK : xq ∈ K) (hxrK : xr ∈ K)
    (hdisjPQ : Disjoint P Q) (hdisjPR : Disjoint P R) (hdisjQR : Disjoint Q R)
    (hP : ∀ u ∈ P, G.Adj u xp ∧ ¬ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hQ : ∀ u ∈ Q, ¬ G.Adj u xp ∧ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hR : ∀ u ∈ R, ¬ G.Adj u xp ∧ ¬ G.Adj u xq ∧ G.Adj u xr)
    (hindP : ∀ u ∈ P, ∀ v ∈ P, ¬ G.Adj u v)
    (hindQ : ∀ u ∈ Q, ∀ v ∈ Q, ¬ G.Adj u v)
    (hindR : ∀ u ∈ R, ∀ v ∈ R, ¬ G.Adj u v)
    (hPQcard : d < P.card + Q.card) (hPne : P.Nonempty)
    (hPR : ∃ u ∈ P, ∃ z ∈ R, G.Adj u z)
    (hQanti : ∃ y₀ ∈ Q, ∀ x ∈ P, ¬ G.Adj x y₀) :
    (∃ x ∈ P, ∀ z ∈ R, G.Adj x z) ∧ (∃ z ∈ R, ∀ x ∈ P, G.Adj z x) := by
  rcases hPR with ⟨x0, hx0P, z0, hz0R, hx0z0⟩
  rcases hQanti with ⟨y0, hy0Q, hy0anti⟩
  have hz0y0 : G.Adj z0 y0 := by
    rcases h2k2 x0 z0 xq y0 hx0z0 (hQ y0 hy0Q).2.1.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hPY hx0P)).2 (h' ▸ hxqK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjPQ hx0P (h' ▸ hy0Q))
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hRY hz0R)).2 (h' ▸ hxqK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjQR (h' ▸ hy0Q) hz0R)
    · exact absurd h (hP x0 hx0P).2.1
    · exact absurd h (hy0anti x0 hx0P)
    · exact absurd h (hR z0 hz0R).2.1
    · exact h
  have hz0P : ∀ x ∈ P, G.Adj z0 x := by
    intro x hxP
    rcases h2k2 z0 y0 xp x hz0y0 (hP x hxP).1.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hRY hz0R)).2 (h' ▸ hxpK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjPR hxP (h' ▸ hz0R))
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hQY hy0Q)).2 (h' ▸ hxpK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjPQ hxP (h' ▸ hy0Q))
    · exact absurd h (hR z0 hz0R).1
    · exact h
    · exact absurd h (hQ y0 hy0Q).1
    · exact absurd h.symm (hy0anti x hxP)
  have hex_y1 : ∃ y1 ∈ Q, ¬ G.Adj z0 y1 := by
    by_contra hall; push Not at hall
    have hsub : P ∪ Q ⊆ (Finset.univ \ K).filter (G.Adj z0) := by
      intro v hv; simp only [Finset.mem_union, Finset.mem_filter] at hv ⊢
      rcases hv with h | h
      · exact ⟨hPY h, hz0P v h⟩
      · exact ⟨hQY h, hall v h⟩
    have hle : P.card + Q.card ≤ d - 1 := by
      rw [← Finset.card_union_of_disjoint hdisjPQ]
      exact (Finset.card_le_card hsub).trans (hdegY z0 (hRY hz0R))
    omega
  rcases hex_y1 with ⟨y1, hy1Q, hnz0y1⟩
  have hy1P : ∀ x ∈ P, G.Adj y1 x := by
    intro x hxP
    rcases h2k2 x z0 xq y1 (hz0P x hxP).symm (hQ y1 hy1Q).2.1.symm with h | h | h | h | h | h | h | h
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hPY hxP)).2 (h' ▸ hxqK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjPQ hxP (h' ▸ hy1Q))
    · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hRY hz0R)).2 (h' ▸ hxqK))
    · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjQR (h' ▸ hy1Q) hz0R)
    · exact absurd h (hP x hxP).2.1
    · exact h.symm
    · exact absurd h (hR z0 hz0R).2.1
    · exact absurd h hnz0y1
  refine ⟨?_, ⟨z0, hz0R, hz0P⟩⟩
  rcases p3_claim6 h2k2 hdisjPR hPne hindP hindR with h | ⟨z1, hz1R, hz1anti⟩
  · exact h
  · exfalso
    have hy1z1 : G.Adj y1 z1 := by
      rcases h2k2 x0 y1 xr z1 (hy1P x0 hx0P).symm (hR z1 hz1R).2.2.symm with
        h | h | h | h | h | h | h | h
      · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hPY hx0P)).2 (h' ▸ hxrK))
      · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjPR hx0P (h' ▸ hz1R))
      · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hQY hy1Q)).2 (h' ▸ hxrK))
      · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjQR hy1Q (h' ▸ hz1R))
      · exact absurd h (hP x0 hx0P).2.2
      · exact absurd h (hz1anti x0 hx0P)
      · exact absurd h (hQ y1 hy1Q).2.2
      · exact h
    have hy0y1 : y0 ≠ y1 := by rintro rfl; exact hnz0y1 hz0y0
    have hz0z1 : z0 ≠ z1 := by rintro rfl; exact hz1anti x0 hx0P hx0z0
    have hy0z1 : G.Adj y0 z1 := by
      rcases h2k2 y0 z0 y1 z1 hz0y0.symm hy1z1 with h | h | h | h | h | h | h | h
      · exact absurd h hy0y1
      · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjQR hy0Q (h' ▸ hz1R))
      · exact absurd h (fun h' => Finset.disjoint_left.1 hdisjQR (h' ▸ hy1Q) hz0R)
      · exact absurd h hz0z1
      · exact absurd h (hindQ y0 hy0Q y1 hy1Q)
      · exact h
      · exact absurd h hnz0y1
      · exact absurd h (hindR z0 hz0R z1 hz1R)
    rcases h2k2 y0 z1 xp x0 hy0z1 (hP x0 hx0P).1.symm with h | h | h | h | h | h | h | h
    · exact (Finset.mem_sdiff.1 (hQY hy0Q)).2 (h ▸ hxpK)
    · exact Finset.disjoint_left.1 hdisjPQ (h ▸ hx0P) hy0Q
    · exact (Finset.mem_sdiff.1 (hRY hz1R)).2 (h ▸ hxpK)
    · exact Finset.disjoint_left.1 hdisjPR (h ▸ hx0P) hz1R
    · exact (hQ y0 hy0Q).1 h
    · exact hy0anti x0 hx0P h.symm
    · exact (hR z1 hz1R).1 h
    · exact hz1anti x0 hx0P h.symm

private lemma p3_linked_contra {G : SimpleGraph V} [DecidableRel G.Adj] {d lam2 : ℕ}
    {K P Q Bij : Finset V} {xp xq xr : V}
    (h2k2 : Is2K2Free G)
    (hdegY : ∀ y ∈ Finset.univ \ K, ((Finset.univ \ K).filter (G.Adj y)).card ≤ d - 1)
    (hClaim1 : 5 * d < 2 * (Finset.univ \ K).card + 8)
    (hClaim3 : 2 * lam2 + 4 < d)
    (hPY : P ⊆ Finset.univ \ K) (hQY : Q ⊆ Finset.univ \ K)
    (hxrK : xr ∈ K)
    (hBij_le : Bij.card ≤ lam2)
    (hP : ∀ u ∈ P, G.Adj u xp ∧ ¬ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hQ : ∀ u ∈ Q, ¬ G.Adj u xp ∧ G.Adj u xq ∧ ¬ G.Adj u xr)
    (hrest : ∀ y ∈ Finset.univ \ K, y ∉ P → y ∉ Q → y ∉ Bij → G.Adj y xr)
    (hPQ : ∃ a₀ ∈ P, ∀ b ∈ Q, G.Adj a₀ b)
    (hQP : ∃ b₀ ∈ Q, ∀ a ∈ P, G.Adj b₀ a) :
    False := by
  set Y := Finset.univ \ K
  rcases hPQ with ⟨a₀, ha₀P, ha₀Q⟩
  rcases hQP with ⟨b₀, hb₀Q, hb₀P⟩
  have ha₀b₀ : G.Adj a₀ b₀ := ha₀Q b₀ hb₀Q
  have hsub : Y \ Bij ⊆ Y.filter (G.Adj a₀) ∪ Y.filter (G.Adj b₀) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hyP : y ∈ P
    · exact Or.inr ⟨hy.1, hb₀P y hyP⟩
    · by_cases hyQ : y ∈ Q
      · exact Or.inl ⟨hy.1, ha₀Q y hyQ⟩
      · have hyxr : G.Adj y xr := hrest y hy.1 hyP hyQ hy.2
        rcases h2k2 y xr a₀ b₀ hyxr ha₀b₀ with h | h | h | h | h | h | h | h
        · exact absurd (h ▸ ha₀P) hyP
        · exact absurd (h ▸ hb₀Q) hyQ
        · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hPY ha₀P)).2 (h' ▸ hxrK))
        · exact absurd h (fun h' => (Finset.mem_sdiff.1 (hQY hb₀Q)).2 (h' ▸ hxrK))
        · exact Or.inl ⟨hy.1, h.symm⟩
        · exact Or.inr ⟨hy.1, h.symm⟩
        · exact absurd h.symm (hP a₀ ha₀P).2.2
        · exact absurd h.symm (hQ b₀ hb₀Q).2.2
  have hcard : (Y \ Bij).card ≤ 2 * (d - 1) := by
    calc (Y \ Bij).card
        ≤ (Y.filter (G.Adj a₀) ∪ Y.filter (G.Adj b₀)).card := Finset.card_le_card hsub
      _ ≤ (Y.filter (G.Adj a₀)).card + (Y.filter (G.Adj b₀)).card := Finset.card_union_le _ _
      _ ≤ (d - 1) + (d - 1) := Nat.add_le_add (hdegY a₀ (hPY ha₀P)) (hdegY b₀ (hQY hb₀Q))
      _ = 2 * (d - 1) := by omega
  have hY_le : Y.card ≤ 2 * (d - 1) + Bij.card := by
    have : Y.card - Bij.card ≤ (Y \ Bij).card := Finset.le_card_sdiff Bij Y
    omega
  omega

/-- Case (v): `p = 3`. -/
private lemma case_p_eq_3 {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    {K : Finset V} (hmax : IsMaxClique G K)
    (hdom : ∀ v : V, v ∉ K → ∃ u ∈ K, G.Adj v u) (hp3 : K.card = 3) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  by_contra hgt
  push Not at hgt
  set Y := Finset.univ \ K
  obtain ⟨hEK, hw_bounds, hdegY_raw, hEKY, _, _⟩ := dominating_clique_bounds h2k2 hdeg hmax hdom
  have hdegY : ∀ y ∈ Y, (Y.filter (G.Adj y)).card ≤ d - 1 := by
    intro y hy
    have h1 : 1 ≤ (K.filter (G.Adj y)).card := (hw_bounds y hy).1
    have h2 : (Y.filter (G.Adj y)).card + (K.filter (G.Adj y)).card ≤ d := hdegY_raw y hy
    omega
  have hpart := card_edgeFinset_partition G K
  have hEK3 : (edgesIn G K).card = 3 := by rw [hp3] at hEK; omega
  obtain ⟨x1, x2, x3, hx12, hx13, hx23, hKeq⟩ := Finset.card_eq_three.1 hp3
  have hx1K : x1 ∈ K := by rw [hKeq]; simp
  have hx2K : x2 ∈ K := by rw [hKeq]; simp
  have hx3K : x3 ∈ K := by rw [hKeq]; simp
  have hadj12 : G.Adj x1 x2 := hmax.1 hx1K hx2K hx12
  have hadj13 : G.Adj x1 x3 := hmax.1 hx1K hx3K hx13
  have hadj23 : G.Adj x2 x3 := hmax.1 hx2K hx3K hx23
  have hd2 : 2 ≤ d := by
    have hsub : ({x2, x3} : Finset V) ⊆ Finset.univ.filter (G.Adj x1) := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hz with rfl | rfl <;> assumption
    calc 2 = ({x2, x3} : Finset V).card := (Finset.card_pair hx23).symm
      _ ≤ (Finset.univ.filter (G.Adj x1)).card := Finset.card_le_card hsub
      _ ≤ d := hdeg x1
  have hEY_hand : 2 * (edgesIn G Y).card ≤ Y.card * (d - 1) := by
    rw [two_mul_card_edgesIn]
    calc ∑ y ∈ Y, (Y.filter (G.Adj y)).card
        ≤ ∑ _y ∈ Y, (d - 1) := Finset.sum_le_sum (fun y hy => hdegY y hy)
      _ = Y.card * (d - 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hClaim1 : 5 * d < 2 * Y.card + 8 := by
    by_contra hle; push Not at hle
    have hgoal : (4 * G.edgeFinset.card : ℤ) ≤ (5 * d ^ 2 : ℤ) := by
      have hd2z : (2 : ℤ) ≤ d := by exact_mod_cast hd2
      have hEKYz : ((edgesBetween G K Y).card : ℤ) ≤ 3 * ((d : ℤ) - 2) := by
        rw [hp3] at hEKY; zify [show 2 ≤ d by omega] at hEKY; exact hEKY
      have hEYz : (2 * (edgesIn G Y).card : ℤ) ≤ (Y.card : ℤ) * ((d : ℤ) - 1) := by
        zify [show 1 ≤ d by omega] at hEY_hand; exact hEY_hand
      have hpartz : (G.edgeFinset.card : ℤ) =
          3 + (edgesBetween G K Y).card + (edgesIn G Y).card := by
        rw [hpart, hEK3]; push_cast; ring
      have hlez : (2 * Y.card : ℤ) ≤ 5 * (d : ℤ) - 8 := by omega
      nlinarith
    have : 4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by exact_mod_cast hgoal
    omega
  set A1 := Y.filter (fun y => G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ ¬ G.Adj y x3)
  set A2 := Y.filter (fun y => ¬ G.Adj y x1 ∧ G.Adj y x2 ∧ ¬ G.Adj y x3)
  set A3 := Y.filter (fun y => ¬ G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ G.Adj y x3)
  set A12 := Y.filter (fun y => G.Adj y x1 ∧ G.Adj y x2 ∧ ¬ G.Adj y x3)
  set A13 := Y.filter (fun y => G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ G.Adj y x3)
  set A23 := Y.filter (fun y => ¬ G.Adj y x1 ∧ G.Adj y x2 ∧ G.Adj y x3)
  have hy_cases : ∀ y ∈ Y,
      (G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ ¬ G.Adj y x3) ∨
      (¬ G.Adj y x1 ∧ G.Adj y x2 ∧ ¬ G.Adj y x3) ∨
      (¬ G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ G.Adj y x3) ∨
      (G.Adj y x1 ∧ G.Adj y x2 ∧ ¬ G.Adj y x3) ∨
      (G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ G.Adj y x3) ∨
      (¬ G.Adj y x1 ∧ G.Adj y x2 ∧ G.Adj y x3) := by
    intro y hy
    have hwb := hw_bounds y hy
    have h1 : G.Adj y x1 ∨ G.Adj y x2 ∨ G.Adj y x3 := by
      obtain ⟨u, huK, hyu⟩ := hdom y (Finset.mem_sdiff.1 hy).2
      rw [hKeq] at huK; simp only [Finset.mem_insert, Finset.mem_singleton] at huK
      rcases huK with rfl | rfl | rfl <;> tauto
    have hnotall : ¬ (G.Adj y x1 ∧ G.Adj y x2 ∧ G.Adj y x3) := by
      rintro ⟨a1, a2, a3⟩
      have hsub : K ⊆ K.filter (G.Adj y) := by
        intro z hz; rw [hKeq] at hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [Finset.mem_filter]
        rcases hz with rfl | rfl | rfl <;> exact ⟨by rw [hKeq]; simp, by assumption⟩
      have hle : K.card ≤ (K.filter (G.Adj y)).card := Finset.card_le_card hsub
      omega
    by_cases a1 : G.Adj y x1
    · by_cases a2 : G.Adj y x2
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, fun h => hnotall ⟨a1, a2, h⟩⟩)))
      · by_cases a3 : G.Adj y x3
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2, a3⟩))))
        · exact Or.inl ⟨a1, a2, a3⟩
    · by_cases a2 : G.Adj y x2
      · by_cases a3 : G.Adj y x3
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2, a3⟩))))
        · exact Or.inr (Or.inl ⟨a1, a2, a3⟩)
      · have a3 : G.Adj y x3 := by
          rcases h1 with h | h | h
          · exact absurd h a1
          · exact absurd h a2
          · exact h
        exact Or.inr (Or.inr (Or.inl ⟨a1, a2, a3⟩))
  have hY_sum : Y.card = A1.card + A2.card + A3.card + A12.card + A13.card + A23.card := by
    have hdisj_f : ∀ (P Q : V → Prop) [DecidablePred P] [DecidablePred Q],
        (∀ y, P y → Q y → False) → Disjoint (Y.filter P) (Y.filter Q) := by
      intro P Q _ _ h; rw [Finset.disjoint_left]; intro y h1 h2
      exact h y (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).2
    have h12 : Disjoint A1 A2 := hdisj_f _ _ (fun _ h1 h2 => h2.1 h1.1)
    have h13 : Disjoint A1 A3 := hdisj_f _ _ (fun _ h1 h2 => h2.1 h1.1)
    have h23 : Disjoint A2 A3 := hdisj_f _ _ (fun _ h1 h2 => h2.2.1 h1.2.1)
    have h1_12 : Disjoint A1 A12 := hdisj_f _ _ (fun _ h1 h2 => h1.2.1 h2.2.1)
    have h2_12 : Disjoint A2 A12 := hdisj_f _ _ (fun _ h1 h2 => h1.1 h2.1)
    have h3_12 : Disjoint A3 A12 := hdisj_f _ _ (fun _ h1 h2 => h1.1 h2.1)
    have h1_13 : Disjoint A1 A13 := hdisj_f _ _ (fun _ h1 h2 => h1.2.2 h2.2.2)
    have h2_13 : Disjoint A2 A13 := hdisj_f _ _ (fun _ h1 h2 => h1.1 h2.1)
    have h3_13 : Disjoint A3 A13 := hdisj_f _ _ (fun _ h1 h2 => h1.1 h2.1)
    have h12_13 : Disjoint A12 A13 := hdisj_f _ _ (fun _ h1 h2 => h1.2.2 h2.2.2)
    have h1_23 : Disjoint A1 A23 := hdisj_f _ _ (fun _ h1 h2 => h2.1 h1.1)
    have h2_23 : Disjoint A2 A23 := hdisj_f _ _ (fun _ h1 h2 => h1.2.2 h2.2.2)
    have h3_23 : Disjoint A3 A23 := hdisj_f _ _ (fun _ h1 h2 => h1.2.1 h2.2.1)
    have h12_23 : Disjoint A12 A23 := hdisj_f _ _ (fun _ h1 h2 => h2.1 h1.1)
    have h13_23 : Disjoint A13 A23 := hdisj_f _ _ (fun _ h1 h2 => h2.1 h1.1)
    have heq : Y = A1 ∪ A2 ∪ A3 ∪ A12 ∪ A13 ∪ A23 := by
      ext y; simp only [A1, A2, A3, A12, A13, A23, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hy
        rcases hy_cases y hy with h | h | h | h | h | h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hy, h⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hy, h⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hy, h⟩)))
        · exact Or.inl (Or.inl (Or.inr ⟨hy, h⟩))
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr ⟨hy, h⟩
      · rintro (((((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
    rw [heq,
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, h1_23, h2_23, h3_23, h12_23, h13_23]),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, h1_13, h2_13, h3_13, h12_13]),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, h1_12, h2_12, h3_12]),
      Finset.card_union_of_disjoint (by simp [Finset.disjoint_union_left, h13, h23]),
      Finset.card_union_of_disjoint h12]
  have hx_deg : ∀ (a b c : V), a ∈ K → b ∈ K → c ∈ K → b ≠ c → G.Adj a b → G.Adj a c →
      (Y.filter (G.Adj a)).card ≤ d - 2 := by
    intro a b c _ hbK hcK hbc hab hac
    have hd : Disjoint (Y.filter (G.Adj a)) ({b, c} : Finset V) := by
      rw [Finset.disjoint_left]; intro z hz1 hz2
      have hzK : z ∉ K := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hz1).1).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl <;> [exact hzK hbK; exact hzK hcK]
    have hle : (Y.filter (G.Adj a) ∪ {b, c}).card ≤ d := by
      refine (Finset.card_le_card ?_).trans (hdeg a)
      intro z hz
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_insert,
        Finset.mem_singleton, Finset.mem_univ, true_and] at hz ⊢
      rcases hz with ⟨_, h⟩ | rfl | rfl <;> assumption
    rw [Finset.card_union_of_disjoint hd, Finset.card_pair hbc] at hle; omega
  have hx1_deg : A1.card + A12.card + A13.card ≤ d - 2 := by
    have hsub : A1 ∪ A12 ∪ A13 ⊆ Y.filter (G.Adj x1) := by
      intro y hy; simp only [A1, A12, A13, Finset.mem_union, Finset.mem_filter] at hy ⊢
      rcases hy with (⟨hyY, h1, _⟩ | ⟨hyY, h1, _⟩) | ⟨hyY, h1, _⟩ <;> exact ⟨hyY, h1.symm⟩
    have hcard : (A1 ∪ A12 ∪ A13).card = A1.card + A12.card + A13.card := by
      repeat rw [Finset.card_union_of_disjoint]
      all_goals
        rw [Finset.disjoint_left]; intro y h1 h2
        simp only [A1, A12, A13, Finset.mem_union, Finset.mem_filter] at h1 h2; tauto
    exact hcard ▸ (Finset.card_le_card hsub).trans (hx_deg x1 x2 x3 hx1K hx2K hx3K hx23 hadj12 hadj13)
  have hx2_deg : A2.card + A12.card + A23.card ≤ d - 2 := by
    have hsub : A2 ∪ A12 ∪ A23 ⊆ Y.filter (G.Adj x2) := by
      intro y hy; simp only [A2, A12, A23, Finset.mem_union, Finset.mem_filter] at hy ⊢
      rcases hy with (⟨hyY, _, h2, _⟩ | ⟨hyY, _, h2, _⟩) | ⟨hyY, _, h2, _⟩ <;> exact ⟨hyY, h2.symm⟩
    have hcard : (A2 ∪ A12 ∪ A23).card = A2.card + A12.card + A23.card := by
      repeat rw [Finset.card_union_of_disjoint]
      all_goals
        rw [Finset.disjoint_left]; intro y h1 h2
        simp only [A2, A12, A23, Finset.mem_union, Finset.mem_filter] at h1 h2; tauto
    exact hcard ▸ (Finset.card_le_card hsub).trans (hx_deg x2 x1 x3 hx2K hx1K hx3K hx13 hadj12.symm hadj23)
  have hx3_deg : A3.card + A13.card + A23.card ≤ d - 2 := by
    have hsub : A3 ∪ A13 ∪ A23 ⊆ Y.filter (G.Adj x3) := by
      intro y hy; simp only [A3, A13, A23, Finset.mem_union, Finset.mem_filter] at hy ⊢
      rcases hy with (⟨hyY, _, _, h3⟩ | ⟨hyY, _, _, h3⟩) | ⟨hyY, _, _, h3⟩ <;> exact ⟨hyY, h3.symm⟩
    have hcard : (A3 ∪ A13 ∪ A23).card = A3.card + A13.card + A23.card := by
      repeat rw [Finset.card_union_of_disjoint]
      all_goals
        rw [Finset.disjoint_left]; intro y h1 h2
        simp only [A3, A13, A23, Finset.mem_union, Finset.mem_filter] at h1 h2; tauto
    exact hcard ▸ (Finset.card_le_card hsub).trans (hx_deg x3 x1 x2 hx3K hx1K hx2K hx12 hadj13.symm hadj23.symm)
  set lam2 := A12.card + A13.card + A23.card
  have hClaim2_1 : 2 * A23.card + d < 2 * A1.card := by omega
  have hClaim2_2 : 2 * A13.card + d < 2 * A2.card := by omega
  have hClaim2_3 : 2 * A12.card + d < 2 * A3.card := by omega
  have hClaim3 : 2 * lam2 + 4 < d := by omega
  have hindA1 : ∀ u ∈ A1, ∀ v ∈ A1, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [A1, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu hv
    rcases h2k2 u v x2 x3 huv hadj23 with h | h | h | h | h | h | h | h
    · exact hu.1 (h ▸ hx2K)
    · exact hu.1 (h ▸ hx3K)
    · exact hv.1 (h ▸ hx2K)
    · exact hv.1 (h ▸ hx3K)
    · exact hu.2.2.1 h
    · exact hu.2.2.2 h
    · exact hv.2.2.1 h
    · exact hv.2.2.2 h
  have hindA2 : ∀ u ∈ A2, ∀ v ∈ A2, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [A2, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu hv
    rcases h2k2 u v x1 x3 huv hadj13 with h | h | h | h | h | h | h | h
    · exact hu.1 (h ▸ hx1K)
    · exact hu.1 (h ▸ hx3K)
    · exact hv.1 (h ▸ hx1K)
    · exact hv.1 (h ▸ hx3K)
    · exact hu.2.1 h
    · exact hu.2.2.2 h
    · exact hv.2.1 h
    · exact hv.2.2.2 h
  have hindA3 : ∀ u ∈ A3, ∀ v ∈ A3, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [A3, Y, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hu hv
    rcases h2k2 u v x1 x2 huv hadj12 with h | h | h | h | h | h | h | h
    · exact hu.1 (h ▸ hx1K)
    · exact hu.1 (h ▸ hx2K)
    · exact hv.1 (h ▸ hx1K)
    · exact hv.1 (h ▸ hx2K)
    · exact hu.2.1 h
    · exact hu.2.2.1 h
    · exact hv.2.1 h
    · exact hv.2.2.1 h
  have hClaim4 : ∃ u ∈ A1 ∪ A2 ∪ A3, ∃ v ∈ A1 ∪ A2 ∪ A3, G.Adj u v := by
    by_contra hind; push Not at hind
    set B2 := A12 ∪ A13 ∪ A23
    have hB2_card : B2.card = lam2 := by
      repeat rw [Finset.card_union_of_disjoint]
      all_goals
        rw [Finset.disjoint_left]; intro y h1 h2
        simp only [A12, A13, A23, Finset.mem_union, Finset.mem_filter] at h1 h2; tauto
    have hEY_le : (edgesIn G Y).card ≤ lam2 * (d - 2) := by
      rw [← hB2_card]
      refine card_edges_le_of_cover G (Subset.refl _) ?_ ?_
      · intro e he
        simp only [edgesIn, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
        induction e using Sym2.ind with
        | _ u v =>
          by_cases hu : u ∈ B2
          · exact ⟨u, hu, by simp⟩
          · by_cases hv : v ∈ B2
            · exact ⟨v, hv, by simp⟩
            · exfalso
              have hmem1 : ∀ z ∈ Y, z ∉ B2 → z ∈ A1 ∪ A2 ∪ A3 := by
                intro z hzY hzB
                simp only [B2, A1, A2, A3, A12, A13, A23, Finset.mem_union, Finset.mem_filter] at hzB ⊢
                rcases hy_cases z hzY with h | h | h | h | h | h
                · exact Or.inl (Or.inl ⟨hzY, h⟩)
                · exact Or.inl (Or.inr ⟨hzY, h⟩)
                · exact Or.inr ⟨hzY, h⟩
                · exact absurd (Or.inl (Or.inl ⟨hzY, h⟩)) hzB
                · exact absurd (Or.inl (Or.inr ⟨hzY, h⟩)) hzB
                · exact absurd (Or.inr ⟨hzY, h⟩) hzB
              have hu1 : u ∈ A1 ∪ A2 ∪ A3 := hmem1 u (he.2 u (by simp)) hu
              have hv1 : v ∈ A1 ∪ A2 ∪ A3 := hmem1 v (he.2 v (by simp)) hv
              exact hind u hu1 v hv1 he.1
      · intro c hc
        have hcY : c ∈ Y := by
          simp only [B2, A12, A13, A23, Finset.mem_union, Finset.mem_filter] at hc
          rcases hc with (⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩ <;> exact h
        have hwc : 2 ≤ (K.filter (G.Adj c)).card := by
          simp only [B2, A12, A13, A23, Finset.mem_union, Finset.mem_filter] at hc
          rcases hc with (⟨_, h1, h2, _⟩ | ⟨_, h1, _, h3⟩) | ⟨_, _, h2, h3⟩
          · calc 2 = ({x1, x2} : Finset V).card := (Finset.card_pair hx12).symm
              _ ≤ (K.filter (G.Adj c)).card := Finset.card_le_card (fun z hz => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  simp only [Finset.mem_filter]
                  rcases hz with rfl | rfl <;> exact ⟨by assumption, by assumption⟩)
          · calc 2 = ({x1, x3} : Finset V).card := (Finset.card_pair hx13).symm
              _ ≤ (K.filter (G.Adj c)).card := Finset.card_le_card (fun z hz => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  simp only [Finset.mem_filter]
                  rcases hz with rfl | rfl <;> exact ⟨by assumption, by assumption⟩)
          · calc 2 = ({x2, x3} : Finset V).card := (Finset.card_pair hx23).symm
              _ ≤ (K.filter (G.Adj c)).card := Finset.card_le_card (fun z hz => by
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  simp only [Finset.mem_filter]
                  rcases hz with rfl | rfl <;> exact ⟨by assumption, by assumption⟩)
        have hdc : (Y.filter (G.Adj c)).card + (K.filter (G.Adj c)).card ≤ d := hdegY_raw c hcY
        omega
    have hgoal : (4 * G.edgeFinset.card : ℤ) ≤ (5 * d ^ 2 : ℤ) := by
      have hd5z : (5 : ℤ) ≤ d := by omega
      have hlamz : (2 * lam2 + 4 : ℤ) < d := by exact_mod_cast hClaim3
      have hEKYz : ((edgesBetween G K Y).card : ℤ) ≤ 3 * ((d : ℤ) - 2) := by
        rw [hp3] at hEKY; zify [show 2 ≤ d by omega] at hEKY; exact hEKY
      have hEYz : ((edgesIn G Y).card : ℤ) ≤ (lam2 : ℤ) * ((d : ℤ) - 2) := by
        zify [show 2 ≤ d by omega] at hEY_le; exact hEY_le
      have hpartz : (G.edgeFinset.card : ℤ) =
          3 + (edgesBetween G K Y).card + (edgesIn G Y).card := by
        rw [hpart, hEK3]; push_cast; ring
      nlinarith only [hd5z, hlamz, hEKYz, hEYz, hpartz]
    have : 4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by exact_mod_cast hgoal
    omega
  have hhas_some : (∃ u ∈ A1, ∃ v ∈ A2, G.Adj u v) ∨
      (∃ u ∈ A2, ∃ v ∈ A3, G.Adj u v) ∨
      (∃ u ∈ A1, ∃ v ∈ A3, G.Adj u v) := by
    rcases hClaim4 with ⟨u, hu, v, hv, huv⟩
    simp only [Finset.mem_union] at hu hv
    rcases hu with (hu | hu) | hu <;> rcases hv with (hv | hv) | hv
    · exact absurd huv (hindA1 u hu v hv)
    · exact Or.inl ⟨u, hu, v, hv, huv⟩
    · exact Or.inr (Or.inr ⟨u, hu, v, hv, huv⟩)
    · exact Or.inl ⟨v, hv, u, hu, huv.symm⟩
    · exact absurd huv (hindA2 u hu v hv)
    · exact Or.inr (Or.inl ⟨u, hu, v, hv, huv⟩)
    · exact Or.inr (Or.inr ⟨v, hv, u, hu, huv.symm⟩)
    · exact Or.inr (Or.inl ⟨v, hv, u, hu, huv.symm⟩)
    · exact absurd huv (hindA3 u hu v hv)
  have hA1Y : A1 ⊆ Y := Finset.filter_subset _ _
  have hA2Y : A2 ⊆ Y := Finset.filter_subset _ _
  have hA3Y : A3 ⊆ Y := Finset.filter_subset _ _
  have hA1m : ∀ y ∈ A1, G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ ¬ G.Adj y x3 := fun y hy => (Finset.mem_filter.1 hy).2
  have hA2m : ∀ y ∈ A2, ¬ G.Adj y x1 ∧ G.Adj y x2 ∧ ¬ G.Adj y x3 := fun y hy => (Finset.mem_filter.1 hy).2
  have hA3m : ∀ y ∈ A3, ¬ G.Adj y x1 ∧ ¬ G.Adj y x2 ∧ G.Adj y x3 := fun y hy => (Finset.mem_filter.1 hy).2
  have hE12 : ∃ u ∈ A1, ∃ v ∈ A2, G.Adj u v := by
    rcases hhas_some with h | ⟨u, hu, v, hv, huv⟩ | ⟨u, hu, v, hv, huv⟩
    · exact h
    · have h21 := p3_claim5_aux (P := A2) (Q := A1) (R := A3) (xp := x2) (xq := x1) (xr := x3)
        h2k2 hdegY hA2Y hA1Y hA3Y hx2K hx1K
        (fun y hy => ⟨(hA2m y hy).2.1, (hA2m y hy).1, (hA2m y hy).2.2⟩)
        (fun y hy => ⟨(hA1m y hy).2.1, (hA1m y hy).1, (hA1m y hy).2.2⟩)
        (fun y hy => ⟨(hA3m y hy).2.1, (hA3m y hy).1, (hA3m y hy).2.2⟩)
        (by omega) (by omega) ⟨u, hu, v, hv, huv⟩
      rcases h21 with ⟨a, ha, b, hb, hab⟩; exact ⟨b, hb, a, ha, hab.symm⟩
    · exact p3_claim5_aux (P := A1) (Q := A2) (R := A3) (xp := x1) (xq := x2) (xr := x3)
        h2k2 hdegY hA1Y hA2Y hA3Y hx1K hx2K hA1m hA2m hA3m
        (by omega) (by omega) ⟨u, hu, v, hv, huv⟩
  have hE13 : ∃ u ∈ A1, ∃ v ∈ A3, G.Adj u v := by
    rcases hE12 with ⟨u, hu, v, hv, huv⟩
    exact p3_claim5_aux (P := A1) (Q := A3) (R := A2) (xp := x1) (xq := x3) (xr := x2)
      h2k2 hdegY hA1Y hA3Y hA2Y hx1K hx3K
      (fun y hy => ⟨(hA1m y hy).1, (hA1m y hy).2.2, (hA1m y hy).2.1⟩)
      (fun y hy => ⟨(hA3m y hy).1, (hA3m y hy).2.2, (hA3m y hy).2.1⟩)
      (fun y hy => ⟨(hA2m y hy).1, (hA2m y hy).2.2, (hA2m y hy).2.1⟩)
      (by omega) (by omega) ⟨u, hu, v, hv, huv⟩
  have hE23 : ∃ u ∈ A2, ∃ v ∈ A3, G.Adj u v := by
    rcases hE12 with ⟨u, hu, v, hv, huv⟩
    exact p3_claim5_aux (P := A2) (Q := A3) (R := A1) (xp := x2) (xq := x3) (xr := x1)
      h2k2 hdegY hA2Y hA3Y hA1Y hx2K hx3K
      (fun y hy => ⟨(hA2m y hy).2.1, (hA2m y hy).2.2, (hA2m y hy).1⟩)
      (fun y hy => ⟨(hA3m y hy).2.1, (hA3m y hy).2.2, (hA3m y hy).1⟩)
      (fun y hy => ⟨(hA1m y hy).2.1, (hA1m y hy).2.2, (hA1m y hy).1⟩)
      (by omega) (by omega) ⟨v, hv, u, hu, huv.symm⟩
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro y h1 h2; exact (hA2m y h2).1 (hA1m y h1).1
  have hd13 : Disjoint A1 A3 := by
    rw [Finset.disjoint_left]; intro y h1 h2; exact (hA3m y h2).1 (hA1m y h1).1
  have hd23 : Disjoint A2 A3 := by
    rw [Finset.disjoint_left]; intro y h1 h2; exact (hA3m y h2).2.1 (hA2m y h1).2.1
  have h12_1 := p3_claim6 h2k2 hd12 (Finset.card_pos.1 (by omega)) hindA1 hindA2
  have h12_2 := p3_claim6 h2k2 hd12.symm (Finset.card_pos.1 (by omega)) hindA2 hindA1
  rcases h12_1 with h12c | h2anti1
  · rcases h12_2 with h21c | h1anti2
    · exact p3_linked_contra (P := A1) (Q := A2) (Bij := A12) (xp := x1) (xq := x2) (xr := x3)
        h2k2 hdegY hClaim1 hClaim3 hA1Y hA2Y hx3K (by omega) hA1m hA2m
        (fun y hy hy1 hy2 hy12 => by
          rcases hy_cases y hy with h | h | h | h | h | h
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy1
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy2
          · exact h.2.2
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy12
          · exact h.2.2
          · exact h.2.2)
        h12c h21c
    · obtain ⟨h23c, h32c⟩ := p3_claim7_step (P := A2) (Q := A1) (R := A3) (xp := x2) (xq := x1) (xr := x3)
        h2k2 hdegY hA2Y hA1Y hA3Y hx2K hx1K hx3K hd12.symm hd23 hd13
        (fun y hy => ⟨(hA2m y hy).2.1, (hA2m y hy).1, (hA2m y hy).2.2⟩)
        (fun y hy => ⟨(hA1m y hy).2.1, (hA1m y hy).1, (hA1m y hy).2.2⟩)
        (fun y hy => ⟨(hA3m y hy).2.1, (hA3m y hy).1, (hA3m y hy).2.2⟩)
        hindA2 hindA1 hindA3 (by omega) (Finset.card_pos.1 (by omega)) hE23 h1anti2
      exact p3_linked_contra (P := A2) (Q := A3) (Bij := A23) (xp := x2) (xq := x3) (xr := x1)
        h2k2 hdegY hClaim1 hClaim3 hA2Y hA3Y hx1K (by omega)
        (fun y hy => ⟨(hA2m y hy).2.1, (hA2m y hy).2.2, (hA2m y hy).1⟩)
        (fun y hy => ⟨(hA3m y hy).2.1, (hA3m y hy).2.2, (hA3m y hy).1⟩)
        (fun y hy hy2 hy3 hy23 => by
          rcases hy_cases y hy with h | h | h | h | h | h
          · exact h.1
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy2
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy3
          · exact h.1
          · exact h.1
          · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy23)
        h23c h32c
  · obtain ⟨h13c, h31c⟩ := p3_claim7_step (P := A1) (Q := A2) (R := A3) (xp := x1) (xq := x2) (xr := x3)
      h2k2 hdegY hA1Y hA2Y hA3Y hx1K hx2K hx3K hd12 hd13 hd23
      hA1m hA2m hA3m hindA1 hindA2 hindA3 (by omega) (Finset.card_pos.1 (by omega)) hE13 h2anti1
    exact p3_linked_contra (P := A1) (Q := A3) (Bij := A13) (xp := x1) (xq := x3) (xr := x2)
      h2k2 hdegY hClaim1 hClaim3 hA1Y hA3Y hx2K (by omega)
      (fun y hy => ⟨(hA1m y hy).1, (hA1m y hy).2.2, (hA1m y hy).2.1⟩)
      (fun y hy => ⟨(hA3m y hy).1, (hA3m y hy).2.2, (hA3m y hy).2.1⟩)
      (fun y hy hy1 hy3 hy13 => by
        rcases hy_cases y hy with h | h | h | h | h | h
        · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy1
        · exact h.2.1
        · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy3
        · exact h.2.1
        · exact absurd (Finset.mem_filter.2 ⟨hy, h⟩) hy13
        · exact h.2.1)
      h13c h31c

end CaseClique

/- Main Upper Bound for Finite `2K2`-Free Graphs -/

section MainUpper

variable {V : Type*} [Fintype V] [DecidableEq V]

private lemma edge_bound_no_isolated {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d)
    (hnoiso : ∀ v : V, ∃ w : V, G.Adj v w) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  by_cases hcol : G.Colorable 2
  · exact case_bipartite h2k2 hdeg hcol
  · by_cases htf : G.CliqueFree 3
    · exact case_triangleFree_not_bipartite h2k2 hdeg hnoiso htf hcol
    · obtain ⟨K, hmax, hp3, hdom⟩ := exists_dominating_maxClique h2k2 hnoiso htf
      by_cases hp5 : 5 ≤ K.card
      · exact case_p_ge_5 h2k2 hdeg hmax hdom hp5
      · by_cases hp4 : K.card = 4
        · exact case_p_eq_4 h2k2 hdeg hmax hdom hp4
        · have hp3' : K.card = 3 := by omega
          exact case_p_eq_3 h2k2 hdeg hmax hdom hp3'

/-- General upper bound: every finite `2K2`-free graph of max degree `≤ d` satisfies
    `4 * |E(G)| ≤ 5 * d^2`. -/
private lemma edge_bound_2k2_free {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
    (h2k2 : Is2K2Free G) (hdeg : ∀ v : V, (Finset.univ.filter (G.Adj v)).card ≤ d) :
    4 * G.edgeFinset.card ≤ 5 * d ^ 2 := by
  classical
  let V0 := {v : V // ∃ w : V, G.Adj v w}
  let H : SimpleGraph V0 := G.induce {v : V | ∃ w : V, G.Adj v w}
  have h2k2H : Is2K2Free H := by
    intro u v w x huv hwx
    rcases h2k2 u.1 v.1 w.1 x.1 huv hwx with h | h | h | h | h | h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  have hnoisoH : ∀ v : V0, ∃ w : V0, H.Adj v w := by
    intro ⟨v, w, hvw⟩
    exact ⟨⟨w, v, hvw.symm⟩, hvw⟩
  have hdegH : ∀ v : V0, (Finset.univ.filter (H.Adj v)).card ≤ d := by
    intro v
    calc (Finset.univ.filter (H.Adj v)).card
        = ((Finset.univ.filter (H.Adj v)).image Subtype.val).card :=
          (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (Finset.univ.filter (G.Adj v.1)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rcases hx with ⟨w, hvw, rfl⟩
          exact hvw
      _ ≤ d := hdeg v.1
  have hEeq : G.edgeFinset.card = H.edgeFinset.card := by
    symm
    refine Finset.card_bij (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
    · intro e he
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      induction e using Sym2.ind with
      | _ u v => exact he
    · intro e₁ _ e₂ _ heq
      exact Sym2.map.injective Subtype.val_injective heq
    · intro e he
      rw [SimpleGraph.mem_edgeFinset] at he
      induction e using Sym2.ind with
      | _ u v =>
        refine ⟨s(⟨u, v, he⟩, ⟨v, u, he.symm⟩), ?_, rfl⟩
        rw [SimpleGraph.mem_edgeFinset]; exact he
  rw [hEeq]
  exact edge_bound_no_isolated h2k2H hdegH hnoisoH

end MainUpper

/- Lower Bound for Even `d` (Balanced `C5` Blow-Up) -/

section LowerBound

private def c5Blowup (k : ℕ) : SimpleGraph (Fin (5 * k)) where
  Adj u v :=
    ((u.1 / k) + 1) % 5 = v.1 / k ∨ ((v.1 / k) + 1) % 5 = u.1 / k
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => by
    have hu : u.1 / k < 5 := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact Fin.elim0 u
      · exact Nat.div_lt_of_lt_mul (by linarith [u.2])
    omega⟩

private lemma c5Blowup_is2K2Free (k : ℕ) : Is2K2Free (c5Blowup k) := by
  intro u v w x huv hwx
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Fin.elim0 u
    · exact hk
  have hu : u.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [u.2])
  have hv : v.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [v.2])
  have hw : w.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [w.2])
  have hx : x.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [x.2])
  change ((u.1 / k) + 1) % 5 = v.1 / k ∨ ((v.1 / k) + 1) % 5 = u.1 / k at huv
  change ((w.1 / k) + 1) % 5 = x.1 / k ∨ ((x.1 / k) + 1) % 5 = w.1 / k at hwx
  have hcheck :
      ∀ a b c e : ℕ, a < 5 → b < 5 → c < 5 → e < 5 →
      ((a + 1) % 5 = b ∨ (b + 1) % 5 = a) →
      ((c + 1) % 5 = e ∨ (e + 1) % 5 = c) →
      ((a + 1) % 5 = c ∨ (c + 1) % 5 = a) ∨
      ((a + 1) % 5 = e ∨ (e + 1) % 5 = a) ∨
      ((b + 1) % 5 = c ∨ (c + 1) % 5 = b) ∨
      ((b + 1) % 5 = e ∨ (e + 1) % 5 = b) := by
    intro a b c e ha hb hc he hab hce
    omega
  rcases hcheck (u.1 / k) (v.1 / k) (w.1 / k) (x.1 / k) hu hv hw hx huv hwx with
    h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

private lemma c5Blowup_part_card {k : ℕ} (hk : 0 < k) {r : ℕ} (hr : r < 5) :
    (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = r)).card = k := by
  trans (Finset.univ : Finset (Fin k)).card
  swap
  · simp
  refine Finset.card_bij (fun (v : Fin (5 * k)) _ => (⟨v.1 % k, Nat.mod_lt _ hk⟩ : Fin k)) ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro v1 hv1 v2 hv2 heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
    have hmod : v1.1 % k = v2.1 % k := congrArg Fin.val heq
    ext
    have h1 := Nat.div_add_mod v1.1 k
    have h2 := Nat.div_add_mod v2.1 k
    rw [hv1] at h1; rw [hv2] at h2
    linarith
  · intro m _
    refine ⟨⟨r * k + m.1, by nlinarith [m.2]⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mul_comm r k, Nat.mul_add_div hk, Nat.div_eq_of_lt m.2, add_zero]
    · ext; simp [Nat.add_mod, Nat.mod_eq_of_lt m.2]

private lemma c5Blowup_adj_iff_mod (a b : ℕ) (ha : a < 5) (hb : b < 5) :
    ((a + 1) % 5 = b ∨ (b + 1) % 5 = a) ↔ (b = (a + 1) % 5 ∨ b = (a + 4) % 5) := by
  omega

private lemma c5Blowup_deg (k : ℕ) (u : Fin (5 * k)) :
    ((c5Blowup k).neighborSet u).ncard ≤ 2 * k := by
  classical
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact Fin.elim0 u
    · exact hk
  have hu : u.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [u.2])
  rw [Set.ncard_eq_toFinset_card']
  have hsub : ((c5Blowup k).neighborSet u).toFinset ⊆
      Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 1) % 5) ∪
      Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 4) % 5) := by
    intro v hv
    simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet,
      Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    have hv5 : v.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [v.2])
    exact (c5Blowup_adj_iff_mod (u.1 / k) (v.1 / k) hu hv5).1 hv
  calc ((c5Blowup k).neighborSet u).toFinset.card
      ≤ (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 1) % 5) ∪
         Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 4) % 5)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 1) % 5)).card +
        (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 4) % 5)).card :=
        Finset.card_union_le _ _
    _ = k + k := by
        rw [c5Blowup_part_card hk (Nat.mod_lt _ (by decide)),
          c5Blowup_part_card hk (Nat.mod_lt _ (by decide))]
    _ = 2 * k := by omega

private lemma c5Blowup_edge_card (k : ℕ) :
    (c5Blowup k).edgeSet.ncard = 5 * k ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [Set.ncard_eq_toFinset_card']
  · rw [Set.ncard_eq_toFinset_card']
    have hto : (c5Blowup k).edgeSet.toFinset = (c5Blowup k).edgeFinset := by
      ext e; simp
    rw [hto]
    have h2 := two_mul_card_edgesIn (c5Blowup k) Finset.univ
    have heq : edgesIn (c5Blowup k) Finset.univ = (c5Blowup k).edgeFinset := by
      ext e; simp [edgesIn]
    rw [heq] at h2
    have hdeg_eq : ∀ u : Fin (5 * k), (Finset.univ.filter ((c5Blowup k).Adj u)).card = 2 * k := by
      intro u
      have hu : u.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [u.2])
      have hset : Finset.univ.filter ((c5Blowup k).Adj u) =
          Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 1) % 5) ∪
          Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 4) % 5) := by
        ext v
        have hv5 : v.1 / k < 5 := Nat.div_lt_of_lt_mul (by linarith [v.2])
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and]
        exact c5Blowup_adj_iff_mod (u.1 / k) (v.1 / k) hu hv5
      have hdisj : Disjoint
          (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 1) % 5))
          (Finset.univ.filter (fun v : Fin (5 * k) => v.1 / k = (u.1 / k + 4) % 5)) := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
      rw [hset, Finset.card_union_of_disjoint hdisj,
        c5Blowup_part_card hk (Nat.mod_lt _ (by decide)),
        c5Blowup_part_card hk (Nat.mod_lt _ (by decide))]
      omega
    rw [Finset.sum_congr rfl (fun u _ => hdeg_eq u), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at h2
    nlinarith

end LowerBound

end Erdos934Proof

theorem OMA.solution : type_of% @Erdos934.erdos_934.variants.h_two := by
  classical
  have hupper : ∀ d : ℕ, 4 * Erdos934.h 2 d ≤ 5 * d ^ 2 + 4 := by
    intro d
    set m := 5 * d ^ 2 / 4 + 1
    have hm : m ∈ {m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ v, (G.neighborSet v).ncard ≤ d) → m ≤ G.edgeSet.ncard → Erdos934.HasFarEdges G 2} := by
      intro n G hdeg hcard
      by_contra hno
      have h2k2 := Erdos934Proof.is2K2Free_of_not_hasFarEdges hno
      have hdeg' : ∀ v : Fin n, (Finset.univ.filter (G.Adj v)).card ≤ d := by
        intro v
        have h1 := hdeg v
        rw [Set.ncard_eq_toFinset_card'] at h1
        have heq : (G.neighborSet v).toFinset = Finset.univ.filter (G.Adj v) := by
          ext w; simp [SimpleGraph.mem_neighborSet]
        rwa [heq] at h1
      have hbound := Erdos934Proof.edge_bound_2k2_free h2k2 hdeg'
      rw [Set.ncard_eq_toFinset_card'] at hcard
      have heq : G.edgeSet.toFinset = G.edgeFinset := by ext e; simp
      rw [heq] at hcard
      omega
    have hle : Erdos934.h 2 d ≤ m := Nat.sInf_le hm
    omega
  refine ⟨hupper, fun d heven => ?_⟩
  rcases heven with ⟨k, rfl⟩
  have hle := hupper (k + k)
  have hge : 5 * k ^ 2 + 1 ≤ Erdos934.h 2 (k + k) := by
    have hne : ({m : ℕ | ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
        (∀ v, (G.neighborSet v).ncard ≤ k + k) → m ≤ G.edgeSet.ncard →
        Erdos934.HasFarEdges G 2}).Nonempty := by
      refine ⟨5 * (k + k) ^ 2 / 4 + 1, fun n G hdeg hcard => ?_⟩
      by_contra hno
      have h2k2 := Erdos934Proof.is2K2Free_of_not_hasFarEdges hno
      have hdeg' : ∀ v : Fin n, (Finset.univ.filter (G.Adj v)).card ≤ k + k := by
        intro v
        have h1 := hdeg v
        rw [Set.ncard_eq_toFinset_card'] at h1
        have heq : (G.neighborSet v).toFinset = Finset.univ.filter (G.Adj v) := by
          ext w; simp [SimpleGraph.mem_neighborSet]
        rwa [heq] at h1
      have hbound := Erdos934Proof.edge_bound_2k2_free h2k2 hdeg'
      rw [Set.ncard_eq_toFinset_card'] at hcard
      have heq : G.edgeSet.toFinset = G.edgeFinset := by ext e; simp
      rw [heq] at hcard
      omega
    refine le_csInf hne (fun m hm => ?_)
    by_contra hlt
    push Not at hlt
    have hfar := hm (5 * k) (Erdos934Proof.c5Blowup k)
      (fun u => by simpa [two_mul] using Erdos934Proof.c5Blowup_deg k u)
      (by rw [Erdos934Proof.c5Blowup_edge_card k]; omega)
    exact Erdos934Proof.not_hasFarEdges_of_is2K2Free (Erdos934Proof.c5Blowup_is2K2Free k) hfar
  nlinarith
