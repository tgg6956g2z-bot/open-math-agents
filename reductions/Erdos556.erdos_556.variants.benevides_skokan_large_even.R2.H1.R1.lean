import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2

-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1.R1
-- of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R2.H1
-- Credit: @tgg6956g2z-bot

/-!
# Splitting `R2.H1` into EC1 absorption, EC3 absorption, and 3-colour stability

`R2.H2` (EC2 absorption) is already proved. The remaining open step `R2.H1` bundles
three independent parts of Benevides–Skokan [BeSk09]:

* `H1`: **EC1 absorption** (Lemma 5 of [BeSk09]) — elementary bipartite Hall/absorption
  argument (no regularity lemma needed).
* `H2`: **EC3 absorption** (Lemma 7 of [BeSk09]) — elementary Hall + internal-matching /
  green-clique absorption argument (no regularity lemma needed).
* `H3`: **3-colour stability** (Theorem 4 + Section 5 of [BeSk09]) — 3-colour Szemerédi
  regularity + Łuczak connected-matching blow-up (already proved in
  `proofs/Erdos556.erdos_556.variants.luczak_asymptotic_even.lean`) + reduced-graph
  stability into EC1, EC2, or EC3.

Proving `H1`, `H2`, and `H3` closes `R2.H1`, which together with the already-proved
`R2.H2` closes `Erdos556.erdos_556.variants.benevides_skokan_large_even`.
-/

open Filter SimpleGraph Finset

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1

/- Notation used in all three hypotheses (inlined as `let`s, since a reduction may declare only
`H1 … Hk`): `W j` is the `j`-th block `f⁻¹ j` of a 4-partition of `Fin (4 * m)`, and
`dense ε i X Y` says colour `σ i` has `(1 - ε)`-edge density between `X` and `Y`. -/

lemma dense_mono {ι : Type*} (X Y : Finset ι) (s : ℝ) {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    (h : (1 - ε₁) * (X.card : ℝ) * Y.card ≤ s) : (1 - ε₂) * (X.card : ℝ) * Y.card ≤ s := by
  have hXY : (0 : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by positivity
  nlinarith

/-- Step 1 (EC1 absorption, Benevides–Skokan Lemma 5): for sufficiently small `α > 0`
and all sufficiently large `m`, every 3-colouring of `K_{4m}` in `EC1(α)` (four blocks of size
at least `(1 - α)m`, the three perfect matchings of `K_4` each `(1 - α)`-dense in one colour)
contains a monochromatic `C_{2m}`. -/
def H1 : Prop :=
  ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ →
    ∀ᶠ m : ℕ in atTop,
      ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
        (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
        ∀ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)),
          let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
          let dense := fun (i : Fin 3) (X Y : Finset (Fin (4 * m))) =>
            (1 - α) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
          ((∀ j, (1 - α) * (m : ℝ) ≤ (W j).card) ∧
            dense 0 (W 0) (W 1) ∧ dense 0 (W 2) (W 3) ∧
            dense 1 (W 0) (W 3) ∧ dense 1 (W 1) (W 2) ∧
            dense 2 (W 0) (W 2) ∧ dense 2 (W 1) (W 3)) →
          ∃ i, cycleGraph (2 * m) ⊑ c i

/-- Step 2 (EC3 absorption, Benevides–Skokan Lemma 7): for sufficiently small `μ > 0`
and `δ > 0` (depending on `μ`), every 3-colouring of `K_{4m}` in `EC3(μ, 4/5, 3/10, δ)`
(`W 0` dominating the other blocks by `μ m`, `|W 0| + |W 3| ≤ (2 + 3μ/5)m`, and the six EC1
cross-pairs `(1 - δ)`-dense) contains a monochromatic `C_{2m}`. -/
def H2 : Prop :=
  ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ ≤ μ₀ → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ᶠ m : ℕ in atTop,
        ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
          (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
          ∀ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)),
            let W := fun j : Fin 4 => Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
            let a := fun j : Fin 4 => ((W j).card : ℝ)
            let dense := fun (i : Fin 3) (X Y : Finset (Fin (4 * m))) =>
              (1 - δ) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c (σ i)).Adj x)).card : ℝ)
            ((1 - 4 / 5 * μ) * (m : ℝ) ≤ min (a 0) (min (a 1) (a 2)) ∧
              μ * (m : ℝ) ≤ a 3 ∧
              max (a 1) (max (a 2) (a 3)) + μ * (m : ℝ) ≤ a 0 ∧
              a 0 + a 3 ≤ (2 + 3 / 5 * μ) * (m : ℝ) ∧
              dense 0 (W 0) (W 1) ∧ dense 0 (W 2) (W 3) ∧
              dense 1 (W 0) (W 3) ∧ dense 1 (W 1) (W 2) ∧
              dense 2 (W 0) (W 2) ∧ dense 2 (W 1) (W 3)) →
            ∃ i, cycleGraph (2 * m) ⊑ c i

/-- Step 3 (3-colour stability, Benevides–Skokan Theorem 4 + Section 5): for small `α`
and `μ₁`, there exists `0 < μ < μ₁` such that for every `δ > 0` and all sufficiently
large `m`, every 3-colouring of `K_{4m}` contains a monochromatic `C_{2m}` or falls
into `EC1(α)`, `EC2(α)`, or `EC3(μ, 4/5, 3/10, δ)` (as spelled out in `H1`, `R2.H1`, `H2`). -/
def H3 : Prop :=
  ∃ α₀ μ₀ : ℝ, 0 < α₀ ∧ 0 < μ₀ ∧ ∀ α : ℝ, 0 < α → α ≤ α₀ → ∀ μ₁ : ℝ, 0 < μ₁ → μ₁ ≤ μ₀ →
    ∃ μ : ℝ, 0 < μ ∧ μ < μ₁ ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      ∀ (c : Fin 3 → SimpleGraph (Fin (4 * m))) [∀ i, DecidableRel (c i).Adj],
        (⊤ : SimpleGraph (Fin (4 * m))).IsEdgeColouring c →
        let W := fun (f : Fin (4 * m) → Fin 4) (j : Fin 4) =>
          Finset.univ.filter (fun v : Fin (4 * m) => f v = j)
        let a := fun (f : Fin (4 * m) → Fin 4) (j : Fin 4) => ((W f j).card : ℝ)
        let D := fun (ε : ℝ) (k : Fin 3) (X Y : Finset (Fin (4 * m))) =>
          (1 - ε) * (X.card : ℝ) * Y.card ≤ ∑ x ∈ X, ((Y.filter ((c k).Adj x)).card : ℝ)
        let six := fun (ε : ℝ) (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)) =>
          D ε (σ 0) (W f 0) (W f 1) ∧ D ε (σ 0) (W f 2) (W f 3) ∧
          D ε (σ 1) (W f 0) (W f 3) ∧ D ε (σ 1) (W f 1) (W f 2) ∧
          D ε (σ 2) (W f 0) (W f 2) ∧ D ε (σ 2) (W f 1) (W f 3)
        (∃ i, cycleGraph (2 * m) ⊑ c i) ∨
        (∃ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)), (∀ j, (1 - α) * (m : ℝ) ≤ a f j) ∧ six α f σ) ∨
        (∃ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)), (∀ j, (1 - α) * (m : ℝ) ≤ a f j) ∧ D α (σ 0) (W f 0) (W f 1) ∧
          D α (σ 1) (W f 2) (W f 0 ∪ W f 1) ∧ D α (σ 2) (W f 3) (W f 0 ∪ W f 1)) ∨
        (∃ (f : Fin (4 * m) → Fin 4) (σ : Equiv.Perm (Fin 3)), (1 - 4 / 5 * μ) * (m : ℝ) ≤ min (a f 0) (min (a f 1) (a f 2)) ∧
          μ * (m : ℝ) ≤ a f 3 ∧ max (a f 1) (max (a f 2) (a f 3)) + μ * (m : ℝ) ≤ a f 0 ∧
          a f 0 + a f 3 ≤ (2 + 3 / 5 * μ) * (m : ℝ) ∧ six δ f σ)

theorem main :
    H1 → H2 → H3 →
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2.H1 := by
  intro h1 h2 h3 α hα
  obtain ⟨α₁, hα₁, hEC1⟩ := h1
  obtain ⟨μ₂, hμ₂, hEC3⟩ := h2
  obtain ⟨α₃, μ₃, hα₃, hμ₃, hStab⟩ := h3
  set α' : ℝ := min α (min α₁ α₃)
  have hα'_pos : 0 < α' := lt_min hα (lt_min hα₁ hα₃)
  have hα'_le_α : α' ≤ α := min_le_left _ _
  have hα'_le_1 : α' ≤ α₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hα'_le_3 : α' ≤ α₃ := le_trans (min_le_right _ _) (min_le_right _ _)
  set μ₁ : ℝ := min μ₂ μ₃
  have hμ₁_pos : 0 < μ₁ := lt_min hμ₂ hμ₃
  have hμ₁_le_2 : μ₁ ≤ μ₂ := min_le_left _ _
  have hμ₁_le_3 : μ₁ ≤ μ₃ := min_le_right _ _
  obtain ⟨μ, hμ_pos, hμ_lt, hStab_μ⟩ := hStab α' hα'_pos hα'_le_3 μ₁ hμ₁_pos hμ₁_le_3
  obtain ⟨δ₀, hδ₀_pos, hEC3_μ⟩ := hEC3 μ hμ_pos (le_trans hμ_lt.le hμ₁_le_2)
  filter_upwards [hEC1 α' hα'_pos hα'_le_1, hEC3_μ δ₀ hδ₀_pos le_rfl, hStab_μ δ₀ hδ₀_pos]
    with m hm1 hm3 hmS c _ hc
  rcases hmS c hc with hcyc | ⟨f, σ, hec1⟩ | ⟨f, σ, hec2⟩ | ⟨f, σ, hec3⟩
  · exact Or.inl hcyc
  · exact Or.inl (hm1 c hc f σ hec1)
  · right
    obtain ⟨hcard, hd0, hd1, hd2⟩ := hec2
    refine ⟨f, σ, ?_, ?_, ?_, ?_⟩
    · intro j
      have hj := hcard j
      have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    · exact dense_mono _ _ _ hα'_le_α hd0
    · exact dense_mono _ _ _ hα'_le_α hd1
    · exact dense_mono _ _ _ hα'_le_α hd2
  · exact Or.inl (hm3 c hc f σ hec3)

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R2_H1_R1
