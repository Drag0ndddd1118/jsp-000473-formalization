import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Formalization of JSP-000473 (Erdős Problem #584)

**Problem Statement (JSP-000473 / Erdős Problem #584 — Duke, Erdős, and Rödl 1982/1984):**
*Must a dense graph contain a large subgraph in which every two edges lie on a common short cycle?*
-/

namespace JSP000473

open SimpleGraph Finset

variable {V : Type*}

/-! ## Section 1: Short Cycles and Cycle-Connectedness Definitions -/

/-- Four vertices `(v₁, v₂, v₃, v₄)` form a simple 4-cycle `v₁ - v₂ - v₃ - v₄ - v₁` in `H`. -/
def IsFourCycle (H : SimpleGraph V) (v₁ v₂ v₃ v₄ : V) : Prop :=
  v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₁ ≠ v₄ ∧ v₂ ≠ v₃ ∧ v₂ ≠ v₄ ∧ v₃ ≠ v₄ ∧
  H.Adj v₁ v₂ ∧ H.Adj v₂ v₃ ∧ H.Adj v₃ v₄ ∧ H.Adj v₄ v₁

/-- An edge `e : Sym2 V` is one of the 4 edges of the 4-cycle `(v₁, v₂, v₃, v₄)`. -/
def OnFourCycleEdges (e : Sym2 V) (v₁ v₂ v₃ v₄ : V) : Prop :=
  e = s(v₁, v₂) ∨ e = s(v₂, v₃) ∨ e = s(v₃, v₄) ∨ e = s(v₄, v₁)

/-- Two edges `e₁, e₂` lie together on a simple 4-cycle in `H`. -/
def LieOnCommonC4 (H : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v₁ v₂ v₃ v₄ : V, IsFourCycle H v₁ v₂ v₃ v₄ ∧
    OnFourCycleEdges e₁ v₁ v₂ v₃ v₄ ∧ OnFourCycleEdges e₂ v₁ v₂ v₃ v₄

/-- Six vertices `(v₁, v₂, v₃, v₄, v₅, v₆)` form a simple 6-cycle in `H`. -/
def IsSixCycle (H : SimpleGraph V) (v₁ v₂ v₃ v₄ v₅ v₆ : V) : Prop :=
  ([v₁, v₂, v₃, v₄, v₅, v₆] : List V).Nodup ∧
  H.Adj v₁ v₂ ∧ H.Adj v₂ v₃ ∧ H.Adj v₃ v₄ ∧ H.Adj v₄ v₅ ∧ H.Adj v₅ v₆ ∧ H.Adj v₆ v₁

/-- An edge `e : Sym2 V` is one of the 6 edges of the 6-cycle `(v₁, v₂, v₃, v₄, v₅, v₆)`. -/
def OnSixCycleEdges (e : Sym2 V) (v₁ v₂ v₃ v₄ v₅ v₆ : V) : Prop :=
  e = s(v₁, v₂) ∨ e = s(v₂, v₃) ∨ e = s(v₃, v₄) ∨
  e = s(v₄, v₅) ∨ e = s(v₅, v₆) ∨ e = s(v₆, v₁)

/-- Two edges `e₁, e₂` lie together on a simple 6-cycle in `H`. -/
def LieOnCommonC6 (H : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v₁ v₂ v₃ v₄ v₅ v₆ : V, IsSixCycle H v₁ v₂ v₃ v₄ v₅ v₆ ∧
    OnSixCycleEdges e₁ v₁ v₂ v₃ v₄ v₅ v₆ ∧ OnSixCycleEdges e₂ v₁ v₂ v₃ v₄ v₅ v₆

/-- Two edges `e₁, e₂` lie together on a simple cycle of length at most 6 (a `C₄` or `C₆`) in `H`. -/
def LieOnCommonShortCycle6 (H : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  LieOnCommonC4 H e₁ e₂ ∨ LieOnCommonC6 H e₁ e₂

/-- Eight vertices `(v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈)` form a simple 8-cycle in `H`. -/
def IsEightCycle (H : SimpleGraph V) (v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V) : Prop :=
  ([v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈] : List V).Nodup ∧
  H.Adj v₁ v₂ ∧ H.Adj v₂ v₃ ∧ H.Adj v₃ v₄ ∧ H.Adj v₄ v₅ ∧
  H.Adj v₅ v₆ ∧ H.Adj v₆ v₇ ∧ H.Adj v₇ v₈ ∧ H.Adj v₈ v₁

/-- An edge `e : Sym2 V` is one of the 8 edges of the 8-cycle `(v₁, …, v₈)`. -/
def OnEightCycleEdges (e : Sym2 V) (v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V) : Prop :=
  e = s(v₁, v₂) ∨ e = s(v₂, v₃) ∨ e = s(v₃, v₄) ∨ e = s(v₄, v₅) ∨
  e = s(v₅, v₆) ∨ e = s(v₆, v₇) ∨ e = s(v₇, v₈) ∨ e = s(v₈, v₁)

/-- Two edges `e₁, e₂` lie together on a simple 8-cycle in `H`. -/
def LieOnCommonC8 (H : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V, IsEightCycle H v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ ∧
    OnEightCycleEdges e₁ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ ∧
    OnEightCycleEdges e₂ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈

/-- Two edges `e₁, e₂` lie together on a simple cycle of length at most 8 in `H` (`C₄`, `C₆`, or `C₈`). -/
def LieOnCommonShortCycle8 (H : SimpleGraph V) (e₁ e₂ : Sym2 V) : Prop :=
  LieOnCommonC4 H e₁ e₂ ∨ LieOnCommonC6 H e₁ e₂ ∨ LieOnCommonC8 H e₁ e₂

/-- A graph `H` is internally `C₆`-connected if every two distinct edges of `H` lie together
on a simple 4-cycle or 6-cycle in `H`. -/
def IsC6Connected (H : SimpleGraph V) : Prop :=
  ∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → e₁ ≠ e₂ →
    LieOnCommonShortCycle6 H e₁ e₂

/-- A graph `H` is internally `C₈`-connected if every two distinct edges of `H` lie together
on a simple 4-cycle, 6-cycle, or 8-cycle in `H`. -/
def IsC8Connected (H : SimpleGraph V) : Prop :=
  ∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → e₁ ≠ e₂ →
    LieOnCommonShortCycle8 H e₁ e₂

/-- Two edges `e₁, e₂` share a vertex (are adjacent edges) if they are distinct and have a common endpoint. -/
def EdgesShareVertex (e₁ e₂ : Sym2 V) : Prop :=
  e₁ ≠ e₂ ∧ ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

/-- A subgraph `H ≤ G` is ambiently strongly `C₆`-connected in `G` if every two distinct edges
of `H` lie together on a simple `C₄` or `C₆` in `G`, and every two adjacent distinct edges of `H`
lie together on a simple `C₄` in `G` (Eric Li, arXiv:2606.06522, Definition 1.1(ii)). -/
def IsAmbientStronglyC6Connected (G H : SimpleGraph V) : Prop :=
  H ≤ G ∧
  (∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → e₁ ≠ e₂ →
    LieOnCommonShortCycle6 G e₁ e₂) ∧
  (∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → EdgesShareVertex e₁ e₂ →
    LieOnCommonC4 G e₁ e₂)

/-- A graph `H` is internally strongly `C₆`-connected if it is `C₆`-connected and every two
adjacent distinct edges of `H` lie together on a simple `C₄` in `H`
(Eric Li, arXiv:2606.06522, Definition 1.1(iii)). -/
def IsInternallyStronglyC6Connected (H : SimpleGraph V) : Prop :=
  IsC6Connected H ∧
  ∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → EdgesShareVertex e₁ e₂ →
    LieOnCommonC4 H e₁ e₂

/-- Every internally `C₆`-connected graph is automatically internally `C₈`-connected. -/
theorem IsC6Connected.isC8Connected {H : SimpleGraph V} (hH : IsC6Connected H) :
    IsC8Connected H := by
  intro e₁ e₂ he₁ he₂ hne
  rcases hH he₁ he₂ hne with h4 | h6
  · exact Or.inl h4
  · exact Or.inr (Or.inl h6)

/-- Symmetry of `LieOnCommonC4`. -/
theorem LieOnCommonC4.symm {H : SimpleGraph V} {e₁ e₂ : Sym2 V}
    (h : LieOnCommonC4 H e₁ e₂) : LieOnCommonC4 H e₂ e₁ := by
  rcases h with ⟨v₁, v₂, v₃, v₄, hc, h1, h2⟩
  exact ⟨v₁, v₂, v₃, v₄, hc, h2, h1⟩

/-- Symmetry of `LieOnCommonC6`. -/
theorem LieOnCommonC6.symm {H : SimpleGraph V} {e₁ e₂ : Sym2 V}
    (h : LieOnCommonC6 H e₁ e₂) : LieOnCommonC6 H e₂ e₁ := by
  rcases h with ⟨v₁, v₂, v₃, v₄, v₅, v₆, hc, h1, h2⟩
  exact ⟨v₁, v₂, v₃, v₄, v₅, v₆, hc, h2, h1⟩

/-- Symmetry of `LieOnCommonShortCycle6`. -/
theorem LieOnCommonShortCycle6.symm {H : SimpleGraph V} {e₁ e₂ : Sym2 V}
    (h : LieOnCommonShortCycle6 H e₁ e₂) : LieOnCommonShortCycle6 H e₂ e₁ := by
  rcases h with h4 | h6
  · exact Or.inl h4.symm
  · exact Or.inr h6.symm

/-! ## Section 2: Bipartite Cycle Helpers and Gao–Zhao Lemma 2.1 -/

variable [DecidableEq V]

/-- Helper constructing a simple 4-cycle `(x₁, y₁, x₂, y₂)` in a bipartite graph with disjoint
vertex sets `X, Y`. -/
theorem isFourCycle_of_bipartite {H : SimpleGraph V} {X Y : Finset V}
    (hXY : Disjoint X Y) {x₁ x₂ y₁ y₂ : V}
    (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (h11 : H.Adj x₁ y₁) (h21 : H.Adj x₂ y₁) (h22 : H.Adj x₂ y₂) (h12 : H.Adj x₁ y₂) :
    IsFourCycle H x₁ y₁ x₂ y₂ := by
  have hne : ∀ a ∈ X, ∀ b ∈ Y, a ≠ b := fun a ha b hb h =>
    Finset.disjoint_left.mp hXY ha (h ▸ hb)
  refine ⟨hne x₁ hx₁ y₁ hy₁, hx, hne x₁ hx₁ y₂ hy₂, (hne x₂ hx₂ y₁ hy₁).symm, hy,
    hne x₂ hx₂ y₂ hy₂, h11, h21.symm, h22, h12.symm⟩

/-- Helper constructing a simple 6-cycle `(x₁, y₁, x₂, y₂, x₃, y₃)` in a bipartite graph with
disjoint vertex sets `X, Y`. -/
theorem isSixCycle_of_bipartite {H : SimpleGraph V} {X Y : Finset V}
    (hXY : Disjoint X Y) {x₁ x₂ x₃ y₁ y₂ y₃ : V}
    (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hx₃ : x₃ ∈ X)
    (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) (hy₃ : y₃ ∈ Y)
    (hx12 : x₁ ≠ x₂) (hx13 : x₁ ≠ x₃) (hx23 : x₂ ≠ x₃)
    (hy12 : y₁ ≠ y₂) (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (h11 : H.Adj x₁ y₁) (h21 : H.Adj x₂ y₁) (h22 : H.Adj x₂ y₂)
    (h32 : H.Adj x₃ y₂) (h33 : H.Adj x₃ y₃) (h13 : H.Adj x₁ y₃) :
    IsSixCycle H x₁ y₁ x₂ y₂ x₃ y₃ := by
  have hne : ∀ a ∈ X, ∀ b ∈ Y, a ≠ b := fun a ha b hb h =>
    Finset.disjoint_left.mp hXY ha (h ▸ hb)
  have hnodup : ([x₁, y₁, x₂, y₂, x₃, y₃] : List V).Nodup := by
    rw [List.nodup_cons, List.nodup_cons, List.nodup_cons, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_, List.nodup_singleton y₃⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h | h)
      · exact hne x₁ hx₁ y₁ hy₁ h
      · exact hx12 h
      · exact hne x₁ hx₁ y₂ hy₂ h
      · exact hx13 h
      · exact hne x₁ hx₁ y₃ hy₃ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h | h)
      · exact hne x₂ hx₂ y₁ hy₁ h.symm
      · exact hy12 h
      · exact hne x₃ hx₃ y₁ hy₁ h.symm
      · exact hy13 h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h | h)
      · exact hne x₂ hx₂ y₂ hy₂ h
      · exact hx23 h
      · exact hne x₂ hx₂ y₃ hy₃ h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro (h | h)
      · exact hne x₃ hx₃ y₂ hy₂ h.symm
      · exact hy23 h
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact hne x₃ hx₃ y₃ hy₃
  exact ⟨hnodup, h11, h21.symm, h22, h32.symm, h33, h13.symm⟩

/-- The simple graph on `V` defined by a set `E : Finset (V × V)` of directed edges. -/
def subgraphOfBipEdges (E : Finset (V × V)) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ((a, b) ∈ E ∨ (b, a) ∈ E)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (E : Finset (V × V)) : DecidableRel (subgraphOfBipEdges E).Adj :=
  fun a b => by
    change Decidable (a ≠ b ∧ ((a, b) ∈ E ∨ (b, a) ∈ E))
    infer_instance

theorem subgraphOfBipEdges_le {G : SimpleGraph V} {E : Finset (V × V)}
    (hE : ∀ p ∈ E, G.Adj p.1 p.2) : subgraphOfBipEdges E ≤ G := by
  rintro a b ⟨_, h | h⟩
  · exact hE (a, b) h
  · exact (hE (b, a) h).symm

theorem adj_subgraphOfBipEdges_of_mem {X Y : Finset V} (hXY : Disjoint X Y)
    {E : Finset (V × V)} (hEXY : E ⊆ X ×ˢ Y) {x y : V} (h : (x, y) ∈ E) :
    (subgraphOfBipEdges E).Adj x y := by
  have hxy := Finset.mem_product.mp (hEXY h)
  have hne : x ≠ y := fun heq => Finset.disjoint_left.mp hXY hxy.1 (heq ▸ hxy.2)
  exact ⟨hne, Or.inl h⟩

theorem mem_edgeSet_subgraphOfBipEdges_iff {X Y : Finset V} (hXY : Disjoint X Y)
    {E : Finset (V × V)} (hEXY : E ⊆ X ×ˢ Y) (e : Sym2 V) :
    e ∈ (subgraphOfBipEdges E).edgeSet ↔ ∃ p ∈ E, e = s(p.1, p.2) := by
  constructor
  · refine Sym2.ind (fun u v huv => ?_) e
    change (subgraphOfBipEdges E).Adj u v at huv
    rcases huv.2 with h | h
    · exact ⟨(u, v), h, rfl⟩
    · exact ⟨(v, u), h, Sym2.eq_swap⟩
  · rintro ⟨⟨x, y⟩, hp, rfl⟩
    exact adj_subgraphOfBipEdges_of_mem hXY hEXY hp

theorem card_edgeFinset_subgraphOfBipEdges [Fintype V] {X Y : Finset V} (hXY : Disjoint X Y)
    {E : Finset (V × V)} (hEXY : E ⊆ X ×ˢ Y) :
    (subgraphOfBipEdges E).edgeFinset.card = E.card := by
  have heq : (subgraphOfBipEdges E).edgeFinset = E.image (fun p => s(p.1, p.2)) := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, mem_edgeSet_subgraphOfBipEdges_iff hXY hEXY, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, hpe⟩
      exact ⟨p, hp, hpe.symm⟩
  rw [heq]
  apply Finset.card_image_of_injOn
  intro ⟨x₁, y₁⟩ h1 ⟨x₂, y₂⟩ h2 hsym
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq] at hsym
  rcases hsym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exfalso
    have h1' := Finset.mem_product.mp (hEXY h1)
    have h2' := Finset.mem_product.mp (hEXY h2)
    exact Finset.disjoint_left.mp hXY h1'.1 h2'.2

/-- Given two distinct neighbors in `Y`, at least one is distinct from any given `y₀`. -/
lemma exists_ne_of_two_neighbors {α β : Type*} [DecidableEq β] {Y : Finset β} {E : Finset (α × β)}
    {x : α} (h : ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ y₂ ∧ (x, y₁) ∈ E ∧ (x, y₂) ∈ E) (y₀ : β) :
    ∃ y' ∈ Y, y' ≠ y₀ ∧ (x, y') ∈ E := by
  rcases h with ⟨y₁, hy₁, y₂, hy₂, hne, h1, h2⟩
  by_cases h10 : y₁ = y₀
  · subst h10
    exact ⟨y₂, hy₂, hne.symm, h2⟩
  · exact ⟨y₁, hy₁, h10, h1⟩

/-- Symmetry helper for `exists_ne_of_two_neighbors` on the left factor. -/
lemma exists_ne_of_two_neighbors_left {α β : Type*} [DecidableEq α] {X : Finset α}
    {E : Finset (α × β)} {y : β}
    (h : ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ x₂ ∧ (x₁, y) ∈ E ∧ (x₂, y) ∈ E) (x₀ : α) :
    ∃ x' ∈ X, x' ≠ x₀ ∧ (x', y) ∈ E := by
  rcases h with ⟨x₁, hx₁, x₂, hx₂, hne, h1, h2⟩
  by_cases h10 : x₁ = x₀
  · subst h10
    exact ⟨x₂, hx₂, hne.symm, h2⟩
  · exact ⟨x₁, hx₁, h10, h1⟩

/-- Subcase C3 of Gao–Zhao Lemma 2.1: two disjoint edges `(x₁, y₁), (x₂, y₂) ∈ E` with
`(x₁, y₂) ∈ E` and `(x₂, y₁) ∉ E` lie on a common simple 6-cycle in `subgraphOfBipEdges E`. -/
lemma gao_zhao_lemma_2_1_subcase_one_cross {X Y : Finset V} (hXY : Disjoint X Y)
    {E : Finset (V × V)} (hEXY : E ⊆ X ×ˢ Y)
    (hdegX : ∀ x ∈ X, ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ y₂ ∧ (x, y₁) ∈ E ∧ (x, y₂) ∈ E)
    (hdegY : ∀ y ∈ Y, ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ x₂ ∧ (x₁, y) ∈ E ∧ (x₂, y) ∈ E)
    (hcovX : ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∃ y ∈ Y, (x₁, y) ∈ E ∧ (x₂, y) ∈ E)
    (hcovY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ∃ x ∈ X, (x, y₁) ∈ E ∧ (x, y₂) ∈ E)
    {x₁ x₂ y₁ y₂ : V} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y)
    (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (he₁ : (x₁, y₁) ∈ E) (he₂ : (x₂, y₂) ∈ E)
    (hcross1 : (x₁, y₂) ∈ E) (hcross2 : (x₂, y₁) ∉ E) :
    LieOnCommonShortCycle6 (subgraphOfBipEdges E) s(x₁, y₁) s(x₂, y₂) := by
  have adj : ∀ {a b}, (a, b) ∈ E → (subgraphOfBipEdges E).Adj a b :=
    fun h => adj_subgraphOfBipEdges_of_mem hXY hEXY h
  rcases exists_ne_of_two_neighbors (hdegX x₂ hx₂) y₂ with ⟨a, haY, hay₂, hx₂a⟩
  have hay₁ : a ≠ y₁ := fun h => hcross2 (h ▸ hx₂a)
  rcases exists_ne_of_two_neighbors_left (hdegY y₁ hy₁) x₁ with ⟨b, hbX, hbx₁, hby₁⟩
  have hbx₂ : b ≠ x₂ := fun h => hcross2 (h ▸ hby₁)
  by_cases hx₁a : (x₁, a) ∈ E
  · by_cases hby₂ : (b, y₂) ∈ E
    · -- 6-cycle: x₁ - y₁ - b - y₂ - x₂ - a - x₁
      refine Or.inr ⟨x₁, y₁, b, y₂, x₂, a, ?_, ?_, ?_⟩
      · exact isSixCycle_of_bipartite hXY hx₁ hbX hx₂ hy₁ hy₂ haY
          hbx₁.symm hx hbx₂ hy hay₁.symm hay₂.symm
          (adj he₁) (adj hby₁) (adj hby₂) (adj he₂) (adj hx₂a) (adj hx₁a)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))
    · -- Choose w ∈ N(b) ∩ N(x₂); then w ∉ {y₁, y₂}, 6-cycle: x₁ - y₁ - b - w - x₂ - y₂ - x₁
      rcases hcovX b hbX x₂ hx₂ with ⟨w, hwY, hbw, hx₂w⟩
      have hwy₁ : w ≠ y₁ := fun h => hcross2 (h ▸ hx₂w)
      have hwy₂ : w ≠ y₂ := fun h => hby₂ (h ▸ hbw)
      refine Or.inr ⟨x₁, y₁, b, w, x₂, y₂, ?_, ?_, ?_⟩
      · exact isSixCycle_of_bipartite hXY hx₁ hbX hx₂ hy₁ hwY hy₂
          hbx₁.symm hx hbx₂ hwy₁.symm hy hwy₂
          (adj he₁) (adj hby₁) (adj hbw) (adj hx₂w) (adj he₂) (adj hcross1)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · -- Choose z ∈ N(a) ∩ N(y₁); then z ∉ {x₁, x₂}, 6-cycle: x₁ - y₁ - z - a - x₂ - y₂ - x₁
    rcases hcovY y₁ hy₁ a haY with ⟨z, hzX, hzy₁, hza⟩
    have hzx₁ : z ≠ x₁ := fun h => hx₁a (h ▸ hza)
    have hzx₂ : z ≠ x₂ := fun h => hcross2 (h ▸ hzy₁)
    refine Or.inr ⟨x₁, y₁, z, a, x₂, y₂, ?_, ?_, ?_⟩
    · exact isSixCycle_of_bipartite hXY hx₁ hzX hx₂ hy₁ haY hy₂
        hzx₁.symm hx hzx₂ hay₁.symm hy hay₂
        (adj he₁) (adj hzy₁) (adj hza) (adj hx₂a) (adj he₂) (adj hcross1)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- **Gao–Zhao Lemma 2.1 (Sufficiency Direction, arXiv:2610.34307):**
If a bipartite graph `H = subgraphOfBipEdges E` on disjoint classes `X, Y` (`E ⊆ X ×ˢ Y`) has
minimum degree at least 2 on active vertices and every two vertices in the same class have a
common neighbor in the opposite class, then `H` is internally `C₆`-connected (`IsC6Connected H`). -/
theorem gao_zhao_lemma_2_1 {X Y : Finset V} (hXY : Disjoint X Y)
    {E : Finset (V × V)} (hEXY : E ⊆ X ×ˢ Y)
    (hdegX : ∀ x ∈ X, ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, y₁ ≠ y₂ ∧ (x, y₁) ∈ E ∧ (x, y₂) ∈ E)
    (hdegY : ∀ y ∈ Y, ∃ x₁ ∈ X, ∃ x₂ ∈ X, x₁ ≠ x₂ ∧ (x₁, y) ∈ E ∧ (x₂, y) ∈ E)
    (hcovX : ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∃ y ∈ Y, (x₁, y) ∈ E ∧ (x₂, y) ∈ E)
    (hcovY : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ∃ x ∈ X, (x, y₁) ∈ E ∧ (x, y₂) ∈ E) :
    IsC6Connected (subgraphOfBipEdges E) := by
  have adj : ∀ {a b}, (a, b) ∈ E → (subgraphOfBipEdges E).Adj a b :=
    fun h => adj_subgraphOfBipEdges_of_mem hXY hEXY h
  intro e₁ e₂ he₁ he₂ hne
  rcases (mem_edgeSet_subgraphOfBipEdges_iff hXY hEXY e₁).mp he₁ with ⟨⟨x₁, y₁⟩, hp₁, rfl⟩
  rcases (mem_edgeSet_subgraphOfBipEdges_iff hXY hEXY e₂).mp he₂ with ⟨⟨x₂, y₂⟩, hp₂, rfl⟩
  have h1 := Finset.mem_product.mp (hEXY hp₁)
  have h2 := Finset.mem_product.mp (hEXY hp₂)
  rcases h1 with ⟨hx₁, hy₁⟩
  rcases h2 with ⟨hx₂, hy₂⟩
  by_cases hx : x₁ = x₂
  · -- Case A: x₁ = x₂ and y₁ ≠ y₂
    subst hx
    have hy : y₁ ≠ y₂ := fun h => hne (h ▸ rfl)
    rcases exists_ne_of_two_neighbors_left (hdegY y₁ hy₁) x₁ with ⟨a₁, ha₁X, ha₁x, ha₁y₁⟩
    rcases exists_ne_of_two_neighbors_left (hdegY y₂ hy₂) x₁ with ⟨a₂, ha₂X, ha₂x, ha₂y₂⟩
    by_cases ha12 : a₁ = a₂
    · subst ha12
      refine Or.inl ⟨x₁, y₁, a₁, y₂, ?_, Or.inl rfl, Or.inr (Or.inr (Or.inr Sym2.eq_swap))⟩
      exact isFourCycle_of_bipartite hXY hx₁ ha₁X hy₁ hy₂ ha₁x.symm hy
        (adj hp₁) (adj ha₁y₁) (adj ha₂y₂) (adj hp₂)
    · rcases hcovX a₁ ha₁X a₂ ha₂X with ⟨z, hzY, ha₁z, ha₂z⟩
      by_cases hzy₁ : z = y₁
      · subst hzy₁
        refine Or.inl ⟨x₁, z, a₂, y₂, ?_, Or.inl rfl, Or.inr (Or.inr (Or.inr Sym2.eq_swap))⟩
        exact isFourCycle_of_bipartite hXY hx₁ ha₂X hy₁ hy₂ ha₂x.symm hy
          (adj hp₁) (adj ha₂z) (adj ha₂y₂) (adj hp₂)
      · by_cases hzy₂ : z = y₂
        · subst hzy₂
          refine Or.inl ⟨x₁, y₁, a₁, z, ?_, Or.inl rfl, Or.inr (Or.inr (Or.inr Sym2.eq_swap))⟩
          exact isFourCycle_of_bipartite hXY hx₁ ha₁X hy₁ hy₂ ha₁x.symm hy
            (adj hp₁) (adj ha₁y₁) (adj ha₁z) (adj hp₂)
        · refine Or.inr ⟨x₁, y₁, a₁, z, a₂, y₂, ?_, Or.inl rfl,
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr Sym2.eq_swap))))⟩
          exact isSixCycle_of_bipartite hXY hx₁ ha₁X ha₂X hy₁ hzY hy₂
            ha₁x.symm ha₂x.symm ha12 (Ne.symm hzy₁) hy hzy₂
            (adj hp₁) (adj ha₁y₁) (adj ha₁z) (adj ha₂z) (adj ha₂y₂) (adj hp₂)
  · by_cases hy : y₁ = y₂
    · -- Case B: y₁ = y₂ and x₁ ≠ x₂
      subst hy
      rcases exists_ne_of_two_neighbors (hdegX x₁ hx₁) y₁ with ⟨b₁, hb₁Y, hb₁y, hx₁b₁⟩
      rcases exists_ne_of_two_neighbors (hdegX x₂ hx₂) y₁ with ⟨b₂, hb₂Y, hb₂y, hx₂b₂⟩
      by_cases hb12 : b₁ = b₂
      · subst hb12
        refine Or.inl ⟨x₁, y₁, x₂, b₁, ?_, Or.inl rfl, Or.inr (Or.inl Sym2.eq_swap)⟩
        exact isFourCycle_of_bipartite hXY hx₁ hx₂ hy₁ hb₁Y hx hb₁y.symm
          (adj hp₁) (adj hp₂) (adj hx₂b₂) (adj hx₁b₁)
      · rcases hcovY b₁ hb₁Y b₂ hb₂Y with ⟨w, hwX, hwb₁, hwb₂⟩
        by_cases hwx₁ : w = x₁
        · subst hwx₁
          refine Or.inl ⟨w, y₁, x₂, b₂, ?_, Or.inl rfl, Or.inr (Or.inl Sym2.eq_swap)⟩
          exact isFourCycle_of_bipartite hXY hx₁ hx₂ hy₁ hb₂Y hx hb₂y.symm
            (adj hp₁) (adj hp₂) (adj hx₂b₂) (adj hwb₂)
        · by_cases hwx₂ : w = x₂
          · subst hwx₂
            refine Or.inl ⟨x₁, y₁, w, b₁, ?_, Or.inl rfl, Or.inr (Or.inl Sym2.eq_swap)⟩
            exact isFourCycle_of_bipartite hXY hx₁ hx₂ hy₁ hb₁Y hx hb₁y.symm
              (adj hp₁) (adj hp₂) (adj hwb₁) (adj hx₁b₁)
          · refine Or.inr ⟨x₁, y₁, x₂, b₂, w, b₁, ?_, Or.inl rfl, Or.inr (Or.inl Sym2.eq_swap)⟩
            exact isSixCycle_of_bipartite hXY hx₁ hx₂ hwX hy₁ hb₂Y hb₁Y
              hx (Ne.symm hwx₁) (Ne.symm hwx₂) hb₂y.symm hb₁y.symm (Ne.symm hb12)
              (adj hp₁) (adj hp₂) (adj hx₂b₂) (adj hwb₂) (adj hwb₁) (adj hx₁b₁)
    · -- Case C: x₁ ≠ x₂ and y₁ ≠ y₂
      by_cases hcross1 : (x₁, y₂) ∈ E
      · by_cases hcross2 : (x₂, y₁) ∈ E
        · -- Subcase C1: both cross-edges present -> 4-cycle x₁ - y₁ - x₂ - y₂ - x₁
          refine Or.inl ⟨x₁, y₁, x₂, y₂, ?_, Or.inl rfl, Or.inr (Or.inr (Or.inl rfl))⟩
          exact isFourCycle_of_bipartite hXY hx₁ hx₂ hy₁ hy₂ hx hy
            (adj hp₁) (adj hcross2) (adj hp₂) (adj hcross1)
        · -- Subcase C3: only (x₁, y₂) ∈ E
          exact gao_zhao_lemma_2_1_subcase_one_cross hXY hEXY hdegX hdegY hcovX hcovY
            hx₁ hx₂ hy₁ hy₂ hx hy hp₁ hp₂ hcross1 hcross2
      · by_cases hcross2 : (x₂, y₁) ∈ E
        · -- Subcase C4: only (x₂, y₁) ∈ E -> symmetric to Subcase C3
          exact (gao_zhao_lemma_2_1_subcase_one_cross hXY hEXY hdegX hdegY hcovX hcovY
            hx₂ hx₁ hy₂ hy₁ (Ne.symm hx) (Ne.symm hy) hp₂ hp₁ hcross2 hcross1).symm
        · -- Subcase C2: neither cross-edge present -> 6-cycle x₁ - y₁ - b - y₂ - x₂ - a - x₁
          rcases hcovX x₁ hx₁ x₂ hx₂ with ⟨a, haY, hx₁a, hx₂a⟩
          rcases hcovY y₁ hy₁ y₂ hy₂ with ⟨b, hbX, hby₁, hby₂⟩
          have hay₁ : a ≠ y₁ := fun h => hcross2 (h ▸ hx₂a)
          have hay₂ : a ≠ y₂ := fun h => hcross1 (h ▸ hx₁a)
          have hbx₁ : b ≠ x₁ := fun h => hcross1 (h ▸ hby₂)
          have hbx₂ : b ≠ x₂ := fun h => hcross2 (h ▸ hby₁)
          refine Or.inr ⟨x₁, y₁, b, y₂, x₂, a, ?_, Or.inl rfl,
            Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))⟩
          exact isSixCycle_of_bipartite hXY hx₁ hbX hx₂ hy₁ hy₂ haY
            (Ne.symm hbx₁) hx hbx₂ hy (Ne.symm hay₁) (Ne.symm hay₂)
            (adj hp₁) (adj hby₁) (adj hby₂) (adj hp₂) (adj hx₂a) (adj hx₁a)

/-! ## Section 3: Constructive Subgraphs from Middle-Edge Bundles (Gao–Zhao & Eric Li) -/

/-- **Eric Li's Opposite-Edge Core (arXiv:2606.06522, Theorem 1.3):**
Given a bipartite pair `(A, B)` (`Disjoint A B`), endpoints `x ∈ A` and `y ∈ B`, and any bundle
`M ⊆ (A.erase x) ×ˢ (B.erase y)` of middle edges `(v, u)` of 3-edge paths `x - u - v - y` in `G`,
the subgraph `H = subgraphOfBipEdges M` has `M.card` edges and is ambiently strongly `C₆`-connected
in `G`: every two distinct edges lie on an ambient `C₄` or `C₆` in `G`, and every two adjacent
distinct edges lie on an ambient `C₄` in `G`. -/
theorem li_opposite_edges_ambient_strong_c6 [Fintype V] {G : SimpleGraph V}
    {A B : Finset V} (hAB : Disjoint A B) {x y : V} (hx : x ∈ A) (hy : y ∈ B)
    {M : Finset (V × V)} (hM : M ⊆ (A.erase x) ×ˢ (B.erase y))
    (hpath : ∀ p ∈ M, G.Adj x p.2 ∧ G.Adj p.1 p.2 ∧ G.Adj p.1 y) :
    let H := subgraphOfBipEdges M
    H.edgeFinset.card = M.card ∧ IsAmbientStronglyC6Connected G H := by
  intro H
  have hMAB : M ⊆ A ×ˢ B :=
    hM.trans (Finset.product_subset_product (Finset.erase_subset x A) (Finset.erase_subset y B))
  have hcard : H.edgeFinset.card = M.card := card_edgeFinset_subgraphOfBipEdges hAB hMAB
  have hle : H ≤ G := subgraphOfBipEdges_le (fun p hp => (hpath p hp).2.1)
  have hshared : ∀ ⦃e₁ e₂ : Sym2 V⦄, e₁ ∈ H.edgeSet → e₂ ∈ H.edgeSet → e₁ ≠ e₂ →
      (∀ (v₁ u₁ v₂ u₂ : V), (v₁, u₁) ∈ M → (v₂, u₂) ∈ M →
        e₁ = s(v₁, u₁) → e₂ = s(v₂, u₂) → (v₁ = v₂ ∨ u₁ = u₂)) →
      LieOnCommonC4 G e₁ e₂ := by
    intro e₁ e₂ he₁ he₂ hne hshare
    rcases (mem_edgeSet_subgraphOfBipEdges_iff hAB hMAB e₁).mp he₁ with ⟨⟨v₁, u₁⟩, hp₁, rfl⟩
    rcases (mem_edgeSet_subgraphOfBipEdges_iff hAB hMAB e₂).mp he₂ with ⟨⟨v₂, u₂⟩, hp₂, rfl⟩
    have hm₁ := Finset.mem_product.mp (hM hp₁)
    have hm₂ := Finset.mem_product.mp (hM hp₂)
    have hv₁A : v₁ ∈ A := Finset.mem_of_mem_erase hm₁.1
    have hv₁x : v₁ ≠ x := Finset.ne_of_mem_erase hm₁.1
    have hu₁B : u₁ ∈ B := Finset.mem_of_mem_erase hm₁.2
    have hu₁y : u₁ ≠ y := Finset.ne_of_mem_erase hm₁.2
    have hv₂A : v₂ ∈ A := Finset.mem_of_mem_erase hm₂.1
    have hu₂B : u₂ ∈ B := Finset.mem_of_mem_erase hm₂.2
    rcases hshare v₁ u₁ v₂ u₂ hp₁ hp₂ rfl rfl with rfl | rfl
    · have hu : u₁ ≠ u₂ := fun h => hne (h ▸ rfl)
      refine ⟨v₁, u₁, x, u₂, ?_, Or.inl rfl, Or.inr (Or.inr (Or.inr Sym2.eq_swap))⟩
      exact isFourCycle_of_bipartite hAB hv₁A hx hu₁B hu₂B hv₁x hu
        (hpath _ hp₁).2.1 (hpath _ hp₁).1 (hpath _ hp₂).1 (hpath _ hp₂).2.1
    · have hv : v₁ ≠ v₂ := fun h => hne (h ▸ rfl)
      refine ⟨v₁, u₁, v₂, y, ?_, Or.inl rfl, Or.inr (Or.inl Sym2.eq_swap)⟩
      exact isFourCycle_of_bipartite hAB hv₁A hv₂A hu₁B hy hv hu₁y
        (hpath _ hp₁).2.1 (hpath _ hp₂).2.1 (hpath _ hp₂).2.2 (hpath _ hp₁).2.2
  refine ⟨hcard, hle, ?_, ?_⟩
  · intro e₁ e₂ he₁ he₂ hne
    rcases (mem_edgeSet_subgraphOfBipEdges_iff hAB hMAB e₁).mp he₁ with ⟨⟨v₁, u₁⟩, hp₁, heq₁⟩
    rcases (mem_edgeSet_subgraphOfBipEdges_iff hAB hMAB e₂).mp he₂ with ⟨⟨v₂, u₂⟩, hp₂, heq₂⟩
    by_cases hv : v₁ = v₂
    · subst heq₁ heq₂
      exact Or.inl (hshared he₁ he₂ hne (fun a₁ b₁ a₂ b₂ h1 h2 hq1 hq2 => by
        have h1' := Finset.mem_product.mp (hMAB h1)
        have h2' := Finset.mem_product.mp (hMAB h2)
        have hv1' := Finset.mem_product.mp (hMAB hp₁)
        have hv2' := Finset.mem_product.mp (hMAB hp₂)
        simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq] at hq1 hq2
        rcases hq1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hq2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl hv
          · exfalso; exact Finset.disjoint_left.mp hAB hv2'.1 h2'.2
        · exfalso; exact Finset.disjoint_left.mp hAB hv1'.1 h1'.2))
    · by_cases hu : u₁ = u₂
      · subst heq₁ heq₂
        exact Or.inl (hshared he₁ he₂ hne (fun a₁ b₁ a₂ b₂ h1 h2 hq1 hq2 => by
          have h1' := Finset.mem_product.mp (hMAB h1)
          have h2' := Finset.mem_product.mp (hMAB h2)
          have hv1' := Finset.mem_product.mp (hMAB hp₁)
          have hv2' := Finset.mem_product.mp (hMAB hp₂)
          simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq] at hq1 hq2
          rcases hq1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases hq2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr hu
            · exfalso; exact Finset.disjoint_left.mp hAB hv2'.1 h2'.2
          · exfalso; exact Finset.disjoint_left.mp hAB hv1'.1 h1'.2))
      · subst heq₁ heq₂
        have hm₁ := Finset.mem_product.mp (hM hp₁)
        have hm₂ := Finset.mem_product.mp (hM hp₂)
        have hv₁A : v₁ ∈ A := Finset.mem_of_mem_erase hm₁.1
        have hv₁x : v₁ ≠ x := Finset.ne_of_mem_erase hm₁.1
        have hu₁B : u₁ ∈ B := Finset.mem_of_mem_erase hm₁.2
        have hu₁y : u₁ ≠ y := Finset.ne_of_mem_erase hm₁.2
        have hv₂A : v₂ ∈ A := Finset.mem_of_mem_erase hm₂.1
        have hv₂x : v₂ ≠ x := Finset.ne_of_mem_erase hm₂.1
        have hu₂B : u₂ ∈ B := Finset.mem_of_mem_erase hm₂.2
        have hu₂y : u₂ ≠ y := Finset.ne_of_mem_erase hm₂.2
        refine Or.inr ⟨v₁, u₁, x, u₂, v₂, y, ?_, Or.inl rfl,
          Or.inr (Or.inr (Or.inr (Or.inl Sym2.eq_swap)))⟩
        exact isSixCycle_of_bipartite hAB hv₁A hx hv₂A hu₁B hu₂B hy
          hv₁x hv hv₂x.symm hu hu₁y hu₂y
          (hpath _ hp₁).2.1 (hpath _ hp₁).1 (hpath _ hp₂).1
          (hpath _ hp₂).2.1 (hpath _ hp₂).2.2 (hpath _ hp₁).2.2
  · intro e₁ e₂ he₁ he₂ ⟨hne, w, hw₁, hw₂⟩
    refine hshared he₁ he₂ hne (fun v₁ u₁ v₂ u₂ h1 h2 hq1 hq2 => ?_)
    subst hq1 hq2
    have h1' := Finset.mem_product.mp (hMAB h1)
    have h2' := Finset.mem_product.mp (hMAB h2)
    rw [Sym2.mem_iff] at hw₁ hw₂
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with h | h
    · exact Or.inl h
    · exfalso; exact Finset.disjoint_left.mp hAB h1'.1 (h ▸ h2'.2)
    · exfalso; exact Finset.disjoint_left.mp hAB (h ▸ h2'.1) h1'.2
    · exact Or.inr h

/-- **Complete Bipartite Subgraph `K_{a,b}` is `C₆`-Connected (Duke–Erdős–Rödl Proposition 0):**
For any disjoint vertex sets `X, Y` with `2 ≤ X.card` and `2 ≤ Y.card` such that every `x ∈ X`
and `y ∈ Y` are adjacent in `G`, the complete bipartite subgraph `H = subgraphOfBipEdges (X ×ˢ Y)`
satisfies `H ≤ G`, `H.edgeFinset.card = X.card * Y.card`, and `IsC6Connected H`. -/
theorem biclique_isC6Connected [Fintype V] {G : SimpleGraph V}
    {X Y : Finset V} (hXY : Disjoint X Y) (hX2 : 2 ≤ X.card) (hY2 : 2 ≤ Y.card)
    (hadj : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    let H := subgraphOfBipEdges (X ×ˢ Y)
    H ≤ G ∧ H.edgeFinset.card = X.card * Y.card ∧ IsC6Connected H := by
  intro H
  have hsub : X ×ˢ Y ⊆ X ×ˢ Y := Finset.Subset.refl _
  have hle : H ≤ G := subgraphOfBipEdges_le (fun p hp => by
    have h := Finset.mem_product.mp hp
    exact hadj p.1 h.1 p.2 h.2)
  have hcard : H.edgeFinset.card = X.card * Y.card := by
    rw [card_edgeFinset_subgraphOfBipEdges hXY hsub, Finset.card_product]
  rcases Finset.one_lt_card_iff.mp (by omega : 1 < X.card) with ⟨x₁, x₂, hx₁, hx₂, hxne⟩
  rcases Finset.one_lt_card_iff.mp (by omega : 1 < Y.card) with ⟨y₁, y₂, hy₁, hy₂, hyne⟩
  have hConn : IsC6Connected H := by
    refine gao_zhao_lemma_2_1 hXY hsub ?_ ?_ ?_ ?_
    · intro x hx
      exact ⟨y₁, hy₁, y₂, hy₂, hyne,
        Finset.mem_product.mpr ⟨hx, hy₁⟩, Finset.mem_product.mpr ⟨hx, hy₂⟩⟩
    · intro y hy
      exact ⟨x₁, hx₁, x₂, hx₂, hxne,
        Finset.mem_product.mpr ⟨hx₁, hy⟩, Finset.mem_product.mpr ⟨hx₂, hy⟩⟩
    · intro a₁ ha₁ a₂ ha₂
      exact ⟨y₁, hy₁, Finset.mem_product.mpr ⟨ha₁, hy₁⟩, Finset.mem_product.mpr ⟨ha₂, hy₁⟩⟩
    · intro b₁ hb₁ b₂ hb₂
      exact ⟨x₁, hx₁, Finset.mem_product.mpr ⟨hx₁, hb₁⟩, Finset.mem_product.mpr ⟨hx₁, hb₂⟩⟩
  exact ⟨hle, hcard, hConn⟩

/-- If `M ⊆ V_set ×ˢ U`, `1 ≤ V_set.card`, and `V_set.card < 2`, then `V_set = {v₀}` for some
`v₀ ∈ V_set` and `M.card ≤ U.card`. -/
lemma singleton_left_of_card_lt_two {V_set U : Finset V} {M : Finset (V × V)}
    (hM : M ⊆ V_set ×ˢ U) (h1 : 1 ≤ V_set.card) (h2 : V_set.card < 2) :
    ∃ v₀ ∈ V_set, V_set = {v₀} ∧ M.card ≤ U.card := by
  have hcard1 : V_set.card = 1 := by omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨v₀, hv₀⟩
  refine ⟨v₀, hv₀ ▸ Finset.mem_singleton_self v₀, hv₀, ?_⟩
  have hle := Finset.card_le_card hM
  rw [Finset.card_product, hcard1, one_mul] at hle
  exact hle

/-- If `M ⊆ V_set ×ˢ U`, `1 ≤ U.card`, and `U.card < 2`, then `U = {u₀}` for some
`u₀ ∈ U` and `M.card ≤ V_set.card`. -/
lemma singleton_right_of_card_lt_two {V_set U : Finset V} {M : Finset (V × V)}
    (hM : M ⊆ V_set ×ˢ U) (h1 : 1 ≤ U.card) (h2 : U.card < 2) :
    ∃ u₀ ∈ U, U = {u₀} ∧ M.card ≤ V_set.card := by
  have hcard1 : U.card = 1 := by omega
  rcases Finset.card_eq_one.mp hcard1 with ⟨u₀, hu₀⟩
  refine ⟨u₀, hu₀ ▸ Finset.mem_singleton_self u₀, hu₀, ?_⟩
  have hle := Finset.card_le_card hM
  rw [Finset.card_product, hcard1, mul_one] at hle
  exact hle

/-- **Gao–Zhao Petal/Star Core Theorem (arXiv:2610.34307, Proposition 2.6 core step):**
Given a bipartite pair `(A, B)` (`Disjoint A B`), endpoints `x ∈ A` and `y ∈ B`, and any bundle
`M ⊆ (A.erase x) ×ˢ (B.erase y)` of at least 2 middle edges `(v, u)` of 3-edge paths
`x - u - v - y` in `G`, there exists a subgraph `H ≤ G` with at least `M.card` edges that is
internally `C₆`-connected (`IsC6Connected H`). -/
theorem gao_zhao_petal_or_star_internal_c6_connected [Fintype V] {G : SimpleGraph V}
    {A B : Finset V} (hAB : Disjoint A B) {x y : V} (hx : x ∈ A) (hy : y ∈ B)
    {M : Finset (V × V)} (hM : M ⊆ (A.erase x) ×ˢ (B.erase y))
    (hpath : ∀ p ∈ M, G.Adj x p.2 ∧ G.Adj p.1 p.2 ∧ G.Adj p.1 y)
    (hM2 : 2 ≤ M.card) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      H ≤ G ∧ M.card ≤ H.edgeFinset.card ∧ IsC6Connected H := by
  let V_set := M.image Prod.fst
  let U := M.image Prod.snd
  have hVsub : V_set ⊆ A.erase x := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
    exact (Finset.mem_product.mp (hM hp)).1
  have hUsub : U ⊆ B.erase y := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
    exact (Finset.mem_product.mp (hM hp)).2
  have hMVU : M ⊆ V_set ×ˢ U := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hMne : M.Nonempty := Finset.card_pos.mp (by omega)
  have hV1 : 1 ≤ V_set.card := Finset.card_pos.mpr (hMne.image _)
  have hU1 : 1 ≤ U.card := Finset.card_pos.mpr (hMne.image _)
  by_cases hV2 : 2 ≤ V_set.card
  · by_cases hU2 : 2 ≤ U.card
    · -- Case 1: 2 ≤ V_set.card and 2 ≤ U.card -> Enlarged Petal Graph
      let X := insert x V_set
      let Y := insert y U
      let E := M ∪ (({x} : Finset V) ×ˢ U) ∪ (V_set ×ˢ ({y} : Finset V))
      have hXA : X ⊆ A := Finset.insert_subset_iff.mpr ⟨hx, hVsub.trans (Finset.erase_subset x A)⟩
      have hYB : Y ⊆ B := Finset.insert_subset_iff.mpr ⟨hy, hUsub.trans (Finset.erase_subset y B)⟩
      have hXY : Disjoint X Y := hAB.mono hXA hYB
      have hEXY : E ⊆ X ×ˢ Y := by
        rintro ⟨a, b⟩ hp
        simp only [E, Finset.mem_union, Finset.mem_product, Finset.mem_singleton] at hp
        rw [Finset.mem_product]
        rcases hp with (hp | ⟨hax, hu⟩) | ⟨hv, hby⟩
        · have hvu := Finset.mem_product.mp (hMVU hp)
          exact ⟨Finset.mem_insert_of_mem hvu.1, Finset.mem_insert_of_mem hvu.2⟩
        · subst a
          exact ⟨Finset.mem_insert_self x V_set, Finset.mem_insert_of_mem hu⟩
        · subst b
          exact ⟨Finset.mem_insert_of_mem hv, Finset.mem_insert_self y U⟩
      have hEG : ∀ p ∈ E, G.Adj p.1 p.2 := by
        rintro ⟨a, b⟩ hp
        simp only [E, Finset.mem_union, Finset.mem_product, Finset.mem_singleton] at hp
        rcases hp with (hp | ⟨hax, hu⟩) | ⟨hv, hby⟩
        · exact (hpath (a, b) hp).2.1
        · subst a
          rcases Finset.mem_image.mp hu with ⟨q, hq, hqb⟩
          exact hqb ▸ (hpath q hq).1
        · subst b
          rcases Finset.mem_image.mp hv with ⟨q, hq, hqa⟩
          exact hqa ▸ (hpath q hq).2.2
      refine ⟨subgraphOfBipEdges E, inferInstance, subgraphOfBipEdges_le hEG, ?_, ?_⟩
      · rw [card_edgeFinset_subgraphOfBipEdges hXY hEXY]
        exact Finset.card_le_card (Finset.subset_union_left.trans Finset.subset_union_left)
      · rcases Finset.one_lt_card_iff.mp (by omega : 1 < V_set.card) with ⟨v₁, v₂, hv₁, hv₂, hvne⟩
        rcases Finset.one_lt_card_iff.mp (by omega : 1 < U.card) with ⟨u₁, u₂, hu₁, hu₂, hune⟩
        refine gao_zhao_lemma_2_1 hXY hEXY ?_ ?_ ?_ ?_
        · intro a ha
          rcases Finset.mem_insert.mp ha with hax | haV
          · subst a
            refine ⟨u₁, Finset.mem_insert_of_mem hu₁, u₂, Finset.mem_insert_of_mem hu₂, hune, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hu₁⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hu₂⟩))
          · rcases Finset.mem_image.mp haV with ⟨p, hp, rfl⟩
            have hp2U : p.2 ∈ U := Finset.mem_image_of_mem Prod.snd hp
            have hp2y : p.2 ≠ y := Finset.ne_of_mem_erase (hUsub hp2U)
            refine ⟨y, Finset.mem_insert_self y U, p.2, Finset.mem_insert_of_mem hp2U,
              hp2y.symm, ?_, ?_⟩
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨haV, Finset.mem_singleton_self y⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
        · intro b hb
          rcases Finset.mem_insert.mp hb with hby | hbU
          · subst b
            refine ⟨v₁, Finset.mem_insert_of_mem hv₁, v₂, Finset.mem_insert_of_mem hv₂, hvne, ?_, ?_⟩
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨hv₁, Finset.mem_singleton_self y⟩)
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨hv₂, Finset.mem_singleton_self y⟩)
          · rcases Finset.mem_image.mp hbU with ⟨p, hp, rfl⟩
            have hp1V : p.1 ∈ V_set := Finset.mem_image_of_mem Prod.fst hp
            have hp1x : p.1 ≠ x := Finset.ne_of_mem_erase (hVsub hp1V)
            refine ⟨x, Finset.mem_insert_self x V_set, p.1, Finset.mem_insert_of_mem hp1V,
              hp1x.symm, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hbU⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
        · intro a₁ ha₁ a₂ ha₂
          rcases Finset.mem_insert.mp ha₁ with ha₁x | ha₁V <;>
            rcases Finset.mem_insert.mp ha₂ with ha₂x | ha₂V
          · subst a₁; subst a₂
            refine ⟨u₁, Finset.mem_insert_of_mem hu₁, ?_, ?_⟩ <;>
              exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hu₁⟩))
          · subst a₁
            rcases Finset.mem_image.mp ha₂V with ⟨p, hp, rfl⟩
            have hp2U : p.2 ∈ U := Finset.mem_image_of_mem Prod.snd hp
            refine ⟨p.2, Finset.mem_insert_of_mem hp2U, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hp2U⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
          · subst a₂
            rcases Finset.mem_image.mp ha₁V with ⟨p, hp, rfl⟩
            have hp2U : p.2 ∈ U := Finset.mem_image_of_mem Prod.snd hp
            refine ⟨p.2, Finset.mem_insert_of_mem hp2U, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hp2U⟩))
          · refine ⟨y, Finset.mem_insert_self y U, ?_, ?_⟩
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨ha₁V, Finset.mem_singleton_self y⟩)
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨ha₂V, Finset.mem_singleton_self y⟩)
        · intro b₁ hb₁ b₂ hb₂
          rcases Finset.mem_insert.mp hb₁ with hb₁y | hb₁U <;>
            rcases Finset.mem_insert.mp hb₂ with hb₂y | hb₂U
          · subst b₁; subst b₂
            refine ⟨v₁, Finset.mem_insert_of_mem hv₁, ?_, ?_⟩ <;>
              exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨hv₁, Finset.mem_singleton_self y⟩)
          · subst b₁
            rcases Finset.mem_image.mp hb₂U with ⟨p, hp, rfl⟩
            have hp1V : p.1 ∈ V_set := Finset.mem_image_of_mem Prod.fst hp
            refine ⟨p.1, Finset.mem_insert_of_mem hp1V, ?_, ?_⟩
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨hp1V, Finset.mem_singleton_self y⟩)
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
          · subst b₂
            rcases Finset.mem_image.mp hb₁U with ⟨p, hp, rfl⟩
            have hp1V : p.1 ∈ V_set := Finset.mem_image_of_mem Prod.fst hp
            refine ⟨p.1, Finset.mem_insert_of_mem hp1V, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ hp)
            · exact Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨hp1V, Finset.mem_singleton_self y⟩)
          · refine ⟨x, Finset.mem_insert_self x V_set, ?_, ?_⟩
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hb₁U⟩))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_product.mpr ⟨Finset.mem_singleton_self x, hb₂U⟩))
    · -- Case 2: 2 ≤ V_set.card and U.card = 1 -> Biclique K_{|V_set|, 2} on V_set ×ˢ {y, u₀}
      rcases singleton_right_of_card_lt_two hMVU hU1 (by omega) with ⟨u₀, hu₀U, hUeq, hMV⟩
      let Y := ({y, u₀} : Finset V)
      have hu₀B : u₀ ∈ B := Finset.mem_of_mem_erase (hUsub hu₀U)
      have hu₀y : u₀ ≠ y := Finset.ne_of_mem_erase (hUsub hu₀U)
      have hVA : V_set ⊆ A := hVsub.trans (Finset.erase_subset x A)
      have hYB : Y ⊆ B := by
        intro b hb
        simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact hy
        · exact hu₀B
      have hXY : Disjoint V_set Y := hAB.mono hVA hYB
      have hY2 : 2 ≤ Y.card := by
        rw [Finset.card_pair hu₀y.symm]
      have hadj : ∀ v ∈ V_set, ∀ b ∈ Y, G.Adj v b := by
        intro v hv b hb
        rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
        have hp2 : p.2 = u₀ := by
          have : p.2 ∈ U := Finset.mem_image_of_mem Prod.snd hp
          rw [hUeq, Finset.mem_singleton] at this
          exact this
        simp only [Y, Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl
        · exact (hpath p hp).2.2
        · exact hp2 ▸ (hpath p hp).2.1
      rcases biclique_isC6Connected hXY hV2 hY2 hadj with ⟨hle, hcard, hConn⟩
      refine ⟨subgraphOfBipEdges (V_set ×ˢ Y), inferInstance, hle, ?_, hConn⟩
      rw [hcard]
      calc M.card ≤ V_set.card := hMV
        _ ≤ V_set.card * Y.card := Nat.le_mul_of_pos_right _ (by omega)
  · -- Case 3: V_set.card = 1 and 2 ≤ U.card -> Biclique K_{2, |U|} on {x, v₀} ×ˢ U
    rcases singleton_left_of_card_lt_two hMVU hV1 (by omega) with ⟨v₀, hv₀V, hVeq, hMU⟩
    have hU2 : 2 ≤ U.card := by omega
    let X := ({x, v₀} : Finset V)
    have hv₀A : v₀ ∈ A := Finset.mem_of_mem_erase (hVsub hv₀V)
    have hv₀x : v₀ ≠ x := Finset.ne_of_mem_erase (hVsub hv₀V)
    have hXA : X ⊆ A := by
      intro a ha
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact hx
      · exact hv₀A
    have hUB : U ⊆ B := hUsub.trans (Finset.erase_subset y B)
    have hXY : Disjoint X U := hAB.mono hXA hUB
    have hX2 : 2 ≤ X.card := by
      rw [Finset.card_pair hv₀x.symm]
    have hadj : ∀ a ∈ X, ∀ u ∈ U, G.Adj a u := by
      intro a ha u hu
      rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
      have hp1 : p.1 = v₀ := by
        have : p.1 ∈ V_set := Finset.mem_image_of_mem Prod.fst hp
        rw [hVeq, Finset.mem_singleton] at this
        exact this
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · exact (hpath p hp).1
      · exact hp1 ▸ (hpath p hp).2.1
    rcases biclique_isC6Connected hXY hX2 hU2 hadj with ⟨hle, hcard, hConn⟩
    refine ⟨subgraphOfBipEdges (X ×ˢ U), inferInstance, hle, ?_, hConn⟩
    rw [hcard]
    calc M.card ≤ U.card := hMU
      _ ≤ X.card * U.card := Nat.le_mul_of_pos_left _ (by omega)

/-! ## Section 4: Bipartite Max-Cut, Degree Pruning, Path Double-Counting, and Main Positive Theorems -/

/-- The directed bipartite edges of `G` from `A` to `B`. -/
def bipEdges (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) : Finset (V × V) :=
  (A ×ˢ B).filter (fun p => G.Adj p.1 p.2)

/-- The number of neighbors of `v` inside `S`. -/
def bipDeg (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (fun u => G.Adj v u)).card

lemma bipEdges_subset_product (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    bipEdges G A B ⊆ A ×ˢ B :=
  Finset.filter_subset _ _

lemma adj_of_mem_bipEdges {G : SimpleGraph V} [DecidableRel G.Adj] {A B : Finset V}
    {p : V × V} (hp : p ∈ bipEdges G A B) : G.Adj p.1 p.2 :=
  (Finset.mem_filter.mp hp).2

lemma card_bipEdges_eq_sum_left (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (bipEdges G A B).card = ∑ a ∈ A, bipDeg G B a := by
  simp only [bipEdges, bipDeg, Finset.card_filter, Finset.sum_product]

lemma card_bipEdges_eq_sum_right (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (bipEdges G A B).card = ∑ b ∈ B, bipDeg G A b := by
  rw [bipEdges, Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [bipDeg, Finset.card_filter]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  by_cases h : G.Adj a b
  · simp [h, h.symm]
  · have h' : ¬ G.Adj b a := fun hba => h hba.symm
    simp [h, h']

lemma card_bipEdges_insert_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) {v : V} (hv : v ∉ A) :
    (bipEdges G (insert v A) B).card = bipDeg G B v + (bipEdges G A B).card := by
  rw [card_bipEdges_eq_sum_left, Finset.sum_insert hv, ← card_bipEdges_eq_sum_left]

lemma card_bipEdges_insert_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) {v : V} (hv : v ∉ B) :
    (bipEdges G A (insert v B)).card = bipDeg G A v + (bipEdges G A B).card := by
  rw [card_bipEdges_eq_sum_right, Finset.sum_insert hv, ← card_bipEdges_eq_sum_right]

lemma card_bipEdges_erase_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) {a : V} (ha : a ∈ A) :
    (bipEdges G A B).card = bipDeg G B a + (bipEdges G (A.erase a) B).card := by
  rw [card_bipEdges_eq_sum_left G A B, ← Finset.add_sum_erase A (fun x => bipDeg G B x) ha,
    ← card_bipEdges_eq_sum_left]

lemma card_bipEdges_erase_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) {b : V} (hb : b ∈ B) :
    (bipEdges G A B).card = bipDeg G A b + (bipEdges G A (B.erase b)).card := by
  rw [card_bipEdges_eq_sum_right G A B, ← Finset.add_sum_erase B (fun y => bipDeg G A y) hb,
    ← card_bipEdges_eq_sum_right]

lemma bipDeg_insert_self (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    bipDeg G (insert v S) v = bipDeg G S v := by
  have hirr : ¬ G.Adj v v := G.loopless.irrefl v
  simp only [bipDeg, Finset.filter_insert, hirr, ↓reduceIte]

lemma card_bipEdges_self_insert (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {v : V} (hv : v ∉ S) :
    (bipEdges G (insert v S) (insert v S)).card =
      2 * bipDeg G S v + (bipEdges G S S).card := by
  rw [card_bipEdges_insert_left G S (insert v S) hv,
    card_bipEdges_insert_right G S S hv, bipDeg_insert_self]
  omega

lemma bipDeg_union_of_disjoint (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} (hAB : Disjoint A B) (v : V) :
    bipDeg G (A ∪ B) v = bipDeg G A v + bipDeg G B v := by
  simp only [bipDeg, Finset.filter_union]
  exact Finset.card_union_of_disjoint (hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- Greedy Max-Cut on an arbitrary vertex subset `S`: there is a bipartition `A ∪ B = S`
holding at least half of the internal edges of `S`. -/
lemma exists_bipartite_cut_subset (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = S ∧
      (bipEdges G S S).card ≤ 4 * (bipEdges G A B).card := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨∅, ∅, Finset.disjoint_empty_left ∅, Finset.empty_union ∅, ?_⟩
    simp [bipEdges]
  | @insert v S hv ih =>
    rcases ih with ⟨A, B, hAB, hunion, hcard⟩
    have hvA : v ∉ A := fun h => hv (hunion ▸ Finset.mem_union_left B h)
    have hvB : v ∉ B := fun h => hv (hunion ▸ Finset.mem_union_right A h)
    have hdeg : bipDeg G S v = bipDeg G A v + bipDeg G B v := by
      rw [← hunion, bipDeg_union_of_disjoint G hAB v]
    have hself := card_bipEdges_self_insert G S hv
    by_cases hle : bipDeg G A v ≤ bipDeg G B v
    · refine ⟨insert v A, B, Finset.disjoint_insert_left.mpr ⟨hvB, hAB⟩, ?_, ?_⟩
      · rw [Finset.insert_union, hunion]
      · rw [card_bipEdges_insert_left G A B hvA]
        omega
    · refine ⟨A, insert v B, Finset.disjoint_insert_right.mpr ⟨hvA, hAB⟩, ?_, ?_⟩
      · rw [Finset.union_insert, hunion]
      · rw [card_bipEdges_insert_right G A B hvB]
        omega

/-- Every finite simple graph `G` has a bipartite cut `(A, B)` with at least `e(G)/2` edges. -/
theorem exists_bipartite_cut_ge_half [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ A B : Finset V, Disjoint A B ∧ G.edgeFinset.card ≤ 2 * (bipEdges G A B).card := by
  rcases exists_bipartite_cut_subset G Finset.univ with ⟨A, B, hAB, _, hcard⟩
  refine ⟨A, B, hAB, ?_⟩
  have huniv : (bipEdges G Finset.univ Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [card_bipEdges_eq_sum_left]
    have hdeg : ∀ v : V, bipDeg G Finset.univ v = G.degree v := by
      intro v
      simp [bipDeg, SimpleGraph.degree, SimpleGraph.neighborFinset]
    simp_rw [hdeg]
    exact G.sum_degrees_eq_twice_card_edges
  omega

/-- Iterative minimum-degree pruning on a bipartite graph: removing vertices of degree `< d₀`
loses at most `(|A| + |B| - |A'| - |B'|) * d₀` edges and leaves minimum degree `≥ d₀` on both sides. -/
theorem exists_pruned_bipartite_subgraph (G : SimpleGraph V) [DecidableRel G.Adj]
    (d₀ : ℕ) (A B : Finset V) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
      (∀ a ∈ A', d₀ ≤ bipDeg G B' a) ∧
      (∀ b ∈ B', d₀ ≤ bipDeg G A' b) ∧
      (bipEdges G A B).card + (A'.card + B'.card) * d₀ ≤
        (bipEdges G A' B').card + (A.card + B.card) * d₀ := by
  suffices h : ∀ k : ℕ, ∀ A B : Finset V, A.card + B.card = k →
      ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧
        (∀ a ∈ A', d₀ ≤ bipDeg G B' a) ∧
        (∀ b ∈ B', d₀ ≤ bipDeg G A' b) ∧
        (bipEdges G A B).card + (A'.card + B'.card) * d₀ ≤
          (bipEdges G A' B').card + (A.card + B.card) * d₀ from
    h (A.card + B.card) A B rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro A B hcard
    by_cases hA : ∃ a ∈ A, bipDeg G B a < d₀
    · rcases hA with ⟨a, ha, hdeg⟩
      have hcardA : (A.erase a).card + 1 = A.card := Finset.card_erase_add_one ha
      have hlt : (A.erase a).card + B.card < k := by omega
      rcases ih ((A.erase a).card + B.card) hlt (A.erase a) B rfl with
        ⟨A', B', hA', hB', hdegA', hdegB', hineq⟩
      refine ⟨A', B', hA'.trans (Finset.erase_subset a A), hB', hdegA', hdegB', ?_⟩
      have herase := card_bipEdges_erase_left G A B ha
      have hmul : (A.card + B.card) * d₀ = ((A.erase a).card + B.card) * d₀ + d₀ := by
        have : A.card + B.card = ((A.erase a).card + B.card) + 1 := by omega
        rw [this, Nat.add_mul, Nat.one_mul]
      omega
    · by_cases hB : ∃ b ∈ B, bipDeg G A b < d₀
      · rcases hB with ⟨b, hb, hdeg⟩
        have hcardB : (B.erase b).card + 1 = B.card := Finset.card_erase_add_one hb
        have hlt : A.card + (B.erase b).card < k := by omega
        rcases ih (A.card + (B.erase b).card) hlt A (B.erase b) rfl with
          ⟨A', B', hA', hB', hdegA', hdegB', hineq⟩
        refine ⟨A', B', hA', hB'.trans (Finset.erase_subset b B), hdegA', hdegB', ?_⟩
        have herase := card_bipEdges_erase_right G A B hb
        have hmul : (A.card + B.card) * d₀ = (A.card + (B.erase b).card) * d₀ + d₀ := by
          have : A.card + B.card = (A.card + (B.erase b).card) + 1 := by omega
          rw [this, Nat.add_mul, Nat.one_mul]
        omega
      · push Not at hA hB
        exact ⟨A, B, Finset.Subset.rfl, Finset.Subset.rfl, hA, hB, le_rfl⟩

/-- The bundle of middle edges `(v, u) ∈ (A' \ {x}) × (B' \ {y})` of 3-edge paths `x - u - v - y`. -/
def middleEdgeBundle (G : SimpleGraph V) [DecidableRel G.Adj]
    (A' B' : Finset V) (x y : V) : Finset (V × V) :=
  ((A'.erase x) ×ˢ (B'.erase y)).filter (fun p => G.Adj x p.2 ∧ G.Adj p.1 p.2 ∧ G.Adj p.1 y)

lemma middleEdgeBundle_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A' B' : Finset V) (x y : V) :
    middleEdgeBundle G A' B' x y ⊆ (A'.erase x) ×ˢ (B'.erase y) :=
  Finset.filter_subset _ _

lemma middleEdgeBundle_adj {G : SimpleGraph V} [DecidableRel G.Adj]
    {A' B' : Finset V} {x y : V} {p : V × V} (hp : p ∈ middleEdgeBundle G A' B' x y) :
    G.Adj x p.2 ∧ G.Adj p.1 p.2 ∧ G.Adj p.1 y :=
  (Finset.mem_filter.mp hp).2

lemma card_sub_one_le_card_erase (S : Finset V) (a : V) :
    S.card - 1 ≤ (S.erase a).card := by
  by_cases ha : a ∈ S
  · have h := Finset.card_erase_add_one ha
    omega
  · rw [Finset.erase_eq_of_notMem ha]
    omega

/-- Double-counting 3-edge paths in a bipartite graph `(A', B')` with minimum degree `≥ d₀`:
each middle edge `(v, u) ∈ bipEdges G A' B'` extends to at least `(d₀ - 1)²` endpoint pairs `(x, y)`,
so some pair `(x, y) ∈ A' ×ˢ B'` is joined by at least `4 * e(A', B') * (d₀ - 1)² / n²` 3-edge paths. -/
theorem exists_endpoint_pair_many_three_paths [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {A' B' : Finset V} {d₀ : ℕ} (hAB : Disjoint A' B')
    (hdegA : ∀ a ∈ A', d₀ ≤ bipDeg G B' a)
    (hdegB : ∀ b ∈ B', d₀ ≤ bipDeg G A' b)
    (hpos : 0 < (bipEdges G A' B').card) :
    ∃ x ∈ A', ∃ y ∈ B',
      4 * (bipEdges G A' B').card * (d₀ - 1) ^ 2 ≤
        (Fintype.card V) ^ 2 * (middleEdgeBundle G A' B' x y).card := by
  have hsum : (bipEdges G A' B').card * (d₀ - 1) ^ 2 ≤
      ∑ q ∈ A' ×ˢ B', (middleEdgeBundle G A' B' q.1 q.2).card := by
    have h1 : ∑ q ∈ A' ×ˢ B', (middleEdgeBundle G A' B' q.1 q.2).card =
        ∑ q ∈ A' ×ˢ B', ∑ p ∈ bipEdges G A' B',
          if p ∈ middleEdgeBundle G A' B' q.1 q.2 then 1 else 0 := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      rw [← Finset.card_filter]
      congr 1
      ext p
      simp only [middleEdgeBundle, bipEdges, Finset.mem_filter, Finset.mem_product,
        Finset.mem_erase]
      tauto
    rw [h1, Finset.sum_comm]
    have h2 : ∀ p ∈ bipEdges G A' B',
        (d₀ - 1) ^ 2 ≤ ∑ q ∈ A' ×ˢ B',
          if p ∈ middleEdgeBundle G A' B' q.1 q.2 then 1 else 0 := by
      intro p hp
      rw [← Finset.card_filter]
      have hp_mem := Finset.mem_filter.mp hp
      have hp1 : p.1 ∈ A' := (Finset.mem_product.mp hp_mem.1).1
      have hp2 : p.2 ∈ B' := (Finset.mem_product.mp hp_mem.1).2
      have hadj : G.Adj p.1 p.2 := hp_mem.2
      let X_p := (A'.filter (fun x => G.Adj p.2 x)).erase p.1
      let Y_p := (B'.filter (fun y => G.Adj p.1 y)).erase p.2
      have hsub : X_p ×ˢ Y_p ⊆
          (A' ×ˢ B').filter (fun q => p ∈ middleEdgeBundle G A' B' q.1 q.2) := by
        intro q hq
        rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
        simp only [X_p, Y_p, Finset.mem_erase, Finset.mem_filter] at hq1 hq2
        simp only [middleEdgeBundle, Finset.mem_filter, Finset.mem_product, Finset.mem_erase]
        exact ⟨⟨hq1.2.1, hq2.2.1⟩, ⟨⟨hq1.1.symm, hp1⟩, ⟨hq2.1.symm, hp2⟩⟩,
          hq1.2.2.symm, hadj, hq2.2.2⟩
      have hXp : d₀ - 1 ≤ X_p.card := by
        have hdeg2 : d₀ ≤ (A'.filter (fun x => G.Adj p.2 x)).card := hdegB p.2 hp2
        have hcard_er : (A'.filter (fun x => G.Adj p.2 x)).card - 1 ≤ X_p.card :=
          card_sub_one_le_card_erase (A'.filter (fun x => G.Adj p.2 x)) p.1
        exact (Nat.sub_le_sub_right hdeg2 1).trans hcard_er
      have hYp : d₀ - 1 ≤ Y_p.card := by
        have hdeg1 : d₀ ≤ (B'.filter (fun y => G.Adj p.1 y)).card := hdegA p.1 hp1
        have hcard_er : (B'.filter (fun y => G.Adj p.1 y)).card - 1 ≤ Y_p.card :=
          card_sub_one_le_card_erase (B'.filter (fun y => G.Adj p.1 y)) p.2
        exact (Nat.sub_le_sub_right hdeg1 1).trans hcard_er
      calc (d₀ - 1) ^ 2 = (d₀ - 1) * (d₀ - 1) := sq (d₀ - 1)
        _ ≤ X_p.card * Y_p.card := Nat.mul_le_mul hXp hYp
        _ = (X_p ×ˢ Y_p).card := (Finset.card_product X_p Y_p).symm
        _ ≤ ((A' ×ˢ B').filter (fun q => p ∈ middleEdgeBundle G A' B' q.1 q.2)).card :=
            Finset.card_le_card hsub
    calc (bipEdges G A' B').card * (d₀ - 1) ^ 2
        = ∑ _p ∈ bipEdges G A' B', (d₀ - 1) ^ 2 := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ p ∈ bipEdges G A' B', ∑ q ∈ A' ×ˢ B',
          if p ∈ middleEdgeBundle G A' B' q.1 q.2 then 1 else 0 :=
          Finset.sum_le_sum h2
  have hne : (A' ×ˢ B').Nonempty := by
    rcases Finset.card_pos.mp hpos with ⟨p, hp⟩
    exact ⟨p, bipEdges_subset_product G A' B' hp⟩
  have hsum_scaled : ∑ _q ∈ A' ×ˢ B', (bipEdges G A' B').card * (d₀ - 1) ^ 2 ≤
      ∑ q ∈ A' ×ˢ B', (A' ×ˢ B').card * (middleEdgeBundle G A' B' q.1 q.2).card := by
    rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
    exact Nat.mul_le_mul_left (A' ×ˢ B').card hsum
  rcases Finset.exists_le_of_sum_le hne hsum_scaled with ⟨q, hq, hq_le⟩
  rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
  refine ⟨q.1, hq1, q.2, hq2, ?_⟩
  have hAB_le : A'.card + B'.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hAB]
    exact Finset.card_le_univ (A' ∪ B')
  have hprod_le : 4 * (A' ×ˢ B').card ≤ (Fintype.card V) ^ 2 := by
    rw [Finset.card_product]
    have h4 : 4 * (A'.card * B'.card) ≤ (A'.card + B'.card) ^ 2 := by
      zify
      nlinarith [sq_nonneg ((A'.card : ℤ) - (B'.card : ℤ))]
    calc 4 * (A'.card * B'.card) ≤ (A'.card + B'.card) ^ 2 := h4
      _ ≤ (Fintype.card V) ^ 2 := Nat.pow_le_pow_left hAB_le 2
  calc 4 * (bipEdges G A' B').card * (d₀ - 1) ^ 2
      = 4 * ((bipEdges G A' B').card * (d₀ - 1) ^ 2) := by ring
    _ ≤ 4 * ((A' ×ˢ B').card * (middleEdgeBundle G A' B' q.1 q.2).card) :=
        Nat.mul_le_mul_left 4 hq_le
    _ = (4 * (A' ×ˢ B').card) * (middleEdgeBundle G A' B' q.1 q.2).card := by ring
    _ ≤ (Fintype.card V) ^ 2 * (middleEdgeBundle G A' B' q.1 q.2).card :=
        Nat.mul_le_mul_right _ hprod_le

/-- Threshold-parameterized 3-edge path bundle extraction: for any degree threshold `d₀` with
`4 * n * d₀ ≤ e(G)` and `0 < e(G)`, `G` contains a disjoint pair `(A', B')` and endpoints
`x ∈ A'`, `y ∈ B'` whose middle-edge bundle `M` satisfies `e(G) * (d₀ - 1)² ≤ n² * |M|`. -/
theorem exists_three_path_bundle_of_threshold [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {d₀ : ℕ} (hpos : 0 < G.edgeFinset.card)
    (hd₀ : 4 * Fintype.card V * d₀ ≤ G.edgeFinset.card) :
    ∃ A' B' : Finset V, Disjoint A' B' ∧
      ∃ x ∈ A', ∃ y ∈ B',
        G.edgeFinset.card * (d₀ - 1) ^ 2 ≤
          (Fintype.card V) ^ 2 * (middleEdgeBundle G A' B' x y).card := by
  rcases exists_bipartite_cut_ge_half G with ⟨A, B, hAB, hcut⟩
  rcases exists_pruned_bipartite_subgraph G d₀ A B with
    ⟨A', B', hA', hB', hdegA', hdegB', hprune⟩
  have hAB' : Disjoint A' B' := hAB.mono hA' hB'
  have hAB_card : A.card + B.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hAB]
    exact Finset.card_le_univ (A ∪ B)
  have hrem : G.edgeFinset.card ≤ 4 * (bipEdges G A' B').card := by
    have h1 : (A.card + B.card) * d₀ ≤ Fintype.card V * d₀ :=
      Nat.mul_le_mul_right d₀ hAB_card
    have h2 : 4 * ((A.card + B.card) * d₀) ≤ 4 * Fintype.card V * d₀ := by
      calc 4 * ((A.card + B.card) * d₀) ≤ 4 * (Fintype.card V * d₀) :=
            Nat.mul_le_mul_left 4 h1
        _ = 4 * Fintype.card V * d₀ := by ring
    omega
  have hpos' : 0 < (bipEdges G A' B').card := by omega
  rcases exists_endpoint_pair_many_three_paths G hAB' hdegA' hdegB' hpos' with
    ⟨x, hx, y, hy, hpaths⟩
  refine ⟨A', B', hAB', x, hx, y, hy, ?_⟩
  calc G.edgeFinset.card * (d₀ - 1) ^ 2
      ≤ 4 * (bipEdges G A' B').card * (d₀ - 1) ^ 2 :=
        Nat.mul_le_mul_right ((d₀ - 1) ^ 2) hrem
    _ ≤ (Fintype.card V) ^ 2 * (middleEdgeBundle G A' B' x y).card := hpaths

lemma two_mul_card_edgeFinset_le_sq [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    2 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2 := by
  have huniv : (bipEdges G Finset.univ Finset.univ).card = 2 * G.edgeFinset.card := by
    rw [card_bipEdges_eq_sum_left]
    have hdeg : ∀ v : V, bipDeg G Finset.univ v = G.degree v := by
      intro v
      simp [bipDeg, SimpleGraph.degree, SimpleGraph.neighborFinset]
    simp_rw [hdeg]
    exact G.sum_degrees_eq_twice_card_edges
  rw [← huniv]
  calc (bipEdges G Finset.univ Finset.univ).card
      ≤ (Finset.univ ×ˢ Finset.univ : Finset (V × V)).card :=
        Finset.card_le_card (bipEdges_subset_product G Finset.univ Finset.univ)
    _ = (Fintype.card V) ^ 2 := by
        rw [Finset.card_product, Finset.card_univ, sq]

/-- Dense 3-edge path bundle extraction: whenever `0 < e(G)` and `512 * n⁴ ≤ e(G)³`,
there exist disjoint vertex sets `A', B'` and endpoints `x ∈ A'`, `y ∈ B'` whose middle-edge
bundle `M = middleEdgeBundle G A' B' x y` has `2 ≤ M.card` and `e(G)³ ≤ 256 * n⁴ * M.card`. -/
theorem exists_dense_three_path_bundle [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpos : 0 < G.edgeFinset.card)
    (hdense : 512 * (Fintype.card V) ^ 4 ≤ G.edgeFinset.card ^ 3) :
    ∃ A' B' : Finset V, Disjoint A' B' ∧
      ∃ x ∈ A', ∃ y ∈ B',
        2 ≤ (middleEdgeBundle G A' B' x y).card ∧
        G.edgeFinset.card ^ 3 ≤
          256 * (Fintype.card V) ^ 4 * (middleEdgeBundle G A' B' x y).card := by
  let n := Fintype.card V
  let m := G.edgeFinset.card
  have h2m : 2 * m ≤ n ^ 2 := two_mul_card_edgeFinset_le_sq G
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    have : 2 * m ≤ 0 := by rw [hn0] at h2m; simpa using h2m
    omega
  have hn4_pos : 0 < n ^ 4 := Nat.pow_pos hn_pos
  have h16n : 16 * n ≤ m := by
    by_contra hlt
    have hm_le : m ≤ 16 * n := by omega
    have hcube : 2 * m ^ 3 ≤ 256 * n ^ 4 := by
      calc 2 * m ^ 3 = (2 * m) * (m * m) := by ring
        _ ≤ n ^ 2 * ((16 * n) * (16 * n)) :=
          Nat.mul_le_mul h2m (Nat.mul_le_mul hm_le hm_le)
        _ = 256 * n ^ 4 := by ring
    have h512 : 1024 * n ^ 4 ≤ 2 * m ^ 3 := by
      calc 1024 * n ^ 4 = 2 * (512 * n ^ 4) := by ring
        _ ≤ 2 * m ^ 3 := Nat.mul_le_mul_left 2 hdense
    omega
  let d₀ := m / (8 * n) + 1
  have hd₀_sub : d₀ - 1 = m / (8 * n) := rfl
  have hdiv_mod := Nat.div_add_mod m (8 * n)
  have hmod_lt : m % (8 * n) < 8 * n := Nat.mod_lt m (by omega)
  have hd₀_bound : 4 * n * d₀ ≤ m := by
    have h8d : 2 * (4 * n * d₀) = (8 * n) * (m / (8 * n)) + 8 * n := by
      dsimp [d₀]
      ring
    omega
  have hd₀_lower : m ≤ 16 * n * (d₀ - 1) := by
    have h16d : 16 * n * (d₀ - 1) = 2 * ((8 * n) * (m / (8 * n))) := by
      rw [hd₀_sub]
      ring
    omega
  rcases exists_three_path_bundle_of_threshold G hpos hd₀_bound with
    ⟨A', B', hAB', x, hx, y, hy, hbundle⟩
  have hM_bound : m ^ 3 ≤ 256 * n ^ 4 * (middleEdgeBundle G A' B' x y).card := by
    calc m ^ 3 = m * m ^ 2 := by ring
      _ ≤ m * (16 * n * (d₀ - 1)) ^ 2 :=
          Nat.mul_le_mul_left m (Nat.pow_le_pow_left hd₀_lower 2)
      _ = 256 * n ^ 2 * (m * (d₀ - 1) ^ 2) := by ring
      _ ≤ 256 * n ^ 2 * (n ^ 2 * (middleEdgeBundle G A' B' x y).card) :=
          Nat.mul_le_mul_left (256 * n ^ 2) hbundle
      _ = 256 * n ^ 4 * (middleEdgeBundle G A' B' x y).card := by ring
  refine ⟨A', B', hAB', x, hx, y, hy, ?_, hM_bound⟩
  by_contra hlt2
  have hle1 : (middleEdgeBundle G A' B' x y).card ≤ 1 := by omega
  have h1 : 256 * n ^ 4 * (middleEdgeBundle G A' B' x y).card ≤ 256 * n ^ 4 := by
    calc 256 * n ^ 4 * (middleEdgeBundle G A' B' x y).card
        ≤ 256 * n ^ 4 * 1 := Nat.mul_le_mul_left (256 * n ^ 4) hle1
      _ = 256 * n ^ 4 := Nat.mul_one _
  have h2 : 512 * n ^ 4 ≤ 256 * n ^ 4 := hdense.trans (hM_bound.trans h1)
  omega

/-- **Weakened Quantitative Version of Gao–Zhao Proposition 2.6 (arXiv:2610.34307):**
Every finite simple graph `G` on `n` vertices with `e(G) > 0` and `512 * n⁴ ≤ e(G)³`
contains an internally `C₆`-connected subgraph `H₁ ≤ G` (every two distinct edges of `H₁` lie
on a common `C₄` or `C₆` inside `H₁`) with `e(G)³ ≤ 256 * n⁴ * e(H₁)`, i.e.
`e(H₁) ≥ e(G)³ / (256 n⁴) = Ω(δ³ n²)`.
(Factor-of-4 constant relaxation from the paper's `128 n⁴` / `64 n⁴` bounds due to the 3-path
counting lemma, preserving the exact optimal range `β ≤ 2/3` and asymptotic order `Θ(δ³ n²)`.) -/
theorem gao_zhao_internal_c6_connected_subgraph [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hpos : 0 < G.edgeFinset.card)
    (hdense : 512 * (Fintype.card V) ^ 4 ≤ G.edgeFinset.card ^ 3) :
    ∃ (H₁ : SimpleGraph V) (_ : DecidableRel H₁.Adj),
      H₁ ≤ G ∧
      G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card V) ^ 4 * H₁.edgeFinset.card ∧
      IsC6Connected H₁ := by
  rcases exists_dense_three_path_bundle G hpos hdense with
    ⟨A', B', hAB', x, hx, y, hy, hM2, hM_bound⟩
  rcases gao_zhao_petal_or_star_internal_c6_connected hAB' hx hy
    (middleEdgeBundle_subset G A' B' x y)
    (fun p hp => middleEdgeBundle_adj hp) hM2 with ⟨H₁, hDec, hle, hcard, hConn⟩
  refine ⟨H₁, hDec, hle, ?_, hConn⟩
  exact hM_bound.trans (Nat.mul_le_mul_left (256 * (Fintype.card V) ^ 4) hcard)

/-- **Corollary of Proposition 2.6 (Internal `C₈`-Connected Subgraph):**
Every finite simple graph `G` on `n` vertices with `e(G) > 0` and `512 * n⁴ ≤ e(G)³`
contains an internally `C₈`-connected subgraph `H₂ ≤ G` (every two distinct edges of `H₂` lie
on a common cycle of length at most `8` inside `H₂`) with `e(G)³ ≤ 256 * n⁴ * e(H₂)`, i.e.
`e(H₂) = Ω(δ³ n²)` (immediate from `gao_zhao_internal_c6_connected_subgraph` since `C₆`-connectedness
implies `C₈`-connectedness, improving the Duke–Erdős–Rödl `δ¹² n²` bound to cubic density dependence). -/
theorem dense_internal_c8_connected_subgraph [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hpos : 0 < G.edgeFinset.card)
    (hdense : 512 * (Fintype.card V) ^ 4 ≤ G.edgeFinset.card ^ 3) :
    ∃ (H₂ : SimpleGraph V) (_ : DecidableRel H₂.Adj),
      H₂ ≤ G ∧
      G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card V) ^ 4 * H₂.edgeFinset.card ∧
      IsC8Connected H₂ := by
  rcases gao_zhao_internal_c6_connected_subgraph G hpos hdense with
    ⟨H₁, hDec, hle, hbound, hConn6⟩
  exact ⟨H₁, hDec, hle, hbound, hConn6.isC8Connected⟩

/-- **Ambient Strong `C₆` Subgraph (Li Definition 1.1(ii), proved in Gao–Zhao's quantitative range):**
Every finite simple graph `G` on `n` vertices with `e(G) > 0` and `512 * n⁴ ≤ e(G)³`
contains a subgraph `H₁ ≤ G` with `e(G)³ ≤ 256 * n⁴ * e(H₁)` that is ambiently strongly
`C₆`-connected in `G`: every two distinct edges of `H₁` lie on a common `C₄` or `C₆` in `G`,
and every two distinct edges of `H₁` sharing a vertex lie on a common `C₄` in `G`.
(Holds uniformly for all `n` up to `β ≤ 2/3` with `C₄`/`C₆` witnesses, implying Eric Li's
asymptotic `β < 1/2` Theorem 1.3 in `arXiv:2606.06522`.) -/
theorem li_ambient_strong_c6_subgraph [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hpos : 0 < G.edgeFinset.card)
    (hdense : 512 * (Fintype.card V) ^ 4 ≤ G.edgeFinset.card ^ 3) :
    ∃ (H₁ : SimpleGraph V) (_ : DecidableRel H₁.Adj),
      H₁ ≤ G ∧
      G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card V) ^ 4 * H₁.edgeFinset.card ∧
      IsAmbientStronglyC6Connected G H₁ := by
  rcases exists_dense_three_path_bundle G hpos hdense with
    ⟨A', B', hAB', x, hx, y, hy, _, hM_bound⟩
  let M := middleEdgeBundle G A' B' x y
  rcases li_opposite_edges_ambient_strong_c6 hAB' hx hy
    (middleEdgeBundle_subset G A' B' x y)
    (fun p hp => middleEdgeBundle_adj hp) with ⟨hcard, hStrong⟩
  refine ⟨subgraphOfBipEdges M, inferInstance, hStrong.1, ?_, hStrong⟩
  rw [hcard]
  exact hM_bound

/-! ## Section 5: Counterexamples and Negative Resolutions (Internal Strong `C₆` & Subquadratic `C₈`) -/

lemma IsFourCycle.mono {G H : SimpleGraph V} (hle : H ≤ G) {v₁ v₂ v₃ v₄ : V}
    (h : IsFourCycle H v₁ v₂ v₃ v₄) : IsFourCycle G v₁ v₂ v₃ v₄ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    hle h.2.2.2.2.2.2.1, hle h.2.2.2.2.2.2.2.1,
    hle h.2.2.2.2.2.2.2.2.1, hle h.2.2.2.2.2.2.2.2.2⟩

lemma IsSixCycle.mono {G H : SimpleGraph V} (hle : H ≤ G) {v₁ v₂ v₃ v₄ v₅ v₆ : V}
    (h : IsSixCycle H v₁ v₂ v₃ v₄ v₅ v₆) : IsSixCycle G v₁ v₂ v₃ v₄ v₅ v₆ :=
  ⟨h.1, hle h.2.1, hle h.2.2.1, hle h.2.2.2.1, hle h.2.2.2.2.1,
    hle h.2.2.2.2.2.1, hle h.2.2.2.2.2.2⟩

lemma IsEightCycle.mono {G H : SimpleGraph V} (hle : H ≤ G) {v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V}
    (h : IsEightCycle H v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈) :
    IsEightCycle G v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ :=
  ⟨h.1, hle h.2.1, hle h.2.2.1, hle h.2.2.2.1, hle h.2.2.2.2.1,
    hle h.2.2.2.2.2.1, hle h.2.2.2.2.2.2.1, hle h.2.2.2.2.2.2.2.1,
    hle h.2.2.2.2.2.2.2.2⟩

/-- **Structural Obstruction to Internal Strong `C₆`-Connectedness (Corollary of Lemma 2.1 + `C₄`-freeness):**
In any `C₄`-free graph `G`, every subgraph `H ≤ G` satisfying the internal strong `C₆` condition
(`IsInternallyStronglyC6Connected H`) has at most `1` edge (`e(H) ≤ 1`).
Indeed, any two distinct edges of `H` would lie on a `C₄` or `C₆` in `H`, and any `C₆` in `H`
contains two consecutive edges sharing a vertex, which by the internal strong condition would
have to lie on a `C₄` in `H ≤ G`, impossible. -/
theorem card_edgeFinset_le_one_of_internallyStronglyC6_of_no_C4 [Fintype V]
    {G H : SimpleGraph V} [DecidableRel H.Adj] (hle : H ≤ G)
    (hnoC4 : ∀ v₁ v₂ v₃ v₄ : V, ¬ IsFourCycle G v₁ v₂ v₃ v₄)
    (hStrong : IsInternallyStronglyC6Connected H) :
    H.edgeFinset.card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun e₁ he₁ e₂ he₂ => ?_)
  by_contra hne
  rw [SimpleGraph.mem_edgeFinset] at he₁ he₂
  rcases hStrong.1 he₁ he₂ hne with hC4 | hC6
  · rcases hC4 with ⟨v₁, v₂, v₃, v₄, h4, _, _⟩
    exact hnoC4 v₁ v₂ v₃ v₄ (h4.mono hle)
  · rcases hC6 with ⟨v₁, v₂, v₃, v₄, v₅, v₆, h6, _, _⟩
    have hf₁ : s(v₁, v₂) ∈ H.edgeSet := h6.2.1
    have hf₂ : s(v₂, v₃) ∈ H.edgeSet := h6.2.2.1
    have hnodup := h6.1
    simp only [List.nodup_cons, List.mem_cons] at hnodup
    have hv12 : v₁ ≠ v₂ := fun h => hnodup.1 (Or.inl h)
    have hv13 : v₁ ≠ v₃ := fun h => hnodup.1 (Or.inr (Or.inl h))
    have hf_ne : s(v₁, v₂) ≠ s(v₂, v₃) := by
      intro h_eq
      rcases Sym2.eq_iff.mp h_eq with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact hv12 h1
      · exact hv13 h1
    have hshare : EdgesShareVertex s(v₁, v₂) s(v₂, v₃) :=
      ⟨hf_ne, v₂, Sym2.mem_mk_right v₁ v₂, Sym2.mem_mk_left v₂ v₃⟩
    rcases hStrong.2 hf₁ hf₂ hshare with ⟨u₁, u₂, u₃, u₄, h4, _, _⟩
    exact hnoC4 u₁ u₂ u₃ u₄ (h4.mono hle)

/-- **Structural Obstruction to Subquadratic `C₈`-Connectedness:**
If a host graph `G` has girth `> 8` (no 4-cycle, 6-cycle, or 8-cycle), then every internally
`C₈`-connected subgraph `H₂ ≤ G` has at most `1` edge (`e(H₂) ≤ 1`). -/
theorem card_edgeFinset_le_one_of_isC8Connected_of_girth_gt_8 [Fintype V]
    {G H₂ : SimpleGraph V} [DecidableRel H₂.Adj] (hle : H₂ ≤ G)
    (hnoC4 : ∀ v₁ v₂ v₃ v₄ : V, ¬ IsFourCycle G v₁ v₂ v₃ v₄)
    (hnoC6 : ∀ v₁ v₂ v₃ v₄ v₅ v₆ : V, ¬ IsSixCycle G v₁ v₂ v₃ v₄ v₅ v₆)
    (hnoC8 : ∀ v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ : V, ¬ IsEightCycle G v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈)
    (hConn8 : IsC8Connected H₂) :
    H₂.edgeFinset.card ≤ 1 := by
  refine Finset.card_le_one.mpr (fun e₁ he₁ e₂ he₂ => ?_)
  by_contra hne
  rw [SimpleGraph.mem_edgeFinset] at he₁ he₂
  rcases hConn8 he₁ he₂ hne with hC4 | hC6 | hC8
  · rcases hC4 with ⟨v₁, v₂, v₃, v₄, h4, _, _⟩
    exact hnoC4 v₁ v₂ v₃ v₄ (h4.mono hle)
  · rcases hC6 with ⟨v₁, v₂, v₃, v₄, v₅, v₆, h6, _, _⟩
    exact hnoC6 v₁ v₂ v₃ v₄ v₅ v₆ (h6.mono hle)
  · rcases hC8 with ⟨v₁, v₂, v₃, v₄, v₅, v₆, v₇, v₈, h8, _, _⟩
    exact hnoC8 v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ (h8.mono hle)

/-- Vertices of the explicit `C₄`-free biaffine incidence graph over `ZMod q`:
`(false, (s, a))` represents the line `Y = s X + a`, and `(true, (x, y))` represents the point `(x, y)`. -/
abbrev BiaffineVertex (q : ℕ) := Bool × (ZMod q × ZMod q)

/-- Parameterization of the `q³` incidences `((s, a), x) ↦ ((false, (s, a)), (true, (x, s*x + a)))`. -/
def biaffineParamEdge (q : ℕ) (t : (ZMod q × ZMod q) × ZMod q) :
    BiaffineVertex q × BiaffineVertex q :=
  ((false, t.1), (true, (t.2, t.1.1 * t.2 + t.1.2)))

/-- The directed edge set of the biaffine incidence graph over `ZMod q`. -/
def biaffineEdges (q : ℕ) [NeZero q] : Finset (BiaffineVertex q × BiaffineVertex q) :=
  Finset.univ.image (biaffineParamEdge q)

/-- The biaffine incidence graph `B_q` on `2 q²` vertices with `q³` edges. -/
def biaffineGraph (q : ℕ) [NeZero q] : SimpleGraph (BiaffineVertex q) :=
  subgraphOfBipEdges (biaffineEdges q)

instance (q : ℕ) [NeZero q] : DecidableRel (biaffineGraph q).Adj :=
  inferInstanceAs (DecidableRel (subgraphOfBipEdges (biaffineEdges q)).Adj)

lemma biaffineParamEdge_injective (q : ℕ) :
    Function.Injective (biaffineParamEdge q) := by
  intro t₁ t₂ h
  simp only [biaffineParamEdge, Prod.mk.injEq] at h
  exact Prod.ext h.1.2 h.2.2.1

lemma card_biaffineVertex (q : ℕ) [NeZero q] :
    Fintype.card (BiaffineVertex q) = 2 * q ^ 2 := by
  simp only [BiaffineVertex, Fintype.card_prod, Fintype.card_bool, ZMod.card]
  ring

lemma card_edgeFinset_biaffineGraph (q : ℕ) [NeZero q] :
    (biaffineGraph q).edgeFinset.card = q ^ 3 := by
  let L : Finset (BiaffineVertex q) :=
    Finset.univ.filter (fun v => v.1 = false)
  let R : Finset (BiaffineVertex q) :=
    Finset.univ.filter (fun v => v.1 = true)
  have hLR : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    simp only [L, R, Finset.mem_filter] at hvL hvR
    have : false = true := hvL.2.symm.trans hvR.2
    exact Bool.false_ne_true this
  have hsub : biaffineEdges q ⊆ L ×ˢ R := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨t, _, rfl⟩
    simp [L, R, biaffineParamEdge]
  have hcard : (subgraphOfBipEdges (biaffineEdges q)).edgeFinset.card = (biaffineEdges q).card :=
    card_edgeFinset_subgraphOfBipEdges hLR hsub
  change (subgraphOfBipEdges (biaffineEdges q)).edgeFinset.card = q ^ 3
  rw [hcard, biaffineEdges,
    Finset.card_image_of_injective _ (biaffineParamEdge_injective q), Finset.card_univ]
  simp only [Fintype.card_prod, ZMod.card]
  ring

lemma biaffineGraph_adj_iff (q : ℕ) [NeZero q] (u v : BiaffineVertex q) :
    (biaffineGraph q).Adj u v ↔
      (u.1 = false ∧ v.1 = true ∧ v.2.2 = u.2.1 * v.2.1 + u.2.2) ∨
      (v.1 = false ∧ u.1 = true ∧ u.2.2 = v.2.1 * u.2.1 + v.2.2) := by
  constructor
  · intro hadj
    rcases hadj with ⟨_, hmem | hmem⟩
    · rcases Finset.mem_image.mp hmem with ⟨t, _, ht⟩
      left
      have hu : (false, t.1) = u := (Prod.mk.injEq _ _ _ _ |>.mp ht).1
      have hv : (true, (t.2, t.1.1 * t.2 + t.1.2)) = v := (Prod.mk.injEq _ _ _ _ |>.mp ht).2
      rw [← hu, ← hv]
      exact ⟨rfl, rfl, rfl⟩
    · rcases Finset.mem_image.mp hmem with ⟨t, _, ht⟩
      right
      have hv : (false, t.1) = v := (Prod.mk.injEq _ _ _ _ |>.mp ht).1
      have hu : (true, (t.2, t.1.1 * t.2 + t.1.2)) = u := (Prod.mk.injEq _ _ _ _ |>.mp ht).2
      rw [← hv, ← hu]
      exact ⟨rfl, rfl, rfl⟩
  · intro h
    rcases h with ⟨hu1, hv1, heq⟩ | ⟨hv1, hu1, heq⟩
    · refine ⟨?_, Or.inl ?_⟩
      · intro huv
        have : false = true := hu1.symm.trans (huv ▸ hv1)
        exact Bool.false_ne_true this
      · rw [biaffineEdges, Finset.mem_image]
        refine ⟨(u.2, v.2.1), Finset.mem_univ _, ?_⟩
        exact Prod.ext (Prod.ext hu1.symm rfl) (Prod.ext hv1.symm (Prod.ext rfl heq.symm))
    · refine ⟨?_, Or.inr ?_⟩
      · intro huv
        have : true = false := hu1.symm.trans (huv ▸ hv1)
        exact Bool.false_ne_true this.symm
      · rw [biaffineEdges, Finset.mem_image]
        refine ⟨(v.2, u.2.1), Finset.mem_univ _, ?_⟩
        exact Prod.ext (Prod.ext hv1.symm rfl) (Prod.ext hu1.symm (Prod.ext rfl heq.symm))

lemma no_two_lines_two_points (q : ℕ) [Fact (Nat.Prime q)]
    {l₁ l₂ p₁ p₂ : ZMod q × ZMod q} (hl : l₁ ≠ l₂) (hp : p₁ ≠ p₂)
    (h11 : p₁.2 = l₁.1 * p₁.1 + l₁.2) (h12 : p₁.2 = l₂.1 * p₁.1 + l₂.2)
    (h21 : p₂.2 = l₁.1 * p₂.1 + l₁.2) (h22 : p₂.2 = l₂.1 * p₂.1 + l₂.2) : False := by
  have hmul : (l₁.1 - l₂.1) * (p₁.1 - p₂.1) = 0 := by
    calc (l₁.1 - l₂.1) * (p₁.1 - p₂.1)
        = (l₁.1 * p₁.1 + l₁.2 - (l₂.1 * p₁.1 + l₂.2)) -
          (l₁.1 * p₂.1 + l₁.2 - (l₁.1 * 0 + l₂.1 * p₂.1 + l₂.2)) := by ring
      _ = (p₁.2 - p₁.2) - (p₂.2 - p₂.2) := by
          have h0 : l₁.1 * 0 + l₂.1 * p₂.1 + l₂.2 = l₂.1 * p₂.1 + l₂.2 := by ring
          rw [h0, ← h11, ← h12, ← h21, ← h22]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hmul with hs | hx
  · have hs_eq : l₁.1 = l₂.1 := sub_eq_zero.mp hs
    have ha_eq : l₁.2 = l₂.2 := by
      have h : l₁.1 * p₁.1 + l₁.2 = l₂.1 * p₁.1 + l₂.2 := h11.symm.trans h12
      rw [hs_eq] at h
      exact add_left_cancel h
    exact hl (Prod.ext hs_eq ha_eq)
  · have hx_eq : p₁.1 = p₂.1 := sub_eq_zero.mp hx
    have hy_eq : p₁.2 = p₂.2 := by
      rw [h11, h21, hx_eq]
    exact hp (Prod.ext hx_eq hy_eq)

/-- Over any prime field `ZMod q`, the biaffine incidence graph `biaffineGraph q` is `C₄`-free. -/
theorem biaffineGraph_no_fourCycle (q : ℕ) [Fact (Nat.Prime q)]
    (v₁ v₂ v₃ v₄ : BiaffineVertex q) :
    ¬ IsFourCycle (biaffineGraph q) v₁ v₂ v₃ v₄ := by
  intro ⟨_, hv13, _, _, hv24, _, h12, h23, h34, h41⟩
  rw [biaffineGraph_adj_iff] at h12 h23 h34 h41
  rcases h12 with ⟨hv1_f, hv2_t, eq12⟩ | ⟨hv2_f, hv1_t, eq12⟩
  · have h23' : v₃.1 = false ∧ v₂.1 = true ∧ v₂.2.2 = v₃.2.1 * v₂.2.1 + v₃.2.2 := by
      rcases h23 with ⟨hv2_f, _, _⟩ | h23'
      · exfalso; exact Bool.false_ne_true (hv2_f.symm.trans hv2_t)
      · exact h23'
    have h34' : v₃.1 = false ∧ v₄.1 = true ∧ v₄.2.2 = v₃.2.1 * v₄.2.1 + v₃.2.2 := by
      rcases h34 with h34' | ⟨_, hv3_t, _⟩
      · exact h34'
      · exfalso; exact Bool.false_ne_true (h23'.1.symm.trans hv3_t)
    have h41' : v₁.1 = false ∧ v₄.1 = true ∧ v₄.2.2 = v₁.2.1 * v₄.2.1 + v₁.2.2 := by
      rcases h41 with ⟨hv4_f, _, _⟩ | h41'
      · exfalso; exact Bool.false_ne_true (hv4_f.symm.trans h34'.2.1)
      · exact h41'
    have hl : v₁.2 ≠ v₃.2 := fun h => hv13 (Prod.ext (hv1_f.trans h23'.1.symm) h)
    have hp : v₂.2 ≠ v₄.2 := fun h => hv24 (Prod.ext (hv2_t.trans h34'.2.1.symm) h)
    exact no_two_lines_two_points q hl hp eq12 h23'.2.2 h41'.2.2 h34'.2.2
  · have h23' : v₂.1 = false ∧ v₃.1 = true ∧ v₃.2.2 = v₂.2.1 * v₃.2.1 + v₂.2.2 := by
      rcases h23 with h23' | ⟨_, hv2_t, _⟩
      · exact h23'
      · exfalso; exact Bool.false_ne_true (hv2_f.symm.trans hv2_t)
    have h34' : v₄.1 = false ∧ v₃.1 = true ∧ v₃.2.2 = v₄.2.1 * v₃.2.1 + v₄.2.2 := by
      rcases h34 with ⟨hv3_f, _, _⟩ | h34'
      · exfalso; exact Bool.false_ne_true (hv3_f.symm.trans h23'.2.1)
      · exact h34'
    have h41' : v₄.1 = false ∧ v₁.1 = true ∧ v₁.2.2 = v₄.2.1 * v₁.2.1 + v₄.2.2 := by
      rcases h41 with h41' | ⟨_, hv4_t, _⟩
      · exact h41'
      · exfalso; exact Bool.false_ne_true (h34'.1.symm.trans hv4_t)
    have hl : v₂.2 ≠ v₄.2 := fun h => hv24 (Prod.ext (hv2_f.trans h34'.1.symm) h)
    have hp : v₁.2 ≠ v₃.2 := fun h => hv13 (Prod.ext (hv1_t.trans h23'.2.1.symm) h)
    exact no_two_lines_two_points q hl hp eq12 h41'.2.2 h23'.2.2 h34'.2.2

/-- **Biaffine Obstruction to Internal Strong `C₆`-Connectedness (Corollary of Lemma 2.1 + `C₄`-freeness of `B_Q`, Gao–Zhao §2, arXiv:2610.34307):**
For every prime `q`, the biaffine incidence graph `biaffineGraph q` has `N = 2 q²` vertices
and `q³` edges (`e(G) = (N/2)^(3/2)`), yet every internally strongly `C₆`-connected subgraph
`H ≤ biaffineGraph q` has at most `1` edge (`e(H) ≤ 1`).
(Obstructs the internal strong `C₆` variant at `β = 1/2`; distinct from Li Theorem 1.4's
random shift-lift obstruction for `β ≥ 1/3`.) -/
theorem internal_strong_c6_biaffine_obstruction (q : ℕ) [Fact (Nat.Prime q)] :
    Fintype.card (BiaffineVertex q) = 2 * q ^ 2 ∧
    (biaffineGraph q).edgeFinset.card = q ^ 3 ∧
    ∀ (H : SimpleGraph (BiaffineVertex q)) [DecidableRel H.Adj],
      H ≤ biaffineGraph q → IsInternallyStronglyC6Connected H → H.edgeFinset.card ≤ 1 :=
  ⟨card_biaffineVertex q, card_edgeFinset_biaffineGraph q,
    fun _ _ hle hStrong =>
      card_edgeFinset_le_one_of_internallyStronglyC6_of_no_C4 hle
        (biaffineGraph_no_fourCycle q) hStrong⟩

/-- **2026 Resolution Package for Erdős Problem #584 (JSP-000473, Gao–Zhao arXiv:2610.34307 & Li arXiv:2606.06522):**
Packages the 2026 positive and negative results for `JSP-000473` (rather than a literal
clause-by-clause formalization of the 1984 fixed-`δ` internal strong `H₁` statement):
1. **Internal `C₆`-Connected Subgraph of Cubic Density (`gao_zhao_internal_c6_connected_subgraph`):**
   Weakened quantitative version of Gao–Zhao Proposition 2.6: every `n`-vertex simple graph `G`
   with `e(G) > 0` and `512 n⁴ ≤ e(G)³` contains an internally `C₆`-connected subgraph `H₁ ≤ G`
   with `e(G)³ ≤ 256 n⁴ e(H₁)`.
2. **Internal `C₈`-Connected Subgraph of Cubic Density (`dense_internal_c8_connected_subgraph`):**
   Corollary of Proposition 2.6: every such graph `G` contains an internally `C₈`-connected
   subgraph `H₂ ≤ G` with `e(G)³ ≤ 256 n⁴ e(H₂)`, improving the Duke–Erdős–Rödl `δ¹² n²` bound to `Ω(δ³ n²)`.
3. **Ambient Strong `C₆` Subgraph of Cubic Density (`li_ambient_strong_c6_subgraph`):**
   Li Definition 1.1(ii) proved in Gao–Zhao's quantitative range: every such graph `G` contains
   a subgraph `H₁' ≤ G` with `e(G)³ ≤ 256 n⁴ e(H₁')` that is ambiently strongly `C₆`-connected in `G`.
4. **Biaffine Obstruction to Internal Strong `C₆` (`internal_strong_c6_biaffine_obstruction`):**
   Corollary of Lemma 2.1 + `C₄`-freeness of `B_Q`: for every prime `q`, `biaffineGraph q` has
   `2 q²` vertices and `q³` edges, yet every internally strongly `C₆`-connected subgraph
   `H ≤ biaffineGraph q` has `e(H) ≤ 1`. -/
theorem erdos_584_duke_erdos_rodl_resolution :
    (∀ {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj],
      0 < G.edgeFinset.card → 512 * (Fintype.card W) ^ 4 ≤ G.edgeFinset.card ^ 3 →
      (∃ (H₁ : SimpleGraph W) (_ : DecidableRel H₁.Adj),
        H₁ ≤ G ∧ G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card W) ^ 4 * H₁.edgeFinset.card ∧
        IsC6Connected H₁) ∧
      (∃ (H₂ : SimpleGraph W) (_ : DecidableRel H₂.Adj),
        H₂ ≤ G ∧ G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card W) ^ 4 * H₂.edgeFinset.card ∧
        IsC8Connected H₂) ∧
      (∃ (H₁' : SimpleGraph W) (_ : DecidableRel H₁'.Adj),
        H₁' ≤ G ∧ G.edgeFinset.card ^ 3 ≤ 256 * (Fintype.card W) ^ 4 * H₁'.edgeFinset.card ∧
        IsAmbientStronglyC6Connected G H₁')) ∧
    (∀ (q : ℕ) [Fact (Nat.Prime q)],
      Fintype.card (BiaffineVertex q) = 2 * q ^ 2 ∧
      (biaffineGraph q).edgeFinset.card = q ^ 3 ∧
      ∀ (H : SimpleGraph (BiaffineVertex q)) [DecidableRel H.Adj],
        H ≤ biaffineGraph q → IsInternallyStronglyC6Connected H → H.edgeFinset.card ≤ 1) := by
  refine ⟨?_, fun q _ => internal_strong_c6_biaffine_obstruction q⟩
  intro W _ _ G _ hpos hdense
  exact ⟨gao_zhao_internal_c6_connected_subgraph G hpos hdense,
    dense_internal_c8_connected_subgraph G hpos hdense,
    li_ambient_strong_c6_subgraph G hpos hdense⟩

end JSP000473
