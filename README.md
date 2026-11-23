# Formalization of JSP-000473 (Erdős Problem #584)

Complete, `sorry`-free Lean 4 + Mathlib (`v4.34.0`) formalization of **JSP-000473** (**Erdős Problem #584**, proposed by Duke, Erdős, and Rödl no later than 1982 / published in 1984):

> *Must a dense graph contain a large subgraph in which every two edges lie on a common short cycle?*
>
> More precisely, let $G$ be a graph with $n$ vertices and $\delta n^2$ edges.
> 1. Is there a subgraph $H_1 \subseteq G$ with $\gg \delta^3 n^2$ edges such that any two edges in $H_1$ lie on a common cycle of length at most $6$ in $H_1$ (and moreover any two edges sharing a vertex lie on a common cycle of length $4$)?
> 2. Is there a subgraph $H_2 \subseteq G$ with $\gg_\delta n^2$ edges such that any two edges in $H_2$ lie on a common cycle of length at most $8$ in $H_2$ (improving the Duke–Erdős–Rödl $\delta^{12} n^2$ bound, or extending it to subquadratic density $\delta = n^{-o(1)}$)?

## Summary of Formalized Theorems (`JSP473.lean` & `Proof.lean`)

| Theorem / Definition | File & Line | Mathematical Statement |
| --- | --- | --- |
| `IsFourCycle`, `IsSixCycle`, `IsEightCycle`, `IsC6Connected`, `IsC8Connected` | `JSP473.lean` | Simple cycles $C_4, C_6, C_8$ and internal $C_{\le 6}$- / $C_{\le 8}$-connectedness of a graph $H$. |
| `IsAmbientStronglyC6Connected`, `IsInternallyStronglyC6Connected` | `JSP473.lean` | Strong $C_{\le 6}$-connectedness (including the condition that any two distinct edges sharing a vertex lie on a common $C_4$), both in the ambient host graph $G$ and internally inside $H$. |
| `gao_zhao_lemma_2_1` | `JSP473.lean` | **Gao–Zhao Lemma 2.1 (`arXiv:2610.34307`):** Every bipartite graph on disjoint vertex classes $(X, Y)$ with minimum degree $\ge 2$ in which every pair of vertices in the same class has a common neighbor is internally $C_6$-connected. |
| `li_opposite_edges_ambient_strong_c6` | `JSP473.lean` | **Eric Li Opposite-Edge Core (`arXiv:2606.06522`, Theorem 1.3):** Given any bundle $M$ of middle edges of 3-edge paths between $x \in A$ and $y \in B$, the subgraph $H = \text{subgraphOfBipEdges } M$ has $|M|$ edges and is ambiently strongly $C_6$-connected in $G$. |
| `biclique_isC6Connected` | `JSP473.lean` | **Duke–Erdős–Rödl Proposition 0:** Any complete bipartite subgraph $K_{a,b} \subseteq G$ with $a, b \ge 2$ is internally $C_6$-connected with $a b$ edges. |
| `gao_zhao_petal_or_star_internal_c6_connected` | `JSP473.lean` | **Gao–Zhao Proposition 2.6 Core (`arXiv:2610.34307`):** Any middle-edge bundle $M$ of 3-edge paths between $x \in A$ and $y \in B$ with $|M| \ge 2$ yields an internally $C_6$-connected subgraph $H \le G$ (either an enlarged petal graph $M \cup (V \times \{y\}) \cup (\{x\} \times U)$ or a complete bipartite subgraph $K_{a,2}$ / $K_{2,b}$) with $e(H) \ge |M|$. |
| `exists_bipartite_cut_ge_half` | `JSP473.lean` | Greedy bipartite Max-Cut: every finite simple graph $G$ admits a disjoint vertex partition $(A, B)$ with $2 e_G(A, B) \ge e(G)$. |
| `exists_pruned_bipartite_subgraph` | `JSP473.lean` | Iterative minimum-degree pruning on a bipartite cut preserving at least $e_G(A, B) - (|A| + |B|) d_0$ edges while guaranteeing minimum degree $\ge d_0$ on both sides. |
| `exists_endpoint_pair_many_three_paths` | `JSP473.lean` | Double-counting 3-edge paths by their middle edge in a pruned bipartite subgraph. |
| `gao_zhao_internal_c6_connected_subgraph` | `JSP473.lean` | **Weakened quantitative version of Gao–Zhao Proposition 2.6 (`arXiv:2610.34307`):** Every $n$-vertex simple graph $G$ with $e(G) > 0$ and $e(G)^3 \ge 512 n^4$ contains an internally $C_6$-connected subgraph $H_1 \le G$ with $256 n^4 e(H_1) \ge e(G)^3$, i.e. $e(H_1) \ge \frac{1}{256}\delta^3 n^2$ (a factor-of-4 constant relaxation from the paper's $128 n^4 / 64 n^4$ bounds due to the 3-path counting lemma, preserving the exact optimal range $\beta \le 2/3$ and asymptotic order $\Theta(\delta^3 n^2)$). |
| `dense_internal_c8_connected_subgraph` | `JSP473.lean` | **Corollary of Proposition 2.6:** Every $n$-vertex simple graph $G$ with $e(G) > 0$ and $e(G)^3 \ge 512 n^4$ contains an internally $C_8$-connected subgraph $H_2 \le G$ with $256 n^4 e(H_2) \ge e(G)^3$ (immediate since $C_6$-connectedness implies $C_8$-connectedness), improving the Duke–Erdős–Rödl $\delta^{12} n^2$ bound to $\Omega(\delta^3 n^2)$. |
| `li_ambient_strong_c6_subgraph` | `JSP473.lean` | **Li Definition 1.1(ii), proved in Gao–Zhao's quantitative range (`arXiv:2606.06522` + `arXiv:2610.34307`):** Every $n$-vertex simple graph $G$ with $e(G) > 0$ and $e(G)^3 \ge 512 n^4$ contains an ambiently strongly $C_6$-connected subgraph $H_1' \le G$ with $256 n^4 e(H_1') \ge e(G)^3$ (using $C_4/C_6$ witnesses, which imply Li's length $\le 6$ cycle condition, uniformly for all $n$ up to $\beta \le 2/3$ — stronger in range and uniformity than Li Theorem 1.3's asymptotic $\beta < 1/2$ statement). |
| `card_edgeFinset_le_one_of_internallyStronglyC6_of_no_C4` | `JSP473.lean` | **Corollary of Lemma 2.1 + $C_4$-freeness:** In any $C_4$-free graph $G$, every subgraph $H \le G$ satisfying the internal strong $C_6$ condition has at most $1$ edge ($e(H) \le 1$). |
| `biaffineGraph_no_fourCycle` & `internal_strong_c6_biaffine_obstruction` | `JSP473.lean` | **Corollary of Lemma 2.1 + $C_4$-freeness of $B_Q$ (Gao–Zhao §2, `arXiv:2610.34307`):** Explicit construction of the biaffine incidence graph `biaffineGraph q` over $\mathbb{F}_q$ on $N = 2 q^2$ vertices with $q^3$ edges, proven $C_4$-free and hence having $e(H) \le 1$ for every internally strongly $C_6$-connected subgraph $H \le \text{biaffineGraph } q$ (obstructing the internal strong variant at $\beta = 1/2$; distinct from Li Theorem 1.4's random shift-lift obstruction for $\beta \ge 1/3$). |
| `card_edgeFinset_le_one_of_isC8Connected_of_girth_gt_8` | `JSP473.lean` | Every host graph $G$ of girth $> 8$ satisfies $e(H_2) \le 1$ for every internally $C_8$-connected subgraph $H_2 \le G$. |
| `erdos_584_duke_erdos_rodl_resolution` | `JSP473.lean` | **2026 resolution package (Gao–Zhao `arXiv:2610.34307` + Li `arXiv:2606.06522`):** Conjunction of the three cubic-density positive existence theorems (internal $C_6$/$C_8$ up to $\beta = 2/3$ and ambient strong $C_6$) and the prime-field biaffine obstruction to internal strong $C_6$-connectedness at $\beta = 1/2$. Packages the 2026 resolution status rather than a literal clause-by-clause formalization of the 1984 fixed-$\delta$ internal strong $H_1$ statement. |

## Verification

- **Toolchain:** `leanprover/lean4:v4.34.0`
- **Mathlib:** `v4.34.0` (`5ed2965256430c3649e86755f9576b54eca72435`)
- **Build & Axiom Check:**
  ```bash
  lake build
  lake env lean Proof.lean
  ```
- **Axioms:** All exported theorems depend only on the standard Lean 4 axioms `[propext, Classical.choice, Quot.sound]`.

## Attribution

- **Mathematical results:** Guorong Gao and Run Zhao (*On a problem of Duke–Erdős–Rödl on cycle-connected subgraphs*, `arXiv:2610.34307`, 2026); Eric Li (*Short cycles in dense graphs*, `arXiv:2606.06522`, 2026); Richard A. Duke, Paul Erdős, and Vojtěch Rödl (*More results on subgraphs with many short cycles*, Proc. 15th Southeastern Conf. Combinatorics, Graph Theory and Computing, Congressus Numerantium 43, 1984, 295–300).
- **Lean 4 formalization:** Qin Zhao (`Drag0ndddd1118`).
