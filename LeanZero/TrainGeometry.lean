import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs

example : True := by trivial

structure TrainMap (Station : Type) where
  StationSet : Finset Station
  hStationSetIsNonEmpty : Finset.Nonempty StationSet
  G : SimpleGraph StationSet
  hConnected : G.Connected
  W : G.edgeSet → NNReal
  hNoZeroEdge : ∀ e :G.edgeSet , W e > 0

def walk_wehigt [AddZeroClass R]
  (G : SimpleGraph V) (W : G.edgeSet → R) (p : G.Walk u v): R :=
  List.foldl (fun acc d => acc + W ⟨d.edge, d.edge_mem⟩) 0 p.darts

noncomputable def TrainMap.distance
  (t : TrainMap Station) (x y : t.StationSet) : NNReal :=
  ⨅ p : t.G.Path x y, walk_wehigt t.G t.W p.val

theorem TraiMap.nonempty_path (t : TrainMap Station) (x y : t.StationSet) :
  Nonempty (t.G.Path x y) := by
  classical
  obtain ⟨w⟩ := t.hConnected x y
  exact ⟨w.toPath⟩

#check (α : Type) → (V : Set α) → Sym2 V

theorem TrainMap.finite_edges (t : TrainMap Station) :
    t.G.edgeSet.Finite := by
  -- 頂点集合は有限（Finset の coercion なので Fintype が付く）
  have h_vertex : Finite t.StationSet := inferInstance
  -- 頂点集合^2 も有限
  have h_prod : Finite (t.StationSet × t.StationSet) := inferInstance
  -- 辺の住む型 Sym2 は 頂点集合^2 の全射像（Sym2.mk）なので有限
  have h_sym2 : Finite (Sym2 t.StationSet) :=
    @Finite.of_surjective _ _ h_prod _ Sym2.mk_surjective
  -- したがって全体集合 univ は有限集合
  have h_univ : (Set.univ : Set (Sym2 t.StationSet)).Finite := @Set.finite_univ _ h_sym2
  -- edgeSet はその部分集合
  have h_subset : t.G.edgeSet ⊆ (Set.univ : Set (Sym2 t.StationSet)) :=
    Set.subset_univ _
  -- 有限集合の部分集合は有限
  exact h_univ.subset h_subset

/-- `finite_edges` の自動探索版。
`Set.toFinite (s) [Finite ↑s] : s.Finite` は前提が全部インスタンス引数なので、
「頂点集合が有限 → 頂点集合^2 が有限 → Sym2 が有限 → その部分型が有限」を
型クラス推論が丸ごと辿ってくれる。`exact?` もこれを見つける。 -/
theorem TrainMap.finite_edges2 (t : TrainMap Station) :
    t.G.edgeSet.Finite :=
  --Set.toFinite _
  --by apply Set.toFinite
  --by apply?
  by exact?
  --by hint

/-- 路線図に含まれる全ての単純道の集合。
始点・終点も動かすので `Σ x y, t.G.Path x y` 上の `Finset` になる。
`Path.instFintype` が効くよう、駅の等号判定と隣接判定を仮定として受け取る
（この 2 つがあれば実際に列挙が走る）。 -/
def TrainMap.set_all_paths (t : TrainMap Station)
    [DecidableEq Station] [DecidableRel t.G.Adj] :
    Finset (Σ x y : t.StationSet, t.G.Path x y) :=
  Finset.univ

/-- 駅 `x` と `y` を結ぶ単純道の全体。
`t.G.Path x y` という型自体が既に「`x` から `y` への単純道」なので、
その上の集合としては全体集合になる。 -/
def TrainMap.all_paths_2_vertices (t : TrainMap Station)
    (x y : t.StationSet) :
    Set (t.G.Path x y) :=
  Set.univ

@[simp]
theorem finite_TrainMap.all_paths_vertices (t : TrainMap Station)
  (x y : t.StationSet) :
  Finite (t.G.Path x y) := by
  classical
  exact Finite.of_fintype _

@[simp]
theorem nonempty_TrainMap.all_paths_vertices (t : TrainMap Station)
  (x y : t.StationSet) :
  Nonempty (t.G.Path x y) := by
  exact TraiMap.nonempty_path t x y

/-- 非空な有限全順序集合には最小元がある。
`Finite.exists_min f : ∃ x₀, ∀ x, f x₀ ≤ f x` を `f = id` で使うだけ。
`x`, `h_finite`, `h_nonmepty` は明示引数だが、型がクラスなので
ローカルインスタンスとして推論に拾われる。 -/
theorem nonempty_finite_total_order_has_minimum_vallue
  (x : LinearOrder α) (h_finite: Finite α) (h_nonmepty : Nonempty α) :
  ∃ m : α, ∀ n : α, m ≤ n
  := Finite.exists_min id

/-- 名前の通り、`x`-`y` 間の道は全部入っている。 -/
@[simp]
theorem TrainMap.mem_all_paths_2_vertices (t : TrainMap Station)
    (x y : t.StationSet) (p : t.G.Path x y) :
    p ∈ t.all_paths_2_vertices x y :=
  Set.mem_univ p

/-- `all_paths_2_vertices` の計算可能版。`Finset` なので実際に列挙でき、
最短経路を取るときはこちらを使う。 -/
def TrainMap.finset_paths_2_vertices (t : TrainMap Station)
    [DecidableEq Station] [DecidableRel t.G.Adj]
    (x y : t.StationSet) :
    Finset (t.G.Path x y) :=
  Finset.univ

/-- 名前の通り、全ての道が入っている。 -/
@[simp]
theorem TrainMap.mem_set_all_paths (t : TrainMap Station)
    [DecidableEq Station] [DecidableRel t.G.Adj]
    (p : Σ x y : t.StationSet, t.G.Path x y) :
    p ∈ t.set_all_paths :=
  Finset.mem_univ p

@[simp]
theorem TrainMap.set_all_paths_finite (t : TrainMap Station)
    [DecidableEq Station] [DecidableRel t.G.Adj] :
  Finite $ TrainMap.set_all_paths t :=
  Finite.of_fintype _

/-- 路線図に含まれる道の全体は有限。
駅集合が有限 → 各ペアの道が有限（`Path.instFintype`）→ Σ 型全体が有限、という連鎖。
`Finite` は `Prop` なので decidability の仮定は要らず、`classical` で足りる。 -/
theorem TrainMap.finite_paths (t : TrainMap Station) :
    Finite (Σ x y : t.StationSet, t.G.Path x y) := by
  classical
  --exact Finite.of_fintype ((x : ↥t.StationSet) × (y : ↥t.StationSet) × t.G.Path x y)
  exact Finite.of_fintype _

theorem Finite.exists_min2 [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty

--def TrainMap.distance (t : TrainMap Station) (x y : TrainMap Station) : NNReal :=
  --match TrainMap
--def TrainMap.distance2
--  (t : TrainMap Station) (x y : t.StationSet) : NNReal :=
--where
--  getMinWehightPath ()
--theorem TrainMap.nonempty_path (t : TrainMap Station) (x y : t.StationSet) :
--    Nonempty (t.G.Path x y) := by
--  classical
--  obtain ⟨w⟩ := t.hConnected x y
--  exact ⟨w.toPath⟩
--
--theorem TrainMap.distance_le (t : TrainMap Station) (x y : t.StationSet)
--    (p : t.G.Path x y) : t.distance x y ≤ walk_wehigt t.G t.W p.val :=
--  ciInf_le (OrderBot.bddBelow _) p
