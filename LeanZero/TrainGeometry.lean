import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
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
