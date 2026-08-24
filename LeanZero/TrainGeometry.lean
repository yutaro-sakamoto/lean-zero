import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.NNReal.Defs

example : True := by trivial

structure TrainMap (Station : Type) where
  StationSet : Finset Station
  G : SimpleGraph StationSet
  hConnected : G.Connected
  W : G.edgeSet → NNReal

def walk_wehigt [AddZeroClass R]
  (G : SimpleGraph V) (W : G.edgeSet → R) (p : G.Walk u v): R :=
  List.foldl (fun acc d => acc + W ⟨d.edge, d.edge_mem⟩) 0 p.darts

noncomputable def TrainMap.distance
  (t : TrainMap Station) (x y : t.StationSet) : NNReal :=
  ⨅ p : t.G.Path x y, walk_wehigt t.G t.W p.val

theorem TrainMap.nonempty_path (t : TrainMap Station) (x y : t.StationSet) :
    Nonempty (t.G.Path x y) := by
  classical
  obtain ⟨w⟩ := t.hConnected x y
  exact ⟨w.toPath⟩

theorem TrainMap.distance_le (t : TrainMap Station) (x y : t.StationSet)
    (p : t.G.Path x y) : t.distance x y ≤ walk_wehigt t.G t.W p.val :=
  ciInf_le (OrderBot.bddBelow _) p
