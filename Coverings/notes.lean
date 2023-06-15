import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.PathConnected
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Homeomorph
import Mathlib.Topology.SubsetProperties
import Mathlib.Topology.Maps
import Mathlib.Topology.UnitInterval

open Classical Set TopologicalSpace Topology Filter Function unitInterval


variable {X : Type _} [TopologicalSpace X]
--  [TopologicalSpace X] (x₀ : X) {x₁ : X }

lemma lem_Patrick (X : Type _) (s : Set (Set X)) (h : ∀ U V : Set X, U ∈ s → V ⊆ U → V ∈ s)
  (h' : ∀ x: X, ∃ U ∈ s, x ∈ U) :
    IsTopologicalBasis (t := generateFrom s) s := by
  let _ := generateFrom s
  apply isTopologicalBasis_of_open_of_nhds
  · intros u hu
    exact isOpen_generateFrom_of_mem hu
  · intros x U hx hU
    induction hU with
    | basic V hV => use V, hV, hx
    | univ => simpa using h' x
    | inter V W _ _ h₃ h₄ =>
        rcases h₃ hx.1 with ⟨R, _, hxR, hRV⟩
        rcases h₄ hx.2 with ⟨S, S_in, hxS, hSW⟩
        refine ⟨R ∩ S, ?_, ⟨hxR, hxS⟩, ?_⟩
        · exact h _ _ S_in (Set.inter_subset_right R S)
        · exact Set.inter_subset_inter hRV hSW
    | sUnion S _ hS =>
        rcases hx with ⟨T, T_in, hxT⟩
        rcases hS T T_in hxT with ⟨V, V_in, hxV, hVT⟩
        use V, V_in, hxV
        exact Set.subset_sUnion_of_subset S T hVT T_in

namespace ContinuousMap

section CompactOpen

instance pathSpace : TopologicalSpace C(I, X) := 
  TopologicalSpace.generateFrom
    { m | ∃ (s : Set I) (_ : IsCompact s) (u : Set X) (_ : IsOpen u), m = CompactOpen.gen s u}

-- 
-- 

#exit
instance topologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ → C(I, X)) ContinuousMap.compactOpen

example [TopologicalSpace.Compact]