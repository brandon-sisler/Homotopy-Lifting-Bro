-- import Mathlib
import Mathlib.Topology.Constructions
import Mathlib.Topology.Covering
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

--CompactIccSpace
open Function
open unitInterval 

theorem uniqueness_of_homotopy_lifting
  (Y X Xt : Type _)
  [instY: TopologicalSpace Y] [instX: TopologicalSpace X] [instXt: TopologicalSpace Xt]
  (p: Xt → X)
  -- (Cp: Continuous p)
  (hp: IsCoveringMap p)
  (F: I → Y → X)
  (CF : Continuous (uncurry F)) -- uncurry F: ℝ × Y → X  
  (F0t: Y → Xt)
  (CF0t: Continuous F0t) 
  (hF0tp : F 0 = p ∘ F0t) : 
  ∃ Ft : I → Y → Xt, Continuous (uncurry Ft) ∧ ∀ t, p ∘ (Ft t) = F t ∧
  Ft 0 = F0t := by
  have q : (∀ y: Y, ∀ t: I, 
  (∃ U: Set Y, (instY.IsOpen U ∧ y ∈ U) ) ∧ (∃ ab: I × I, ab.1 < t ∧ t < ab.2 )) := by
    --unfold IsCoveringMap at hp
    intro y t
    let x := F t y
    specialize hp x
    have ⟨hp1, hp2, hp3⟩ := hp
    let V : Set X := hp2.baseSet
    have U_is_open := (CF.isOpen_preimage V) hp2.open_baseSet
    have ty_in_U : ((t,y) ∈ (uncurry F) ⁻¹' V) := by 
      unfold Set.preimage
      simp
      exact hp3
    --mem_nhds_prod_iff
    sorry
  have qU : (I → Y → Set Y) := by
    intro t y
    have A := (q y t).1
    sorry
  have qab : (I → Y → (I × I)) := by
    intro t y
    have A := (q y t).2
    sorry
  sorry
  /-theorem 
  is_compact.elim_finite_subcover {α : Type u} [topological_space α]{s : set α} {ι : Type v} 
   (hs : is_compact s) 
   (U : ι → set α) 
   (hUo : ∀ (i : ι), is_open (U i)) 
   (hsU : s ⊆ ⋃ (i : ι), U i) :
   ∃ (t : finset ι), s ⊆ ⋃ (i : ι) (H : i ∈ t), U i
   -/
