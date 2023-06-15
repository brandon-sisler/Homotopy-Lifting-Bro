-- import Mathlib
import Mathlib.Topology.Constructions
import Mathlib.Topology.Covering
import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.SubsetProperties
import Mathlib.Data.Set.Prod
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

--CompactIccSpace
open Function
open unitInterval 
open Topology
open Set

--instance : Nontrivial I := ⟨0, 1, sorry⟩
instance : NoMaxOrder ↑I := by sorry
instance : NoMinOrder ↑I := by sorry

theorem existence_of_homotopy_lifting
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
  (∃ (U: Set Y) (ab: I × I), (IsOpen U ∧ y ∈ U)  ∧  ab.1 < t ∧ t < ab.2 )) := by
    --unfold IsCoveringMap at hp
    intro y t
    let x := F t y
    specialize hp x
    have ⟨hp1, hp2, hp3⟩ := hp
    let V : Set X := hp2.baseSet
    have U_is_open := (CF.isOpen_preimage V) hp2.open_baseSet
    rw [isOpen_prod_iff] at U_is_open
    have ty_in_U : ((t,y) ∈ (uncurry F) ⁻¹' V) := by 
      unfold Set.preimage
      simp
      exact hp3
    specialize U_is_open t y ty_in_U
    have ⟨A,B,A_is_open,B_is_open,t_in_A,y_in_B,hU⟩ := U_is_open
    have ab := IsOpen.mem_nhds A_is_open t_in_A
    rw [mem_nhds_iff_exists_Ioo_subset] at ab
    have ⟨a,b,t_in_ab,ab_in_A⟩ := ab
    clear ab
    clear ab
    use B
    use (a,b)
    constructor
    exact ⟨B_is_open, y_in_B⟩
    simp
    unfold Set.Ioo at t_in_ab
    simp at t_in_ab
    exact t_in_ab
  choose! U ab hU hab using q
  have q : (∀ y: Y, true) := by
    intro y
    let box : (Y → I → Set (Y × I)) := fun y t => Set.prod (U y t) (Set.Ioo (ab y t).1 (ab y t).2)
    let opencover := ⋃ (t: I), box y t
    have hcover: Set.prod {y} (Set.Icc (0:I) (1:I)) ⊆ opencover := by
      intro ⟨k1,k2⟩
      intro h
      unfold Set.prod at h
      simp at h
      have ⟨h1,h2,h3⟩ := h
      clear h
      rw [Set.mem_iUnion]
      use k2
      simp
      constructor
      rw [h1]
      exact (hU y k2).2
      exact (hab y k2)
    have hopen : ∀ (t: I), IsOpen (box y t) := by
      intro t
      simp
      rw [isOpen_prod_iff]
      intro a b
      intro h
      unfold Set.prod at h
      simp at h
      use U y t
      use (Ioo (ab y t).fst (ab y t).snd)
      constructor
      exact (hU y t).1
      constructor
      exact isOpen_Ioo
      constructor
      exact h.1
      constructor
      unfold Ioo
      simp
      exact ⟨h.2.1, h.2.2⟩
      intro qq hq
      unfold Set.prod
      simp
      constructor
      exact hq.1
      exact hq.2
    have I_is_compact : IsCompact (prod {y} (univ : Set I)) := by
      exact isCompact_singleton.prod isCompact_univ
    have := box y
    have := IsCompact.elim_finite_subcover I_is_compact (box y) hopen hcover
    

    sorry
  sorry

  theorem test (Y X Xt : Type _)
  [instY: TopologicalSpace Y] [instX: TopologicalSpace X] [instXt: TopologicalSpace Xt]
  (p: Xt → X)
  -- (Cp: Continuous p)
  (hp: IsCoveringMap p)
  (F: I → Y → X)
  (CF : Continuous (uncurry F)) -- uncurry F: ℝ × Y → X  
  (F0t: Y → Xt)
  (CF0t: Continuous F0t) 
  (hF0tp : F 0 = p ∘ F0t) : 
  ∀ y : Y, ∃ U ∈ 𝓝 y, ∃ Ft : I → Y → Xt, ContinuousOn (uncurry Ft) (univ ×ˢ U) 
  ∧ EqOn (Ft 0) F0t U 
  ∧ EqOn (uncurry F) (p ∘ uncurry Ft) (univ ×ˢ U) := by sorry 
  
  /-theorem 
  IsCompact.elim_finite_subcover {α : Type u} [topological_space α]{s : set α} {ι : Type v} 
   (hs : is_compact s) 
   (U : ι → set α) 
   (hUo : ∀ (i : ι), is_open (U i)) 
   (hsU : s ⊆ ⋃ (i : ι), U i) :   ------------DONE

   ∃ (t : finset ι), s ⊆ ⋃ (i : ι) (H : i ∈ t), U i
   -/
