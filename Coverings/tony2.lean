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
  (F: ℝ → Y → X)
  (CF : Continuous (uncurry F)) -- uncurry F: ℝ × Y → X  
  (F0t: Y → Xt)
  (CF0t: Continuous F0t) 
  (hF0tp : F 0 = p ∘ F0t) : 
  ∃ Ft : ℝ → Y → Xt, Continuous (uncurry Ft) ∧ ∀ t, p ∘ (Ft t) = F t ∧
  Ft 0 = F0t := by
  have q : (∀ y: Y, ∀ t ∈ I, 
  (∃ U : Set Y, ∃ a, ∃ b, (IsOpen U ∧ y ∈ U)  ∧  a < t ∧ t < b)) := by
    --unfold IsCoveringMap at hp
    intro y t t_in
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
    rcases ab with ⟨a,b,t_in_ab,ab_in_A⟩
    use B, a, b
    constructor
    exact ⟨B_is_open, y_in_B⟩
    simp
    unfold Set.Ioo at t_in_ab
    simp at t_in_ab
    exact t_in_ab
  choose! U a b hU ha hb using q
  have q : (∀ y: Y, true) := by
    intro y
    let box : (Y → ℝ → Set (Y × ℝ)) := fun y t => Set.prod (U y t) (Set.Ioo (a y t) (b y t))
    let opencover := ⋃ (t ∈ I), box y t
    have hcover: Set.prod {y} (Set.Icc (0:ℝ) 1) ⊆ opencover := by
      rintro ⟨k1 ,t⟩ ⟨hk1, ht : t ∈ _⟩
      rw [(mem_singleton_iff.mp hk1 : k1 = y)]; clear hk1 k1
      
      rw [Set.mem_iUnion₂]
      use t, ht
      constructor
      exact (hU y t ht).2
      exact ⟨ha y t ht, hb y t ht⟩
    have hopen : ∀ t, IsOpen (box y t) := by
      intro t
      simp
      rw [isOpen_prod_iff]
      intro y' t'
      intro h
      unfold Set.prod at h
      simp at h
      use U y t
      use (Ioo (a y t) (b y t))
      constructor
      -- exact (hU y t).1
      -- constructor
      -- exact isOpen_Ioo
      -- constructor
      -- exact h.1
      -- constructor
      -- unfold Ioo
      -- simp
      -- exact ⟨h.2.1, h.2.2⟩
      -- intro qq hq
      -- unfold Set.prod
      -- simp
      -- constructor
      -- exact hq.1
      -- exact hq.2
      sorry
    have I_is_compact : IsCompact (prod {y} (Icc (0:ℝ) 1)) := by
      exact isCompact_singleton.prod isCompact_Icc
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
