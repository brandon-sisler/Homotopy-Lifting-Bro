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
--import Mathlib.Data.Finset.Sort

--set_option autoImplicit false

--CompactIccSpace
open Function
open unitInterval 
open Topology
open Set

--instance : Nontrivial I := ⟨0, 1, sorry⟩
instance : NoMaxOrder ↑I := by sorry
instance : NoMinOrder ↑I := by sorry


 -- SECTION 1
structure ConstructionData  [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Xt] (p: Xt → X)
    (F: I → Y → X) where
  U : Y → I → Set Y
  a : Y → I → I
  b : Y → I → I 
  qt : (y : Y) → (t : I) → Trivialization (p ⁻¹' {F t y}) p
  U_op : ∀ y: Y, ∀ t: I, IsOpen (U y t)
  in_U : ∀ y: Y, ∀ t: I, y ∈ U y t
  a_lt : ∀ y: Y, ∀ t: I, a y t < t
  lt_b : ∀ y: Y, ∀ t: I, t < b y t    
  sub_triv : ∀ y: Y, ∀ t: I, (Ioo (a y t) (b y t)) ×ˢ U y t ⊆ (uncurry F) ⁻¹' ((qt y t).baseSet)

lemma aux₁ 
  [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Xt]
  {p: Xt → X}
  -- (Cp: Continuous p)
  (hp: IsCoveringMap p)
  {F: I → Y → X}
  (CF : Continuous (uncurry F)) : 
    ∀ y: Y, ∀ t: I, 
    (∃ (U: Set Y) (ab: I × I) (qt : Trivialization (↑(p ⁻¹' {F t y})) p), 
    (IsOpen U ∧ y ∈ U)  ∧  (ab.1 < t ∧ t < ab.2) ∧ (Ioo ab.1 ab.2) ×ˢ U ⊆ (uncurry F) ⁻¹' (qt.baseSet)) := by
  unfold IsCoveringMap at hp
  intro y t
  let x := F t y
  specialize hp x
  have ⟨_, hp2, hp3⟩ := hp
  clear hp
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
  clear A_is_open t_in_A
  rw [mem_nhds_iff_exists_Ioo_subset] at ab
  have ⟨a,b,t_in_ab,ab_in_A⟩ := ab
  clear ab
  clear ab
  -- construction done
  use B
  use (a,b)
  use hp2
  constructor
  exact ⟨B_is_open, y_in_B⟩
  simp
  unfold Set.Ioo at t_in_ab
  simp at t_in_ab
  constructor
  exact t_in_ab
  rw [prod_subset_iff]
  intro x' hx' y' hy' 
  apply hU
  rw [mem_prod_eq]
  simp
  exact ⟨ab_in_A hx', hy'⟩

variable [TopologicalSpace Y] [TopologicalSpace X] [TopologicalSpace Xt]

noncomputable
def mkConstructionData 
  {p: Xt → X}
  -- (Cp: Continuous p)
  (hp: IsCoveringMap p)
  {F: I → Y → X}
  (CF : Continuous (uncurry F)) : ConstructionData p F where
    U := fun y t ↦ (aux₁ hp CF y t).choose
    a := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose.1
    b := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose.2
    qt := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose
    U_op := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose_spec.1.1
    in_U := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose_spec.1.2
    a_lt := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose_spec.2.1.1
    lt_b := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose_spec.2.1.2
    sub_triv := fun y t ↦ (aux₁ hp CF y t).choose_spec.choose_spec.choose_spec.2.2


 -- SECTION 2
def ConstructionData.box {p: Xt → X}
    {F: I → Y → X} (data : ConstructionData p F) := 
    fun y t => Set.prod (data.U y t) (Set.Ioo (data.a y t) (data.b y t))

def ConstructionData.box_cover {p: Xt → X}
    {F: I → Y → X} (data : ConstructionData p F) (y) := ⋃ (t: I), data.box y t

lemma ConstructionData.box_cover_covers {p: Xt → X} {F: I → Y → X} (data : ConstructionData p F) (y) : 
    Set.prod {y} (univ) ⊆ data.box_cover y := by
  unfold box_cover
  intro ⟨k1,k2⟩
  intro h
  unfold Set.prod at h
  simp at h
  rw [Set.mem_iUnion]
  use k2
  simp
  constructor
  simp
  rw [h]
  exact (data.in_U y k2)
  exact ⟨data.a_lt y k2, data.lt_b y k2⟩

lemma ConstructionData.box_cover_open {p: Xt → X} {F: I → Y → X} (data : ConstructionData p F) (y) : 
    ∀ (t: I), IsOpen (data.box y t) := by
  intro t
  simp
  rw [isOpen_prod_iff]
  intro a b
  intro h
  simp at h
  use data.U y t
  use (Ioo (data.a y t) (data.b y t))
  constructor
  exact (data.U_op y t)
  constructor
  exact isOpen_Ioo
  constructor
  exact h.1
  constructor
  unfold Ioo
  simp
  exact ⟨h.2.1, h.2.2⟩
  intro qq hq
  simp
  constructor
  exact hq.1
  exact hq.2

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
  Ft 0 = F0t := by sorry

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
    ∧ EqOn (uncurry F) (p ∘ uncurry Ft) (univ ×ˢ U) := by
  intro yq
  let data := mkConstructionData hp CF
  let opencover := data.box_cover yq
  have hcover: Set.prod {yq} (univ) ⊆ opencover  := by
    exact data.box_cover_covers yq 
  have hopen : ∀ (t: I), IsOpen (data.box yq t) := by
    exact data.box_cover_open yq
  have I_is_compact : IsCompact ({yq} ×ˢ (univ : Set I)) := by
    exact isCompact_singleton.prod isCompact_univ
  have JJ := I_is_compact.elim_finite_subcover (data.box yq) hopen hcover
  choose J hJ using JJ
  have N := ⋂ (i: I) (_ : i ∈ J), data.U yq i
  use N
  -- have q : ∀ y: Y, ∃ J: Finset I,  
  have Ft : I → Y → Xt := by
    intro t
    intro y
    --have J_is_nonempty : (∃ Ft : N × Set.Icc 0 (i:J)) ∅ := by sorry
    --have := finset.induction_on_min J 
    --have := finset.sort_to_finset J
    have triv := data.qt y t
    sorry
  sorry






  


-- Induction
def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)

#eval fib 10
#reduce fib 100
-- Automation
