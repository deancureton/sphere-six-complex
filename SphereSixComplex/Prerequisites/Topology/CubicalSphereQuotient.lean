module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# The cubical sphere as a boundary quotient

This module forms the quotient of the unit `N`-cube by collapsing its boundary to one point. It
proves the universal factorization property needed to turn mathlib's cubical generalized loops
into based maps out of this quotient. No comparison with the Euclidean sphere is assumed here.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

/-- Two cube points are equivalent when they are equal or both lie on the boundary. -/
public def cubeBoundaryRel (N : Type*) (a b : I^N) : Prop :=
  a = b ∨ (a ∈ Cube.boundary N ∧ b ∈ Cube.boundary N)

theorem cubeBoundaryRel_equivalence (N : Type*) :
    Equivalence (cubeBoundaryRel N) := by
  constructor
  · exact fun a ↦ Or.inl rfl
  · intro a b hab
    exact hab.elim (Or.inl ∘ Eq.symm) fun h ↦ Or.inr ⟨h.2, h.1⟩
  · intro a b c hab hbc
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr ⟨hab.1, hbc.2⟩

/-- The setoid that collapses the boundary of the unit cube. -/
public def cubeBoundarySetoid (N : Type*) : Setoid (I^N) where
  r := cubeBoundaryRel N
  iseqv := cubeBoundaryRel_equivalence N

/-- The cubical `N`-sphere, defined as the unit `N`-cube modulo its boundary. -/
public abbrev CubicalSphere (N : Type*) := Quotient (cubeBoundarySetoid N)

/-- The quotient projection from the cube to the cubical sphere. -/
public def cubicalSphereMk (N : Type*) : C(I^N, CubicalSphere N) where
  toFun := @Quotient.mk' _ (cubeBoundarySetoid N)
  continuous_toFun := continuous_quotient_mk'

@[simp]
public theorem cubicalSphereMk_apply (N : Type*) (a : I^N) :
    cubicalSphereMk N a = @Quotient.mk' _ (cubeBoundarySetoid N) a :=
  rfl

public theorem cubicalSphereMk_eq_iff (N : Type*) (a b : I^N) :
    cubicalSphereMk N a = cubicalSphereMk N b ↔ cubeBoundaryRel N a b :=
  @Quotient.eq _ (cubeBoundarySetoid N) a b

/-- The distinguished point represented by the collapsed boundary. -/
public def cubicalSphereBasepoint (N : Type*) [Nonempty N] : CubicalSphere N :=
  cubicalSphereMk N (fun _ : N ↦ (0 : I))

public theorem cubicalSphereMk_eq_basepoint_of_mem_boundary
    {N : Type*} [Nonempty N] {a : I^N} (ha : a ∈ Cube.boundary N) :
    cubicalSphereMk N a = cubicalSphereBasepoint N := by
  apply Quotient.sound
  exact Or.inr ⟨ha, Classical.arbitrary N, Or.inl rfl⟩

/-- A generalized loop descends to the cube-boundary quotient. -/
public def genLoopToCubicalSphereMap
    {N X : Type*} [TopologicalSpace X] {x : X} (p : Ω^ N X x) :
    C(CubicalSphere N, X) where
  toFun := Quotient.lift p fun a b hab ↦ by
    rcases hab with rfl | hab
    · rfl
    · exact (p.property a hab.1).trans (p.property b hab.2).symm
  continuous_toFun := continuous_quot_lift (fun a b hab ↦ by
    rcases hab with rfl | hab
    · rfl
    · exact (p.property a hab.1).trans (p.property b hab.2).symm) p.1.continuous

@[simp]
public theorem genLoopToCubicalSphereMap_mk
    {N X : Type*} [TopologicalSpace X] {x : X} (p : Ω^ N X x) (a : I^N) :
    genLoopToCubicalSphereMap p (cubicalSphereMk N a) = p a :=
  rfl

@[simp]
public theorem genLoopToCubicalSphereMap_comp_mk
    {N X : Type*} [TopologicalSpace X] {x : X} (p : Ω^ N X x) :
    (genLoopToCubicalSphereMap p).comp (cubicalSphereMk N) = p.1 := by
  ext a
  rfl

@[simp]
public theorem genLoopToCubicalSphereMap_basepoint
    {N X : Type*} [Nonempty N] [TopologicalSpace X] {x : X} (p : Ω^ N X x) :
    genLoopToCubicalSphereMap p (cubicalSphereBasepoint N) = x := by
  exact p.property _ ⟨Classical.arbitrary N, Or.inl rfl⟩

/-- Continuous maps out of the cubical sphere are determined by their composites with the cube
quotient projection. -/
public theorem ContinuousMap.eq_of_comp_cubicalSphereMk_eq
    {N X : Type*} [TopologicalSpace X] {f g : C(CubicalSphere N, X)}
    (h : f.comp (cubicalSphereMk N) = g.comp (cubicalSphereMk N)) : f = g := by
  ext q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  have ha := DFunLike.congr_fun h a
  exact ha

/-- Based continuous maps out of the cubical sphere. -/
public def CubicalSphereBasedMap
    (N X : Type*) [Nonempty N] [TopologicalSpace X] (x : X) :=
  {f : C(CubicalSphere N, X) // f (cubicalSphereBasepoint N) = x}

/-- Generalized loops are exactly based continuous maps out of the cube-boundary quotient. -/
public def genLoopEquivCubicalSphereBasedMap
    (N X : Type*) [Nonempty N] [TopologicalSpace X] (x : X) :
    Ω^ N X x ≃ CubicalSphereBasedMap N X x where
  toFun p := ⟨genLoopToCubicalSphereMap p, genLoopToCubicalSphereMap_basepoint p⟩
  invFun f := ⟨f.1.comp (cubicalSphereMk N), fun a ha ↦ by
    rw [ContinuousMap.comp_apply, cubicalSphereMk_eq_basepoint_of_mem_boundary ha, f.2]⟩
  left_inv p := by
    ext a
    rfl
  right_inv f := by
    apply Subtype.ext
    apply ContinuousMap.eq_of_comp_cubicalSphereMk_eq
    ext a
    rfl

end SphereSixComplex
