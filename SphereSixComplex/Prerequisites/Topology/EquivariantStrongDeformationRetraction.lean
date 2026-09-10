module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section
noncomputable section
open Set
open scoped ContinuousMap
namespace SphereSixComplex

/-- An equivariant strong deformation retraction of `X` onto `A`. -/
public structure EquivariantStrongDeformationRetraction
    (G X : Type*) [Group G] [TopologicalSpace X] [MulAction G X] (A : Set X) where
  retract : C(X, X)
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id X) retract
  retract_mem : ∀ x, retract x ∈ A
  retract_fixed : ∀ x, x ∈ A → retract x = x
  homotopy_fixed : ∀ s x, x ∈ A → homotopy (s, x) = x
  retract_equivariant : ∀ (g : G) x, retract (g • x) = g • retract x
  homotopy_equivariant : ∀ (g : G) s x, homotopy (s, g • x) = g • homotopy (s, x)

namespace EquivariantStrongDeformationRetraction

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
  {A : Set X} (D : EquivariantStrongDeformationRetraction G X A)

/-- The orbit quotient of the ambient action. -/
public abbrev OrbitQuotient (_D : EquivariantStrongDeformationRetraction G X A) :=
  Quotient (MulAction.orbitRel G X)

/-- The image of the retract in the orbit quotient. -/
public def quotientCore : Set (D.OrbitQuotient) :=
  Quotient.mk (MulAction.orbitRel G X) '' A

/-- The equivariant retraction descended to the orbit quotient. -/
public def quotientRetract : C(D.OrbitQuotient, D.OrbitQuotient) := by
  letI := MulAction.orbitRel G X
  exact {
    toFun := Quotient.lift (fun x ↦ Quotient.mk' (D.retract x)) (by
      intro a b hab
      apply Quotient.sound
      change MulAction.orbitRel G X a b at hab
      change MulAction.orbitRel G X (D.retract a) (D.retract b)
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.retract_equivariant g b).symm)
    continuous_toFun := continuous_quot_lift _
      (continuous_quot_mk.comp D.retract.continuous) }

/-- The underlying map of the descended homotopy. -/
public def quotientHomotopyToFun : unitInterval × D.OrbitQuotient → D.OrbitQuotient := by
  letI := MulAction.orbitRel G X
  exact fun z ↦ Quotient.lift
    (fun x ↦ Quotient.mk' (D.homotopy (z.1, x))) (by
      intro a b hab
      apply Quotient.sound
      change MulAction.orbitRel G X a b at hab
      change MulAction.orbitRel G X (D.homotopy (z.1, a)) (D.homotopy (z.1, b))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
      obtain ⟨g, hg⟩ := hab
      refine ⟨g, ?_⟩
      rw [← hg]
      exact (D.homotopy_equivariant g z.1 b).symm) z.2

variable [ContinuousConstSMul G X]

public theorem quotientHomotopyToFun_continuous : Continuous D.quotientHomotopyToFun := by
  let q : X → D.OrbitQuotient := Quotient.mk (MulAction.orbitRel G X)
  have hq : IsOpenQuotientMap (Prod.map (id : unitInterval → unitInterval) q) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk (Γ := G) (T := X))
  apply hq.isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : unitInterval × X ↦
    Quotient.mk (MulAction.orbitRel G X) (D.homotopy (z.1, z.2)))
  exact continuous_quot_mk.comp D.homotopy.continuous

/-- The strong deformation homotopy descended to the orbit quotient. -/
public def quotientHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id D.OrbitQuotient) D.quotientRetract where
  toFun := D.quotientHomotopyToFun
  continuous_toFun := D.quotientHomotopyToFun_continuous
  map_zero_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (D.homotopy.map_zero_left x)
  map_one_left q := by
    induction q using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (D.homotopy.map_one_left x)

omit [ContinuousConstSMul G X] in
public theorem quotientRetract_mem (q : D.OrbitQuotient) :
    D.quotientRetract q ∈ D.quotientCore := by
  induction q using Quotient.inductionOn with
  | _ x => exact ⟨D.retract x, D.retract_mem x, rfl⟩

omit [ContinuousConstSMul G X] in
public theorem quotientRetract_fixed (q : D.OrbitQuotient) (hq : q ∈ D.quotientCore) :
    D.quotientRetract q = q := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact congrArg (Quotient.mk _) (D.retract_fixed x hx)

public theorem quotientHomotopy_fixed (s : unitInterval) (q : D.OrbitQuotient)
    (hq : q ∈ D.quotientCore) : D.quotientHomotopy (s, q) = q := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact congrArg (Quotient.mk _) (D.homotopy_fixed s x hx)

end EquivariantStrongDeformationRetraction

end SphereSixComplex
end
end
