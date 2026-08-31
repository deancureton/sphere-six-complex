module

public import SphereSixComplex.Topology.StableFramingSpecialOrthogonalPolar
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.CompactOpen

/-!
# From cube homotopy groups to sphere representatives

Mathlib defines higher homotopy groups using maps from a cube which are constant on its boundary.
The clutching argument in this project instead uses ordinary, unbased maps out of a concrete
sphere.  This file isolates the precise geometric datum connecting those presentations: a
quotient map from the cube which collapses exactly its boundary.

For topological-group targets, no connectedness assumption is needed to pass from based to
unbased maps.  Translation by the inverse of the value at the collapsed point normalizes any
sphere map.  A relative-boundary cube nullhomotopy then descends along the quotient map, and
translation restores the original map.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open Topology.Homotopy
open scoped MatrixGroups Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

universe u v

/-- Inversion on `SO(7)` is matrix transposition, hence is continuous. -/
public instance stableSpecialOrthogonalSevenContinuousInv :
    ContinuousInv StableSpecialOrthogonalSeven where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    rw [show (Subtype.val ∘ fun Q : StableSpecialOrthogonalSeven ↦ Q⁻¹) =
        fun Q : StableSpecialOrthogonalSeven ↦ Q.1ᵀ by
      funext Q
      rfl]
    exact Continuous.matrix_transpose continuous_subtype_val

/-- The matrix model of `SO(7)` is a topological group. -/
public instance stableSpecialOrthogonalSevenIsTopologicalGroup :
    IsTopologicalGroup StableSpecialOrthogonalSeven :=
  IsTopologicalGroup.mk

/-- By the quotient definition, `π_N(X,x)` is a singleton exactly when every generalized
cube loop is homotopic relative to the boundary to the constant loop. -/
public theorem subsingleton_homotopyGroup_iff_all_genLoop_homotopic_const
    {N : Type u} {X : Type v} [TopologicalSpace X] (x : X) :
    Subsingleton (HomotopyGroup N X x) ↔
      ∀ p : Ω^ N X x, GenLoop.Homotopic p GenLoop.const := by
  constructor
  · intro h p
    exact show p ≈ (GenLoop.const : Ω^ N X x) from
      Quotient.exact (h.elim (⟦p⟧ : HomotopyGroup N X x)
        ⟦(GenLoop.const : Ω^ N X x)⟧)
  · intro h
    constructor
    intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    apply Quotient.sound
    exact (h p).trans (h q).symm

/-- A sphere-like space presented as a cube with its whole boundary collapsed to one point.

The `fiber` field records that the quotient identifies exactly the boundary points.  Together
with `isQuotientMap`, this is the effective point-set input needed to descend homotopies relative
to the cube boundary. -/
public structure CubeBoundaryCollapseModel
    (N : Type u) (S : Type v) [TopologicalSpace S] (base : S) where
  quotient : C(I^N, S)
  boundary : ∀ y : I^N, y ∈ Cube.boundary N → quotient y = base
  fiber : ∀ a b : I^N, quotient a = quotient b →
    a = b ∨ (a ∈ Cube.boundary N ∧ b ∈ Cube.boundary N)
  isQuotientMap : IsQuotientMap quotient

namespace CubeBoundaryCollapseModel

variable {N : Type u} {S : Type v} [TopologicalSpace S] {base : S}

/-- A chosen cube representative.  Continuity is not required: descended-map continuity comes
from the quotient-map property. -/
private noncomputable def chooseRep
    (Q : CubeBoundaryCollapseModel N S base) (s : S) : I^N :=
  Classical.choose (Q.isQuotientMap.surjective s)

private theorem quotient_chooseRep
    (Q : CubeBoundaryCollapseModel N S base) (s : S) :
    Q.quotient (Q.chooseRep s) = s :=
  Classical.choose_spec (Q.isQuotientMap.surjective s)

/-- Normalize an unbased group-valued map at the collapsed point. -/
public def normalizeAt
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (_Q : CubeBoundaryCollapseModel N S base) (f : C(S, G)) : C(S, G) where
  toFun s := (f base)⁻¹ * f s
  continuous_toFun := continuous_const.mul f.continuous

@[simp] public theorem normalizeAt_base
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : CubeBoundaryCollapseModel N S base) (f : C(S, G)) :
    Q.normalizeAt f base = 1 := by
  simp [normalizeAt]

/-- Pull the normalized sphere map back along the quotient cube. -/
public def normalizedGenLoop
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : CubeBoundaryCollapseModel N S base) (f : C(S, G)) : Ω^ N G (1 : G) :=
  ⟨(Q.normalizeAt f).comp Q.quotient, by
    intro y hy
    simp only [ContinuousMap.comp_apply]
    rw [Q.boundary y hy]
    exact Q.normalizeAt_base f⟩

@[simp] public theorem normalizedGenLoop_apply
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : CubeBoundaryCollapseModel N S base) (f : C(S, G)) (y : I^N) :
    Q.normalizedGenLoop f y = (f base)⁻¹ * f (Q.quotient y) :=
  rfl

/-- A relative-boundary nullhomotopy of the normalized cube representative descends to an
ordinary nullhomotopy of the original unbased sphere map. -/
public theorem nullhomotopic_of_normalizedGenLoop_homotopic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : CubeBoundaryCollapseModel N S base) (f : C(S, G))
    (h : GenLoop.Homotopic (Q.normalizedGenLoop f) GenLoop.const) :
    f.Nullhomotopic := by
  let p : Ω^ N G (1 : G) := Q.normalizedGenLoop f
  obtain ⟨H⟩ := h
  have H_fiber (t : unitInterval) (a b : I^N)
      (hab : Q.quotient a = Q.quotient b) : H (t, a) = H (t, b) := by
    rcases Q.fiber a b hab with rfl | ⟨ha, hb⟩
    · rfl
    · calc
        H (t, a) = p a := H.eq_fst t ha
        _ = 1 := p.property a ha
        _ = p b := (p.property b hb).symm
        _ = H (t, b) := (H.eq_fst t hb).symm
  let Kfun : unitInterval × S → G := fun z ↦ H (z.1, Q.chooseRep z.2)
  have K_comp (t : unitInterval) (a : I^N) :
      Kfun (t, Q.quotient a) = H (t, a) := by
    apply H_fiber
    exact Q.quotient_chooseRep (Q.quotient a)
  have hK : Continuous Kfun := by
    apply Q.isQuotientMap.continuous_lift_prod_right
    exact H.continuous.congr (fun z ↦ (K_comp z.1 z.2).symm)
  let normalizedHomotopy :
      (Q.normalizeAt f).Homotopy (ContinuousMap.const S 1) := {
    toFun := Kfun
    continuous_toFun := hK
    map_zero_left s := by
      let a := Q.chooseRep s
      calc
        Kfun (0, s) = H (0, a) := rfl
        _ = p a := H.apply_zero a
        _ = Q.normalizeAt f (Q.quotient a) := rfl
        _ = Q.normalizeAt f s := by rw [Q.quotient_chooseRep]
    map_one_left s := by
      let a := Q.chooseRep s
      calc
        Kfun (1, s) = H (1, a) := rfl
        _ = (GenLoop.const : Ω^ N G (1 : G)) a := H.apply_one a
        _ = 1 := rfl
        _ = ContinuousMap.const S 1 s := rfl }
  let restore : C(G, G) := {
    toFun := fun g ↦ f base * g
    continuous_toFun := continuous_const.mul continuous_id }
  have hnormalized : (Q.normalizeAt f).Nullhomotopic :=
    ⟨1, ⟨normalizedHomotopy⟩⟩
  have hrestored := hnormalized.comp_right restore
  have heq : restore.comp (Q.normalizeAt f) = f := by
    ext s
    simp [restore, normalizeAt]
  simpa only [heq] using hrestored

/-- Triviality of the cube-based homotopy group implies representative-level nullhomotopy for
all maps out of a supplied boundary-collapse model. -/
public theorem all_maps_nullhomotopic_of_subsingleton_homotopyGroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (Q : CubeBoundaryCollapseModel N S base)
    [Subsingleton (HomotopyGroup N G (1 : G))]
    (f : C(S, G)) : f.Nullhomotopic := by
  let p : Ω^ N G (1 : G) := Q.normalizedGenLoop f
  have hconst :
      (⟦p⟧ : HomotopyGroup N G (1 : G)) =
        ⟦(GenLoop.const : Ω^ N G (1 : G))⟧ :=
    (inferInstance : Subsingleton (HomotopyGroup N G (1 : G))).elim _ _
  have hp : GenLoop.Homotopic p GenLoop.const := Quotient.exact hconst
  exact Q.nullhomotopic_of_normalizedGenLoop_homotopic f hp

end CubeBoundaryCollapseModel

/-- The missing geometric input for applying Mathlib's cube-based `π₅` to the clutching
five-sphere. -/
public abbrev StableFiveSphereCubeBoundaryCollapseModel :=
  CubeBoundaryCollapseModel (Fin 5) StableClutchingEquatorFiveSphere

/-- Given a cube-boundary presentation of the clutching sphere, cube-based `π₅(SO(7)) = 0`
implies exactly the representative-level proposition required by the clutching pipeline. -/
public theorem specialOrthogonalSevenFiveSphereNullhomotopyVanishing_of_piFive
    (base : StableClutchingEquatorFiveSphere)
    (Q : StableFiveSphereCubeBoundaryCollapseModel base)
    [Subsingleton (HomotopyGroup.Pi 5 StableSpecialOrthogonalSeven
      (1 : StableSpecialOrthogonalSeven))] :
    SpecialOrthogonalSevenFiveSphereNullhomotopyVanishing := by
  intro f
  exact Q.all_maps_nullhomotopic_of_subsingleton_homotopyGroup f

end SphereSixComplex
