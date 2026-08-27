module

public import SphereSixComplex.LatticeData
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Constructions

/-!
# Wang presentations for bundles over finite bouquets: definitions

This file carries the source-independent part of `WangHomologyPresentation`: the algebra of four
consecutive maps in a Wang long exact sequence, the explicit finite-bouquet mapping torus, its
monodromy differences, and the structure `FiniteBouquetMappingTorusWangSequence` recording the
exactness data of its Wang sequence.

Only definitions and their immediate algebraic consequences live here.  The Wang sequence itself
is constructed from the Mayer--Vietoris sequence of an explicit open cover in
`WangHomologyPresentationProof`, and the presentations built from it are assembled in
`WangHomologyPresentation`, which re-exports this file so every module path is unchanged.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

universe u v w

/-- Four consecutive maps in a Wang long exact sequence. -/
public structure WangHomologyPresentation
    (HighRelations High Total LowRelations Low : Type*)
    [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
    [AddCommGroup LowRelations] [AddCommGroup Low] where
  highDifference : HighRelations →+ High
  inclusion : High →+ Total
  boundary : Total →+ LowRelations
  lowDifference : LowRelations →+ Low
  exact_highDifference_inclusion : Function.Exact highDifference inclusion
  exact_inclusion_boundary : Function.Exact inclusion boundary
  exact_boundary_lowDifference : Function.Exact boundary lowDifference

namespace WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]
  (P : WangHomologyPresentation HighRelations High Total LowRelations Low)

public theorem inclusion_highDifference (x : HighRelations) :
    P.inclusion (P.highDifference x) = 0 :=
  P.exact_highDifference_inclusion.apply_apply_eq_zero x

public theorem boundary_inclusion (x : High) : P.boundary (P.inclusion x) = 0 :=
  P.exact_inclusion_boundary.apply_apply_eq_zero x

public theorem lowDifference_boundary (x : Total) :
    P.lowDifference (P.boundary x) = 0 :=
  P.exact_boundary_lowDifference.apply_apply_eq_zero x

/-- The monodromy coinvariants in the upper degree. -/
public abbrev Coinvariants :=
  High ⧸ LinearMap.range P.highDifference.toIntLinearMap

/-- The monodromy invariants in the lower degree. -/
public abbrev Invariants :=
  LinearMap.ker P.lowDifference.toIntLinearMap

/-- The map from upper-degree coinvariants into the total-space homology group. -/
public def coinvariantsToTotal : P.Coinvariants →ₗ[ℤ] Total :=
  (LinearMap.range P.highDifference.toIntLinearMap).liftQ
    P.inclusion.toIntLinearMap fun x hx ↦ by
      obtain ⟨y, rfl⟩ := hx
      exact P.inclusion_highDifference y

/-- The boundary map, with codomain restricted to the lower-degree invariants. -/
public def totalToInvariants : Total →ₗ[ℤ] P.Invariants :=
  { toFun := fun x ↦ ⟨P.boundary x, P.lowDifference_boundary x⟩
    map_add' := fun x y ↦ by
      apply Subtype.ext
      exact P.boundary.map_add x y
    map_smul' := fun n x ↦ by
      apply Subtype.ext
      exact P.boundary.map_zsmul n x }

public theorem coinvariantsToTotal_injective :
    Function.Injective P.coinvariantsToTotal := by
  apply LinearMap.injective_range_liftQ_of_exact
  exact P.exact_highDifference_inclusion

public theorem totalToInvariants_surjective :
    Function.Surjective P.totalToInvariants := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := (P.exact_boundary_lowDifference y).mp hy
  refine ⟨x, Subtype.ext ?_⟩
  exact hx

public theorem exact_coinvariantsToTotal_totalToInvariants :
    Function.Exact P.coinvariantsToTotal P.totalToInvariants := by
  intro x
  constructor
  · intro hx
    have hx' : P.boundary x = 0 := by
      have h := congrArg Subtype.val hx
      exact h
    obtain ⟨y, hy⟩ := (P.exact_inclusion_boundary x).mp hx'
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    rw [coinvariantsToTotal, Submodule.liftQ_apply]
    exact hy
  · rintro ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply Subtype.ext
    rw [coinvariantsToTotal, Submodule.liftQ_apply]
    exact P.boundary_inclusion z

/-- The canonical short exact sequence extracted from four consecutive Wang maps. -/
public theorem shortExact_coinvariants_total_invariants :
    Function.Injective P.coinvariantsToTotal ∧
      Function.Exact P.coinvariantsToTotal P.totalToInvariants ∧
      Function.Surjective P.totalToInvariants :=
  ⟨P.coinvariantsToTotal_injective,
    P.exact_coinvariantsToTotal_totalToInvariants,
    P.totalToInvariants_surjective⟩

end WangHomologyPresentation

section FiniteBouquet

variable {ι F : Type}
  [Fintype ι] [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace F]

/-- Generating identifications for the bundle over a bouquet of circles.  All zero ends are
identified fibrewise, while the one end of edge `i` is attached to the common zero end using
the monodromy `φ i`. -/
public def finiteBouquetMappingTorusRelation (φ : ι → F ≃ₜ F)
    (p q : ι × unitInterval × F) : Prop :=
  (p.1 = q.1 ∧ p.2 = q.2) ∨
    (p.2.1 = 0 ∧ q.2.1 = 0 ∧ p.2.2 = q.2.2) ∨
    (p.2.1 = 1 ∧ q.2.1 = 0 ∧ q.2.2 = φ p.1 p.2.2)

/-- The equivalence relation generated by the endpoint attachments. -/
public def finiteBouquetMappingTorusSetoid (φ : ι → F ≃ₜ F) :
    Setoid (ι × unitInterval × F) :=
  Relation.EqvGen.setoid (finiteBouquetMappingTorusRelation φ)

/-- The total space of the bundle over a finite bouquet with the specified monodromies. -/
public def FiniteBouquetMappingTorus (φ : ι → F ≃ₜ F) :=
  Quotient (finiteBouquetMappingTorusSetoid φ)

public instance finiteBouquetMappingTorusTopologicalSpace (φ : ι → F ≃ₜ F) :
    TopologicalSpace (FiniteBouquetMappingTorus φ) :=
  inferInstanceAs (TopologicalSpace (Quotient (finiteBouquetMappingTorusSetoid φ)))

/-- Inclusion of the fibre over the bouquet vertex. -/
public def finiteBouquetMappingTorusFiberInclusion (φ : ι → F ≃ₜ F) :
    C(F, FiniteBouquetMappingTorus φ) :=
  ⟨fun x ↦ Quotient.mk (finiteBouquetMappingTorusSetoid φ) (default, (0, x)),
    continuous_quot_mk.comp
      (continuous_const.prodMk (continuous_const.prodMk continuous_id))⟩

/-- The cellular local-coefficient differential for a finite bouquet: the sum of
`(φᵢ)_* - 1` over its oriented loops. -/
public def finiteBouquetMonodromyDifference (φ : ι → F ≃ₜ F) (k : ℕ) :
    (ι → IntegralSingularHomology k F) →+ IntegralSingularHomology k F where
  toFun x := ∑ i, (integralSingularHomologyMap k (φ i) (x i) - x i)
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, map_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel

/-- Sum the edge-indexed copies of an additive group into the vertex copy. -/
public def finiteBouquetSum (G : Type w) [AddCommGroup G] : (ι → G) →+ G where
  toFun x := ∑ i, x i
  map_zero' := by simp
  map_add' x y := Finset.sum_add_distrib

/-- The exact data in the Wang sequence for the explicit finite-bouquet mapping torus. -/
public structure FiniteBouquetMappingTorusWangSequence (φ : ι → F ≃ₜ F) (k : ℕ) where
  boundary : IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ) →+
    (ι → IntegralSingularHomology k F)
  exact_highDifference_inclusion : Function.Exact
    (finiteBouquetMonodromyDifference φ (k + 1))
    (integralSingularHomologyMap (k + 1)
      (finiteBouquetMappingTorusFiberInclusion φ))
  exact_inclusion_boundary : Function.Exact
    (integralSingularHomologyMap (k + 1)
      (finiteBouquetMappingTorusFiberInclusion φ))
    boundary
  exact_boundary_lowDifference : Function.Exact boundary
    (finiteBouquetMonodromyDifference φ k)

end FiniteBouquet

section Circle

variable {F : Type} [TopologicalSpace F]

/-- The one-loop instance of the finite-bouquet mapping torus. -/
public abbrev CircleMappingTorus (φ : F ≃ₜ F) :=
  FiniteBouquetMappingTorus (fun _ : Unit ↦ φ)

/-- The usual circle Wang differential `(φ_*) - 1`. -/
public def circleMonodromyDifference (φ : F ≃ₜ F) (k : ℕ) :
    IntegralSingularHomology k F →+ IntegralSingularHomology k F :=
  integralSingularHomologyMap k φ - AddMonoidHom.id _

public theorem finiteBouquetMonodromyDifference_unit_apply
    (φ : F ≃ₜ F) (k : ℕ) (x : Unit → IntegralSingularHomology k F) :
    finiteBouquetMonodromyDifference (fun _ : Unit ↦ φ) k x =
      circleMonodromyDifference φ k (x ()) := by
  simp [finiteBouquetMonodromyDifference, circleMonodromyDifference]

end Circle

end SphereSixComplex
