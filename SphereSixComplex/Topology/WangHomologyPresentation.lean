module

public import SphereSixComplex.LatticeData
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Topology.Constructions

/-!
# Wang presentations for bundles over finite bouquets

This file separates the algebra of the Wang sequence from its one missing general-topology
input.  A finite connected graph is represented by a bouquet of finitely many oriented circles.
Given monodromy homeomorphisms of a fibre, `FiniteBouquetMappingTorus` is the literal quotient
obtained by gluing the two ends of one cylinder per circle.  The standard Wang exact sequence for
that quotient is isolated in `establishedFiniteBouquetMappingTorusWangSequence`.

The rest of the file is algebraic.  In particular, any four consecutive exact maps in a Wang
sequence give a short exact presentation of the middle group as an extension of monodromy
coinvariants by monodromy invariants.
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

/-- Mathlib currently has singular homology and exact-sequence algebra but no Wang theorem.
This is the standard integral Wang exact sequence for the explicit finite-bouquet mapping-torus
quotient above.  It is the sole general-topology boundary in this module.
Reference: the Wang sequence of a fibre bundle over a sphere [Wang49]; for a mapping torus it is
the Mayer-Vietoris sequence of the two-piece cover of the bundle over the circle, [Hat02,
Section 2.2].  The bouquet case is the same argument with one edge per index. -/
public axiom establishedFiniteBouquetMappingTorusWangSequence
    [DiscreteTopology ι]
    (φ : ι → F ≃ₜ F) (k : ℕ) :
    FiniteBouquetMappingTorusWangSequence φ k

/-- The general algebraic Wang presentation supplied by the established topological theorem. -/
public def finiteBouquetMappingTorusWangPresentation (φ : ι → F ≃ₜ F) (k : ℕ) :
    WangHomologyPresentation
      (ι → IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ))
      (ι → IntegralSingularHomology k F)
      (IntegralSingularHomology k F) :=
  let W := establishedFiniteBouquetMappingTorusWangSequence φ k
  { highDifference := finiteBouquetMonodromyDifference φ (k + 1)
    inclusion := integralSingularHomologyMap (k + 1)
      (finiteBouquetMappingTorusFiberInclusion φ)
    boundary := W.boundary
    lowDifference := finiteBouquetMonodromyDifference φ k
    exact_highDifference_inclusion := W.exact_highDifference_inclusion
    exact_inclusion_boundary := W.exact_inclusion_boundary
    exact_boundary_lowDifference := W.exact_boundary_lowDifference }

/-- The degree-one homology presentation, using the induced maps on `H₁` and `H₀`. -/
public abbrev finiteBouquetMappingTorusHOnePresentation (φ : ι → F ≃ₜ F) :=
  finiteBouquetMappingTorusWangPresentation φ 0

/-- The degree-two homology presentation, using the induced maps on `H₂` and `H₁`. -/
public abbrev finiteBouquetMappingTorusHTwoPresentation (φ : ι → F ≃ₜ F) :=
  finiteBouquetMappingTorusWangPresentation φ 1

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

/-- The circle Wang sequence, derived from the single general finite-bouquet theorem. -/
public def circleMappingTorusWangPresentation (φ : F ≃ₜ F) (k : ℕ) :
    WangHomologyPresentation
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) (CircleMappingTorus φ))
      (IntegralSingularHomology k F)
      (IntegralSingularHomology k F) := by
  let W := establishedFiniteBouquetMappingTorusWangSequence
    (fun _ : Unit ↦ φ) k
  let δ : IntegralSingularHomology (k + 1) (CircleMappingTorus φ) →+
      IntegralSingularHomology k F :=
    { toFun := fun x ↦ W.boundary x ()
      map_zero' := by simp
      map_add' := by simp }
  refine
    { highDifference := circleMonodromyDifference φ (k + 1)
      inclusion := integralSingularHomologyMap (k + 1)
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ φ))
      boundary := δ
      lowDifference := circleMonodromyDifference φ k
      exact_highDifference_inclusion := ?_
      exact_inclusion_boundary := ?_
      exact_boundary_lowDifference := ?_ }
  · intro y
    rw [W.exact_highDifference_inclusion y]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x (), by
        rw [← finiteBouquetMonodromyDifference_unit_apply φ (k + 1) x]
        exact hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨fun _ ↦ x, by
        rw [finiteBouquetMonodromyDifference_unit_apply]
        exact hx⟩
  · intro y
    rw [← W.exact_inclusion_boundary y]
    constructor
    · intro h
      funext i
      cases i
      exact h
    · intro h
      exact congrFun h ()
  · intro y
    rw [← finiteBouquetMonodromyDifference_unit_apply φ k (fun _ ↦ y),
      W.exact_boundary_lowDifference (fun _ ↦ y)]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, congrFun hx ()⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, funext fun i ↦ ?_⟩
      cases i
      exact hx

/-- The degree-one circle-bundle presentation from the induced `H₁` and `H₀` monodromies. -/
public abbrev circleMappingTorusHOnePresentation (φ : F ≃ₜ F) :=
  circleMappingTorusWangPresentation φ 0

/-- The degree-two circle-bundle presentation from the induced `H₂` and `H₁` monodromies. -/
public abbrev circleMappingTorusHTwoPresentation (φ : F ≃ₜ F) :=
  circleMappingTorusWangPresentation φ 1

end Circle

end SphereSixComplex
