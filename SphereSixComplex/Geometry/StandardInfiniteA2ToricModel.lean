module

public import SphereSixComplex.Geometry.CuspFilling
public import SphereSixComplex.ComplexStructure

/-!
# The standard infinite `A₂` toric model

This file gives the exact interface for the standard toric construction used in Lemmas 4.2 and
4.3(i)--(ii) of the paper.  It contains no phase corrections, quotient estimates, compactness
claims, or sphere-recognition input.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold
open Matrix
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- The rank-three lattice used by the cone fan. -/
public abbrev FanLattice := Fin 3 → ℤ

/-- The dense algebraic torus `(C×)³`. -/
public abbrev DenseTorus := Fin 3 → ℂˣ

/-- Embed a vertex of the `A₂` triangulation as a primitive height-one ray. -/
public def heightOneRay (v : ToricLattice) : FanLattice :=
  ![v 0, v 1, 1]

@[simp]
public theorem heightOneRay_last (v : ToricLattice) : heightOneRay v 2 = 1 :=
  rfl

/-- The three primitive ray generators of a maximal cone, as columns of an integral matrix. -/
public def a2ConeMatrix (upper : Bool) (v : ToricLattice) :
    Matrix (Fin 3) (Fin 3) ℤ :=
  fun i j ↦ heightOneRay (a2Triangle upper v j) i

/-- The integral fan shear on the dense torus.  The last coordinate is `t`; the first two are
multiplied by the corresponding integral powers of `t`. -/
public def denseTorusShear
    (lambda : ParameterLattice) (x : DenseTorus) : DenseTorus :=
  ![x 0 * x 2 ^ shearVector lambda 0,
    x 1 * x 2 ^ shearVector lambda 1,
    x 2]

@[simp]
public theorem denseTorusShear_last
    (lambda : ParameterLattice) (x : DenseTorus) :
    denseTorusShear lambda x 2 = x 2 :=
  rfl

/-- A bundled realization of the infinite height-one `A₂` fan as a complex toric
three-manifold.  Mathlib currently has no scheme-theoretic divisor/reducedness layer for this
construction, so the exact local squarefree normal form `t = z₀ z₁ z₂`, together with its
three coordinate-hyperplane components, is the topological/analytic substitute for
scheme-theoretic reducedness.  `cone_unimodular` belongs to the standard fan construction. -/
public structure Model where
  /-- The toric variety associated to the infinite fan. -/
  Carrier : Type
  /-- Its topology. -/
  topology : TopologicalSpace Carrier
  /-- Its complex atlas, modelled on complex dimension three. -/
  charts : ChartedSpace ComplexModel Carrier
  /-- The atlas makes the carrier a complex three-manifold. -/
  manifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) ∞ Carrier topology charts
  /-- The infinite toric variety is Hausdorff. -/
  t2 : @T2Space Carrier topology
  /-- The countable fan gives a second-countable topology. -/
  secondCountable : @SecondCountableTopology Carrier topology
  /-- All affine toric charts meet the dense torus, hence the variety is connected. -/
  connected : @ConnectedSpace Carrier topology
  /-- Every maximal cone of the explicit infinite `A₂` fan is unimodular. -/
  cone_unimodular : ∀ upper v, IsUnit (a2ConeMatrix upper v).det
  /-- The character associated to the height coordinate. -/
  t : Carrier → ℂ
  /-- The height character is holomorphic. -/
  t_holomorphic :
    letI := topology
    letI := charts
    ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ t
  /-- Inclusion of the torus orbit corresponding to the zero cone. -/
  torusEmbedding : DenseTorus → Carrier
  /-- The torus is embedded as an open subspace. -/
  torus_openEmbedding :
    letI := topology
    Topology.IsOpenEmbedding torusEmbedding
  /-- The open torus is dense. -/
  torus_dense :
    letI := topology
    DenseRange torusEmbedding
  /-- The dense torus is exactly the nonzero fibre of `t`. -/
  torus_range : Set.range torusEmbedding = {p | t p ≠ 0}
  /-- On the dense torus, `t` is its third character. -/
  t_torus : ∀ x, t (torusEmbedding x) = (x 2 : ℂ)
  /-- The holomorphic torus action on the toric variety. -/
  torusAction : DenseTorus →* Equiv.Perm Carrier
  /-- Every torus element acts biholomorphically. -/
  torusAction_holomorphic :
    letI := topology
    letI := charts
    ∀ g, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (torusAction g)
  /-- The algebraic torus action is jointly holomorphic, in the coefficientwise form needed on
  open subsets of the toric variety. -/
  variableTorusAction_holomorphic :
    letI := topology
    letI := charts
    ∀ (U : TopologicalSpace.Opens Carrier) (c : U → DenseTorus),
      (∀ i, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ℂ) ∞ (fun p : U ↦ (c p i : ℂ))) →
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞
        (fun p : U ↦ torusAction (c p) (p : Carrier))
  /-- The action restricts to multiplication on the dense torus. -/
  torusAction_torus : ∀ g x,
    torusAction g (torusEmbedding x) = torusEmbedding (g * x)
  /-- The height character transforms by the third torus coordinate. -/
  t_torusAction : ∀ g p, t (torusAction g p) = (g 2 : ℂ) * t p
  /-- The affine chart belonging to either triangle based at `v`. -/
  toricChart :
    letI := topology
    letI := charts
    Bool → ToricLattice →
      PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel)
        Carrier ComplexModel ∞
  /-- Each unimodular affine chart has all of `C³` as its target. -/
  toricChart_target :
    letI := topology
    letI := charts
    ∀ upper v, (toricChart upper v).target = Set.univ
  /-- The maximal-cone charts cover the toric variety. -/
  toricChart_cover :
    letI := topology
    letI := charts
    ∀ p, ∃ upper v, p ∈ (toricChart upper v).source
  /-- In every unimodular chart the height character is the squarefree monomial
  `z₀ z₁ z₂`. -/
  toricChart_t :
    letI := topology
    letI := charts
    ∀ upper v p, p ∈ (toricChart upper v).source →
      t p = (toricChart upper v p) 0 *
        (toricChart upper v p) 1 * (toricChart upper v p) 2
  /-- Ray components of the central fibre, indexed by height-one rays. -/
  centralComponent : ToricLattice → Set Carrier
  /-- The central fibre is the union of all ray components. -/
  centralFiber_eq_iUnion : t ⁻¹' {0} = ⋃ v, centralComponent v
  /-- In a maximal chart, its three ray components are exactly the three coordinate
  hyperplanes. -/
  centralComponent_in_chart :
    letI := topology
    letI := charts
    ∀ upper v i p, p ∈ (toricChart upper v).source →
      (p ∈ centralComponent (a2Triangle upper v i) ↔
        (toricChart upper v p) i = 0)
  /-- No other ray component meets a maximal affine chart. -/
  otherCentralComponent_disjoint_chart :
    letI := topology
    letI := charts
    ∀ upper v w, w ∉ Set.range (a2Triangle upper v) →
      Disjoint (centralComponent w) (toricChart upper v).source
  /-- Integral translations of the `A₂` fan induce toric automorphisms. -/
  fanShear : ParameterLattice →+ Additive (Equiv.Perm Carrier)
  /-- Every induced fan automorphism is biholomorphic. -/
  fanShear_holomorphic :
    letI := topology
    letI := charts
    ∀ lambda, ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun p ↦ Additive.toMul (fanShear lambda) p)
  /-- Fan shears preserve the height character. -/
  fanShear_preserves_t : ∀ lambda p,
    t (Additive.toMul (fanShear lambda) p) = t p
  /-- On the dense torus, the induced automorphism is the integral monomial shear. -/
  fanShear_torus : ∀ lambda x,
    Additive.toMul (fanShear lambda) (torusEmbedding x) =
      torusEmbedding (denseTorusShear lambda x)
  /-- The fan automorphism carries a maximal-cone chart to the translated maximal-cone
  chart. -/
  fanShear_chart :
    letI := topology
    letI := charts
    ∀ lambda upper v p,
      p ∈ (toricChart upper v).source ↔
        Additive.toMul (fanShear lambda) p ∈
          (toricChart upper (v + shearVector lambda)).source
  /-- The fan automorphism translates height-one components by `B₀ lambda`. -/
  fanShear_component : ∀ lambda v,
    (fun p ↦ Additive.toMul (fanShear lambda) p) '' centralComponent v =
      centralComponent (v + shearVector lambda)

namespace Model

public instance (M : Model) : TopologicalSpace M.Carrier := M.topology
public instance (M : Model) : ChartedSpace ComplexModel M.Carrier := M.charts
public instance (M : Model) :
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ M.Carrier := M.manifold
public instance (M : Model) : T2Space M.Carrier := M.t2
public instance (M : Model) : SecondCountableTopology M.Carrier := M.secondCountable
public instance (M : Model) : ConnectedSpace M.Carrier := M.connected

end Model

namespace Established

/-- Standard toric geometry for the countable smooth fan obtained by coning the `A₂`
triangulation at height one.  This is precisely the external toric input of Lemma 4.2 and
Lemma 4.3(i)--(ii), with no paper-specific analytic or quotient assertions. -/
public axiom model : Nonempty Model

end Established

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
