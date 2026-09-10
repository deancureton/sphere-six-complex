module

public import SphereSixComplex.Paper.Geometry.StandardA2ModelEquivalence
public import SphereSixComplex.Paper.Topology.PaperCuspCentralFiberCWConstruction
public import Mathlib.Topology.Homeomorph.Quotient

@[expose] public section
noncomputable section
open Set

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M₁ M₂ : Model}

public def centralModelMap (W₁ : ActualPuncturedCuspCollarWitness N M₁)
    (W₂ : ActualPuncturedCuspCollarWitness N M₂)
    (p : actualLocalCuspCentralSubMulAction W₁) : actualLocalCuspCentralSubMulAction W₂ :=
  ⟨⟨Model.transport M₁ M₂ p.1.1, by
    change M₂.t (Model.transport M₁ M₂ p.1.1) ∈ Metric.ball 0 W₂.localWitness.radius
    have hp : M₁.t p.1.1 = 0 := p.2
    simpa only [Model.transport_t, hp, Metric.mem_ball, dist_self] using
      W₂.localWitness.radius_pos⟩, by
    change M₂.t (Model.transport M₁ M₂ p.1.1) = 0
    exact (Model.transport_t M₁ M₂ p.1.1).trans p.2⟩

public def centralModelHomeomorph (W₁ : ActualPuncturedCuspCollarWitness N M₁)
    (W₂ : ActualPuncturedCuspCollarWitness N M₂) :
    (actualLocalCuspCentralSubMulAction W₁) ≃ₜ (actualLocalCuspCentralSubMulAction W₂) where
  toFun := centralModelMap W₁ W₂
  invFun := centralModelMap W₂ W₁
  left_inv := fun p ↦ Subtype.ext (Subtype.ext (Model.transport_left_inverse M₁ M₂ p.1.1))
  right_inv := fun p ↦ Subtype.ext (Subtype.ext (Model.transport_left_inverse M₂ M₁ p.1.1))
  continuous_toFun := (((Model.transport_continuous M₁ M₂).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  continuous_invFun := (((Model.transport_continuous M₂ M₁).comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _).subtype_mk _

public theorem central_smul_coe (W : ActualPuncturedCuspCollarWitness N M₁) :
    letI := actualLocalCuspQuotientAction W
    ∀ (g : Multiplicative ParameterLattice) (p : actualLocalCuspCentralSubMulAction W),
      (g • p).1.1 = CuspToricPhaseAction.ToricModel.phaseAction M₁
        (N.phaseCoefficient (Multiplicative.toAdd g) 0)
        (Additive.toMul (M₁.fanShear (Multiplicative.toAdd g)) p.1.1) := by
  let _ := actualLocalCuspQuotientAction W
  intro g p
  let C := restrictedActualLocalPhaseCoefficients N M₁ W.localWitness.radius
    W.localWitness.radius_pos W.localWitness.radius_le
  change ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
    (Multiplicative.toAdd g) p.1 : M₁.Carrier) = _
  rw [← C.psiMap_eq_generic, C.psiMap_coe]
  change CuspToricPhaseAction.ToricModel.phaseAction M₁
    (N.phaseCoefficient (Multiplicative.toAdd g) (M₁.t p.1.1)) _ = _
  rw [show M₁.t p.1.1 = 0 from p.2]

public theorem centralModelHomeomorph_equivariant
    (W₁ : ActualPuncturedCuspCollarWitness N M₁)
    (W₂ : ActualPuncturedCuspCollarWitness N M₂) :
    letI := actualLocalCuspQuotientAction W₁
    letI := actualLocalCuspQuotientAction W₂
    ∀ (g : Multiplicative ParameterLattice) (p : actualLocalCuspCentralSubMulAction W₁),
      centralModelHomeomorph W₁ W₂ (g • p) = g • centralModelHomeomorph W₁ W₂ p := by
  let _ := actualLocalCuspQuotientAction W₁
  let _ := actualLocalCuspQuotientAction W₂
  intro g p
  apply Subtype.ext
  apply Subtype.ext
  change Model.transport M₁ M₂ (g • p).1.1 =
    (g • centralModelHomeomorph W₁ W₂ p).1.1
  rw [central_smul_coe W₁, central_smul_coe W₂]
  simp only [CuspToricPhaseAction.ToricModel.phaseAction_apply, Model.transport_torusAction,
    Model.transport_fanShear]
  rfl

public def centralOrbitModelHomeomorph (W₁ : ActualPuncturedCuspCollarWitness N M₁)
    (W₂ : ActualPuncturedCuspCollarWitness N M₂) :
    ActualLocalCuspCentralOrbitQuotient W₁ ≃ₜ ActualLocalCuspCentralOrbitQuotient W₂ := by
  let _ := actualLocalCuspQuotientAction W₁
  let _ := actualLocalCuspQuotientAction W₂
  apply Homeomorph.Quotient.congr (centralModelHomeomorph W₁ W₂)
  intro x y
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [← centralModelHomeomorph_equivariant W₁ W₂, hg]
  · rintro ⟨g, hg⟩
    refine ⟨g, (centralModelHomeomorph W₁ W₂).injective ?_⟩
    rw [centralModelHomeomorph_equivariant W₁ W₂]
    exact hg

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
