module

public import SphereSixComplex.Topology.ConstructedPositiveInteriorProjection
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomainProof
public import Mathlib.Topology.Instances.AddCircle.Real

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex.Periods CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate
open CuspPeriodExpansion StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def positiveLogTorusProjection (r : ℝ) :
    ((Fin 2 → ℝ) × Set.Ioo (0 : ℝ) r) → ((Fin 2 → UnitAddCircle) × Set.Ioo (0 : ℝ) r) :=
  Prod.map (fun x i ↦ (x i : UnitAddCircle)) id

theorem positiveLogTorusProjection_isQuotientMap (r : ℝ) :
    IsQuotientMap (positiveLogTorusProjection r) := by
  have h : IsOpenQuotientMap (fun x : Fin 2 → ℝ ↦ fun i ↦ (x i : UnitAddCircle)) :=
    IsOpenQuotientMap.piMap (fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk)
  exact (h.prodMap IsOpenQuotientMap.id).isQuotientMap

theorem realVector_torus_eq_iff (x y : Fin 2 → ℝ) :
    (fun i ↦ (x i : UnitAddCircle)) = (fun i ↦ (y i : UnitAddCircle)) ↔
      ∃ lambda : ParameterLattice, x = y + realParameter lambda := by
  constructor
  · intro h
    have hi (i : Fin 2) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
      have hh : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, congrFun h i, sub_self]
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hh
    choose lambda hlambda using hi
    refine ⟨lambda, ?_⟩
    ext i
    change x i = y i + (lambda i : ℝ)
    rw [hlambda]
    ring
  · rintro ⟨lambda, rfl⟩
    ext i
    change ((y i + (lambda i : ℝ) : ℝ) : UnitAddCircle) = _
    rw [AddCircle.coe_add]
    have h : ((lambda i : ℝ) : UnitAddCircle) = 0 :=
      (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨lambda i, by simp⟩
    rw [h, add_zero]

def constructedPositiveInteriorTorusMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :=
  positiveLogTorusProjection W.localWitness.radius ∘ positiveInteriorLogProduct W

theorem constructedPositiveInteriorTorusMap_isQuotientMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsQuotientMap (constructedPositiveInteriorTorusMap W) :=
  (positiveLogTorusProjection_isQuotientMap W.localWitness.radius).comp
    (positiveInteriorLogProduct W).isQuotientMap

theorem constructedPositiveInteriorTorusMap_fibers
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : constructedA2PositiveOffCentral W.localWitness.radius) :
    constructedPositiveInteriorProjection W p = constructedPositiveInteriorProjection W q ↔
      constructedPositiveInteriorTorusMap W p = constructedPositiveInteriorTorusMap W q := by
  rw [constructedPositiveInteriorProjection_eq_iff]
  change (∃ lambda, positiveOffCentralDeck W lambda q = p) ↔
    ((fun i ↦ ((positiveInteriorLogProduct W p).1 i : UnitAddCircle)),
      (positiveInteriorLogProduct W p).2) =
    ((fun i ↦ ((positiveInteriorLogProduct W q).1 i : UnitAddCircle)),
      (positiveInteriorLogProduct W q).2)
  rw [Prod.mk.injEq, realVector_torus_eq_iff]
  constructor
  · rintro ⟨lambda, h⟩
    obtain ⟨h₁, h₂⟩ := (positiveOffCentralDeck_eq_iff_logProduct W lambda q p).mp h
    exact ⟨⟨lambda, h₁⟩, h₂⟩
  · rintro ⟨⟨lambda, h₁⟩, h₂⟩
    exact ⟨lambda, (positiveOffCentralDeck_eq_iff_logProduct W lambda q p).mpr ⟨h₁, h₂⟩⟩

def constructedPositiveInteriorTorusHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ↥((ConstructedA2PositiveQuotientCore W)ᶜ) ≃ₜ
      ((Fin 2 → UnitAddCircle) × Set.Ioo (0 : ℝ) W.localWitness.radius) :=
  CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
    (constructedPositiveInteriorProjection_isQuotientMap W)
    (constructedPositiveInteriorTorusMap_isQuotientMap W)
    (constructedPositiveInteriorTorusMap_fibers W)

theorem constructedPositiveInteriorTorusHomeomorph_projection
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : constructedA2PositiveOffCentral W.localWitness.radius) :
    constructedPositiveInteriorTorusHomeomorph W (constructedPositiveInteriorProjection W p) =
      constructedPositiveInteriorTorusMap W p :=
  CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps_apply _ _ _ p

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
