module

public import SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality
public import SphereSixComplex.Topology.PositiveCircleCross

/-!
# Orbit sweeps for normalized finite-order mapping-torus covers
-/

@[expose] public section

noncomputable section

open AlgebraicTopology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep

open CircleProductIdentityMappingTorus
open FiniteCyclicMappingTorusWangNaturality
open NormalizedAffineMappingTorusCover
open PositiveCircleCross
open StandardTorusHomology

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]

/-- Postcomposition by an additive self-homeomorphism on parametrized circle maps. -/
public def loopAction (phi : G ≃ₜ+ G) :
    C(StdTorus 1, G) →ₗ[ℤ] C(StdTorus 1, G) where
  toFun c := (⟨phi, phi.toHomeomorph.continuous⟩ : C(G, G)).comp c
  map_add' c d := by
    ext x
    exact map_add phi (c x) (d x)
  map_smul' n c := by
    ext x
    exact map_zsmul phi.toAddEquiv n (c x)

/-- Parametrized circle maps fixed pointwise after postcomposition by `phi`. -/
public abbrev FixedLoop (phi : G ≃ₜ+ G) :=
  LinearMap.ker (loopAction phi - LinearMap.id)

private theorem loopAction_pow_apply (phi : G ≃ₜ+ G) (n : ℕ)
    (c : C(StdTorus 1, G)) :
    ((loopAction phi) ^ n) c =
      (((phi.toHomeomorph ^ n : G ≃ₜ G) : C(G, G)).comp c) := by
  induction n generalizing c with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ]
      change ((loopAction phi) ^ n) (loopAction phi c) = _
      rw [ih]
      ext x
      rfl

/-- The cyclic orbit norm, regarded as a pointwise-fixed parametrized loop. -/
public def orbitNorm (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) :
    C(StdTorus 1, G) →ₗ[ℤ] FixedLoop phi :=
  (∑ i ∈ Finset.range m, (loopAction phi) ^ i).codRestrict _ fun c => by
    apply LinearMap.mem_ker.mpr
    let A : Module.End ℤ C(StdTorus 1, G) := loopAction phi
    have hgeom := DFunLike.congr_fun (mul_geom_sum A m) c
    change (A - 1) ((∑ i ∈ Finset.range m, A ^ i) c) =
        (A ^ m - 1) c at hgeom
    dsimp [A] at hgeom
    rw [LinearMap.sub_apply, LinearMap.id_apply, hgeom]
    change ((loopAction phi) ^ m) c - c = 0
    rw [loopAction_pow_apply, hpow]
    ext x
    simp

@[simp]
public theorem orbitNorm_value (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G)) :
    (orbitNorm m phi hpow c).1 =
      ∑ i ∈ Finset.range m, ((loopAction phi) ^ i) c :=
  by simp [orbitNorm]

/-- Chain-level orbit-sweep data for a normalized finite cyclic mapping-torus cover.

No splitting of the full invariant homology is asserted.  The sweep is defined only on explicit
pointwise-fixed parametrized loops. -/
public structure SweepData (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) where
  fibre_square : ∀ x : IntegralSingularHomology 2 G,
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (integralSingularHomologyMap 2 (circleProductFiberInclusion (X := G)) x) =
      (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).inclusion x
  boundary_square : ∀ z : IntegralSingularHomology 2 (UnitAddCircle × G),
    (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
        (integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow) z) =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap 1
          ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
          (canonicalProductWangBoundary 1 z)
  fixedSweep : FixedLoop phi →+ IntegralSingularHomology 2
    (CircleMappingTorus phi.toHomeomorph)
  boundary_fixedSweep : ∀ c,
    (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
        (fixedSweep c) =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator
  normalizedCover_cross : ∀ c,
    integralSingularHomologyMap 2
        (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
        (positiveCircleCross c) =
      fixedSweep (orbitNorm m phi hpow c)

/-- The standard chain-level mapping-cone orbit-sweep theorem.

For a finite-order additive self-homeomorphism, this packages the standard mapping-cone
naturality squares together with the chain-level orbit sweep.  The normalized cover sends the
positive base-circle cross a fibre loop to the sweep of its cyclic orbit norm, and the final
boundary clause fixes the Mayer--Vietoris sign on every pointwise-fixed loop. -/
public axiom normalizedFiniteOrderAdditiveCircleSweep
    [PathConnectedSpace G]
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) :
    Nonempty (SweepData m phi hpow)

end SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweep

end

end
