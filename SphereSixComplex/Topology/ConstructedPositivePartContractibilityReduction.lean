module

public import SphereSixComplex.Topology.ConstructedA2GlobalMomentExistenceProof

/-!
# Direct contractibility reduction for the constructed positive part

The explicit polar modulus is a continuous retraction from the constructed local carrier onto
its nonnegative locus. Consequently, contractibility of the local carrier would imply
contractibility of the positive part without any moment coordinates.

The existing chart-cover argument proves only that the local carrier is simply connected. A
global contraction of that carrier, or a different global coordinate homeomorphism compatible
with the central toric strata, is still required.
-/

@[expose] public section

noncomputable section

open ContinuousMap Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established

open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

/-- A continuous retract of a contractible space is contractible. -/
public theorem contractibleSpace_of_continuousRetract
    {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]
    [ContractibleSpace X] (i : C(A, X)) (R : C(X, A))
    (hR : R.comp i = ContinuousMap.id A) :
    ContractibleSpace A := by
  rw [contractible_iff_id_nullhomotopic]
  obtain ⟨x, hx⟩ := id_nullhomotopic X
  refine ⟨R x, ?_⟩
  rw [← hR]
  simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp,
    ContinuousMap.comp_const] using
    ContinuousMap.Homotopic.comp (.refl R)
      (ContinuousMap.Homotopic.comp hx (.refl i))

/-- The explicit modulus reduces positive-part contractibility to contractibility of the whole
constructed local carrier. -/
public theorem constructedLocalPositivePart_contractible_of_localCarrier
    (r : ℝ) [ContractibleSpace (LocalCarrier constructedModel r)] :
    ContractibleSpace (constructedLocalPositivePart r) := by
  let i : C(constructedLocalPositivePart r, LocalCarrier constructedModel r) :=
    ⟨fun q ↦ q, continuous_subtype_val⟩
  let R := constructedLocalModulusRetraction r
  apply contractibleSpace_of_continuousRetract i R
  apply ContinuousMap.ext
  intro q
  change constructedLocalModulusRetraction r
    (q : LocalCarrier constructedModel r) = q
  exact constructedLocalModulusRetraction_fixed r q

/-- The currently specified logarithmic moment-coordinate certificate cannot supply the missing
contraction: it is inconsistent with the explicit central degeneration. -/
public theorem no_constructedA2ProperMomentCoordinate
    {r : ℝ} (hr : 0 < r) (H : ConstructedHoneycombCellData r) :
    ¬ Nonempty (ConstructedA2ProperMomentCoordinate r H) := by
  intro h
  let _ : IsEmpty (ConstructedA2ProperMomentCoordinate r H) :=
    constructedA2ProperMomentCoordinate_isEmpty hr H
  exact IsEmpty.false h.some

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
