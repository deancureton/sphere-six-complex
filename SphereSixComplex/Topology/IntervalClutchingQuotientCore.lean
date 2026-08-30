module

public import SphereSixComplex.Topology.WangHomologyPresentationDefs

/-!
# Interval clutching quotients

The source-independent quotient-topology comparison between an interval clutching presentation
and the explicit one-loop mapping torus.
-/

@[expose] public section

noncomputable section

open Topology
open scoped ContinuousMap

namespace SphereSixComplex

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- The cylinder projection to the explicit one-loop mapping torus. -/
public def circleMappingTorusCylinderProjection (φ : F ≃ₜ F) :
    C(unitInterval × F, CircleMappingTorus φ) :=
  ⟨fun p ↦ Quotient.mk (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ φ)) ((), p),
    continuous_quot_mk.comp (continuous_const.prodMk continuous_id)⟩

/-- A chosen interval trivialization of a circle bundle, stated at the exact quotient-topology
level needed to recover its total space. -/
public structure IntervalClutchingQuotientData (E F : Type)
    [TopologicalSpace E] [TopologicalSpace F] (φ : F ≃ₜ F) where
  projection : C(unitInterval × F, E)
  projection_surjective : Function.Surjective projection
  projection_isQuotientMap : IsQuotientMap projection
  projection_eq_iff : ∀ p q,
    projection p = projection q ↔
      circleMappingTorusCylinderProjection φ p =
        circleMappingTorusCylinderProjection φ q

namespace IntervalClutchingQuotientData

variable {φ : F ≃ₜ F} (D : IntervalClutchingQuotientData E F φ)

/-- The map from the explicit mapping torus to a total space presented by the same clutching
quotient. -/
public def circleToTotal : CircleMappingTorus φ → E :=
  Quotient.lift (fun p ↦ D.projection p.2) fun p q hpq ↦ by
    apply (D.projection_eq_iff p.2 q.2).mpr
    exact Quotient.sound hpq

public theorem circleToTotal_mk (p : unitInterval × F) :
    D.circleToTotal (circleMappingTorusCylinderProjection φ p) = D.projection p :=
  rfl

public theorem circleToTotal_continuous : Continuous D.circleToTotal := by
  apply continuous_quot_lift
  exact D.projection.continuous.comp continuous_snd

public theorem circleToTotal_bijective : Function.Bijective D.circleToTotal := by
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn with
    | _ p =>
      induction y using Quotient.inductionOn with
      | _ q =>
        apply (D.projection_eq_iff p.2 q.2).mp
        exact hxy
  · intro y
    obtain ⟨p, hp⟩ := D.projection_surjective y
    exact ⟨circleMappingTorusCylinderProjection φ p, by simpa [hp]⟩

/-- A total space with an exact interval clutching presentation is homeomorphic to the explicit
mapping torus of its clutching map. -/
public def totalHomeomorphCircleMappingTorus : E ≃ₜ CircleMappingTorus φ := by
  let e : CircleMappingTorus φ ≃ E := Equiv.ofBijective D.circleToTotal D.circleToTotal_bijective
  have he : Continuous e := D.circleToTotal_continuous
  have hcomp : e.symm ∘ D.projection = circleMappingTorusCylinderProjection φ := by
    funext p
    apply e.injective
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    exact D.circleToTotal_mk p
  exact (Homeomorph.mk e he
    (D.projection_isQuotientMap.continuous_iff.mpr (hcomp ▸
      (circleMappingTorusCylinderProjection φ).continuous))).symm

end IntervalClutchingQuotientData

end SphereSixComplex

end

end
