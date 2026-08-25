module

public import SphereSixComplex.Topology.GeometricOrientedHCobordismSix

/-!
# Oriented gluing of geometric h-cobordisms of six-spheres

The smooth gluing already constructs the underlying collared h-cobordism.  This module keeps
canonical homotopy equivalences from both old bordism carriers into the glued carrier.  Their
forward maps agree on the common end, so cancellation of homotopy inverses identifies the new
outer transition with the composite of the two old transitions.  The two given orientation
conditions can consequently be composed.
-/

@[expose] public section

noncomputable section

open ContinuousMap Function
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

namespace OrientedMarkedSmoothHomotopySixSphere

namespace SmoothHCobordism

universe uA uB uG uY

/-- If two homotopy equivalences into a common target agree after maps out of the same source,
then the transition between their sources is homotopic to the transition through that source. -/
public theorem transition_homotopic_of_commute
    {A : Type uA} {B : Type uB} {G : Type uG} {Y : Type uY}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace G] [TopologicalSpace Y]
    (a : A ≃ₕ G) (b : B ≃ₕ G) (o : Y ≃ₕ A) (i : Y ≃ₕ B)
    (hcomm : a.toFun.comp o.toFun = b.toFun.comp i.toFun) :
    (a.trans b.symm).toFun.Homotopic (o.symm.trans i).toFun := by
  have ho :
      (b.invFun.comp (a.toFun.comp (o.toFun.comp o.invFun))).Homotopic
        (b.invFun.comp a.toFun) :=
    ContinuousMap.Homotopic.comp (.refl b.invFun)
      (ContinuousMap.Homotopic.comp (.refl a.toFun) o.right_inv)
  have hmiddle :
      b.invFun.comp (a.toFun.comp (o.toFun.comp o.invFun)) =
        b.invFun.comp (b.toFun.comp (i.toFun.comp o.invFun)) := by
    apply congrArg (fun f ↦ b.invFun.comp f)
    calc
      a.toFun.comp (o.toFun.comp o.invFun) =
          (a.toFun.comp o.toFun).comp o.invFun :=
        (ContinuousMap.comp_assoc _ _ _).symm
      _ = (b.toFun.comp i.toFun).comp o.invFun :=
        congrArg (fun f ↦ f.comp o.invFun) hcomm
      _ = b.toFun.comp (i.toFun.comp o.invFun) :=
        ContinuousMap.comp_assoc _ _ _
  have hb :
      (b.invFun.comp (b.toFun.comp (i.toFun.comp o.invFun))).Homotopic
        (i.toFun.comp o.invFun) := by
    rw [← ContinuousMap.comp_assoc]
    exact ContinuousMap.Homotopic.comp b.left_inv
      (.refl (i.toFun.comp o.invFun))
  have hmiddleHomotopic :
      (b.invFun.comp (a.toFun.comp (o.toFun.comp o.invFun))).Homotopic
        (b.invFun.comp (b.toFun.comp (i.toFun.comp o.invFun))) := by
    rw [hmiddle]
  exact ho.symm.trans (hmiddleHomotopic.trans hb)

variable {D : SixSphereDegreeTheory}
variable {X Y Z : OrientedMarkedSmoothHomotopySixSphere.{0}}

/-- The canonical homotopy equivalence from the left old bordism carrier into the smooth glued
carrier.  It is obtained from the seam strong deformation retract and the comparison between the
direct quotient and the smooth three-piece presentation. -/
public noncomputable def gluedLeftCarrierEquiv
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    B₀₁.bordism.W ≃ₕ
      SmoothCollaredBordism.QuotientGluing.OpenGluedCarrier
        B₀₁.bordism B₁₂.bordism := by
  let hSeam := B₁₂.isHCobordism.1
  let retract := Classical.choice
    (B₁₂.bordism.incoming.exists_ambientStrongDeformationRetract hSeam)
  let hLeft :=
    SmoothCollaredBordism.QuotientGluing.toGlueLeft_isHomotopyEquivalence_of_strong
      B₀₁.bordism B₁₂.bordism retract
  exact hLeft.postcompHomeomorph
    (SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
      B₀₁.bordism B₁₂.bordism).symm

/-- The canonical homotopy equivalence from the right old bordism carrier into the smooth glued
carrier. -/
public noncomputable def gluedRightCarrierEquiv
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    B₁₂.bordism.W ≃ₕ
      SmoothCollaredBordism.QuotientGluing.OpenGluedCarrier
        B₀₁.bordism B₁₂.bordism := by
  let hSeam := B₀₁.isHCobordism.2
  let retract := Classical.choice
    (B₀₁.bordism.outgoing.exists_ambientStrongDeformationRetract hSeam)
  let hRight :=
    SmoothCollaredBordism.QuotientGluing.toGlueRight_isHomotopyEquivalence_of_strong
      B₀₁.bordism B₁₂.bordism retract
  exact hRight.postcompHomeomorph
    (SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
      B₀₁.bordism B₁₂.bordism).symm

@[simp]
public theorem gluedLeftCarrierEquiv_apply
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z)
    (w : B₀₁.bordism.W) :
    gluedLeftCarrierEquiv B₀₁ B₁₂ w =
      (SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
        B₀₁.bordism B₁₂.bordism).symm
        (SmoothCollaredBordism.QuotientGluing.toGlueLeft B₀₁.bordism B₁₂.bordism w) := by
  unfold gluedLeftCarrierEquiv
  rw [IsHomotopyEquivalence.postcompHomeomorph_apply]

@[simp]
public theorem gluedRightCarrierEquiv_apply
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z)
    (w : B₁₂.bordism.W) :
    gluedRightCarrierEquiv B₀₁ B₁₂ w =
      (SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
        B₀₁.bordism B₁₂.bordism).symm
        (SmoothCollaredBordism.QuotientGluing.toGlueRight B₀₁.bordism B₁₂.bordism w) := by
  unfold gluedRightCarrierEquiv
  rw [IsHomotopyEquivalence.postcompHomeomorph_apply]

/-- The canonical left and right carrier equivalences agree on the common glued end. -/
public theorem gluedCarrierEquiv_seam
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) (y : Y.carrier) :
    gluedLeftCarrierEquiv B₀₁ B₁₂ (B₀₁.bordism.outgoing.inclusion y) =
      gluedRightCarrierEquiv B₀₁ B₁₂ (B₁₂.bordism.incoming.inclusion y) := by
  rw [gluedLeftCarrierEquiv_apply, gluedRightCarrierEquiv_apply]
  congr 1
  exact SmoothCollaredBordism.QuotientGluing.toGlue_commute
    B₀₁.bordism B₁₂.bordism y

/-- The transition induced by the canonical carrier equivalences is the old seam transition, up
to homotopy. -/
public theorem gluedCarrierTransition_homotopic_seamTransition
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    ((gluedLeftCarrierEquiv B₀₁ B₁₂).trans
      (gluedRightCarrierEquiv B₀₁ B₁₂).symm).toFun.Homotopic
        (B₀₁.outgoingEquiv.symm.trans B₁₂.incomingEquiv).toFun := by
  apply transition_homotopic_of_commute
  ext y
  rw [ContinuousMap.comp_apply, ContinuousMap.comp_apply]
  rw [congrFun B₀₁.outgoingEquiv_toFun y, congrFun B₁₂.incomingEquiv_toFun y]
  exact gluedCarrierEquiv_seam B₀₁ B₁₂ y

/-- After adjoining the two untouched outer ends, the transition of the canonical glued
h-cobordism is homotopic to the composite of the original transitions. -/
public theorem gluedOuterTransition_homotopic_composite
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    ((B₀₁.incomingEquiv.trans (gluedLeftCarrierEquiv B₀₁ B₁₂)).trans
      (B₁₂.outgoingEquiv.trans (gluedRightCarrierEquiv B₀₁ B₁₂)).symm).toFun.Homotopic
        (B₀₁.transition.trans B₁₂.transition).toFun := by
  exact ContinuousMap.Homotopic.comp (.refl B₁₂.outgoingEquiv.invFun)
    (ContinuousMap.Homotopic.comp
      (gluedCarrierTransition_homotopic_seamTransition B₀₁ B₁₂)
      (.refl B₀₁.incomingEquiv.toFun))

/-- The canonical incoming equivalence has exactly the incoming collar inclusion of the smooth
gluing as its forward map. -/
public theorem gluedIncomingEquiv_toFun
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    ((B₀₁.incomingEquiv.trans (gluedLeftCarrierEquiv B₀₁ B₁₂)) :
      X.carrier →
        SmoothCollaredBordism.QuotientGluing.OpenGluedCarrier
          B₀₁.bordism B₁₂.bordism) =
      (SmoothCollaredBordism.QuotientGluing.smoothGlue
        B₀₁.bordism B₁₂.bordism).incoming.inclusion := by
  funext x
  let h := SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
    B₀₁.bordism B₁₂.bordism
  apply h.injective
  change h (gluedLeftCarrierEquiv B₀₁ B₁₂ (B₀₁.incomingEquiv x)) =
    h ((SmoothCollaredBordism.QuotientGluing.smoothGlue
      B₀₁.bordism B₁₂.bordism).incoming.inclusion x)
  rw [congrFun B₀₁.incomingEquiv_toFun x, gluedLeftCarrierEquiv_apply,
    Homeomorph.apply_symm_apply]
  rw [SmoothCollaredBordism.QuotientGluing.smoothGlue_incoming_inclusion,
    SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph_smoothIncomingInclusion]
  rfl

/-- The canonical outgoing equivalence has exactly the outgoing collar inclusion of the smooth
gluing as its forward map. -/
public theorem gluedOutgoingEquiv_toFun
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    ((B₁₂.outgoingEquiv.trans (gluedRightCarrierEquiv B₀₁ B₁₂)) :
      Z.carrier →
        SmoothCollaredBordism.QuotientGluing.OpenGluedCarrier
          B₀₁.bordism B₁₂.bordism) =
      (SmoothCollaredBordism.QuotientGluing.smoothGlue
        B₀₁.bordism B₁₂.bordism).outgoing.inclusion := by
  funext z
  let h := SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph
    B₀₁.bordism B₁₂.bordism
  apply h.injective
  change h (gluedRightCarrierEquiv B₀₁ B₁₂ (B₁₂.outgoingEquiv z)) =
    h ((SmoothCollaredBordism.QuotientGluing.smoothGlue
      B₀₁.bordism B₁₂.bordism).outgoing.inclusion z)
  rw [congrFun B₁₂.outgoingEquiv_toFun z, gluedRightCarrierEquiv_apply,
    Homeomorph.apply_symm_apply]
  rw [SmoothCollaredBordism.QuotientGluing.smoothGlue_outgoing_inclusion,
    SmoothCollaredBordism.QuotientGluing.openPresentationHomeomorph_smoothOutgoingInclusion]
  rfl

/-- The two old orientation conditions compose to the orientation condition for their composite
endpoint transition. -/
public theorem compositeTransition_orientation_preserving
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    SameOrientation D X.marking
      ((B₀₁.transition.trans B₁₂.transition).trans Z.marking) := by
  have hpre := SameOrientation.precomp D B₀₁.transition B₁₂.orientation_preserving
  apply SameOrientation.trans D B₀₁.orientation_preserving
  apply SameOrientation.trans D hpre
  apply SameOrientation.of_homotopic
  exact .refl _

/-- The canonical glued outer transition preserves the endpoint markings. -/
public theorem gluedOuterTransition_orientation_preserving
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    SameOrientation D X.marking
      ((((B₀₁.incomingEquiv.trans (gluedLeftCarrierEquiv B₀₁ B₁₂)).trans
        (B₁₂.outgoingEquiv.trans (gluedRightCarrierEquiv B₀₁ B₁₂)).symm).trans
          Z.marking)) := by
  apply SameOrientation.trans D
    (compositeTransition_orientation_preserving B₀₁ B₁₂)
  apply SameOrientation.of_homotopic
  exact ContinuousMap.Homotopic.comp (.refl Z.marking.toFun)
    (gluedOuterTransition_homotopic_composite B₀₁ B₁₂).symm

/-- Smooth gluing, equipped with its canonical end equivalences, is an oriented geometric
h-cobordism. -/
public noncomputable def glue
    (B₀₁ : SmoothHCobordism D X Y) (B₁₂ : SmoothHCobordism D Y Z) :
    SmoothHCobordism D X Z where
  bordism := SmoothCollaredBordism.QuotientGluing.smoothGlue B₀₁.bordism B₁₂.bordism
  incomingEquiv := B₀₁.incomingEquiv.trans (gluedLeftCarrierEquiv B₀₁ B₁₂)
  incomingEquiv_toFun := gluedIncomingEquiv_toFun B₀₁ B₁₂
  outgoingEquiv := B₁₂.outgoingEquiv.trans (gluedRightCarrierEquiv B₀₁ B₁₂)
  outgoingEquiv_toFun := gluedOutgoingEquiv_toFun B₀₁ B₁₂
  orientation_preserving := gluedOuterTransition_orientation_preserving B₀₁ B₁₂

end SmoothHCobordism

/-- The constructed smooth closed-boundary gluing proves the global oriented gluing theorem for
marked homotopy six-spheres. -/
public theorem smoothHCobordismGluingTheorem (D : SixSphereDegreeTheory) :
    SmoothHCobordismGluingTheorem D := by
  intro X Y Z B₀₁ B₁₂
  exact ⟨SmoothHCobordism.glue B₀₁ B₁₂⟩

/-- Consequently the genuine geometric oriented h-cobordism relation is available without a
separate gluing hypothesis. -/
public noncomputable def unconditionalGeometricSmoothHCobordismRelation
    (D : SixSphereDegreeTheory) : OrientedSmoothHCobordismRelation :=
  geometricSmoothHCobordismRelation D (smoothHCobordismGluingTheorem D)

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
