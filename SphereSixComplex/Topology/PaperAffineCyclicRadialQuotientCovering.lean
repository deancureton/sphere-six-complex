module

public import SphereSixComplex.Topology.PaperAffineCyclicQuotientCovering
public import SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
public import SphereSixComplex.TriangleGroup.Representation

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
namespace EstablishedAffineCyclicQuotientHomology

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.LatticeData
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

/-- Pull an action back through a homeomorphism of its underlying space. -/
@[instance_reducible]
public noncomputable def pullbackMulActionHomeomorph
    {G E E' : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace E']
    (action : MulAction G E) (e : E' ≃ₜ E) : MulAction G E' where
  smul g x := e.symm (@SMul.smul _ _ action.toSMul g (e x))
  one_smul x := by
    change e.symm (@SMul.smul _ _ action.toSMul 1 (e x)) = x
    exact (congrArg e.symm
      (@MulAction.one_smul G E _ action (e x))).trans
        (e.symm_apply_apply x)
  mul_smul g h x := by
    change e.symm (@SMul.smul _ _ action.toSMul (g * h) (e x)) =
      e.symm (@SMul.smul _ _ action.toSMul g
        (e (e.symm (@SMul.smul _ _ action.toSMul h (e x)))))
    rw [e.apply_symm_apply]
    exact congrArg e.symm
      (@SemigroupAction.mul_smul G E _ action.toSemigroupAction
        g h (e x))

/-- Precomposition by a homeomorphism preserves a quotient-covering structure when the deck
action is conjugated through that homeomorphism. -/
public theorem isQuotientCoveringMap_comp_homeomorph
    {G E E' B : Type*} [Group G]
    [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
    (action : MulAction G E) (e : E' ≃ₜ E) (f : E → B)
    (hf : @IsQuotientCoveringMap E B _ _ f G _ action) :
    let action' := pullbackMulActionHomeomorph action e
    @IsQuotientCoveringMap E' B _ _ (f ∘ e) G _ action' := by
  let _ := action
  let action' := pullbackMulActionHomeomorph action e
  let _ := action'
  refine
    { toIsQuotientMap := hf.toIsQuotientMap.comp e.isQuotientMap
      continuous_const_smul := fun g ↦ e.symm.continuous.comp
        ((hf.continuous_const_smul g).comp e.continuous)
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro x y
    change f (e x) = f (e y) ↔ _
    rw [hf.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      apply e.injective
      change e (e.symm (@SMul.smul _ _ action.toSMul g (e y))) = e x
      rw [e.apply_symm_apply]
      exact hg
    · rintro ⟨g, hg⟩
      refine ⟨g, ?_⟩
      have := congrArg e hg
      change e (e.symm (@SMul.smul _ _ action.toSMul g (e y))) = e x at this
      rw [e.apply_symm_apply] at this
      exact this
  · intro x
    obtain ⟨U, hU, hdisjoint⟩ := hf.disjoint (e x)
    refine ⟨e ⁻¹' U, e.continuous.continuousAt hU, ?_⟩
    rintro g ⟨z, hzImage, hzU⟩
    rcases hzImage with ⟨y, hyU, rfl⟩
    apply hdisjoint g
    refine ⟨@SMul.smul _ _ action.toSMul g (e y),
      ⟨e y, hyU, rfl⟩, ?_⟩
    change e (e.symm (@SMul.smul _ _ action.toSMul g (e y))) ∈ U at hzU
    rw [e.apply_symm_apply] at hzU
    exact hzU

variable {m : ℕ} [NeZero m]
variable {p : SphereSixComplex.Periods.Parameters}
variable {D : RadialEllipticActionData m (AdditiveTorus p)}

/-- The finite cyclic degree of the canonical affine filling deck group. -/
public noncomputable def affineCyclicFillingDegree
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).FillingDeck →* FiniteCyclic m :=
  affineCyclicBoundaryDegree P

public theorem affineCyclicFillingDegree_fillingDeckMap
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (d : CanonicalCyclicAffineBoundaryDeck P.affine.latticeMap.toAddEquiv) :
    affineCyclicFillingDegree P
        ((affineCyclicBoundaryDeckData P).fillingDeckMap d) =
      Multiplicative.ofAdd (((d.right.toAdd : ℤ) : ZMod m)) := by
  rfl

/-- The disc rotation associated to the finite degree of a filling deck transformation. -/
public noncomputable def affineCyclicFillingDiscRepresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).FillingDeck →* Equiv.Perm ComplexUnitDisc :=
  (cyclicRepresentation m D.actionData.rotation D.actionData.rotation_pow).comp
    (affineCyclicFillingDegree P)

/-- The fibre action associated to the finite degree of a filling deck transformation. -/
public noncomputable def affineCyclicFillingFiberRepresentation
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    (affineCyclicBoundaryDeckData P).FillingDeck →*
      Equiv.Perm (AdditiveTorus p) :=
  (cyclicRepresentation m D.actionData.fiberGenerator
    D.actionData.fiberGenerator_pow).comp (affineCyclicFillingDegree P)

public theorem affineCyclicFillingDiscRepresentation_apply_eq_pow
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck) (u : ComplexUnitDisc) :
    affineCyclicFillingDiscRepresentation P g u =
      (D.actionData.rotation ^
        (Multiplicative.toAdd (affineCyclicFillingDegree P g)).val) u := by
  rw [affineCyclicFillingDiscRepresentation, MonoidHom.comp_apply]
  let c := affineCyclicFillingDegree P g
  calc
    (cyclicRepresentation m D.actionData.rotation D.actionData.rotation_pow) c u =
        (cyclicRepresentation m D.actionData.rotation D.actionData.rotation_pow)
          (cyclicGenerator m ^ (Multiplicative.toAdd c).val) u := by
      rw [← cyclic_eq_generator_pow c]
    _ = (D.actionData.rotation ^ (Multiplicative.toAdd c).val) u := by
      rw [map_pow,
        show cyclicGenerator m = Multiplicative.ofAdd 1 from rfl,
        cyclicRepresentation_generator]

public theorem affineCyclicFillingFiberRepresentation_apply_eq_pow
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck) (u : AdditiveTorus p) :
    affineCyclicFillingFiberRepresentation P g u =
      (D.actionData.fiberGenerator ^
        (Multiplicative.toAdd (affineCyclicFillingDegree P g)).val) u := by
  rw [affineCyclicFillingFiberRepresentation, MonoidHom.comp_apply]
  let c := affineCyclicFillingDegree P g
  calc
    (cyclicRepresentation m D.actionData.fiberGenerator
        D.actionData.fiberGenerator_pow) c u =
      (cyclicRepresentation m D.actionData.fiberGenerator
        D.actionData.fiberGenerator_pow)
          (cyclicGenerator m ^ (Multiplicative.toAdd c).val) u := by
      rw [← cyclic_eq_generator_pow c]
    _ = (D.actionData.fiberGenerator ^ (Multiplicative.toAdd c).val) u := by
      rw [map_pow,
        show cyclicGenerator m = Multiplicative.ofAdd 1 from rfl,
        cyclicRepresentation_generator]

/-- The canonical filling deck action on the radial vector cover. -/
@[instance_reducible]
public noncomputable def affineCyclicRadialFillingDeckAction
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    MulAction (affineCyclicBoundaryDeckData P).FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) where
  smul g q := (affineCyclicFillingDiscRepresentation P g q.1,
    @SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul g q.2)
  one_smul q := by
    apply Prod.ext
    · change affineCyclicFillingDiscRepresentation P 1 q.1 = q.1
      rw [map_one]
      rfl
    · exact @one_smul _ _ _ (affineCyclicFillingDeckAction P) q.2
  mul_smul g h q := by
    apply Prod.ext
    · change affineCyclicFillingDiscRepresentation P (g * h) q.1 =
        affineCyclicFillingDiscRepresentation P g
          (affineCyclicFillingDiscRepresentation P h q.1)
      rw [map_mul]
      rfl
    · change affineCyclicFillingDeckRepresentation P (g * h) q.2 =
        affineCyclicFillingDeckRepresentation P g
          (affineCyclicFillingDeckRepresentation P h q.2)
      rw [map_mul]
      rfl

/-- Projection of the radial vector cover to the fixed finite cyclic filling quotient. -/
public noncomputable def affineCyclicRadialFillingProjection
    (_P : AffineCyclicCentralFiberPresentationData m p D) :
    C(ComplexUnitDisc × ComplexTwoSpace, D.FillingQuotient) where
  toFun q := Quotient.mk (orbitRelOf D.actionData.diagonalAction)
    (q.1, torusProjection p q.2)
  continuous_toFun := continuous_quot_mk.comp
    (continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd))

public theorem affineCyclicRadialFillingProjection_isOpenQuotientMap
    (P : AffineCyclicCentralFiberPresentationData m p D) :
    IsOpenQuotientMap (affineCyclicRadialFillingProjection P) := by
  let periodAction : MulAction (PeriodGroup p) ComplexTwoSpace := inferInstance
  let _ := periodAction
  have htorus : IsOpenQuotientMap (torusProjection p) := by
    change IsOpenQuotientMap
      (Quotient.mk (MulAction.orbitRel (PeriodGroup p) ComplexTwoSpace))
    exact MulAction.isOpenQuotientMap_quotientMk
  have hproduct : IsOpenQuotientMap
      (Prod.map (id : ComplexUnitDisc → ComplexUnitDisc) (torusProjection p)) :=
    IsOpenQuotientMap.id.prodMap htorus
  let diagonalAction := D.actionData.diagonalAction
  let _ := diagonalAction
  let _ : ContinuousConstSMul (FiniteCyclic m) D.Product :=
    ⟨D.representation_continuous⟩
  have hfinite : IsOpenQuotientMap
      (Quotient.mk (orbitRelOf D.actionData.diagonalAction) :
        D.Product → D.FillingQuotient) := by
    change IsOpenQuotientMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic m) D.Product))
    exact MulAction.isOpenQuotientMap_quotientMk
  change IsOpenQuotientMap
    ((Quotient.mk (orbitRelOf D.actionData.diagonalAction)) ∘
      Prod.map id (torusProjection p))
  exact hfinite.comp hproduct

public theorem torusProjection_affineCyclicFillingDeck_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck) (z : ComplexTwoSpace) :
    letI := affineCyclicFillingDeckAction P
    torusProjection p (g • z) =
      affineCyclicFillingFiberRepresentation P g (torusProjection p z) := by
  let _ := affineCyclicFillingDeckAction P
  obtain ⟨d, rfl⟩ :=
    (affineCyclicBoundaryDeckData P).fillingDeckMap_surjective g
  rw [affineCyclicFillingDeckMap_smul]
  change torusProjection p
      (periodVector p d.left.toAdd +
        (affineEquiv P.affine.lift P.liftTranslation ^ d.right.toAdd) z) = _
  rw [torusProjection_period_add, torusProjection_affineEquiv_zpow,
    fiberGenerator_zpow_eq_modOrder_pow,
    affineCyclicFillingFiberRepresentation_apply_eq_pow,
    affineCyclicFillingDegree_fillingDeckMap]
  rfl

public theorem affineCyclicRadialFillingProjection_smul
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (g : (affineCyclicBoundaryDeckData P).FillingDeck)
    (q : ComplexUnitDisc × ComplexTwoSpace) :
    letI := affineCyclicRadialFillingDeckAction P
    affineCyclicRadialFillingProjection P (g • q) =
      affineCyclicRadialFillingProjection P q := by
  let _ := affineCyclicRadialFillingDeckAction P
  apply Quotient.sound
  refine ⟨affineCyclicFillingDegree P g, ?_⟩
  change
    (D.actionData.representation (affineCyclicFillingDegree P g)
      (q.1, torusProjection p q.2)) =
    (affineCyclicFillingDiscRepresentation P g q.1,
      torusProjection p
        (@SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul g q.2))
  have hrepresentation :
      D.actionData.representation (affineCyclicFillingDegree P g) =
        D.actionData.diagonalGenerator ^
          (Multiplicative.toAdd (affineCyclicFillingDegree P g)).val := by
    let c := affineCyclicFillingDegree P g
    calc
      D.actionData.representation c =
          D.actionData.representation
            (cyclicGenerator m ^ (Multiplicative.toAdd c).val) := by
        rw [← cyclic_eq_generator_pow c]
      _ = D.actionData.diagonalGenerator ^ (Multiplicative.toAdd c).val := by
        rw [map_pow, D.actionData.representation_generator]
  rw [hrepresentation, D.actionData.diagonalGenerator_pow_apply]
  apply Prod.ext
  · exact (affineCyclicFillingDiscRepresentation_apply_eq_pow P g q.1).symm
  · change (D.actionData.fiberGenerator ^
        (Multiplicative.toAdd (affineCyclicFillingDegree P g)).val)
        (torusProjection p q.2) =
      torusProjection p
        (@SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul g q.2)
    have h := torusProjection_affineCyclicFillingDeck_smul P g q.2
    rw [affineCyclicFillingFiberRepresentation_apply_eq_pow] at h
    exact h.symm

public theorem affineCyclicRadialFillingDeckAction_continuous
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift) (hLinv : Continuous P.affine.lift.symm) :
    letI := affineCyclicRadialFillingDeckAction P
    ContinuousConstSMul (affineCyclicBoundaryDeckData P).FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) := by
  let _ := affineCyclicRadialFillingDeckAction P
  let centralAction := affineCyclicFillingDeckAction P
  let _ := centralAction
  have hcentral := affineCyclicFillingDeckAction_continuous P hL hLinv
  refine ⟨fun g ↦ ?_⟩
  have hrepresentation :
      D.actionData.representation (affineCyclicFillingDegree P g) =
        D.actionData.diagonalGenerator ^
          (Multiplicative.toAdd (affineCyclicFillingDegree P g)).val := by
    let c := affineCyclicFillingDegree P g
    calc
      D.actionData.representation c =
          D.actionData.representation
            (cyclicGenerator m ^ (Multiplicative.toAdd c).val) := by
        rw [← cyclic_eq_generator_pow c]
      _ = D.actionData.diagonalGenerator ^ (Multiplicative.toAdd c).val := by
        rw [map_pow, D.actionData.representation_generator]
  have hdisc : Continuous fun u : ComplexUnitDisc ↦
      affineCyclicFillingDiscRepresentation P g u := by
    have h := continuous_fst.comp
      ((D.representation_continuous (affineCyclicFillingDegree P g)).comp
        (continuous_id.prodMk
          (show Continuous (fun _ : ComplexUnitDisc ↦ (0 : AdditiveTorus p)) from
            continuous_const)))
    apply h.congr
    intro u
    change (D.actionData.representation (affineCyclicFillingDegree P g)
      (u, (0 : AdditiveTorus p))).1 =
        affineCyclicFillingDiscRepresentation P g u
    rw [hrepresentation, D.actionData.diagonalGenerator_pow_apply]
    exact (affineCyclicFillingDiscRepresentation_apply_eq_pow P g u).symm
  exact hdisc.comp continuous_fst |>.prodMk
    (hcentral.continuous_const_smul g |>.comp continuous_snd)

public theorem affineCyclicRadialFillingDeckAction_disjoint
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift) (hLinv : Continuous P.affine.lift.symm)
    (q : ComplexUnitDisc × ComplexTwoSpace) :
    letI := affineCyclicRadialFillingDeckAction P
    ∃ U ∈ 𝓝 q, ∀ g : (affineCyclicBoundaryDeckData P).FillingDeck,
      ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  let _ := affineCyclicRadialFillingDeckAction P
  let centralAction := affineCyclicFillingDeckAction P
  let _ := centralAction
  let hc := affineCyclicFilling_isQuotientCoveringMap P hL hLinv
  obtain ⟨U, hU, hdisjoint⟩ := hc.disjoint q.2
  refine ⟨Set.univ ×ˢ U, by
    simpa only [Prod.eta] using
      prod_mem_nhds (show Set.univ ∈ 𝓝 q.1 by simp) hU, ?_⟩
  rintro g ⟨v, hvImage, hvU⟩
  rcases hvImage with ⟨w, hwU, rfl⟩
  apply hdisjoint g
  refine ⟨@SMul.smul _ _ centralAction.toSMul g w.2,
    ⟨w.2, hwU.2, rfl⟩, hvU.2⟩

public theorem affineCyclicRadialFillingProjection_eq_iff_exists_deck
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (x y : ComplexUnitDisc × ComplexTwoSpace) :
    letI := affineCyclicRadialFillingDeckAction P
    affineCyclicRadialFillingProjection P x =
        affineCyclicRadialFillingProjection P y ↔
      ∃ g : (affineCyclicBoundaryDeckData P).FillingDeck, g • y = x := by
  let _ := affineCyclicRadialFillingDeckAction P
  let centralAction := affineCyclicFillingDeckAction P
  let _ := centralAction
  constructor
  · intro hq
    have horbit := Quotient.exact hq
    change ∃ c : FiniteCyclic m,
      D.actionData.representation c (y.1, torusProjection p y.2) =
        (x.1, torusProjection p x.2) at horbit
    obtain ⟨c, hc⟩ := horbit
    let k := (Multiplicative.toAdd c).val
    have hrepresentation :
        D.actionData.representation c = D.actionData.diagonalGenerator ^ k := by
      calc
        D.actionData.representation c =
            D.actionData.representation (cyclicGenerator m ^ k) := by
          rw [← cyclic_eq_generator_pow c]
        _ = D.actionData.diagonalGenerator ^ k := by
          rw [map_pow, D.actionData.representation_generator]
    rw [hrepresentation, D.actionData.diagonalGenerator_pow_apply] at hc
    have hfirst := congrArg Prod.fst hc
    have hsecond := congrArg Prod.snd hc
    let gen := (affineCyclicBoundaryDeckData P).fillingDeckMap
      (affineCyclicBoundaryDeckData P).meridian
    let g0 := gen ^ k
    have hdegreeGen : affineCyclicFillingDegree P gen = cyclicGenerator m := by
      dsimp [gen]
      rw [affineCyclicFillingDegree_fillingDeckMap]
      simp [affineCyclicBoundaryDeckData, canonicalCyclicAffineBoundaryDeckData,
        canonicalCyclicAffineMeridian, cyclicGenerator]
    have hdegree0 : affineCyclicFillingDegree P g0 = c := by
      dsimp [g0]
      rw [map_pow, hdegreeGen]
      exact (cyclic_eq_generator_pow c).symm
    have htorus0 : torusProjection p
        (@SMul.smul _ _ centralAction.toSMul g0 y.2) = torusProjection p x.2 := by
      have ht := torusProjection_affineCyclicFillingDeck_smul P g0 y.2
      change torusProjection p (@SMul.smul _ _ centralAction.toSMul g0 y.2) =
        affineCyclicFillingFiberRepresentation P g0 (torusProjection p y.2) at ht
      rw [affineCyclicFillingFiberRepresentation_apply_eq_pow, hdegree0] at ht
      exact ht.trans hsecond
    obtain ⟨a, ha⟩ := torusProjection_eq_implies_period_add x.2
      (@SMul.smul _ _ centralAction.toSMul g0 y.2) htorus0.symm
    let g := affineCyclicKernelIncl P a * g0
    refine ⟨g, ?_⟩
    apply Prod.ext
    · change affineCyclicFillingDiscRepresentation P g y.1 = x.1
      have hdegreeIncl : affineCyclicFillingDegree P (affineCyclicKernelIncl P a) = 1 := by
        rw [affineCyclicKernelIncl,
          affineCyclicFillingDegree_fillingDeckMap]
        simp [affineCyclicBoundaryDeckData, canonicalCyclicAffineBoundaryDeckData,
          canonicalCyclicAffineTranslation]
      have hdegree : affineCyclicFillingDegree P g = c := by
        dsimp [g]
        rw [map_mul, hdegreeIncl, one_mul, hdegree0]
      rw [affineCyclicFillingDiscRepresentation_apply_eq_pow, hdegree]
      exact hfirst
    · change @SMul.smul _ _ centralAction.toSMul g y.2 = x.2
      dsimp [g]
      change affineCyclicFillingDeckRepresentation P
        (affineCyclicKernelIncl P a * g0) y.2 = x.2
      rw [map_mul]
      change @SMul.smul _ _ centralAction.toSMul (affineCyclicKernelIncl P a)
        (@SMul.smul _ _ centralAction.toSMul g0 y.2) = x.2
      have hk := affineCyclicKernelIncl_smul P a
        (@SMul.smul _ _ centralAction.toSMul g0 y.2)
      change @SMul.smul _ _ centralAction.toSMul (affineCyclicKernelIncl P a)
        (@SMul.smul _ _ centralAction.toSMul g0 y.2) =
          periodVector p a + @SMul.smul _ _ centralAction.toSMul g0 y.2 at hk
      rw [hk]
      exact ha
  · rintro ⟨g, rfl⟩
    exact affineCyclicRadialFillingProjection_smul P g y

public theorem affineCyclicRadialFilling_isQuotientCoveringMap
    (P : AffineCyclicCentralFiberPresentationData m p D)
    (hL : Continuous P.affine.lift) (hLinv : Continuous P.affine.lift.symm) :
    letI := affineCyclicRadialFillingDeckAction P
    IsQuotientCoveringMap (affineCyclicRadialFillingProjection P)
      (affineCyclicBoundaryDeckData P).FillingDeck := by
  let _ := affineCyclicRadialFillingDeckAction P
  refine
    { toIsQuotientMap :=
        (affineCyclicRadialFillingProjection_isOpenQuotientMap P).isQuotientMap
      continuous_const_smul :=
        (affineCyclicRadialFillingDeckAction_continuous P hL hLinv).continuous_const_smul
      apply_eq_iff_mem_orbit := ?_
      disjoint := affineCyclicRadialFillingDeckAction_disjoint P hL hLinv }
  intro x y
  rw [affineCyclicRadialFillingProjection_eq_iff_exists_deck]
  rfl

end EstablishedAffineCyclicQuotientHomology
end SphereSixComplex.Topology.PaperMultipleFiberHOneTopology

end

end
