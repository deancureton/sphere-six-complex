module

public import SphereSixComplex.Topology.EstablishedMappingTorusFundamentalGroupCore
public import SphereSixComplex.Topology.MayerVietoris

@[expose] public section

noncomputable section

open CategoryTheory

namespace SphereSixComplex

open IntegralMayerVietoris

theorem fundamentalGroupoid_inv_eq_symm
    {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path.Homotopic.Quotient x y) :
    Groupoid.inv
        (show FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y from p) =
      p.symm := by
  induction p using Quotient.ind
  rfl

theorem pathConnectedSpaceOfHomotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) : PathConnectedSpace X where
  nonempty := ⟨e.invFun (Classical.choice (inferInstance : Nonempty Y))⟩
  joined x z := by
    let h := Classical.choice e.left_inv
    exact ⟨(h.evalAt x).symm.trans
      ((PathConnectedSpace.somePath (e.toFun x) (e.toFun z)).map e.invFun.continuous |>.trans
        (h.evalAt z))⟩

theorem singleObjGaugeFunctor_eq_of_natIso
    {C : Type*} [Category C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (e : A ≅ B) :
    singleObjGaugeFunctor A (fun y ↦ (e.hom.app y : H)) = B := by
  fapply CategoryTheory.Functor.hext
  · intro y
    rfl
  · intro y z p
    apply heq_of_eq
    have h := e.hom.naturality p
    change (e.hom.app z : H) * A.map p = B.map p * (e.hom.app y : H) at h
    change (e.hom.app z : H) * A.map p * (e.hom.app y : H)⁻¹ = B.map p
    rw [h]
    group

theorem singleObjGaugeFunctor_comp
    {C : Type*} [Category C] {H : Type*} [Group H]
    (A : C ⥤ SingleObj H) (a c : C → H) :
    singleObjGaugeFunctor (singleObjGaugeFunctor A a) c =
      singleObjGaugeFunctor A (fun y ↦ c y * a y) := by
  fapply CategoryTheory.Functor.hext
  · intro y
    rfl
  · intro y z p
    apply heq_of_eq
    change c z * (a z * A.map p * (a y)⁻¹) * (c y)⁻¹ =
      (c z * a z) * A.map p * (c y * a y)⁻¹
    group

theorem groupoidSingleObjGaugeEqOfBase
    {C : Type*} [Groupoid C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (b : C)
    (hconn : ∀ y : C, Nonempty (b ⟶ y)) (u : H)
    (hu : ∀ a : b ⟶ b, A.map a ≫ u = u ≫ B.map a) :
    ∃ c : C → H, c b = u ∧ singleObjGaugeFunctor A c = B := by
  let e := groupoidSingleObjNatIsoOfBase A B b hconn u hu
  refine ⟨fun y ↦ (e.hom.app y : H), ?_, singleObjGaugeFunctor_eq_of_natIso A B e⟩
  exact groupoidSingleObjNatIsoOfBase_app_base A B b hconn u hu

theorem singleObjGauges_eq_at_target
    {C : Type*} [Groupoid C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (c d : C → H)
    (hc : singleObjGaugeFunctor A c = B) (hd : singleObjGaugeFunctor A d = B)
    {x y : C} (p : x ⟶ y) (hxy : c x = d x) : c y = d y := by
  have hcmap := congrArg (fun K : C ⥤ SingleObj H ↦ K.map p) hc
  have hdmap := congrArg (fun K : C ⥤ SingleObj H ↦ K.map p) hd
  change c y * A.map p * (c x)⁻¹ = B.map p at hcmap
  change d y * A.map p * (d x)⁻¹ = B.map p at hdmap
  calc
    c y = (c y * A.map p * (c x)⁻¹) * (c x * (A.map p)⁻¹) := by group
    _ = B.map p * (c x * (A.map p)⁻¹) := by rw [hcmap]
    _ = B.map p * (d x * (A.map p)⁻¹) := by rw [hxy]
    _ = (d y * A.map p * (d x)⁻¹) * (d x * (A.map p)⁻¹) := by rw [hdmap]
    _ = d y := by group

def normalizedBasedFunctorExtractionGauge
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K : FundamentalGroupoid X ⥤ SingleObj H) (x : X)
    (y : FundamentalGroupoid X) : H :=
  K.map (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as)) *
    (K.map (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)))⁻¹

@[simp] theorem normalizedBasedFunctorExtractionGauge_base
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K : FundamentalGroupoid X ⥤ SingleObj H) (x : X) :
    normalizedBasedFunctorExtractionGauge K x (FundamentalGroupoid.mk x) = 1 := by
  unfold normalizedBasedFunctorExtractionGauge
  group

theorem normalizedBasedFunctorExtractionGauge_eq
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K : FundamentalGroupoid X ⥤ SingleObj H) (x : X) :
    singleObjGaugeFunctor
        (normalizedFundamentalGroupoidBasedFunctor x
          (K.mapEnd (FundamentalGroupoid.mk x)))
        (normalizedBasedFunctorExtractionGauge K x) = K := by
  fapply CategoryTheory.Functor.hext
  · intro y
    rfl
  · intro y z p
    apply heq_of_eq
    simp only [singleObjGaugeFunctor, normalizedFundamentalGroupoidBasedFunctor,
      fundamentalGroupoidBasedFunctor, normalizedBasedFunctorExtractionGauge]
    let q₀ : FundamentalGroup (X := X) x :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
    let qy : FundamentalGroupoid.mk x ⟶ y :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as)
    let qz : FundamentalGroupoid.mk x ⟶ z :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x z.as)
    change K.map qz * (K.map q₀)⁻¹ *
          (K.map q₀ * K.map (qy ≫ p ≫ Groupoid.inv qz) * (K.map q₀)⁻¹) *
        (K.map qy * (K.map q₀)⁻¹)⁻¹ = K.map p
    rw [K.map_comp, K.map_comp, Groupoid.inv_eq_inv, K.map_inv]
    simp only [SingleObj.comp_as_mul, SingleObj.inv_as_inv]
    group

def normalizedBasedFunctorComparisonGauge
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K L : FundamentalGroupoid X ⥤ SingleObj H) (x : X)
    (y : FundamentalGroupoid X) : H :=
  normalizedBasedFunctorExtractionGauge L x y *
    (normalizedBasedFunctorExtractionGauge K x y)⁻¹

@[simp] theorem normalizedBasedFunctorComparisonGauge_base
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K L : FundamentalGroupoid X ⥤ SingleObj H) (x : X) :
    normalizedBasedFunctorComparisonGauge K L x (FundamentalGroupoid.mk x) = 1 := by
  simp [normalizedBasedFunctorComparisonGauge]

theorem normalizedBasedFunctorComparisonGauge_eq
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (K L : FundamentalGroupoid X ⥤ SingleObj H) (x : X)
    (hbase : K.mapEnd (FundamentalGroupoid.mk x) =
      L.mapEnd (FundamentalGroupoid.mk x)) :
    singleObjGaugeFunctor K (normalizedBasedFunctorComparisonGauge K L x) = L := by
  let a := normalizedBasedFunctorExtractionGauge K x
  let b := normalizedBasedFunctorExtractionGauge L x
  let N := normalizedFundamentalGroupoidBasedFunctor x
    (K.mapEnd (FundamentalGroupoid.mk x))
  have hK : singleObjGaugeFunctor N a = K :=
    normalizedBasedFunctorExtractionGauge_eq K x
  have hL : singleObjGaugeFunctor N b = L := by
    have hL' := normalizedBasedFunctorExtractionGauge_eq L x
    rw [← hbase] at hL'
    exact hL'
  let c := fun y ↦ b y * (a y)⁻¹
  change singleObjGaugeFunctor K c = L
  calc
    singleObjGaugeFunctor K c =
        singleObjGaugeFunctor (singleObjGaugeFunctor N a) c :=
      (congrArg (fun Q ↦ singleObjGaugeFunctor Q c) hK).symm
    _ = singleObjGaugeFunctor N (fun y ↦ c y * a y) :=
      singleObjGaugeFunctor_comp N a c
    _ = singleObjGaugeFunctor N b := by
      congr 1
      funext y
      dsimp [c]
      group
    _ = L := hL

theorem circleMappingTorusVertexRestriction_mapEnd_eq
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (hf : ∀ a : FundamentalGroup F x, q (circleMappingTorusFiberHom phi x a) = f a) :
    (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q).mapEnd
          (FundamentalGroupoid.mk (vertexFiberInclusion (fun _ : Unit ↦ phi) x)) =
      (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
          (circleMappingTorusVanKampenLift phi x delta f t h)).mapEnd
            (FundamentalGroupoid.mk (vertexFiberInclusion (fun _ : Unit ↦ phi) x)) := by
  apply MonoidHom.ext
  intro a
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (vertexPieceHomotopyEquiv (fun _ : Unit ↦ phi)).symm
  obtain ⟨aF, ha⟩ := E.fullyFaithfulFunctor.map_bijective
    (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x) |>.2 a
  change FundamentalGroup F x at aF
  change (FundamentalGroupoid.map
    (vertexFiberInclusion (fun _ : Unit ↦ phi))).map aF = a at ha
  rw [← ha]
  change (normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q).map
      ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map
        ((FundamentalGroupoid.map
          (vertexFiberInclusion (fun _ : Unit ↦ phi))).map aF)) =
    (normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
      (circleMappingTorusVanKampenLift phi x delta f t h)).map
        ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map
          ((FundamentalGroupoid.map
            (vertexFiberInclusion (fun _ : Unit ↦ phi))).map aF))
  rw [fundamentalGroupoid_map_comp_apply]
  have hmap :
      (FundamentalGroupoid.map ((vertexPieceInclusion phi).comp
        (vertexFiberInclusion (fun _ : Unit ↦ phi)))).map aF =
      circleMappingTorusFiberHom phi x aF := by
    induction aF using Quotient.ind
    rfl
  let Q := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let L := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
    (circleMappingTorusVanKampenLift phi x delta f t h)
  have hleft := congrArg (fun p ↦ Q.map p) hmap
  have hright := congrArg (fun p ↦ L.map p) hmap
  have hq : q (circleMappingTorusFiberHom phi x aF) =
      circleMappingTorusVanKampenLift phi x delta f t h
        (circleMappingTorusFiberHom phi x aF) := by
    rw [hf, circleMappingTorusVanKampenLift_fiber]
  exact hleft.trans <|
    (normalizedFundamentalGroupoidBasedFunctor_map_base _ _ _).trans <|
      hq.trans <| (normalizedFundamentalGroupoidBasedFunctor_map_base _ _ _).symm.trans
        hright.symm

theorem circleMappingTorusVertexRestriction_compatibleGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (hf : ∀ a : FundamentalGroup F x, q (circleMappingTorusFiberHom phi x a) = f a) :
    let A := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
      normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
    let B := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
      normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
        (circleMappingTorusVanKampenLift phi x delta f t h)
    let v := FundamentalGroupoid.mk (vertexFiberInclusion (fun _ : Unit ↦ phi) x)
    ∃ c : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H,
      c v = 1 ∧ singleObjGaugeFunctor A c = B := by
  dsimp only
  let _ : PathConnectedSpace ↥(vertexPiece (fun _ : Unit ↦ phi)) :=
    pathConnectedSpaceOfHomotopyEquiv (vertexPieceHomotopyEquiv (fun _ : Unit ↦ phi))
  let A := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
    normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let B := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
    normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
      (circleMappingTorusVanKampenLift phi x delta f t h)
  let v := FundamentalGroupoid.mk (vertexFiberInclusion (fun _ : Unit ↦ phi) x)
  let c := normalizedBasedFunctorComparisonGauge A B v.as
  have hbase : A.mapEnd v = B.mapEnd v :=
    circleMappingTorusVertexRestriction_mapEnd_eq phi x delta q f t h hf
  exact ⟨c, normalizedBasedFunctorComparisonGauge_base A B v.as,
    normalizedBasedFunctorComparisonGauge_eq A B v.as hbase⟩

def lowerHalfParam (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 2, by
    constructor
    · linarith [s.2.1]
    · linarith [s.2.2]⟩

@[simp] theorem lowerHalfParam_zero : lowerHalfParam 0 = 0 := by
  ext
  norm_num [lowerHalfParam]

@[simp] theorem lowerHalfParam_one : lowerHalfParam 1 = uHalf := by
  ext
  norm_num [lowerHalfParam, uHalf]

theorem continuous_lowerHalfParam : Continuous lowerHalfParam := by
  apply Continuous.subtype_mk
  fun_prop

def circleMappingTorusLowerHalfCylinderHomotopy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ContinuousMap.Homotopy
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))
      ((edgePieceInclusion phi).comp (circleMappingTorusEdgePieceHomotopyEquiv phi).toFun) where
  toFun p := Quotient.mk (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
    ((), (lowerHalfParam p.1, p.2))
  continuous_toFun := continuous_quot_mk.comp
    (continuous_const.prodMk
      ((continuous_lowerHalfParam.comp continuous_fst).prodMk continuous_snd))
  map_zero_left y := by rw [lowerHalfParam_zero]; rfl
  map_one_left y := by rw [lowerHalfParam_one]; rfl

def circleMappingTorusLowerHalfPath
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path (circleMappingTorusBase phi x)
      (edgePieceInclusion phi (edgePt (fun _ : Unit ↦ phi) () x)) :=
  (circleMappingTorusLowerHalfCylinderHomotopy phi).evalAt x

theorem circleMappingTorusFiberHom_trans_lowerHalf
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (a : FundamentalGroup F x) :
    circleMappingTorusFiberHom phi x a ≫
        Path.Homotopic.Quotient.mk (circleMappingTorusLowerHalfPath phi x) =
      Path.Homotopic.Quotient.mk (circleMappingTorusLowerHalfPath phi x) ≫
        (FundamentalGroupoid.map (edgePieceInclusion phi)).map
          ((FundamentalGroupoid.map
            (circleMappingTorusEdgePieceHomotopyEquiv phi).toFun).map a) := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso
    (circleMappingTorusLowerHalfCylinderHomotopy phi)).naturality a
  convert h using 1
  all_goals
    induction a using Quotient.ind
    rfl

def circleMappingTorusEdgeLowHomotopyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ContinuousMap.HomotopyEquiv F ↥(edgePiece (fun _ : Unit ↦ phi)) :=
  ((fiberBandProdHomotopyEquiv (F := F) uQuarter_mem_edgeBand).trans
    unitProdHomeomorph.symm.toHomotopyEquiv).trans
      (bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand
        (fun _ h ↦ h)).toHomotopyEquiv

@[simp] theorem circleMappingTorusEdgeLowHomotopyEquiv_toFun
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgeLowHomotopyEquiv phi).toFun x =
      edgeLowPt (fun _ : Unit ↦ phi) () x :=
  rfl

def circleMappingTorusLowCollarCylinderHomotopy
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ContinuousMap.Homotopy
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi))
      ((edgePieceInclusion phi).comp (circleMappingTorusEdgeLowHomotopyEquiv phi).toFun) where
  toFun p := Quotient.mk (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
    ((), (quarterParam p.1, p.2))
  continuous_toFun := continuous_quot_mk.comp
    (continuous_const.prodMk
      ((continuous_quarterParam.comp continuous_fst).prodMk continuous_snd))
  map_zero_left y := by rw [quarterParam_zero]; rfl
  map_one_left y := by rw [quarterParam_one]; rfl

theorem circleMappingTorusFiberHom_trans_lowCollar
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (a : FundamentalGroup F x) :
    circleMappingTorusFiberHom phi x a ≫
        Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous) =
      Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous) ≫
        (FundamentalGroupoid.map (edgePieceInclusion phi)).map
          ((FundamentalGroupoid.map
            (circleMappingTorusEdgeLowHomotopyEquiv phi).toFun).map a) := by
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso
    (circleMappingTorusLowCollarCylinderHomotopy phi)).naturality a
  convert h using 1
  all_goals
    induction a using Quotient.ind
    rfl

theorem circleMappingTorusEdgeRestriction_compatibleGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (hf : ∀ a : FundamentalGroup F x, q (circleMappingTorusFiberHom phi x a) = f a) :
    let A := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
      normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
    let B := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
      normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
        (circleMappingTorusVanKampenLift phi x delta f t h)
    let m := FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)
    let p := Path.Homotopic.Quotient.mk
      ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous)
    ∃ c : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H,
      c m =
          (normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
            (circleMappingTorusVanKampenLift phi x delta f t h)).map p *
          ((normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q).map p)⁻¹ ∧
        singleObjGaugeFunctor A c = B := by
  dsimp only
  let A₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let B₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
    (circleMappingTorusVanKampenLift phi x delta f t h)
  let A := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ A₀
  let B := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ B₀
  let m := FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)
  let p := Path.Homotopic.Quotient.mk
    ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  let u := B₀.map p * (A₀.map p)⁻¹
  let edgeEquiv := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (circleMappingTorusEdgeLowHomotopyEquiv phi)
  let _ : PathConnectedSpace ↥(edgePiece (fun _ : Unit ↦ phi)) :=
    pathConnectedSpaceOfHomotopyEquiv (circleMappingTorusEdgeLowHomotopyEquiv phi).symm
  have hconn : ∀ y : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)),
      Nonempty (m ⟶ y) := fun y ↦
    ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath m.as y.as)⟩
  have hu : ∀ a : m ⟶ m, A.map a ≫ u = u ≫ B.map a := by
    intro a
    obtain ⟨aF, ha⟩ := edgeEquiv.fullyFaithfulFunctor.map_bijective
      (FundamentalGroupoid.mk x) (FundamentalGroupoid.mk x) |>.2 a
    change FundamentalGroup F x at aF
    change (FundamentalGroupoid.map
      (circleMappingTorusEdgeLowHomotopyEquiv phi).toFun).map aF = a at ha
    rw [← ha]
    have hpath := circleMappingTorusFiberHom_trans_lowCollar phi x aF
    have hA := congrArg (fun w ↦ A₀.map w) hpath
    have hB := congrArg (fun w ↦ B₀.map w) hpath
    let e := (FundamentalGroupoid.map (edgePieceInclusion phi)).map
      ((FundamentalGroupoid.map
        (circleMappingTorusEdgeLowHomotopyEquiv phi).toFun).map aF)
    change A₀.map (circleMappingTorusFiberHom phi x aF ≫ p) = A₀.map (p ≫ e) at hA
    change B₀.map (circleMappingTorusFiberHom phi x aF ≫ p) = B₀.map (p ≫ e) at hB
    rw [A₀.map_comp (circleMappingTorusFiberHom phi x aF) p, A₀.map_comp p e] at hA
    rw [B₀.map_comp (circleMappingTorusFiberHom phi x aF) p, B₀.map_comp p e] at hB
    simp only [SingleObj.comp_as_mul] at hA hB
    have hA' : A₀.map p * A₀.map (circleMappingTorusFiberHom phi x aF) =
        A₀.map e * A₀.map p := hA
    have hB' : B₀.map p * B₀.map (circleMappingTorusFiberHom phi x aF) =
        B₀.map e * B₀.map p := hB
    have hbase : A₀.map (circleMappingTorusFiberHom phi x aF) =
        B₀.map (circleMappingTorusFiberHom phi x aF) := by
      dsimp [A₀, B₀]
      rw [normalizedFundamentalGroupoidBasedFunctor_map_base,
        normalizedFundamentalGroupoidBasedFunctor_map_base]
      change q (circleMappingTorusFiberHom phi x aF) =
        circleMappingTorusVanKampenLift phi x delta f t h
          (circleMappingTorusFiberHom phi x aF)
      rw [hf, circleMappingTorusVanKampenLift_fiber]
    change u * A₀.map e = B₀.map e * u
    dsimp [u] at hA' hB' ⊢
    rw [← hbase] at hB'
    have hAe : (A₀.map p)⁻¹ * A₀.map e =
        A₀.map (circleMappingTorusFiberHom phi x aF) * (A₀.map p)⁻¹ := by
      calc
        (A₀.map p)⁻¹ * A₀.map e =
            (A₀.map p)⁻¹ * (A₀.map e * A₀.map p) * (A₀.map p)⁻¹ := by group
        _ = (A₀.map p)⁻¹ *
            (A₀.map p * A₀.map (circleMappingTorusFiberHom phi x aF)) *
              (A₀.map p)⁻¹ := by rw [hA']
        _ = A₀.map (circleMappingTorusFiberHom phi x aF) * (A₀.map p)⁻¹ := by group
    calc
      B₀.map p * (A₀.map p)⁻¹ * A₀.map e =
          B₀.map p *
            (A₀.map (circleMappingTorusFiberHom phi x aF) * (A₀.map p)⁻¹) := by
            rw [mul_assoc, hAe]
      _ = (B₀.map p * A₀.map (circleMappingTorusFiberHom phi x aF)) *
          (A₀.map p)⁻¹ := by rw [mul_assoc]
      _ = (B₀.map e * B₀.map p) * (A₀.map p)⁻¹ := by rw [hB']
      _ = B₀.map e * (B₀.map p * (A₀.map p)⁻¹) := by rw [mul_assoc]
  obtain ⟨c, hc, heq⟩ := groupoidSingleObjGaugeEqOfBase A B m hconn u hu
  exact ⟨c, hc, heq⟩

theorem circleMappingTorusRestrictionGauges_eq_low
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (hcVbase : cV (FundamentalGroupoid.mk
      (vertexFiberInclusion (fun _ : Unit ↦ phi) x)) = 1)
    (hcV : singleObjGaugeFunctor
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q) cV =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
          (circleMappingTorusVanKampenLift phi x delta f t h))
    (hcElow : cE (FundamentalGroupoid.mk
        (edgeLowPt (fun _ : Unit ↦ phi) () x)) =
      (normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
        (circleMappingTorusVanKampenLift phi x delta f t h)).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)) *
      ((normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)))⁻¹) :
    cV (FundamentalGroupoid.mk (vertexLowPt (fun _ : Unit ↦ phi) () x)) =
      cE (FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)) := by
  let A₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let B₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
    (circleMappingTorusVanKampenLift phi x delta f t h)
  let pV := Path.Homotopic.Quotient.mk (circleMappingTorusLowCollarPath phi x)
  let p := Path.Homotopic.Quotient.mk
    ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  have hmap := congrArg
    (fun K : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H ↦
      K.map pV) hcV
  change cV (FundamentalGroupoid.mk (vertexLowPt (fun _ : Unit ↦ phi) () x)) *
        A₀.map p *
          (cV (FundamentalGroupoid.mk
            (vertexFiberInclusion (fun _ : Unit ↦ phi) x)))⁻¹ =
      B₀.map p at hmap
  rw [hcVbase] at hmap
  rw [hcElow]
  calc
    cV (FundamentalGroupoid.mk (vertexLowPt (fun _ : Unit ↦ phi) () x)) =
        B₀.map p * (A₀.map p)⁻¹ := by
          calc
            _ = (cV (FundamentalGroupoid.mk
                  (vertexLowPt (fun _ : Unit ↦ phi) () x)) * A₀.map p) *
                (A₀.map p)⁻¹ := by group
            _ = B₀.map p * (A₀.map p)⁻¹ := by simpa using hmap
    _ = _ := rfl

def circleMappingTorusVertexHighConnector
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F)
    (delta : Path (phi x) x) :
    Path (vertexFiberInclusion (fun _ : Unit ↦ phi) x)
      (vertexHighPt (fun _ : Unit ↦ phi) () x) :=
  (delta.map (vertexFiberInclusion (fun _ : Unit ↦ phi)).continuous).symm.trans
    (circleMappingTorusHighCollarPath phi x).symm

theorem circleMappingTorusFunctor_map_collarComposite
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F)
    (K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H) :
    K.map (Path.Homotopic.Quotient.mk (circleMappingTorusCollarCompositePath phi x)) =
      K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) *
        K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusMiddleCollarPath phi x).map
            (edgePieceInclusion phi).continuous)) *
        K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) := by
  let plow := Path.Homotopic.Quotient.mk
    ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  let pmiddle := Path.Homotopic.Quotient.mk
    ((circleMappingTorusMiddleCollarPath phi x).map (edgePieceInclusion phi).continuous)
  let phigh := Path.Homotopic.Quotient.mk
    ((circleMappingTorusHighCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  let qmiddle := Path.Homotopic.Quotient.mk
    (((circleMappingTorusMiddleCollarPath phi x).map
      (edgePieceInclusion phi).continuous).cast
        (circleMappingTorusLowCollarEndpoint_eq phi x) rfl)
  let qhigh := Path.Homotopic.Quotient.mk
    (((circleMappingTorusHighCollarPath phi x).map
      (vertexPieceInclusion phi).continuous).cast
        (circleMappingTorusHighCollarEndpoint_eq phi x) rfl)
  have hmiddle : K.map qmiddle = K.map pmiddle := by
    rw [show qmiddle = pmiddle.cast
      (circleMappingTorusLowCollarEndpoint_eq phi x) rfl by
        exact Path.Homotopic.Quotient.mk_cast _ _ _]
    exact (singleObjFunctor_map_pathCast K pmiddle
      (circleMappingTorusLowCollarEndpoint_eq phi x) rfl).symm
  have hhigh : K.map qhigh = K.map phigh := by
    rw [show qhigh = phigh.cast
      (circleMappingTorusHighCollarEndpoint_eq phi x) rfl by
        exact Path.Homotopic.Quotient.mk_cast _ _ _]
    exact (singleObjFunctor_map_pathCast K phigh
      (circleMappingTorusHighCollarEndpoint_eq phi x) rfl).symm
  have hcomp : Path.Homotopic.Quotient.mk
        (circleMappingTorusCollarCompositePath phi x) =
      plow.trans (qmiddle.trans qhigh) := by
    calc
      _ = Path.Homotopic.Quotient.mk
          (((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous).trans
            ((((circleMappingTorusMiddleCollarPath phi x).map
                (edgePieceInclusion phi).continuous).cast
                  (circleMappingTorusLowCollarEndpoint_eq phi x) rfl).trans
              (((circleMappingTorusHighCollarPath phi x).map
                (vertexPieceInclusion phi).continuous).cast
                  (circleMappingTorusHighCollarEndpoint_eq phi x) rfl))) := rfl
      _ = _ := (Path.Homotopic.Quotient.mk_trans _ _).trans
        (congrArg plow.trans (Path.Homotopic.Quotient.mk_trans _ _))
  have hmap := congrArg (fun q ↦ K.map q) hcomp
  have houter := K.map_comp plow (qmiddle.trans qhigh)
  have hinner := K.map_comp qmiddle qhigh
  calc
    K.map (Path.Homotopic.Quotient.mk (circleMappingTorusCollarCompositePath phi x)) =
        K.map (plow.trans (qmiddle.trans qhigh)) := hmap
    _ = K.map (qmiddle.trans qhigh) * K.map plow := by
      simpa only [FundamentalGroupoid.comp_eq, SingleObj.comp_as_mul] using houter
    _ = (K.map qhigh * K.map qmiddle) * K.map plow := by
      rw [show K.map (qmiddle.trans qhigh) = K.map qhigh * K.map qmiddle by
        simpa only [FundamentalGroupoid.comp_eq, SingleObj.comp_as_mul] using hinner]
    _ = _ := by rw [hhigh, hmiddle]

theorem circleMappingTorusFunctor_map_edgePath
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F)
    (K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H) :
    K.map (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)) =
      K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) *
        K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusMiddleCollarPath phi x).map
            (edgePieceInclusion phi).continuous)) *
        K.map (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) := by
  have hmap := congrArg (fun p ↦ K.map p)
    (circleMappingTorusEdgePath_collar_decomposition phi x)
  exact hmap.trans (circleMappingTorusFunctor_map_collarComposite phi x K)

theorem circleMappingTorusFunctor_map_vertexDelta
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H) :
    K.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map
      (Path.Homotopic.Quotient.mk
        (delta.map (vertexFiberInclusion (fun _ : Unit ↦ phi)).continuous))) =
      K.map (Path.Homotopic.Quotient.mk
        (delta.map
          (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)).continuous)) := by
  rfl

theorem circleMappingTorusFunctor_map_vertexHighCollar
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F)
    (K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H) :
    K.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map
      (Path.Homotopic.Quotient.mk (circleMappingTorusHighCollarPath phi x))) =
      K.map (Path.Homotopic.Quotient.mk
        ((circleMappingTorusHighCollarPath phi x).map
          (vertexPieceInclusion phi).continuous)) := by
  rfl

theorem circleMappingTorusRestrictionGauges_eq_high
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (ht : q (circleMappingTorusMeridian phi x delta) = t)
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (hcVbase : cV (FundamentalGroupoid.mk
      (vertexFiberInclusion (fun _ : Unit ↦ phi) x)) = 1)
    (hcV : singleObjGaugeFunctor
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q) cV =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
          (circleMappingTorusVanKampenLift phi x delta f t h))
    (hcE : singleObjGaugeFunctor
        (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q) cE =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
          (circleMappingTorusVanKampenLift phi x delta f t h))
    (hcElow : cE (FundamentalGroupoid.mk
        (edgeLowPt (fun _ : Unit ↦ phi) () x)) =
      (normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
        (circleMappingTorusVanKampenLift phi x delta f t h)).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)) *
      ((normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)))⁻¹) :
    cV (FundamentalGroupoid.mk (vertexHighPt (fun _ : Unit ↦ phi) () x)) =
      cE (FundamentalGroupoid.mk (edgeHighPt (fun _ : Unit ↦ phi) () x)) := by
  let A₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let B₀ := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
    (circleMappingTorusVanKampenLift phi x delta f t h)
  let AV := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ A₀
  let BV := FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ B₀
  let AE := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ A₀
  let BE := FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ B₀
  let P := Path.Homotopic.Quotient.mk
    ((circleMappingTorusLowCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  let M := Path.Homotopic.Quotient.mk
    ((circleMappingTorusMiddleCollarPath phi x).map (edgePieceInclusion phi).continuous)
  let U := Path.Homotopic.Quotient.mk
    ((circleMappingTorusHighCollarPath phi x).map (vertexPieceInclusion phi).continuous)
  let D := Path.Homotopic.Quotient.mk
    (delta.map (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)).continuous)
  let dV := Path.Homotopic.Quotient.mk
    (delta.map (vertexFiberInclusion (fun _ : Unit ↦ phi)).continuous)
  let uV := Path.Homotopic.Quotient.mk (circleMappingTorusHighCollarPath phi x)
  let rV := dV.symm.trans uV.symm
  let mE := Path.Homotopic.Quotient.mk (circleMappingTorusMiddleCollarPath phi x)
  have hcVmap := congrArg
    (fun K : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H ↦
      K.map rV) hcV
  have hcEmap := congrArg
    (fun K : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) ⥤ SingleObj H ↦
      K.map mE) hcE
  change cV (FundamentalGroupoid.mk (vertexHighPt (fun _ : Unit ↦ phi) () x)) *
        AV.map rV *
          (cV (FundamentalGroupoid.mk
            (vertexFiberInclusion (fun _ : Unit ↦ phi) x)))⁻¹ =
      BV.map rV at hcVmap
  change cE (FundamentalGroupoid.mk (edgeHighPt (fun _ : Unit ↦ phi) () x)) *
        AE.map mE *
          (cE (FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)))⁻¹ =
      BE.map mE at hcEmap
  rw [hcVbase] at hcVmap
  have hAV : AV.map rV = (A₀.map U)⁻¹ * (A₀.map D)⁻¹ := by
    change AV.map (dV.symm.trans uV.symm) = _
    rw [← FundamentalGroupoid.comp_eq]
    rw [AV.map_comp]
    simp only [SingleObj.comp_as_mul]
    rw [show AV.map uV.symm = (AV.map uV)⁻¹ by
      rw [← fundamentalGroupoid_inv_eq_symm uV, Groupoid.inv_eq_inv, AV.map_inv]
      simp only [SingleObj.inv_as_inv]]
    rw [show AV.map dV.symm = (AV.map dV)⁻¹ by
      rw [← fundamentalGroupoid_inv_eq_symm dV, Groupoid.inv_eq_inv, AV.map_inv]
      simp only [SingleObj.inv_as_inv]]
    rw [show AV.map uV = A₀.map U from
      circleMappingTorusFunctor_map_vertexHighCollar phi x A₀]
    rw [show AV.map dV = A₀.map D from
      circleMappingTorusFunctor_map_vertexDelta phi x delta A₀]
  have hBV : BV.map rV = (B₀.map U)⁻¹ * (B₀.map D)⁻¹ := by
    change BV.map (dV.symm.trans uV.symm) = _
    rw [← FundamentalGroupoid.comp_eq]
    rw [BV.map_comp]
    simp only [SingleObj.comp_as_mul]
    rw [show BV.map uV.symm = (BV.map uV)⁻¹ by
      rw [← fundamentalGroupoid_inv_eq_symm uV, Groupoid.inv_eq_inv, BV.map_inv]
      simp only [SingleObj.inv_as_inv]]
    rw [show BV.map dV.symm = (BV.map dV)⁻¹ by
      rw [← fundamentalGroupoid_inv_eq_symm dV, Groupoid.inv_eq_inv, BV.map_inv]
      simp only [SingleObj.inv_as_inv]]
    rw [show BV.map uV = B₀.map U from
      circleMappingTorusFunctor_map_vertexHighCollar phi x B₀]
    rw [show BV.map dV = B₀.map D from
      circleMappingTorusFunctor_map_vertexDelta phi x delta B₀]
  have hAE : AE.map mE = A₀.map M := rfl
  have hBE : BE.map mE = B₀.map M := rfl
  have hmer : A₀.map (circleMappingTorusMeridian phi x delta) =
      B₀.map (circleMappingTorusMeridian phi x delta) := by
    dsimp [A₀, B₀]
    rw [normalizedFundamentalGroupoidBasedFunctor_map_base,
      normalizedFundamentalGroupoidBasedFunctor_map_base, ht,
      circleMappingTorusVanKampenLift_meridian]
  have hAmer : A₀.map (circleMappingTorusMeridian phi x delta) =
      A₀.map D * (A₀.map U * A₀.map M * A₀.map P) := by
    change A₀.map
      (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x) ≫ D) = _
    rw [A₀.map_comp]
    simp only [SingleObj.comp_as_mul]
    rw [circleMappingTorusFunctor_map_edgePath phi x A₀]
  have hBmer : B₀.map (circleMappingTorusMeridian phi x delta) =
      B₀.map D * (B₀.map U * B₀.map M * B₀.map P) := by
    change B₀.map
      (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x) ≫ D) = _
    rw [B₀.map_comp]
    simp only [SingleObj.comp_as_mul]
    rw [circleMappingTorusFunctor_map_edgePath phi x B₀]
  have hword : A₀.map D * A₀.map U * A₀.map M * A₀.map P =
      B₀.map D * B₀.map U * B₀.map M * B₀.map P := by
    simpa only [mul_assoc] using hAmer.symm.trans (hmer.trans hBmer)
  have hratio : B₀.map M * B₀.map P *
        (A₀.map P)⁻¹ * (A₀.map M)⁻¹ =
      (B₀.map U)⁻¹ * (B₀.map D)⁻¹ *
        A₀.map D * A₀.map U := by
    calc
      _ = (B₀.map U)⁻¹ * (B₀.map D)⁻¹ *
          (B₀.map D * B₀.map U * B₀.map M * B₀.map P) *
            (A₀.map P)⁻¹ * (A₀.map M)⁻¹ := by group
      _ = (B₀.map U)⁻¹ * (B₀.map D)⁻¹ *
          (A₀.map D * A₀.map U * A₀.map M * A₀.map P) *
            (A₀.map P)⁻¹ * (A₀.map M)⁻¹ := by rw [← hword]
      _ = _ := by group
  calc
    cV (FundamentalGroupoid.mk (vertexHighPt (fun _ : Unit ↦ phi) () x)) =
        BV.map rV * (AV.map rV)⁻¹ := by
          calc
            _ = (cV (FundamentalGroupoid.mk
                  (vertexHighPt (fun _ : Unit ↦ phi) () x)) * AV.map rV) *
                (AV.map rV)⁻¹ := by group
            _ = BV.map rV * (AV.map rV)⁻¹ := by simpa using hcVmap
    _ = (B₀.map U)⁻¹ * (B₀.map D)⁻¹ * A₀.map D * A₀.map U := by
      rw [hAV, hBV]
      group
    _ = B₀.map M * B₀.map P * (A₀.map P)⁻¹ * (A₀.map M)⁻¹ := hratio.symm
    _ = B₀.map M *
        cE (FundamentalGroupoid.mk (edgeLowPt (fun _ : Unit ↦ phi) () x)) *
          (A₀.map M)⁻¹ := by
      rw [hcElow]
      change B₀.map M * B₀.map P * (A₀.map P)⁻¹ * (A₀.map M)⁻¹ =
        B₀.map M * (B₀.map P * (A₀.map P)⁻¹) * (A₀.map M)⁻¹
      group
    _ = cE (FundamentalGroupoid.mk (edgeHighPt (fun _ : Unit ↦ phi) () x)) := by
      rw [hAE, hBE] at hcEmap
      rw [← hcEmap]
      group

theorem circleMappingTorusRestrictionGauges_eq_at_overlapTarget
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F)
    (A B : CategoryTheory.Functor
      (FundamentalGroupoid (CircleMappingTorus phi)) (CategoryTheory.SingleObj H))
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (hcV : singleObjGaugeFunctor
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ A) cV =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ B)
    (hcE : singleObjGaugeFunctor
        (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ A) cE =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ B)
    {z y : FundamentalGroupoid
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))}
    (p : z ⟶ y)
    (hz : cV ((FundamentalGroupoid.map
          (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj z) =
      cE ((FundamentalGroupoid.map
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj z)) :
    cV ((FundamentalGroupoid.map
        (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))).obj y) =
      cE ((FundamentalGroupoid.map
        (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))).obj y) := by
  let jV := FundamentalGroupoid.map
    (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
      (edgePiece (fun _ : Unit ↦ phi)))
  let jE := FundamentalGroupoid.map
    (interToRight (vertexPiece (fun _ : Unit ↦ phi))
      (edgePiece (fun _ : Unit ↦ phi)))
  have hV := congrArg
    (fun K : CategoryTheory.Functor
        (FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)))
        (CategoryTheory.SingleObj H) ↦
      K.map (jV.map p)) hcV
  have hE := congrArg
    (fun K : CategoryTheory.Functor
        (FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)))
        (CategoryTheory.SingleObj H) ↦
      K.map (jE.map p)) hcE
  change cV (jV.obj y) * A.map ((FundamentalGroupoid.map
        (vertexPieceInclusion phi)).map (jV.map p)) * (cV (jV.obj z))⁻¹ =
      B.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map (jV.map p)) at hV
  change cE (jE.obj y) * A.map ((FundamentalGroupoid.map
        (edgePieceInclusion phi)).map (jE.map p)) * (cE (jE.obj z))⁻¹ =
      B.map ((FundamentalGroupoid.map (edgePieceInclusion phi)).map (jE.map p)) at hE
  have hAp : A.map ((FundamentalGroupoid.map
        (vertexPieceInclusion phi)).map (jV.map p)) =
      A.map ((FundamentalGroupoid.map
        (edgePieceInclusion phi)).map (jE.map p)) := by
    induction p using Quotient.ind
    rfl
  have hBp : B.map ((FundamentalGroupoid.map
        (vertexPieceInclusion phi)).map (jV.map p)) =
      B.map ((FundamentalGroupoid.map
        (edgePieceInclusion phi)).map (jE.map p)) := by
    induction p using Quotient.ind
    rfl
  calc
    cV (jV.obj y) =
        (cV (jV.obj y) * A.map ((FundamentalGroupoid.map
          (vertexPieceInclusion phi)).map (jV.map p)) * (cV (jV.obj z))⁻¹) *
          (cV (jV.obj z) *
            (A.map ((FundamentalGroupoid.map
              (vertexPieceInclusion phi)).map (jV.map p)))⁻¹) := by group
    _ = B.map ((FundamentalGroupoid.map
          (vertexPieceInclusion phi)).map (jV.map p)) *
        (cV (jV.obj z) *
          (A.map ((FundamentalGroupoid.map
            (vertexPieceInclusion phi)).map (jV.map p)))⁻¹) := by rw [hV]
    _ = B.map ((FundamentalGroupoid.map
          (edgePieceInclusion phi)).map (jE.map p)) *
        (cE (jE.obj z) *
          (A.map ((FundamentalGroupoid.map
            (edgePieceInclusion phi)).map (jE.map p)))⁻¹) := by rw [hAp, hBp, hz]
    _ = cE (jE.obj y) := by rw [← hE]; group

theorem circleMappingTorusRestrictionGauges_eq_on_overlap
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F)
    (A B : CategoryTheory.Functor
      (FundamentalGroupoid (CircleMappingTorus phi)) (CategoryTheory.SingleObj H))
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (hcV : singleObjGaugeFunctor
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ A) cV =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ B)
    (hcE : singleObjGaugeFunctor
        (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ A) cE =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ B)
    (hlow : cV (FundamentalGroupoid.mk
        (vertexLowPt (fun _ : Unit ↦ phi) () x)) =
      cE (FundamentalGroupoid.mk
        (edgeLowPt (fun _ : Unit ↦ phi) () x)))
    (hhigh : cV (FundamentalGroupoid.mk
        (vertexHighPt (fun _ : Unit ↦ phi) () x)) =
      cE (FundamentalGroupoid.mk
        (edgeHighPt (fun _ : Unit ↦ phi) () x)))
    (y : FundamentalGroupoid
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) :
    cV ((FundamentalGroupoid.map
        (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))).obj y) =
      cE ((FundamentalGroupoid.map
        (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))).obj y) := by
  let e := circleMappingTorusOverlapHomotopyEquiv phi
  let r := Classical.choice e.right_inv
  generalize hs : e.invFun y.as = s
  cases s with
  | inl z =>
      let q := (PathConnectedSpace.somePath x z).map
        (e.toFun.comp (sumInlContinuousMap (X := F))).continuous
      let p : Path
          (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x) y.as :=
        (q.cast
          (circleMappingTorusOverlapHomotopyEquiv_toFun_inl phi x).symm
          (congrArg e.toFun hs)).trans (r.evalAt y.as)
      apply circleMappingTorusRestrictionGauges_eq_at_overlapTarget
        phi A B cV cE hcV hcE (Path.Homotopic.Quotient.mk p)
      have hl := congrArg (fun g : C(F, ↥(vertexPiece (fun _ : Unit ↦ phi))) ↦ g x)
        (interToLeft_comp_overlapLowPt (fun _ : Unit ↦ phi) ())
      have hr := congrArg (fun g : C(F, ↥(edgePiece (fun _ : Unit ↦ phi))) ↦ g x)
        (interToRight_comp_overlapLowPt (fun _ : Unit ↦ phi) ())
      change (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))
            (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x) =
        vertexLowPt (fun _ : Unit ↦ phi) () x at hl
      change (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))
            (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x) =
        edgeLowPt (fun _ : Unit ↦ phi) () x at hr
      change cV (FundamentalGroupoid.mk
          ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))
              (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x))) =
        cE (FundamentalGroupoid.mk
          ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))
              (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x)))
      rw [hl, hr]
      exact hlow
  | inr z =>
      let q := (PathConnectedSpace.somePath x z).map
        (e.toFun.comp (sumInrContinuousMap (X := F))).continuous
      let p : Path
          (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x) y.as :=
        (q.cast
          (circleMappingTorusOverlapHomotopyEquiv_toFun_inr phi x).symm
          (congrArg e.toFun hs)).trans (r.evalAt y.as)
      apply circleMappingTorusRestrictionGauges_eq_at_overlapTarget
        phi A B cV cE hcV hcE (Path.Homotopic.Quotient.mk p)
      have hl := congrArg (fun g : C(F, ↥(vertexPiece (fun _ : Unit ↦ phi))) ↦ g x)
        (interToLeft_comp_overlapHighPt (fun _ : Unit ↦ phi) ())
      have hr := congrArg (fun g : C(F, ↥(edgePiece (fun _ : Unit ↦ phi))) ↦ g x)
        (interToRight_comp_overlapHighPt (fun _ : Unit ↦ phi) ())
      change (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))
            (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x) =
        vertexHighPt (fun _ : Unit ↦ phi) () x at hl
      change (interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi)))
            (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x) =
        edgeHighPt (fun _ : Unit ↦ phi) () x at hr
      change cV (FundamentalGroupoid.mk
          ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))
              (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x))) =
        cE (FundamentalGroupoid.mk
          ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))
              (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x)))
      rw [hl, hr]
      exact hhigh

def circleMappingTorusPatchedGauge
    {F H : Type} [TopologicalSpace F]
    (phi : F ≃ₜ F)
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (y : FundamentalGroupoid (CircleMappingTorus phi)) : H :=
  @dite H (y.as ∈ vertexPiece (fun _ : Unit ↦ phi))
    (Classical.propDecidable _) (fun hy ↦
      cV (FundamentalGroupoid.mk ⟨y.as, hy⟩)) (fun hy ↦
      cE (FundamentalGroupoid.mk ⟨y.as, by
      have hcover : y.as ∈ vertexPiece (fun _ : Unit ↦ phi) ∪
          edgePiece (fun _ : Unit ↦ phi) := by
        rw [vertexPiece_union_edgePiece]
        exact Set.mem_univ _
      exact hcover.resolve_left hy⟩))

@[simp] theorem circleMappingTorusPatchedGauge_vertex
    {F H : Type} [TopologicalSpace F]
    (phi : F ≃ₜ F)
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (y : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi))) :
    circleMappingTorusPatchedGauge phi cV cE
        ((FundamentalGroupoid.map (vertexPieceInclusion phi)).obj y) = cV y := by
  rw [circleMappingTorusPatchedGauge]
  have hy : ((FundamentalGroupoid.map (vertexPieceInclusion phi)).obj y).as ∈
      vertexPiece (fun _ : Unit ↦ phi) := y.as.2
  rw [dite_eq_left hy]
  rfl

theorem circleMappingTorusPatchedGauge_edge
    {F H : Type} [TopologicalSpace F]
    (phi : F ≃ₜ F)
    (cV : FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)) → H)
    (cE : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)) → H)
    (hoverlap : ∀ y : FundamentalGroupoid
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)),
      cV ((FundamentalGroupoid.map
          (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj y) =
        cE ((FundamentalGroupoid.map
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj y))
    (y : FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi))) :
    circleMappingTorusPatchedGauge phi cV cE
        ((FundamentalGroupoid.map (edgePieceInclusion phi)).obj y) = cE y := by
  rw [circleMappingTorusPatchedGauge]
  by_cases hy : (y.as : CircleMappingTorus phi) ∈ vertexPiece (fun _ : Unit ↦ phi)
  · have hy' : ((FundamentalGroupoid.map (edgePieceInclusion phi)).obj y).as ∈
        vertexPiece (fun _ : Unit ↦ phi) := hy
    rw [dite_eq_left hy']
    let z : ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)) :=
      ⟨y.as, hy, y.as.2⟩
    have hz := hoverlap (FundamentalGroupoid.mk z)
    exact hz
  · have hy' : ((FundamentalGroupoid.map (edgePieceInclusion phi)).obj y).as ∉
        vertexPiece (fun _ : Unit ↦ phi) := hy
    rw [dite_eq_right hy']
    rfl

theorem circleMappingTorusVanKampenLift_unique
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)]
    (x : F) (delta : Path (phi x) x)
    (q : FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x) →* H)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (hf : ∀ a : FundamentalGroup F x,
      q (circleMappingTorusFiberHom phi x a) = f a)
    (ht : q (circleMappingTorusMeridian phi x delta) = t) :
    q = circleMappingTorusVanKampenLift phi x delta f t h := by
  obtain ⟨cV, hcVbase, hcV⟩ :=
    circleMappingTorusVertexRestriction_compatibleGauge phi x delta q f t h hf
  obtain ⟨cE, hcElow, hcE⟩ :=
    circleMappingTorusEdgeRestriction_compatibleGauge phi x delta q f t h hf
  have hlow := circleMappingTorusRestrictionGauges_eq_low
    phi x delta q f t h cV cE hcVbase hcV hcElow
  have hhigh := circleMappingTorusRestrictionGauges_eq_high
    phi x delta q f t h ht cV cE hcVbase hcV hcE hcElow
  let A := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x) q
  let B := normalizedFundamentalGroupoidBasedFunctor (circleMappingTorusBase phi x)
    (circleMappingTorusVanKampenLift phi x delta f t h)
  let c := circleMappingTorusPatchedGauge phi cV cE
  have hoverlap : ∀ y : FundamentalGroupoid
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)),
      cV ((FundamentalGroupoid.map
          (interToLeft (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj y) =
        cE ((FundamentalGroupoid.map
          (interToRight (vertexPiece (fun _ : Unit ↦ phi))
            (edgePiece (fun _ : Unit ↦ phi)))).obj y) := by
    intro y
    exact circleMappingTorusRestrictionGauges_eq_on_overlap
      phi x A B cV cE hcV hcE hlow hhigh y
  apply circleMappingTorusFundamentalGroup_hom_ext_of_compatible_gauges
    phi x q (circleMappingTorusVanKampenLift phi x delta f t h) c (fun _ ↦ 1)
  · change circleMappingTorusPatchedGauge phi cV cE
        ((FundamentalGroupoid.map (vertexPieceInclusion phi)).obj
          (FundamentalGroupoid.mk
            (vertexFiberInclusion (fun _ : Unit ↦ phi) x))) = 1
    rw [circleMappingTorusPatchedGauge_vertex]
    exact hcVbase
  · rfl
  · fapply CategoryTheory.Functor.hext
    · intro y
      rfl
    · intro y z p
      apply heq_of_eq
      have hv := congrArg
        (fun K : CategoryTheory.Functor
            (FundamentalGroupoid ↥(vertexPiece (fun _ : Unit ↦ phi)))
            (CategoryTheory.SingleObj H) ↦ K.map p) hcV
      change cV z * A.map ((FundamentalGroupoid.map
          (vertexPieceInclusion phi)).map p) * (cV y)⁻¹ =
        B.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map p) at hv
      change circleMappingTorusPatchedGauge phi cV cE
            ((FundamentalGroupoid.map (vertexPieceInclusion phi)).obj z) *
          A.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map p) *
            (circleMappingTorusPatchedGauge phi cV cE
              ((FundamentalGroupoid.map (vertexPieceInclusion phi)).obj y))⁻¹ =
        1 * B.map ((FundamentalGroupoid.map (vertexPieceInclusion phi)).map p) * 1⁻¹
      rw [circleMappingTorusPatchedGauge_vertex,
        circleMappingTorusPatchedGauge_vertex]
      simpa using hv
  · fapply CategoryTheory.Functor.hext
    · intro y
      rfl
    · intro y z p
      apply heq_of_eq
      have he := congrArg
        (fun K : CategoryTheory.Functor
            (FundamentalGroupoid ↥(edgePiece (fun _ : Unit ↦ phi)))
            (CategoryTheory.SingleObj H) ↦ K.map p) hcE
      change cE z * A.map ((FundamentalGroupoid.map
          (edgePieceInclusion phi)).map p) * (cE y)⁻¹ =
        B.map ((FundamentalGroupoid.map (edgePieceInclusion phi)).map p) at he
      change circleMappingTorusPatchedGauge phi cV cE
            ((FundamentalGroupoid.map (edgePieceInclusion phi)).obj z) *
          A.map ((FundamentalGroupoid.map (edgePieceInclusion phi)).map p) *
            (circleMappingTorusPatchedGauge phi cV cE
              ((FundamentalGroupoid.map (edgePieceInclusion phi)).obj y))⁻¹ =
        1 * B.map ((FundamentalGroupoid.map (edgePieceInclusion phi)).map p) * 1⁻¹
      rw [circleMappingTorusPatchedGauge_edge phi cV cE hoverlap,
        circleMappingTorusPatchedGauge_edge phi cV cE hoverlap]
      simpa using he

theorem mappingTorusHNNToFundamentalGroup_rightInverse_proof
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    (mappingTorusHNNToFundamentalGroup phi x delta).comp
        (mappingTorusFundamentalGroupToHNN phi x delta) =
      MonoidHom.id
        (FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x)) := by
  let Q := (mappingTorusHNNToFundamentalGroup phi x delta).comp
    (mappingTorusFundamentalGroupToHNN phi x delta)
  let I := MonoidHom.id
    (FundamentalGroup (CircleMappingTorus phi) (circleMappingTorusBase phi x))
  let f := circleMappingTorusFiberHom phi x
  let t := circleMappingTorusMeridian phi x delta
  let h := circleMappingTorus_conjugate phi x delta
  have hQf : ∀ a : FundamentalGroup F x,
      Q (circleMappingTorusFiberHom phi x a) = f a := by
    intro a
    change mappingTorusHNNToFundamentalGroup phi x delta
        (circleMappingTorusVanKampenLift phi x delta HNNExtension.of HNNExtension.t
          (mappingTorusHNN_vanKampen_relation phi x delta)
          (circleMappingTorusFiberHom phi x a)) =
      circleMappingTorusFiberHom phi x a
    rw [circleMappingTorusVanKampenLift_fiber]
    simp [mappingTorusHNNToFundamentalGroup]
  have hQt : Q (circleMappingTorusMeridian phi x delta) = t := by
    change mappingTorusHNNToFundamentalGroup phi x delta
        (circleMappingTorusVanKampenLift phi x delta HNNExtension.of HNNExtension.t
          (mappingTorusHNN_vanKampen_relation phi x delta)
          (circleMappingTorusMeridian phi x delta)) =
      circleMappingTorusMeridian phi x delta
    rw [circleMappingTorusVanKampenLift_meridian]
    simp [mappingTorusHNNToFundamentalGroup]
  have hIf : ∀ a : FundamentalGroup F x,
      I (circleMappingTorusFiberHom phi x a) = f a := by
    intro a
    rfl
  have hIt : I (circleMappingTorusMeridian phi x delta) = t := rfl
  let _ : PathConnectedSpace (CircleMappingTorus phi) :=
    pathConnectedSpace_circleMappingTorus_comparison phi
  have hQ := circleMappingTorusVanKampenLift_unique
    phi x delta Q f t h hQf hQt
  have hI := circleMappingTorusVanKampenLift_unique
    phi x delta I f t h hIf hIt
  exact hQ.trans hI.symm

theorem mappingTorusHNNToFundamentalGroup_surjective_proof
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    Function.Surjective (mappingTorusHNNToFundamentalGroup phi x delta) := by
  rw [mappingTorusHNNToFundamentalGroup_surjective_iff_rightInverse]
  exact mappingTorusHNNToFundamentalGroup_rightInverse_proof phi x delta

end SphereSixComplex
