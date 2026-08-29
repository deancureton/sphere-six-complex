module

public import SphereSixComplex.Topology.CircleMappingTorusOpenCoverHomotopyEquivalences
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section

noncomputable section

open Set ContinuousMap CategoryTheory TopologicalSpace
open scoped FundamentalGroupoid

namespace SphereSixComplex

theorem pathConnectedSpace_circleMappingTorus_comparison
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F] (phi : F ≃ₜ F) :
    PathConnectedSpace (CircleMappingTorus phi) := by
  let _ : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (𝕜 := ℝ) 0 1).isPathConnected ⟨0, by simp⟩)
  let _ : PathConnectedSpace (Unit × unitInterval × F) := inferInstance
  change PathConnectedSpace
    (Quotient (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi)))
  infer_instance

def quarterParam (s : unitInterval) : unitInterval :=
  ⟨(s : ℝ) / 4, by
    constructor
    · linarith [s.2.1]
    · linarith [s.2.2]⟩

def middleParam (s : unitInterval) : unitInterval :=
  ⟨1 / 4 + (s : ℝ) / 2, by
    constructor
    · linarith [s.2.1]
    · linarith [s.2.2]⟩

def upperParam (s : unitInterval) : unitInterval :=
  ⟨3 / 4 + (s : ℝ) / 4, by
    constructor
    · linarith [s.2.1]
    · linarith [s.2.2]⟩

@[simp] theorem quarterParam_zero : quarterParam 0 = 0 := by ext; norm_num [quarterParam]

@[simp] theorem quarterParam_one : quarterParam 1 = uQuarter := by
  ext
  norm_num [quarterParam, uQuarter]

@[simp] theorem middleParam_zero : middleParam 0 = uQuarter := by
  ext
  norm_num [middleParam, uQuarter]

@[simp] theorem middleParam_one : middleParam 1 = uThreeQuarters := by
  ext
  norm_num [middleParam, uThreeQuarters]

@[simp] theorem upperParam_zero : upperParam 0 = uThreeQuarters := by
  ext
  norm_num [upperParam, uThreeQuarters]

@[simp] theorem upperParam_one : upperParam 1 = 1 := by ext; norm_num [upperParam]

theorem continuous_quarterParam : Continuous quarterParam := by
  apply Continuous.subtype_mk
  fun_prop

theorem continuous_middleParam : Continuous middleParam := by
  apply Continuous.subtype_mk
  fun_prop

theorem continuous_upperParam : Continuous upperParam := by
  apply Continuous.subtype_mk
  fun_prop

def quarterParamPath : Path (0 : unitInterval) uQuarter where
  toFun := quarterParam
  continuous_toFun := continuous_quarterParam
  source' := by ext; norm_num [quarterParam]
  target' := by ext; norm_num [quarterParam, uQuarter]

def middleParamPath : Path uQuarter uThreeQuarters where
  toFun := middleParam
  continuous_toFun := continuous_middleParam
  source' := by ext; norm_num [middleParam, uQuarter]
  target' := by ext; norm_num [middleParam, uThreeQuarters]

def upperParamPath : Path uThreeQuarters (1 : unitInterval) where
  toFun := upperParam
  continuous_toFun := continuous_upperParam
  source' := by ext; norm_num [upperParam, uThreeQuarters]
  target' := by ext; norm_num [upperParam]

theorem quarterParam_mem_vertexBand (s : unitInterval) :
    quarterParam s ∈ vertexBand := by
  left
  dsimp [quarterParam]
  linarith [s.2.2]

theorem middleParam_mem_edgeBand (s : unitInterval) :
    middleParam s ∈ edgeBand := by
  constructor <;> dsimp [middleParam] <;> linarith [s.2.1, s.2.2]

theorem upperParam_mem_vertexBand (s : unitInterval) :
    upperParam s ∈ vertexBand := by
  right
  dsimp [upperParam]
  linarith [s.2.1]

def circleMappingTorusLowCollarPath
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path (vertexFiberInclusion (fun _ : Unit ↦ phi) x)
      (vertexLowPt (fun _ : Unit ↦ phi) () x) where
  toFun s := pieceMk (fun _ : Unit ↦ phi) vertexBand
    ⟨((), quarterParam s, x), quarterParam_mem_vertexBand s⟩
  continuous_toFun := (continuous_pieceMk (fun _ : Unit ↦ phi) vertexBand).comp <|
    Continuous.subtype_mk
      (continuous_const.prodMk (continuous_quarterParam.prodMk continuous_const)) _
  source' := by
    apply Subtype.ext
    change bouquetMk (fun _ : Unit ↦ phi) ((), quarterParam 0, x) =
      bouquetMk (fun _ : Unit ↦ phi) ((), 0, x)
    rw [quarterParam_zero]
  target' := by
    apply Subtype.ext
    change bouquetMk (fun _ : Unit ↦ phi) ((), quarterParam 1, x) =
      bouquetMk (fun _ : Unit ↦ phi) ((), uQuarter, x)
    rw [quarterParam_one]

def circleMappingTorusMiddleCollarPath
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path (edgeLowPt (fun _ : Unit ↦ phi) () x)
      (edgeHighPt (fun _ : Unit ↦ phi) () x) where
  toFun s := pieceMk (fun _ : Unit ↦ phi) edgeBand
    ⟨((), middleParam s, x), middleParam_mem_edgeBand s⟩
  continuous_toFun := (continuous_pieceMk (fun _ : Unit ↦ phi) edgeBand).comp <|
    Continuous.subtype_mk
      (continuous_const.prodMk (continuous_middleParam.prodMk continuous_const)) _
  source' := by
    apply Subtype.ext
    change bouquetMk (fun _ : Unit ↦ phi) ((), middleParam 0, x) =
      bouquetMk (fun _ : Unit ↦ phi) ((), uQuarter, x)
    rw [middleParam_zero]
  target' := by
    apply Subtype.ext
    change bouquetMk (fun _ : Unit ↦ phi) ((), middleParam 1, x) =
      bouquetMk (fun _ : Unit ↦ phi) ((), uThreeQuarters, x)
    rw [middleParam_one]

def circleMappingTorusHighCollarPath
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path (vertexHighPt (fun _ : Unit ↦ phi) () x)
      (vertexFiberInclusion (fun _ : Unit ↦ phi) (phi x)) where
  toFun s := pieceMk (fun _ : Unit ↦ phi) vertexBand
    ⟨((), upperParam s, x), upperParam_mem_vertexBand s⟩
  continuous_toFun := (continuous_pieceMk (fun _ : Unit ↦ phi) vertexBand).comp <|
    Continuous.subtype_mk
      (continuous_const.prodMk (continuous_upperParam.prodMk continuous_const)) _
  source' := by
    apply Subtype.ext
    change bouquetMk (fun _ : Unit ↦ phi) ((), upperParam 0, x) =
      bouquetMk (fun _ : Unit ↦ phi) ((), uThreeQuarters, x)
    rw [upperParam_zero]
  target' := by
    apply Subtype.ext
    apply Quotient.sound
    apply Relation.EqvGen.rel
    change finiteBouquetMappingTorusRelation (fun _ : Unit ↦ phi)
      ((), upperParam 1, x) ((), 0, phi x)
    rw [upperParam_one]
    exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)

def vertexPieceInclusion
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    C(↥(vertexPiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def edgePieceInclusion
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    C(↥(edgePiece (fun _ : Unit ↦ phi)), CircleMappingTorus phi) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem circleMappingTorusLowCollarEndpoint_eq
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    vertexPieceInclusion phi (vertexLowPt (fun _ : Unit ↦ phi) () x) =
      edgePieceInclusion phi (edgeLowPt (fun _ : Unit ↦ phi) () x) :=
  rfl

theorem circleMappingTorusHighCollarEndpoint_eq
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    edgePieceInclusion phi (edgeHighPt (fun _ : Unit ↦ phi) () x) =
      vertexPieceInclusion phi (vertexHighPt (fun _ : Unit ↦ phi) () x) :=
  rfl

def circleMappingTorusCollarCompositePath
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path (circleMappingTorusBase phi x) (circleMappingTorusBase phi (phi x)) :=
  ((circleMappingTorusLowCollarPath phi x).map
      (vertexPieceInclusion phi).continuous).trans
    ((((circleMappingTorusMiddleCollarPath phi x).map
      (edgePieceInclusion phi).continuous).cast
        (circleMappingTorusLowCollarEndpoint_eq phi x) rfl).trans
      (((circleMappingTorusHighCollarPath phi x).map
        (vertexPieceInclusion phi).continuous).cast
          (circleMappingTorusHighCollarEndpoint_eq phi x) rfl))

theorem circleMappingTorusEdgePath_collar_decomposition
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x) =
      Path.Homotopic.Quotient.mk (circleMappingTorusCollarCompositePath phi x) := by
  let rho : Path (0 : unitInterval) 1 :=
    quarterParamPath.trans (middleParamPath.trans upperParamPath)
  have hreparam := Path.Homotopy.reparam (circleMappingTorusEdgePath phi x) rho
    rho.continuous rho.source rho.target
  apply Path.Homotopic.Quotient.eq.mpr
  refine (show Path.Homotopic _ _ from ⟨hreparam⟩).trans ?_
  have heq :
      (circleMappingTorusEdgePath phi x).reparam rho rho.continuous rho.source rho.target =
        circleMappingTorusCollarCompositePath phi x := by
    ext s
    simp only [Path.coe_reparam, Function.comp_apply]
    change Quotient.mk _ ((), (rho s, x)) =
      (((circleMappingTorusLowCollarPath phi x).map
          (vertexPieceInclusion phi).continuous).trans
        ((((circleMappingTorusMiddleCollarPath phi x).map
            (edgePieceInclusion phi).continuous).cast
              (circleMappingTorusLowCollarEndpoint_eq phi x) rfl).trans
          (((circleMappingTorusHighCollarPath phi x).map
            (vertexPieceInclusion phi).continuous).cast
              (circleMappingTorusHighCollarEndpoint_eq phi x) rfl))) s
    dsimp [rho]
    by_cases hs : (s : ℝ) ≤ 1 / 2
    · conv_lhs => rw [Path.trans_apply, dite_eq_left hs]
      conv_rhs => rw [Path.trans_apply, dite_eq_left hs]
      rfl
    · conv_lhs => rw [Path.trans_apply, dite_eq_right hs]
      conv_rhs => rw [Path.trans_apply, dite_eq_right hs]
      by_cases hs' : 2 * (s : ℝ) - 1 ≤ 1 / 2
      · conv_lhs => rw [Path.trans_apply, dite_eq_left hs']
        conv_rhs => rw [Path.trans_apply, dite_eq_left hs']
        rfl
      · conv_lhs => rw [Path.trans_apply, dite_eq_right hs']
        conv_rhs => rw [Path.trans_apply, dite_eq_right hs']
        rfl
  rw [heq]

theorem circleMappingTorusLowCollarPath_vertexRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    ((circleMappingTorusLowCollarPath phi x).map
        (vertexRetract (fun _ : Unit ↦ phi)).continuous).cast
          (by simp)
          (by
            simpa using (congrArg (fun g : C(F, F) ↦ g x)
              (vertexRetract_comp_vertexLowPt (fun _ : Unit ↦ phi) ())).symm) =
      Path.refl x := by
  ext s
  change vertexRetract (fun _ : Unit ↦ phi)
      (pieceMk (fun _ : Unit ↦ phi) vertexBand
        ⟨((), quarterParam s, x), quarterParam_mem_vertexBand s⟩) = x
  rw [vertexRetract_pieceMk]
  exact vertexRetractFun_of_lt (fun _ : Unit ↦ phi) (by
    dsimp [quarterParam]
    linarith [s.2.2])

theorem circleMappingTorusMiddleCollarPath_edgeRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    ((circleMappingTorusMiddleCollarPath phi x).map
        (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.continuous).cast
          (by simp)
          (by simp) =
      Path.refl x := by
  ext s
  change (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun
      (pieceMk (fun _ : Unit ↦ phi) edgeBand
        ⟨((), middleParam s, x), middleParam_mem_edgeBand s⟩) = x
  rw [show pieceMk (fun _ : Unit ↦ phi) edgeBand
      ⟨((), middleParam s, x), middleParam_mem_edgeBand s⟩ =
    bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)
      ((), ⟨middleParam s, middleParam_mem_edgeBand s⟩, x) by rfl]
  change
    (fiberBandProdHomotopyEquiv uHalf_mem_edgeOpenBand).invFun
      (unitProdHomeomorph
        ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)).symm
          ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h))
            ((), ⟨middleParam s, middleParam_mem_edgeBand s⟩, x)))) = x
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem circleMappingTorusHighCollarPath_vertexRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    ((circleMappingTorusHighCollarPath phi x).map
        (vertexRetract (fun _ : Unit ↦ phi)).continuous).cast
          (by
            simpa using (congrArg (fun g : C(F, F) ↦ g x)
              (vertexRetract_comp_vertexHighPt (fun _ : Unit ↦ phi) ())).symm)
          (by simp) =
      Path.refl (phi x) := by
  ext s
  change vertexRetract (fun _ : Unit ↦ phi)
      (pieceMk (fun _ : Unit ↦ phi) vertexBand
        ⟨((), upperParam s, x), upperParam_mem_vertexBand s⟩) = phi x
  rw [vertexRetract_pieceMk]
  exact vertexRetractFun_of_gt (fun _ : Unit ↦ phi) (by
    dsimp [upperParam]
    linarith [s.2.1])

theorem singleObjFunctor_map_pathCast
    {X H : Type} [TopologicalSpace X] [Group H]
    (K : FundamentalGroupoid X ⥤ SingleObj H)
    {a b a' b' : X} (p : Path.Homotopic.Quotient a b)
    (ha : a' = a) (hb : b' = b) :
    K.map p = K.map (p.cast ha hb) := by
  cases ha
  cases hb
  apply congrArg K.map
  simp

theorem circleMappingTorusVanKampenLiftFunctor_lowCollar
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) = 1 := by
  have hv := congrArg
    (fun K => K.map (Path.Homotopic.Quotient.mk
      (circleMappingTorusLowCollarPath phi x)))
    (circleMappingTorusVanKampenLiftFunctor_vertex phi x delta f t h)
  change
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) =
      (fundamentalGroupoidBasedFunctor x f).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexRetract (fun _ : Unit ↦ phi)).continuous)) at hv
  rw [show
      (fundamentalGroupoidBasedFunctor x f).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexRetract (fun _ : Unit ↦ phi)).continuous)) = 1 by
        let K := fundamentalGroupoidBasedFunctor x f
        have hp : HEq
            (Path.Homotopic.Quotient.mk
              ((circleMappingTorusLowCollarPath phi x).map
                (vertexRetract (fun _ : Unit ↦ phi)).continuous))
            (Path.Homotopic.Quotient.mk (Path.refl x)) :=
          Path.Homotopic.hpath_hext (fun s ↦ by
            have hfun := congrArg DFunLike.coe
              (circleMappingTorusLowCollarPath_vertexRetract phi x)
            exact congrFun hfun s)
        have hmap : HEq
            (K.map (Path.Homotopic.Quotient.mk
              ((circleMappingTorusLowCollarPath phi x).map
                (vertexRetract (fun _ : Unit ↦ phi)).continuous)))
            (K.map (Path.Homotopic.Quotient.mk (Path.refl x))) := by
          congr
          · exact vertexRetract_vertexFiberInclusion (fun _ : Unit ↦ phi) x
          · exact congrArg (fun g : C(F, F) ↦ g x)
              (vertexRetract_comp_vertexLowPt (fun _ : Unit ↦ phi) ())
        have hid := K.map_id (FundamentalGroupoid.mk x)
        change K.map (Path.Homotopic.Quotient.mk (Path.refl x)) = 1 at hid
        exact (eq_of_heq hmap).trans hid] at hv
  exact hv

theorem circleMappingTorusVanKampenLiftFunctor_middleCollar
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusMiddleCollarPath phi x).map
            (edgePieceInclusion phi).continuous)) =
      circleMappingTorusHighGauge phi x delta f t := by
  have he := congrArg
    (fun K => K.map (Path.Homotopic.Quotient.mk
      (circleMappingTorusMiddleCollarPath phi x)))
    (circleMappingTorusVanKampenLiftFunctor_edge phi x delta f t h)
  change
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusMiddleCollarPath phi x).map
            (edgePieceInclusion phi).continuous)) =
      (circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          (circleMappingTorusMiddleCollarPath phi x)) at he
  rw [show
      (circleMappingTorusStrictifiedEdgeFunctor phi x delta f t h).map
          (Path.Homotopic.Quotient.mk
            (circleMappingTorusMiddleCollarPath phi x)) =
        circleMappingTorusHighGauge phi x delta f t by
      change circleMappingTorusEdgeGauge phi x delta f t h _ *
          (fundamentalGroupoidBasedFunctor x f).map
            (Path.Homotopic.Quotient.mk
              ((circleMappingTorusMiddleCollarPath phi x).map
                (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.continuous)) *
          (circleMappingTorusEdgeGauge phi x delta f t h _) ⁻¹ =
        circleMappingTorusHighGauge phi x delta f t
      rw [circleMappingTorusEdgeGauge_low, circleMappingTorusEdgeGauge_high]
      have hp : HEq
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusMiddleCollarPath phi x).map
              (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.continuous))
          (Path.Homotopic.Quotient.mk (Path.refl x)) :=
        Path.Homotopic.hpath_hext (fun s ↦ by
          have hfun := congrArg DFunLike.coe
            (circleMappingTorusMiddleCollarPath_edgeRetract phi x)
          exact congrFun hfun s)
      let K := fundamentalGroupoidBasedFunctor x f
      have hmap : HEq
          (K.map (Path.Homotopic.Quotient.mk
            ((circleMappingTorusMiddleCollarPath phi x).map
              (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.continuous)))
          (K.map (Path.Homotopic.Quotient.mk (Path.refl x))) := by
        congr
        · exact circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeLowPt phi x
        · exact circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeHighPt phi x
      have hid := K.map_id (FundamentalGroupoid.mk x)
      change K.map (Path.Homotopic.Quotient.mk (Path.refl x)) = 1 at hid
      rw [(eq_of_heq hmap).trans hid]
      group] at he
  exact he

theorem circleMappingTorusVanKampenLiftFunctor_highCollar
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) = 1 := by
  have hv := congrArg
    (fun K => K.map (Path.Homotopic.Quotient.mk
      (circleMappingTorusHighCollarPath phi x)))
    (circleMappingTorusVanKampenLiftFunctor_vertex phi x delta f t h)
  change
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)) =
      (fundamentalGroupoidBasedFunctor x f).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexRetract (fun _ : Unit ↦ phi)).continuous)) at hv
  rw [show
      (fundamentalGroupoidBasedFunctor x f).map
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusHighCollarPath phi x).map
              (vertexRetract (fun _ : Unit ↦ phi)).continuous)) = 1 by
        let K := fundamentalGroupoidBasedFunctor x f
        let p := Path.Homotopic.Quotient.mk
          ((circleMappingTorusHighCollarPath phi x).map
            (vertexRetract (fun _ : Unit ↦ phi)).continuous)
        let hs : phi x = vertexRetract (fun _ : Unit ↦ phi)
            (vertexHighPt (fun _ : Unit ↦ phi) () x) :=
          (congrArg (fun g : C(F, F) ↦ g x)
            (vertexRetract_comp_vertexHighPt (fun _ : Unit ↦ phi) ())).symm
        let ht : phi x = vertexRetract (fun _ : Unit ↦ phi)
            (vertexFiberInclusion (fun _ : Unit ↦ phi) (phi x)) :=
          (vertexRetract_vertexFiberInclusion
            (fun _ : Unit ↦ phi) (phi x)).symm
        have hcast := singleObjFunctor_map_pathCast K p hs ht
        have hp : p.cast hs ht =
            Path.Homotopic.Quotient.mk (Path.refl (phi x)) := by
          change Path.Homotopic.Quotient.mk
              (((circleMappingTorusHighCollarPath phi x).map
                (vertexRetract (fun _ : Unit ↦ phi)).continuous).cast hs ht) = _
          exact congrArg Path.Homotopic.Quotient.mk
            (circleMappingTorusHighCollarPath_vertexRetract phi x)
        rw [hcast, hp]
        have hid := K.map_id (FundamentalGroupoid.mk (phi x))
        change K.map (Path.Homotopic.Quotient.mk (Path.refl (phi x))) = 1 at hid
        exact hid] at hv
  exact hv

theorem circleMappingTorusVanKampenLiftFunctor_delta
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          (delta.map (finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ phi)).continuous)) =
      (fundamentalGroupoidBasedFunctor x f).map
        (Path.Homotopic.Quotient.mk delta) := by
  have hf := congrArg
    (fun K => K.map (Path.Homotopic.Quotient.mk delta))
    (circleMappingTorusVanKampenLiftFunctor_fiber phi x delta f t h)
  exact hf

theorem circleMappingTorusVanKampenLiftFunctor_collarComposite
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          (circleMappingTorusCollarCompositePath phi x)) =
      circleMappingTorusHighGauge phi x delta f t := by
  let K := circleMappingTorusVanKampenLiftFunctor phi x delta f t h
  let plow := Path.Homotopic.Quotient.mk
    ((circleMappingTorusLowCollarPath phi x).map
      (vertexPieceInclusion phi).continuous)
  let pmiddle := Path.Homotopic.Quotient.mk
    ((circleMappingTorusMiddleCollarPath phi x).map
      (edgePieceInclusion phi).continuous)
  let phigh := Path.Homotopic.Quotient.mk
    ((circleMappingTorusHighCollarPath phi x).map
      (vertexPieceInclusion phi).continuous)
  let qmiddle := Path.Homotopic.Quotient.mk
    (((circleMappingTorusMiddleCollarPath phi x).map
      (edgePieceInclusion phi).continuous).cast
        (circleMappingTorusLowCollarEndpoint_eq phi x) rfl)
  let qhigh := Path.Homotopic.Quotient.mk
    (((circleMappingTorusHighCollarPath phi x).map
      (vertexPieceInclusion phi).continuous).cast
        (circleMappingTorusHighCollarEndpoint_eq phi x) rfl)
  have hmiddle := singleObjFunctor_map_pathCast K pmiddle
    (circleMappingTorusLowCollarEndpoint_eq phi x) rfl
  have hhigh := singleObjFunctor_map_pathCast K phigh
    (circleMappingTorusHighCollarEndpoint_eq phi x) rfl
  have hmiddle' : K.map qmiddle = K.map pmiddle := by
    rw [show qmiddle = pmiddle.cast
      (circleMappingTorusLowCollarEndpoint_eq phi x) rfl by
        exact Path.Homotopic.Quotient.mk_cast _ _ _]
    exact hmiddle.symm
  have hhigh' : K.map qhigh = K.map phigh := by
    rw [show qhigh = phigh.cast
      (circleMappingTorusHighCollarEndpoint_eq phi x) rfl by
        exact Path.Homotopic.Quotient.mk_cast _ _ _]
    exact hhigh.symm
  have hcomp : Path.Homotopic.Quotient.mk
        (circleMappingTorusCollarCompositePath phi x) =
      (Path.Homotopic.Quotient.mk
          ((circleMappingTorusLowCollarPath phi x).map
            (vertexPieceInclusion phi).continuous)).trans
        ((Path.Homotopic.Quotient.mk
            (((circleMappingTorusMiddleCollarPath phi x).map
              (edgePieceInclusion phi).continuous).cast
                (circleMappingTorusLowCollarEndpoint_eq phi x) rfl)).trans
          (Path.Homotopic.Quotient.mk
            (((circleMappingTorusHighCollarPath phi x).map
              (vertexPieceInclusion phi).continuous).cast
                (circleMappingTorusHighCollarEndpoint_eq phi x) rfl))) := by
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
        (congrArg
          (Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)).trans
          (Path.Homotopic.Quotient.mk_trans _ _))
  have hmap := congrArg (fun q => K.map q) hcomp
  calc
    _ = K.map
        ((Path.Homotopic.Quotient.mk
            ((circleMappingTorusLowCollarPath phi x).map
              (vertexPieceInclusion phi).continuous)).trans
          ((Path.Homotopic.Quotient.mk
              (((circleMappingTorusMiddleCollarPath phi x).map
                (edgePieceInclusion phi).continuous).cast
                  (circleMappingTorusLowCollarEndpoint_eq phi x) rfl)).trans
            (Path.Homotopic.Quotient.mk
              (((circleMappingTorusHighCollarPath phi x).map
                (vertexPieceInclusion phi).continuous).cast
                  (circleMappingTorusHighCollarEndpoint_eq phi x) rfl)))) := hmap
    _ = _ := by
      have houter := K.map_comp plow (qmiddle.trans qhigh)
      have hinner := K.map_comp qmiddle qhigh
      change K.map (plow.trans (qmiddle.trans qhigh)) = _
      rw [show K.map (plow.trans (qmiddle.trans qhigh)) =
          K.map (qmiddle.trans qhigh) * K.map plow by
            simpa only [FundamentalGroupoid.comp_eq, SingleObj.comp_as_mul] using houter,
        show K.map (qmiddle.trans qhigh) = K.map qhigh * K.map qmiddle by
          simpa only [FundamentalGroupoid.comp_eq, SingleObj.comp_as_mul] using hinner,
        hhigh', hmiddle',
        circleMappingTorusVanKampenLiftFunctor_lowCollar,
        circleMappingTorusVanKampenLiftFunctor_middleCollar,
        circleMappingTorusVanKampenLiftFunctor_highCollar]
      group

theorem circleMappingTorusVanKampenLiftFunctor_edgePath
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)) =
      circleMappingTorusHighGauge phi x delta f t := by
  let K := circleMappingTorusVanKampenLiftFunctor phi x delta f t h
  have hmap := congrArg (fun q => K.map q)
    (circleMappingTorusEdgePath_collar_decomposition phi x)
  exact hmap.trans
    (circleMappingTorusVanKampenLiftFunctor_collarComposite phi x delta f t h)

theorem circleMappingTorusVanKampenLift_meridian
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a)) :
    circleMappingTorusVanKampenLift phi x delta f t h
        (circleMappingTorusMeridian phi x delta) = t := by
  change circleMappingTorusBaseGauge x f *
      (circleMappingTorusVanKampenLiftFunctor phi x delta f t h).map
        (Path.Homotopic.Quotient.mk
          ((circleMappingTorusEdgePath phi x).trans
            (delta.map (finiteBouquetMappingTorusFiberInclusion
              (fun _ : Unit ↦ phi)).continuous))) *
      (circleMappingTorusBaseGauge x f)⁻¹ = t
  let K := circleMappingTorusVanKampenLiftFunctor phi x delta f t h
  let qedge := Path.Homotopic.Quotient.mk (circleMappingTorusEdgePath phi x)
  let qdelta := Path.Homotopic.Quotient.mk
    (delta.map (finiteBouquetMappingTorusFiberInclusion
      (fun _ : Unit ↦ phi)).continuous)
  have hmk := Path.Homotopic.Quotient.mk_trans
    (circleMappingTorusEdgePath phi x)
    (delta.map (finiteBouquetMappingTorusFiberInclusion
      (fun _ : Unit ↦ phi)).continuous)
  have hmap := congrArg (fun q => K.map q) hmk
  have hcomp := K.map_comp qedge qdelta
  have hct := FundamentalGroupoid.comp_eq
    (FundamentalGroupoid.mk
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x))
    (FundamentalGroupoid.mk
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) (phi x)))
    (FundamentalGroupoid.mk
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x))
    qedge qdelta
  have hcompTrans : K.map (qedge.trans qdelta) =
      K.map qdelta * K.map qedge := by
    have hctmap := congrArg (fun q => K.map q) hct
    exact hctmap.symm.trans (by
      simpa only [SingleObj.comp_as_mul] using hcomp)
  have hraw : K.map (Path.Homotopic.Quotient.mk
        ((circleMappingTorusEdgePath phi x).trans
          (delta.map (finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ phi)).continuous))) =
      K.map qdelta * K.map qedge := by
    exact hmap.trans hcompTrans
  have hdeltaMap : K.map qdelta =
      (fundamentalGroupoidBasedFunctor x f).map
        (Path.Homotopic.Quotient.mk delta) := by
    exact circleMappingTorusVanKampenLiftFunctor_delta phi x delta f t h
  have hedgeMap : K.map qedge =
      circleMappingTorusHighGauge phi x delta f t := by
    exact circleMappingTorusVanKampenLiftFunctor_edgePath phi x delta f t h
  rw [hraw, hdeltaMap, hedgeMap]
  let p₀ : FundamentalGroup F x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
  let d : FundamentalGroup F x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x)) ≫
      Path.Homotopic.Quotient.mk delta
  have hdelta :
      (fundamentalGroupoidBasedFunctor x f).map
          (Path.Homotopic.Quotient.mk delta) = (f p₀)⁻¹ * f d := by
    change f (Path.Homotopic.Quotient.mk
          (PathConnectedSpace.somePath x (phi x)) ≫
        Path.Homotopic.Quotient.mk delta ≫
        Groupoid.inv
          (Path.Homotopic.Quotient.mk
            (PathConnectedSpace.somePath x x))) = _
    rw [show Path.Homotopic.Quotient.mk
            (PathConnectedSpace.somePath x (phi x)) ≫
          Path.Homotopic.Quotient.mk delta ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk
              (PathConnectedSpace.somePath x x)) = p₀⁻¹ * d by
          change _ ≫ (_ ≫ Groupoid.inv _) = (_ ≫ _) ≫ Groupoid.inv _
          exact (Category.assoc _ _ _).symm,
      f.map_mul, f.map_inv]
  rw [hdelta]
  change f p₀ * ((f p₀)⁻¹ * f d * ((f d)⁻¹ * t * f p₀)) * (f p₀)⁻¹ = t
  group

def normalizedFundamentalGroupoidBasedFunctor
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (x : X) (f : FundamentalGroup X x →* H) :
    FundamentalGroupoid X ⥤ SingleObj H :=
  singleObjGaugeFunctor (fundamentalGroupoidBasedFunctor x f)
    (fun _ => f (Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath x x)))

theorem normalizedFundamentalGroupoidBasedFunctor_map_base
    {X H : Type} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (x : X) (f : FundamentalGroup X x →* H) (a : FundamentalGroup X x) :
    (normalizedFundamentalGroupoidBasedFunctor x f).map a = f a := by
  change f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)) *
      f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
        Groupoid.inv
          (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))) *
      (f (Path.Homotopic.Quotient.mk
        (PathConnectedSpace.somePath x x)))⁻¹ = f a
  let p₀ : FundamentalGroup X x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
  rw [show Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
        Groupoid.inv
          (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)) =
      p₀⁻¹ * a * p₀ by rfl,
    f.map_mul, f.map_mul, f.map_inv]
  dsimp [p₀]
  group

def circleMappingTorusPairwiseCoverInclusion
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    C(↑(iSup (circleMappingTorusPairwiseCover phi)), CircleMappingTorus phi) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem circleMappingTorusFunctor_ext_of_local_restrictions
    {F H : Type} [TopologicalSpace F] [Group H]
    (phi : F ≃ₜ F)
    (A B : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H)
    (hvertex : FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ A =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙ B)
    (hedge : FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ A =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙ B) :
    A = B := by
  let J := FundamentalGroupoid.map
    (circleMappingTorusPairwiseCoverInclusion phi)
  let Acover : (circleMappingTorusVanKampenCocone phi).pt ⟶
      Grpd.of (SingleObj H) := J ⋙ A
  let Bcover : (circleMappingTorusVanKampenCocone phi).pt ⟶
      Grpd.of (SingleObj H) := J ⋙ B
  let P := circleMappingTorusVanKampenIsColimit phi
  have hvertexTo : FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
      (circleMappingTorusVanKampenCocone phi).ι.app (.single false) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hedgeTo : FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
      (circleMappingTorusVanKampenCocone phi).ι.app (.single true) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hmaps : (circleMappingTorusPairwiseCoverInclusion phi).comp
        (circleMappingTorusToPairwiseCover phi) =
      ContinuousMap.id (CircleMappingTorus phi) := by
    ext y
    rfl
  have htoIncl : FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙
        J = 𝟭 (FundamentalGroupoid (CircleMappingTorus phi)) := by
    rw [← FundamentalGroupoid.map_comp, hmaps, FundamentalGroupoid.map_id]
  have hsingle : ∀ i : Bool,
      (circleMappingTorusVanKampenCocone phi).ι.app (.single i) ⋙ Acover =
        (circleMappingTorusVanKampenCocone phi).ι.app (.single i) ⋙ Bcover := by
    intro i
    cases i
    · rw [← hvertexTo]
      change (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ A =
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ B
      rw [htoIncl, Functor.comp_id]
      exact hvertex
    · rw [← hedgeTo]
      change (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ A =
        (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ B
      rw [htoIncl, Functor.comp_id]
      exact hedge
  have hcover : Acover = Bcover := by
    apply P.hom_ext (f := Acover) (f' := Bcover)
    intro j
    cases j with
    | single i => exact hsingle i
    | pair i j =>
        have hp := congrArg
          (fun L =>
            (CategoryTheory.Pairwise.diagram
              (circleMappingTorusPairwiseCover phi) ⋙
              FundamentalGroupoid.opensToGrpd
                (TopCat.of (CircleMappingTorus phi))).map
                (CategoryTheory.Pairwise.Hom.left i j) ⋙ L)
          (hsingle i)
        have hw := (circleMappingTorusVanKampenCocone phi).w
          (CategoryTheory.Pairwise.Hom.left i j)
        rw [← Functor.assoc, ← Functor.assoc] at hp
        have hwA := congrArg (fun L => L ⋙ Acover) hw
        have hwB := congrArg (fun L => L ⋙ Bcover) hw
        exact hwA.symm.trans (hp.trans hwB)
  have hc := congrArg
    (fun L => FundamentalGroupoid.map
      (circleMappingTorusToPairwiseCover phi) ⋙ L) hcover
  change (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J) ⋙ A =
    (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J) ⋙ B at hc
  rw [← FundamentalGroupoid.map_comp, hmaps, FundamentalGroupoid.map_id,
    Functor.id_comp] at hc
  exact hc

theorem circleMappingTorusFundamentalGroup_hom_ext_of_local_restrictions
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)] (x : F)
    (f g : FundamentalGroup (CircleMappingTorus phi)
      (circleMappingTorusBase phi x) →* H)
    (hvertex : FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor
          (circleMappingTorusBase phi x) f =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor
          (circleMappingTorusBase phi x) g)
    (hedge : FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor
          (circleMappingTorusBase phi x) f =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        normalizedFundamentalGroupoidBasedFunctor
          (circleMappingTorusBase phi x) g) :
    f = g := by
  let A := normalizedFundamentalGroupoidBasedFunctor
    (circleMappingTorusBase phi x) f
  let B := normalizedFundamentalGroupoidBasedFunctor
    (circleMappingTorusBase phi x) g
  let J := FundamentalGroupoid.map
    (circleMappingTorusPairwiseCoverInclusion phi)
  let Acover : (circleMappingTorusVanKampenCocone phi).pt ⟶
      Grpd.of (SingleObj H) := J ⋙ A
  let Bcover : (circleMappingTorusVanKampenCocone phi).pt ⟶
      Grpd.of (SingleObj H) := J ⋙ B
  let P := circleMappingTorusVanKampenIsColimit phi
  have hvertexTo : FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
      (circleMappingTorusVanKampenCocone phi).ι.app (.single false) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hedgeTo : FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) =
      (circleMappingTorusVanKampenCocone phi).ι.app (.single true) := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  have hmaps : (circleMappingTorusPairwiseCoverInclusion phi).comp
        (circleMappingTorusToPairwiseCover phi) =
      ContinuousMap.id (CircleMappingTorus phi) := by
    ext y
    rfl
  have htoIncl : FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙
        J = 𝟭 (FundamentalGroupoid (CircleMappingTorus phi)) := by
    rw [← FundamentalGroupoid.map_comp, hmaps, FundamentalGroupoid.map_id]
  have hsingle : ∀ i : Bool,
      (circleMappingTorusVanKampenCocone phi).ι.app (.single i) ⋙ Acover =
        (circleMappingTorusVanKampenCocone phi).ι.app (.single i) ⋙ Bcover := by
    intro i
    cases i
    · rw [← hvertexTo]
      change (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ A =
        (FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ B
      rw [htoIncl, Functor.comp_id]
      exact hvertex
    · rw [← hedgeTo]
      change (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ A =
        (FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J)) ⋙ B
      rw [htoIncl, Functor.comp_id]
      exact hedge
  have hcover : Acover = Bcover := by
    apply P.hom_ext (f := Acover) (f' := Bcover)
    intro j
    cases j with
    | single i => exact hsingle i
    | pair i j =>
        have hp := congrArg
          (fun L =>
            (CategoryTheory.Pairwise.diagram
              (circleMappingTorusPairwiseCover phi) ⋙
              FundamentalGroupoid.opensToGrpd
                (TopCat.of (CircleMappingTorus phi))).map
                (CategoryTheory.Pairwise.Hom.left i j) ⋙ L)
          (hsingle i)
        have hw := (circleMappingTorusVanKampenCocone phi).w
          (CategoryTheory.Pairwise.Hom.left i j)
        rw [← Functor.assoc, ← Functor.assoc] at hp
        have hwA := congrArg (fun L => L ⋙ Acover) hw
        have hwB := congrArg (fun L => L ⋙ Bcover) hw
        exact hwA.symm.trans (hp.trans hwB)
  have hglobal : A = B := by
    have hc := congrArg
      (fun L => FundamentalGroupoid.map
        (circleMappingTorusToPairwiseCover phi) ⋙ L) hcover
    change (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J) ⋙ A =
      (FundamentalGroupoid.map (circleMappingTorusToPairwiseCover phi) ⋙ J) ⋙ B at hc
    rw [← FundamentalGroupoid.map_comp] at hc
    rw [hmaps, FundamentalGroupoid.map_id, Functor.id_comp] at hc
    exact hc
  apply MonoidHom.ext
  intro a
  have ha := congrArg
    (fun K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H => K.map a)
    hglobal
  simpa only [A, B,
    normalizedFundamentalGroupoidBasedFunctor_map_base] using ha

theorem circleMappingTorusFundamentalGroup_hom_ext_of_compatible_gauges
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)] (x : F)
    (f g : FundamentalGroup (CircleMappingTorus phi)
      (circleMappingTorusBase phi x) →* H)
    (cf cg : FundamentalGroupoid (CircleMappingTorus phi) → H)
    (hcf : cf (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) = 1)
    (hcg : cg (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) = 1)
    (hvertex : FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        singleObjGaugeFunctor
          (normalizedFundamentalGroupoidBasedFunctor
            (circleMappingTorusBase phi x) f) cf =
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
        singleObjGaugeFunctor
          (normalizedFundamentalGroupoidBasedFunctor
            (circleMappingTorusBase phi x) g) cg)
    (hedge : FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        singleObjGaugeFunctor
          (normalizedFundamentalGroupoidBasedFunctor
            (circleMappingTorusBase phi x) f) cf =
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
        singleObjGaugeFunctor
          (normalizedFundamentalGroupoidBasedFunctor
            (circleMappingTorusBase phi x) g) cg) :
    f = g := by
  have hglobal := circleMappingTorusFunctor_ext_of_local_restrictions phi
    (singleObjGaugeFunctor
      (normalizedFundamentalGroupoidBasedFunctor
        (circleMappingTorusBase phi x) f) cf)
    (singleObjGaugeFunctor
      (normalizedFundamentalGroupoidBasedFunctor
        (circleMappingTorusBase phi x) g) cg)
    hvertex hedge
  apply MonoidHom.ext
  intro a
  have ha := congrArg
    (fun K : FundamentalGroupoid (CircleMappingTorus phi) ⥤ SingleObj H => K.map a)
    hglobal
  change cf (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) *
      (normalizedFundamentalGroupoidBasedFunctor
        (circleMappingTorusBase phi x) f).map a *
      (cf (FundamentalGroupoid.mk (circleMappingTorusBase phi x)))⁻¹ =
    cg (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) *
      (normalizedFundamentalGroupoidBasedFunctor
        (circleMappingTorusBase phi x) g).map a *
      (cg (FundamentalGroupoid.mk (circleMappingTorusBase phi x)))⁻¹ at ha
  rw [normalizedFundamentalGroupoidBasedFunctor_map_base,
    normalizedFundamentalGroupoidBasedFunctor_map_base, hcf, hcg] at ha
  simpa using ha

theorem circleMappingTorusCompatibleLocalGauges_of_eq
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) [PathConnectedSpace (CircleMappingTorus phi)] (x : F)
    (f g : FundamentalGroup (CircleMappingTorus phi)
      (circleMappingTorusBase phi x) →* H)
    (hfg : f = g) :
    ∃ cf cg : FundamentalGroupoid (CircleMappingTorus phi) → H,
      cf (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) = 1 ∧
      cg (FundamentalGroupoid.mk (circleMappingTorusBase phi x)) = 1 ∧
      FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          singleObjGaugeFunctor
            (normalizedFundamentalGroupoidBasedFunctor
              (circleMappingTorusBase phi x) f) cf =
        FundamentalGroupoid.map (vertexPieceInclusion phi) ⋙
          singleObjGaugeFunctor
            (normalizedFundamentalGroupoidBasedFunctor
              (circleMappingTorusBase phi x) g) cg ∧
      FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          singleObjGaugeFunctor
            (normalizedFundamentalGroupoidBasedFunctor
              (circleMappingTorusBase phi x) f) cf =
        FundamentalGroupoid.map (edgePieceInclusion phi) ⋙
          singleObjGaugeFunctor
            (normalizedFundamentalGroupoidBasedFunctor
              (circleMappingTorusBase phi x) g) cg := by
  subst g
  exact ⟨fun _ ↦ 1, fun _ ↦ 1, rfl, rfl, rfl, rfl⟩

end SphereSixComplex
