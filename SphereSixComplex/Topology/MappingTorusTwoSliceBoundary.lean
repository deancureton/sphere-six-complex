module
public import SphereSixComplex.Topology.FixedLoopSweepWangBoundary
public import SphereSixComplex.Topology.BinaryOpenCoverOrientedRefinementNaturality
/-!
The Wang boundary is the low-quarter fibre class minus the high-quarter fibre class.
Naturality transports this formula through any map preserving the two covers.

The quarter-column formulation was suggested by `RefinedWang.markedConnecting_quarterColumns`
in plby/HopfProblem, commit `9ac8a456b526527837d7082ff775213ca8bc9809`, `Solution.lean`.
The proofs here use this project's existing singular Mayer–Vietoris and Wang APIs.
-/
@[expose] public section
noncomputable section
open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap
namespace SphereSixComplex
public theorem circleMappingTorus_coverBoundary_twoSlices
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus phi)) :
    coverBoundary (fun _ : Unit ↦ phi) n
      ((unionEquiv (fun _ : Unit ↦ phi) (n + 1)).symm x) =
    integralSingularHomologyMap n
      (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand ())
      ((circleMappingTorusWangPresentationOfCover phi n).boundary x) -
    integralSingularHomologyMap n
      (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand ())
      ((circleMappingTorusWangPresentationOfCover phi n).boundary x) := by
  let a := (circleMappingTorusWangPresentationOfCover phi n).boundary x
  have hp : coverWangBoundary (fun _ : Unit ↦ phi) n x =
      ((fun _ ↦ a), fun _ ↦ -a) := by
    apply Prod.ext
    · funext u
      cases u
      rfl
    · have h := coverWangBoundary_snd_eq_neg_fst (fun _ : Unit ↦ phi) n x
      rw [h]
      rfl
  have he := congrArg (overlapEquiv (fun _ : Unit ↦ phi) n) hp
  rw [coverWangBoundary_apply, AddEquiv.apply_symm_apply] at he
  rw [he]
  change overlapLegSum (fun _ : Unit ↦ phi) n ((fun _ ↦ a), fun _ ↦ -a) = _
  simp [overlapLegSum_apply, sub_eq_add_neg, a]

open Topology.CanonicalProductWangBoundaryNaturality BinaryOpenCover
private theorem mappingTorusUnionHomologyIso_apply
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology n
      (vertexPiece (fun _ : Unit ↦ phi) ∪ edgePiece (fun _ : Unit ↦ phi) :
        Set (CircleMappingTorus phi))) :
    ConcreteCategory.hom (opensUnionHomologyIso (mappingTorusVertexOpen phi)
      (mappingTorusEdgeOpen phi) (mappingTorusOpenCover phi) n).hom x =
      unionEquiv (fun _ : Unit ↦ phi) n x := by
  have htop : (TopCat.isoOfHomeo (opensUnionHomeomorph
      (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
      (mappingTorusOpenCover phi))).hom =
      TopCat.ofHom (coverUnionCM (fun _ : Unit ↦ phi)) := by
    ext y
    rfl
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom
    (congrArg (integralHomologyFunctor n).map htop)) x

public theorem circleMappingTorus_boundary_twoSlices
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus phi)) :
    ConcreteCategory.hom ((mappingTorusOpenCoverHomologyComparison phi).boundary n) x =
    ConcreteCategory.hom (opensIntersectionHomologyIso
      (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom
      (integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand ())
        ((circleMappingTorusWangPresentationOfCover phi n).boundary x) -
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand ())
        ((circleMappingTorusWangPresentationOfCover phi n).boundary x)) := by
  rw [← circleMappingTorus_coverBoundary_twoSlices]
  let E := opensUnionHomologyIso (mappingTorusVertexOpen phi)
    (mappingTorusEdgeOpen phi) (mappingTorusOpenCover phi) (n + 1)
  let I := opensIntersectionHomologyIso (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
  let y := (unionEquiv (fun _ : Unit ↦ phi) (n + 1)).symm x
  have hE : ConcreteCategory.hom E.hom y = x := by
    rw [mappingTorusUnionHomologyIso_apply]
    exact AddEquiv.apply_symm_apply _ _
  have hcat : (E.hom ≫ (mappingTorusOpenCoverHomologyComparison phi).boundary n ≫ I.inv) ≫ I.hom =
      E.hom ≫ (mappingTorusOpenCoverHomologyComparison phi).boundary n := by
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := DFunLike.congr_fun (congrArg ConcreteCategory.hom hcat) y
  have hb : coverBoundary (fun _ : Unit ↦ phi) n y =
      ConcreteCategory.hom (E.hom ≫ (mappingTorusOpenCoverHomologyComparison phi).boundary n ≫ I.inv) y := by
    unfold coverBoundary
    rfl
  change ConcreteCategory.hom I.hom
    (ConcreteCategory.hom (E.hom ≫ (mappingTorusOpenCoverHomologyComparison phi).boundary n ≫ I.inv) y) =
      ConcreteCategory.hom ((mappingTorusOpenCoverHomologyComparison phi).boundary n)
        (ConcreteCategory.hom E.hom y) at h
  rw [← hb, hE] at h
  exact h.symm


public def mappingTorusOverlapTransport
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) {Y : TopCat}
    (f : TopCat.of (CircleMappingTorus phi) ⟶ Y) (U V : Opens Y)
    (hU : mappingTorusVertexOpen phi ≤ (Opens.map f).obj U)
    (hV : mappingTorusEdgeOpen phi ≤ (Opens.map f).obj V) (n : ℕ) :
    IntegralSingularHomology n
      (vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi) : Set _) →+
    IntegralSingularHomology n ((Opens.toTopCat Y).obj (U ⊓ V)) :=
  ConcreteCategory.hom
    ((opensIntersectionHomologyIso (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom ≫
      openIntersectionRefinementHomologyMap hU hV n ≫
      openIntersectionPullbackHomologyMap f U V n)

public theorem mappingTorus_boundary_naturality_twoSlices
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) {Y : TopCat}
    (f : TopCat.of (CircleMappingTorus phi) ⟶ Y) (U V : Opens Y) (hcover : U ⊔ V = ⊤)
    (hU : mappingTorusVertexOpen phi ≤ (Opens.map f).obj U)
    (hV : mappingTorusEdgeOpen phi ≤ (Opens.map f).obj V) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus phi)) :
    ConcreteCategory.hom ((openCoverHomologyComparisonOfCover hcover).boundary n)
      (integralSingularHomologyMap (n + 1) f.hom x) =
    mappingTorusOverlapTransport phi f U V hU hV n
      (integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand ())
        ((circleMappingTorusWangPresentationOfCover phi n).boundary x)) -
    mappingTorusOverlapTransport phi f U V hU hV n
      (integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand ())
        ((circleMappingTorusWangPresentationOfCover phi n).boundary x)) := by
  have hp : (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤ := by
    change (Opens.map f).obj (U ⊔ V) = ⊤
    rw [hcover]
    rfl
  have hn := OpenCoverHomologyComparison.boundary_refinement_pullback_naturality
    f U V hU hV (mappingTorusOpenCoverHomologyComparison phi)
    (openCoverHomologyComparisonOfCover hp) (openCoverHomologyComparisonOfCover hcover)
    (openCoverHomologyComparisonOfCover_refinementNaturality hU hV
      (mappingTorusOpenCover phi) hp)
    (openCoverHomologyComparisonOfCover_pullbackNaturality f U V hp hcover) n
  have h := DFunLike.congr_fun (congrArg ConcreteCategory.hom hn) x
  change ConcreteCategory.hom (openIntersectionRefinementHomologyMap hU hV n ≫
      openIntersectionPullbackHomologyMap f U V n)
      (ConcreteCategory.hom ((mappingTorusOpenCoverHomologyComparison phi).boundary n) x) =
    ConcreteCategory.hom ((openCoverHomologyComparisonOfCover hcover).boundary n)
      (integralSingularHomologyMap (n + 1) f.hom x) at h
  rw [circleMappingTorus_boundary_twoSlices] at h
  rw [← h]
  exact map_sub (mappingTorusOverlapTransport phi f U V hU hV n) _ _


public def mappingTorusOverlapMap
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) {Y : TopCat}
    (f : TopCat.of (CircleMappingTorus phi) ⟶ Y) (U V : Opens Y)
    (hU : mappingTorusVertexOpen phi ≤ (Opens.map f).obj U)
    (hV : mappingTorusEdgeOpen phi ≤ (Opens.map f).obj V) :
    C((vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi) : Set _),
      (Opens.toTopCat Y).obj (U ⊓ V)) := by
  refine ⟨fun p ↦ ⟨f p.1, hU p.2.1, hV p.2.2⟩, ?_⟩
  exact (f.hom.continuous.comp continuous_subtype_val).subtype_mk _

public theorem mappingTorusOverlapTransport_eq_map
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) {Y : TopCat}
    (f : TopCat.of (CircleMappingTorus phi) ⟶ Y) (U V : Opens Y)
    (hU : mappingTorusVertexOpen phi ≤ (Opens.map f).obj U)
    (hV : mappingTorusEdgeOpen phi ≤ (Opens.map f).obj V) (n : ℕ) :
    mappingTorusOverlapTransport phi f U V hU hV n =
      integralSingularHomologyMap n (mappingTorusOverlapMap phi f U V hU hV) := by
  ext x
  unfold mappingTorusOverlapTransport opensIntersectionHomologyIso
    openIntersectionRefinementHomologyMap openIntersectionPullbackHomologyMap
  simp only [Functor.mapIso_hom, ← Functor.map_comp]
  rfl

public theorem mappingTorus_boundary_twoSliceMaps
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) {Y : TopCat}
    (f : TopCat.of (CircleMappingTorus phi) ⟶ Y) (U V : Opens Y) (hcover : U ⊔ V = ⊤)
    (hU : mappingTorusVertexOpen phi ≤ (Opens.map f).obj U)
    (hV : mappingTorusEdgeOpen phi ≤ (Opens.map f).obj V) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus phi)) :
    ConcreteCategory.hom ((openCoverHomologyComparisonOfCover hcover).boundary n)
      (integralSingularHomologyMap (n + 1) f.hom x) =
    integralSingularHomologyMap n
      ((mappingTorusOverlapMap phi f U V hU hV).comp
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand ()))
      ((circleMappingTorusWangPresentationOfCover phi n).boundary x) -
    integralSingularHomologyMap n
      ((mappingTorusOverlapMap phi f U V hU hV).comp
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand ()))
      ((circleMappingTorusWangPresentationOfCover phi n).boundary x) := by
  rw [mappingTorus_boundary_naturality_twoSlices phi f U V hcover hU hV,
    mappingTorusOverlapTransport_eq_map, integralSingularHomologyMap_comp_wang,
    integralSingularHomologyMap_comp_wang]


public def identityMappingTorusMapOfLoop
    {F X : Type} [TopologicalSpace F] [LocallyCompactSpace F] [TopologicalSpace X]
    {c : C(F, X)} (p : Path c c) : C(CircleMappingTorus (Homeomorph.refl F), X) where
  toFun := Quotient.lift (fun q : Unit × unitInterval × F ↦ p q.2.1 q.2.2) (by
    intro q r h
    induction h with
    | rel q r h =>
      rcases h with ⟨_, h⟩ | ⟨hq, hr, hf⟩ | ⟨hq, hr, hf⟩
      · rw [h]
      · rw [hq, hr, hf]
      · rw [hq, hr]
        rw [p.target, p.source]
        exact congrArg c hf.symm
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h k => exact h.trans k)
  continuous_toFun := continuous_quot_lift _
    (continuous_eval.comp ((p.continuous.comp
      (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)))

public theorem identityMappingTorusMapOfLoop_cylinder
    {F X : Type} [TopologicalSpace F] [LocallyCompactSpace F] [TopologicalSpace X]
    {c : C(F, X)} (p : Path c c) (t : unitInterval) (x : F) :
    identityMappingTorusMapOfLoop p (torusPt (fun _ : Unit ↦ Homeomorph.refl F) () t x) =
      p t x := rfl


public theorem identityMappingTorusMapOfLoop_vertex
    {F : Type} [TopologicalSpace F] [LocallyCompactSpace F] {Y : TopCat}
    {c : C(F, Y)} (p : Path c c) (U : Opens Y)
    (hU : ∀ t ∈ vertexBand, ∀ x, p t x ∈ U) :
    mappingTorusVertexOpen (Homeomorph.refl F) ≤
      (Opens.map (TopCat.ofHom (identityMappingTorusMapOfLoop p))).obj U := by
  intro z hz
  induction z using Quotient.inductionOn with
  | _ q =>
    exact hU q.2.1 ((mem_bouquetPiece_mk_iff
      (fun _ : Unit ↦ Homeomorph.refl F) vertexBand_ends q).mp hz) q.2.2

public theorem identityMappingTorusMapOfLoop_edge
    {F : Type} [TopologicalSpace F] [LocallyCompactSpace F] {Y : TopCat}
    {c : C(F, Y)} (p : Path c c) (V : Opens Y)
    (hV : ∀ t ∈ edgeBand, ∀ x, p t x ∈ V) :
    mappingTorusEdgeOpen (Homeomorph.refl F) ≤
      (Opens.map (TopCat.ofHom (identityMappingTorusMapOfLoop p))).obj V := by
  intro z hz
  induction z using Quotient.inductionOn with
  | _ q =>
    exact hV q.2.1 ((mem_bouquetPiece_mk_iff
      (fun _ : Unit ↦ Homeomorph.refl F) edgeBand_ends q).mp hz) q.2.2

public def circleLoopOverlapSlice
    {F : Type} [TopologicalSpace F] {Y : TopCat}
    {c : C(F, Y)} (p : Path c c) (U V : Opens Y)
    (hU : ∀ t ∈ vertexBand, ∀ x, p t x ∈ U)
    (hV : ∀ t ∈ edgeBand, ∀ x, p t x ∈ V)
    (t : unitInterval) (ht : t ∈ overlapBand) : C(F, (Opens.toTopCat Y).obj (U ⊓ V)) :=
  ⟨fun x ↦ ⟨p t x, hU t ht.1 x, hV t ht.2 x⟩, (p t).continuous.subtype_mk _⟩

public theorem circleLoop_boundary_twoSlices
    {F : Type} [TopologicalSpace F] [LocallyCompactSpace F] {Y : TopCat}
    {c : C(F, Y)} (p : Path c c) (U V : Opens Y) (hcover : U ⊔ V = ⊤)
    (hU : ∀ t ∈ vertexBand, ∀ x, p t x ∈ U)
    (hV : ∀ t ∈ edgeBand, ∀ x, p t x ∈ V) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus (Homeomorph.refl F))) :
    ConcreteCategory.hom ((openCoverHomologyComparisonOfCover hcover).boundary n)
      (integralSingularHomologyMap (n + 1) (identityMappingTorusMapOfLoop p) x) =
    integralSingularHomologyMap n
      (circleLoopOverlapSlice p U V hU hV uQuarter uQuarter_mem_overlapBand)
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) -
    integralSingularHomologyMap n
      (circleLoopOverlapSlice p U V hU hV uThreeQuarters uThreeQuarters_mem_overlapBand)
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) := by
  exact mappingTorus_boundary_twoSliceMaps (Homeomorph.refl F)
    (TopCat.ofHom (identityMappingTorusMapOfLoop p)) U V hcover
    (identityMappingTorusMapOfLoop_vertex p U hU)
    (identityMappingTorusMapOfLoop_edge p V hV) n x


public def twoSideLoop {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) : Path a a where
  toFun t := if (t : ℝ) ≤ 1 / 3 then p.extend (6 * (t : ℝ))
    else q.extend (3 * (t : ℝ) - 1)
  continuous_toFun := (p.continuous_extend.comp (continuous_const.mul continuous_subtype_val)).if_le
    (q.continuous_extend.comp ((continuous_const.mul continuous_subtype_val).sub continuous_const))
    continuous_subtype_val continuous_const (by
      intro t ht
      change p.extend (6 * (t : ℝ)) = q.extend (3 * (t : ℝ) - 1)
      rw [ht]
      norm_num [p.extend_of_one_le (by norm_num : (1 : ℝ) ≤ 2)])
  source' := by simp
  target' := by
    norm_num
    exact q.extend_of_one_le (by norm_num)

public theorem twoSideLoop_quarter {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) : twoSideLoop p q uQuarter = b := by
  change (if (1 / 4 : ℝ) ≤ 1 / 3 then p.extend (6 * (1 / 4 : ℝ)) else _) = b
  norm_num
  exact p.extend_of_one_le (by norm_num)

public theorem twoSideLoop_threeQuarters {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) : twoSideLoop p q uThreeQuarters = a := by
  change (if (3 / 4 : ℝ) ≤ 1 / 3 then _ else q.extend (3 * (3 / 4 : ℝ) - 1)) = a
  norm_num
  exact q.extend_of_one_le (by norm_num)

public theorem twoSideLoop_mem_vertex {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) (S : Set X) (hp : ∀ t, p t ∈ S)
    (t : unitInterval) (ht : t ∈ vertexBand) : twoSideLoop p q t ∈ S := by
  change (if (t : ℝ) ≤ 1 / 3 then _ else _) ∈ S
  split_ifs with h
  · exact hp _
  · rw [q.extend_of_one_le (by rcases ht with ht | ht <;> linarith)]
    simpa using hp 0

public theorem twoSideLoop_mem_edge {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) (S : Set X) (hq : ∀ t, q t ∈ S)
    (t : unitInterval) (ht : t ∈ edgeBand) : twoSideLoop p q t ∈ S := by
  change (if (t : ℝ) ≤ 1 / 3 then _ else _) ∈ S
  split_ifs with h
  · rw [p.extend_of_one_le (by have := ht.1; linarith)]
    simpa using hq 0
  · exact hq _


public def twoSideLoopReparam (t : unitInterval) : unitInterval :=
  ⟨if (t : ℝ) ≤ 1 / 3 then min (3 * (t : ℝ)) (1 / 2) else min (3 * (t : ℝ) / 2) 1, by
    split_ifs
    · exact ⟨le_min (by have := t.2.1; positivity) (by norm_num), (min_le_right _ _).trans (by norm_num)⟩
    · exact ⟨le_min (by have := t.2.1; positivity) zero_le_one, min_le_right _ _⟩⟩

public theorem twoSideLoopReparam_continuous : Continuous twoSideLoopReparam := by
  apply Continuous.subtype_mk
  exact ((continuous_const.mul continuous_subtype_val).min continuous_const).if_le
    (((continuous_const.mul continuous_subtype_val).div_const 2).min continuous_const)
    continuous_subtype_val continuous_const (by
      intro t ht
      change min (3 * (t : ℝ)) (1 / 2) = min (3 * (t : ℝ) / 2) 1
      rw [ht]
      norm_num)

public theorem twoSideLoopReparam_zero : twoSideLoopReparam 0 = 0 := by
  apply Subtype.ext
  norm_num [twoSideLoopReparam]

public theorem twoSideLoopReparam_one : twoSideLoopReparam 1 = 1 := by
  apply Subtype.ext
  norm_num [twoSideLoopReparam]

public theorem twoSideLoop_eq_reparam {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) :
    twoSideLoop p q = (p.trans q).reparam twoSideLoopReparam twoSideLoopReparam_continuous
      twoSideLoopReparam_zero twoSideLoopReparam_one := by
  ext t
  change (if (t : ℝ) ≤ 1 / 3 then p.extend (6 * (t : ℝ)) else q.extend (3 * (t : ℝ) - 1)) =
    (p.trans q) (twoSideLoopReparam t)
  rw [← Path.extend_apply _ (twoSideLoopReparam t).2]
  change _ = (p.trans q).extend
    (if (t : ℝ) ≤ 1 / 3 then min (3 * (t : ℝ)) (1 / 2) else min (3 * (t : ℝ) / 2) 1)
  split_ifs with h
  · rw [Path.extend_trans_of_le_half _ _ (min_le_right _ _)]
    by_cases ht : (t : ℝ) ≤ 1 / 6
    · rw [min_eq_left (by linarith)]
      congr 1
      ring
    · rw [min_eq_right (by linarith), p.extend_of_one_le (by linarith)]
      norm_num
  · rw [Path.extend_trans_of_half_le _ _ (le_min (by linarith) (by norm_num))]
    by_cases ht : (t : ℝ) ≤ 2 / 3
    · rw [min_eq_left (by linarith)]
      congr 1
      ring
    · rw [min_eq_right (by linarith), q.extend_of_one_le (by linarith)]
      norm_num

public def twoSideLoop_homotopy {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (q : Path b a) : (twoSideLoop p q).Homotopy (p.trans q) := by
  rw [twoSideLoop_eq_reparam]
  exact (Path.Homotopy.reparam (p.trans q) twoSideLoopReparam twoSideLoopReparam_continuous
    twoSideLoopReparam_zero twoSideLoopReparam_one).symm


public def identityMappingTorusMapOfLoop_freeHomotopy
    {F X : Type} [TopologicalSpace F] [LocallyCompactSpace F] [TopologicalSpace X]
    {c d : C(F, X)} {p : Path c c} {q : Path d d}
    (H : p.toContinuousMap.Homotopy q.toContinuousMap)
    (hclosed : ∀ t, H (t, 0) = H (t, 1)) :
    (identityMappingTorusMapOfLoop p).Homotopy (identityMappingTorusMapOfLoop q) where
  toFun z := identityMappingTorusMapOfLoop
    { toFun t := H (z.1, t)
      continuous_toFun := H.continuous.comp (continuous_const.prodMk continuous_id)
      source' := rfl
      target' := (hclosed z.1).symm } z.2
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact continuous_eval.comp
      ((H.continuous.comp (continuous_fst.prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd)))).prodMk
        (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  map_zero_left x := by
    induction x using Quotient.inductionOn with
    | _ z =>
      change H (0, z.2.1) z.2.2 = p z.2.1 z.2.2
      exact DFunLike.congr_fun (H.map_zero_left z.2.1) z.2.2
  map_one_left x := by
    induction x using Quotient.inductionOn with
    | _ z =>
      change H (1, z.2.1) z.2.2 = q z.2.1 z.2.2
      exact DFunLike.congr_fun (H.map_one_left z.2.1) z.2.2

public def identityMappingTorusMapOfLoop_homotopy
    {F X : Type} [TopologicalSpace F] [LocallyCompactSpace F] [TopologicalSpace X]
    {c : C(F, X)} {p q : Path c c} (H : p.Homotopy q) :
    (identityMappingTorusMapOfLoop p).Homotopy (identityMappingTorusMapOfLoop q) :=
  identityMappingTorusMapOfLoop_freeHomotopy H.toHomotopy
    (fun t ↦ (H.source t).trans (H.target t).symm)


public theorem twoSideCircleLoop_boundary
    {F : Type} [TopologicalSpace F] [LocallyCompactSpace F] {Y : TopCat}
    (U V : Opens Y) (hcover : U ⊔ V = ⊤)
    (a b : C(F, (Opens.toTopCat Y).obj (U ⊓ V)))
    (p : Path ((Opens.inclusion' (U ⊓ V)).hom.comp a)
      ((Opens.inclusion' (U ⊓ V)).hom.comp b))
    (q : Path ((Opens.inclusion' (U ⊓ V)).hom.comp b)
      ((Opens.inclusion' (U ⊓ V)).hom.comp a))
    (hp : ∀ t x, p t x ∈ U) (hq : ∀ t x, q t x ∈ V) (n : ℕ)
    (x : IntegralSingularHomology (n + 1) (CircleMappingTorus (Homeomorph.refl F))) :
    ConcreteCategory.hom ((openCoverHomologyComparisonOfCover hcover).boundary n)
      (integralSingularHomologyMap (n + 1) (identityMappingTorusMapOfLoop (p.trans q)) x) =
    integralSingularHomologyMap n b
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) -
    integralSingularHomologyMap n a
      ((circleMappingTorusWangPresentationOfCover (Homeomorph.refl F) n).boundary x) := by
  have hU : ∀ t ∈ vertexBand, ∀ z, twoSideLoop p q t z ∈ U := by
    intro t ht
    exact twoSideLoop_mem_vertex p q {f | ∀ z, f z ∈ U} hp t ht
  have hV : ∀ t ∈ edgeBand, ∀ z, twoSideLoop p q t z ∈ V := by
    intro t ht
    exact twoSideLoop_mem_edge p q {f | ∀ z, f z ∈ V} hq t ht
  have hlow : circleLoopOverlapSlice (twoSideLoop p q) U V hU hV
      uQuarter uQuarter_mem_overlapBand = b := by
    ext1 z
    apply Subtype.ext
    exact DFunLike.congr_fun (twoSideLoop_quarter p q) z
  have hhigh : circleLoopOverlapSlice (twoSideLoop p q) U V hU hV
      uThreeQuarters uThreeQuarters_mem_overlapBand = a := by
    ext1 z
    apply Subtype.ext
    exact DFunLike.congr_fun (twoSideLoop_threeQuarters p q) z
  rw [← integralSingularHomologyMap_eq_of_homotopy (n + 1)
    (identityMappingTorusMapOfLoop_homotopy (twoSideLoop_homotopy p q))]
  rw [circleLoop_boundary_twoSlices _ U V hcover hU hV, hlow, hhigh]

end SphereSixComplex
end
end
