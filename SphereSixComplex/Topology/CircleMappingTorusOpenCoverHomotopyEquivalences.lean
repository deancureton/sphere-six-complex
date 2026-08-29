module

public import SphereSixComplex.Topology.WangHomologyPresentationProof
public import SphereSixComplex.Topology.EstablishedAffineVanKampen
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.IsColimit

@[expose] public section

open Set ContinuousMap CategoryTheory TopologicalSpace

noncomputable section

namespace SphereSixComplex

open IntegralMayerVietoris

def circleMappingTorusVertexOpen
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Opens (CircleMappingTorus phi) :=
  ⟨vertexPiece (fun _ : Unit ↦ phi), isOpen_vertexPiece _⟩

def circleMappingTorusEdgeOpen
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Opens (CircleMappingTorus phi) :=
  ⟨edgePiece (fun _ : Unit ↦ phi), isOpen_edgePiece _⟩

def circleMappingTorusVanKampenCover
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    Set (Opens (CircleMappingTorus phi)) :=
  {U | U ≤ circleMappingTorusVertexOpen phi ∨
    U ≤ circleMappingTorusEdgeOpen phi}

public theorem circleMappingTorusVanKampenCover_covers
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ∀ y : CircleMappingTorus phi, ∃ U : Opens (CircleMappingTorus phi),
      U ∈ circleMappingTorusVanKampenCover phi ∧ y ∈ U := by
  intro y
  by_cases hy : y ∈ vertexPiece (fun _ : Unit ↦ phi)
  · exact ⟨circleMappingTorusVertexOpen phi, Or.inl le_rfl, hy⟩
  · refine ⟨circleMappingTorusEdgeOpen phi, Or.inr le_rfl, ?_⟩
    have h : y ∈ vertexPiece (fun _ : Unit ↦ phi) ∪
        edgePiece (fun _ : Unit ↦ phi) := by
      rw [vertexPiece_union_edgePiece]
      exact Set.mem_univ y
    exact h.resolve_left hy

public theorem circleMappingTorusVanKampenCover_finiteIntersections
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    ∀ s : Finset (Opens (CircleMappingTorus phi)), s.Nonempty →
      (∀ U ∈ s, U ∈ circleMappingTorusVanKampenCover phi) →
      s.inf (fun U : Opens (CircleMappingTorus phi) => U) ∈
        circleMappingTorusVanKampenCover phi := by
  intro s hs hmem
  obtain ⟨U, hU⟩ := hs
  rcases hmem U hU with hUvertex | hUedge
  · exact Or.inl ((Finset.inf_le hU).trans hUvertex)
  · exact Or.inr ((Finset.inf_le hU).trans hUedge)

def singleObjGaugeFunctor {C : Type*} [Category C] {H : Type*} [Group H]
    (B : C ⥤ SingleObj H) (g : C → H) : C ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map {x y} p := g y * B.map p * (g x)⁻¹
  map_id x := by
    rw [B.map_id]
    change g x * 1 * (g x)⁻¹ = 1
    simp
  map_comp {x y z} p q := by
    change g z * B.map (p ≫ q) * (g x)⁻¹ =
      (g z * B.map q * (g y)⁻¹) * (g y * B.map p * (g x)⁻¹)
    rw [B.map_comp]
    change g z * (B.map q * B.map p) * (g x)⁻¹ =
      (g z * B.map q * (g y)⁻¹) * (g y * B.map p * (g x)⁻¹)
    group

def singleObjGaugeNatIso {C : Type*} [Category C] {H : Type*} [Group H]
    (B : C ⥤ SingleObj H) (g : C → H) :
    B ≅ singleObjGaugeFunctor B g :=
  NatIso.ofComponents
    (fun x => Iso.mk (g x) ((g x)⁻¹) (by
      change (g x)⁻¹ * g x = 1
      simp)
      (by
        change g x * (g x)⁻¹ = 1
        simp))
    (by
      intro x y p
      change g y * B.map p =
        (g y * B.map p * (g x)⁻¹) * g x
      group)

def groupoidSingleObjNatIsoOfBase
    {C : Type*} [Groupoid C] {H : Type*} [Group H]
    (A B : C ⥤ SingleObj H) (b : C)
    (hconn : ∀ y : C, Nonempty (b ⟶ y)) (u : H)
    (hu : ∀ a : b ⟶ b, A.map a ≫ u = u ≫ B.map a) :
    A ≅ B := by
  let q : ∀ y : C, b ⟶ y := fun y => Classical.choice (hconn y)
  let c : C → H := fun y => B.map (q y) * u * (A.map (q y))⁻¹
  refine NatIso.ofComponents (fun y => Iso.mk (c y) ((c y)⁻¹) ?_ ?_) ?_
  · change (c y)⁻¹ * c y = 1
    simp
  · change c y * (c y)⁻¹ = 1
    simp
  · intro y z p
    change c z * A.map p = B.map p * c y
    have h := hu (q y ≫ p ≫ Groupoid.inv (q z))
    change u * A.map (q y ≫ p ≫ Groupoid.inv (q z)) =
      B.map (q y ≫ p ≫ Groupoid.inv (q z)) * u at h
    rw [A.map_comp, A.map_comp, B.map_comp, B.map_comp] at h
    simp only [SingleObj.comp_as_mul] at h
    rw [Groupoid.inv_eq_inv, A.map_inv, B.map_inv] at h
    simp only [SingleObj.inv_as_inv] at h
    dsimp [c]
    calc
      B.map (q z) * u * (A.map (q z))⁻¹ * A.map p =
          B.map (q z) *
            (u * (A.map (q z))⁻¹ * A.map p * A.map (q y)) *
              (A.map (q y))⁻¹ := by group
      _ = B.map (q z) *
            ((B.map (q z))⁻¹ * B.map p * B.map (q y) * u) *
              (A.map (q y))⁻¹ := by
            have h' : u * (A.map (q z))⁻¹ * A.map p * A.map (q y) =
                (B.map (q z))⁻¹ * B.map p * B.map (q y) * u := by
              simpa only [mul_assoc] using h
            exact congrArg
              (fun w : H => B.map (q z) * w * (A.map (q y))⁻¹) h'
      _ = B.map p * (B.map (q y) * u * (A.map (q y))⁻¹) := by group

def fundamentalGroupoidBasedFunctor
    {X H : Type*} [TopologicalSpace X] [PathConnectedSpace X] [Group H]
    (x : X) (f : FundamentalGroup X x →* H) :
    FundamentalGroupoid X ⥤ SingleObj H where
  obj _ := SingleObj.star H
  map {y z} p :=
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as) ≫ p ≫
      Groupoid.inv
        (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x z.as)))
  map_id y := by
    rw [SingleObj.id_as_one]
    have h :
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as) ≫ 𝟙 y ≫
            Groupoid.inv
              (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x y.as)) =
          𝟙 (FundamentalGroupoid.mk x) := by simp
    rw [h]
    exact f.map_one
  map_comp {y z w} p q := by
    rw [SingleObj.comp_as_mul]
    change f (_ ≫ (p ≫ q) ≫ _) = f (_ ≫ q ≫ _) * f (_ ≫ p ≫ _)
    rw [← f.map_mul]
    congr 1
    change _ ≫ (p ≫ q) ≫ _ = (_ ≫ p ≫ _) ≫ (_ ≫ q ≫ _)
    simp

def circleMappingTorusHighGauge
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H) : H :=
  (f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x)) ≫
      Path.Homotopic.Quotient.mk delta))⁻¹ * t *
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))

public theorem fundamentalGroupoidBasedFunctor_high_intertwining
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup F x) :
    (fundamentalGroupoidBasedFunctor x f).map a ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map (phi : C(F, F))).map a) := by
  let p₀ : FundamentalGroup F x :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)
  let s : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk (phi x) :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x))
  let e : FundamentalGroupoid.mk (phi x) ⟶ FundamentalGroupoid.mk x :=
    Path.Homotopic.Quotient.mk delta
  let d : FundamentalGroup F x := s ≫ e
  let b : FundamentalGroup F (phi x) :=
    FundamentalGroup.map (phi : C(F, F)) x a
  have hedge :
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x)) =
        p₀⁻¹ * a * p₀ := by
    rfl
  have hhigh :
      s ≫ b ≫ Groupoid.inv s =
        d⁻¹ * mappingTorusMonodromyHom phi x delta a * d := by
    change s ≫ b ≫ Groupoid.inv s =
      (s ≫ e) ≫ (Groupoid.inv e ≫ b ≫ e) ≫ Groupoid.inv (s ≫ e)
    rw [Groupoid.inv_eq_inv e, Groupoid.inv_eq_inv (s ≫ e), IsIso.inv_comp]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [Groupoid.inv_eq_inv]
  change circleMappingTorusHighGauge phi x delta f t *
      f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x) ≫ a ≫
        Groupoid.inv
          (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x x))) =
    f (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x (phi x)) ≫
        (FundamentalGroupoid.map (phi : C(F, F))).map a ≫
          Groupoid.inv
            (Path.Homotopic.Quotient.mk
              (PathConnectedSpace.somePath x (phi x)))) *
      circleMappingTorusHighGauge phi x delta f t
  change circleMappingTorusHighGauge phi x delta f t *
      f (p₀ ≫ a ≫ Groupoid.inv p₀) =
    f (s ≫ b ≫ Groupoid.inv s) * circleMappingTorusHighGauge phi x delta f t
  rw [hedge, hhigh, map_mul, map_mul, map_mul, map_mul]
  dsimp [circleMappingTorusHighGauge, d, p₀, s, e]
  rw [map_inv, ← h a]
  group
  rw [map_zpow]

def sumInrContinuousMap {X : Type*} [TopologicalSpace X] : C(X, X ⊕ X) :=
  ⟨Sum.inr, continuous_inr⟩

def sumFoldContinuousMap {X : Type*} [TopologicalSpace X] : C(X ⊕ X, X) :=
  ⟨Sum.elim id id, continuous_id.sumElim continuous_id⟩

public theorem fundamentalGroupoid_map_comp_apply
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x y : X}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    (FundamentalGroupoid.map g).map ((FundamentalGroupoid.map f).map p) =
      (FundamentalGroupoid.map (g.comp f)).map p := by
  induction p using Quotient.ind with
  | _ p => rfl

public theorem fundamentalGroupoid_sumInr_map_bijective
    {X : Type*} [TopologicalSpace X] (x y : X) :
    Function.Bijective
      ((FundamentalGroupoid.map (sumInrContinuousMap (X := X))).map :
        (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) →
          (FundamentalGroupoid.mk (Sum.inr x) ⟶
            FundamentalGroupoid.mk (Sum.inr y))) := by
  constructor
  · intro p q hpq
    have h := congrArg
      (fun r => (FundamentalGroupoid.map (sumFoldContinuousMap (X := X))).map r) hpq
    induction p using Quotient.ind with
    | _ p =>
      induction q using Quotient.ind with
      | _ q => exact h
  · intro p
    induction p using Quotient.ind with
    | _ p =>
      have hpconn : IsConnected (Set.range p) :=
        isConnected_range p.continuous
      have hprange : Set.range p ⊆ Set.range (Sum.inr : X → X ⊕ X) := by
        rcases Sum.isConnected_iff.mp hpconn with ⟨s, hs, hrange⟩ | ⟨s, hs, hrange⟩
        · exfalso
          have htarget : Sum.inr y ∈ Set.range p := by
            refine ⟨1, ?_⟩
            simpa [sumInrContinuousMap] using p.target
          rw [hrange] at htarget
          obtain ⟨z, -, hz⟩ := htarget
          cases hz
        · rw [hrange]
          exact Set.image_subset_range _ _
      let q : Path x y :=
        { toFun := fun t => Sum.elim id id (p t)
          continuous_toFun := (sumFoldContinuousMap (X := X)).continuous.comp p.continuous
          source' := by
            simpa [sumInrContinuousMap] using
              congrArg (Sum.elim id id) p.source
          target' := by
            simpa [sumInrContinuousMap] using
              congrArg (Sum.elim id id) p.target }
      refine ⟨Path.Homotopic.Quotient.mk q, ?_⟩
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      obtain ⟨z, hz⟩ := hprange ⟨t, rfl⟩
      change Sum.inr (Sum.elim id id (p t)) = p t
      rw [← hz]
      rfl

def unitProdHomeomorph {X : Type} [TopologicalSpace X] : Unit × X ≃ₜ X where
  toFun p := p.2
  invFun x := ((), x)
  left_inv p := by cases p.1; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd
  continuous_invFun := continuous_const.prodMk continuous_id

def disjointOpenUnionHomeomorph
    {X : Type} [TopologicalSpace X] (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hdisj : Disjoint s t) :
    s ⊕ t ≃ₜ ↥(s ∪ t) := by
  classical
  let e : s ⊕ t ≃ ↥(s ∪ t) := (Equiv.Set.union hdisj).symm
  have hleft : e ∘ Sum.inl = fun x : s => (⟨x, Or.inl x.2⟩ : ↥(s ∪ t)) := by
    funext x
    apply Subtype.ext
    rfl
  have hright : e ∘ Sum.inr = fun x : t => (⟨x, Or.inr x.2⟩ : ↥(s ∪ t)) := by
    funext x
    apply Subtype.ext
    rfl
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sum_dom.mpr ⟨by
      rw [hleft]
      exact continuous_subtype_val.subtype_mk _, by
      rw [hright]
      exact continuous_subtype_val.subtype_mk _⟩)
    (isOpenMap_sum.mpr ⟨by
      change IsOpenMap (e ∘ Sum.inl)
      rw [hleft]
      exact hs.isOpenMap_subtype_val.subtype_mk _, by
      change IsOpenMap (e ∘ Sum.inr)
      rw [hright]
      exact ht.isOpenMap_subtype_val.subtype_mk _⟩)

def homotopySum
    {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    {f₀ f₁ : C(X, X')} {g₀ g₁ : C(Y, Y')}
    (hf : Homotopy f₀ f₁) (hg : Homotopy g₀ g₁) :
    Homotopy
      ⟨Sum.map f₀ g₀, f₀.continuous.sumMap g₀.continuous⟩
      ⟨Sum.map f₁ g₁, f₁.continuous.sumMap g₁.continuous⟩ where
  toFun q := match q.2 with
    | Sum.inl x => Sum.inl (hf (q.1, x))
    | Sum.inr y => Sum.inr (hg (q.1, y))
  continuous_toFun := by
    convert ((continuous_inl.comp hf.continuous).sumElim
      (continuous_inr.comp hg.continuous)).comp
        (Homeomorph.prodSumDistrib).continuous using 1
    funext q
    rcases q with ⟨t, z⟩
    cases z <;> rfl
  map_zero_left z := by
    cases z with
    | inl x => exact congrArg Sum.inl (hf.map_zero_left x)
    | inr y => exact congrArg Sum.inr (hg.map_zero_left y)
  map_one_left z := by
    cases z with
    | inl x => exact congrArg Sum.inl (hf.map_one_left x)
    | inr y => exact congrArg Sum.inr (hg.map_one_left y)

def homotopyEquivSum
    {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (e : HomotopyEquiv X X') (f : HomotopyEquiv Y Y') :
    HomotopyEquiv (X ⊕ Y) (X' ⊕ Y') where
  toFun := ⟨Sum.map e.toFun f.toFun, e.toFun.continuous.sumMap f.toFun.continuous⟩
  invFun := ⟨Sum.map e.invFun f.invFun, e.invFun.continuous.sumMap f.invFun.continuous⟩
  left_inv := by
    rcases e.left_inv with ⟨he⟩
    rcases f.left_inv with ⟨hf⟩
    refine ⟨(homotopySum he hf).cast ?_ ?_⟩
    · ext z
      cases z <;> rfl
    · ext z
      cases z <;> rfl
  right_inv := by
    rcases e.right_inv with ⟨he⟩
    rcases f.right_inv with ⟨hf⟩
    refine ⟨(homotopySum he hf).cast ?_ ?_⟩
    · ext z
      cases z <;> rfl
    · ext z
      cases z <;> rfl

public theorem overlapBand_eq_lowBand_union_highBand :
    overlapBand = lowBand ∪ highBand :=
  Set.Subset.antisymm overlapBand_subset_union
    (Set.union_subset lowBand_subset_overlapBand highBand_subset_overlapBand)

def lowHighOverlapBandHomeomorph :
    lowBand ⊕ highBand ≃ₜ overlapBand :=
  (disjointOpenUnionHomeomorph lowBand highBand
    (isOpen_openBand _ _) (isOpen_openBand _ _) disjoint_lowBand_highBand).trans
      (Homeomorph.setCongr overlapBand_eq_lowBand_union_highBand.symm)

/-- For a circle mapping torus, the edge piece deformation-retracts to its midpoint fibre. -/
public def circleMappingTorusEdgePieceHomotopyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    HomotopyEquiv F ↥(edgePiece (fun _ : Unit ↦ phi)) :=
  ((fiberBandProdHomotopyEquiv (F := F) uHalf_mem_edgeOpenBand).trans
    unitProdHomeomorph.symm.toHomotopyEquiv).trans
      (bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand
        (fun _ h ↦ h)).toHomotopyEquiv

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_toFun
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).toFun x =
      edgePt (fun _ : Unit ↦ phi) () x :=
  rfl

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeLowPt
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun
        (edgeLowPt (fun _ : Unit ↦ phi) () x) = x :=
  by
    rw [show edgeLowPt (fun _ : Unit ↦ phi) () x =
      bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)
        ((), ⟨uQuarter, uQuarter_mem_edgeBand⟩, x) by rfl]
    change
      (fiberBandProdHomotopyEquiv uHalf_mem_edgeOpenBand).invFun
        (unitProdHomeomorph
          ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)).symm
            ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h))
              ((), ⟨uQuarter, uQuarter_mem_edgeBand⟩, x)))) = x
    rw [Homeomorph.symm_apply_apply]
    rfl

@[simp]
public theorem circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeHighPt
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun
        (edgeHighPt (fun _ : Unit ↦ phi) () x) = x :=
  by
    rw [show edgeHighPt (fun _ : Unit ↦ phi) () x =
      bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)
        ((), ⟨uThreeQuarters, uThreeQuarters_mem_edgeBand⟩, x) by rfl]
    change
      (fiberBandProdHomotopyEquiv uHalf_mem_edgeOpenBand).invFun
        (unitProdHomeomorph
          ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h)).symm
            ((bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_edgeBand (fun _ h ↦ h))
              ((), ⟨uThreeQuarters, uThreeQuarters_mem_edgeBand⟩, x)))) = x
    rw [Homeomorph.symm_apply_apply]
    rfl

/-- The overlap of the two standard circle-mapping-torus pieces deformation-retracts to its
low and high fibre components. -/
public def circleMappingTorusOverlapHomotopyEquiv
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    HomotopyEquiv (F ⊕ F)
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)) :=
  (((((homotopyEquivSum
      (fiberBandProdHomotopyEquiv (F := F) uQuarter_mem_lowBand)
      (fiberBandProdHomotopyEquiv (F := F) uThreeQuarters_mem_highBand)).trans
        Homeomorph.sumProdDistrib.symm.toHomotopyEquiv).trans
      (lowHighOverlapBandHomeomorph.prodCongr
        (Homeomorph.refl F)).toHomotopyEquiv).trans
    unitProdHomeomorph.symm.toHomotopyEquiv).trans
      (bandPieceHomeo (fun _ : Unit ↦ phi) isOpen_overlapBand
        overlapBand_subset_edgeBand).toHomotopyEquiv).trans
    (overlapHomeo (fun _ : Unit ↦ phi)).toHomotopyEquiv

@[simp]
public theorem circleMappingTorusOverlapHomotopyEquiv_toFun_inl
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inl x) =
      overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand () x := by
  rfl

@[simp]
public theorem circleMappingTorusOverlapHomotopyEquiv_toFun_inr
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (x : F) :
    (circleMappingTorusOverlapHomotopyEquiv phi).toFun (Sum.inr x) =
      overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand () x := by
  rfl

public theorem circleMappingTorusOverlapHigh_edgeRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
        ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInrContinuousMap (X := F)))) =
      ContinuousMap.id F := by
  ext x
  exact circleMappingTorusEdgePieceHomotopyEquiv_invFun_edgeHighPt phi x

public theorem circleMappingTorusOverlapHigh_vertexRetract
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) :
    (vertexRetract (fun _ : Unit ↦ phi)).comp
        ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
          (edgePiece (fun _ : Unit ↦ phi))).comp
            ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
              (sumInrContinuousMap (X := F)))) =
      (phi : C(F, F)) := by
  ext x
  change vertexRetract (fun _ : Unit ↦ phi)
      (vertexHighPt (fun _ : Unit ↦ phi) () x) = phi x
  exact congrArg (fun f : C(F, F) => f x)
    (vertexRetract_comp_vertexHighPt (fun _ : Unit ↦ phi) ())

public theorem circleMappingTorusOverlapHigh_intertwining
    {F H : Type} [TopologicalSpace F] [PathConnectedSpace F] [Group H]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x)
    (f : FundamentalGroup F x →* H) (t : H)
    (h : ∀ a : FundamentalGroup F x,
      t * f a * t⁻¹ = f (mappingTorusMonodromyHom phi x delta a))
    (a : FundamentalGroup F x) :
    (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((circleMappingTorusEdgePieceHomotopyEquiv phi).invFun.comp
              ((interToRight (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInrContinuousMap (X := F)))))).map a) ≫
        circleMappingTorusHighGauge phi x delta f t =
      circleMappingTorusHighGauge phi x delta f t ≫
        (fundamentalGroupoidBasedFunctor x f).map
          ((FundamentalGroupoid.map
            ((vertexRetract (fun _ : Unit ↦ phi)).comp
              ((interToLeft (vertexPiece (fun _ : Unit ↦ phi))
                (edgePiece (fun _ : Unit ↦ phi))).comp
                  ((circleMappingTorusOverlapHomotopyEquiv phi).toFun.comp
                    (sumInrContinuousMap (X := F)))))).map a) := by
  rw [circleMappingTorusOverlapHigh_edgeRetract,
    circleMappingTorusOverlapHigh_vertexRetract]
  rw [show FundamentalGroupoid.map (ContinuousMap.id F) = 𝟭 _ from
    FundamentalGroupoid.map_id]
  exact fundamentalGroupoidBasedFunctor_high_intertwining phi x delta f t h a

end SphereSixComplex
