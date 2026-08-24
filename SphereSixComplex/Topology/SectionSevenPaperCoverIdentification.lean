module

public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.Topology.EstablishedLerayCoverComparison
public import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-!
# Local intersection models for the Section 7 star cover

This file separates the geometry of every nonempty intersection of the actual four-piece star
cover from the finite Section 7 matrix calculation.  The local models form a contravariant
diagram under inclusion of index sets, and their realizations are required to commute strictly
with the induced singular-chain maps.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Set

namespace SphereSixComplex

/-- Index the central star piece by zero and its three fillings by one through three. -/
public def sectionSevenFourPieceStarIndex : Fin 4 → Option (Fin 3) :=
  Fin.cases none some

/-- The actual four-piece open cover of a star gluing by the open images of its pieces. -/
public noncomputable def sectionSevenStarOpenCover (A : FourPieceStarGluingData) :
    FourPieceOpenCover (GluedSpace A.glueData) where
  piece i := Set.range (A.glueData.toGlueData.ι (sectionSevenFourPieceStarIndex i))
  isOpen_piece i :=
    (A.glueData.ι_isOpenEmbedding (sectionSevenFourPieceStarIndex i)).isOpen_range
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := A.glueData.ι_jointly_surjective x
    cases i with
    | none => exact ⟨0, y, hy⟩
    | some i => exact ⟨i.succ, y, hy⟩

section IntersectionMaps

variable {iota X : Type} [TopologicalSpace X] (U : iota → Set X)

/-- Inclusion of a smaller geometric intersection into a larger one: if `s ⊆ t`, then the
intersection indexed by `t` is contained in the intersection indexed by `s`. -/
public def finiteCoverIntersectionInclusion {s t : Finset iota} (h : s ⊆ t) :
    ContinuousMap (finiteCoverIntersection U t) (finiteCoverIntersection U s) where
  toFun x := ⟨x.1, by
    rw [mem_finiteCoverIntersection_iff]
    intro i hi
    exact (mem_finiteCoverIntersection_iff U t x).mp x.2 i (h hi)⟩
  continuous_toFun := by fun_prop

/-- The singular-chain map induced by inclusion of finite cover intersections. -/
public noncomputable def finiteCoverIntersectionChainMap {s t : Finset iota} (h : s ⊆ t) :
    IntegralSingularChainComplex (finiteCoverIntersection U t) ⟶
      IntegralSingularChainComplex (finiteCoverIntersection U s) :=
  integralSingularChainMap (finiteCoverIntersectionInclusion U h)

@[simp]
public theorem finiteCoverIntersectionInclusion_id (s : Finset iota) :
    finiteCoverIntersectionInclusion U (show s ⊆ s from fun _ hi ↦ hi) =
      ContinuousMap.id _ := by
  ext x
  rfl

public theorem finiteCoverIntersectionInclusion_comp
    {r s t : Finset iota} (hrs : r ⊆ s) (hst : s ⊆ t) :
    (finiteCoverIntersectionInclusion U hrs).comp
        (finiteCoverIntersectionInclusion U hst) =
      finiteCoverIntersectionInclusion U (hrs.trans hst) := by
  ext x
  rfl

end IntersectionMaps

/-- A nonempty intersection of members of the four-piece cover. -/
public abbrev FourPieceIntersectionIndex :=
  {s : Finset (Fin 4) // s.Nonempty}

/-- Exact local chain-level input for the actual open cover of a four-piece star gluing. -/
public structure SectionSevenStarIntersectionChainModels (A : FourPieceStarGluingData) where
  /-- A tractable chain model for each nonempty finite intersection. -/
  model : FourPieceIntersectionIndex → ChainComplex AddCommGrpCat ℕ
  /-- Restriction along `s ⊆ t`, directed like inclusion of the corresponding intersections. -/
  face : ∀ {s t : FourPieceIntersectionIndex}, s.1 ⊆ t.1 → (model t ⟶ model s)
  /-- Identity inclusions act as identity chain maps. -/
  face_id : ∀ s, face (show s.1 ⊆ s.1 from fun _ hi ↦ hi) = 𝟙 (model s)
  /-- Restriction maps compose functorially. -/
  face_comp : ∀ {r s t : FourPieceIntersectionIndex}
    (hrs : r.1 ⊆ s.1) (hst : s.1 ⊆ t.1),
    face hst ≫ face hrs = face (hrs.trans hst)
  /-- Each local model is chain-homotopy equivalent to the full singular chains of the actual
  intersection; no acyclicity assumption is made. -/
  realization : ∀ s, HomotopyEquiv (model s)
    (IntegralSingularChainComplex
      (finiteCoverIntersection (sectionSevenStarOpenCover A).piece s.1))
  /-- Forward realizations commute with every intersection inclusion. -/
  realization_hom_naturality : ∀ {s t} (h : s.1 ⊆ t.1),
    face h ≫ (realization s).hom =
      (realization t).hom ≫
        finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece h
  /-- Chosen inverse realizations commute with every intersection inclusion. -/
  realization_inv_naturality : ∀ {s t} (h : s.1 ⊆ t.1),
    finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece h ≫
      (realization s).inv =
      (realization t).inv ≫ face h
  /-- The homotopy from `hom ≫ inv` to the identity is natural under every face map. -/
  homotopyHomInvId_naturality : ∀ {s t} (h : s.1 ⊆ t.1) i j,
    (face h).f i ≫ (realization s).homotopyHomInvId.hom i j =
      (realization t).homotopyHomInvId.hom i j ≫ (face h).f j
  /-- The homotopy from `inv ≫ hom` to the identity is natural under every inclusion of
  singular intersection chains. -/
  homotopyInvHomId_naturality : ∀ {s t} (h : s.1 ⊆ t.1) i j,
    (finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece h).f i ≫
        (realization s).homotopyInvHomId.hom i j =
      (realization t).homotopyInvHomId.hom i j ≫
        (finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece h).f j

namespace SectionSevenStarIntersectionChainModels

variable {A : FourPieceStarGluingData}

/-- Ordered cover indices occurring in one simplicial degree of the Čech nerve. -/
public abbrev CechTuple (n : SimplexCategoryᵒᵖ) :=
  Fin (n.unop.len + 1) → Fin 4

/-- The underlying nonempty finite set of an ordered Čech tuple. -/
public def CechTuple.support {n : SimplexCategoryᵒᵖ} (a : CechTuple n) : Finset (Fin 4) :=
  Finset.univ.image a

public theorem CechTuple.support_nonempty {n : SimplexCategoryᵒᵖ} (a : CechTuple n) :
    a.support.Nonempty := by
  exact ⟨a 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- Regard the support of a Čech tuple as a nonempty intersection index. -/
public def CechTuple.intersectionIndex {n : SimplexCategoryᵒᵖ} (a : CechTuple n) :
    FourPieceIntersectionIndex :=
  ⟨a.support, a.support_nonempty⟩

/-- Restrict an ordered tuple along a simplicial operator. -/
public def CechTuple.restrict {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m)
    (a : CechTuple n) : CechTuple m :=
  fun i ↦ a (f.unop.toOrderHom i)

public theorem CechTuple.support_restrict_subset
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : CechTuple n) :
    (a.restrict f).support ⊆ a.support := by
  intro x hx
  rw [CechTuple.support, Finset.mem_image] at hx ⊢
  obtain ⟨i, _, rfl⟩ := hx
  exact ⟨f.unop.toOrderHom i, Finset.mem_univ _, rfl⟩

public theorem CechTuple.intersectionIndex_restrict_subset
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : CechTuple n) :
    (a.restrict f).intersectionIndex.1 ⊆ a.intersectionIndex.1 :=
  CechTuple.support_restrict_subset f a

/-- The chosen `hom ≫ inv` homotopies commute with every simplicial operator on an ordered
Čech tuple.  Thus no additional pairwise face coherence is required before taking alternating
face sums. -/
public theorem realization_homotopyHomInvId_restrict_naturality
    (L : SectionSevenStarIntersectionChainModels A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : CechTuple n) (i j : ℕ) :
    (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
        (L.realization (a.restrict f).intersectionIndex).homotopyHomInvId.hom i j =
      (L.realization a.intersectionIndex).homotopyHomInvId.hom i j ≫
        (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f j :=
  L.homotopyHomInvId_naturality
    (CechTuple.intersectionIndex_restrict_subset f a) i j

/-- The chosen `inv ≫ hom` homotopies commute with the singular-chain inclusion induced by
every simplicial operator on an ordered Čech tuple. -/
public theorem realization_homotopyInvHomId_restrict_naturality
    (L : SectionSevenStarIntersectionChainModels A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : CechTuple n) (i j : ℕ) :
    (finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece
        (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
        (L.realization (a.restrict f).intersectionIndex).homotopyInvHomId.hom i j =
      (L.realization a.intersectionIndex).homotopyInvHomId.hom i j ≫
        (finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece
          (CechTuple.intersectionIndex_restrict_subset f a)).f j :=
  L.homotopyInvHomId_naturality
    (CechTuple.intersectionIndex_restrict_subset f a) i j

@[simp]
public theorem CechTuple.restrict_id {n : SimplexCategoryᵒᵖ} (a : CechTuple n) :
    a.restrict (𝟙 n) = a := by
  ext i
  rfl

@[simp]
public theorem CechTuple.restrict_comp
    {n m l : SimplexCategoryᵒᵖ} (f : n ⟶ m) (g : m ⟶ l) (a : CechTuple n) :
    (a.restrict f).restrict g = a.restrict (f ≫ g) := by
  ext i
  rfl

/-- The simplicial chain-complex diagram obtained by taking coproducts of the local models over
all ordered Čech tuples.  Repeated indices are retained, matching the canonical Čech nerve. -/
public noncomputable def localCechChainSimplicialObject
    (L : SectionSevenStarIntersectionChainModels A) :
    SimplicialObject (ChainComplex AddCommGrpCat ℕ) where
  obj n := ∐ fun a : CechTuple n ↦ L.model a.intersectionIndex
  map {n m} f := Sigma.desc fun a ↦
    L.face (CechTuple.intersectionIndex_restrict_subset f a) ≫
      Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex) (a.restrict f)
  map_id n := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    change L.face (show a.intersectionIndex.1 ⊆ a.intersectionIndex.1 from fun _ hi ↦ hi) ≫
      Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a =
        Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫ 𝟙 _
    rw [L.face_id]
    simp
  map_comp f g := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_desc]
    rw [Sigma.ι_desc_assoc]
    rw [Category.assoc, Sigma.ι_desc]
    rw [← Category.assoc, L.face_comp]
    congr 1

/-- The alternating-face bicomplex of the explicit local intersection models. -/
public noncomputable def localLerayCechBicomplex
    (L : SectionSevenStarIntersectionChainModels A) :
    HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  (alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).obj
    L.localCechChainSimplicialObject

/-- The total complex of the explicit local intersection models. -/
public noncomputable def localLerayCechTotal
    (L : SectionSevenStarIntersectionChainModels A) : ChainComplex AddCommGrpCat ℕ :=
  L.localLerayCechBicomplex.total (ComplexShape.down ℕ)

/-- The same finite-intersection diagram with the full singular chain complex at every vertex. -/
public noncomputable def singularIntersectionModels (A : FourPieceStarGluingData) :
    SectionSevenStarIntersectionChainModels A where
  model s := IntegralSingularChainComplex
    (finiteCoverIntersection (sectionSevenStarOpenCover A).piece s.1)
  face h := finiteCoverIntersectionChainMap (sectionSevenStarOpenCover A).piece h
  face_id s := by
    simp [finiteCoverIntersectionChainMap, integralSingularChainMap]
  face_comp hrs hst := by
    simp only [finiteCoverIntersectionChainMap, integralSingularChainMap]
    rw [← Functor.map_comp]
    congr 1
  realization s := HomotopyEquiv.refl _
  realization_hom_naturality h := by simp
  realization_inv_naturality h := by simp
  homotopyHomInvId_naturality h i j := by simp
  homotopyInvHomId_naturality h i j := by simp

/-- The explicit total Čech complex whose summands are singular chains on the actual ordered
finite intersections of the four star-cover pieces. -/
public noncomputable abbrev singularIntersectionLerayCechTotal
    (A : FourPieceStarGluingData) : ChainComplex AddCommGrpCat ℕ :=
  (singularIntersectionModels A).localLerayCechTotal

/-- A strictly natural family of maps on intersection models induces a map of the ordered
Čech simplicial chain objects. -/
public noncomputable def naturalTransformationOfFaces
    (L M : SectionSevenStarIntersectionChainModels A)
    (map : ∀ s, L.model s ⟶ M.model s)
    (map_naturality : ∀ {s t} (h : s.1 ⊆ t.1),
      L.face h ≫ map s = map t ≫ M.face h) :
    L.localCechChainSimplicialObject ⟶ M.localCechChainSimplicialObject where
  app n := Sigma.desc fun a ↦
    map a.intersectionIndex ≫
      Sigma.ι (fun b : CechTuple n ↦ M.model b.intersectionIndex) a
  naturality {n m} f := by
    apply Sigma.hom_ext
    intro a
    dsimp [localCechChainSimplicialObject]
    simp only [Sigma.ι_desc_assoc, Category.assoc, Sigma.ι_desc]
    rw [← Category.assoc, map_naturality]
    simp

/-- The strictly natural forward maps from the chosen local models to singular intersection
chains. -/
public noncomputable def realizationHom
    (L : SectionSevenStarIntersectionChainModels A) :
    L.localCechChainSimplicialObject ⟶
      (singularIntersectionModels A).localCechChainSimplicialObject :=
  naturalTransformationOfFaces L (singularIntersectionModels A)
    (fun s ↦ (L.realization s).hom) (fun h ↦ L.realization_hom_naturality h)

/-- The strictly natural chosen inverse maps from singular intersection chains to the local
models. -/
public noncomputable def realizationInv
    (L : SectionSevenStarIntersectionChainModels A) :
    (singularIntersectionModels A).localCechChainSimplicialObject ⟶
      L.localCechChainSimplicialObject :=
  naturalTransformationOfFaces (singularIntersectionModels A) L
    (fun s ↦ (L.realization s).inv) (fun h ↦ L.realization_inv_naturality h)

/-- The total-chain map induced by all forward local realization maps. -/
public noncomputable def totalRealizationHom
    (L : SectionSevenStarIntersectionChainModels A) :
    L.localLerayCechTotal ⟶ singularIntersectionLerayCechTotal A :=
  HomologicalComplex₂.total.map
    ((alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationHom)
    (ComplexShape.down ℕ)

/-- The total-chain map induced by all chosen inverse local realization maps. -/
public noncomputable def totalRealizationInv
    (L : SectionSevenStarIntersectionChainModels A) :
    singularIntersectionLerayCechTotal A ⟶ L.localLerayCechTotal :=
  HomologicalComplex₂.total.map
    ((alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationInv)
    (ComplexShape.down ℕ)

/-- A vertical chain homotopy between bicomplex maps which is natural with respect to the
horizontal differential.  This is the exact generic input needed to totalize a pointwise
homotopy; it does not assume any conclusion about total complexes. -/
public structure VerticallyNaturalHomotopy
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    (φ ψ : K ⟶ M) where
  homotopy : ∀ p, Homotopy (φ.f p) (ψ.f p)
  horizontal_naturality : ∀ {p p'} (_ : (ComplexShape.down ℕ).Rel p p') i j,
    (K.d p p').f i ≫ (homotopy p').hom i j =
      (homotopy p).hom i j ≫ (M.d p p').f j

/-- The signed summand formula for totalizing a vertically natural homotopy.  On the summand
in bidegree `(p,q)` it is `ε₂(p,q)` times the vertical homotopy into `(p,q+1)`.  The target
inclusion is zero unless that bidegree has total degree `n'`. -/
public noncomputable def VerticallyNaturalHomotopy.totalComponent
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {φ ψ : K ⟶ M} (h : VerticallyNaturalHomotopy φ ψ) (n n' : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (M.total (ComplexShape.down ℕ)).X n' :=
  K.totalDesc fun p q _ ↦
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
        (ComplexShape.down ℕ) (p, q) •
      ((h.homotopy p).hom q (q + 1) ≫
        M.ιTotalOrZero (ComplexShape.down ℕ) p (q + 1) n')

@[reassoc]
public theorem VerticallyNaturalHomotopy.ιTotal_totalComponent
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {φ ψ : K ⟶ M} (h : VerticallyNaturalHomotopy φ ψ)
    (p q n n' : ℕ)
    (hpq : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ h.totalComponent n n' =
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, q) •
        ((h.homotopy p).hom q (q + 1) ≫
          M.ιTotalOrZero (ComplexShape.down ℕ) p (q + 1) n') := by
  unfold VerticallyNaturalHomotopy.totalComponent
  rw [HomologicalComplex₂.ι_totalDesc]

public theorem VerticallyNaturalHomotopy.totalComponent_zero
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {φ ψ : K ⟶ M} (h : VerticallyNaturalHomotopy φ ψ) (n n' : ℕ)
    (hn : ¬(ComplexShape.down ℕ).Rel n' n) : h.totalComponent n n' = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  unfold VerticallyNaturalHomotopy.totalComponent
  rw [HomologicalComplex₂.ι_totalDesc]
  rw [M.ιTotalOrZero_eq_zero]
  · rw [comp_zero, smul_zero, comp_zero]
  · intro hpq'
    apply hn
    change n + 1 = n'
    change p + q = n at hpq
    change p + (q + 1) = n' at hpq'
    omega

/-- The two horizontal cross terms in the total homotopy equation cancel.  This is the sign
calculation which explains the `ε₂` coefficient in `totalComponent`. -/
public theorem VerticallyNaturalHomotopy.horizontal_terms_cancel
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {φ ψ : K ⟶ M} (h : VerticallyNaturalHomotopy φ ψ)
    {p p' : ℕ} (hpp' : (ComplexShape.down ℕ).Rel p p') (i j : ℕ) :
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p, i) •
        ((K.d p p').f i ≫ (h.homotopy p').hom i j) +
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (p', i) •
        ((h.homotopy p).hom i j ≫ (M.d p p').f j) = 0 := by
  rw [h.horizontal_naturality hpp' i j]
  change (ComplexShape.down ℕ).ε p • _ + (ComplexShape.down ℕ).ε p' • _ = 0
  rw [(ComplexShape.down ℕ).ε_succ hpp']
  rw [Units.neg_smul, add_neg_cancel]

/-- A vertically natural family of chain homotopies totalizes to a chain homotopy. -/
public noncomputable def VerticallyNaturalHomotopy.totalHomotopy
    {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
    {φ ψ : K ⟶ M} (h : VerticallyNaturalHomotopy φ ψ) :
    Homotopy
      (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ))
      (HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ)) where
  hom := h.totalComponent
  zero := h.totalComponent_zero
  comm n := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    simp only [Preadditive.comp_add, HomologicalComplex₂.ιTotal_map]
    change p + q = n at hpq
    cases n with
    | zero =>
      have hp : p = 0 := by omega
      have hq : q = 0 := by omega
      subst p
      subst q
      rw [Homotopy.dNext_zero_chainComplex, comp_zero, zero_add]
      rw [Homotopy.prevD_chainComplex]
      rw [← Category.assoc, h.ιTotal_totalComponent]
      have heps : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 0) = 1 := by
        change (ComplexShape.down ℕ).ε 0 = 1
        rfl
      rw [heps, one_smul]
      change _ =
        ((h.homotopy 0).hom 0 1 ≫
          M.ιTotalOrZero (ComplexShape.down ℕ) 0 1 1) ≫
            (M.total (ComplexShape.down ℕ)).d 1 0 + _
      rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) 0 1 1 (by rfl)]
      change _ =
        ((h.homotopy 0).hom 0 1 ≫
          M.ιTotal (ComplexShape.down ℕ) 0 1 1 rfl) ≫
            (M.D₁ (ComplexShape.down ℕ) 1 0 +
              M.D₂ (ComplexShape.down ℕ) 1 0) + _
      rw [Preadditive.comp_add, Category.assoc, HomologicalComplex₂.ι_D₁,
        Category.assoc, HomologicalComplex₂.ι_D₂]
      have hd1 : M.d₁ (ComplexShape.down ℕ) 0 1 0 = 0 :=
        M.d₁_eq_zero (ComplexShape.down ℕ) 0 1 0 (by
          rw [ChainComplex.next_nat_zero]
          simp)
      rw [hd1]
      rw [comp_zero, zero_add]
      have heps' : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (ComplexShape.down ℕ) (0, 1) = 1 := by
        change (ComplexShape.down ℕ).ε 0 = 1
        rfl
      have hd2 : M.d₂ (ComplexShape.down ℕ) 0 1 0 =
          (M.X 0).d 1 0 ≫ M.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl := by
        simpa only [heps', one_smul] using
          M.d₂_eq (ComplexShape.down ℕ) 0
            (show (ComplexShape.down ℕ).Rel 1 0 by rfl) 0 rfl
      rw [hd2, ← Category.assoc]
      have hc := (h.homotopy 0).comm 0
      rw [Homotopy.dNext_zero_chainComplex, zero_add,
        Homotopy.prevD_chainComplex] at hc
      rw [hc, Preadditive.add_comp, Category.assoc]
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex]
      rw [Homotopy.prevD_chainComplex]
      have hpqUp : p + (q + 1) = n + 1 + 1 := by omega
      have hnext :
          K.ιTotal (ComplexShape.down ℕ) p q (n + 1) hpq ≫
              (K.total (ComplexShape.down ℕ)).d (n + 1) n ≫
                h.totalComponent n (n + 1) =
            K.d₁ (ComplexShape.down ℕ) p q n ≫ h.totalComponent n (n + 1) +
              K.d₂ (ComplexShape.down ℕ) p q n ≫ h.totalComponent n (n + 1) := by
        rw [← Category.assoc]
        change (K.ιTotal (ComplexShape.down ℕ) p q (n + 1) hpq ≫
          (K.D₁ (ComplexShape.down ℕ) _ _ + K.D₂ (ComplexShape.down ℕ) _ _)) ≫ _ = _
        rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁,
          HomologicalComplex₂.ι_D₂, Preadditive.add_comp]
      have hprev :
          K.ιTotal (ComplexShape.down ℕ) p q (n + 1) hpq ≫
              h.totalComponent (n + 1) (n + 1 + 1) ≫
                (M.total (ComplexShape.down ℕ)).d (n + 1 + 1) (n + 1) =
            ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, q) •
                ((h.homotopy p).hom q (q + 1) ≫
                  M.d₁ (ComplexShape.down ℕ) p (q + 1) (n + 1)) +
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p, q) •
                ((h.homotopy p).hom q (q + 1) ≫
                  M.d₂ (ComplexShape.down ℕ) p (q + 1) (n + 1)) := by
        rw [← Category.assoc, h.ιTotal_totalComponent]
        rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) p (q + 1)
          (n + 1 + 1) hpqUp]
        change (_ • (_ ≫ _)) ≫ (M.D₁ (ComplexShape.down ℕ) _ _ +
          M.D₂ (ComplexShape.down ℕ) _ _) = _
        rw [Preadditive.comp_add, Linear.units_smul_comp, Category.assoc,
          HomologicalComplex₂.ι_D₁, Linear.units_smul_comp, Category.assoc,
          HomologicalComplex₂.ι_D₂]
      rw [hnext, hprev]
      cases p with
      | zero =>
        cases q with
        | zero => omega
        | succ q =>
          have hn : n = q := by omega
          subst n
          have hdK1 : K.d₁ (ComplexShape.down ℕ) 0 (q + 1) q = 0 :=
            K.d₁_eq_zero (ComplexShape.down ℕ) 0 (q + 1) q (by
              rw [ChainComplex.next_nat_zero]
              simp)
          have hdM1 : M.d₁ (ComplexShape.down ℕ) 0 (q + 1 + 1) (q + 1) = 0 :=
            M.d₁_eq_zero (ComplexShape.down ℕ) 0 (q + 1 + 1) (q + 1) (by
              rw [ChainComplex.next_nat_zero]
              simp)
          rw [hdK1, zero_comp, zero_add, hdM1, comp_zero, smul_zero, zero_add]
          have heps0 (r : ℕ) : ComplexShape.ε₂ (ComplexShape.down ℕ)
              (ComplexShape.down ℕ) (ComplexShape.down ℕ) (0, r) = 1 := by
            change (ComplexShape.down ℕ).ε 0 = 1
            rfl
          have hdK2 : K.d₂ (ComplexShape.down ℕ) 0 (q + 1) q =
              (K.X 0).d (q + 1) q ≫
                K.ιTotal (ComplexShape.down ℕ) 0 q q (by
                  change 0 + q = q
                  omega) := by
            simpa only [heps0, one_smul] using
              K.d₂_eq (ComplexShape.down ℕ) 0
                (show (ComplexShape.down ℕ).Rel (q + 1) q by rfl) q (by
                  change 0 + q = q
                  omega)
          have hdM2 : M.d₂ (ComplexShape.down ℕ) 0 (q + 1 + 1) (q + 1) =
              (M.X 0).d (q + 1 + 1) (q + 1) ≫
                M.ιTotal (ComplexShape.down ℕ) 0 (q + 1) (q + 1) (by
                  change 0 + (q + 1) = q + 1
                  omega) := by
            simpa only [heps0, one_smul] using
              M.d₂_eq (ComplexShape.down ℕ) 0
                (show (ComplexShape.down ℕ).Rel (q + 1 + 1) (q + 1) by
                  change q + 1 + 1 = q + 1 + 1
                  rfl)
                (q + 1) (by
                  change 0 + (q + 1) = q + 1
                  omega)
          rw [hdK2, Category.assoc, h.ιTotal_totalComponent, heps0, one_smul]
          rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) 0 (q + 1) (q + 1) (by
            change 0 + (q + 1) = q + 1
            omega)]
          rw [hdM2, heps0, one_smul, ← Category.assoc]
          have hc := (h.homotopy 0).comm (q + 1)
          rw [Homotopy.dNext_succ_chainComplex,
            Homotopy.prevD_chainComplex] at hc
          rw [hc, Preadditive.add_comp, Preadditive.add_comp, Category.assoc]
          simp only [Category.assoc]
      | succ p =>
        cases q with
        | zero =>
          have hn : n = p := by omega
          subst n
          have hpRel : (ComplexShape.down ℕ).Rel (p + 1) p := by rfl
          have hdK2 : K.d₂ (ComplexShape.down ℕ) (p + 1) 0 p = 0 :=
            K.d₂_eq_zero (ComplexShape.down ℕ) (p + 1) 0 p (by
              rw [ChainComplex.next_nat_zero]
              simp)
          rw [hdK2, zero_comp, add_zero]
          have hdK1 : K.d₁ (ComplexShape.down ℕ) (p + 1) 0 p =
              (K.d (p + 1) p).f 0 ≫
                K.ιTotal (ComplexShape.down ℕ) p 0 p (by
                  change p + 0 = p
                  omega) := by
            simpa using K.d₁_eq (ComplexShape.down ℕ) hpRel 0 p (by
              change p + 0 = p
              omega)
          have hdM1 : M.d₁ (ComplexShape.down ℕ) (p + 1) 1 (p + 1) =
              (M.d (p + 1) p).f 1 ≫
                M.ιTotal (ComplexShape.down ℕ) p 1 (p + 1) (by omega) := by
            simpa using M.d₁_eq (ComplexShape.down ℕ) hpRel 1 (p + 1) (by omega)
          have hdM2 : M.d₂ (ComplexShape.down ℕ) (p + 1) 1 (p + 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                  (ComplexShape.down ℕ) (p + 1, 1) •
                ((M.X (p + 1)).d 1 0 ≫
                  M.ιTotal (ComplexShape.down ℕ) (p + 1) 0 (p + 1) (by omega)) := by
            simpa using M.d₂_eq (ComplexShape.down ℕ) (p + 1)
              (show (ComplexShape.down ℕ).Rel 1 0 by rfl) (p + 1) (by omega)
          rw [hdK1, Category.assoc, h.ιTotal_totalComponent]
          rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) p 1 (p + 1) (by omega)]
          rw [hdM1, hdM2]
          have hcancel := h.horizontal_terms_cancel hpRel 0 1
          have hcancelSwap :
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, 0) •
                  ((K.d (p + 1) p).f 0 ≫ (h.homotopy p).hom 0 1) +
                ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p + 1, 0) •
                  ((h.homotopy (p + 1)).hom 0 1 ≫ (M.d (p + 1) p).f 1) = 0 := by
            rw [h.horizontal_naturality hpRel 0 1]
            change (ComplexShape.down ℕ).ε p • _ +
              (ComplexShape.down ℕ).ε (p + 1) • _ = 0
            rw [(ComplexShape.down ℕ).ε_succ hpRel]
            rw [Units.neg_smul, neg_add_cancel]
          have hc := (h.homotopy (p + 1)).comm 0
          rw [Homotopy.dNext_zero_chainComplex, zero_add,
            Homotopy.prevD_chainComplex] at hc
          have hcancelPost := congrArg
            (fun k ↦ k ≫ M.ιTotal (ComplexShape.down ℕ) p 1 (p + 1) (by omega))
            hcancelSwap
          rw [Preadditive.add_comp, zero_comp] at hcancelPost
          have hsign : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, 0) := by rfl
          simp only [Linear.comp_units_smul, smul_smul,
            hsign, Int.units_mul_self, one_smul]
          have hcancelPost' := hcancelPost
          rw [Linear.units_smul_comp, Linear.units_smul_comp] at hcancelPost'
          have hhorizontal :
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, 0) •
                  ((K.d (p + 1) p).f 0 ≫ (h.homotopy p).hom 0 1 ≫
                    M.ιTotal (ComplexShape.down ℕ) p 1 (p + 1) (by omega)) +
                ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p + 1, 0) •
                  ((h.homotopy (p + 1)).hom 0 1 ≫ (M.d (p + 1) p).f 1 ≫
                    M.ιTotal (ComplexShape.down ℕ) p 1 (p + 1) (by omega)) = 0 := by
            simpa only [Category.assoc] using hcancelPost'
          rw [hc, Preadditive.add_comp, Category.assoc]
          rw [← add_assoc, hhorizontal]
          simp
        | succ q =>
          have hn : n = p + q + 1 := by omega
          subst n
          have hpRel : (ComplexShape.down ℕ).Rel (p + 1) p := by rfl
          have hqRel : (ComplexShape.down ℕ).Rel (q + 1) q := by rfl
          have hqUpRel : (ComplexShape.down ℕ).Rel (q + 1 + 1) (q + 1) := by
            change q + 1 + 1 = q + 1 + 1
            rfl
          have hdK1 : K.d₁ (ComplexShape.down ℕ) (p + 1) (q + 1) (p + q + 1) =
              (K.d (p + 1) p).f (q + 1) ≫
                K.ιTotal (ComplexShape.down ℕ) p (q + 1) (p + q + 1) (by
                  change p + (q + 1) = p + q + 1
                  omega) := by
            simpa using K.d₁_eq (ComplexShape.down ℕ) hpRel (q + 1) (p + q + 1) (by
              change p + (q + 1) = p + q + 1
              omega)
          have hdK2 : K.d₂ (ComplexShape.down ℕ) (p + 1) (q + 1) (p + q + 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                  (ComplexShape.down ℕ) (p + 1, q + 1) •
                ((K.X (p + 1)).d (q + 1) q ≫
                  K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + q + 1) (by
                    change p + 1 + q = p + q + 1
                    omega)) := by
            simpa using K.d₂_eq (ComplexShape.down ℕ) (p + 1) hqRel (p + q + 1) (by
              change p + 1 + q = p + q + 1
              omega)
          have hdM1 : M.d₁ (ComplexShape.down ℕ) (p + 1) (q + 1 + 1)
                (p + q + 1 + 1) =
              (M.d (p + 1) p).f (q + 1 + 1) ≫
                M.ιTotal (ComplexShape.down ℕ) p (q + 1 + 1) (p + q + 1 + 1) (by
                  change p + (q + 1 + 1) = p + q + 1 + 1
                  omega) := by
            simpa using M.d₁_eq (ComplexShape.down ℕ) hpRel (q + 1 + 1)
              (p + q + 1 + 1) (by
                change p + (q + 1 + 1) = p + q + 1 + 1
                omega)
          have hdM2 : M.d₂ (ComplexShape.down ℕ) (p + 1) (q + 1 + 1)
                (p + q + 1 + 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                  (ComplexShape.down ℕ) (p + 1, q + 1 + 1) •
                ((M.X (p + 1)).d (q + 1 + 1) (q + 1) ≫
                  M.ιTotal (ComplexShape.down ℕ) (p + 1) (q + 1)
                    (p + q + 1 + 1) (by
                      change p + 1 + (q + 1) = p + q + 1 + 1
                      omega)) := by
            simpa using M.d₂_eq (ComplexShape.down ℕ) (p + 1) hqUpRel
              (p + q + 1 + 1) (by
                change p + 1 + (q + 1) = p + q + 1 + 1
                omega)
          rw [hdK1, Category.assoc, h.ιTotal_totalComponent]
          rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) p (q + 1 + 1)
            (p + q + 1 + 1) (by
              change p + (q + 1 + 1) = p + q + 1 + 1
              omega)]
          rw [hdK2, Linear.units_smul_comp, Category.assoc,
            h.ιTotal_totalComponent]
          rw [M.ιTotalOrZero_eq (ComplexShape.down ℕ) (p + 1) (q + 1)
            (p + q + 1 + 1) (by
              change p + 1 + (q + 1) = p + q + 1 + 1
              omega)]
          rw [hdM1, hdM2]
          have hcancelSwap :
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, q + 1) •
                  ((K.d (p + 1) p).f (q + 1) ≫
                    (h.homotopy p).hom (q + 1) (q + 1 + 1)) +
                ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p + 1, q + 1) •
                  ((h.homotopy (p + 1)).hom (q + 1) (q + 1 + 1) ≫
                    (M.d (p + 1) p).f (q + 1 + 1)) = 0 := by
            rw [h.horizontal_naturality hpRel (q + 1) (q + 1 + 1)]
            change (ComplexShape.down ℕ).ε p • _ +
              (ComplexShape.down ℕ).ε (p + 1) • _ = 0
            rw [(ComplexShape.down ℕ).ε_succ hpRel]
            rw [Units.neg_smul, neg_add_cancel]
          have hcancelPost := congrArg
            (fun k ↦ k ≫ M.ιTotal (ComplexShape.down ℕ) p (q + 1 + 1)
              (p + q + 1 + 1) (by
                change p + (q + 1 + 1) = p + q + 1 + 1
                omega)) hcancelSwap
          rw [Preadditive.add_comp, zero_comp] at hcancelPost
          have hhorizontal :
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p, q + 1) •
                  ((K.d (p + 1) p).f (q + 1) ≫
                    (h.homotopy p).hom (q + 1) (q + 1 + 1) ≫
                    M.ιTotal (ComplexShape.down ℕ) p (q + 1 + 1)
                      (p + q + 1 + 1) (by
                        change p + (q + 1 + 1) = p + q + 1 + 1
                        omega)) +
                ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                    (ComplexShape.down ℕ) (p + 1, q + 1) •
                  ((h.homotopy (p + 1)).hom (q + 1) (q + 1 + 1) ≫
                    (M.d (p + 1) p).f (q + 1 + 1) ≫
                    M.ιTotal (ComplexShape.down ℕ) p (q + 1 + 1)
                      (p + q + 1 + 1) (by
                        change p + (q + 1 + 1) = p + q + 1 + 1
                        omega)) = 0 := by
            simpa only [Linear.units_smul_comp, Category.assoc] using hcancelPost
          have hsignK : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, q + 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, q) := by rfl
          have hsignM : ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, q + 1 + 1) =
              ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ)
                (ComplexShape.down ℕ) (p + 1, q + 1) := by rfl
          simp only [Linear.comp_units_smul, smul_smul,
            hsignK, hsignM, Int.units_mul_self, one_smul]
          have hc := (h.homotopy (p + 1)).comm (q + 1)
          rw [Homotopy.dNext_succ_chainComplex,
            Homotopy.prevD_chainComplex] at hc
          rw [hc, Preadditive.add_comp, Preadditive.add_comp, Category.assoc]
          have hhorizontal' := hhorizontal
          rw [hsignK] at hhorizontal'
          have hsecond := eq_neg_of_add_eq_zero_right hhorizontal'
          rw [hsecond]
          simp only [Category.assoc]
          abel

variable {α : Type} (K : α → ChainComplex AddCommGrpCat ℕ)

public noncomputable def evalCoproductIso (i : ℕ) :=
  preservesColimitIso
    (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i)
    (Discrete.functor K)

public noncomputable def degreeDiagram (i : ℕ) :=
  Discrete.functor K ⋙
    HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i

public noncomputable def degreeNaturalTransformation (i j : ℕ)
    (u : ∀ a, (K a).X i ⟶ (K a).X j) :
    (Discrete.functor K ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i) ⟶
      (Discrete.functor K ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) j) where
  app a := u a.as
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ f
    obtain rfl : x = y := Discrete.eq_of_hom f
    have hf : f = 𝟙 _ := Subsingleton.elim _ _
    subst f
    change (𝟙 (K x) : K x ⟶ K x).f i ≫ u x =
      u x ≫ (𝟙 (K x) : K x ⟶ K x).f j
    simp only [HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

public noncomputable def coproductDegreeMap (i j : ℕ)
    (u : ∀ a, (K a).X i ⟶ (K a).X j) :
    (∐ K).X i ⟶ (∐ K).X j :=
  (evalCoproductIso K i).hom ≫
    colimMap (degreeNaturalTransformation K i j u) ≫
      (evalCoproductIso K j).inv

@[reassoc]
public theorem ι_coproductDegreeMap (i j : ℕ)
    (u : ∀ a, (K a).X i ⟶ (K a).X j) (a : α) :
    (Sigma.ι K a).f i ≫ coproductDegreeMap K i j u =
      u a ≫ (Sigma.ι K a).f j := by
  change _ = (degreeNaturalTransformation K i j u).app (Discrete.mk a) ≫ _
  unfold coproductDegreeMap evalCoproductIso
  change
    (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i).map
          (colimit.ι (Discrete.functor K) (Discrete.mk a)) ≫
        (preservesColimitIso
          (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i)
          (Discrete.functor K)).hom ≫
          colimMap (degreeNaturalTransformation K i j u) ≫
            (preservesColimitIso
              (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) j)
              (Discrete.functor K)).inv = _
  rw [← Category.assoc, ι_preservesColimitIso_hom]
  rw [← Category.assoc, ι_colimMap]
  rw [Category.assoc, ι_preservesColimitIso_inv]
  rfl

public theorem coproduct_hom_ext (i : ℕ) {X : AddCommGrpCat}
    {f g :
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i).obj
          (colimit (Discrete.functor K)) ⟶ X}
    (h : ∀ a,
      (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i).map
          (colimit.ι (Discrete.functor K) (Discrete.mk a)) ≫ f =
        (HomologicalComplex.eval AddCommGrpCat (ComplexShape.down ℕ) i).map
          (colimit.ι (Discrete.functor K) (Discrete.mk a)) ≫ g) : f = g := by
  rw [← cancel_epi (evalCoproductIso K i).inv]
  apply colimit.hom_ext
  rintro ⟨a⟩
  unfold evalCoproductIso
  simpa only [ι_preservesColimitIso_inv_assoc] using h a

public theorem coproductDegreeMap_eq_zero (i j : ℕ)
    (u : ∀ a, (K a).X i ⟶ (K a).X j)
    (hu : ∀ a, u a = 0) : coproductDegreeMap K i j u = 0 := by
  apply coproduct_hom_ext K i
  intro a
  change (Sigma.ι K a).f i ≫ coproductDegreeMap K i j u =
    (Sigma.ι K a).f i ≫ 0
  rw [ι_coproductDegreeMap, hu, zero_comp, comp_zero]

public noncomputable def coproductChainMap
    (f : ∀ a, K a ⟶ K a) : (∐ K) ⟶ (∐ K) :=
  Sigma.desc fun a ↦ f a ≫ Sigma.ι K a

@[reassoc]
public theorem ι_coproductChainMap (f : ∀ a, K a ⟶ K a) (a : α) :
    Sigma.ι K a ≫ coproductChainMap K f = f a ≫ Sigma.ι K a := by
  unfold coproductChainMap
  rw [Sigma.ι_desc]

variable {β : Type}

/-- A chain map between coproducts induced by a map of index types and a chain map on each
source summand. -/
public noncomputable def coproductReindexChainMap
    (K : α → ChainComplex AddCommGrpCat ℕ)
    (M : β → ChainComplex AddCommGrpCat ℕ)
    (r : α → β) (u : ∀ a, K a ⟶ M (r a)) :
    (∐ K) ⟶ (∐ M) :=
  Sigma.desc fun a ↦ u a ≫ Sigma.ι M (r a)

@[reassoc]
public theorem ι_coproductReindexChainMap
    (K : α → ChainComplex AddCommGrpCat ℕ)
    (M : β → ChainComplex AddCommGrpCat ℕ)
    (r : α → β) (u : ∀ a, K a ⟶ M (r a)) (a : α) :
    Sigma.ι K a ≫ coproductReindexChainMap K M r u =
      u a ≫ Sigma.ι M (r a) := by
  unfold coproductReindexChainMap
  rw [Sigma.ι_desc]

/-- A summandwise natural family of graded maps commutes with the induced map between
coproducts. -/
public theorem coproductDegreeMap_reindex_naturality
    (K : α → ChainComplex AddCommGrpCat ℕ)
    (M : β → ChainComplex AddCommGrpCat ℕ)
    (r : α → β) (u : ∀ a, K a ⟶ M (r a))
    (hK : ∀ a, (K a).X i ⟶ (K a).X j)
    (hM : ∀ b, (M b).X i ⟶ (M b).X j)
    (hnat : ∀ a, (u a).f i ≫ hM (r a) = hK a ≫ (u a).f j) :
    (coproductReindexChainMap K M r u).f i ≫
        coproductDegreeMap M i j hM =
      coproductDegreeMap K i j hK ≫
        (coproductReindexChainMap K M r u).f j := by
  apply coproduct_hom_ext K i
  intro a
  have hu_i := congrArg (fun k ↦ k.f i)
    (ι_coproductReindexChainMap K M r u a)
  have hu_j := congrArg (fun k ↦ k.f j)
    (ι_coproductReindexChainMap K M r u a)
  have hMι := ι_coproductDegreeMap M i j hM (r a)
  have hKι := ι_coproductDegreeMap K i j hK a
  simp only [HomologicalComplex.comp_f] at hu_i hu_j
  change (Sigma.ι K a).f i ≫
      ((coproductReindexChainMap K M r u).f i ≫
        coproductDegreeMap M i j hM) =
    (Sigma.ι K a).f i ≫
      (coproductDegreeMap K i j hK ≫
        (coproductReindexChainMap K M r u).f j)
  calc
    _ = ((Sigma.ι K a).f i ≫
        (coproductReindexChainMap K M r u).f i) ≫
          coproductDegreeMap M i j hM := (Category.assoc _ _ _).symm
    _ = ((u a).f i ≫ (Sigma.ι M (r a)).f i) ≫
          coproductDegreeMap M i j hM :=
      congrArg (fun k ↦ k ≫ coproductDegreeMap M i j hM) hu_i
    _ = (u a).f i ≫ ((Sigma.ι M (r a)).f i ≫
          coproductDegreeMap M i j hM) := Category.assoc _ _ _
    _ = (u a).f i ≫ (hM (r a) ≫ (Sigma.ι M (r a)).f j) :=
      congrArg (fun k ↦ (u a).f i ≫ k) hMι
    _ = ((u a).f i ≫ hM (r a)) ≫ (Sigma.ι M (r a)).f j :=
      (Category.assoc _ _ _).symm
    _ = (hK a ≫ (u a).f j) ≫ (Sigma.ι M (r a)).f j :=
      congrArg (fun k ↦ k ≫ (Sigma.ι M (r a)).f j) (hnat a)
    _ = hK a ≫ ((u a).f j ≫ (Sigma.ι M (r a)).f j) :=
      Category.assoc _ _ _
    _ = hK a ≫ ((Sigma.ι K a).f j ≫
          (coproductReindexChainMap K M r u).f j) :=
      congrArg (fun k ↦ hK a ≫ k) hu_j.symm
    _ = (hK a ≫ (Sigma.ι K a).f j) ≫
          (coproductReindexChainMap K M r u).f j :=
      (Category.assoc _ _ _).symm
    _ = ((Sigma.ι K a).f i ≫ coproductDegreeMap K i j hK) ≫
          (coproductReindexChainMap K M r u).f j :=
      congrArg (fun k ↦ k ≫ (coproductReindexChainMap K M r u).f j) hKι.symm
    _ = _ := Category.assoc _ _ _

public noncomputable def coproductHomotopy
    (f g : ∀ a, K a ⟶ K a) (h : ∀ a, Homotopy (f a) (g a)) :
    Homotopy (coproductChainMap K f) (coproductChainMap K g) where
  hom i j := coproductDegreeMap K i j (fun a ↦ (h a).hom i j)
  zero i j hij := coproductDegreeMap_eq_zero K i j _ (fun a ↦ (h a).zero i j hij)
  comm i := by
    apply coproduct_hom_ext K i
    intro a
    change (Sigma.ι K a).f i ≫ _ = (Sigma.ι K a).f i ≫ _
    rw [Preadditive.comp_add, Preadditive.comp_add]
    rw [← HomologicalComplex.comp_f, ι_coproductChainMap,
      HomologicalComplex.comp_f]
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, comp_zero,
        Homotopy.prevD_chainComplex, zero_add]
      rw [← Category.assoc, ι_coproductDegreeMap]
      rw [Category.assoc, HomologicalComplex.Hom.comm]
      have hg := congrArg (fun k ↦ k.f 0) (ι_coproductChainMap K g a)
      simp only [HomologicalComplex.comp_f] at hg ⊢
      rw [hg]
      have hc := (h a).comm 0
      rw [Homotopy.dNext_zero_chainComplex, zero_add,
        Homotopy.prevD_chainComplex] at hc
      have hcpost := congrArg (fun k ↦ k ≫ (Sigma.ι K a).f 0) hc
      rw [Preadditive.add_comp] at hcpost
      simpa only [Category.assoc] using hcpost
    | succ i =>
      rw [Homotopy.dNext_succ_chainComplex,
        Homotopy.prevD_chainComplex]
      rw [← Category.assoc, HomologicalComplex.Hom.comm]
      rw [Category.assoc, ι_coproductDegreeMap]
      rw [ι_coproductDegreeMap_assoc]
      rw [HomologicalComplex.Hom.comm]
      have hg := congrArg (fun k ↦ k.f (i + 1)) (ι_coproductChainMap K g a)
      simp only [HomologicalComplex.comp_f] at hg ⊢
      rw [hg]
      have hc := (h a).comm (i + 1)
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hc
      have hcpost := congrArg
        (fun k ↦ k ≫ (Sigma.ι K a).f (i + 1)) hc
      rw [Preadditive.add_comp, Preadditive.add_comp] at hcpost
      simpa only [Category.assoc] using hcpost

variable {A : FourPieceStarGluingData}

public noncomputable def localRealizationHom
    (L : SectionSevenStarIntersectionChainModels A) {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) :
    L.model a.intersectionIndex ⟶
      (singularIntersectionModels A).model a.intersectionIndex :=
  (L.realization a.intersectionIndex).hom

public noncomputable def localRealizationInv
    (L : SectionSevenStarIntersectionChainModels A) {n : SimplexCategoryᵒᵖ}
    (a : CechTuple n) :
    (singularIntersectionModels A).model a.intersectionIndex ⟶
      L.model a.intersectionIndex :=
  (L.realization a.intersectionIndex).inv

public theorem realizationHomInv_eq_coproductChainMap
    (L : SectionSevenStarIntersectionChainModels A) (n : SimplexCategoryᵒᵖ) :
    L.realizationHom.app n ≫ L.realizationInv.app n =
      coproductChainMap
        (fun a : CechTuple n ↦ L.model a.intersectionIndex)
        (fun a ↦ localRealizationHom L a ≫ localRealizationInv L a) := by
  dsimp [realizationHom, realizationInv, naturalTransformationOfFaces,
    localCechChainSimplicialObject]
  apply Sigma.hom_ext
  intro a
  dsimp [coproductChainMap]
  have hm :
      Sigma.ι
          (fun b : CechTuple n ↦
            (singularIntersectionModels A).model b.intersectionIndex) a ≫
          Sigma.desc (fun b ↦ localRealizationInv L b ≫
            Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) =
        localRealizationInv L a ≫
          Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) a := by
    rw [Sigma.ι_desc]
  have hh :
      Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫
          Sigma.desc (fun b ↦ localRealizationHom L b ≫
            Sigma.ι (fun c : CechTuple n ↦
              (singularIntersectionModels A).model c.intersectionIndex) b) =
        localRealizationHom L a ≫
          Sigma.ι (fun c : CechTuple n ↦
            (singularIntersectionModels A).model c.intersectionIndex) a := by
    rw [Sigma.ι_desc]
  have hr :
      Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫
          Sigma.desc (fun b ↦
            (localRealizationHom L b ≫ localRealizationInv L b) ≫
              Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) =
        (localRealizationHom L a ≫ localRealizationInv L a) ≫
          Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) a := by
    rw [Sigma.ι_desc]
  simp only [localRealizationHom] at hh
  rw [← Category.assoc]
  rw [hh]
  rw [show (L.realization a.intersectionIndex).hom =
    localRealizationHom L a by rfl]
  have hdesc :
      Sigma.desc (fun b : CechTuple n ↦
          (L.realization b.intersectionIndex).inv ≫
            Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) =
        Sigma.desc (fun b ↦ localRealizationInv L b ≫
          Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) := rfl
  have hleft :
      (localRealizationHom L a ≫
          Sigma.ι (fun b : CechTuple n ↦
            (singularIntersectionModels A).model b.intersectionIndex) a) ≫
          Sigma.desc (fun b ↦ localRealizationInv L b ≫
            Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) =
        (localRealizationHom L a ≫ localRealizationInv L a) ≫
          Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) a := by
    rw [Category.assoc, hm, ← Category.assoc]
  have hleftRaw :
      (localRealizationHom L a ≫
          Sigma.ι (fun b : CechTuple n ↦
            (singularIntersectionModels A).model b.intersectionIndex) a) ≫
          Sigma.desc (fun b ↦ (L.realization b.intersectionIndex).inv ≫
            Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) b) =
        (localRealizationHom L a ≫ localRealizationInv L a) ≫
          Sigma.ι (fun c : CechTuple n ↦ L.model c.intersectionIndex) a :=
    (congrArg
      (fun k ↦ (localRealizationHom L a ≫
        Sigma.ι (fun b : CechTuple n ↦
          (singularIntersectionModels A).model b.intersectionIndex) a) ≫ k) hdesc).trans hleft
  rw [hleftRaw, hr]

public theorem id_eq_coproductChainMap
    (L : SectionSevenStarIntersectionChainModels A) (n : SimplexCategoryᵒᵖ) :
    (𝟙 L.localCechChainSimplicialObject.obj n) =
      coproductChainMap
        (fun a : CechTuple n ↦ L.model a.intersectionIndex)
        (fun _ ↦ 𝟙 _) := by
  dsimp [localCechChainSimplicialObject]
  apply Sigma.hom_ext
  intro a
  rw [Category.comp_id]
  unfold coproductChainMap
  rw [Sigma.ι_desc]
  rw [Category.id_comp]

public noncomputable def realizationHomInvHomotopyAt
    (L : SectionSevenStarIntersectionChainModels A) (n : SimplexCategoryᵒᵖ) :
    Homotopy (L.realizationHom.app n ≫ L.realizationInv.app n)
      (𝟙 L.localCechChainSimplicialObject.obj n) := by
  let H := coproductHomotopy
      (fun a : CechTuple n ↦ L.model a.intersectionIndex)
      (fun a ↦ localRealizationHom L a ≫ localRealizationInv L a)
      (fun _ ↦ 𝟙 _)
      (fun a ↦ (L.realization a.intersectionIndex).homotopyHomInvId)
  refine { hom := H.hom, zero := H.zero, comm := ?_ }
  intro i
  rw [congrArg (fun k ↦ k.f i) (realizationHomInv_eq_coproductChainMap L n),
    congrArg (fun k ↦ k.f i) (id_eq_coproductChainMap L n)]
  exact H.comm i

public theorem realizationHomInvHomotopyAt_hom
    (L : SectionSevenStarIntersectionChainModels A) (n : SimplexCategoryᵒᵖ) (i j : ℕ) :
    (realizationHomInvHomotopyAt L n).hom i j =
      coproductDegreeMap
        (fun a : CechTuple n ↦ L.model a.intersectionIndex) i j
        (fun a ↦
          (L.realization a.intersectionIndex).homotopyHomInvId.hom i j) := by
  rfl

@[reassoc]
public theorem ι_localCechChainSimplicialObject_map
    (L : SectionSevenStarIntersectionChainModels A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (a : CechTuple n) :
    Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫
        L.localCechChainSimplicialObject.map f =
      L.face (CechTuple.intersectionIndex_restrict_subset f a) ≫
        Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex) (a.restrict f) := by
  dsimp [localCechChainSimplicialObject]
  rw [Sigma.ι_desc]

public theorem realizationHomInvHomotopyAt_naturality
    (L : SectionSevenStarIntersectionChainModels A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (i j : ℕ) :
    (L.localCechChainSimplicialObject.map f).f i ≫
        (realizationHomInvHomotopyAt L m).hom i j =
      (realizationHomInvHomotopyAt L n).hom i j ≫
        (L.localCechChainSimplicialObject.map f).f j := by
  rw [realizationHomInvHomotopyAt_hom,
    realizationHomInvHomotopyAt_hom]
  dsimp only [localCechChainSimplicialObject]
  apply coproduct_hom_ext
    (fun a : CechTuple n ↦ L.model a.intersectionIndex) i
  intro a
  change
    (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
        ((L.localCechChainSimplicialObject.map f).f i ≫
          coproductDegreeMap
            (fun b : CechTuple m ↦ L.model b.intersectionIndex) i j
            (fun b ↦
              (L.realization b.intersectionIndex).homotopyHomInvId.hom i j)) =
      (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
        (coproductDegreeMap
            (fun b : CechTuple n ↦ L.model b.intersectionIndex) i j
            (fun b ↦
              (L.realization b.intersectionIndex).homotopyHomInvId.hom i j) ≫
          (L.localCechChainSimplicialObject.map f).f j)
  have hface_i := congrArg (fun k ↦ k.f i)
    (ι_localCechChainSimplicialObject_map L f a)
  have hface_j := congrArg (fun k ↦ k.f j)
    (ι_localCechChainSimplicialObject_map L f a)
  change
    (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
        (L.localCechChainSimplicialObject.map f).f i =
      (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
        (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
          (a.restrict f)).f i at hface_i
  change
    (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f j ≫
        (L.localCechChainSimplicialObject.map f).f j =
      (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f j ≫
        (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
          (a.restrict f)).f j at hface_j
  let Hm := coproductDegreeMap
    (fun b : CechTuple m ↦ L.model b.intersectionIndex) i j
    (fun b ↦ (L.realization b.intersectionIndex).homotopyHomInvId.hom i j)
  let Hn := coproductDegreeMap
    (fun b : CechTuple n ↦ L.model b.intersectionIndex) i j
    (fun b ↦ (L.realization b.intersectionIndex).homotopyHomInvId.hom i j)
  have hnat := L.homotopyHomInvId_naturality
    (CechTuple.intersectionIndex_restrict_subset f a) i j
  have hnatPost := congrArg
    (fun k ↦ k ≫ (Sigma.ι
      (fun b : CechTuple m ↦ L.model b.intersectionIndex) (a.restrict f)).f j) hnat
  change (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
      ((L.localCechChainSimplicialObject.map f).f i ≫ Hm) =
    (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
      (Hn ≫ (L.localCechChainSimplicialObject.map f).f j)
  have hi := ι_coproductDegreeMap
    (fun b : CechTuple m ↦ L.model b.intersectionIndex) i j
    (fun b ↦ (L.realization b.intersectionIndex).homotopyHomInvId.hom i j)
    (a.restrict f)
  have hn := ι_coproductDegreeMap
    (fun b : CechTuple n ↦ L.model b.intersectionIndex) i j
    (fun b ↦ (L.realization b.intersectionIndex).homotopyHomInvId.hom i j) a
  have hface_i_post := congrArg (fun k ↦ k ≫ Hm) hface_i
  have hface_j_pre := congrArg
    (fun k ↦ (L.realization a.intersectionIndex).homotopyHomInvId.hom i j ≫ k)
    hface_j
  have hL :
      (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
          ((L.localCechChainSimplicialObject.map f).f i ≫ Hm) =
        ((L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
            (L.realization (a.restrict f).intersectionIndex).homotopyHomInvId.hom i j) ≫
          (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
            (a.restrict f)).f j := by
    calc
      _ = ((Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
          (L.localCechChainSimplicialObject.map f).f i) ≫ Hm :=
        (Category.assoc _ _ _).symm
      _ = ((L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
          (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
            (a.restrict f)).f i) ≫ Hm := hface_i_post
      _ = (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
          ((Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
            (a.restrict f)).f i ≫ Hm) := Category.assoc _ _ _
      _ = (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f i ≫
          ((L.realization (a.restrict f).intersectionIndex).homotopyHomInvId.hom i j ≫
            (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
              (a.restrict f)).f j) := congrArg _ hi
      _ = _ := (Category.assoc _ _ _).symm
  have hR :
      ((L.realization a.intersectionIndex).homotopyHomInvId.hom i j ≫
          (L.face (CechTuple.intersectionIndex_restrict_subset f a)).f j) ≫
        (Sigma.ι (fun b : CechTuple m ↦ L.model b.intersectionIndex)
          (a.restrict f)).f j =
      (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫
        (Hn ≫ (L.localCechChainSimplicialObject.map f).f j) := by
    change
      (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f i ≫ Hn =
        (L.realization a.intersectionIndex).homotopyHomInvId.hom i j ≫
          (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a).f j at hn
    have hnPost := congrArg
      (fun k ↦ k ≫ (L.localCechChainSimplicialObject.map f).f j) hn
    exact (Category.assoc _ _ _).trans
      (hface_j_pre.symm.trans
        ((Category.assoc _ _ _).symm.trans
          (hnPost.symm.trans (Category.assoc _ _ _))))
  exact hL.trans (hnatPost.trans hR)

public theorem realizationInvHom_eq_coproductChainMap
    (L : SectionSevenStarIntersectionChainModels A)
    (n : SimplexCategoryᵒᵖ) :
    L.realizationInv.app n ≫ L.realizationHom.app n =
      coproductChainMap
        (fun a : CechTuple n ↦
          (singularIntersectionModels A).model a.intersectionIndex)
        (fun a ↦ localRealizationInv L a ≫ localRealizationHom L a) := by
  apply Sigma.hom_ext
  intro a
  have hinv :
      Sigma.ι (fun b : CechTuple n ↦
          (singularIntersectionModels A).model b.intersectionIndex) a ≫
          L.realizationInv.app n =
        localRealizationInv L a ≫
          Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a := by
    dsimp [realizationInv, naturalTransformationOfFaces,
      localCechChainSimplicialObject]
    rw [Sigma.ι_desc]
    rfl
  have hhom :
      Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫
          L.realizationHom.app n =
        localRealizationHom L a ≫
          Sigma.ι (fun b : CechTuple n ↦
            (singularIntersectionModels A).model b.intersectionIndex) a := by
    dsimp [realizationHom, naturalTransformationOfFaces,
      localCechChainSimplicialObject]
    rw [Sigma.ι_desc]
    rfl
  change
    (Sigma.ι (fun b : CechTuple n ↦
        (singularIntersectionModels A).model b.intersectionIndex) a ≫
      L.realizationInv.app n) ≫ L.realizationHom.app n = _
  rw [hinv]
  have hhomPre :
      localRealizationInv L a ≫
          (Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a ≫
            L.realizationHom.app n) =
        localRealizationInv L a ≫
          (localRealizationHom L a ≫
            Sigma.ι (fun b : CechTuple n ↦
              (singularIntersectionModels A).model b.intersectionIndex) a) :=
    congrArg (fun k ↦ localRealizationInv L a ≫ k) hhom
  have hleft :
      (localRealizationInv L a ≫
          Sigma.ι (fun b : CechTuple n ↦ L.model b.intersectionIndex) a) ≫
          L.realizationHom.app n =
        (localRealizationInv L a ≫ localRealizationHom L a) ≫
          Sigma.ι (fun b : CechTuple n ↦
            (singularIntersectionModels A).model b.intersectionIndex) a := by
    exact (Category.assoc _ _ _).trans
      (hhomPre.trans (Category.assoc _ _ _).symm)
  exact hleft.trans
    (ι_coproductChainMap
      (fun b : CechTuple n ↦
        (singularIntersectionModels A).model b.intersectionIndex)
      (fun b ↦ localRealizationInv L b ≫ localRealizationHom L b) a).symm

public theorem singular_id_eq_coproductChainMap
    (A : FourPieceStarGluingData) (n : SimplexCategoryᵒᵖ) :
    (𝟙 (singularIntersectionModels A).localCechChainSimplicialObject.obj n) =
      coproductChainMap
        (fun a : CechTuple n ↦
          (singularIntersectionModels A).model a.intersectionIndex)
        (fun _ ↦ 𝟙 _) := by
  dsimp [localCechChainSimplicialObject]
  apply Sigma.hom_ext
  intro a
  rw [Category.comp_id]
  unfold coproductChainMap
  rw [Sigma.ι_desc]
  rw [Category.id_comp]

public noncomputable def realizationInvHomHomotopyAt
    (L : SectionSevenStarIntersectionChainModels A) (n : SimplexCategoryᵒᵖ) :
    Homotopy (L.realizationInv.app n ≫ L.realizationHom.app n)
      (𝟙 (singularIntersectionModels A).localCechChainSimplicialObject.obj n) := by
  let H := coproductHomotopy
      (fun a : CechTuple n ↦
        (singularIntersectionModels A).model a.intersectionIndex)
      (fun a ↦ localRealizationInv L a ≫ localRealizationHom L a)
      (fun _ ↦ 𝟙 _)
      (fun a ↦ (L.realization a.intersectionIndex).homotopyInvHomId)
  refine { hom := H.hom, zero := H.zero, comm := ?_ }
  intro i
  rw [congrArg (fun k ↦ k.f i)
      (realizationInvHom_eq_coproductChainMap L n),
    congrArg (fun k ↦ k.f i)
      (singular_id_eq_coproductChainMap A n)]
  exact H.comm i

public theorem realizationInvHomHomotopyAt_hom
    (L : SectionSevenStarIntersectionChainModels A)
    (n : SimplexCategoryᵒᵖ) (i j : ℕ) :
    (realizationInvHomHomotopyAt L n).hom i j =
      coproductDegreeMap
        (fun a : CechTuple n ↦
          (singularIntersectionModels A).model a.intersectionIndex) i j
        (fun a ↦
          (L.realization a.intersectionIndex).homotopyInvHomId.hom i j) := by
  rfl

public theorem singularCechMap_eq_coproductReindexChainMap
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) :
    (singularIntersectionModels A).localCechChainSimplicialObject.map f =
      coproductReindexChainMap
        (fun a : CechTuple n ↦
          (singularIntersectionModels A).model a.intersectionIndex)
        (fun b : CechTuple m ↦
          (singularIntersectionModels A).model b.intersectionIndex)
        (fun a ↦ a.restrict f)
        (fun a ↦ (singularIntersectionModels A).face
          (CechTuple.intersectionIndex_restrict_subset f a)) := by
  rfl

public theorem realizationInvHomHomotopyAt_naturality
    (L : SectionSevenStarIntersectionChainModels A)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (i j : ℕ) :
    ((singularIntersectionModels A).localCechChainSimplicialObject.map f).f i ≫
        (realizationInvHomHomotopyAt L m).hom i j =
      (realizationInvHomHomotopyAt L n).hom i j ≫
        ((singularIntersectionModels A).localCechChainSimplicialObject.map f).f j := by
  rw [realizationInvHomHomotopyAt_hom,
    realizationInvHomHomotopyAt_hom,
    singularCechMap_eq_coproductReindexChainMap f]
  apply coproductDegreeMap_reindex_naturality
  intro a
  exact L.homotopyInvHomId_naturality
    (CechTuple.intersectionIndex_restrict_subset f a) i j

/-- The coproduct homotopies from the local realizations are natural for the alternating-face
horizontal differential. -/
public noncomputable def realizationHomInvVerticallyNaturalHomotopy
    (L : SectionSevenStarIntersectionChainModels A) :
    VerticallyNaturalHomotopy
      ((alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationHom ≫
        (alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationInv)
      (𝟙 L.localLerayCechBicomplex) where
  homotopy p := realizationHomInvHomotopyAt L
    (Opposite.op (SimplexCategory.mk p))
  horizontal_naturality {p p'} hpp' i j := by
    have hp : p' + 1 = p := by
      simpa only [ComplexShape.down_Rel] using hpp'
    subst p
    rw [alternatingFaceMapComplex_obj_d]
    unfold AlternatingFaceMapComplex.objD
    have eval_sum (r : ℕ) :
        (∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) •
          L.localCechChainSimplicialObject.δ k).f r =
          ∑ k : Fin (p' + 2),
            ((-1 : ℤ) ^ (k : ℕ) •
              L.localCechChainSimplicialObject.δ k).f r := by
      change (HomologicalComplex.Hom.fAddMonoidHom r)
        (∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) •
          L.localCechChainSimplicialObject.δ k) = _
      rw [map_sum]
      simp only [HomologicalComplex.Hom.fAddMonoidHom_apply]
    rw [eval_sum i, eval_sum j, Preadditive.sum_comp,
      Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [HomologicalComplex.zsmul_f_apply,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    congr 1
    exact realizationHomInvHomotopyAt_naturality L _ i j

/-- The inverse-realization coproduct homotopies are natural for the alternating-face
horizontal differential. -/
public noncomputable def realizationInvHomVerticallyNaturalHomotopy
    (L : SectionSevenStarIntersectionChainModels A) :
    VerticallyNaturalHomotopy
      ((alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationInv ≫
        (alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).map L.realizationHom)
      (𝟙 (singularIntersectionModels A).localLerayCechBicomplex) where
  homotopy p := realizationInvHomHomotopyAt L
    (Opposite.op (SimplexCategory.mk p))
  horizontal_naturality {p p'} hpp' i j := by
    have hp : p' + 1 = p := by
      simpa only [ComplexShape.down_Rel] using hpp'
    subst p
    rw [alternatingFaceMapComplex_obj_d]
    unfold AlternatingFaceMapComplex.objD
    have eval_sum (r : ℕ) :
        (∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) •
          (singularIntersectionModels A).localCechChainSimplicialObject.δ k).f r =
          ∑ k : Fin (p' + 2),
            ((-1 : ℤ) ^ (k : ℕ) •
              (singularIntersectionModels A).localCechChainSimplicialObject.δ k).f r := by
      change (HomologicalComplex.Hom.fAddMonoidHom r)
        (∑ k : Fin (p' + 2), (-1 : ℤ) ^ (k : ℕ) •
          (singularIntersectionModels A).localCechChainSimplicialObject.δ k) = _
      rw [map_sum]
      simp only [HomologicalComplex.Hom.fAddMonoidHom_apply]
    rw [eval_sum i, eval_sum j, Preadditive.sum_comp,
      Preadditive.comp_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [HomologicalComplex.zsmul_f_apply,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    congr 1
    exact realizationInvHomHomotopyAt_naturality L _ i j

/-- The two total homotopies obtained from the face-natural local realization homotopies. -/
public structure TotalRealizationHomotopyCoherence
    (L : SectionSevenStarIntersectionChainModels A) where
  homotopyHomInvId : Homotopy
    (L.totalRealizationHom ≫ L.totalRealizationInv) (𝟙 L.localLerayCechTotal)
  homotopyInvHomId : Homotopy
    (L.totalRealizationInv ≫ L.totalRealizationHom)
      (𝟙 (singularIntersectionLerayCechTotal A))

/-- Face-natural local realization homotopies automatically assemble after taking alternating
faces and totalizing. -/
public noncomputable def totalRealizationHomotopyCoherence
    (L : SectionSevenStarIntersectionChainModels A) :
    TotalRealizationHomotopyCoherence L where
  homotopyHomInvId := by
    let h := (realizationHomInvVerticallyNaturalHomotopy L).totalHomotopy
    refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
    · exact (HomologicalComplex₂.total.map_comp _ _ _).symm
    · exact HomologicalComplex₂.total.map_id _ _
  homotopyInvHomId := by
    let h := (realizationInvHomVerticallyNaturalHomotopy L).totalHomotopy
    refine (Homotopy.ofEq ?_).trans (h.trans (Homotopy.ofEq ?_))
    · exact (HomologicalComplex₂.total.map_comp _ _ _).symm
    · exact HomologicalComplex₂.total.map_id _ _

/-- Face-natural local intersection equivalences assemble into a homotopy equivalence of their
explicit total Čech complexes. -/
public noncomputable def totalRealizationEquiv
    (L : SectionSevenStarIntersectionChainModels A) :
    HomotopyEquiv L.localLerayCechTotal (singularIntersectionLerayCechTotal A) where
  hom := L.totalRealizationHom
  inv := L.totalRealizationInv
  homotopyHomInvId := L.totalRealizationHomotopyCoherence.homotopyHomInvId
  homotopyInvHomId := L.totalRealizationHomotopyCoherence.homotopyInvHomId

end SectionSevenStarIntersectionChainModels

/-- Chain-level matrix data still needed after the integer matrices in
`SectionSevenLerayChainModel` have been verified: a basis identification in every total degree and
the assertion that, in those bases, the actual total differential is the displayed Section 7
differential. -/
public structure SectionSevenMatrixChainIdentification
    {A : FourPieceStarGluingData}
    (L : SectionSevenStarIntersectionChainModels A) where
  degreeIso : ∀ n,
    (sectionSevenLerayChainModel (-1)).X n ≅ L.localLerayCechTotal.X n
  differential_comm : ∀ i j, (ComplexShape.down ℕ).Rel i j →
    (degreeIso i).hom ≫ L.localLerayCechTotal.d i j =
      (sectionSevenLerayChainModel (-1)).d i j ≫ (degreeIso j).hom

namespace SectionSevenMatrixChainIdentification

/-- The degreewise Section 7 basis identifications and the checked differential matrices form an
isomorphism of chain complexes. -/
public noncomputable def chainIso
    {A : FourPieceStarGluingData} {L : SectionSevenStarIntersectionChainModels A}
    (h : SectionSevenMatrixChainIdentification L) :
    sectionSevenLerayChainModel (-1) ≅ L.localLerayCechTotal :=
  HomologicalComplex.Hom.isoOfComponents h.degreeIso h.differential_comm

/-- The matrix chain isomorphism, regarded as the homotopy equivalence used in the final
comparison. -/
public noncomputable def homotopyEquiv
    {A : FourPieceStarGluingData} {L : SectionSevenStarIntersectionChainModels A}
    (h : SectionSevenMatrixChainIdentification L) :
    HomotopyEquiv (sectionSevenLerayChainModel (-1)) L.localLerayCechTotal :=
  HomotopyEquiv.ofIso h.chainIso

end SectionSevenMatrixChainIdentification

/-- Degreewise geometric identification of ordered singular intersection chains with the chain
complex of Mathlib's pullback Čech nerve, including compatibility with every simplicial face and
degeneracy. -/
public structure SectionSevenCechNerveChainIdentification (A : FourPieceStarGluingData) where
  degreeIso : ∀ n,
    (SectionSevenStarIntersectionChainModels.singularIntersectionModels A).localCechChainSimplicialObject.obj n ≅
      (finiteCoverCechChainSimplicialObject (sectionSevenStarOpenCover A).piece).obj n
  naturality : ∀ {n m} (f : n ⟶ m),
    (SectionSevenStarIntersectionChainModels.singularIntersectionModels A).localCechChainSimplicialObject.map f ≫
      (degreeIso m).hom =
      (degreeIso n).hom ≫
        (finiteCoverCechChainSimplicialObject (sectionSevenStarOpenCover A).piece).map f

namespace SectionSevenCechNerveChainIdentification

/-- The degreewise intersection-chain identifications form a natural isomorphism of simplicial
chain complexes. -/
public noncomputable def simplicialIso
    {A : FourPieceStarGluingData} (h : SectionSevenCechNerveChainIdentification A) :
    (SectionSevenStarIntersectionChainModels.singularIntersectionModels A).localCechChainSimplicialObject ≅
      finiteCoverCechChainSimplicialObject (sectionSevenStarOpenCover A).piece :=
  NatIso.ofComponents h.degreeIso h.naturality

/-- Alternating faces and totalization carry the natural Čech-nerve identification to an
isomorphism of total chain complexes. -/
public noncomputable def totalIso
    {A : FourPieceStarGluingData} (h : SectionSevenCechNerveChainIdentification A) :
    SectionSevenStarIntersectionChainModels.singularIntersectionLerayCechTotal A ≅
      finiteCoverLerayCechTotal (sectionSevenStarOpenCover A).piece :=
  (HomologicalComplex₂.totalFunctor AddCommGrpCat (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).mapIso
    ((alternatingFaceMapComplex (ChainComplex AddCommGrpCat ℕ)).mapIso h.simplicialIso)

/-- The canonical Čech-nerve chain isomorphism as a homotopy equivalence. -/
public noncomputable def homotopyEquiv
    {A : FourPieceStarGluingData} (h : SectionSevenCechNerveChainIdentification A) :
    HomotopyEquiv
      (SectionSevenStarIntersectionChainModels.singularIntersectionLerayCechTotal A)
      (finiteCoverLerayCechTotal (sectionSevenStarOpenCover A).piece) :=
  HomotopyEquiv.ofIso h.totalIso

end SectionSevenCechNerveChainIdentification

/-- Exact geometric and matrix inputs identifying the paper's Section 7 complex with the
canonical Leray--Čech total complex of the actual four-piece star cover. -/
public structure SectionSevenPaperCoverIdentification (A : FourPieceStarGluingData) where
  /-- Explicit chain models and face-compatible local realizations for every nonempty
  intersection of star-cover pieces. -/
  localModels : SectionSevenStarIntersectionChainModels A
  /-- Degreewise geometric identification with Mathlib's canonical Čech nerve. -/
  cechNerveChainIdentification : SectionSevenCechNerveChainIdentification A
  /-- The actual total differential is the displayed Section 7 matrix in the chosen bases. -/
  matrixChainIdentification : SectionSevenMatrixChainIdentification localModels

namespace SectionSevenPaperCoverIdentification

/-- Assemble the explicit matrix calculation, coherent local realizations, and canonical Čech
nerve identification into the exact input required by the general Leray-cover comparison. -/
public noncomputable def toLerayCechIdentification
    {A : FourPieceStarGluingData} (h : SectionSevenPaperCoverIdentification A) :
    SectionSevenLerayCechIdentification (GluedSpace A.glueData)
      (sectionSevenStarOpenCover A) where
  identification :=
    h.matrixChainIdentification.homotopyEquiv |>.trans
      (SectionSevenStarIntersectionChainModels.totalRealizationEquiv
        h.localModels) |>.trans
          h.cechNerveChainIdentification.homotopyEquiv

end SectionSevenPaperCoverIdentification

end SphereSixComplex
