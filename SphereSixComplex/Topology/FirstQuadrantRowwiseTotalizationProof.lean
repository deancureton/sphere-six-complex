module

public import SphereSixComplex.Topology.FirstQuadrantColumnFiltrationShortExact
public import SphereSixComplex.Topology.BoundarySevenCechLowAssemblyProof

/-!
# Rowwise quasi-isomorphisms and first-quadrant totalization

This file supplies the degree-local stabilization part of the brutal-filtration proof of
rowwise totalization.  A total degree `n` only contains outer columns at most `n`; consequently
the total of the prefix through `N` agrees with the full total in every degree at most `N`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace SphereSixComplex

/-- Component of the canonical map from a finite outer-column prefix to the original
bicomplex. -/
public noncomputable def firstQuadrantColumnPrefixToOriginalComponent
    (K : FirstQuadrantBicomplex) (N p : ℕ) :
    (firstQuadrantColumnPrefix K N).X p ⟶ K.X p := by
  by_cases hp : p ≤ N
  · exact (firstQuadrantColumnPrefixXIso K N p hp).hom
  · exact 0

@[simp]
public theorem firstQuadrantColumnPrefixToOriginalComponent_of_le
    (K : FirstQuadrantBicomplex) (N p : ℕ) (hp : p ≤ N) :
    firstQuadrantColumnPrefixToOriginalComponent K N p =
      (firstQuadrantColumnPrefixXIso K N p hp).hom := by
  simp [firstQuadrantColumnPrefixToOriginalComponent, hp]

public theorem firstQuadrantColumnPrefixToOriginalComponent_eq_zero
    (K : FirstQuadrantBicomplex) (N p : ℕ) (hp : N < p) :
    firstQuadrantColumnPrefixToOriginalComponent K N p = 0 := by
  simp [firstQuadrantColumnPrefixToOriginalComponent, show ¬ p ≤ N by omega]

/-- Canonical map from a finite outer-column prefix to the original bicomplex. -/
public noncomputable def firstQuadrantColumnPrefixToOriginal
    (K : FirstQuadrantBicomplex) (N : ℕ) :
    firstQuadrantColumnPrefix K N ⟶ K where
  f := firstQuadrantColumnPrefixToOriginalComponent K N
  comm' i j hij := by
    change j + 1 = i at hij
    by_cases hi : i ≤ N
    · have hj : j ≤ N := by omega
      rw [firstQuadrantColumnPrefixToOriginalComponent_of_le K N i hi,
        firstQuadrantColumnPrefixToOriginalComponent_of_le K N j hj,
        firstQuadrantColumnPrefix_d_eq K N i j hi hj]
      simp
    · rw [firstQuadrantColumnPrefixToOriginalComponent_eq_zero K N i (by omega),
        zero_comp]
      exact (firstQuadrantColumnPrefix_isZero_X K N i (by omega)).eq_of_src _ _

/-- Totalization of the canonical map from a finite prefix to the full bicomplex. -/
public noncomputable def firstQuadrantColumnPrefixTotalToOriginal
    (K : FirstQuadrantBicomplex) (N : ℕ) :
    (firstQuadrantColumnPrefix K N).total (ComplexShape.down ℕ) ⟶
      K.total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map (firstQuadrantColumnPrefixToOriginal K N)
    (ComplexShape.down ℕ)

/-- In total degree `n ≤ N`, project the full total back to the prefix total by using the
inverse prefix isomorphism on every antidiagonal summand. -/
public noncomputable def firstQuadrantColumnPrefixTotalToOriginalInverseComponent
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n ≤ N) :
    (K.total (ComplexShape.down ℕ)).X n ⟶
      ((firstQuadrantColumnPrefix K N).total (ComplexShape.down ℕ)).X n :=
  K.totalDesc (fun p q hpq =>
    (firstQuadrantColumnPrefixXIso K N p (by
      change p + q = n at hpq
      omega)).inv.f q ≫
      (firstQuadrantColumnPrefix K N).ιTotal
        (ComplexShape.down ℕ) p q n hpq)

public theorem firstQuadrantColumnPrefixTotalToOriginal_hom_inv
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n ≤ N) :
    (firstQuadrantColumnPrefixTotalToOriginal K N).f n ≫
      firstQuadrantColumnPrefixTotalToOriginalInverseComponent K N n hn =
        𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hp : p ≤ N := by
    change p + q = n at hpq
    omega
  dsimp [firstQuadrantColumnPrefixTotalToOriginal,
    firstQuadrantColumnPrefixTotalToOriginalInverseComponent]
  rw [HomologicalComplex₂.ιTotal_map_assoc]
  change (firstQuadrantColumnPrefixToOriginalComponent K N p).f q ≫ _ = _
  rw [
    firstQuadrantColumnPrefixToOriginalComponent_of_le K N p hp,
    HomologicalComplex₂.ι_totalDesc]
  rw [Category.comp_id, ← Category.assoc]
  have hcancel :
      (firstQuadrantColumnPrefixXIso K N p hp).hom.f q ≫
        (firstQuadrantColumnPrefixXIso K N p hp).inv.f q = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun g ↦ g.f q)
        (firstQuadrantColumnPrefixXIso K N p hp).hom_inv_id
  rw [hcancel, Category.id_comp]

public theorem firstQuadrantColumnPrefixTotalToOriginal_inv_hom
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n ≤ N) :
    firstQuadrantColumnPrefixTotalToOriginalInverseComponent K N n hn ≫
      (firstQuadrantColumnPrefixTotalToOriginal K N).f n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  have hp : p ≤ N := by
    change p + q = n at hpq
    omega
  dsimp [firstQuadrantColumnPrefixTotalToOriginal,
    firstQuadrantColumnPrefixTotalToOriginalInverseComponent]
  rw [HomologicalComplex₂.ι_totalDesc_assoc]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (firstQuadrantColumnPrefixXIso K N p _).inv.f q ≫
    (firstQuadrantColumnPrefixToOriginalComponent K N p).f q ≫ _ = _
  rw [firstQuadrantColumnPrefixToOriginalComponent_of_le K N p hp]
  rw [Category.comp_id, ← Category.assoc]
  have hcancel :
      (firstQuadrantColumnPrefixXIso K N p hp).inv.f q ≫
        (firstQuadrantColumnPrefixXIso K N p hp).hom.f q = 𝟙 _ := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
      congrArg (fun g ↦ g.f q)
        (firstQuadrantColumnPrefixXIso K N p hp).inv_hom_id
  rw [hcancel, Category.id_comp]

/-- The finite-prefix total and full total are isomorphic componentwise through the cutoff. -/
public noncomputable def firstQuadrantColumnPrefixTotalToOriginalComponentIso
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n ≤ N) :
    ((firstQuadrantColumnPrefix K N).total (ComplexShape.down ℕ)).X n ≅
      (K.total (ComplexShape.down ℕ)).X n where
  hom := (firstQuadrantColumnPrefixTotalToOriginal K N).f n
  inv := firstQuadrantColumnPrefixTotalToOriginalInverseComponent K N n hn
  hom_inv_id := firstQuadrantColumnPrefixTotalToOriginal_hom_inv K N n hn
  inv_hom_id := firstQuadrantColumnPrefixTotalToOriginal_inv_hom K N n hn

public theorem firstQuadrantColumnPrefixTotalToOriginal_component_isIso
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n ≤ N) :
    IsIso ((firstQuadrantColumnPrefixTotalToOriginal K N).f n) :=
  (firstQuadrantColumnPrefixTotalToOriginalComponentIso K N n hn).isIso_hom

/-- Once the cutoff contains degree `n + 1`, the prefix-to-full total map is a
quasi-isomorphism in degree `n`.  The extra degree is exactly the incoming differential needed
to compute homology in degree `n`. -/
public theorem firstQuadrantColumnPrefixTotalToOriginal_quasiIsoAt
    (K : FirstQuadrantBicomplex) (N n : ℕ) (hn : n + 1 ≤ N) :
    QuasiIsoAt (firstQuadrantColumnPrefixTotalToOriginal K N) n := by
  rw [quasiIsoAt_iff'
    (firstQuadrantColumnPrefixTotalToOriginal K N)
    (n + 1) n ((ComplexShape.down ℕ).next n) (by simp) rfl]
  let φ := (HomologicalComplex.shortComplexFunctor'
    AddCommGrpCat (ComplexShape.down ℕ)
    (n + 1) n ((ComplexShape.down ℕ).next n)).map
      (firstQuadrantColumnPrefixTotalToOriginal K N)
  have hnext : (ComplexShape.down ℕ).next n ≤ N := by
    rcases n with _ | n
    · simp
    · simp
      omega
  let _ : IsIso φ.τ₁ :=
    firstQuadrantColumnPrefixTotalToOriginal_component_isIso K N (n + 1) hn
  let _ : IsIso φ.τ₂ :=
    firstQuadrantColumnPrefixTotalToOriginal_component_isIso K N n (by omega)
  let _ : IsIso φ.τ₃ :=
    firstQuadrantColumnPrefixTotalToOriginal_component_isIso K N
      ((ComplexShape.down ℕ).next n) hnext
  let _ : IsIso φ := ShortComplex.isIso_of_isIso φ
  change ShortComplex.QuasiIso φ
  infer_instance

@[reassoc]
public theorem firstQuadrantColumnPrefixMap_toOriginal_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (N : ℕ) :
    firstQuadrantColumnPrefixMap f N ≫
      firstQuadrantColumnPrefixToOriginal L N =
    firstQuadrantColumnPrefixToOriginal K N ≫ f := by
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : p ≤ N
  · change (firstQuadrantColumnPrefixMap f N).f p ≫
      firstQuadrantColumnPrefixToOriginalComponent L N p =
        firstQuadrantColumnPrefixToOriginalComponent K N p ≫ f.f p
    rw [firstQuadrantColumnPrefixToOriginalComponent_of_le L N p hp,
      firstQuadrantColumnPrefixToOriginalComponent_of_le K N p hp]
    exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
      f (firstQuadrantColumnPrefixEmbedding N) (i := ⟨p, hp⟩) (i' := p) rfl
  · have hNp : N < p := by omega
    change (firstQuadrantColumnPrefixMap f N).f p ≫
      firstQuadrantColumnPrefixToOriginalComponent L N p =
        firstQuadrantColumnPrefixToOriginalComponent K N p ≫ f.f p
    rw [firstQuadrantColumnPrefixToOriginalComponent_eq_zero L N p hNp,
      firstQuadrantColumnPrefixToOriginalComponent_eq_zero K N p hNp,
      comp_zero, zero_comp]

@[reassoc]
public theorem firstQuadrantColumnPrefixTotalToOriginal_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (N : ℕ) :
    HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
        (ComplexShape.down ℕ) ≫
      firstQuadrantColumnPrefixTotalToOriginal L N =
      firstQuadrantColumnPrefixTotalToOriginal K N ≫
      HomologicalComplex₂.total.map f (ComplexShape.down ℕ) := by
  dsimp only [firstQuadrantColumnPrefixTotalToOriginal]
  rw [← HomologicalComplex₂.total.map_comp,
    ← HomologicalComplex₂.total.map_comp]
  exact congrArg
    (fun g => HomologicalComplex₂.total.map g (ComplexShape.down ℕ))
    (firstQuadrantColumnPrefixMap_toOriginal_naturality f N)

/-- A quasi-isomorphism on one sufficiently large finite prefix induces a
quasi-isomorphism of full totals in the requested degree. -/
public theorem firstQuadrantTotal_quasiIsoAt_of_prefix
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (N n : ℕ)
    (hn : n + 1 ≤ N)
    (hprefix : QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
        (ComplexShape.down ℕ))) :
    QuasiIsoAt (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n := by
  let _ : QuasiIsoAt
      (firstQuadrantColumnPrefixTotalToOriginal K N) n :=
    firstQuadrantColumnPrefixTotalToOriginal_quasiIsoAt K N n hn
  let _ : QuasiIsoAt
      (firstQuadrantColumnPrefixTotalToOriginal L N) n :=
    firstQuadrantColumnPrefixTotalToOriginal_quasiIsoAt L N n hn
  let _ : QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
        (ComplexShape.down ℕ)) := hprefix
  have hcomp : QuasiIsoAt
      (firstQuadrantColumnPrefixTotalToOriginal K N ≫
        HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n := by
    rw [← firstQuadrantColumnPrefixTotalToOriginal_naturality f N]
    infer_instance
  exact quasiIsoAt_of_comp_left
    (firstQuadrantColumnPrefixTotalToOriginal K N)
    (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) n

/-- If a bicomplex map is a quasi-isomorphism after totalizing every finite column prefix,
then it is a quasi-isomorphism after full first-quadrant totalization. -/
public theorem firstQuadrantTotal_quasiIso_of_all_prefixes
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hprefix : ∀ N : ℕ, QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
        (ComplexShape.down ℕ))) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  rw [quasiIso_iff]
  intro n
  exact firstQuadrantTotal_quasiIsoAt_of_prefix f (n + 1) n le_rfl (hprefix (n + 1))

/-- The map between bicomplexes concentrated in one outer column induced by a bicomplex map. -/
public noncomputable def firstQuadrantSingleColumnMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    firstQuadrantSingleColumn K p ⟶ firstQuadrantSingleColumn L p :=
  (HomologicalComplex.single (ChainComplex AddCommGrpCat ℕ)
    (ComplexShape.down ℕ) p).map (f.f p)

/-- Projection from a total supported in outer column `p` to its sole summand in
total degree `p + q`. -/
public noncomputable def firstQuadrantSingleColumnTotalXHom
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X (p + q) ⟶
      (K.X p).X q :=
  (firstQuadrantSingleColumn K p).totalDesc (fun r s hrs => by
    by_cases hr : r = p
    · subst r
      have hs : s = q := by
        change p + s = p + q at hrs
        omega
      subst s
      exact (firstQuadrantSingleColumnXIso K p).hom.f q
    · exact 0)

/-- Inclusion of the sole summand of a single-column total. -/
public noncomputable def firstQuadrantSingleColumnTotalXInv
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    (K.X p).X q ⟶
      ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X (p + q) :=
  (firstQuadrantSingleColumnXIso K p).inv.f q ≫
    (firstQuadrantSingleColumn K p).ιTotal
      (ComplexShape.down ℕ) p q (p + q) rfl

public theorem firstQuadrantSingleColumnTotalXHom_inv
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    firstQuadrantSingleColumnTotalXHom K p q ≫
      firstQuadrantSingleColumnTotalXInv K p q = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  by_cases hr : r = p
  · subst r
    have hs : s = q := by
      change p + s = p + q at hrs
      omega
    subst s
    dsimp [firstQuadrantSingleColumnTotalXHom,
      firstQuadrantSingleColumnTotalXInv]
    rw [HomologicalComplex₂.ι_totalDesc_assoc]
    simp only [dite_true, Category.comp_id]
    rw [← Category.assoc]
    have hcancel :
        (firstQuadrantSingleColumnXIso K p).hom.f q ≫
          (firstQuadrantSingleColumnXIso K p).inv.f q = 𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        congrArg (fun g ↦ g.f q) (firstQuadrantSingleColumnXIso K p).hom_inv_id
    rw [hcancel, Category.id_comp]
  · have hz : IsZero (((firstQuadrantSingleColumn K p).X r).X s) :=
      (HomologicalComplex.eval AddCommGrpCat
        (ComplexShape.down ℕ) s).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) p (K.X p) r hr)
    exact hz.eq_of_src _ _

public theorem firstQuadrantSingleColumnTotalXInv_hom
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    firstQuadrantSingleColumnTotalXInv K p q ≫
      firstQuadrantSingleColumnTotalXHom K p q = 𝟙 _ := by
  dsimp [firstQuadrantSingleColumnTotalXHom,
    firstQuadrantSingleColumnTotalXInv]
  rw [Category.assoc, HomologicalComplex₂.ι_totalDesc]
  simp only [dite_true]
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
    congrArg (fun g ↦ g.f q) (firstQuadrantSingleColumnXIso K p).inv_hom_id

/-- In degree `p + q`, a total supported in outer column `p` is canonically its sole
summand in inner degree `q`. -/
public noncomputable def firstQuadrantSingleColumnTotalXIso
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X (p + q) ≅
      (K.X p).X q where
  hom := firstQuadrantSingleColumnTotalXHom K p q
  inv := firstQuadrantSingleColumnTotalXInv K p q
  hom_inv_id := firstQuadrantSingleColumnTotalXHom_inv K p q
  inv_hom_id := firstQuadrantSingleColumnTotalXInv_hom K p q

/-- Under the sole-summand identification, the differential on the total supported in
outer column `p` is the vertical differential multiplied by the total-complex sign at `p`. -/
public theorem firstQuadrantSingleColumnTotalXIso_d
    (K : FirstQuadrantBicomplex) (p i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).d
        (p + i) (p + j) ≫
      (firstQuadrantSingleColumnTotalXIso K p j).hom =
    (ComplexShape.down ℕ).ε p •
      ((firstQuadrantSingleColumnTotalXIso K p i).hom ≫ (K.X p).d i j) := by
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  by_cases hr : r = p
  · subst r
    have hs : s = i := by
      change p + s = p + i at hrs
      omega
    subst s
    rw [Linear.comp_units_smul]
    dsimp only [HomologicalComplex₂.total_d]
    rw [← Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    have hd₁ : (firstQuadrantSingleColumn K p).d₁
        (ComplexShape.down ℕ) p i (p + j) = 0 := by
      unfold HomologicalComplex₂.d₁ HomologicalComplex₂.toGradedObject
        firstQuadrantSingleColumn
      rw [HomologicalComplex.single_obj_d, HomologicalComplex.zero_f,
        zero_comp, smul_zero]
    rw [hd₁, zero_add]
    rw [HomologicalComplex₂.d₂_eq
      (firstQuadrantSingleColumn K p) (ComplexShape.down ℕ)
      p hij (p + j) (by
        change p + j = p + j
        rfl)]
    dsimp [firstQuadrantSingleColumnTotalXIso,
      firstQuadrantSingleColumnTotalXHom]
    rw [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex₂.ι_totalDesc]
    simp
  · have hz : IsZero (((firstQuadrantSingleColumn K p).X r).X s) :=
      (HomologicalComplex.eval AddCommGrpCat
        (ComplexShape.down ℕ) s).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) p (K.X p) r hr)
    exact hz.eq_of_src _ _

/-- The sign-twisted sole-summand identification which removes the constant vertical sign
from a total supported in outer column `p`. -/
public noncomputable def firstQuadrantSingleColumnTotalScaledXIso
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X (p + q) ≅
      (K.X p).X q :=
  ((ComplexShape.down ℕ).ε p) ^ q •
    firstQuadrantSingleColumnTotalXIso K p q

/-- The scaled sole-summand identifications commute with the differentials. -/
public theorem firstQuadrantSingleColumnTotalScaledXIso_d
    (K : FirstQuadrantBicomplex) (p i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (firstQuadrantSingleColumnTotalScaledXIso K p i).hom ≫ (K.X p).d i j =
      ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).d
          (p + i) (p + j) ≫
        (firstQuadrantSingleColumnTotalScaledXIso K p j).hom := by
  change j + 1 = i at hij
  subst i
  change (((ComplexShape.down ℕ).ε p) ^ (j + 1) •
      (firstQuadrantSingleColumnTotalXIso K p (j + 1)).hom) ≫ _ =
    _ ≫ (((ComplexShape.down ℕ).ε p) ^ j •
      (firstQuadrantSingleColumnTotalXIso K p j).hom)
  rw [Linear.units_smul_comp, Linear.comp_units_smul,
    firstQuadrantSingleColumnTotalXIso_d K p (j + 1) j (by simp), smul_smul,
    pow_succ]

/-- Embed inner degree `q` as total degree `p + q`. -/
public abbrev firstQuadrantColumnDegreeEmbedding (p : ℕ) :
    (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) where
  f q := p + q
  injective_f := fun _ _ h => Nat.add_left_cancel h
  rel := by
    intro i j hij
    change j + 1 = i at hij
    change p + j + 1 = p + i
    omega

/-- Naturality of the unscaled sole-summand identification. -/
public theorem firstQuadrantSingleColumnTotalXIso_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p q : ℕ) :
    (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ)).f (p + q) ≫
      (firstQuadrantSingleColumnTotalXIso L p q).hom =
    (firstQuadrantSingleColumnTotalXIso K p q).hom ≫ (f.f p).f q := by
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  by_cases hr : r = p
  · subst r
    have hs : s = q := by
      change p + s = p + q at hrs
      omega
    subst s
    dsimp [firstQuadrantSingleColumnTotalXIso,
      firstQuadrantSingleColumnTotalXHom]
    rw [HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex₂.ι_totalDesc,
      HomologicalComplex₂.ι_totalDesc_assoc]
    dsimp [firstQuadrantSingleColumnMap,
      firstQuadrantSingleColumnXIso]
    rw [HomologicalComplex.single_map_f_self]
    simp only [HomologicalComplex.comp_f, ite_true]
    rw [Category.assoc, Category.assoc]
    have hcancel :
        (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) p (L.X p)).inv.f q ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) p (L.X p)).hom.f q =
            𝟙 _ := by
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f] using
        congrArg (fun g ↦ g.f q)
          (HomologicalComplex.singleObjXSelf
            (ComplexShape.down ℕ) p (L.X p)).inv_hom_id
    rw [hcancel, Category.comp_id]
  · have hz : IsZero (((firstQuadrantSingleColumn K p).X r).X s) :=
      (HomologicalComplex.eval AddCommGrpCat
        (ComplexShape.down ℕ) s).map_isZero
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) p (K.X p) r hr)
    exact hz.eq_of_src _ _

/-- Naturality of the sign-twisted sole-summand identification. -/
public theorem firstQuadrantSingleColumnTotalScaledXIso_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p q : ℕ) :
    (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ)).f (p + q) ≫
      (firstQuadrantSingleColumnTotalScaledXIso L p q).hom =
    (firstQuadrantSingleColumnTotalScaledXIso K p q).hom ≫ (f.f p).f q := by
  change _ ≫ (((ComplexShape.down ℕ).ε p) ^ q •
      (firstQuadrantSingleColumnTotalXIso L p q).hom) =
    (((ComplexShape.down ℕ).ε p) ^ q •
      (firstQuadrantSingleColumnTotalXIso K p q).hom) ≫ _
  rw [Linear.comp_units_smul, Linear.units_smul_comp,
    firstQuadrantSingleColumnTotalXIso_naturality]

/-- Outside degrees `p + q`, the total supported in column `p` is zero. -/
public theorem firstQuadrantSingleColumnTotalX_isZero_of_not_exists
    (K : FirstQuadrantBicomplex) (p n : ℕ)
    (hn : ∀ q : ℕ, p + q ≠ n) :
    IsZero (((firstQuadrantSingleColumn K p).total
      (ComplexShape.down ℕ)).X n) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex₂.total.hom_ext
  intro r s hrs
  rw [Category.comp_id, comp_zero]
  have hr : r ≠ p := by
    intro hr
    subst r
    exact hn s hrs
  have hz : IsZero (((firstQuadrantSingleColumn K p).X r).X s) :=
    (HomologicalComplex.eval AddCommGrpCat
      (ComplexShape.down ℕ) s).map_isZero
      (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) p (K.X p) r hr)
  exact hz.eq_of_src _ _

/-- The component isomorphism from a single-column total to the extension-by-zero of its
sole column, when the total degree is explicitly `p + q`. -/
public noncomputable def firstQuadrantSingleColumnTotalExtendedXIsoOfEq
    (K : FirstQuadrantBicomplex) (p q n : ℕ) (h : p + q = n) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X n ≅
      ((K.X p).extend (firstQuadrantColumnDegreeEmbedding p)).X n :=
  (((firstQuadrantSingleColumn K p).total
      (ComplexShape.down ℕ)).XIsoOfEq h).symm ≪≫
    firstQuadrantSingleColumnTotalScaledXIso K p q ≪≫
    ((K.X p).extendXIso (firstQuadrantColumnDegreeEmbedding p) h).symm

/-- Componentwise comparison of a single-column total with the extension-by-zero of its
sole column. -/
public noncomputable def firstQuadrantSingleColumnTotalExtendedXIso
    (K : FirstQuadrantBicomplex) (p n : ℕ) :
    ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).X n ≅
      ((K.X p).extend (firstQuadrantColumnDegreeEmbedding p)).X n := by
  by_cases hn : p ≤ n
  · exact firstQuadrantSingleColumnTotalExtendedXIsoOfEq K p
      (n - p) n (by omega)
  · exact
      (firstQuadrantSingleColumnTotalX_isZero_of_not_exists K p n
        (by intro q h; omega)).isoZero ≪≫
      ((K.X p).isZero_extend_X (firstQuadrantColumnDegreeEmbedding p) n
        (by
          intro q h
          apply hn
          change p + q = n at h
          omega)).isoZero.symm

public theorem firstQuadrantSingleColumnTotalExtendedXIso_eq
    (K : FirstQuadrantBicomplex) (p q n : ℕ) (h : p + q = n) :
    firstQuadrantSingleColumnTotalExtendedXIso K p n =
      firstQuadrantSingleColumnTotalExtendedXIsoOfEq K p q n h := by
  subst n
  simp [firstQuadrantSingleColumnTotalExtendedXIso]

/-- The extended component comparisons commute with differentials between degrees in the
image of the degree embedding. -/
public theorem firstQuadrantSingleColumnTotalExtendedXIsoOfEq_d
    (K : FirstQuadrantBicomplex) (p i j n m : ℕ)
    (hi : p + i = n) (hj : p + j = m)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (firstQuadrantSingleColumnTotalExtendedXIsoOfEq K p i n hi).hom ≫
        ((K.X p).extend (firstQuadrantColumnDegreeEmbedding p)).d n m =
      ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).d n m ≫
        (firstQuadrantSingleColumnTotalExtendedXIsoOfEq K p j m hj).hom := by
  subst n
  subst m
  dsimp [firstQuadrantSingleColumnTotalExtendedXIsoOfEq]
  rw [(K.X p).extend_d_eq (firstQuadrantColumnDegreeEmbedding p) rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Category.id_comp]
  rw [← Category.assoc,
    firstQuadrantSingleColumnTotalScaledXIso_d K p i j hij]
  rw [Category.assoc]

/-- The componentwise comparisons commute with all differentials, including the lower
boundary where extension by zero supplies the missing target degree. -/
public theorem firstQuadrantSingleColumnTotalExtendedXIso_d
    (K : FirstQuadrantBicomplex) (p n m : ℕ)
    (hnm : (ComplexShape.down ℕ).Rel n m) :
    (firstQuadrantSingleColumnTotalExtendedXIso K p n).hom ≫
        ((K.X p).extend (firstQuadrantColumnDegreeEmbedding p)).d n m =
      ((firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ)).d n m ≫
        (firstQuadrantSingleColumnTotalExtendedXIso K p m).hom := by
  change m + 1 = n at hnm
  by_cases hn : p ≤ n
  · let q := n - p
    have hnq : p + q = n := by
      dsimp [q]
      omega
    by_cases hq : q = 0
    · have hm : m < p := by omega
      have hz : IsZero
          (((K.X p).extend (firstQuadrantColumnDegreeEmbedding p)).X m) :=
        (K.X p).isZero_extend_X (firstQuadrantColumnDegreeEmbedding p) m (by
          intro r hr
          change p + r = m at hr
          omega)
      exact hz.eq_of_tgt _ _
    · let j := q - 1
      have hjq : j + 1 = q := by
        dsimp [j]
        omega
      have hmj : p + j = m := by omega
      rw [firstQuadrantSingleColumnTotalExtendedXIso_eq K p q n hnq,
        firstQuadrantSingleColumnTotalExtendedXIso_eq K p j m hmj]
      exact firstQuadrantSingleColumnTotalExtendedXIsoOfEq_d
        K p q j n m hnq hmj (by
          change j + 1 = q
          exact hjq)
  · have hz : IsZero
        (((firstQuadrantSingleColumn K p).total
          (ComplexShape.down ℕ)).X n) :=
      firstQuadrantSingleColumnTotalX_isZero_of_not_exists K p n (by
        intro q h
        apply hn
        omega)
    exact hz.eq_of_src _ _

/-- A total supported in one outer column is the extension by zero of that column, with
the canonical Koszul untwisting signs. -/
public noncomputable def firstQuadrantSingleColumnTotalExtendedIso
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    (firstQuadrantSingleColumn K p).total (ComplexShape.down ℕ) ≅
      (K.X p).extend (firstQuadrantColumnDegreeEmbedding p) :=
  HomologicalComplex.Hom.isoOfComponents
    (firstQuadrantSingleColumnTotalExtendedXIso K p)
    (firstQuadrantSingleColumnTotalExtendedXIso_d K p)

/-- Naturality of the extended comparison in a degree explicitly in the image. -/
public theorem firstQuadrantSingleColumnTotalExtendedXIsoOfEq_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p q n : ℕ)
    (h : p + q = n) :
    (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ)).f n ≫
      (firstQuadrantSingleColumnTotalExtendedXIsoOfEq L p q n h).hom =
    (firstQuadrantSingleColumnTotalExtendedXIsoOfEq K p q n h).hom ≫
      (HomologicalComplex.extendMap (f.f p)
        (firstQuadrantColumnDegreeEmbedding p)).f n := by
  subst n
  dsimp [firstQuadrantSingleColumnTotalExtendedXIsoOfEq]
  rw [HomologicalComplex.extendMap_f (f.f p)
    (firstQuadrantColumnDegreeEmbedding p) rfl]
  simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc,
    firstQuadrantSingleColumnTotalScaledXIso_naturality,
    Category.assoc]

/-- Naturality of the componentwise extended comparison in every total degree. -/
public theorem firstQuadrantSingleColumnTotalExtendedXIso_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p n : ℕ) :
    (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ)).f n ≫
      (firstQuadrantSingleColumnTotalExtendedXIso L p n).hom =
    (firstQuadrantSingleColumnTotalExtendedXIso K p n).hom ≫
      (HomologicalComplex.extendMap (f.f p)
        (firstQuadrantColumnDegreeEmbedding p)).f n := by
  by_cases hn : p ≤ n
  · let q := n - p
    have h : p + q = n := by
      dsimp [q]
      omega
    rw [firstQuadrantSingleColumnTotalExtendedXIso_eq L p q n h,
      firstQuadrantSingleColumnTotalExtendedXIso_eq K p q n h]
    exact firstQuadrantSingleColumnTotalExtendedXIsoOfEq_naturality f p q n h
  · have hz : IsZero
        (((firstQuadrantSingleColumn K p).total
          (ComplexShape.down ℕ)).X n) :=
      firstQuadrantSingleColumnTotalX_isZero_of_not_exists K p n (by
        intro q h
        apply hn
        omega)
    exact hz.eq_of_src _ _

/-- Naturality of the single-column total/extension chain isomorphism. -/
@[reassoc]
public theorem firstQuadrantSingleColumnTotalExtendedIso_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ) ≫
      (firstQuadrantSingleColumnTotalExtendedIso L p).hom =
    (firstQuadrantSingleColumnTotalExtendedIso K p).hom ≫
      HomologicalComplex.extendMap (f.f p)
        (firstQuadrantColumnDegreeEmbedding p) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact firstQuadrantSingleColumnTotalExtendedXIso_naturality f p n

/-- A quasi-isomorphism on the sole column remains a quasi-isomorphism after placing that
column in any outer degree and totalizing. -/
public theorem firstQuadrantSingleColumnTotal_quasiIso
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ)
    (hcolumn : QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map
      (firstQuadrantSingleColumnMap f p) (ComplexShape.down ℕ)) := by
  let a := HomologicalComplex₂.total.map
    (firstQuadrantSingleColumnMap f p) (ComplexShape.down ℕ)
  let b := (firstQuadrantSingleColumnTotalExtendedIso L p).hom
  let c := (firstQuadrantSingleColumnTotalExtendedIso K p).hom
  let d := HomologicalComplex.extendMap (f.f p)
    (firstQuadrantColumnDegreeEmbedding p)
  let _ : IsIso b := by dsimp [b]; infer_instance
  let _ : IsIso c := by dsimp [c]; infer_instance
  let _ : QuasiIso (f.f p) := hcolumn
  let _ : QuasiIso d := by
    dsimp [d]
    infer_instance
  let _ : QuasiIso (a ≫ b) := by
    rw [show a ≫ b = c ≫ d from
      firstQuadrantSingleColumnTotalExtendedIso_naturality f p]
    infer_instance
  exact quasiIso_of_comp_right a b

@[reassoc]
public theorem firstQuadrantColumnPrefixMap_XIso_hom
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (N p : ℕ) (hp : p ≤ N) :
    (firstQuadrantColumnPrefixMap f N).f p ≫
      (firstQuadrantColumnPrefixXIso L N p hp).hom =
    (firstQuadrantColumnPrefixXIso K N p hp).hom ≫ f.f p := by
  dsimp only [firstQuadrantColumnPrefixMap, firstQuadrantColumnPrefixXIso,
    firstQuadrantColumnPrefix]
  exact HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom
    f (firstQuadrantColumnPrefixEmbedding N)
    (i := ⟨p, hp⟩) (i' := p) rfl

@[reassoc]
public theorem firstQuadrantColumnPrefixSuccInclusion_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    firstQuadrantColumnPrefixMap f p ≫
      firstQuadrantColumnPrefixSuccInclusion L p =
    firstQuadrantColumnPrefixSuccInclusion K p ≫
      firstQuadrantColumnPrefixMap f (p + 1) := by
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hq : q ≤ p
  · change (firstQuadrantColumnPrefixMap f p).f q ≫
      firstQuadrantColumnPrefixSuccInclusionComponent L p q =
        firstQuadrantColumnPrefixSuccInclusionComponent K p q ≫
          (firstQuadrantColumnPrefixMap f (p + 1)).f q
    rw [firstQuadrantColumnPrefixSuccInclusionComponent_of_le L p q hq,
      firstQuadrantColumnPrefixSuccInclusionComponent_of_le K p q hq]
    rw [← Category.assoc,
      firstQuadrantColumnPrefixMap_XIso_hom f p q hq]
    rw [Category.assoc, Category.assoc]
    apply (cancel_mono
      (firstQuadrantColumnPrefixXIso L (p + 1) q (by omega)).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [firstQuadrantColumnPrefixMap_XIso_hom f (p + 1) q (by omega)]
    simp
  · have hpq : p < q := by omega
    change (firstQuadrantColumnPrefixMap f p).f q ≫
      firstQuadrantColumnPrefixSuccInclusionComponent L p q =
        firstQuadrantColumnPrefixSuccInclusionComponent K p q ≫
          (firstQuadrantColumnPrefixMap f (p + 1)).f q
    rw [firstQuadrantColumnPrefixSuccInclusionComponent_eq_zero L p q hpq,
      firstQuadrantColumnPrefixSuccInclusionComponent_eq_zero K p q hpq,
      comp_zero, zero_comp]

@[reassoc]
public theorem firstQuadrantColumnPrefixToLast_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    firstQuadrantColumnPrefixMap f p ≫
      firstQuadrantColumnPrefixToLast L p =
    firstQuadrantColumnPrefixToLast K p ≫
      firstQuadrantSingleColumnMap f p := by
  apply HomologicalComplex.hom_ext
  intro q
  by_cases hq : q = p
  · subst q
    change (firstQuadrantColumnPrefixMap f p).f p ≫
      firstQuadrantColumnPrefixToLastComponent L p p =
        firstQuadrantColumnPrefixToLastComponent K p p ≫
          (firstQuadrantSingleColumnMap f p).f p
    rw [firstQuadrantColumnPrefixToLastComponent_self,
      firstQuadrantColumnPrefixToLastComponent_self]
    rw [← Category.assoc,
      firstQuadrantColumnPrefixMap_XIso_hom f p p le_rfl]
    dsimp only [firstQuadrantSingleColumnMap, firstQuadrantSingleColumnXIso]
    rw [
      HomologicalComplex.single_map_f_self]
    simp
  · change (firstQuadrantColumnPrefixMap f p).f q ≫
      firstQuadrantColumnPrefixToLastComponent L p q =
        firstQuadrantColumnPrefixToLastComponent K p q ≫
          (firstQuadrantSingleColumnMap f p).f q
    rw [firstQuadrantColumnPrefixToLastComponent_eq_zero L p q hq,
      firstQuadrantColumnPrefixToLastComponent_eq_zero K p q hq,
      comp_zero, zero_comp]

/-- A bicomplex map induces a morphism between the successor short exact sequences of its
finite column filtrations. -/
public noncomputable def firstQuadrantColumnPrefixSuccShortComplexMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    firstQuadrantColumnPrefixSuccShortComplex K p ⟶
      firstQuadrantColumnPrefixSuccShortComplex L p where
  τ₁ := firstQuadrantColumnPrefixMap f p
  τ₂ := firstQuadrantColumnPrefixMap f (p + 1)
  τ₃ := firstQuadrantSingleColumnMap f (p + 1)
  comm₁₂ := firstQuadrantColumnPrefixSuccInclusion_naturality f p
  comm₂₃ := firstQuadrantColumnPrefixToLast_naturality f (p + 1)

/-- The zeroth prefix is already its sole-column quotient. -/
public theorem firstQuadrantColumnPrefixToLast_zero_isIso
    (K : FirstQuadrantBicomplex) :
    IsIso (firstQuadrantColumnPrefixToLast K 0) := by
  let _ : ∀ q : ℕ, IsIso ((firstQuadrantColumnPrefixToLast K 0).f q) := fun q => by
    by_cases hq : q = 0
    · subst q
      change IsIso (firstQuadrantColumnPrefixToLastComponent K 0 0)
      rw [firstQuadrantColumnPrefixToLastComponent_self]
      infer_instance
    · have hpos : 0 < q := by omega
      change IsIso (firstQuadrantColumnPrefixToLastComponent K 0 q)
      rw [firstQuadrantColumnPrefixToLastComponent_eq_zero K 0 q hq]
      exact (firstQuadrantColumnPrefix_isZero_X K 0 q hpos).isIso
        (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 (K.X 0) q hq) _
  exact HomologicalComplex.Hom.isIso_of_components _

@[reassoc]
public theorem firstQuadrantColumnPrefixToLast_total_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f p)
        (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map (firstQuadrantColumnPrefixToLast L p)
        (ComplexShape.down ℕ) =
    HomologicalComplex₂.total.map (firstQuadrantColumnPrefixToLast K p)
        (ComplexShape.down ℕ) ≫
      HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ) := by
  rw [← HomologicalComplex₂.total.map_comp,
    ← HomologicalComplex₂.total.map_comp]
  exact congrArg
    (fun g => HomologicalComplex₂.total.map g (ComplexShape.down ℕ))
    (firstQuadrantColumnPrefixToLast_naturality f p)

/-- If every single-column layer map becomes a quasi-isomorphism on totalization, then every
finite column-prefix map does as well. -/
public theorem firstQuadrantFinitePrefixTotal_quasiIso_of_singleColumns
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hsingle : ∀ p : ℕ, QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ))) :
    ∀ N : ℕ, QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
        (ComplexShape.down ℕ)) := by
  intro N
  induction N with
  | zero =>
      let a := HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f 0)
        (ComplexShape.down ℕ)
      let b := HomologicalComplex₂.total.map (firstQuadrantColumnPrefixToLast L 0)
        (ComplexShape.down ℕ)
      let c := HomologicalComplex₂.total.map (firstQuadrantColumnPrefixToLast K 0)
        (ComplexShape.down ℕ)
      let d := HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f 0)
        (ComplexShape.down ℕ)
      let _ : IsIso (firstQuadrantColumnPrefixToLast K 0) :=
        firstQuadrantColumnPrefixToLast_zero_isIso K
      let _ : IsIso (firstQuadrantColumnPrefixToLast L 0) :=
        firstQuadrantColumnPrefixToLast_zero_isIso L
      let _ : IsIso b := by
        dsimp [b]
        exact (HomologicalComplex₂.total.mapIso
          (asIso (firstQuadrantColumnPrefixToLast L 0))
          (ComplexShape.down ℕ)).isIso_hom
      let _ : IsIso c := by
        dsimp [c]
        exact (HomologicalComplex₂.total.mapIso
          (asIso (firstQuadrantColumnPrefixToLast K 0))
          (ComplexShape.down ℕ)).isIso_hom
      let _ : QuasiIso d := hsingle 0
      let _ : QuasiIso (a ≫ b) := by
        rw [show a ≫ b = c ≫ d from
          firstQuadrantColumnPrefixToLast_total_naturality f 0]
        infer_instance
      exact quasiIso_of_comp_right a b
  | succ N ih =>
      let T := HomologicalComplex₂.totalFunctor AddCommGrpCat
        (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      let S₁ := firstQuadrantColumnPrefixSuccShortComplex K N
      let S₂ := firstQuadrantColumnPrefixSuccShortComplex L N
      let φ := T.mapShortComplex.map
        (firstQuadrantColumnPrefixSuccShortComplexMap f N)
      have hS₁ : S₁.ShortExact :=
        firstQuadrantColumnPrefixSuccShortComplex_shortExact K N
      have hS₂ : S₂.ShortExact :=
        firstQuadrantColumnPrefixSuccShortComplex_shortExact L N
      have hTS₁ : (S₁.map T).ShortExact := firstQuadrantTotal_shortExact S₁ hS₁
      have hTS₂ : (S₂.map T).ShortExact := firstQuadrantTotal_shortExact S₂ hS₂
      have h₁ : QuasiIso φ.τ₁ := by
        change QuasiIso
          (HomologicalComplex₂.total.map (firstQuadrantColumnPrefixMap f N)
            (ComplexShape.down ℕ))
        exact ih
      have h₃ : QuasiIso φ.τ₃ := by
        change QuasiIso
          (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f (N + 1))
            (ComplexShape.down ℕ))
        exact hsingle (N + 1)
      have h₂ : QuasiIso φ.τ₂ :=
        quasiIso_middle_of_shortExact φ hTS₁ hTS₂ h₁ h₃
      exact h₂

/-- Columnwise quasi-isomorphisms after totalizing the individual layers imply a
quasi-isomorphism on the full first-quadrant total. -/
public theorem firstQuadrantTotal_quasiIso_of_singleColumns
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hsingle : ∀ p : ℕ, QuasiIso
      (HomologicalComplex₂.total.map (firstQuadrantSingleColumnMap f p)
        (ComplexShape.down ℕ))) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) :=
  firstQuadrantTotal_quasiIso_of_all_prefixes f
    (firstQuadrantFinitePrefixTotal_quasiIso_of_singleColumns f hsingle)

/-- Koszul symmetry for the standard first-quadrant total-complex signs. -/
public instance firstQuadrantTotalComplexShapeSymmetry :
    TotalComplexShapeSymmetry
      (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ) where
  symm p q := add_comm q p
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := by
    rintro p p' hp q
    change p' + 1 = p at hp
    subst p
    dsimp
    rw [mul_one, add_mul, one_mul, pow_add, pow_mul]
    exact mul_comm _ _
  σ_ε₂ := by
    rintro p q q' hq
    change q' + 1 = q at hq
    subst q
    dsimp
    rw [one_mul, mul_add, mul_one, pow_add, mul_assoc,
      Int.units_mul_self, mul_one]

/-- Flip a first-quadrant bicomplex map across the diagonal. -/
public def firstQuadrantFlipMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) : K.flip ⟶ L.flip :=
  (HomologicalComplex₂.flipFunctor AddCommGrpCat
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map f

/-- A column map of the flipped bicomplex is exactly the corresponding horizontal row map. -/
public theorem firstQuadrantFlipMap_column_eq_horizontalRowMap
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) (q : ℕ) :
    (firstQuadrantFlipMap f).f q = firstQuadrantHorizontalRowMap f q := by
  rfl

@[reassoc]
public theorem firstQuadrant_totalFlipIso_naturality
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L) :
    HomologicalComplex₂.total.map (firstQuadrantFlipMap f)
        (ComplexShape.down ℕ) ≫
      (L.totalFlipIso (ComplexShape.down ℕ)).hom =
    (K.totalFlipIso (ComplexShape.down ℕ)).hom ≫
      HomologicalComplex₂.total.map f (ComplexShape.down ℕ) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  dsimp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc]
  change (f.f q).f p ≫ (_ • _) = (_ • _) ≫ _
  rw [Linear.comp_units_smul, Linear.units_smul_comp,
    HomologicalComplex₂.ιTotal_map]

/-- It is enough to prove the single-column total statement after flipping: total symmetry then
returns the desired quasi-isomorphism for the original bicomplex map. -/
public theorem firstQuadrantTotal_quasiIso_of_flipped_singleColumns
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hsingle : ∀ p : ℕ, QuasiIso
      (HomologicalComplex₂.total.map
        (firstQuadrantSingleColumnMap (firstQuadrantFlipMap f) p)
        (ComplexShape.down ℕ))) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  let g := HomologicalComplex₂.total.map (firstQuadrantFlipMap f)
    (ComplexShape.down ℕ)
  let eK := (K.totalFlipIso (ComplexShape.down ℕ)).hom
  let eL := (L.totalFlipIso (ComplexShape.down ℕ)).hom
  let h := HomologicalComplex₂.total.map f (ComplexShape.down ℕ)
  let _ : QuasiIso g := firstQuadrantTotal_quasiIso_of_singleColumns
    (firstQuadrantFlipMap f) hsingle
  let _ : IsIso eK := by dsimp [eK]; infer_instance
  let _ : IsIso eL := by dsimp [eL]; infer_instance
  let _ : QuasiIso (eK ≫ h) := by
    rw [← show g ≫ eL = eK ≫ h from firstQuadrant_totalFlipIso_naturality f]
    infer_instance
  exact quasiIso_of_comp_left eK h

/-- Rowwise quasi-isomorphisms of first-quadrant bicomplexes induce a quasi-isomorphism on
their direct-sum total complexes. -/
public theorem firstQuadrantTotal_quasiIso_of_rows
    {K L : FirstQuadrantBicomplex} (f : K ⟶ L)
    (hrow : ∀ q : ℕ, QuasiIso (firstQuadrantHorizontalRowMap f q)) :
    QuasiIso (HomologicalComplex₂.total.map f (ComplexShape.down ℕ)) := by
  apply firstQuadrantTotal_quasiIso_of_flipped_singleColumns f
  intro q
  apply firstQuadrantSingleColumnTotal_quasiIso
    (firstQuadrantFlipMap f) q
  rw [firstQuadrantFlipMap_column_eq_horizontalRowMap]
  exact hrow q

/-- The exact generic rowwise-totalization proposition used by the boundary-seven Cech
assembly is therefore unconditional. -/
public theorem firstQuadrantRowwiseTotalization :
    FirstQuadrantRowwiseTotalization := by
  intro K L f hrow
  exact firstQuadrantTotal_quasiIso_of_rows f hrow

end SphereSixComplex
