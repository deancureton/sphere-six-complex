module

public import DifferentialGeometry.Topology.Homology.Local.CompactEuclidean

@[expose] public section

open CategoryTheory Limits Metric

noncomputable section

universe u

namespace DifferentialGeometry.Topology.SingularPair

variable (R : ModuleCat.{u} ℤ)

lemma iso_inv_comp_eq_comp_inv {𝒞 : Type*} [Category 𝒞] {a b c d : 𝒞} (i : a ≅ b) (i' : c ≅ d)
    {f : a ⟶ c} {g : b ⟶ d} (h : i.hom ≫ g = f ≫ i'.hom) : i.inv ≫ f = g ≫ i'.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

section excisionCompact

variable {X : Type u} [TopologicalSpace X] [T2Space X]

lemma interior_union_interior_compl_eq_univ {U A : Set X} (hU : IsOpen U) (hA : IsCompact A)
    (hAU : A ⊆ U) : interior U ∪ interior Aᶜ = Set.univ := by
  rw [hU.interior_eq, hA.isClosed.isOpen_compl.interior_eq]
  exact Set.eq_univ_of_forall fun x => by
    by_cases hx : x ∈ A
    · exact Or.inl (hAU hx)
    · exact Or.inr hx

def excisionCompactIso {U A : Set X} (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U) (k : ℕ) :
    relativeHomology R (TopCat.of U) (Subtype.val ⁻¹' Aᶜ) k ≅ relativeHomology R (TopCat.of X) Aᶜ k :=
  excisionIso R (X := TopCat.of X) (U := U) (V := Aᶜ)
    (interior_union_interior_compl_eq_univ hU hA hAU) k

lemma excisionCompactIso_hom {U A : Set X} (hU : IsOpen U) (hA : IsCompact A) (hAU : A ⊆ U)
    (k : ℕ) :
    (excisionCompactIso R hU hA hAU k).hom =
      relativeHomologyMap R (incl (TopCat.of X) U) (mapsTo_incl (X := TopCat.of X) U Aᶜ) k :=
  rfl

omit [T2Space X] in
lemma mapsTo_id_preimage_val {U A A' : Set X} (h : A' ⊆ A) :
    Set.MapsTo (𝟙 (TopCat.of U)) (Subtype.val ⁻¹' Aᶜ) (Subtype.val ⁻¹' A'ᶜ) :=
  fun _ hx => Set.compl_subset_compl.2 h hx

lemma excisionCompactIso_natural {U A A' : Set X} (hU : IsOpen U) (hA : IsCompact A)
    (hAU : A ⊆ U) (hA' : IsCompact A') (hA'U : A' ⊆ U) (h : A' ⊆ A) (k : ℕ) :
    (excisionCompactIso R hU hA hAU k).hom ≫
        relativeHomologyMap R (𝟙 (TopCat.of X)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k =
      relativeHomologyMap R (𝟙 (TopCat.of U)) (mapsTo_id_preimage_val h) k ≫
        (excisionCompactIso R hU hA' hA'U k).hom :=
  relativeHomologyMap_comp_id R _ _ _ _ _ k

end excisionCompact

section chart

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

def chartUp (m : M) : EU.{u} n := ULift.up (φ m)

@[simp]
lemma chartUp_apply (m : M) : chartUp φ m = ULift.up (φ m) := rfl

def chartLift : φ.source ≃ₜ (ULift.down ⁻¹' φ.target : Set (EU.{u} n)) :=
  φ.toHomeomorphSourceTarget.trans
    ((Homeomorph.ulift.{u} (X := EuclideanSpace ℝ (Fin n))).symm.image φ.target |>.trans
      (Homeomorph.setCongr (Set.ext fun x =>
        ⟨fun ⟨_, hy, e⟩ => e ▸ hy, fun h => ⟨x.down, h, rfl⟩⟩)))

@[simp]
lemma chartLift_apply_coe (x : φ.source) : (chartLift φ x : EU.{u} n) = chartUp φ x := rfl

lemma isOpen_liftedTarget : IsOpen (ULift.down ⁻¹' φ.target : Set (EU.{u} n)) :=
  φ.open_target.preimage continuous_uliftDown

lemma chartUp_image_subset {A : Set M} (hAφ : A ⊆ φ.source) :
    chartUp φ '' A ⊆ ULift.down ⁻¹' φ.target := by
  rintro _ ⟨a, ha, rfl⟩
  exact φ.map_source (hAφ ha)

lemma isCompact_chartUp_image {A : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source) :
    IsCompact (chartUp φ '' A) :=
  hA.image_of_continuousOn (continuous_uliftUp.comp_continuousOn (φ.continuousOn.mono hAφ))

lemma chartUp_injOn : Set.InjOn (chartUp φ) φ.source :=
  fun _ hx _ hy e => φ.injOn hx hy (ULift.up.inj e)

lemma chartLift_mem_iff {A : Set M} (hAφ : A ⊆ φ.source) {B : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (x : φ.source) :
    x ∈ (Subtype.val ⁻¹' Aᶜ : Set φ.source) ↔
      chartLift φ x ∈
        (Subtype.val ⁻¹' Bᶜ : Set (ULift.down ⁻¹' φ.target : Set (EU.{u} n))) := by
  subst hB
  change x.1 ∉ A ↔ chartUp φ x.1 ∉ chartUp φ '' A
  constructor
  · rintro hx ⟨a, ha, e⟩
    exact hx (chartUp_injOn φ (hAφ ha) x.2 e ▸ ha)
  · exact fun h hx => h ⟨x.1, hx, rfl⟩

end chart

section transport

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))

def chartTransportIso {A : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source) {B : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (k : ℕ) :
    relativeHomology R (TopCat.of M) Aᶜ k ≅ relativeHomology R (TopCat.of (EU n)) Bᶜ k :=
  (excisionCompactIso R φ.open_source hA hAφ k).symm ≪≫
    relativeHomologyIsoOfHomeomorphMemIff R (chartLift φ) (chartLift_mem_iff φ hAφ hB) k ≪≫
      excisionCompactIso R (isOpen_liftedTarget φ) (hB ▸ isCompact_chartUp_image φ hA hAφ)
        (hB ▸ chartUp_image_subset φ hAφ) k

theorem chartTransportIso_natural {A A' : Set M} (hA : IsCompact A) (hAφ : A ⊆ φ.source)
    (hA' : IsCompact A') (hA'φ : A' ⊆ φ.source) {B B' : Set (EU.{u} n)}
    (hB : chartUp φ '' A = B) (hB' : chartUp φ '' A' = B') (h : A' ⊆ A) (h' : B' ⊆ B) (k : ℕ) :
    (chartTransportIso R φ hA hAφ hB k).hom ≫
        relativeHomologyMap R (𝟙 (TopCat.of (EU n))) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h')) k =
      relativeHomologyMap R (𝟙 (TopCat.of M)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k ≫
        (chartTransportIso R φ hA' hA'φ hB' k).hom := by
  have e₃ := excisionCompactIso_natural R (isOpen_liftedTarget φ)
    (hB ▸ isCompact_chartUp_image φ hA hAφ) (hB ▸ chartUp_image_subset φ hAφ)
    (hB' ▸ isCompact_chartUp_image φ hA' hA'φ) (hB' ▸ chartUp_image_subset φ hA'φ) h' k
  have e₂ : (relativeHomologyIsoOfHomeomorphMemIff R (chartLift φ) (chartLift_mem_iff φ hAφ hB) k).hom ≫
      relativeHomologyMap R (𝟙 (TopCat.of (ULift.down ⁻¹' φ.target : Set (EU.{u} n))))
        (mapsTo_id_preimage_val h') k =
      relativeHomologyMap R (𝟙 (TopCat.of φ.source)) (mapsTo_id_preimage_val h) k ≫
        (relativeHomologyIsoOfHomeomorphMemIff R (chartLift φ) (chartLift_mem_iff φ hA'φ hB') k).hom :=
    relativeHomologyMap_comp_id R _ _ _ _ _ k
  have e₁ := iso_inv_comp_eq_comp_inv _ _
    (excisionCompactIso_natural R φ.open_source hA hAφ hA' hA'φ h k)
  simp only [chartTransportIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [e₃, ← Category.assoc _ (relativeHomologyMap R (𝟙 _) _ k), e₂, Category.assoc,
    ← Category.assoc _ _
      ((relativeHomologyIsoOfHomeomorphMemIff R (chartLift φ) (chartLift_mem_iff φ hA'φ hB') k).hom ≫ _),
    e₁, Category.assoc]

theorem exists_relativeHomologyTransport :
    ∃ i : ∀ (A : Set M), IsCompact A → A ⊆ φ.source → ∀ k,
        relativeHomology R (TopCat.of M) Aᶜ k ≅ relativeHomology R (TopCat.of (EU n)) (chartUp φ '' A)ᶜ k,
      ∀ (A : Set M) (hA : IsCompact A) (hAφ : A ⊆ φ.source) (A' : Set M) (hA' : IsCompact A')
        (hA'φ : A' ⊆ φ.source) (h : A' ⊆ A) (k : ℕ),
        (i A hA hAφ k).hom ≫ relativeHomologyMap R (𝟙 (TopCat.of (EU n)))
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.image_mono h))) k =
          relativeHomologyMap R (𝟙 (TopCat.of M)) (mapsTo_id_of_subset (Set.compl_subset_compl.2 h)) k ≫
            (i A' hA' hA'φ k).hom :=
  ⟨fun _ hA hAφ k => chartTransportIso R φ hA hAφ rfl k,
    fun _ hA hAφ _ hA' hA'φ h k =>
      chartTransportIso_natural R φ hA hAφ hA' hA'φ rfl rfl h (Set.image_mono h) k⟩

theorem localGood.of_subset_chart_source (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A)
    (hAφ : A ⊆ φ.source) : localGood R (TopCat.of M) n A := by
  refine localGood.of_iso_map (Y := TopCat.of (EU.{u} n)) (B := chartUp φ '' A) (chartUp φ)
    (fun x hx => ⟨x, hx, rfl⟩) (fun _ ⟨x, hx, e⟩ => ⟨x, hx, e⟩)
    (fun k => chartTransportIso R φ hA hAφ rfl k)
    (fun x hx => (chartTransportIso R φ isCompact_singleton
      (Set.singleton_subset_iff.2 (hAφ hx)) Set.image_singleton n).hom)
    (fun x hx => ?_) (localGood.of_isCompact_EU R hn (isCompact_chartUp_image φ hA hAφ))
  exact chartTransportIso_natural R φ hA hAφ isCompact_singleton
    (Set.singleton_subset_iff.2 (hAφ hx)) rfl Set.image_singleton
    (Set.singleton_subset_iff.2 hx) (Set.singleton_subset_iff.2 ⟨x, hx, rfl⟩) n

theorem localGood.of_finset_chart (hn : 1 ≤ n) {ι : Type*} (F : Finset ι) (C : ι → Set M)
    (hC : ∀ a ∈ F, IsCompact (C a) ∧
      ∃ φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)), C a ⊆ φ.source) :
    localGood R (TopCat.of M) n (⋃ a ∈ F, C a) := by
  classical
  induction F using Finset.induction_on generalizing C with
  | empty => exact (localGood.empty _ _).of_eq (by simp)
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨hCa, φ, hφ⟩ := hC a (Finset.mem_insert_self a F)
    refine localGood.union hCa.isClosed
      (isClosed_biUnion_finset fun b hb => (hC b (Finset.mem_insert_of_mem hb)).1.isClosed)
      (localGood.of_subset_chart_source R φ hn hCa hφ)
      (ih C fun b hb => hC b (Finset.mem_insert_of_mem hb)) ?_
    rw [Set.inter_iUnion₂]
    exact ih (fun b => C a ∩ C b) fun b hb =>
      ⟨hCa.inter_right (hC b (Finset.mem_insert_of_mem hb)).1.isClosed,
        φ, Set.inter_subset_left.trans hφ⟩

end transport

section charted

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem localGood.of_isCompact (hn : 1 ≤ n) {A : Set M} (hA : IsCompact A) :
    localGood R (TopCat.of M) n A := by
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  choose N hN using fun a : M =>
    exists_compact_subset (chartAt (EuclideanSpace ℝ (Fin n)) a).open_source
      (mem_chart_source (EuclideanSpace ℝ (Fin n)) a)
  obtain ⟨F, -, hAF⟩ := hA.elim_nhds_subcover (fun a => interior (N a))
    fun a _ => isOpen_interior.mem_nhds (hN a).2.1
  refine (localGood.of_finset_chart R hn F (fun a => A ∩ N a) fun a _ =>
    ⟨hA.inter_right (hN a).1.isClosed, chartAt (EuclideanSpace ℝ (Fin n)) a,
      Set.inter_subset_right.trans (hN a).2.2⟩).of_eq ?_
  ext x
  constructor
  · intro hx
    obtain ⟨a, -, hxa⟩ := Set.mem_iUnion₂.1 hx
    exact hxa.1
  · intro hx
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hAF hx)
    exact Set.mem_iUnion₂.2 ⟨a, ha, hx, interior_subset hxa⟩

theorem isZero_relativeHomology_compl_singleton_manifold (hn : 1 ≤ n) (x : M) {k : ℕ} (hk : k ≠ n) :
    IsZero (relativeHomology R (TopCat.of M) {x}ᶜ k) :=
  (isZero_relativeHomology_EU_compl_singleton R hn (chartUp (chartAt (EuclideanSpace ℝ (Fin n)) x) x)
    hk).of_iso (chartTransportIso R (chartAt (EuclideanSpace ℝ (Fin n)) x) isCompact_singleton
      (Set.singleton_subset_iff.2 (mem_chart_source _ x)) Set.image_singleton k)

def relativeHomologyManifoldPointIso (hn : 1 ≤ n) (x : M) :
    relativeHomology R (TopCat.of M) {x}ᶜ n ≅ R :=
  chartTransportIso R (chartAt (EuclideanSpace ℝ (Fin n)) x) isCompact_singleton
      (Set.singleton_subset_iff.2 (mem_chart_source _ x)) Set.image_singleton n ≪≫
    relativeHomologyEuclideanPointIso R hn (chartUp (chartAt (EuclideanSpace ℝ (Fin n)) x) x)

lemma uliftUp_image_closedBall (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ULift.up.{u} '' closedBall c r = closedBall (ULift.up c) r := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [ULift.dist_up_up] using hy
  · intro hz
    exact ⟨z.down, by simpa [ULift.dist_eq] using hz, rfl⟩

theorem exists_chartBall_isIso_ptRes (hn : 1 ≤ n) (x : M) :
    ∃ D : Set M, IsCompact D ∧ x ∈ interior D ∧ ∀ y (hy : y ∈ D),
      IsIso (relativeHomologyMap R (𝟙 (TopCat.of M)) (compl_mapsTo hy) n :
        relativeHomology R (TopCat.of M) Dᶜ n ⟶ relativeHomology R (TopCat.of M) {y}ᶜ n) := by
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) x with hφ
  have hxs : x ∈ φ.source := mem_chart_source _ x
  obtain ⟨r, hr, hKt⟩ :=
    nhds_basis_closedBall.mem_iff.1 (φ.open_target.mem_nhds (φ.map_source hxs))
  have hD : IsCompact (φ.symm '' closedBall (φ x) r) :=
    (isCompact_closedBall _ _).image_of_continuousOn (φ.continuousOn_symm.mono hKt)
  refine ⟨φ.symm '' closedBall (φ x) r, hD, ?_, fun y hy => ?_⟩
  · refine mem_interior.2 ⟨φ.symm '' ball (φ x) r, Set.image_mono ball_subset_closedBall,
      φ.symm.isOpen_image_of_subset_source isOpen_ball
        (φ.symm_source ▸ ball_subset_closedBall.trans hKt),
      ⟨φ x, mem_ball_self hr, φ.left_inv hxs⟩⟩
  · have hDφ : φ.symm '' closedBall (φ x) r ⊆ φ.source :=
      (Set.image_mono hKt).trans φ.symm_image_target_eq_source.subset
    have hB : chartUp φ '' (φ.symm '' closedBall (φ x) r) = closedBall (ULift.up (φ x)) r :=
      calc chartUp φ '' (φ.symm '' closedBall (φ x) r)
          = ULift.up '' (φ '' (φ.symm '' closedBall (φ x) r)) :=
          (Set.image_image ULift.up φ (φ.symm '' closedBall (φ x) r)).symm
        _ = ULift.up '' closedBall (φ x) r :=
          congrArg (ULift.up '' ·) (φ.image_symm_image_of_subset_target hKt)
        _ = closedBall (ULift.up (φ x)) r := uliftUp_image_closedBall _ _
    have hyB : chartUp φ y ∈ closedBall (ULift.up (φ x)) r := hB ▸ ⟨y, hy, rfl⟩
    have hnat := chartTransportIso_natural R φ hD hDφ isCompact_singleton
      (Set.singleton_subset_iff.2 (hDφ hy)) hB Set.image_singleton
      (Set.singleton_subset_iff.2 hy) (Set.singleton_subset_iff.2 hyB) n
    have hiso : IsIso (relativeHomologyMap R (𝟙 (TopCat.of (EU n)))
        (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hyB))) n) :=
      isIso_ptRes_of_convex R hn (convex_closedBall _ _) (isCompact_closedBall _ _) hyB n
    have : relativeHomologyMap R (𝟙 (TopCat.of M)) (compl_mapsTo hy) n =
        (chartTransportIso R φ hD hDφ hB n).hom ≫
          relativeHomologyMap R (𝟙 (TopCat.of (EU n)))
            (mapsTo_id_of_subset (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hyB))) n ≫
          (chartTransportIso R φ isCompact_singleton (Set.singleton_subset_iff.2 (hDφ hy))
            Set.image_singleton n).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv, hnat]
    rw [this]
    infer_instance

end charted

end DifferentialGeometry.Topology.SingularPair

end
