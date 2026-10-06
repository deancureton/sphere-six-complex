module

public import DifferentialGeometry.Topology.Morse.Handle.Middle.Configuration.MiddleBlock

@[expose] public section

set_option autoImplicit false

open Set Filter
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm negPart posPart
  recombine)

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M]

namespace Handle

open CategoryTheory Limits SingularPair

universe u

variable {X : Type u} [TopologicalSpace X]

abbrev relativeHomologyPair (B A : Set X) (k : ℕ) : ModuleCat.{u} ℤ :=
  relativeHomology integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) k

def inclPair {B A B' A' : Set X} (hB : B ⊆ B') (hA : A ⊆ A') (k : ℕ) :
    relativeHomologyPair B A k ⟶ relativeHomologyPair B' A' k :=
  relativeHomologyMap integerCoefficients (inclOfLE (X := TopCat.of X) hB) (mapsTo_inclOfLE_preimage hB hA) k

def tripleBoundary (A B C : Set X) (k : ℕ) : relativeHomologyPair C B (k + 1) ⟶ relativeHomologyPair B A k :=
  δ integerCoefficients (TopCat.of ↥C) (Subtype.val ⁻¹' B) k ≫
    singularHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x => (⟨x.1.1, x.2⟩ : ↥B),
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩) k ≫
    relπ integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) k

def isGen {A : ModuleCat.{u} ℤ} (g : A) : Prop := ∀ x : A, ∃ m : ℤ, x = m • g

open Classical in
def sphereClass (B A : Set X) {ℓ : ℕ} (F : EuclideanSpace ℝ (Fin (ℓ + 1)) → X)
    (g : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ) : relativeHomologyPair B A ℓ :=
  if h : ContinuousOn F (unitSphere ℓ) ∧ MapsTo F (unitSphere ℓ) B then
    (singularHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere ℓ) => (⟨F x.down.1, h.2 x.down.2⟩ : ↥B),
        (h.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2)).subtype_mk _⟩) ℓ ≫
      relπ integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) ℓ) g
  else 0

open Classical in
def discClass (B A : Set X) {m : ℕ} (F : EuclideanSpace ℝ (Fin m) → X)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m) :
    relativeHomologyPair B A m :=
  if h : ContinuousOn F (Metric.closedBall 0 1) ∧ MapsTo F (Metric.closedBall 0 1) B ∧
      MapsTo F (Metric.sphere 0 1) A then
    relativeHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ULift.{u} (Disk m) => (⟨F x.down.1, h.2.1 x.down.2⟩ : ↥B),
        (h.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2)).subtype_mk _⟩)
      (fun _ hx => h.2.2 hx) m g
  else 0

def boundaryGen {m : ℕ}
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) (ULift.down ⁻¹' diskSphere (m + 1))
      (m + 1)) : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} m) m :=
  (δ integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) (ULift.down ⁻¹' diskSphere (m + 1)) m ≫
    singularHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ↥(ULift.down ⁻¹' diskSphere (m + 1) : Set (ULift.{u} (Disk (m + 1)))) =>
        (ULift.up ⟨x.1.down.1, x.2⟩ : ULift.{u} (unitSphere m)),
      continuous_uliftUp.comp ((continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)⟩) m) g

theorem tripleBoundary_exact {T S Y : Set X} (hTS : T ⊆ S) (hSY : S ⊆ Y) (k : ℕ)
    (x : relativeHomologyPair S T k) (hx : inclPair hSY (subset_refl T) k x = 0) :
    ∃ z : relativeHomologyPair Y S (k + 1), tripleBoundary T S Y k z = x := by
  classical
  let : HasCoproducts.{u} (ModuleCat.{u} ℤ) := fun _ => inferInstance
  let f : TopCat.of ↥S ⟶ TopCat.of ↥Y := inclOfLE (X := TopCat.of X) hSY
  have hf : MapsTo f (Subtype.val ⁻¹' T : Set ↥S) (Subtype.val ⁻¹' T : Set ↥Y) :=
    mapsTo_inclOfLE_preimage hSY (subset_refl T)
  let g := restr f hf
  have hgiso : ∀ j : ℕ, IsIso (singularHomologyMap integerCoefficients g j) := fun j =>
    isIso_singularHomologyMap_restr_inclOfLE integerCoefficients hTS (hTS.trans hSY) hSY (subset_refl T)
      (isHomotopyEquivInclusion_refl T) j
  let φ : TopCat.of ↥(Subtype.val ⁻¹' S : Set ↥Y) ⟶ TopCat.of ↥S :=
    TopCat.ofHom ⟨fun x => (⟨x.1.1, x.2⟩ : ↥S),
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  let ψ : TopCat.of ↥S ⟶ TopCat.of ↥(Subtype.val ⁻¹' S : Set ↥Y) :=
    TopCat.ofHom ⟨fun x => (⟨⟨x.1, hSY x.2⟩, x.2⟩ : ↥(Subtype.val ⁻¹' S : Set ↥Y)),
      ((continuous_subtype_val.subtype_mk _).subtype_mk _)⟩
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    ext x
    rfl
  have hψincl : ψ ≫ incl (TopCat.of ↥Y) (Subtype.val ⁻¹' S) = f := by
    ext x
    rfl
  have hx' : relativeHomologyMap integerCoefficients f hf k x = 0 := hx
  obtain ⟨s, hs⟩ : ∃ s : singularHomology integerCoefficients (TopCat.of ↥S) k,
      relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k s = x := by
    cases k with
    | zero =>
      have : Epi (relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) 0) :=
        inferInstanceAs (Epi ((pair (TopCat.of ↥S) (Subtype.val ⁻¹' T)).homologyπ integerCoefficients 0))
      exact (ModuleCat.epi_iff_surjective _).1 this x
    | succ k' =>
      have hδ : δ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k' x = 0 := by
        have hinj := (ModuleCat.mono_iff_injective (singularHomologyMap integerCoefficients g k')).1 inferInstance
        apply hinj
        have h1 := congrArg (fun m => m x) (δ_natural integerCoefficients f hf k')
        simp only [CategoryTheory.comp_apply] at h1
        rw [map_zero]
        refine h1.trans ?_
        rw [hx', map_zero]
      exact (ShortComplex.moduleCat_exact_iff _).1
        (les_exact₃ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k') x hδ
  have hfs : relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T) k (singularHomologyMap integerCoefficients f k s) = 0 := by
    have h1 := congrArg (fun m => m s) (relπ_natural integerCoefficients f hf k)
    simp only [CategoryTheory.comp_apply] at h1
    rw [← h1, hs, hx']
  obtain ⟨t, ht⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (les_exact₂ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T) k) _ hfs
  let t₀ := inv (singularHomologyMap integerCoefficients g k) t
  have ht₀ : singularHomologyMap integerCoefficients g k t₀ = t := by
    change (inv (singularHomologyMap integerCoefficients g k) ≫ singularHomologyMap integerCoefficients g k) t = t
    rw [IsIso.inv_hom_id]
    rfl
  let s' := inclMap integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k t₀
  have hs' : singularHomologyMap integerCoefficients f k s' = singularHomologyMap integerCoefficients f k s := by
    have h1 := congrArg (fun m => m t₀) (inclMap_natural integerCoefficients f hf k)
    simp only [CategoryTheory.comp_apply] at h1
    rw [← ht, ← ht₀]
    exact h1
  have hπs' : relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k s' = 0 := by
    have h1 := congrArg (fun m => m t₀)
      ((pair (TopCat.of ↥S) (Subtype.val ⁻¹' T)).homologyMap_hom_homologyπ integerCoefficients k)
    simp only at h1
    exact h1
  let u := singularHomologyMap integerCoefficients ψ k (s - s')
  have hu : inclMap integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S) k u = 0 := by
    have h1 : inclMap integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S) k u = singularHomologyMap integerCoefficients f k (s - s') := by
      change (singularHomologyMap integerCoefficients ψ k ≫ singularHomologyMap integerCoefficients (incl (TopCat.of ↥Y) (Subtype.val ⁻¹' S)) k) (s - s') = _
      rw [← singularHomologyMap_comp, hψincl]
    rw [h1, map_sub, hs', sub_self]
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (les_exact₁ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S) k) u hu
  refine ⟨z, ?_⟩
  have hφu : singularHomologyMap integerCoefficients φ k u = s - s' := by
    change (singularHomologyMap integerCoefficients ψ k ≫ singularHomologyMap integerCoefficients φ k) (s - s') = _
    rw [← singularHomologyMap_comp, hψφ, singularHomologyMap_id]
    rfl
  change relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) k
    (singularHomologyMap integerCoefficients φ k (δ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S) k z)) = x
  rw [hz, hφu, map_sub, hs, hπs', sub_zero]

theorem triple_exact_mid {T S Y : Set X} (hTS : T ⊆ S) (hSY : S ⊆ Y) (k : ℕ)
    (x : relativeHomologyPair Y T k) (hx : inclPair (subset_refl Y) hTS k x = 0) :
    ∃ y : relativeHomologyPair S T k, inclPair hSY (subset_refl T) k y = x := by
  classical
  let : HasCoproducts.{u} (ModuleCat.{u} ℤ) := fun _ => inferInstance
  let g : TopCat.of ↥(Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) ⟶
      TopCat.of ↥(Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) :=
    TopCat.ofHom ⟨fun y => ⟨⟨y.1.1, hTS y.2⟩, y.2⟩, by fun_prop⟩
  let q : TopCat.of ↥(Subtype.val ⁻¹' S : Set (TopCat.of ↥Y)) ⟶ TopCat.of ↥S :=
    TopCat.ofHom ⟨fun y => ⟨y.1.1, y.2⟩, by fun_prop⟩
  have hjT : Set.MapsTo (𝟙 (TopCat.of ↥Y)) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y))
      (Subtype.val ⁻¹' S) := fun y hy => hTS hy
  have hiT : Set.MapsTo (inclOfLE (X := TopCat.of X) hSY) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S))
      (Subtype.val ⁻¹' T) := mapsTo_inclOfLE_preimage hSY (subset_refl T)
  have hj : ∀ l, inclPair (subset_refl Y) hTS l = relativeHomologyMap integerCoefficients (𝟙 (TopCat.of ↥Y)) hjT l := fun l =>
    relativeHomologyMap_eq_of_eq integerCoefficients (by ext; rfl) _ l
  have hU : IsZero (relativeHomology integerCoefficients (TopCat.of ↥S) Set.univ k) := by
    have : IsIso (incl (TopCat.of ↥S) Set.univ) := by
      have e : incl (TopCat.of ↥S) Set.univ = (TopCat.isoOfHomeo
          (X := TopCat.of (Set.univ : Set (TopCat.of ↥S))) (Y := TopCat.of ↥S)
          (Homeomorph.Set.univ _)).hom := rfl
      rw [e]
      infer_instance
    have : IsIso (pair (TopCat.of ↥S) Set.univ).hom :=
      inferInstanceAs (IsIso (TopCat.toSSet.map (incl (TopCat.of ↥S) Set.univ)))
    exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_isZero
      (SSetPair.isZero_chainComplex (pair (TopCat.of ↥S) Set.univ) integerCoefficients)
  have hij : ∀ y : relativeHomologyPair S T k,
      inclPair (subset_refl Y) hTS k (inclPair hSY (subset_refl T) k y) = 0 := by
    intro y
    have h1 : Set.MapsTo (𝟙 (TopCat.of ↥S)) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) Set.univ :=
      fun _ _ => trivial
    have h2 : Set.MapsTo (inclOfLE (X := TopCat.of X) hSY) Set.univ
        (Subtype.val ⁻¹' S : Set (TopCat.of ↥Y)) := fun s _ => s.2
    have e : inclPair hSY (subset_refl T) k ≫ inclPair (subset_refl Y) hTS k =
        relativeHomologyMap integerCoefficients (𝟙 _) h1 k ≫ relativeHomologyMap integerCoefficients (inclOfLE (X := TopCat.of X) hSY) h2 k := by
      rw [inclPair, inclPair, ← relativeHomologyMap_comp integerCoefficients _ _ _ _ (fun _ hy => hTS hy),
        ← relativeHomologyMap_comp integerCoefficients _ _ _ _ (fun _ hy => hTS hy)]
      exact relativeHomologyMap_eq_of_eq integerCoefficients (by ext; rfl) _ k
    rw [← ModuleCat.comp_apply, e, hU.eq_of_tgt (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of ↥S)) h1 k) 0, zero_comp]
    rfl
  obtain ⟨y₀, w, hxw⟩ : ∃ (y₀ : relativeHomologyPair S T k) (w : singularHomology integerCoefficients (TopCat.of ↥Y) k),
      x = inclPair hSY (subset_refl T) k y₀ +
        relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) k w := by
    cases k with
    | zero =>
      have : Epi (relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) 0) :=
        inferInstanceAs (Epi ((pair (TopCat.of ↥Y)
          (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y))).homologyπ integerCoefficients 0))
      obtain ⟨w, hw⟩ := (ModuleCat.epi_iff_surjective _).1 this x
      exact ⟨0, w, by rw [map_zero, zero_add, hw]⟩
    | succ m =>
      set a := δ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) m x with ha
      have h1 : singularHomologyMap integerCoefficients (restr (𝟙 (TopCat.of ↥Y)) hjT) m a = 0 := by
        have hn := δ_natural integerCoefficients (𝟙 (TopCat.of ↥Y)) hjT m
        rw [ha, ← ModuleCat.comp_apply, hn, ModuleCat.comp_apply, ← hj, hx, map_zero]
      have h2 : inclMap integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) m
          (singularHomologyMap integerCoefficients g m a) = 0 := by
        have e : g ≫ incl (TopCat.of ↥S) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) =
            restr (𝟙 (TopCat.of ↥Y)) hjT ≫ q := rfl
        rw [inclMap_eq_singularHomologyMap, ← ModuleCat.comp_apply, ← singularHomologyMap_comp, e, singularHomologyMap_comp,
          ModuleCat.comp_apply, h1, map_zero]
      obtain ⟨y₀, hy₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (les_exact₁ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) m) _ h2
      have h3 : δ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) m
          (inclPair hSY (subset_refl T) (m + 1) y₀) = a := by
        have hn := δ_natural integerCoefficients (inclOfLE (X := TopCat.of X) hSY) hiT m
        have e : g ≫ restr (inclOfLE (X := TopCat.of X) hSY) hiT = 𝟙 _ := rfl
        rw [inclPair, ← ModuleCat.comp_apply, ← hn, ModuleCat.comp_apply]
        change singularHomologyMap integerCoefficients (restr (inclOfLE (X := TopCat.of X) hSY) hiT) m
          (δ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) m y₀) = a
        rw [hy₀, ← ModuleCat.comp_apply, ← singularHomologyMap_comp, e, singularHomologyMap_id]
        rfl
      obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1
        (les_exact₃ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) m)
        (x - inclPair hSY (subset_refl T) (m + 1) y₀) (by
          change δ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) m
            (x - inclPair hSY (subset_refl T) (m + 1) y₀) = 0
          rw [map_sub, h3, ha, sub_self])
      refine ⟨y₀, w, ?_⟩
      change relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) (m + 1) w =
        x - inclPair hSY (subset_refl T) (m + 1) y₀ at hw
      rw [hw, add_sub_cancel]
  have hw0 : relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S : Set (TopCat.of ↥Y)) k w = 0 := by
    have hn := relπ_natural integerCoefficients (𝟙 (TopCat.of ↥Y)) hjT k
    rw [singularHomologyMap_id, Category.id_comp] at hn
    have e : relπ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' T : Set (TopCat.of ↥Y)) k w =
        x - inclPair hSY (subset_refl T) k y₀ := by
      rw [hxw, add_sub_cancel_left]
    rw [← hn, ModuleCat.comp_apply, e, ← hj, map_sub, hx, hij, sub_zero]
  obtain ⟨v, hv⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (les_exact₂ integerCoefficients (TopCat.of ↥Y) (Subtype.val ⁻¹' S : Set (TopCat.of ↥Y)) k) w hw0
  refine ⟨y₀ + relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T : Set (TopCat.of ↥S)) k (singularHomologyMap integerCoefficients q k v), ?_⟩
  rw [map_add, hxw]
  congr 1
  have hn := relπ_natural integerCoefficients (inclOfLE (X := TopCat.of X) hSY) hiT k
  have e : q ≫ inclOfLE (X := TopCat.of X) hSY =
      incl (TopCat.of ↥Y) (Subtype.val ⁻¹' S : Set (TopCat.of ↥Y)) := rfl
  rw [inclPair, ← ModuleCat.comp_apply, hn, ModuleCat.comp_apply,
    ← ModuleCat.comp_apply (singularHomologyMap integerCoefficients q k), ← singularHomologyMap_comp, e, ← inclMap_eq_singularHomologyMap]
  exact congrArg _ hv

theorem exists_disc_generator (m : ℕ) (hm : 1 ≤ m) :
    ∃ g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) (ULift.down ⁻¹' diskSphere (m + 1))
      (m + 1), isGen g ∧ isGen (boundaryGen g) := by
  classical
  let X : TopCat.{u} := TopCat.of (ULift.{u} (Disk (m + 1)))
  let A : Set X := ULift.down ⁻¹' diskSphere (m + 1)
  have : ContractibleSpace (Disk (m + 1)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have : ContractibleSpace (ULift.{u} (Disk (m + 1))) := Homeomorph.ulift.contractibleSpace
  have hX1 : IsZero (singularHomology integerCoefficients X (m + 1)) :=
    isZero_of_contractible integerCoefficients (ULift.{u} (Disk (m + 1))) (m + 1) (by omega)
  have hX0 : IsZero (singularHomology integerCoefficients X m) :=
    isZero_of_contractible integerCoefficients (ULift.{u} (Disk (m + 1))) m (by omega)
  have hmono : Mono (δ integerCoefficients X A m) :=
    (les_exact₃ integerCoefficients X A m).mono_g (hX1.eq_zero_of_src _)
  have hepi : Epi (δ integerCoefficients X A m) :=
    (les_exact₁ integerCoefficients X A m).epi_f (hX0.eq_zero_of_tgt _)
  have : IsIso (δ integerCoefficients X A m) := isIso_of_mono_of_epi _
  let f : TopCat.of ↥A ⟶ Sphere.liftedSphere.{u} m :=
    TopCat.ofHom ⟨fun x : ↥A => (ULift.up ⟨x.1.down.1, x.2⟩ : ULift.{u} (unitSphere m)),
      continuous_uliftUp.comp ((continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)⟩
  let g' : Sphere.liftedSphere.{u} m ⟶ TopCat.of ↥A :=
    TopCat.ofHom ⟨fun y : ULift.{u} (unitSphere m) =>
        (⟨ULift.up ⟨y.down.1, Metric.sphere_subset_closedBall y.down.2⟩, y.down.2⟩ : ↥A),
      ((continuous_uliftUp.comp ((continuous_subtype_val.comp continuous_uliftDown).subtype_mk
        _)).subtype_mk _)⟩
  have hfg : f ≫ g' = 𝟙 _ := by ext x; rfl
  have hgf : g' ≫ f = 𝟙 _ := by ext x; rfl
  have : IsIso (singularHomologyMap integerCoefficients f m) :=
    ⟨singularHomologyMap integerCoefficients g' m, by rw [← singularHomologyMap_comp, hfg, singularHomologyMap_id], by rw [← singularHomologyMap_comp, hgf, singularHomologyMap_id]⟩
  let φ := asIso (δ integerCoefficients X A m ≫ singularHomologyMap integerCoefficients f m)
  obtain ⟨e⟩ := (Sphere.homology_sphere integerCoefficients m m).1 rfl (by omega)
  let h : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} m) m := e.inv (ULift.up (1 : ℤ))
  have hh : isGen h := by
    intro x
    refine ⟨(e.hom x).down, ?_⟩
    have hx : e.hom x = (e.hom x).down • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
      apply ULift.ext
      simp
    calc x = e.inv (e.hom x) := by simp
      _ = e.inv ((e.hom x).down • (ULift.up (1 : ℤ) : ULift.{u} ℤ)) := by rw [← hx]
      _ = (e.hom x).down • h := map_zsmul (e.inv).hom _ _
  refine ⟨φ.inv h, ?_, ?_⟩
  · intro x
    obtain ⟨k, hk⟩ := hh (φ.hom x)
    refine ⟨k, ?_⟩
    calc x = φ.inv (φ.hom x) := by simp
      _ = φ.inv (k • h) := by rw [hk]
      _ = k • φ.inv h := map_zsmul (φ.inv).hom _ _
  · have hb : boundaryGen (φ.inv h) = φ.hom (φ.inv h) := rfl
    rw [hb]
    simpa using hh

theorem isGen_boundaryGen {m : ℕ} (hm : 1 ≤ m)
    {g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) (ULift.down ⁻¹' diskSphere (m + 1)) (m + 1)}
    (hg : isGen g) : isGen (boundaryGen g) := by
  have hc0 : ContractibleSpace (Disk (m + 1)) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1))) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  have hc : ContractibleSpace (ULift.{u} (Disk (m + 1))) := Homeomorph.ulift.contractibleSpace
  have hz : IsZero (singularHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) m) :=
    isZero_of_contractible integerCoefficients (ULift.{u} (Disk (m + 1))) m (by omega)
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (les_exact₁ integerCoefficients (TopCat.of (ULift.{u} (Disk (m + 1)))) (ULift.down ⁻¹' diskSphere (m + 1)) m)
  let A : Set (ULift.{u} (Disk (m + 1))) := ULift.down ⁻¹' diskSphere (m + 1)
  let f : TopCat.of ↥A ⟶ Sphere.liftedSphere.{u} m :=
    TopCat.ofHom ⟨fun x : ↥A => (ULift.up ⟨x.1.down.1, x.2⟩ : ULift.{u} (unitSphere m)),
      continuous_uliftUp.comp ((continuous_subtype_val.comp
        (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)⟩
  let k : Sphere.liftedSphere.{u} m ⟶ TopCat.of ↥A :=
    TopCat.ofHom ⟨fun y : ULift.{u} (unitSphere m) =>
        (⟨ULift.up ⟨y.down.1, Metric.sphere_subset_closedBall y.down.2⟩, y.down.2⟩ : ↥A),
      ((continuous_uliftUp.comp ((continuous_subtype_val.comp continuous_uliftDown).subtype_mk
        _)).subtype_mk _)⟩
  have hkf : k ≫ f = 𝟙 _ := by
    ext y
    rfl
  intro x
  obtain ⟨y, hy⟩ := hex (singularHomologyMap integerCoefficients k m x)
    ((ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _)
  obtain ⟨c, rfl⟩ := hg y
  refine ⟨c, ?_⟩
  have h1 : singularHomologyMap integerCoefficients f m (singularHomologyMap integerCoefficients k m x) = x := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hkf, CategoryTheory.Functor.map_id]
    rfl
  rw [← h1, ← hy, map_zsmul, map_zsmul]
  rfl

theorem relativeHomologyPair_iUnion_vanishes {ι : Type*} (s : Finset ι) (U : ι → Set X) (K : Set X)
    (hU : ∀ i ∈ s, IsOpen (Subtype.val ⁻¹' U i : Set ↥(⋃ i ∈ s, U i)))
    (hK : ∀ i ∈ s, IsOpen (Subtype.val ⁻¹' (U i \ K) : Set ↥(U i)))
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (U i) (U i')) (j : ℕ)
    (h0 : ∀ i ∈ s, IsZero (relativeHomologyPair (U i) (U i \ K) j)) :
    IsZero (relativeHomologyPair (⋃ i ∈ s, U i) ((⋃ i ∈ s, U i) \ K) j) := by
  classical
  generalize hW : (⋃ i ∈ s, U i) = W at hU ⊢
  have huniv : ∀ n, IsZero (relativeHomology integerCoefficients (TopCat.of ↥W) Set.univ n) := by
    intro n
    have := (isHomotopyEquivInclusion_refl W).relHomologyVanishes n
    rwa [Subtype.coe_preimage_self] at this
  have hKW : ∀ i ∈ s, IsOpen (Subtype.val ⁻¹' (U i \ K) : Set ↥W) := by
    intro i hi
    obtain ⟨t, ht, hteq⟩ := isOpen_induced_iff.1 (hK i hi)
    have : (Subtype.val ⁻¹' (U i \ K) : Set ↥W) =
        (Subtype.val ⁻¹' t : Set ↥W) ∩ Subtype.val ⁻¹' U i := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, hx.1⟩
        have h1 : (⟨x.1, hx.1⟩ : ↥(U i)) ∈ (Subtype.val ⁻¹' (U i \ K) : Set ↥(U i)) := hx
        rw [← hteq] at h1
        exact h1
      · rintro ⟨hxt, hxU⟩
        have h1 : (⟨x.1, hxU⟩ : ↥(U i)) ∈ (Subtype.val ⁻¹' t : Set ↥(U i)) := hxt
        rw [hteq] at h1
        exact h1
    rw [this]
    exact (ht.preimage continuous_subtype_val).inter (hU i hi)
  have hmemW : ∀ x : ↥W, ∃ i ∈ s, x.1 ∈ U i := by
    intro x
    have h : (x : X) ∈ ⋃ i ∈ s, U i := by
      rw [hW]
      exact x.2
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 h
    exact ⟨i, hi, hxi⟩
  let C : Finset ι → Set ↥W := fun T => {x | x.1 ∉ K ∨ ∃ i ∈ s, i ∉ T ∧ x.1 ∈ U i}
  have key : ∀ T : Finset ι, T ⊆ s → IsZero (relativeHomology integerCoefficients (TopCat.of ↥W) (C T) j) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have hC : C ∅ = Set.univ := by
        ext x
        obtain ⟨i, hi, hx⟩ := hmemW x
        simp only [C, Set.mem_univ, iff_true]
        exact Or.inr ⟨i, hi, Finset.notMem_empty i, hx⟩
      rw [hC]
      exact huniv j
    | insert a T haT ih =>
      intro hsub
      have has : a ∈ s := hsub (Finset.mem_insert_self a T)
      have hTs : T ⊆ s := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hPz := ih hTs
      let P : Set ↥W := C T
      let Q : Set ↥W := {x | x.1 ∉ K ∨ x.1 ∉ U a}
      have hPo : IsOpen P := by
        refine isOpen_iff_forall_mem_open.2 ?_
        intro x hx
        rcases hx with hx | ⟨i, hi, hiT, hxi⟩
        · obtain ⟨i, hi, hxi⟩ := hmemW x
          refine ⟨Subtype.val ⁻¹' (U i \ K), ?_, hKW i hi, ⟨hxi, hx⟩⟩
          intro y hy
          exact Or.inl hy.2
        · refine ⟨Subtype.val ⁻¹' U i, ?_, hU i hi, hxi⟩
          intro y hy
          exact Or.inr ⟨i, hi, hiT, hy⟩
      have hQo : IsOpen Q := by
        refine isOpen_iff_forall_mem_open.2 ?_
        intro x hx
        obtain ⟨i, hi, hxi⟩ := hmemW x
        rcases hx with hx | hx
        · refine ⟨Subtype.val ⁻¹' (U i \ K), ?_, hKW i hi, ⟨hxi, hx⟩⟩
          intro y hy
          exact Or.inl hy.2
        · have hia : i ≠ a := by
            rintro rfl
            exact hx hxi
          refine ⟨Subtype.val ⁻¹' U i, ?_, hU i hi, hxi⟩
          intro y hy
          exact Or.inr (Set.disjoint_left.1 (hdisj i hi a has hia) hy)
      have hPQ : P ∪ Q = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        by_cases hxa : x.1 ∈ U a
        · exact Or.inl (Or.inr ⟨a, has, haT, hxa⟩)
        · exact Or.inr (Or.inr hxa)
      have hPQi : P ∩ Q = C (insert a T) := by
        ext x
        constructor
        · rintro ⟨hxP, hxQ⟩
          rcases hxP with hxK | ⟨i, hi, hiT, hxi⟩
          · exact Or.inl hxK
          · rcases hxQ with hxK | hxa
            · exact Or.inl hxK
            · have hia : i ≠ a := by
                rintro rfl
                exact hxa hxi
              refine Or.inr ⟨i, hi, ?_, hxi⟩
              rw [Finset.mem_insert, not_or]
              exact ⟨hia, hiT⟩
        · rintro (hxK | ⟨i, hi, hiT, hxi⟩)
          · exact ⟨Or.inl hxK, Or.inl hxK⟩
          · rw [Finset.mem_insert, not_or] at hiT
            refine ⟨Or.inr ⟨i, hi, hiT.2, hxi⟩, Or.inr ?_⟩
            exact Set.disjoint_left.1 (hdisj i hi a has hiT.1) hxi
      have h₁ : IsZero (relativeHomology integerCoefficients (TopCat.of ↥W) (P ∪ Q) (j + 1)) := by
        rw [hPQ]
        exact huniv (j + 1)
      have hVa : IsOpen (Subtype.val ⁻¹' U a : Set ↥W) := hU a has
      have hVQ : (Subtype.val ⁻¹' U a : Set ↥W) ∪ Q = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_univ, iff_true]
        by_cases hxa : x.1 ∈ U a
        · exact Or.inl hxa
        · exact Or.inr (Or.inr hxa)
      have hexc := excision_open integerCoefficients (X := TopCat.of ↥W) hVa hQo hVQ j
      have hUaW : U a ⊆ W := fun x hx => by
        rw [← hW, Set.mem_iUnion₂]
        exact ⟨a, has, hx⟩
      have hsets : (Subtype.val ⁻¹' Q : Set ↥(Subtype.val ⁻¹' U a : Set ↥W)) =
          Subtype.val ⁻¹' (Subtype.val ⁻¹' (U a \ K)) := by
        ext y
        constructor
        · rintro (hy | hy)
          · exact ⟨y.2, hy⟩
          · exact absurd y.2 hy
        · rintro ⟨_, hy⟩
          exact Or.inl hy
      have hsrc : IsZero (relativeHomology integerCoefficients (TopCat.of ↥(Subtype.val ⁻¹' U a : Set ↥W))
          (Subtype.val ⁻¹' Q) j) := by
        rw [hsets]
        exact IsZero.of_iso (h0 a has) (relativeHomologyIsoOfSubtypeSubtype integerCoefficients hUaW (U a \ K) j)
      have hQz : IsZero (relativeHomology integerCoefficients (TopCat.of ↥W) Q j) :=
        IsZero.of_iso hsrc (@asIso _ _ _ _ _ hexc).symm
      have := isZero_relativeHomology_inter_of_isZero integerCoefficients hPo hQo j h₁ hPz hQz
      rw [hPQi] at this
      exact this
  have hfin : C s = (Subtype.val ⁻¹' (W \ K) : Set ↥W) := by
    ext x
    constructor
    · rintro (hx | ⟨i, hi, his, _⟩)
      · exact ⟨x.2, hx⟩
      · exact absurd hi his
    · rintro ⟨_, hx⟩
      exact Or.inl hx
  have := key s (subset_refl s)
  rw [hfin] at this
  exact this

theorem relativeHomologyPair_iUnion_basis {ι : Type*} (s : Finset ι) (U : ι → Set X) (K : Set X)
    (hU : ∀ i ∈ s, IsOpen (Subtype.val ⁻¹' U i : Set ↥(⋃ i ∈ s, U i)))
    (hK : ∀ i ∈ s, IsOpen (Subtype.val ⁻¹' (U i \ K) : Set ↥(U i)))
    (hdisj : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → Disjoint (U i) (U i')) {j : ℕ}
    (F : ι → EuclideanSpace ℝ (Fin j) → X)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk j))) (ULift.down ⁻¹' diskSphere j) j)
    (hspan : ∀ i ∈ s, ∀ y : relativeHomologyPair (U i) (U i \ K) j, ∃ m : ℤ,
      y = m • discClass (U i) (U i \ K) (F i) g)
    (hind : ∀ i ∈ s, ∀ m : ℤ, m • discClass (U i) (U i \ K) (F i) g = 0 → m = 0) :
    (∀ y : relativeHomologyPair (⋃ i ∈ s, U i) ((⋃ i ∈ s, U i) \ K) j, ∃ v : ι → ℤ,
      y = ∑ i ∈ s, v i • discClass (⋃ i ∈ s, U i) ((⋃ i ∈ s, U i) \ K) (F i) g) ∧
    ∀ v : ι → ℤ, ∑ i ∈ s, v i • discClass (⋃ i ∈ s, U i) ((⋃ i ∈ s, U i) \ K) (F i) g = 0 →
      ∀ i ∈ s, v i = 0 := by
  classical
  set Xs : Set X := ⋃ i ∈ s, U i with hXs
  have hsub : ∀ i ∈ s, U i ⊆ Xs := fun i hi x hx => Set.mem_iUnion₂.2 ⟨i, hi, hx⟩
  have hsubA : ∀ i ∈ s, U i \ K ⊆ Xs \ K := fun i hi => Set.sdiff_subset_sdiff_left (hsub i hi)
  have hcomp : ∀ {P Q W : TopCat.{u}} {A : Set P} {B : Set Q} {D : Set W} (f : P ⟶ Q)
      (f' : Q ⟶ W) (hf : Set.MapsTo f A B) (hf' : Set.MapsTo f' B D) (x : relativeHomology integerCoefficients P A j),
      relativeHomologyMap integerCoefficients f' hf' j (relativeHomologyMap integerCoefficients f hf j x) = relativeHomologyMap integerCoefficients (f ≫ f') (mapsTo_comp hf hf') j x := by
    intro P Q W A B D f f' hf hf' x
    rw [relativeHomologyMap_comp integerCoefficients f f' hf hf' (mapsTo_comp hf hf') j]
    rfl
  have hzero : ∀ (W : TopCat.{u}) (k : ℕ), IsZero (relativeHomology integerCoefficients W Set.univ k) := by
    intro W k
    have h1 : IsIso (incl W Set.univ) := by
      rw [show incl W Set.univ = (TopCat.isoOfHomeo (Homeomorph.Set.univ W)).hom from rfl]
      infer_instance
    have h2 : IsIso (pair W Set.univ).hom :=
      inferInstanceAs (IsIso (TopCat.toSSet.map (incl W Set.univ)))
    exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_isZero
      (SSetPair.isZero_chainComplex (pair W Set.univ) integerCoefficients)
  have hFi : ∀ i ∈ s, ContinuousOn (F i) (Metric.closedBall 0 1) ∧
      MapsTo (F i) (Metric.closedBall 0 1) (U i) ∧ MapsTo (F i) (Metric.sphere 0 1) (U i \ K) := by
    intro i hi
    by_contra h
    have h1 := hind i hi 1 (by
      rw [discClass, dite_eq_right_of_eq_false (eq_false h)]
      simp)
    exact one_ne_zero h1
  have hde : ∀ i (hi : i ∈ s), inclPair (hsub i hi) (hsubA i hi) j
      (discClass (U i) (U i \ K) (F i) g) = discClass Xs (Xs \ K) (F i) g := by
    intro i hi
    have hc := hFi i hi
    have hc' : ContinuousOn (F i) (Metric.closedBall 0 1) ∧
        MapsTo (F i) (Metric.closedBall 0 1) Xs ∧ MapsTo (F i) (Metric.sphere 0 1) (Xs \ K) :=
      ⟨hc.1, hc.2.1.mono_right (hsub i hi), hc.2.2.mono_right (hsubA i hi)⟩
    rw [discClass, discClass, dite_eq_left_of_eq_true (eq_true hc),
      dite_eq_left_of_eq_true (eq_true hc'), inclPair]
    refine (hcomp _ _ _ _ g).trans ?_
    rfl
  let B : ι → Set ↥Xs := fun i => Subtype.val ⁻¹' (U i ∩ K)ᶜ
  have hBopen : ∀ i ∈ s, IsOpen (B i) := by
    intro i hi
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 x.2
    by_cases hii : i' = i
    · subst hii
      obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.1 (hK i' hi)
      have hxK : x.1 ∉ K := fun hxK => hx ⟨hxi', hxK⟩
      have hxO : (⟨x.1, hxi'⟩ : ↥(U i')) ∈ Subtype.val ⁻¹' O := by
        rw [hOeq]
        exact ⟨hxi', hxK⟩
      refine ⟨Subtype.val ⁻¹' U i' ∩ Subtype.val ⁻¹' O, ?_, (hU i' hi').inter
        (hO.preimage continuous_subtype_val), ⟨hxi', hxO⟩⟩
      rintro y ⟨hyU, hyO⟩ ⟨_, hyK⟩
      have : (⟨y.1, hyU⟩ : ↥(U i')) ∈ Subtype.val ⁻¹' O := hyO
      rw [hOeq] at this
      exact this.2 hyK
    · refine ⟨Subtype.val ⁻¹' U i', ?_, hU i' hi', hxi'⟩
      rintro y hyU ⟨hyUi, _⟩
      exact Set.disjoint_left.1 (hdisj i' hi' i hi hii) hyU hyUi
  have hπmaps : ∀ i, Set.MapsTo (𝟙 (TopCat.of ↥Xs))
      (Subtype.val ⁻¹' (Xs \ K) : Set ↥Xs) (B i) := fun i x hx hx' => hx.2 hx'.2
  let π : ∀ i, relativeHomologyPair Xs (Xs \ K) j ⟶ relativeHomology integerCoefficients (TopCat.of ↥Xs) (B i) j := fun i =>
    relativeHomologyMap integerCoefficients (𝟙 (TopCat.of ↥Xs)) (hπmaps i) j
  have hcover : ∀ i, (Subtype.val ⁻¹' U i : Set ↥Xs) ∪ B i = Set.univ := by
    intro i
    ext x
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, Set.mem_inter_iff, B,
      Set.mem_univ, iff_true]
    tauto
  have hseq : ∀ i, (Subtype.val ⁻¹' (U i \ K) : Set ↥(U i)) = Subtype.val ⁻¹' (U i ∩ K)ᶜ := by
    intro i
    ext x
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff, Set.mem_inter_iff]
    have := x.2
    tauto
  let E : ∀ i, i ∈ s → (relativeHomologyPair (U i) (U i \ K) j ≅ relativeHomology integerCoefficients (TopCat.of ↥Xs) (B i) j) :=
    fun i hi => relativeHomologyIsoOfEq integerCoefficients (TopCat.of ↥(U i)) (hseq i) j ≪≫
      (relativeHomologyIsoOfSubtypeSubtype integerCoefficients (hsub i hi) ((U i ∩ K)ᶜ) j).symm ≪≫
      excisionOpenIso integerCoefficients (X := TopCat.of ↥Xs) (hU i hi) (hBopen i hi) (hcover i) j
  have hE : ∀ i (hi : i ∈ s) (z : relativeHomologyPair (U i) (U i \ K) j),
      π i (inclPair (hsub i hi) (hsubA i hi) j z) = (E i hi).hom z := by
    intro i hi z
    simp only [E, π, inclPair, Iso.trans_hom, Iso.symm_hom, ModuleCat.comp_apply,
      excisionOpenIso, asIso_hom, relativeHomologyIsoOfSubtypeSubtype, relativeHomologyIsoOfHomeomorphImage_inv,
      relativeHomologyIsoOfEq, hcomp]
    rfl
  have hK2 : ∀ i ∈ s, ∀ i' (hi' : i' ∈ s), i ≠ i' → ∀ z : relativeHomologyPair (U i') (U i' \ K) j,
      π i (inclPair (hsub i' hi') (hsubA i' hi') j z) = 0 := by
    intro i hi i' hi' hne z
    have hm1 : Set.MapsTo (𝟙 (TopCat.of ↥(U i'))) (Subtype.val ⁻¹' (U i' \ K)) Set.univ :=
      fun _ _ => trivial
    have hm2 : Set.MapsTo (inclOfLE (X := TopCat.of X) (hsub i' hi')) Set.univ (B i) :=
      fun x _ hx => Set.disjoint_left.1 (hdisj i hi i' hi' hne) hx.1 x.2
    have h1 : π i (inclPair (hsub i' hi') (hsubA i' hi') j z) =
        relativeHomologyMap integerCoefficients (inclOfLE (X := TopCat.of X) (hsub i' hi')) hm2 j
          (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of ↥(U i'))) hm1 j z) := by
      simp only [π, inclPair, hcomp]
      rfl
    have h2 : relativeHomologyMap integerCoefficients (𝟙 (TopCat.of ↥(U i'))) hm1 j z = 0 :=
      (ModuleCat.isZero_iff_subsingleton.1 (hzero (TopCat.of ↥(U i')) j)).elim _ _
    rw [h1, h2, map_zero]
  have hK3 : ∀ t : Finset ι, t ⊆ s → ∀ C : Set ↥Xs, C = ⋂ i ∈ t, B i →
      ∀ y : relativeHomology integerCoefficients (TopCat.of ↥Xs) C j,
      (∀ i ∈ t, ∀ h : Set.MapsTo (𝟙 (TopCat.of ↥Xs)) C (B i), relativeHomologyMap integerCoefficients (𝟙 _) h j y = 0) →
        y = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ C hC y _
      have hz : IsZero (relativeHomology integerCoefficients (TopCat.of ↥Xs) C j) := by
        rw [hC]
        simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ]
        exact hzero _ j
      exact (ModuleCat.isZero_iff_subsingleton.1 hz).elim _ _
    | insert a t ha ih =>
      intro hts C hC y hy
      have haS : a ∈ s := hts (Finset.mem_insert_self a t)
      have hts' : t ⊆ s := (Finset.subset_insert a t).trans hts
      rw [Finset.set_biInter_insert] at hC
      subst hC
      refine relMV_injective integerCoefficients (hBopen a haS)
        (isOpen_biInter_finset fun i hi => hBopen i (hts' hi)) j ?_ y ?_ ?_
      · have hun : B a ∪ ⋂ i ∈ t, B i = Set.univ := by
          ext x
          simp only [Set.mem_union, Set.mem_iInter, Set.mem_univ, iff_true]
          by_cases hxa : x ∈ B a
          · exact Or.inl hxa
          · right
            intro i hi hxi
            have hia : i ≠ a := fun h => ha (h ▸ hi)
            have hxa' : x.1 ∈ U a ∩ K := by simpa [B] using hxa
            have hxi' : x.1 ∈ U i ∩ K := by simpa [B] using hxi
            exact Set.disjoint_left.1 (hdisj a haS i (hts' hi) hia.symm) hxa'.1 hxi'.1
        rw [hun]
        exact hzero _ (j + 1)
      · exact hy a (Finset.mem_insert_self a t) _
      · refine ih hts' _ rfl _ ?_
        intro i hi h
        rw [hcomp]
        exact hy i (Finset.mem_insert_of_mem hi) _
  have hdi : ∀ i (hi : i ∈ s), π i (discClass Xs (Xs \ K) (F i) g) =
      (E i hi).hom (discClass (U i) (U i \ K) (F i) g) := by
    intro i hi
    rw [← hde i hi, hE i hi]
  have hdo : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → π i (discClass Xs (Xs \ K) (F i') g) = 0 := by
    intro i hi i' hi' hne
    rw [← hde i' hi', hK2 i hi i' hi' hne]
  have hπsum : ∀ i (hi : i ∈ s) (v : ι → ℤ),
      π i (∑ i' ∈ s, v i' • discClass Xs (Xs \ K) (F i') g) =
        v i • (E i hi).hom (discClass (U i) (U i \ K) (F i) g) := by
    intro i hi v
    rw [map_sum, Finset.sum_eq_single i]
    · rw [map_zsmul, hdi i hi]
    · intro b hb hbi
      rw [map_zsmul, hdo i hi b hb (Ne.symm hbi)]
      exact zsmul_zero _
    · intro h
      exact absurd hi h
  have hAeq : (Subtype.val ⁻¹' (Xs \ K) : Set ↥Xs) = ⋂ i ∈ s, B i := by
    ext x
    simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_iInter, B, Set.mem_compl_iff,
      Set.mem_inter_iff]
    constructor
    · rintro ⟨_, hxK⟩ i _ ⟨_, h⟩
      exact hxK h
    · intro h
      obtain ⟨i₀, hi₀, hxi₀⟩ := Set.mem_iUnion₂.1 x.2
      exact ⟨x.2, fun hxK => h i₀ hi₀ ⟨hxi₀, hxK⟩⟩
  have hinj : ∀ y : relativeHomologyPair Xs (Xs \ K) j, (∀ i ∈ s, π i y = 0) → y = 0 := fun y hy =>
    hK3 s subset_rfl _ hAeq y (fun i hi _ => hy i hi)
  refine ⟨fun y => ?_, fun v hv i hi => ?_⟩
  · have hm : ∀ i (hi : i ∈ s), ∃ m : ℤ,
        (E i hi).inv (π i y) = m • discClass (U i) (U i \ K) (F i) g :=
      fun i hi => hspan i hi _
    choose m hm using hm
    refine ⟨fun i => if hi : i ∈ s then m i hi else 0, ?_⟩
    rw [← sub_eq_zero]
    apply hinj
    intro i hi
    rw [map_sub, hπsum i hi]
    beta_reduce
    rw [dite_eq_left_of_eq_true (eq_true hi), ← map_zsmul, ← hm i hi, Iso.inv_hom_id_apply,
      sub_self]
  · have h1 := congrArg (π i) hv
    rw [hπsum i hi, map_zero, ← map_zsmul] at h1
    apply hind i hi
    have h2 := congrArg (E i hi).inv h1
    rwa [Iso.hom_inv_id_apply, map_zero] at h2

end Handle

namespace Handle

open CategoryTheory Limits SingularPair

universe u

theorem relativeHomologyMap_eq_of_homotopy {X Y : TopCat.{u}} {A : Set X} {B : Set Y} (f₀ f₁ : X ⟶ Y)
    (h₀ : MapsTo f₀ A B) (h₁ : MapsTo f₁ A B) (F : ContinuousMap.Homotopy f₀.hom f₁.hom)
    (hF : ∀ t, ∀ x ∈ A, F (t, x) ∈ B) (k : ℕ) :
    relativeHomologyMap integerCoefficients f₀ h₀ k = relativeHomologyMap integerCoefficients f₁ h₁ k := by
  let P : TopCat.{u} := TopCat.of (unitInterval × X)
  let PA : Set (unitInterval × X) := {q | q.2 ∈ A}
  let i₀ : X ⟶ P := TopCat.ofHom ⟨fun x => ((0 : unitInterval), x), by fun_prop⟩
  let i₁ : X ⟶ P := TopCat.ofHom ⟨fun x => ((1 : unitInterval), x), by fun_prop⟩
  let p : P ⟶ X := TopCat.ofHom ⟨fun q : unitInterval × X => q.2, by fun_prop⟩
  let Fm : P ⟶ Y := TopCat.ofHom F.toContinuousMap
  have hi₀ : MapsTo i₀ A PA := fun _ hx => hx
  have hi₁ : MapsTo i₁ A PA := fun _ hx => hx
  have hp : MapsTo p PA A := fun _ hq => hq
  have hFm : MapsTo Fm PA B := fun q hq => hF q.1 q.2 hq
  have hcongr : ∀ {S T : TopCat.{u}} {C : Set S} {D : Set T} (g g' : S ⟶ T)
      (hg : MapsTo g C D) (hg' : MapsTo g' C D), g = g' →
      relativeHomologyMap integerCoefficients g hg k = relativeHomologyMap integerCoefficients g' hg' k := by
    rintro S T C D g g' hg hg' rfl
    rfl
  have e₀ : f₀ = i₀ ≫ Fm := by
    ext x
    exact (F.apply_zero x).symm
  have e₁ : f₁ = i₁ ≫ Fm := by
    ext x
    exact (F.apply_one x).symm
  let eX : ContinuousMap.HomotopyEquiv (unitInterval × X) X :=
    { toFun := ⟨fun q : unitInterval × X => q.2, by fun_prop⟩
      invFun := ⟨fun x => ((0 : unitInterval), x), by fun_prop⟩
      left_inv := ⟨{ toFun := fun r : unitInterval × (unitInterval × X) => (r.1 * r.2.1, r.2.2)
                     continuous_toFun := by fun_prop
                     map_zero_left := fun q => by simp
                     map_one_left := fun q => by simp }⟩
      right_inv := ContinuousMap.Homotopic.refl _ }
  let eA : ContinuousMap.HomotopyEquiv ↥PA ↥A :=
    { toFun := ⟨fun q : ↥PA => (⟨(q : unitInterval × X).2, q.2⟩ : ↥A), by fun_prop⟩
      invFun := ⟨fun a : ↥A => (⟨((0 : unitInterval), (a : X)), a.2⟩ : ↥PA), by fun_prop⟩
      left_inv := ⟨{ toFun := fun r : unitInterval × ↥PA =>
                       (⟨(r.1 * (r.2 : unitInterval × X).1, (r.2 : unitInterval × X).2),
                         r.2.2⟩ : ↥PA)
                     continuous_toFun := by fun_prop
                     map_zero_left := fun q => by ext <;> simp
                     map_one_left := fun q => by ext <;> simp }⟩
      right_inv := ContinuousMap.Homotopic.refl _ }
  have hpX : ∀ n, IsIso (singularHomologyMap integerCoefficients p n) := fun n => by
    have h : TopCat.ofHom eX.toFun = p := rfl
    rw [← h]
    exact isIso_singularHomologyMap_of_homotopyEquiv integerCoefficients eX n
  have hpA : ∀ n, IsIso (singularHomologyMap integerCoefficients (restr p hp) n) := fun n => by
    have h : TopCat.ofHom eA.toFun = restr p hp := rfl
    rw [← h]
    exact isIso_singularHomologyMap_of_homotopyEquiv integerCoefficients eA n
  have : IsIso (relativeHomologyMap integerCoefficients p hp k) := isIso_relativeHomologyMap_of_isIso_singularHomologyMap integerCoefficients p hp hpA hpX k
  have hid₀ : i₀ ≫ p = 𝟙 X := rfl
  have hid₁ : i₁ ≫ p = 𝟙 X := rfl
  have hA : MapsTo (𝟙 X) A A := fun _ hx => hx
  have hi : relativeHomologyMap integerCoefficients i₀ hi₀ k = relativeHomologyMap integerCoefficients i₁ hi₁ k := by
    refine (cancel_mono (relativeHomologyMap integerCoefficients p hp k)).1 ?_
    refine (relativeHomologyMap_comp integerCoefficients i₀ p hi₀ hp (hid₀ ▸ hA) k).symm.trans ?_
    refine (hcongr (i₀ ≫ p) (i₁ ≫ p) _ (hid₁ ▸ hA) (hid₀.trans hid₁.symm)).trans ?_
    exact relativeHomologyMap_comp integerCoefficients i₁ p hi₁ hp (hid₁ ▸ hA) k
  refine (hcongr f₀ (i₀ ≫ Fm) h₀ (fun _ hx => hFm (hi₀ hx)) e₀).trans ?_
  refine (relativeHomologyMap_comp integerCoefficients i₀ Fm hi₀ hFm _ k).trans ?_
  refine (congrArg (· ≫ relativeHomologyMap integerCoefficients Fm hFm k) hi).trans ?_
  refine (relativeHomologyMap_comp integerCoefficients i₁ Fm hi₁ hFm (fun _ hx => hFm (hi₁ hx)) k).symm.trans ?_
  exact (hcongr f₁ (i₁ ≫ Fm) h₁ (fun _ hx => hFm (hi₁ hx)) e₁).symm

theorem isIso_relativeHomologyMap_of_pairHomotopyEquiv {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (g : Y ⟶ X) (hf : MapsTo f A B) (hg : MapsTo g B A)
    (F : ContinuousMap.Homotopy (f ≫ g).hom (ContinuousMap.id X)) (hF : ∀ t, ∀ x ∈ A, F (t, x) ∈ A)
    (G : ContinuousMap.Homotopy (g ≫ f).hom (ContinuousMap.id Y)) (hG : ∀ t, ∀ y ∈ B, G (t, y) ∈ B)
    (k : ℕ) : IsIso (relativeHomologyMap integerCoefficients f hf k) := by
  have hfg : MapsTo (f ≫ g) A A := hg.comp hf
  have hgf : MapsTo (g ≫ f) B B := hf.comp hg
  have hidX : MapsTo (𝟙 X) A A := fun _ hx => hx
  have hidY : MapsTo (𝟙 Y) B B := fun _ hy => hy
  have e1 : relativeHomologyMap integerCoefficients (f ≫ g) hfg k = relativeHomologyMap integerCoefficients (𝟙 X) hidX k :=
    relativeHomologyMap_eq_of_homotopy (f ≫ g) (𝟙 X) hfg hidX F hF k
  have e2 : relativeHomologyMap integerCoefficients (g ≫ f) hgf k = relativeHomologyMap integerCoefficients (𝟙 Y) hidY k :=
    relativeHomologyMap_eq_of_homotopy (g ≫ f) (𝟙 Y) hgf hidY G hG k
  refine ⟨⟨relativeHomologyMap integerCoefficients g hg k, ?_, ?_⟩⟩
  · rw [← relativeHomologyMap_comp integerCoefficients f g hf hg hfg k, e1, relativeHomologyMap_id]
  · rw [← relativeHomologyMap_comp integerCoefficients g f hg hf hgf k, e2, relativeHomologyMap_id]

variable {X : Type u} [TopologicalSpace X]

theorem discClass_eq_of_homotopy (B A : Set X) {m : ℕ} (F₀ F₁ : EuclideanSpace ℝ (Fin m) → X)
    (Hm : ℝ → EuclideanSpace ℝ (Fin m) → X)
    (hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Hm p.1 p.2)
      (Icc 0 1 ×ˢ Metric.closedBall 0 1))
    (h0 : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, Hm 0 y = F₀ y)
    (h1 : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, Hm 1 y = F₁ y)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Metric.closedBall 0 1) B)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (Metric.sphere 0 1) A)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m) :
    discClass B A F₀ g = discClass B A F₁ g := by
  have hsub : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 ⊆ Metric.closedBall 0 1 :=
    Metric.sphere_subset_closedBall
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousOn (Hm t) (Metric.closedBall 0 1) := by
    intro t ht
    have := hH.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id)
      (s := Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1))
      (fun y hy => (⟨ht, hy⟩ : (t, y) ∈ Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 1))
    exact this
  have hd0 : ContinuousOn F₀ (Metric.closedBall 0 1) ∧ MapsTo F₀ (Metric.closedBall 0 1) B ∧
      MapsTo F₀ (Metric.sphere 0 1) A := by
    refine ⟨(hcont 0 hI0).congr (fun y hy => (h0 y hy).symm), fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h0 y hy]; exact hB 0 hI0 hy
    · rw [← h0 y (hsub hy)]; exact hA 0 hI0 hy
  have hd1 : ContinuousOn F₁ (Metric.closedBall 0 1) ∧ MapsTo F₁ (Metric.closedBall 0 1) B ∧
      MapsTo F₁ (Metric.sphere 0 1) A := by
    refine ⟨(hcont 1 hI1).congr (fun y hy => (h1 y hy).symm), fun y hy => ?_, fun y hy => ?_⟩
    · rw [← h1 y hy]; exact hB 1 hI1 hy
    · rw [← h1 y (hsub hy)]; exact hA 1 hI1 hy
  unfold discClass
  rw [dite_eq_left hd0, dite_eq_left hd1]
  let Hom : ContinuousMap.Homotopy
      (TopCat.ofHom (X := TopCat.of (ULift.{u} (Disk m))) (Y := TopCat.of ↥B)
        ⟨fun x : ULift.{u} (Disk m) => (⟨F₀ x.down.1, hd0.2.1 x.down.2⟩ : ↥B),
        (hd0.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2)).subtype_mk _⟩).hom
      (TopCat.ofHom (X := TopCat.of (ULift.{u} (Disk m))) (Y := TopCat.of ↥B)
        ⟨fun x : ULift.{u} (Disk m) => (⟨F₁ x.down.1, hd1.2.1 x.down.2⟩ : ↥B),
        (hd1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2)).subtype_mk _⟩).hom :=
    { toFun := fun p => ⟨Hm p.1.1 p.2.down.1, hB p.1.1 p.1.2 p.2.down.2⟩
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact hH.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk
            (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)))
          (fun p => ⟨p.1.2, p.2.down.2⟩)
      map_zero_left := fun x => Subtype.ext (h0 x.down.1 x.down.2)
      map_one_left := fun x => Subtype.ext (h1 x.down.1 x.down.2) }
  have hF : ∀ (t : unitInterval) (x : ULift.{u} (Disk m)),
      x ∈ (ULift.down ⁻¹' diskSphere m : Set (ULift.{u} (Disk m))) →
        Hom (t, x) ∈ (Subtype.val ⁻¹' A : Set ↥B) :=
    fun t x hx => hA t.1 t.2 hx
  exact congrArg (fun φ => (ConcreteCategory.hom φ) g)
    (relativeHomologyMap_eq_of_homotopy _ _ (fun _ hx => hd0.2.2 hx) (fun _ hx => hd1.2.2 hx) Hom hF m)

theorem sphereClass_eq_of_homotopy (B A : Set X) {ℓ : ℕ} (F₀ F₁ : EuclideanSpace ℝ (Fin (ℓ + 1)) → X)
    (Hm : ℝ → EuclideanSpace ℝ (Fin (ℓ + 1)) → X)
    (hH : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin (ℓ + 1)) => Hm p.1 p.2)
      (Icc 0 1 ×ˢ unitSphere ℓ))
    (h0 : ∀ y ∈ unitSphere ℓ, Hm 0 y = F₀ y) (h1 : ∀ y ∈ unitSphere ℓ, Hm 1 y = F₁ y)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (Hm t) (unitSphere ℓ) B)
    (g : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ) :
    sphereClass B A F₀ g = sphereClass B A F₁ g := by
  have hc0 : ContinuousOn F₀ (unitSphere ℓ) := by
    have h : ContinuousOn (fun y => Hm 0 y) (unitSphere ℓ) :=
      hH.comp (Continuous.continuousOn (by fun_prop))
        (fun y hy => Set.mk_mem_prod (Set.left_mem_Icc.2 zero_le_one) hy)
    exact h.congr (fun y hy => (h0 y hy).symm)
  have hc1 : ContinuousOn F₁ (unitSphere ℓ) := by
    have h : ContinuousOn (fun y => Hm 1 y) (unitSphere ℓ) :=
      hH.comp (Continuous.continuousOn (by fun_prop))
        (fun y hy => Set.mk_mem_prod (Set.right_mem_Icc.2 zero_le_one) hy)
    exact h.congr (fun y hy => (h1 y hy).symm)
  have hm0 : MapsTo F₀ (unitSphere ℓ) B := fun y hy =>
    (h0 y hy) ▸ hB 0 (Set.left_mem_Icc.2 zero_le_one) hy
  have hm1 : MapsTo F₁ (unitSphere ℓ) B := fun y hy =>
    (h1 y hy) ▸ hB 1 (Set.right_mem_Icc.2 zero_le_one) hy
  have hC0 : ContinuousOn F₀ (unitSphere ℓ) ∧ MapsTo F₀ (unitSphere ℓ) B := ⟨hc0, hm0⟩
  have hC1 : ContinuousOn F₁ (unitSphere ℓ) ∧ MapsTo F₁ (unitSphere ℓ) B := ⟨hc1, hm1⟩
  unfold sphereClass
  rw [dite_eq_left hC0, dite_eq_left hC1]
  let f₀ : Sphere.liftedSphere.{u} ℓ ⟶ TopCat.of ↥B :=
    TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere ℓ) => (⟨F₀ x.down.1, hC0.2 x.down.2⟩ : ↥B),
      (hC0.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun x => x.down.2)).subtype_mk _⟩
  let f₁ : Sphere.liftedSphere.{u} ℓ ⟶ TopCat.of ↥B :=
    TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere ℓ) => (⟨F₁ x.down.1, hC1.2 x.down.2⟩ : ↥B),
      (hC1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun x => x.down.2)).subtype_mk _⟩
  have hcont : Continuous (fun p : unitInterval × ULift.{u} (unitSphere ℓ) =>
      (⟨Hm (p.1 : ℝ) p.2.down.1, hB _ p.1.2 p.2.down.2⟩ : ↥B)) := by
    refine Continuous.subtype_mk ?_ _
    have hp : Continuous (fun p : unitInterval × ULift.{u} (unitSphere ℓ) =>
        ((p.1 : ℝ), (p.2.down.1 : EuclideanSpace ℝ (Fin (ℓ + 1))))) := by fun_prop
    exact hH.comp_continuous hp (fun p => Set.mk_mem_prod p.1.2 p.2.down.2)
  let Hom : TopCat.Homotopy f₀ f₁ :=
    { toFun := fun p => ⟨Hm (p.1 : ℝ) p.2.down.1, hB _ p.1.2 p.2.down.2⟩
      continuous_toFun := hcont
      map_zero_left := fun x => Subtype.ext (h0 _ x.down.2)
      map_one_left := fun x => Subtype.ext (h1 _ x.down.2) }
  have hEq : singularHomologyMap integerCoefficients f₀ ℓ = singularHomologyMap integerCoefficients f₁ ℓ :=
    TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor Hom integerCoefficients ℓ
  change (singularHomologyMap integerCoefficients f₀ ℓ ≫ relπ integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) ℓ) g =
    (singularHomologyMap integerCoefficients f₁ ℓ ≫ relπ integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) ℓ) g
  rw [hEq]

theorem sphereClass_congr (B A : Set X) {ℓ : ℕ} {F G : EuclideanSpace ℝ (Fin (ℓ + 1)) → X}
    (hFG : ∀ z ∈ unitSphere ℓ, F z = G z) (g : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ) :
    sphereClass B A F g = sphereClass B A G g := by
  unfold sphereClass
  by_cases h : ContinuousOn F (unitSphere ℓ) ∧ MapsTo F (unitSphere ℓ) B
  · have hG : ContinuousOn G (unitSphere ℓ) ∧ MapsTo G (unitSphere ℓ) B :=
      ⟨h.1.congr (fun z hz => (hFG z hz).symm), fun z hz => hFG z hz ▸ h.2 hz⟩
    rw [dite_eq_left h, dite_eq_left hG]
    congr 4
    ext x
    exact hFG _ x.down.2
  · have hG : ¬ (ContinuousOn G (unitSphere ℓ) ∧ MapsTo G (unitSphere ℓ) B) := fun hG =>
      h ⟨hG.1.congr (fun z hz => hFG z hz), fun z hz => (hFG z hz).symm ▸ hG.2 hz⟩
    rw [dite_eq_right h, dite_eq_right hG]

theorem inclPair_discClass {B A B' A' : Set X} (hB : B ⊆ B') (hA : A ⊆ A') {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → X) (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hFB : MapsTo F (Metric.closedBall 0 1) B) (hFA : MapsTo F (Metric.sphere 0 1) A)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m) :
    inclPair hB hA m (discClass B A F g) = discClass B' A' F g := by
  have h : ContinuousOn F (Metric.closedBall 0 1) ∧ MapsTo F (Metric.closedBall 0 1) B ∧
      MapsTo F (Metric.sphere 0 1) A := ⟨hF, hFB, hFA⟩
  have h' : ContinuousOn F (Metric.closedBall 0 1) ∧ MapsTo F (Metric.closedBall 0 1) B' ∧
      MapsTo F (Metric.sphere 0 1) A' := ⟨hF, hFB.mono_right hB, hFA.mono_right hA⟩
  unfold discClass
  rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h'), inclPair]
  let f : TopCat.of (ULift.{u} (Disk m)) ⟶ TopCat.of ↥B :=
    TopCat.ofHom ⟨fun x : ULift.{u} (Disk m) => (⟨F x.down.1, h.2.1 x.down.2⟩ : ↥B),
      (h.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun x => x.down.2)).subtype_mk _⟩
  have hf : MapsTo f (ULift.down ⁻¹' diskSphere m) (Subtype.val ⁻¹' A) :=
    fun _ hx => h.2.2 hx
  have key := relativeHomologyMap_comp integerCoefficients f (inclOfLE (X := TopCat.of X) hB) hf
    (mapsTo_inclOfLE_preimage hB hA) (fun _ hx => h'.2.2 hx) m
  exact (congrArg (fun φ => φ g) key).symm

theorem inclPair_sphereClass {B A B' A' : Set X} (hB : B ⊆ B') (hA : A ⊆ A') {ℓ : ℕ}
    (F : EuclideanSpace ℝ (Fin (ℓ + 1)) → X) (hF : ContinuousOn F (unitSphere ℓ))
    (hFB : MapsTo F (unitSphere ℓ) B) (g : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ) :
    inclPair hB hA ℓ (sphereClass B A F g) = sphereClass B' A' F g := by
  have h1 : ContinuousOn F (unitSphere ℓ) ∧ MapsTo F (unitSphere ℓ) B := ⟨hF, hFB⟩
  have h2 : ContinuousOn F (unitSphere ℓ) ∧ MapsTo F (unitSphere ℓ) B' := ⟨hF, fun _ hx => hB (hFB hx)⟩
  unfold sphereClass
  rw [dite_eq_left_of_eq_true (eq_true h1), dite_eq_left_of_eq_true (eq_true h2)]
  have hnat := relπ_natural integerCoefficients (inclOfLE (X := TopCat.of X) hB)
    (mapsTo_inclOfLE_preimage hB hA) ℓ
  have key := congrArg (fun φ => (singularHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere ℓ) =>
      (⟨F x.down.1, h1.2 x.down.2⟩ : ↥B),
      (h1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
        (fun x => x.down.2)).subtype_mk _⟩) ℓ ≫ φ) g) hnat
  simp only [← Category.assoc, ← singularHomologyMap_comp] at key
  simp only [ModuleCat.comp_apply] at key ⊢
  unfold inclPair
  exact key

end Handle

namespace Handle

open CategoryTheory SingularPair

universe u

def euMap {μ : ℕ} (A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ)) :
    TopCat.of (EU.{u} μ) ⟶ TopCat.of (EU.{u} μ) :=
  TopCat.ofHom ⟨fun x => ULift.up (A x.down),
    continuous_uliftUp.comp (A.continuous.comp continuous_uliftDown)⟩

theorem euMap_mapsTo {μ : ℕ} (A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ)) :
    MapsTo (euMap.{u} A) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) {ULift.up 0}ᶜ := by
  intro x hx hAx
  apply hx
  have h1 : A x.down = 0 := congrArg ULift.down hAx
  have h2 : x.down = 0 := by
    have := congrArg A.symm h1
    simpa using this
  change x = ULift.up 0
  exact ULift.ext h2

theorem hrelMap_euMap_of_det_pos {μ : ℕ} (hμ : 1 ≤ μ)
    (A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ))
    (hA : 0 < LinearMap.det (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)))
    (y : relativeHomology integerCoefficients (TopCat.of (EU.{u} μ)) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) μ) :
    relativeHomologyMap integerCoefficients (euMap.{u} A) (euMap_mapsTo A) μ y = y := by
  classical
  have hJ : ∀ M : Matrix (Fin μ) (Fin μ) ℝ, 0 < M.det →
      JoinedIn {N : Matrix (Fin μ) (Fin μ) ℝ | N.det ≠ 0} 1 M := by
    intro M hM
    set S : Set (Matrix (Fin μ) (Fin μ) ℝ) := {N | N.det ≠ 0} with hS
    have hjoin : ∀ f : ℝ → Matrix (Fin μ) (Fin μ) ℝ, Continuous f →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ S) → JoinedIn S (f 0) (f 1) := by
      intro f hf hfS
      exact ⟨⟨⟨fun t => f t, hf.comp continuous_subtype_val⟩, rfl, rfl⟩, fun t => hfS t t.2⟩
    have hmul : ∀ {A B : Matrix (Fin μ) (Fin μ) ℝ}, JoinedIn S 1 A → JoinedIn S 1 B →
        JoinedIn S 1 (A * B) := by
      intro A B hA hB
      open scoped Pointwise in
      have hSS : S * S ⊆ S := by
        rw [Set.mul_subset_iff]
        intro x hx y hy
        simp only [hS, Set.mem_ofPred_eq, Matrix.det_mul] at hx hy ⊢
        exact mul_ne_zero hx hy
      have := (hA.mul hB).mono hSS
      rwa [mul_one] at this
    have hdiagpos : ∀ (i : Fin μ) (a : ℝ), 0 < a →
        JoinedIn S 1 (Matrix.diagonal (Pi.mulSingle i a)) := by
      intro i a ha
      have h := hjoin (fun s => Matrix.diagonal (Pi.mulSingle i (Real.exp (s * Real.log a))))
        (Continuous.matrix_diagonal ((continuous_mulSingle i).comp (by fun_prop))) (fun s _ => by
          simp only [hS, Set.mem_ofPred_eq, Matrix.det_diagonal]
          rw [Finset.prod_ne_zero_iff]
          intro k _
          by_cases hk : k = i
          · subst hk; simp [Real.exp_ne_zero]
          · simp [hk])
      simpa [Real.exp_log ha] using h
    have htr : ∀ (i j : Fin μ), i ≠ j → ∀ a : ℝ, JoinedIn S 1 (1 + Matrix.single i j a) := by
      intro i j hij a
      have h := hjoin (fun s => 1 + (s * a) • Matrix.single i j (1 : ℝ))
        (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const))
        (fun s _ => by
          simp only [hS, Set.mem_ofPred_eq, Matrix.smul_single, smul_eq_mul, mul_one]
          rw [← Matrix.transvection, Matrix.det_transvection_of_ne i j hij]; exact one_ne_zero)
      simpa [Matrix.smul_single] using h
    have hd2pos : ∀ (i j : Fin μ), i ≠ j → ∀ c : ℝ, 0 < c →
        JoinedIn S 1 (Matrix.diagonal (fun k => if k = i then c else if k = j then c⁻¹ else 1)) := by
      intro i j hij c hc
      have h := hjoin (fun s => Matrix.diagonal (fun k => if k = i then Real.exp (s * Real.log c)
          else if k = j then Real.exp (-(s * Real.log c)) else 1))
        (Continuous.matrix_diagonal (continuous_pi fun k => by
          split_ifs
          · fun_prop
          · fun_prop
          · fun_prop)) (fun s _ => by
          simp only [hS, Set.mem_ofPred_eq, Matrix.det_diagonal]
          rw [Finset.prod_ne_zero_iff]
          intro k _
          split_ifs <;> simp [Real.exp_ne_zero])
      simpa [Real.exp_neg, Real.exp_log hc] using h
    have hrot : ∀ (i j : Fin μ), i ≠ j →
        JoinedIn S 1 (Matrix.diagonal (fun k => if k = i then (-1 : ℝ) else if k = j then -1 else 1)) := by
      intro i j hij
      let R : ℝ → Matrix (Fin μ) (Fin μ) ℝ := fun θ =>
        1 + (Real.cos θ - 1) • (Matrix.single i i 1 + Matrix.single j j 1) +
          Real.sin θ • (Matrix.single j i 1 - Matrix.single i j 1)
      have hR : Continuous R := by
        refine (continuous_const.add ((Real.continuous_cos.sub continuous_const).smul
          continuous_const)).add (Real.continuous_sin.smul continuous_const)
      have hRS : ∀ θ, R θ ∈ S := by
        intro θ
        simp only [hS, Set.mem_ofPred_eq]
        intro hdet
        obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
        have e1 := congrFun hv i
        have e2 := congrFun hv j
        have e3 : ∀ k, k ≠ i → k ≠ j → v k = 0 := by
          intro k hki hkj
          have := congrFun hv k
          simpa [R, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec, Function.update_apply,
            hki, hkj] using this
        replace e1 : v i + (Real.cos θ - 1) * v i + Real.sin θ * -v j = 0 := by
          simpa [R, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec,
            hij, hij.symm] using e1
        replace e2 : v j + (Real.cos θ - 1) * v j + Real.sin θ * v i = 0 := by
          simpa [R, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.single_mulVec,
            hij, hij.symm] using e2
        have hsc := Real.sin_sq_add_cos_sq θ
        have hvi : v i = 0 := by
          linear_combination (Real.cos θ) * e1 + (Real.sin θ) * e2 - v i * hsc
        have hvj : v j = 0 := by
          linear_combination (Real.cos θ) * e2 - (Real.sin θ) * e1 - v j * hsc
        apply hv0
        funext k
        by_cases hki : k = i
        · subst hki; simpa using hvi
        by_cases hkj : k = j
        · subst hkj; simpa using hvj
        simpa using e3 k hki hkj
      have h := hjoin (fun s => R (Real.pi * s)) (hR.comp (continuous_const.mul continuous_id))
        (fun s _ => hRS _)
      have h0 : R (Real.pi * 0) = 1 := by simp [R]
      have h1 : R (Real.pi * 1) =
          Matrix.diagonal (fun k => if k = i then (-1 : ℝ) else if k = j then -1 else 1) := by
        ext k l
        simp only [R, mul_one, Real.cos_pi, Real.sin_pi, Matrix.add_apply,
          Matrix.smul_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply,
          smul_eq_mul]
        by_cases hkl : k = l
        · subst hkl
          by_cases hki : k = i
          · subst hki; simp [Ne.symm hij]
          · by_cases hkj : k = j
            · subst hkj; simp [hki, Ne.symm hki]
            · simp [hki, hkj, Ne.symm hki, Ne.symm hkj]
        · have : ¬ (i = k ∧ i = l) := fun h => hkl (h.1.symm.trans h.2)
          have : ¬ (j = k ∧ j = l) := fun h => hkl (h.1.symm.trans h.2)
          simp [*]
      rw [h0, h1] at h
      exact h
    have hSL : ∀ N : Matrix.SpecialLinearGroup (Fin μ) ℝ, JoinedIn S 1 (N : Matrix (Fin μ) (Fin μ) ℝ) := by
      intro N
      rcases subsingleton_or_nontrivial (Fin μ) with hsub | hnt
      · have hN1 : (N : Matrix (Fin μ) (Fin μ) ℝ) = 1 := by
          ext k l
          have hkl : k = l := Subsingleton.elim k l
          subst hkl
          have := Matrix.det_eq_elem_of_subsingleton (N : Matrix (Fin μ) (Fin μ) ℝ) k
          rw [N.2] at this
          simp [← this]
        rw [hN1]
        exact JoinedIn.refl (by simp [hS])
      · refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
          (fun N => JoinedIn S 1 (N : Matrix (Fin μ) (Fin μ) ℝ)) N ?_ ?_ ?_
        · intro i j hij c hc
          simp only [Matrix.SpecialLinearGroup.diag2n_coe]
          rcases lt_or_gt_of_ne hc with hneg | hpos
          · have hsplit : Matrix.diagonal (fun k => if k = i then c else if k = j then c⁻¹ else 1) =
                Matrix.diagonal (fun k => if k = i then (-1 : ℝ) else if k = j then -1 else 1) *
                  Matrix.diagonal (fun k => if k = i then -c else if k = j then (-c)⁻¹ else 1) := by
              rw [Matrix.diagonal_mul_diagonal]
              congr 1
              funext k
              split_ifs <;> simp [inv_neg]
            rw [hsplit]
            exact hmul (hrot i j hij) (hd2pos i j hij (-c) (neg_pos.mpr hneg))
          · exact hd2pos i j hij c hpos
        · intro i j hij a
          rw [Matrix.SpecialLinearGroup.transvection_coe]
          exact htr i j hij a
        · intro A B hA hB
          rw [Matrix.SpecialLinearGroup.coe_mul]
          exact hmul hA hB
    set i₀ : Fin μ := ⟨0, hμ⟩
    set a := M.det
    have hdet_d : ∀ x : ℝ, (Matrix.diagonal (Pi.mulSingle i₀ x)).det = x := by
      intro x
      rw [Matrix.det_diagonal]
      rw [Finset.prod_eq_single i₀ (fun k _ hk => by simp [hk]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
    have hM' : (M * Matrix.diagonal (Pi.mulSingle i₀ a⁻¹)).det = 1 := by
      rw [Matrix.det_mul, hdet_d, mul_inv_cancel₀ hM.ne']
    have hfac : M = (M * Matrix.diagonal (Pi.mulSingle i₀ a⁻¹)) * Matrix.diagonal (Pi.mulSingle i₀ a) := by
      rw [mul_assoc, Matrix.diagonal_mul_diagonal]
      change M = M * Matrix.diagonal (Pi.mulSingle i₀ a⁻¹ * Pi.mulSingle i₀ a)
      rw [← Pi.mulSingle_mul, inv_mul_cancel₀ hM.ne',
        Pi.mulSingle_one]
      simp
    rw [hfac]
    exact hmul (hSL ⟨_, hM'⟩) (hdiagpos i₀ a hM)
  let b := (EuclideanSpace.basisFun (Fin μ) ℝ).toBasis
  let M : Matrix (Fin μ) (Fin μ) ℝ := LinearMap.toMatrix b b
    (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ))
  have hMdet : 0 < M.det := by rw [LinearMap.det_toMatrix]; exact hA
  have hJM := hJ M hMdet
  let γ : Path M 1 := hJM.somePath.symm
  have hγS : ∀ t, (γ t).det ≠ 0 := fun t => hJM.somePath_mem _
  let Φ : Matrix (Fin μ) (Fin μ) ℝ →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ)) :=
    (LinearMap.toContinuousLinearMap : (EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ))
      ≃ₗ[ℝ] _).toLinearMap ∘ₗ (Matrix.toLin b b).toLinearMap
  have hΦ : Continuous Φ := LinearMap.continuous_of_finiteDimensional Φ
  have hΦapp : ∀ N x, Φ N x = Matrix.toLin b b N x := fun N x => rfl
  let F : ContinuousMap.Homotopy (euMap.{u} A).hom
      (TopCat.Hom.hom (𝟙 (TopCat.of (EU.{u} μ)))) :=
    { toFun := fun p => ULift.up (Φ (γ p.1) p.2.down)
      continuous_toFun := continuous_uliftUp.comp
        ((hΦ.comp (γ.continuous.comp continuous_fst)).clm_apply
          (continuous_uliftDown.comp continuous_snd))
      map_zero_left := fun x => by
        simp only [hΦapp, Path.source, M, Matrix.toLin_toMatrix]
        rfl
      map_one_left := fun x => by
        simp only [hΦapp, Path.target, Matrix.toLin_one]
        rfl }
  have hF : ∀ t, ∀ x ∈ ({ULift.up 0}ᶜ : Set (EU.{u} μ)),
      F (t, x) ∈ ({ULift.up 0}ᶜ : Set (EU.{u} μ)) := by
    intro t x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro h0
    apply hx
    have hinj : Function.Injective (Matrix.toLin b b (γ t)) := by
      have hu : IsUnit (Matrix.toLin b b (γ t)) := by
        rw [LinearMap.isUnit_iff_isUnit_det, LinearMap.det_toLin]
        exact (hγS t).isUnit
      exact ((Module.End.isUnit_iff _).mp hu).1
    have h1 : Matrix.toLin b b (γ t) x.down = Matrix.toLin b b (γ t) 0 := by
      rw [map_zero]
      exact congrArg ULift.down h0
    exact congrArg ULift.up (hinj h1)
  have hid : Set.MapsTo (𝟙 (TopCat.of (EU.{u} μ))) ({ULift.up 0}ᶜ : Set (EU.{u} μ))
      ({ULift.up 0}ᶜ : Set (EU.{u} μ)) := fun x hx => hx
  rw [relativeHomologyMap_eq_of_homotopy (euMap.{u} A) (𝟙 _) (euMap_mapsTo A) hid F hF μ,
    relativeHomologyMap_id]
  rfl

theorem exists_reflection_neg {μ : ℕ} (hμ : 1 ≤ μ) :
    ∃ A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ),
      LinearMap.det (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) < 0 ∧
      ∀ y : relativeHomology integerCoefficients (TopCat.of (EU.{u} μ)) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) μ,
        relativeHomologyMap integerCoefficients (euMap.{u} A) (euMap_mapsTo A) μ y = -y := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  let e0 : ∀ k : ℕ, EuclideanSpace ℝ (Fin (k + 1)) := fun k => EuclideanSpace.single 0 1
  let Rf : ∀ k : ℕ, EuclideanSpace ℝ (Fin (k + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
    fun k => ((ℝ ∙ e0 k)ᗮ).reflection.toLinearEquiv.toContinuousLinearEquiv
  have hRf : ∀ k (x : EuclideanSpace ℝ (Fin (k + 1))) (i : Fin (k + 1)),
      Rf k x i = if i = 0 then -x i else x i := by
    intro k x i
    have h1 : Rf k x = ((ℝ ∙ e0 k)ᗮ).reflection x := rfl
    rw [h1, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
    have hn : ‖e0 k‖ = 1 := by simp [e0]
    have hi : inner ℝ (e0 k) x = x 0 := by simp [e0, EuclideanSpace.inner_single_left]
    rw [hn, hi]
    by_cases h : i = 0
    · subst h; simp [e0]; ring
    · simp [e0, h]
  have hdet : ∀ k, LinearMap.det (Rf k : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (k + 1))) < 0 := by
    intro k
    have h1 : (Rf k : EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1))) =
        ((((ℝ ∙ e0 k)ᗮ).reflection.toLinearEquiv : EuclideanSpace ℝ (Fin (k + 1)) ≃ₗ[ℝ] _) :
          EuclideanSpace ℝ (Fin (k + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (k + 1))) := rfl
    rw [h1, Submodule.det_reflection, Submodule.orthogonal_orthogonal,
      finrank_span_singleton (by simp [e0])]
    norm_num
  have main : ∀ k (y : relativeHomology integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1)))
      ({ULift.up 0}ᶜ : Set (EU.{u} (k + 1))) (k + 1)),
      relativeHomologyMap integerCoefficients.{u} (euMap.{u} (Rf k)) (euMap_mapsTo (Rf k)) (k + 1) y = -y := by
    intro k
    induction k with
    | zero =>
      intro y
      have hneg : ∀ x, Rf 0 x = -x := by
        intro x
        ext i
        have hi : i = 0 := Fin.ext (by have := i.2; simp)
        rw [hRf]
        simp [hi]
      have he0 : ∀ i : Fin 1, e0 0 i = 1 := by
        intro i
        have hi : i = 0 := Fin.ext (by have := i.2; simp)
        subst hi
        simp [e0]
      have hnorm : ∀ v : EuclideanSpace ℝ (Fin 1), ‖v‖ = |v 0| := by
        intro v
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
          Real.sqrt_sq_eq_abs]
      have hv0 : ∀ v : EuclideanSpace ℝ (Fin 1), v ≠ 0 → v 0 ≠ 0 := by
        intro v hv h0
        apply hv
        ext i
        have hi : i = 0 := Fin.ext (by have := i.2; simp)
        rw [hi, h0]
        rfl
      let P : Set (EU.{u} (0 + 1)) := {ULift.up 0}ᶜ
      have hP : ∀ p : P, p.1.down ≠ 0 := by
        intro p hp
        apply p.2
        change p.1 = ULift.up 0
        rw [← hp]
      have hr : Set.MapsTo (euMap.{u} (Rf 0)) P P := euMap_mapsTo (Rf 0)
      let r' : TopCat.of P ⟶ TopCat.of P := restr (euMap.{u} (Rf 0)) hr
      have hδinj : Function.Injective (δ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0) := by
        rw [← ModuleCat.mono_iff_injective]
        exact (les_exact₃ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0).mono_g
          ((isZero_singularHomology_EU integerCoefficients.{u} (0 + 1) (0 + 1) (by omega)).eq_of_src _ _)
      apply hδinj
      have h1 : δ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0
          (relativeHomologyMap integerCoefficients.{u} (euMap.{u} (Rf 0)) hr (0 + 1) y) =
          singularHomologyMap integerCoefficients.{u} r' 0 (δ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0 y) := by
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, δ_natural]
      rw [h1, map_neg]
      set c := δ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0 y with hc_def
      have hc : ε integerCoefficients.{u} (TopCat.of P) c = 0 := by
        have h0 : δ integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0 ≫
            inclMap integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P 0 = 0 :=
          (pair (TopCat.of (EU.{u} (0 + 1))) P).homologyδ_comp integerCoefficients.{u} (0 + 1) 0 rfl
        rw [← inclMap_ε integerCoefficients.{u} (TopCat.of (EU.{u} (0 + 1))) P, hc_def, ← ModuleCat.comp_apply,
          ← Category.assoc, h0, Limits.zero_comp]
        rfl
      have : ContractibleSpace (Set.Ioi (0:ℝ)) :=
        (convex_Ioi 0).contractibleSpace Set.nonempty_Ioi
      have : ContractibleSpace (ULift.{u} (Set.Ioi (0:ℝ))) := Homeomorph.ulift.contractibleSpace
      have hεY : Function.Injective (ε integerCoefficients.{u} (TopCat.of (ULift.{u} (Set.Ioi (0:ℝ))))) := by
        rw [← ModuleCat.mono_iff_injective]
        have := isIso_ε_of_contractible integerCoefficients.{u} (ULift.{u} (Set.Ioi (0:ℝ)))
        infer_instance
      have hne : ∀ x : P, 0 < ‖x.1.down‖ := fun x => norm_pos_iff.2 (hP x)
      have he0ne : ∀ t : ℝ, t ≠ 0 → t • e0 0 ≠ 0 := by
        intro t ht h
        have := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
        exact ht (by simpa [he0] using this)
      let a : TopCat.of P ⟶ TopCat.of (ULift.{u} (Set.Ioi (0:ℝ))) :=
        TopCat.ofHom ⟨fun x => ULift.up ⟨‖x.1.down‖, hne x⟩, by fun_prop⟩
      let bp : TopCat.of (ULift.{u} (Set.Ioi (0:ℝ))) ⟶ TopCat.of P :=
        TopCat.ofHom ⟨fun t => ⟨ULift.up (t.down.1 • e0 0), fun h =>
          he0ne t.down.1 (ne_of_gt t.down.2) (congrArg ULift.down h)⟩, by fun_prop⟩
      let bm : TopCat.of (ULift.{u} (Set.Ioi (0:ℝ))) ⟶ TopCat.of P :=
        TopCat.ofHom ⟨fun t => ⟨ULift.up ((-t.down.1) • e0 0), fun h =>
          he0ne (-t.down.1) (neg_ne_zero.2 (ne_of_gt t.down.2)) (congrArg ULift.down h)⟩, by fun_prop⟩
      have ha : singularHomologyMap integerCoefficients.{u} a 0 c = 0 := by
        apply hεY
        rw [← ModuleCat.comp_apply, ε_natural, hc, map_zero]
      have hPext : ∀ p q : P, p.1.down 0 = q.1.down 0 → p = q := by
        intro p q h
        apply Subtype.ext
        apply ULift.ext
        ext i
        have hi : i = 0 := Fin.ext (by have := i.2; simp)
        rw [hi]
        exact h
      have hx : ∀ x : (TopCat.toSSet.obj (TopCat.of P)).obj (Opposite.op (SimplexCategory.mk 0)),
          ((TopCat.toSSet.map (𝟙 (TopCat.of P))).app _ x =
              (TopCat.toSSet.map (a ≫ bp)).app _ x ∧
            (TopCat.toSSet.map r').app _ x = (TopCat.toSSet.map (a ≫ bm)).app _ x) ∨
          ((TopCat.toSSet.map (𝟙 (TopCat.of P))).app _ x =
              (TopCat.toSSet.map (a ≫ bm)).app _ x ∧
            (TopCat.toSSet.map r').app _ x = (TopCat.toSSet.map (a ≫ bp)).app _ x) := by
        intro x
        obtain ⟨σ, rfl⟩ := ((TopCat.of P).toSSetObjEquiv _).symm.surjective x
        have hσ : ∀ t, σ t = σ default := fun t => by rw [Subsingleton.elim t default]
        have hp0 := hv0 _ (hP (σ default))
        have key1 : ∀ f g : TopCat.of P ⟶ TopCat.of P, (∀ p : P, p = σ default → f p = g p) →
            (TopCat.toSSet.map f).app _ (((TopCat.of P).toSSetObjEquiv _).symm σ) =
              (TopCat.toSSet.map g).app _ (((TopCat.of P).toSSetObjEquiv _).symm σ) := by
          intro f g hfg
          change sing (f.hom.comp σ) = sing (g.hom.comp σ)
          congr 1
          ext1 t
          exact hfg (σ t) (hσ t)
        rcases lt_or_gt_of_ne hp0 with hlt | hgt
        · right
          constructor
          · refine key1 _ _ (fun p hp => hPext _ _ ?_)
            subst hp
            change (σ default).1.down 0 = (-‖(σ default).1.down‖ • e0 0) 0
            rw [hnorm, abs_of_neg hlt]
            simp [he0]
          · refine key1 _ _ (fun p hp => hPext _ _ ?_)
            subst hp
            change (Rf 0 (σ default).1.down) 0 = (‖(σ default).1.down‖ • e0 0) 0
            rw [hnorm, abs_of_neg hlt, hneg]
            simp [he0]
        · left
          constructor
          · refine key1 _ _ (fun p hp => hPext _ _ ?_)
            subst hp
            change (σ default).1.down 0 = (‖(σ default).1.down‖ • e0 0) 0
            rw [hnorm, abs_of_pos hgt]
            simp [he0]
          · refine key1 _ _ (fun p hp => hPext _ _ ?_)
            subst hp
            change (Rf 0 (σ default).1.down) 0 = (-‖(σ default).1.down‖ • e0 0) 0
            rw [hnorm, abs_of_pos hgt, hneg]
            simp [he0]
      have key : singularHomologyMap integerCoefficients.{u} (𝟙 (TopCat.of P)) 0 + singularHomologyMap integerCoefficients.{u} r' 0 =
          singularHomologyMap integerCoefficients.{u} (a ≫ bp) 0 + singularHomologyMap integerCoefficients.{u} (a ≫ bm) 0 := by
        change (SSet.homologyMap (TopCat.toSSet.map (𝟙 (TopCat.of P))) integerCoefficients.{u} 0 +
            SSet.homologyMap (TopCat.toSSet.map r') integerCoefficients.{u} 0 :
            (TopCat.toSSet.obj (TopCat.of P)).homology integerCoefficients.{u} 0 ⟶
              (TopCat.toSSet.obj (TopCat.of P)).homology integerCoefficients.{u} 0) =
          SSet.homologyMap (TopCat.toSSet.map (a ≫ bp)) integerCoefficients.{u} 0 +
            SSet.homologyMap (TopCat.toSSet.map (a ≫ bm)) integerCoefficients.{u} 0
        rw [← cancel_epi (((TopCat.toSSet.obj (TopCat.of P)).chainComplex integerCoefficients.{u}).homologyπ 0),
          ← cancel_epi (inv (((TopCat.toSSet.obj (TopCat.of P)).chainComplex integerCoefficients.{u}).iCycles 0))]
        apply SSet.chainComplex_hom_ext
        intro x
        simp only [Preadditive.comp_add, SSet.homologyMap, HomologicalComplex.homologyπ_naturality,
          ι_inv_iCycles_assoc, HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
          SSet.ι_chainComplexMap_f]
        rcases hx x with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [h1, h2]
        · simp only [h1, h2]
          exact add_comm _ _
      have hkey := congrArg (fun φ => φ c) key
      simp only [ModuleCat.hom_add, LinearMap.add_apply, singularHomologyMap_id, singularHomologyMap_comp,
        ModuleCat.comp_apply, ha, map_zero, add_zero] at hkey
      rw [ModuleCat.id_apply] at hkey
      exact eq_neg_of_add_eq_zero_right hkey
    | succ k ih =>
      intro y
      let P : Set (EU.{u} (k + 1 + 1)) := {ULift.up 0}ᶜ
      let lst : Fin (k + 1 + 1) := Fin.last (k + 1)
      let el : EuclideanSpace ℝ (Fin (k + 1 + 1)) := EuclideanSpace.single lst 1
      let J : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1 + 1)) :=
        fun v => SingularPair.Sphere.incl k v + el
      have hJc : ∀ v i, J v (Fin.castSucc i) = v i := by
        intro v i
        simp [J, el, lst, Fin.castSucc_ne_last]
      have hJl : ∀ v, J v lst = 1 := by
        intro v
        simp [J, el, lst]
      have hJcont : Continuous J := by
        have := SingularPair.Sphere.continuous_incl k
        fun_prop
      have hveq : ∀ v : EuclideanSpace ℝ (Fin (k + 1 + 1)),
          (∀ i : Fin (k + 1), v (Fin.castSucc i) = 0) → v lst = 0 → v = 0 := by
        intro v h1 h2
        ext i
        induction i using Fin.lastCases with
        | last => exact h2
        | cast i => exact h1 i
      let B' : Set (EuclideanSpace ℝ (Fin (k + 1 + 1))) :=
        {v | (∃ i : Fin (k + 1), v (Fin.castSucc i) ≠ 0) ∨ v lst < 0}
      let B : Set (EU.{u} (k + 1 + 1)) := ULift.down ⁻¹' B'
      have hBP : B ⊆ P := by
        intro x hx h0
        have h0' : x.down = 0 := congrArg ULift.down h0
        rcases hx with ⟨i, hi⟩ | hl
        · exact hi (by rw [h0']; rfl)
        · rw [h0'] at hl
          exact lt_irrefl _ hl
      let A' : Set (TopCat.of P) := Subtype.val ⁻¹' B
      have hstar : StarConvex ℝ (-el) B' := by
        intro v hv a b ha hb hab
        rcases hv with ⟨i, hi⟩ | hl
        · by_cases hb0 : b = 0
          · right
            have ha1 : a = 1 := by linarith
            simp [el, lst, ha1, hb0]
          · left
            refine ⟨i, ?_⟩
            simpa [el, lst, Fin.castSucc_ne_last] using mul_ne_zero hb0 hi
        · right
          show (a • -el + b • v) lst < 0
          have hel : el lst = 1 := by simp [el]
          simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, hel]
          by_cases ha0 : a = 0
          · have hb1 : b = 1 := by linarith
            subst ha0 hb1
            simpa using hl
          · have : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
            nlinarith
      have hB'ne : B'.Nonempty := ⟨-el, Or.inr (by simp [el, lst])⟩
      have : ContractibleSpace B' := hstar.contractibleSpace hB'ne
      have : ContractibleSpace A' :=
        ((homeomorphPreimageVal hBP).trans (SingularPair.Sphere.uliftSetHomeomorph B')).contractibleSpace
      have hA'0 : CategoryTheory.Limits.IsZero (singularHomology integerCoefficients.{u} (TopCat.of A') (k + 1)) :=
        isZero_of_contractible integerCoefficients.{u} A' (k + 1) (by omega)
      have hπinj : Function.Injective (relπ integerCoefficients.{u} (TopCat.of P) A' (k + 1)) := by
        rw [← ModuleCat.mono_iff_injective]
        exact (les_exact₂ integerCoefficients.{u} (TopCat.of P) A' (k + 1)).mono_g (hA'0.eq_of_src _ _)
      have hδinj : Function.Injective (δ integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1 + 1))) P (k + 1)) := by
        rw [← ModuleCat.mono_iff_injective]
        exact (les_exact₃ integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1 + 1))) P (k + 1)).mono_g
          ((isZero_singularHomology_EU integerCoefficients.{u} (k + 1 + 1) (k + 1 + 1) (by omega)).eq_of_src _ _)
      have hlst0 : lst ≠ 0 := by
        intro h
        have := congrArg Fin.val h
        simp [lst] at this
      have hRc : ∀ (v : EuclideanSpace ℝ (Fin (k + 1 + 1))) (i : Fin (k + 1)),
          Rf (k + 1) v (Fin.castSucc i) = if i = 0 then -v (Fin.castSucc i) else v (Fin.castSucc i) := by
        intro v i
        rw [hRf]
        simp only [Fin.castSucc_eq_zero_iff]
      have hRl : ∀ v : EuclideanSpace ℝ (Fin (k + 1 + 1)), Rf (k + 1) v lst = v lst := by
        intro v
        rw [hRf]
        simp [hlst0]
      have hrP : Set.MapsTo (euMap.{u} (Rf (k + 1))) P P := euMap_mapsTo (Rf (k + 1))
      let r' : TopCat.of P ⟶ TopCat.of P := restr (euMap.{u} (Rf (k + 1))) hrP
      have hr'A : Set.MapsTo r' A' A' := by
        intro p hp
        change Rf (k + 1) p.1.down ∈ B'
        rcases hp with ⟨i, hi⟩ | hl
        · left
          refine ⟨i, ?_⟩
          rw [hRc]
          split_ifs
          · exact neg_ne_zero.2 hi
          · exact hi
        · right
          rw [hRl]
          exact hl
      have hnat1 : δ integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1 + 1))) P (k + 1)
          (relativeHomologyMap integerCoefficients.{u} (euMap.{u} (Rf (k + 1))) hrP (k + 1 + 1) y) =
          singularHomologyMap integerCoefficients.{u} r' (k + 1) (δ integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1 + 1))) P (k + 1) y) := by
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, δ_natural]
      have hnat2 : ∀ z, relπ integerCoefficients.{u} (TopCat.of P) A' (k + 1) (singularHomologyMap integerCoefficients.{u} r' (k + 1) z) =
          relativeHomologyMap integerCoefficients.{u} r' hr'A (k + 1) (relπ integerCoefficients.{u} (TopCat.of P) A' (k + 1) z) := by
        intro z
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, relπ_natural]
      apply hδinj
      apply hπinj
      rw [hnat1, hnat2, map_neg, map_neg]
      let Zc : Set (TopCat.of P) := {p | p.1.down lst ≤ 0}
      have hZc : closure Zc ⊆ interior A' := by
        have hcl : IsClosed Zc :=
          isClosed_le ((continuous_apply lst).comp ((PiLp.continuous_ofLp 2 _).comp
            (continuous_uliftDown.comp continuous_subtype_val))) continuous_const
        have hop : IsOpen A' := by
          have hcv : ∀ j : Fin (k + 1 + 1), Continuous fun v : EuclideanSpace ℝ (Fin (k + 1 + 1)) => v j :=
            fun j => (continuous_apply j).comp (PiLp.continuous_ofLp 2 _)
          have hB'o : IsOpen B' := by
            have : B' = (⋃ i : Fin (k + 1), {v | v (Fin.castSucc i) ≠ 0}) ∪ {v | v lst < 0} := by
              ext v
              simp [B']
            rw [this]
            exact (isOpen_iUnion fun i => isOpen_ne_fun (hcv (Fin.castSucc i)) continuous_const).union
              (isOpen_lt (hcv lst) continuous_const)
          exact (hB'o.preimage continuous_uliftDown).preimage continuous_subtype_val
        rw [hcl.closure_eq, hop.interior_eq]
        intro p hp
        by_cases hl : p.1.down lst < 0
        · exact Or.inr hl
        · left
          by_contra hne
          push Not at hne
          apply p.2
          change p.1 = ULift.up 0
          apply ULift.ext
          exact hveq _ hne (le_antisymm hp (not_lt.1 hl))
      have hJP : ∀ v, (ULift.up (J v) : EU.{u} (k + 1 + 1)) ∈ P := by
        intro v h
        have := congrArg (fun x : EU.{u} (k + 1 + 1) => x.down lst) h
        simp only [hJl] at this
        exact one_ne_zero this
      have hJT : ∀ v, (⟨ULift.up (J v), hJP v⟩ : P) ∈ Zcᶜ := by
        intro v h
        change J v lst ≤ 0 at h
        rw [hJl] at h
        linarith
      have hTl : ∀ p : (Zcᶜ : Set (TopCat.of P)), 0 < p.1.1.down lst := fun p => not_le.1 p.2
      let f : TopCat.of (EU.{u} (k + 1)) ⟶ TopCat.of (Zcᶜ : Set (TopCat.of P)) :=
        TopCat.ofHom ⟨fun v => ⟨⟨ULift.up (J v.down), hJP v.down⟩, hJT v.down⟩,
          ((continuous_uliftUp.comp (hJcont.comp continuous_uliftDown)).subtype_mk _).subtype_mk _⟩
      let g : TopCat.of (Zcᶜ : Set (TopCat.of P)) ⟶ TopCat.of (EU.{u} (k + 1)) :=
        TopCat.ofHom ⟨fun p => ULift.up (SingularPair.Sphere.proj k p.1.1.down),
          continuous_uliftUp.comp ((SingularPair.Sphere.continuous_proj k).comp
            (continuous_uliftDown.comp (continuous_subtype_val.comp continuous_subtype_val)))⟩
      have hf : Set.MapsTo f ({ULift.up 0}ᶜ : Set (EU.{u} (k + 1))) (Subtype.val ⁻¹' A') := by
        intro v hv
        change J v.down ∈ B'
        left
        by_contra h
        push Not at h
        apply hv
        change v = ULift.up 0
        apply ULift.ext
        ext i
        have := h i
        rw [hJc] at this
        exact this
      have hg : Set.MapsTo g (Subtype.val ⁻¹' A') ({ULift.up 0}ᶜ : Set (EU.{u} (k + 1))) := by
        intro p hp h0
        have hp' : p.1.1.down ∈ B' := hp
        rcases hp' with ⟨i, hi⟩ | hl
        · apply hi
          have := congrArg (fun x : EU.{u} (k + 1) => x.down i) h0
          change SingularPair.Sphere.proj k p.1.1.down i = 0 at this
          rw [SingularPair.Sphere.proj_apply] at this
          exact this
        · exact absurd hl (not_lt.2 (le_of_lt (hTl p)))
      have hfg : (f ≫ g).hom = ContinuousMap.id _ := by
        ext1 v
        change ULift.up (SingularPair.Sphere.proj k (J v.down)) = v
        apply ULift.ext
        ext i
        rw [SingularPair.Sphere.proj_apply, hJc]
      let F : ContinuousMap.Homotopy (f ≫ g).hom (ContinuousMap.id _) :=
        (ContinuousMap.Homotopy.refl (ContinuousMap.id _)).cast hfg.symm rfl
      have hF : ∀ t, ∀ x ∈ ({ULift.up 0}ᶜ : Set (EU.{u} (k + 1))), F (t, x) ∈
          ({ULift.up 0}ᶜ : Set (EU.{u} (k + 1))) := fun _ _ hx => hx
      let W : unitInterval × (Zcᶜ : Set (TopCat.of P)) → EuclideanSpace ℝ (Fin (k + 1 + 1)) :=
        fun q => SingularPair.Sphere.incl k (SingularPair.Sphere.proj k q.2.1.1.down) +
          ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * q.2.1.1.down lst) • el
      have hWl : ∀ q, W q lst = (1 - (q.1 : ℝ)) + (q.1 : ℝ) * q.2.1.1.down lst := by
        intro q
        simp [W, el, lst]
      have hWc : ∀ q i, W q (Fin.castSucc i) = q.2.1.1.down (Fin.castSucc i) := by
        intro q i
        simp [W, el, lst, Fin.castSucc_ne_last]
      have hWpos : ∀ q, 0 < W q lst := by
        intro q
        rw [hWl]
        have h0 := q.1.2.1
        have h1 := q.1.2.2
        have h2 := hTl q.2
        by_cases ht : (q.1 : ℝ) = 1
        · rw [ht]
          linarith
        · have : (0 : ℝ) < 1 - q.1 := by
            have := lt_of_le_of_ne h1 ht
            linarith
          nlinarith
      have hWcont : Continuous W := by
        have h1 := SingularPair.Sphere.continuous_incl k
        have h2 := SingularPair.Sphere.continuous_proj k
        have h3 : Continuous fun q : unitInterval × (Zcᶜ : Set (TopCat.of P)) => q.2.1.1.down :=
          continuous_uliftDown.comp (continuous_subtype_val.comp (continuous_subtype_val.comp
            continuous_snd))
        have h4 : Continuous fun q : unitInterval × (Zcᶜ : Set (TopCat.of P)) => (q.1 : ℝ) :=
          continuous_subtype_val.comp continuous_fst
        have h5 : Continuous fun q : unitInterval × (Zcᶜ : Set (TopCat.of P)) => q.2.1.1.down lst :=
          (continuous_apply lst).comp ((PiLp.continuous_ofLp 2 _).comp h3)
        exact ((h1.comp (h2.comp h3)).add
          (((continuous_const.sub h4).add (h4.mul h5)).smul continuous_const))
      have hWP : ∀ q, (ULift.up (W q) : EU.{u} (k + 1 + 1)) ∈ P := by
        intro q h
        have := congrArg (fun x : EU.{u} (k + 1 + 1) => x.down lst) h
        change W q lst = 0 at this
        exact (hWpos q).ne' this
      have hWT : ∀ q, (⟨ULift.up (W q), hWP q⟩ : P) ∈ Zcᶜ := by
        intro q h
        change W q lst ≤ 0 at h
        exact absurd h (not_le.2 (hWpos q))
      let G : ContinuousMap.Homotopy (g ≫ f).hom (ContinuousMap.id _) :=
        { toFun := fun q => ⟨⟨ULift.up (W q), hWP q⟩, hWT q⟩
          continuous_toFun :=
            ((continuous_uliftUp.comp hWcont).subtype_mk _).subtype_mk _
          map_zero_left := fun p => by
            apply Subtype.ext
            apply Subtype.ext
            apply ULift.ext
            change W (0, p) = J (SingularPair.Sphere.proj k p.1.1.down)
            simp [W, J]
          map_one_left := fun p => by
            apply Subtype.ext
            apply Subtype.ext
            apply ULift.ext
            change W (1, p) = p.1.1.down
            ext i
            induction i using Fin.lastCases with
            | last => rw [show Fin.last (k + 1) = lst from rfl, hWl]; simp
            | cast i => exact hWc _ i }
      have hG : ∀ t, ∀ p ∈ (Subtype.val ⁻¹' A' : Set (Zcᶜ : Set (TopCat.of P))),
          G (t, p) ∈ (Subtype.val ⁻¹' A' : Set (Zcᶜ : Set (TopCat.of P))) := by
        intro t p hp
        have hp' : p.1.1.down ∈ B' := hp
        change W (t, p) ∈ B'
        rcases hp' with ⟨i, hi⟩ | hl
        · exact Or.inl ⟨i, by rw [hWc]; exact hi⟩
        · exact absurd hl (not_lt.2 (le_of_lt (hTl p)))
      have hiso1 : CategoryTheory.IsIso (relativeHomologyMap integerCoefficients.{u} f hf (k + 1)) :=
        isIso_relativeHomologyMap_of_pairHomotopyEquiv f g hf hg F hF G hG (k + 1)
      have hiso2 := excision_closed integerCoefficients.{u} Zc A' hZc (k + 1)
      have hsurj : Function.Surjective (relativeHomologyMap integerCoefficients.{u} f hf (k + 1) ≫
          relativeHomologyMap integerCoefficients.{u} (incl (TopCat.of P) Zcᶜ) (mapsTo_incl Zcᶜ A') (k + 1)) := by
        rw [← ModuleCat.epi_iff_surjective]
        infer_instance
      obtain ⟨w, hw⟩ := hsurj (relπ integerCoefficients.{u} (TopCat.of P) A' (k + 1)
        (δ integerCoefficients.{u} (TopCat.of (EU.{u} (k + 1 + 1))) P (k + 1) y))
      rw [← hw]
      have hmor : f ≫ incl (TopCat.of P) Zcᶜ ≫ r' =
          euMap.{u} (Rf k) ≫ f ≫ incl (TopCat.of P) Zcᶜ := by
        ext v : 1
        apply Subtype.ext
        apply ULift.ext
        change Rf (k + 1) (J v.down) = J (Rf k v.down)
        ext i
        induction i using Fin.lastCases with
        | last => rw [show Fin.last (k + 1) = lst from rfl, hRl, hJl, hJl]
        | cast i => rw [hRc, hJc, hJc, hRf]
      have hcomm : relativeHomologyMap integerCoefficients.{u} f hf (k + 1) ≫
          relativeHomologyMap integerCoefficients.{u} (incl (TopCat.of P) Zcᶜ) (mapsTo_incl Zcᶜ A') (k + 1) ≫
            relativeHomologyMap integerCoefficients.{u} r' hr'A (k + 1) =
          relativeHomologyMap integerCoefficients.{u} (euMap.{u} (Rf k)) (euMap_mapsTo (Rf k)) (k + 1) ≫
            relativeHomologyMap integerCoefficients.{u} f hf (k + 1) ≫
              relativeHomologyMap integerCoefficients.{u} (incl (TopCat.of P) Zcᶜ) (mapsTo_incl Zcᶜ A') (k + 1) := by
        rw [← relativeHomologyMap_comp integerCoefficients.{u} _ _ (mapsTo_incl Zcᶜ A') hr'A
            (mapsTo_comp (mapsTo_incl Zcᶜ A') hr'A),
          ← relativeHomologyMap_comp integerCoefficients.{u} _ _ hf (mapsTo_comp (mapsTo_incl Zcᶜ A') hr'A)
            (mapsTo_comp hf (mapsTo_comp (mapsTo_incl Zcᶜ A') hr'A)),
          ← relativeHomologyMap_comp integerCoefficients.{u} _ _ hf (mapsTo_incl Zcᶜ A') (mapsTo_comp hf (mapsTo_incl Zcᶜ A')),
          ← relativeHomologyMap_comp integerCoefficients.{u} _ _ (euMap_mapsTo (Rf k)) (mapsTo_comp hf (mapsTo_incl Zcᶜ A'))
            (mapsTo_comp (euMap_mapsTo (Rf k)) (mapsTo_comp hf (mapsTo_incl Zcᶜ A')))]
        exact relativeHomologyMap_eq_of_eq integerCoefficients.{u} hmor _ _
      have hw2 := congrArg (fun φ => φ w) hcomm
      simp only [ModuleCat.comp_apply] at hw2
      simp only [ModuleCat.comp_apply]
      rw [hw2, ih, map_neg, map_neg]
  exact ⟨Rf m, hdet m, main m⟩

theorem hrelMap_euMap {μ : ℕ} (hμ : 1 ≤ μ)
    (A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ))
    (y : relativeHomology integerCoefficients (TopCat.of (EU.{u} μ)) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) μ) :
    relativeHomologyMap integerCoefficients (euMap.{u} A) (euMap_mapsTo A) μ y =
      ((SignType.sign (LinearMap.det (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin μ))) : SignType) : ℤ) • y := by
  classical
  have hdetmul : ∀ (P Q : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ)),
      LinearMap.det ((P.trans Q : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ)) :
        EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) =
      LinearMap.det (Q : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) *
        LinearMap.det (P : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) := by
    intro P Q
    rw [← LinearMap.det_comp]
    rfl
  have hdetinv : ∀ (P : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ)),
      LinearMap.det (P.symm : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) *
        LinearMap.det (P : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) = 1 := by
    intro P
    rw [← hdetmul, ContinuousLinearEquiv.self_trans_symm]
    exact LinearMap.det_id
  have hA0 : LinearMap.det (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) ≠ 0 := by
    intro h
    have := hdetinv A
    rw [h, mul_zero] at this
    exact zero_ne_one this
  rcases lt_or_gt_of_ne hA0 with hneg | hpos
  · obtain ⟨R, hR, hRy⟩ := exists_reflection_neg.{u} hμ
    set B : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ) := R.symm.trans A with hB
    have hRs : LinearMap.det (R.symm : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin μ)) < 0 := by
      have h1 := hdetinv R
      by_contra hc
      rw [not_lt] at hc
      have : LinearMap.det (R.symm : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) *
          LinearMap.det (R : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hc hR.le
      linarith
    have hBpos : 0 < LinearMap.det (B : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin μ)) := by
      rw [hB, hdetmul]
      exact mul_pos_of_neg_of_neg hneg hRs
    have hcomp : euMap.{u} A = euMap.{u} R ≫ euMap.{u} B := by
      ext x
      simp [euMap, hB]
    have hmap : relativeHomologyMap integerCoefficients (euMap.{u} A) (euMap_mapsTo A) μ =
        relativeHomologyMap integerCoefficients (euMap.{u} R ≫ euMap.{u} B) (hcomp ▸ euMap_mapsTo A) μ := by
      congr 1
    rw [hmap, relativeHomologyMap_comp integerCoefficients (euMap.{u} R) (euMap.{u} B) (euMap_mapsTo R) (euMap_mapsTo B)]
    rw [ModuleCat.comp_apply, hRy, map_neg, hrelMap_euMap_of_det_pos hμ B hBpos y,
      sign_neg hneg]
    simp
  · rw [hrelMap_euMap_of_det_pos hμ A hpos y, sign_pos hpos]
    simp

open Classical in
def euDiscClass {μ : ℕ} (F : EuclideanSpace ℝ (Fin μ) → EuclideanSpace ℝ (Fin μ))
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk μ))) (ULift.down ⁻¹' diskSphere μ) μ) :
    relativeHomology integerCoefficients (TopCat.of (EU.{u} μ)) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) μ :=
  if h : ContinuousOn F (Metric.closedBall 0 1) ∧ ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin μ)) 1, F y ≠ 0 then
    relativeHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ULift.{u} (Disk μ) => ULift.up (F x.down.1),
        continuous_uliftUp.comp (h.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2))⟩)
      (fun x hx => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h'
        exact h.2 x.down.1 hx (congrArg ULift.down h'))
      μ g
  else 0

theorem euDiscClass_isGen {μ : ℕ} (hμ : 1 ≤ μ)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk μ))) (ULift.down ⁻¹' diskSphere μ) μ) (hg : isGen g) :
    isGen (euDiscClass (fun y => y) g) ∧
      ∀ m : ℤ, m • euDiscClass (fun y => y) g = 0 → m = 0 := by
  classical
  let r : EuclideanSpace ℝ (Fin μ) → EuclideanSpace ℝ (Fin μ) := fun z => (max 1 ‖z‖)⁻¹ • z
  have hmax_pos : ∀ z : EuclideanSpace ℝ (Fin μ), 0 < max 1 ‖z‖ :=
    fun z => lt_of_lt_of_le one_pos (le_max_left _ _)
  have hr_cont : Continuous r :=
    ((continuous_const.max continuous_norm).inv₀ fun z => (hmax_pos z).ne').smul continuous_id
  have hr_norm : ∀ z, ‖r z‖ ≤ 1 := by
    intro z
    simp only [r, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hmax_pos z)]
    rw [inv_mul_le_iff₀ (hmax_pos z), mul_one]
    exact le_max_right _ _
  have hr_of_le : ∀ z : EuclideanSpace ℝ (Fin μ), ‖z‖ ≤ 1 → r z = z := by
    intro z hz
    simp [r, max_eq_left hz]
  have hr_of_ge : ∀ z : EuclideanSpace ℝ (Fin μ), 1 ≤ ‖z‖ → r z = ‖z‖⁻¹ • z := by
    intro z hz
    simp [r, max_eq_right hz]
  let C : Set (EU.{u} μ) := Metric.closedBall 0 (1 / 2)
  have h0C : (ULift.up 0 : EU.{u} μ) ∈ C := by
    simp [C, Metric.mem_closedBall]
  let f : TopCat.of (ULift.{u} (Disk μ)) ⟶ TopCat.of (EU.{u} μ) :=
    TopCat.ofHom ⟨fun x => ULift.up x.down.1,
      continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩
  have hf1 : MapsTo f (ULift.down ⁻¹' diskSphere μ) Cᶜ := by
    intro x hx
    have hx1 : ‖(x.down : EuclideanSpace ℝ (Fin μ))‖ = 1 := by
      simpa [diskSphere] using hx
    simp only [C, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, ULift.norm_def, not_le]
    change 1 / 2 < ‖(x.down : EuclideanSpace ℝ (Fin μ))‖
    rw [hx1]; norm_num
  have hf0 : MapsTo f (ULift.down ⁻¹' diskSphere μ) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) :=
    fun x hx => compl_mapsTo h0C (hf1 hx)
  have hr2_mem : ∀ y : EU.{u} μ,
      r ((2 : ℝ) • y.down) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin μ)) 1 :=
    fun y => by rw [Metric.mem_closedBall, dist_zero_right]; exact hr_norm _
  have hgm_cont : Continuous fun y : EU.{u} μ =>
      (ULift.up.{u} (⟨r ((2 : ℝ) • y.down), hr2_mem y⟩ : Disk μ)) :=
    continuous_uliftUp.comp
      ((hr_cont.comp (continuous_uliftDown.const_smul (2 : ℝ))).subtype_mk hr2_mem)
  let gm : TopCat.of (EU.{u} μ) ⟶ TopCat.of (ULift.{u} (Disk μ)) :=
    TopCat.ofHom ⟨fun y => ULift.up.{u} (⟨r ((2 : ℝ) • y.down), hr2_mem y⟩ : Disk μ), hgm_cont⟩
  have hg1 : MapsTo gm Cᶜ (ULift.down ⁻¹' diskSphere μ) := by
    intro y hy
    have hy' : 1 / 2 < ‖y.down‖ := by
      have h := not_le.1 (fun h => hy (Metric.mem_closedBall.2 h))
      rwa [dist_zero_right, ULift.norm_def] at h
    have hy0 : 0 < ‖y.down‖ := by linarith
    have h2 : 1 ≤ ‖(2 : ℝ) • y.down‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos two_pos]; linarith
    change r ((2 : ℝ) • y.down) ∈ Metric.sphere 0 1
    rw [hr_of_ge _ h2, mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (lt_of_lt_of_le one_pos h2)), inv_mul_cancel₀ (by linarith)]
  have hF_mem : ∀ p : unitInterval × ULift.{u} (Disk μ),
      r ((2 - (p.1 : ℝ)) • (p.2.down : EuclideanSpace ℝ (Fin μ))) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin μ)) 1 :=
    fun p => by rw [Metric.mem_closedBall, dist_zero_right]; exact hr_norm _
  have hF_cont0 : Continuous fun p : unitInterval × ULift.{u} (Disk μ) =>
      r ((2 - (p.1 : ℝ)) • (p.2.down : EuclideanSpace ℝ (Fin μ))) := by
    fun_prop
  have hF_cont : Continuous fun p : unitInterval × ULift.{u} (Disk μ) =>
      ULift.up.{u} (⟨r ((2 - (p.1 : ℝ)) • (p.2.down : EuclideanSpace ℝ (Fin μ))), hF_mem p⟩ :
        Disk μ) :=
    continuous_uliftUp.comp (hF_cont0.subtype_mk hF_mem)
  let F : ContinuousMap.Homotopy (f ≫ gm).hom
      (ContinuousMap.id (TopCat.of (ULift.{u} (Disk μ)))) :=
    { toFun := fun p => ULift.up.{u}
        (⟨r ((2 - (p.1 : ℝ)) • (p.2.down : EuclideanSpace ℝ (Fin μ))), hF_mem p⟩ : Disk μ)
      continuous_toFun := hF_cont
      map_zero_left := by
        intro x
        apply ULift.ext; apply Subtype.ext
        change r ((2 - ((0 : unitInterval) : ℝ)) • (x.down : EuclideanSpace ℝ (Fin μ))) =
          r ((2 : ℝ) • (x.down : EuclideanSpace ℝ (Fin μ)))
        simp
      map_one_left := by
        intro x
        apply ULift.ext; apply Subtype.ext
        change r ((2 - ((1 : unitInterval) : ℝ)) • (x.down : EuclideanSpace ℝ (Fin μ))) =
          (x.down : EuclideanSpace ℝ (Fin μ))
        have hx := x.down.2
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        norm_num
        exact hr_of_le _ hx }
  have hF : ∀ t, ∀ x ∈ (ULift.down ⁻¹' diskSphere μ : Set (ULift.{u} (Disk μ))),
      F (t, x) ∈ (ULift.down ⁻¹' diskSphere μ : Set (ULift.{u} (Disk μ))) := by
    intro t x hx
    have hx1 : ‖(x.down : EuclideanSpace ℝ (Fin μ))‖ = 1 := by
      simpa [diskSphere] using hx
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h2 : ‖(2 - (t : ℝ)) • (x.down : EuclideanSpace ℝ (Fin μ))‖ = 2 - t := by
      rw [norm_smul, hx1, Real.norm_eq_abs, abs_of_pos (by linarith), mul_one]
    change r ((2 - (t : ℝ)) • (x.down : EuclideanSpace ℝ (Fin μ))) ∈ Metric.sphere 0 1
    rw [hr_of_ge _ (by rw [h2]; linarith), h2, smul_smul, inv_mul_cancel₀ (by linarith), one_smul,
      mem_sphere_zero_iff_norm, hx1]
  let G : ContinuousMap.Homotopy (gm ≫ f).hom (ContinuousMap.id (TopCat.of (EU.{u} μ))) :=
    { toFun := fun p => ULift.up ((1 - (p.1 : ℝ)) • r ((2 : ℝ) • p.2.down) + (p.1 : ℝ) • p.2.down)
      continuous_toFun := by fun_prop
      map_zero_left := by
        intro y
        apply ULift.ext
        change (1 - ((0 : unitInterval) : ℝ)) • r ((2 : ℝ) • y.down) +
          ((0 : unitInterval) : ℝ) • y.down = r ((2 : ℝ) • y.down)
        simp
      map_one_left := by
        intro y
        apply ULift.ext
        change (1 - ((1 : unitInterval) : ℝ)) • r ((2 : ℝ) • y.down) +
          ((1 : unitInterval) : ℝ) • y.down = y.down
        simp }
  have hG : ∀ t, ∀ y ∈ Cᶜ, G (t, y) ∈ Cᶜ := by
    intro t y hy
    have hy' : 1 / 2 < ‖y.down‖ := by
      have h := not_le.1 (fun h => hy (Metric.mem_closedBall.2 h))
      rwa [dist_zero_right, ULift.norm_def] at h
    have hy0 : 0 < ‖y.down‖ := by linarith
    have h2n : ‖(2 : ℝ) • y.down‖ = 2 * ‖y.down‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos two_pos]
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hval : (1 - (t : ℝ)) • r ((2 : ℝ) • y.down) + (t : ℝ) • y.down =
        ((1 - (t : ℝ)) * ‖y.down‖⁻¹ + t) • y.down := by
      rw [hr_of_ge _ (by rw [h2n]; linarith), h2n, smul_smul, add_smul, smul_smul]
      congr 2
      field_simp
    have hnorm : ‖((1 - (t : ℝ)) * ‖y.down‖⁻¹ + t) • y.down‖ = (1 - t) + t * ‖y.down‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, mul_assoc,
        inv_mul_cancel₀ hy0.ne', mul_one]
    simp only [C, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, ULift.norm_def,
      not_le]
    change 1 / 2 < ‖(1 - (t : ℝ)) • r ((2 : ℝ) • y.down) + (t : ℝ) • y.down‖
    rw [hval, hnorm]
    rcases ht0.lt_or_eq with htp | ht0'
    · nlinarith [mul_lt_mul_of_pos_left hy' htp]
    · rw [← ht0']; norm_num
  have hiso1 := isIso_relativeHomologyMap_of_pairHomotopyEquiv f gm hf1 hg1 F hF G hG μ
  have hiso2 := isIso_ptRes_of_convex integerCoefficients hμ (convex_closedBall (0 : EU.{u} μ) (1 / 2))
    (isCompact_closedBall _ _) h0C μ
  have hcomp : relativeHomologyMap integerCoefficients f hf0 μ =
      relativeHomologyMap integerCoefficients f hf1 μ ≫ relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} μ))) (compl_mapsTo h0C) μ :=
    relativeHomologyMap_comp integerCoefficients f (𝟙 _) hf1 (compl_mapsTo h0C) hf0 μ
  have hiso : IsIso (relativeHomologyMap integerCoefficients f hf0 μ) := by
    rw [hcomp]; infer_instance
  have hdef : euDiscClass (fun y => y) g = relativeHomologyMap integerCoefficients f hf0 μ g := by
    have hcond : ContinuousOn (fun y : EuclideanSpace ℝ (Fin μ) => y) (Metric.closedBall 0 1) ∧
        ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin μ)) 1, (fun y => y) y ≠ 0 := by
      refine ⟨continuousOn_id, fun y hy h => ?_⟩
      have h' : y = 0 := h
      rw [mem_sphere_zero_iff_norm, h', norm_zero] at hy
      exact zero_ne_one hy
    rw [euDiscClass]
    split_ifs with hc
    · rfl
    · exact absurd hcond hc
  let φ := relativeHomologyMap integerCoefficients f hf0 μ
  let e := relativeHomologyEuclideanPointIso integerCoefficients hμ (ULift.up 0 : EU.{u} μ)
  have hφ_surj : ∀ y, φ (inv φ y) = y := fun y => by
    simp [φ]
  have hgen : isGen (euDiscClass (fun y => y) g) := by
    intro y
    obtain ⟨m, hm⟩ := hg (inv φ y)
    refine ⟨m, ?_⟩
    rw [hdef, ← hφ_surj y, hm, map_zsmul]
  refine ⟨hgen, fun m hm => ?_⟩
  have hne : e.hom (euDiscClass (fun y => y) g) ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := hgen (e.inv (ULift.up 1))
    have h1 := congrArg e.hom hk
    rw [map_zsmul, h0, smul_zero, Iso.inv_hom_id_apply] at h1
    exact one_ne_zero (congrArg ULift.down h1)
  have h2 := congrArg e.hom hm
  rw [map_zsmul, map_zero] at h2
  have h3 := congrArg ULift.down h2
  rw [ULift.smul_down, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_right fun h => hne (ULift.ext h)

theorem euDiscClass_linearize {μ : ℕ} (hμ : 1 ≤ μ)
    {F : EuclideanSpace ℝ (Fin μ) → EuclideanSpace ℝ (Fin μ)} (hF0 : F 0 = 0)
    (hF : ContDiffAt ℝ 1 F 0)
    (hdet : LinearMap.det (fderiv ℝ F 0 : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin μ)) ≠ 0)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk μ))) (ULift.down ⁻¹' diskSphere μ) μ) :
    ∃ r₀ > (0 : ℝ), ∀ r : ℝ, 0 < r → r < r₀ →
      euDiscClass (fun y => F (r • y)) g =
        ((SignType.sign (LinearMap.det (fderiv ℝ F 0 : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin μ))) : SignType) : ℤ) • euDiscClass (fun y => y) g := by
  classical
  set L : EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ) := fderiv ℝ F 0 with hLdef
  have hLbij : Function.Bijective (L : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) :=
    (Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  let A : EuclideanSpace ℝ (Fin μ) ≃L[ℝ] EuclideanSpace ℝ (Fin μ) :=
    (LinearEquiv.ofInjectiveEndo (L : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ))
      hLbij.1).toContinuousLinearEquiv
  have hAx : ∀ x, A x = L x := fun x => rfl
  have hAL : (A : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) =
      (L : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ] EuclideanSpace ℝ (Fin μ)) :=
    LinearMap.ext fun x => rfl
  set K : ℝ := ‖(A.symm : EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ))‖ + 1 with hK
  have hKpos : 0 < K := by positivity
  set c : ℝ := K⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hKpos
  have hlow : ∀ x, c * ‖x‖ ≤ ‖L x‖ := by
    intro x
    have h1 : ‖x‖ ≤ K * ‖L x‖ := by
      have h2 : x = (A.symm : EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ)) (L x) := by
        rw [← hAx]; simp
      calc ‖x‖ = ‖(A.symm : EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ)) (L x)‖ := by
            rw [← h2]
        _ ≤ ‖(A.symm : EuclideanSpace ℝ (Fin μ) →L[ℝ] EuclideanSpace ℝ (Fin μ))‖ * ‖L x‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖L x‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [hK]; linarith
    rw [hc, inv_mul_le_iff₀ hKpos]
    exact h1
  have hFd : HasFDerivAt F L 0 :=
    (hF.differentiableAt (by norm_num)).hasFDerivAt
  have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hFd).def (half_pos hcpos)
  have hev := hF.eventually (by simp)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hlo.and hev)
  have hest : ∀ z : EuclideanSpace ℝ (Fin μ), ‖z‖ < δ → ‖F z - L z‖ ≤ c / 2 * ‖z‖ := by
    intro z hz
    have h := (hδP (show dist z 0 < δ by rwa [dist_zero_right])).1
    simpa [hF0] using h
  have hFc : ∀ z : EuclideanSpace ℝ (Fin μ), ‖z‖ < δ → ContinuousAt F z := by
    intro z hz
    exact (hδP (show dist z 0 < δ by rwa [dist_zero_right])).2.continuousAt
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hball : ∀ y : EuclideanSpace ℝ (Fin μ), ‖y‖ ≤ 1 → ‖r • y‖ < δ := by
    intro y hy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc r * ‖y‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hy hr.le
      _ < δ := by linarith
  have hnv : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ y : EuclideanSpace ℝ (Fin μ), ‖y‖ = 1 →
      (1 - t) • F (r • y) + t • L y ≠ 0 := by
    intro t ht0 ht1 y hy hv
    set e := F (r • y) - L (r • y) with he
    have hen : ‖e‖ ≤ c / 2 * r := by
      have := hest (r • y) (hball y hy.le)
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hy, mul_one] at this
    have hLy : c ≤ ‖L y‖ := by simpa [hy] using hlow y
    have hdecomp : (1 - t) • F (r • y) + t • L y = ((1 - t) * r + t) • L y + (1 - t) • e := by
      rw [he, map_smul, smul_sub, smul_smul, add_smul]
      module
    rw [hdecomp] at hv
    have hn := congrArg norm (eq_neg_of_add_eq_zero_left hv)
    rw [norm_neg, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith), abs_of_nonneg (by linarith)] at hn
    have h1 : ((1 - t) * r + t) * c ≤ ((1 - t) * r + t) * ‖L y‖ :=
      mul_le_mul_of_nonneg_left hLy (by nlinarith)
    have h2 : (1 - t) * ‖e‖ ≤ (1 - t) * (c / 2 * r) :=
      mul_le_mul_of_nonneg_left hen (by linarith)
    have h3 : 0 ≤ (1 - t) * r * c := by
      have : 0 ≤ (1 - t) * r := mul_nonneg (by linarith) hr.le
      exact mul_nonneg this hcpos.le
    rcases ht0.lt_or_eq with htp | ht0'
    · nlinarith [mul_pos htp hcpos]
    · subst ht0'
      nlinarith [mul_pos hr hcpos]
  have hcontF : Continuous fun x : ULift.{u} (Disk μ) => F (r • (x.down : EuclideanSpace ℝ (Fin μ))) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    have hx : ‖(x.down : EuclideanSpace ℝ (Fin μ))‖ ≤ 1 := by
      have := x.down.2
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    exact ContinuousAt.comp (f := fun x : ULift.{u} (Disk μ) => r • (x.down : EuclideanSpace ℝ (Fin μ)))
      (hFc _ (hball _ hx)) (by fun_prop)
  let f : TopCat.of (ULift.{u} (Disk μ)) ⟶ TopCat.of (EU.{u} μ) :=
    TopCat.ofHom ⟨fun x => ULift.up x.down.1,
      continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩
  have hf : MapsTo f (ULift.down ⁻¹' diskSphere μ) ({ULift.up 0}ᶜ : Set (EU.{u} μ)) := by
    intro x hx h0
    have hx1 : ‖(x.down : EuclideanSpace ℝ (Fin μ))‖ = 1 := by
      simpa [diskSphere] using hx
    have h0' : (x.down : EuclideanSpace ℝ (Fin μ)) = 0 := congrArg ULift.down h0
    rw [h0', norm_zero] at hx1
    exact zero_ne_one hx1
  have hf1 : MapsTo (f ≫ euMap.{u} A) (ULift.down ⁻¹' diskSphere μ)
      ({ULift.up 0}ᶜ : Set (EU.{u} μ)) :=
    fun x hx => euMap_mapsTo A (hf hx)
  have hid : euDiscClass (fun y => y) g = relativeHomologyMap integerCoefficients f hf μ g := by
    have hcond : ContinuousOn (fun y : EuclideanSpace ℝ (Fin μ) => y) (Metric.closedBall 0 1) ∧
        ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin μ)) 1, (fun y => y) y ≠ 0 := by
      refine ⟨continuousOn_id, fun y hy h => ?_⟩
      have h' : y = 0 := h
      rw [mem_sphere_zero_iff_norm, h', norm_zero] at hy
      exact zero_ne_one hy
    rw [euDiscClass]
    split_ifs with hc
    · rfl
    · exact absurd hcond hc
  have hlin : relativeHomologyMap integerCoefficients (f ≫ euMap.{u} A) hf1 μ g =
      ((SignType.sign (LinearMap.det (fderiv ℝ F 0 : EuclideanSpace ℝ (Fin μ) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin μ))) : SignType) : ℤ) • euDiscClass (fun y => y) g := by
    rw [relativeHomologyMap_comp integerCoefficients f (euMap.{u} A) hf (euMap_mapsTo A) hf1 μ, ModuleCat.comp_apply,
      hrelMap_euMap hμ A, hAL, hid]
  have key : ∀ (f₀ : TopCat.of (ULift.{u} (Disk μ)) ⟶ TopCat.of (EU.{u} μ))
      (h₀ : MapsTo f₀ (ULift.down ⁻¹' diskSphere μ) ({ULift.up 0}ᶜ : Set (EU.{u} μ))),
      (∀ x, f₀ x = ULift.up (F (r • (x.down : EuclideanSpace ℝ (Fin μ))))) →
      relativeHomologyMap integerCoefficients f₀ h₀ μ g = relativeHomologyMap integerCoefficients (f ≫ euMap.{u} A) hf1 μ g := by
    intro f₀ h₀ hf₀
    let Hom : ContinuousMap.Homotopy f₀.hom (f ≫ euMap.{u} A).hom :=
      { toFun := fun p => ULift.up ((1 - (p.1 : ℝ)) • F (r • (p.2.down : EuclideanSpace ℝ (Fin μ))) +
          (p.1 : ℝ) • L (p.2.down : EuclideanSpace ℝ (Fin μ)))
        continuous_toFun := by
          refine continuous_uliftUp.comp ?_
          refine ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            (hcontF.comp continuous_snd)).add ?_
          exact (continuous_subtype_val.comp continuous_fst).smul
            (L.continuous.comp (continuous_subtype_val.comp (continuous_uliftDown.comp continuous_snd)))
        map_zero_left := by
          intro x
          rw [hf₀ x]
          simp
        map_one_left := by
          intro x
          change ULift.up ((1 - ((1 : unitInterval) : ℝ)) • F (r • (x.down : EuclideanSpace ℝ (Fin μ))) +
            ((1 : unitInterval) : ℝ) • L (x.down : EuclideanSpace ℝ (Fin μ))) =
              ULift.up (A (x.down : EuclideanSpace ℝ (Fin μ)))
          simp [hAx] }
    have hH : ∀ t, ∀ x ∈ (ULift.down ⁻¹' diskSphere μ : Set (ULift.{u} (Disk μ))),
        Hom (t, x) ∈ ({ULift.up 0}ᶜ : Set (EU.{u} μ)) := by
      intro t x hx h0
      have hx1 : ‖(x.down : EuclideanSpace ℝ (Fin μ))‖ = 1 := by
        simpa [diskSphere] using hx
      exact hnv t t.2.1 t.2.2 _ hx1 (congrArg ULift.down h0)
    exact congrArg (fun φ => (ConcreteCategory.hom φ) g)
      (relativeHomologyMap_eq_of_homotopy f₀ (f ≫ euMap.{u} A) h₀ hf1 Hom hH μ)
  have hcond : ContinuousOn (fun y => F (r • y)) (Metric.closedBall 0 1) ∧
      ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin μ)) 1, F (r • y) ≠ 0 := by
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · have hy' : ‖y‖ ≤ 1 := by rwa [Metric.mem_closedBall, dist_zero_right] at hy
      exact (ContinuousAt.comp (f := fun y : EuclideanSpace ℝ (Fin μ) => r • y)
        (hFc _ (hball _ hy')) (by fun_prop)).continuousWithinAt
    · have hy1 : ‖y‖ = 1 := by rwa [mem_sphere_zero_iff_norm] at hy
      have := hnv 0 le_rfl zero_le_one y hy1
      simpa using this
  rw [← hlin]
  rw [euDiscClass, dite_eq_left hcond]
  exact key _ _ (fun x => rfl)

theorem sign_det_comp_frame {l : ℕ} (w : EuclideanSpace ℝ (Fin (l + 1)))
    (L : EuclideanSpace ℝ (Fin (l + 1)) →L[ℝ] EuclideanSpace ℝ (Fin l))
    (Φ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin (l + 1))) (hw : w ≠ 0)
    (hLw : L w = 0) (hΦw : ∀ v, inner ℝ w (Φ v) = 0)
    (hor : 0 < (Matrix.of fun i j : Fin (l + 1) =>
      if (j : ℕ) = 0 then w i else if hj : (j : ℕ) - 1 < l then Φ (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i
        else 0).det) :
    SignType.sign (LinearMap.det ((L.comp Φ : EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l)) :
        EuclideanSpace ℝ (Fin l) →ₗ[ℝ] EuclideanSpace ℝ (Fin l))) =
      SignType.sign (Matrix.of fun i j : Fin (l + 1) =>
        if (i : ℕ) = 0 then w j else if hi : (i : ℕ) - 1 < l then L (EuclideanSpace.single j 1) ⟨(i : ℕ) - 1, hi⟩
          else 0).det := by
  have _ := hΦw
  set B : Matrix (Fin (l + 1)) (Fin (l + 1)) ℝ := Matrix.of fun i j : Fin (l + 1) =>
      if (j : ℕ) = 0 then w i else if hj : (j : ℕ) - 1 < l then Φ (EuclideanSpace.single ⟨(j : ℕ) - 1, hj⟩ 1) i
        else 0 with hB
  set A : Matrix (Fin (l + 1)) (Fin (l + 1)) ℝ := Matrix.of fun i j : Fin (l + 1) =>
        if (i : ℕ) = 0 then w j else if hi : (i : ℕ) - 1 < l then L (EuclideanSpace.single j 1) ⟨(i : ℕ) - 1, hi⟩
          else 0 with hA
  have hLsum : ∀ (x : EuclideanSpace ℝ (Fin (l + 1))) (p : Fin l),
      L x p = ∑ j, L (EuclideanSpace.single j 1) p * x j := by
    intro x p
    have hx : x = ∑ j, x j • EuclideanSpace.single j (1 : ℝ) := by
      ext k
      simp [Pi.single_apply]
    conv_lhs => rw [hx]
    simp [map_sum, map_smul, mul_comm]
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin (l + 1)), inner ℝ x y = ∑ j, x j * y j := by
    intro x y
    rw [PiLp.inner_apply]
    simp [mul_comm]
  have hB0 : ∀ i, B i 0 = w i := by intro i; simp [hB]
  have hBs : ∀ i (m : Fin l), B i m.succ = Φ (EuclideanSpace.single m 1) i := by
    intro i m
    simp [hB]
  have hA0 : ∀ j, A 0 j = w j := by intro j; simp [hA]
  have hAs : ∀ (p : Fin l) j, A p.succ j = L (EuclideanSpace.single j 1) p := by
    intro p j
    simp [hA]
  have hAB0 : ∀ p : Fin l, (A * B) p.succ 0 = 0 := by
    intro p
    rw [Matrix.mul_apply]
    simp only [hAs, hB0]
    rw [← hLsum, hLw]
    simp
  have hABs : ∀ (p m : Fin l), (A * B) p.succ m.succ =
      L (Φ (EuclideanSpace.single m 1)) p := by
    intro p m
    rw [Matrix.mul_apply]
    simp only [hAs, hBs]
    rw [← hLsum]
  have hAB00 : (A * B) 0 0 = ‖w‖ ^ 2 := by
    rw [Matrix.mul_apply, ← real_inner_self_eq_norm_sq, hinner]
    simp only [hA0, hB0]
  have hdetAB : (A * B).det = ‖w‖ ^ 2 * LinearMap.det ((L.comp Φ :
      EuclideanSpace ℝ (Fin l) →L[ℝ] EuclideanSpace ℝ (Fin l)) :
        EuclideanSpace ℝ (Fin l) →ₗ[ℝ] EuclideanSpace ℝ (Fin l)) := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp only [hAB0, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
      one_mul, hAB00]
    congr 1
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin l) ℝ).toBasis]
    congr 1
    ext p m
    rw [LinearMap.toMatrix_apply]
    simp [hABs]
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  have hs := congrArg SignType.sign hdetAB
  rw [Matrix.det_mul, sign_mul, sign_mul, sign_pos hor, sign_pos hw2, mul_one, one_mul] at hs
  exact hs.symm

end Handle

namespace Handle

open CategoryTheory SingularPair

universe u

def bigDisc (ℓ : ℕ) (ρ : ℝ) (y : EuclideanSpace ℝ (Fin ℓ)) : EuclideanSpace ℝ (Fin (ℓ + 1)) :=
  WithLp.toLp 2 fun i =>
    if h : (i : ℕ) = 0 then Real.cos (ρ * Real.pi * ‖y‖)
    else Real.sin (ρ * Real.pi * ‖y‖) * (‖y‖⁻¹ * y ⟨(i : ℕ) - 1, by have := i.2; omega⟩)

theorem bigDisc_spec (ℓ : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    MapsTo (bigDisc ℓ ρ) (Metric.closedBall 0 1) (unitSphere ℓ) ∧
      InjOn (bigDisc ℓ ρ) (Metric.closedBall 0 1) ∧
      (∀ z ∈ unitSphere ℓ, Real.cos (ρ * Real.pi) ≤ z 0 →
        ∃ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1, bigDisc ℓ ρ y = z) ∧
      (∀ y : EuclideanSpace ℝ (Fin ℓ), bigDisc ℓ ρ y 0 = Real.cos (ρ * Real.pi * ‖y‖)) ∧
      bigDisc ℓ ρ 0 = EuclideanSpace.single 0 1 ∧ Continuous (bigDisc ℓ ρ) ∧
      ContDiffOn ℝ ∞ (bigDisc ℓ ρ) {y | y ≠ 0} := by
  have hform : ∀ y : EuclideanSpace ℝ (Fin ℓ), bigDisc ℓ ρ y = WithLp.toLp 2
      (Fin.cons (Real.cos (ρ * Real.pi * ‖y‖))
        (fun j : Fin ℓ => Real.sin (ρ * Real.pi * ‖y‖) * (‖y‖⁻¹ * y j)) :
          Fin (ℓ + 1) → ℝ) := by
    intro y
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [bigDisc]
    · simp [bigDisc]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsinc : ∀ (y : EuclideanSpace ℝ (Fin ℓ)) (j : Fin ℓ),
      Real.sin (ρ * Real.pi * ‖y‖) * (‖y‖⁻¹ * y j) =
        ρ * Real.pi * Real.sinc (ρ * Real.pi * ‖y‖) * y j := by
    intro y j
    by_cases hy : y = 0
    · subst hy; simp
    · have ht : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
      have hθ : ρ * Real.pi * ‖y‖ ≠ 0 := by positivity
      rw [Real.sinc_of_ne_zero hθ]
      field_simp
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin ℓ), ‖bigDisc ℓ ρ y‖ = 1 := by
    intro y
    have h2 : ‖bigDisc ℓ ρ y‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, hform, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hy : y = 0
      · subst hy; simp
      · have ht : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
        have hy2 := EuclideanSpace.real_norm_sq_eq y
        have : ∑ j : Fin ℓ, (Real.sin (ρ * Real.pi * ‖y‖) * (‖y‖⁻¹ * y j)) ^ 2 =
            Real.sin (ρ * Real.pi * ‖y‖) ^ 2 * (‖y‖⁻¹) ^ 2 * ∑ j : Fin ℓ, y j ^ 2 := by
          rw [Finset.mul_sum]; congr 1; ext j; ring
        rw [this, ← hy2]
        field_simp
        nlinarith [Real.sin_sq_add_cos_sq (ρ * Real.pi * ‖y‖)]
    have h0 : 0 ≤ ‖bigDisc ℓ ρ y‖ := norm_nonneg _
    nlinarith
  have hc0 : ∀ y : EuclideanSpace ℝ (Fin ℓ), bigDisc ℓ ρ y 0 = Real.cos (ρ * Real.pi * ‖y‖) := by
    intro y; simp [bigDisc]
  have hcs : ∀ (y : EuclideanSpace ℝ (Fin ℓ)) (j : Fin ℓ),
      bigDisc ℓ ρ y j.succ = Real.sin (ρ * Real.pi * ‖y‖) * (‖y‖⁻¹ * y j) := by
    intro y j; rw [hform]; simp
  have hρπ : ρ * Real.pi < Real.pi := by nlinarith
  refine ⟨?_, ?_, ?_, hc0, ?_, ?_, ?_⟩
  · intro y _
    change bigDisc ℓ ρ y ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm]; exact hnorm y
  · intro y hy y' hy' h
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    have hy1' : ‖y'‖ ≤ 1 := by simpa using hy'
    have hcos : Real.cos (ρ * Real.pi * ‖y‖) = Real.cos (ρ * Real.pi * ‖y'‖) := by
      rw [← hc0, ← hc0, h]
    have hθ : ρ * Real.pi * ‖y‖ = ρ * Real.pi * ‖y'‖ := by
      refine Real.injOn_cos ⟨by positivity, ?_⟩ ⟨by positivity, ?_⟩ hcos
      · nlinarith [norm_nonneg y]
      · nlinarith [norm_nonneg y']
    have hnn : ‖y‖ = ‖y'‖ := by
      have : ρ * Real.pi ≠ 0 := by positivity
      exact mul_left_cancel₀ this hθ
    by_cases hy0 : y = 0
    · subst hy0
      have : y' = 0 := by
        rw [← norm_eq_zero, ← hnn]; simp
      rw [this]
    · have ht : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy0
      have htp : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      have hsin : Real.sin (ρ * Real.pi * ‖y‖) ≠ 0 := by
        refine (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_).ne'
        nlinarith
      ext j
      have hj := congrArg (fun z : EuclideanSpace ℝ (Fin (ℓ + 1)) => z j.succ) h
      simp only [hcs] at hj
      rw [← hnn] at hj
      have := mul_left_cancel₀ hsin hj
      have := mul_left_cancel₀ (inv_ne_zero ht) this
      exact this
  · intro z hz hz0
    have hz1 : ‖z‖ = 1 := by simpa using hz
    set w : EuclideanSpace ℝ (Fin ℓ) := WithLp.toLp 2 (fun j : Fin ℓ => z j.succ) with hw
    have hwj : ∀ j : Fin ℓ, w j = z j.succ := fun j => rfl
    have hw2 : ‖w‖ ^ 2 = 1 - z 0 ^ 2 := by
      have h1 := EuclideanSpace.real_norm_sq_eq z
      rw [hz1, Fin.sum_univ_succ] at h1
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [hwj]
      linarith
    have hzsq : z 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖w‖]
    have hzle : z 0 ≤ 1 := by nlinarith
    have hzge : -1 ≤ z 0 := by nlinarith
    set θ := Real.arccos (z 0) with hθdef
    have hθ0 : 0 ≤ θ := Real.arccos_nonneg _
    have hθle : θ ≤ ρ * Real.pi := by
      have := Real.arccos_le_arccos hz0
      rwa [Real.arccos_cos (by positivity) hρπ.le] at this
    have hcosθ : Real.cos θ = z 0 := Real.cos_arccos hzge hzle
    have hsinθ : Real.sin θ = ‖w‖ := by
      rw [hθdef, Real.sin_arccos, ← hw2, Real.sqrt_sq (norm_nonneg _)]
    have hρπ0 : 0 < ρ * Real.pi := by positivity
    by_cases hw0 : w = 0
    · have hθz : θ = 0 := by
        by_contra hne
        have hpos : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hne)
        have := Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
        rw [hsinθ, hw0, norm_zero] at this
        exact lt_irrefl _ this
      refine ⟨0, by simp, ?_⟩
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hc0, ← hcosθ, hθz]; simp
      · rw [hcs, ← hwj, hw0]; simp
    · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hθpos : 0 < θ := by
        by_contra hne
        have : θ = 0 := le_antisymm (not_lt.mp hne) hθ0
        rw [this, Real.sin_zero] at hsinθ
        exact hwn.ne hsinθ
      refine ⟨(θ / (ρ * Real.pi) / ‖w‖) • w, ?_, ?_⟩
      · have : ‖(θ / (ρ * Real.pi) / ‖w‖) • w‖ = θ / (ρ * Real.pi) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          field_simp
        rw [mem_closedBall_zero_iff, this, div_le_one hρπ0]
        exact hθle
      · have hny : ‖(θ / (ρ * Real.pi) / ‖w‖) • w‖ = θ / (ρ * Real.pi) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          field_simp
        have harg : ρ * Real.pi * (θ / (ρ * Real.pi)) = θ := by field_simp
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [hc0, hny, harg, hcosθ]
        · rw [hcs, hny, harg, hsinθ, ← hwj]
          simp only [PiLp.smul_apply, smul_eq_mul]
          field_simp
  · ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [hc0]; simp
    · rw [hcs]; simp [Fin.succ_ne_zero]
  · have heq : bigDisc ℓ ρ = fun y : EuclideanSpace ℝ (Fin ℓ) => WithLp.toLp 2
        (Fin.cons (Real.cos (ρ * Real.pi * ‖y‖))
          (fun j : Fin ℓ => ρ * Real.pi * Real.sinc (ρ * Real.pi * ‖y‖) * y j) :
            Fin (ℓ + 1) → ℝ) := by
      funext y; rw [hform]; simp only [hsinc]
    rw [heq]
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]; fun_prop
    · simp only [Fin.cons_succ]
      have h1 : Continuous fun y : EuclideanSpace ℝ (Fin ℓ) => y j :=
        (EuclideanSpace.proj j).continuous
      exact (continuous_const.mul (Real.continuous_sinc.comp
        (continuous_const.mul continuous_norm))).mul h1
  · rw [contDiffOn_piLp]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [hc0]
      intro x hx
      have hx' : x ≠ 0 := hx
      exact (Real.contDiff_cos.contDiffAt.comp x
        (contDiffAt_const.mul (contDiffAt_norm ℝ hx'))).contDiffWithinAt
    · simp only [hcs]
      intro x hx
      have hx' : x ≠ 0 := hx
      have hn : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin ℓ) => ‖y‖) x :=
        contDiffAt_norm ℝ hx'
      have hp : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin ℓ) => y j) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt
      exact ((Real.contDiff_sin.contDiffAt.comp x (contDiffAt_const.mul hn)).mul
        ((hn.inv (norm_ne_zero_iff.mpr hx')).mul hp)).contDiffWithinAt

theorem exists_rotation_sphereClass (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (w : EuclideanSpace ℝ (Fin (ℓ + 1)))
    (hw : ‖w‖ = 1) :
    ∃ R : EuclideanSpace ℝ (Fin (ℓ + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1)),
      R (EuclideanSpace.single 0 1) = w ∧
      0 < LinearMap.det (R.toLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
        EuclideanSpace ℝ (Fin (ℓ + 1))) ∧
      ∀ {X : Type u} [TopologicalSpace X] (B A : Set X) (F : EuclideanSpace ℝ (Fin (ℓ + 1)) → X)
        (gS : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ), ContinuousOn F (unitSphere ℓ) → MapsTo F (unitSphere ℓ) B →
        sphereClass B A (F ∘ R) gS = sphereClass B A F gS := by
  classical
  set e : EuclideanSpace ℝ (Fin (ℓ + 1)) := EuclideanSpace.single 0 1 with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  obtain ⟨u, α, hu, heu, hα0, hwα⟩ : ∃ (u : EuclideanSpace ℝ (Fin (ℓ + 1))) (α : ℝ), ‖u‖ = 1 ∧
      inner ℝ e u = 0 ∧ 0 ≤ α ∧ w = Real.cos α • e + Real.sin α • u := by
    set a : ℝ := inner ℝ e w with ha_def
    set v : EuclideanSpace ℝ (Fin (ℓ + 1)) := w - a • e with hv_def
    have hev : inner ℝ e v = 0 := by
      simp only [hv_def, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he, ha_def]
      ring
    have hwv : w = a • e + v := by simp [hv_def]
    have hnorm : a ^ 2 + ‖v‖ ^ 2 = 1 := by
      have h1 : ‖w‖ ^ 2 = ‖a • e + v‖ ^ 2 := by rw [← hwv]
      rw [hw, norm_add_sq_real, inner_smul_left, hev, norm_smul, he] at h1
      simp only [Real.norm_eq_abs, sq_abs, mul_one, mul_zero, add_zero, one_pow] at h1
      simpa [sq_abs] using h1.symm
    have ha1 : -1 ≤ a ∧ a ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg ‖v‖, norm_nonneg v]
    have hcos : Real.cos (Real.arccos a) = a := Real.cos_arccos ha1.1 ha1.2
    have hsin : Real.sin (Real.arccos a) = ‖v‖ := by
      rw [Real.sin_arccos, show 1 - a ^ 2 = ‖v‖ ^ 2 by linarith]
      exact Real.sqrt_sq (norm_nonneg v)
    by_cases hv0 : v = 0
    · refine ⟨EuclideanSpace.single ⟨1, by omega⟩ 1, Real.arccos a, by simp, ?_,
        Real.arccos_nonneg a, ?_⟩
      · rw [he_def, EuclideanSpace.inner_single_left]
        simp
      · rw [hcos, hsin, hv0]
        simpa [hv0] using hwv
    · refine ⟨‖v‖⁻¹ • v, Real.arccos a, ?_, ?_, Real.arccos_nonneg a, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]
      · rw [inner_smul_right, hev, mul_zero]
      · rw [hcos, hsin, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0), one_smul]
        exact hwv
  obtain ⟨L, hLc, hL⟩ : ∃ L : ℝ → (EuclideanSpace ℝ (Fin (ℓ + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))),
      Continuous L ∧ ∀ θ x, L θ x = x + (Real.cos θ - 1) • (inner ℝ e x • e + inner ℝ u x • u) +
        Real.sin θ • (inner ℝ e x • u - inner ℝ u x • e) := by
    refine ⟨fun θ => ContinuousLinearMap.id ℝ _ +
      (Real.cos θ - 1) • ((innerSL ℝ e).smulRight e + (innerSL ℝ u).smulRight u) +
      Real.sin θ • ((innerSL ℝ e).smulRight u - (innerSL ℝ u).smulRight e), ?_, ?_⟩
    · fun_prop
    · intro θ x
      simp
  have hLnorm : ∀ θ x, ‖L θ x‖ = ‖x‖ := by
    intro θ x
    have hsc := Real.sin_sq_add_cos_sq θ
    have hue : inner ℝ u e = 0 := by rw [real_inner_comm]; exact heu
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hsq : ‖L θ x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hL]
      simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
        inner_smul_left, inner_smul_right, hue, heu, hee, huu, RCLike.conj_to_real]
      have hxe : inner ℝ x e = inner ℝ e x := real_inner_comm _ _
      have hxu : inner ℝ x u = inner ℝ u x := real_inner_comm _ _
      simp only [hxe, hxu]
      linear_combination (inner ℝ e x ^ 2 + inner ℝ u x ^ 2) * hsc
    have := norm_nonneg (L θ x)
    have := norm_nonneg x
    nlinarith [sq_nonneg (‖L θ x‖ - ‖x‖), sq_nonneg (‖L θ x‖ + ‖x‖)]
  have hL0 : ∀ x, L 0 x = x := by
    intro x
    simp [hL]
  have hLe : L α e = w := by
    have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
    have hue : inner ℝ u e = 0 := by rw [real_inner_comm]; exact heu
    rw [hL, hee, hue, hwα]
    module
  obtain ⟨Rf, hRf⟩ : ∃ Rf : ℝ → (EuclideanSpace ℝ (Fin (ℓ + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))),
      ∀ θ x, Rf θ x = L θ x :=
    ⟨fun θ => LinearIsometry.toLinearIsometryEquiv
      { toLinearMap := (L θ : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))),
        norm_map' := hLnorm θ } rfl, fun _ _ => rfl⟩
  have hRlin : ∀ θ, ((Rf θ).toLinearEquiv : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1))) = (L θ : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1))) := by
    intro θ
    exact LinearMap.ext fun x => hRf θ x
  set g : ℝ → ℝ := fun θ => LinearMap.det (L θ : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (ℓ + 1))) with hg_def
  have hgc : Continuous g := ContinuousLinearMap.continuous_det.comp hLc
  have hg0 : g 0 = 1 := by
    have : (L 0 : EuclideanSpace ℝ (Fin (ℓ + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (ℓ + 1))) =
        LinearMap.id := by
      exact LinearMap.ext fun x => hL0 x
    simp only [hg_def, this, LinearMap.det_id]
  have hgne : ∀ θ, g θ ≠ 0 := by
    intro θ
    simp only [hg_def]
    rw [← hRlin θ]
    exact (LinearEquiv.isUnit_det' _).ne_zero
  have hgα : 0 < g α := by
    by_contra hneg'
    have hneg : g α ≤ 0 := not_lt.mp hneg'
    obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc' hα0 hgc.continuousOn
      (show (0 : ℝ) ∈ Icc (g α) (g 0) by rw [hg0]; exact ⟨hneg, zero_le_one⟩)
    exact hgne θ hθ
  refine ⟨Rf α, by rw [hRf, hLe], by rw [hRlin]; exact hgα, ?_⟩
  intro X _ B A F gS hF hFB
  have hmaps : ∀ θ, MapsTo (L θ) (unitSphere ℓ) (unitSphere ℓ) := by
    intro θ y hy
    simp only [unitSphere, mem_sphere_iff_norm, sub_zero] at hy ⊢
    rw [hLnorm, hy]
  symm
  refine sphereClass_eq_of_homotopy B A F (F ∘ Rf α) (fun t y => F (L (t * α) y)) ?_ ?_ ?_ ?_ gS
  · refine hF.comp ?_ ?_
    · exact ((hLc.comp (continuous_fst.mul continuous_const)).clm_apply continuous_snd).continuousOn
    · intro p hp
      exact hmaps _ hp.2
  · intro y _
    simp [hL0]
  · intro y _
    simp [hRf]
  · intro t _ y hy
    exact hFB (hmaps _ hy)

theorem exists_sphere_bigDisc_sign (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (gS : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) ℓ) (hgS : isGen gS)
    (gD : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk ℓ))) (ULift.down ⁻¹' diskSphere ℓ) ℓ) (hgD : isGen gD) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ {X : Type u} [TopologicalSpace X] (B A : Set X)
      (F : EuclideanSpace ℝ (Fin (ℓ + 1)) → X) (ρ : ℝ), 0 < ρ → ρ < 1 →
      ContinuousOn F (unitSphere ℓ) → MapsTo F (unitSphere ℓ) B →
      (∀ z ∈ unitSphere ℓ, z 0 ≤ Real.cos (ρ * Real.pi) → F z ∈ A) →
      sphereClass B A F gS = s • discClass B A (F ∘ bigDisc ℓ ρ) gD := by
  have hcosle : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → Real.cos (b * Real.pi) ≤ Real.cos (a * Real.pi) :=
    fun a b ha hab hb1 => Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have hscale : ∀ (ρ c : ℝ), 0 < c → ∀ y : EuclideanSpace ℝ (Fin ℓ),
      bigDisc ℓ ρ (c • y) = bigDisc ℓ (ρ * c) y := by
    intro ρ c hc y
    unfold bigDisc
    congr 1
    funext i
    have hn : ‖c • y‖ = c * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    split_ifs with h
    · rw [hn]; ring_nf
    · rw [hn, PiLp.smul_apply, smul_eq_mul]
      have e1 : (c * ‖y‖)⁻¹ * (c * y ⟨(i : ℕ) - 1, by have := i.2; omega⟩) =
          ‖y‖⁻¹ * y ⟨(i : ℕ) - 1, by have := i.2; omega⟩ := by
        rw [mul_inv, mul_assoc, ← mul_assoc ‖y‖⁻¹, mul_comm ‖y‖⁻¹ c, mul_assoc, ← mul_assoc c⁻¹,
          inv_mul_cancel₀ hc.ne', one_mul]
      rw [e1]
      ring_nf
  have hgS0 : ∀ m : ℤ, m • gS = 0 → m = 0 := by
    intro m hm
    let i := Sphere.singularHomologyTopLiftedSphereIso integerCoefficients ℓ (by omega)
    obtain ⟨k, hk⟩ := hgS (i.inv (ULift.up 1))
    have h1 : (ULift.up 1 : integerCoefficients.{u}) = k • i.hom gS := by
      rw [← map_zsmul, ← hk, Iso.inv_hom_id_apply]
    have h2 : m • i.hom gS = 0 := by rw [← map_zsmul, hm, map_zero]
    have h1' := congrArg ULift.down h1
    have h2' := congrArg ULift.down h2
    simp only [ULift.smul_down, smul_eq_mul, ULift.zero_down] at h1' h2'
    rcases mul_eq_zero.1 h2' with h | h
    · exact h
    · rw [h, mul_zero] at h1'
      exact absurd h1' one_ne_zero
  have hrelπ : ∀ (V : Set (ULift.{u} (unitSphere ℓ))) [ContractibleSpace ↥V],
      Function.Bijective (relπ integerCoefficients (Sphere.liftedSphere.{u} ℓ) V ℓ) := by
    intro V _
    have hmono : Mono (relπ integerCoefficients (Sphere.liftedSphere.{u} ℓ) V ℓ) := by
      rw [(les_exact₂ integerCoefficients (Sphere.liftedSphere.{u} ℓ) V ℓ).mono_g_iff]
      exact (isZero_of_contractible integerCoefficients V ℓ (by omega)).eq_of_src _ _
    have hepi : Epi (relπ integerCoefficients (Sphere.liftedSphere.{u} ℓ) V ℓ) := by
      obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [(les_red_exact₃ integerCoefficients (Sphere.liftedSphere.{u} (0 + 1)) V).epi_f_iff]
        exact (isZero_reducedHomologyZero_of_contractible integerCoefficients V).eq_of_tgt _ _
      · rw [(les_exact₃ integerCoefficients (Sphere.liftedSphere.{u} (k + 1)) V k).epi_f_iff]
        exact (isZero_of_contractible integerCoefficients V k (by omega)).eq_of_tgt _ _
    exact ⟨(ModuleCat.mono_iff_injective _).1 hmono, (ModuleCat.epi_iff_surjective _).1 hepi⟩
  have hcontr : ∀ c : ℝ, -1 ≤ c → c < 1 →
      ContractibleSpace ↥({x : ULift.{u} (unitSphere ℓ) | (x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0 ≤ c}) := by
    intro c hc0 hc1
    set e₀ : EuclideanSpace ℝ (Fin (ℓ + 1)) := EuclideanSpace.single 0 1 with he₀
    have he₀0 : e₀ 0 = 1 := by simp [he₀]
    have he₀n : ‖e₀‖ = 1 := by simp [he₀]
    have key : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ z : EuclideanSpace ℝ (Fin (ℓ + 1)), ‖z‖ = 1 → z 0 ≤ c →
        0 < ‖(1 - t) • z - t • e₀‖ ∧ ((1 - t) • z - t • e₀) 0 ≤ c * ‖(1 - t) • z - t • e₀‖ := by
      intro t ht0 ht1 z hz hzc
      set w := (1 - t) • z - t • e₀ with hw
      have hw0 : w 0 = (1 - t) * z 0 - t := by simp [hw, he₀0]
      have hz0 : |z 0| ≤ 1 := by
        have := PiLp.norm_apply_le z 0
        rw [hz] at this
        simpa [Real.norm_eq_abs] using this
      have hN1 : ‖w‖ ≤ 1 := by
        calc ‖w‖ ≤ ‖(1 - t) • z‖ + ‖t • e₀‖ := norm_sub_le _ _
          _ = 1 := by
            rw [norm_smul, norm_smul, hz, he₀n, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith), abs_of_nonneg ht0]
            ring
      have hN2 : (1 - t) - t ≤ ‖w‖ := by
        have := norm_sub_norm_le ((1 - t) • z) (t • e₀)
        rw [norm_smul, norm_smul, hz, he₀n, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by linarith), abs_of_nonneg ht0] at this
        linarith
      have hpos : 0 < ‖w‖ := by
        rcases (norm_nonneg w).lt_or_eq with h | h
        · exact h
        · exfalso
          have hw' : w = 0 := norm_eq_zero.1 h.symm
          have h1 : ‖(1 - t) • z‖ = ‖t • e₀‖ := by
            rw [hw, sub_eq_zero] at hw'
            rw [hw']
          rw [norm_smul, norm_smul, hz, he₀n, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg ht0] at h1
          have h2 : w 0 = 0 := by rw [hw']; rfl
          rw [hw0] at h2
          have ht : t = 1 / 2 := by linarith
          subst ht
          have : z 0 = 1 := by linarith
          linarith
      refine ⟨hpos, ?_⟩
      rw [hw0]
      have hle : (1 - t) * z 0 - t ≤ z 0 * ‖w‖ := by
        rcases le_or_gt 0 (z 0) with h | h
        · have := abs_le.1 hz0
          nlinarith
        · have := abs_le.1 hz0
          nlinarith
      nlinarith
    set V := ({x : ULift.{u} (unitSphere ℓ) | (x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0 ≤ c}) with hV
    have hme₀ : -e₀ ∈ unitSphere ℓ := by simp [he₀n]
    let p : V := ⟨ULift.up ⟨-e₀, hme₀⟩, by simp [hV, he₀0, hc0]⟩
    have : Nonempty V := ⟨p⟩
    rw [contractible_iff_id_nullhomotopic]
    refine ⟨p, ⟨?_⟩⟩
    let w : unitInterval × V → EuclideanSpace ℝ (Fin (ℓ + 1)) := fun q =>
      (1 - (q.1 : ℝ)) • ((q.2.1.down : EuclideanSpace ℝ (Fin (ℓ + 1)))) - (q.1 : ℝ) • e₀
    have hwk : ∀ q : unitInterval × V, 0 < ‖w q‖ ∧ w q 0 ≤ c * ‖w q‖ := fun q =>
      key q.1 q.1.2.1 q.1.2.2 _ (by simp) q.2.2
    have hwc : Continuous w := by fun_prop
    have hnc : Continuous fun q => ‖w q‖⁻¹ • w q :=
      ((continuous_norm.comp hwc).inv₀ fun q => (hwk q).1.ne').smul hwc
    have hmem : ∀ q, ‖w q‖⁻¹ • w q ∈ unitSphere ℓ := fun q => by
      simp [norm_smul, (hwk q).1.ne']
    have hmemV : ∀ q, (ULift.up.{u} (⟨‖w q‖⁻¹ • w q, hmem q⟩ : unitSphere ℓ)) ∈ V := fun q => by
      change (‖w q‖⁻¹ • w q) 0 ≤ c
      rw [PiLp.smul_apply, smul_eq_mul, inv_mul_le_iff₀ (hwk q).1]
      linarith [(hwk q).2]
    exact
      { toFun := fun q => ⟨ULift.up ⟨‖w q‖⁻¹ • w q, hmem q⟩, hmemV q⟩
        continuous_toFun := (continuous_uliftUp.comp (hnc.subtype_mk _)).subtype_mk _
        map_zero_left := fun x => by
          apply Subtype.ext; apply ULift.ext; apply Subtype.ext
          have : ‖(x.1.down : EuclideanSpace ℝ (Fin (ℓ + 1)))‖ = 1 := by simp
          simp [w, this]
        map_one_left := fun x => by
          apply Subtype.ext; apply ULift.ext; apply Subtype.ext
          simp [w, he₀n, p] }
  let V : ℝ → Set (ULift.{u} (unitSphere ℓ)) := fun ρ =>
    {x | (x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0 ≤ Real.cos (ρ * Real.pi)}
  let bm : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 →
      (TopCat.of (ULift.{u} (Disk ℓ)) ⟶ Sphere.liftedSphere.{u} ℓ) := fun ρ hρ =>
    TopCat.ofHom ⟨fun x => ULift.up ⟨bigDisc ℓ ρ x.down.1, (bigDisc_spec ℓ hρ.1 hρ.2).1 x.down.2⟩,
      continuous_uliftUp.comp (((bigDisc_spec ℓ hρ.1 hρ.2).2.2.2.2.2.1.comp
        (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _)⟩
  have hbmV : ∀ ρ₁ ρ₂ (h₂ : ρ₂ ∈ Ioo (0 : ℝ) 1), 0 ≤ ρ₁ → ρ₁ ≤ ρ₂ →
      MapsTo (bm ρ₂ h₂) (ULift.down ⁻¹' diskSphere ℓ) (V ρ₁) := by
    intro ρ₁ ρ₂ h₂ h₁0 h₁₂ x hx
    have hx1 : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
    change (bigDisc ℓ ρ₂ x.down.1) 0 ≤ Real.cos (ρ₁ * Real.pi)
    rw [(bigDisc_spec ℓ h₂.1 h₂.2).2.2.2.1, hx1, mul_one]
    exact hcosle ρ₁ ρ₂ h₁0 h₁₂ h₂.2.le
  have hVsub : ∀ ρ₁ ρ₂ : ℝ, 0 ≤ ρ₁ → ρ₁ ≤ ρ₂ → ρ₂ ≤ 1 → V ρ₂ ⊆ V ρ₁ :=
    fun ρ₁ ρ₂ h₁ h₁₂ h₂ x (hx : _ ≤ _) => (hx.trans (hcosle ρ₁ ρ₂ h₁ h₁₂ h₂) : _ ≤ _)
  have hG : ∀ ρ₁ ρ₂ (h₁ : ρ₁ ∈ Ioo (0 : ℝ) 1) (h₂ : ρ₂ ∈ Ioo (0 : ℝ) 1) (h₁₂ : ρ₁ ≤ ρ₂),
      relativeHomologyMap integerCoefficients (bm ρ₂ h₂) (hbmV ρ₁ ρ₂ h₂ h₁.1.le h₁₂) ℓ =
        relativeHomologyMap integerCoefficients (bm ρ₁ h₁) (hbmV ρ₁ ρ₁ h₁ h₁.1.le le_rfl) ℓ := by
    intro ρ₁ ρ₂ h₁ h₂ h₁₂
    let cf : unitInterval → ℝ := fun t => 1 - (t : ℝ) + (t : ℝ) * (ρ₁ / ρ₂)
    have hρ₂ : ρ₂ ≠ 0 := h₂.1.ne'
    have hq : 0 < ρ₁ / ρ₂ := div_pos h₁.1 h₂.1
    have hq1 : ρ₁ / ρ₂ ≤ 1 := (div_le_one h₂.1).2 h₁₂
    have hcf0 : ∀ t, 0 < cf t := fun t => by
      have := t.2.1; have := t.2.2
      simp only [cf]; nlinarith
    have hcf1 : ∀ t, cf t ≤ 1 := fun t => by
      have := t.2.1; have := t.2.2
      simp only [cf]; nlinarith
    have hρc : ∀ t, ρ₁ ≤ ρ₂ * cf t := fun t => by
      have := t.2.1; have := t.2.2
      have e : ρ₂ * cf t = ρ₂ * (1 - (t : ℝ)) + (t : ℝ) * ρ₁ := by
        simp only [cf]; field_simp
      rw [e]; nlinarith
    have hmemB : ∀ (t : unitInterval) (x : ULift.{u} (Disk ℓ)),
        cf t • x.down.1 ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1 := fun t x => by
      have hx := x.down.2
      rw [mem_closedBall_zero_iff] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcf0 t)]
      nlinarith [hcf0 t, hcf1 t, norm_nonneg x.down.1]
    refine relativeHomologyMap_eq_of_homotopy _ _ _ _
      { toFun := fun q => ULift.up ⟨bigDisc ℓ ρ₂ (cf q.1 • q.2.down.1),
          (bigDisc_spec ℓ h₂.1 h₂.2).1 (hmemB q.1 q.2)⟩
        continuous_toFun := continuous_uliftUp.comp (((bigDisc_spec ℓ h₂.1 h₂.2).2.2.2.2.2.1.comp
          (by fun_prop)).subtype_mk _)
        map_zero_left := fun x => by
          apply ULift.ext; apply Subtype.ext
          simp [cf]
          rfl
        map_one_left := fun x => by
          apply ULift.ext; apply Subtype.ext
          change bigDisc ℓ ρ₂ (cf 1 • x.down.1) = bigDisc ℓ ρ₁ x.down.1
          rw [hscale _ _ (hcf0 1)]
          congr 1
          simp only [cf, Set.Icc.coe_one]
          rw [sub_self, zero_add, one_mul, mul_div_cancel₀ _ hρ₂] } ?_ ℓ
    intro t x hx
    have hx1 : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
    change (bigDisc ℓ ρ₂ (cf t • x.down.1)) 0 ≤ Real.cos (ρ₁ * Real.pi)
    rw [hscale _ _ (hcf0 t), (bigDisc_spec ℓ (mul_pos h₂.1 (hcf0 t))
      (lt_of_le_of_lt (mul_le_of_le_one_right h₂.1.le (hcf1 t)) h₂.2)).2.2.2.1, hx1, mul_one]
    exact hcosle ρ₁ _ h₁.1.le (hρc t) ((mul_le_of_le_one_right h₂.1.le (hcf1 t)).trans h₂.2.le)
  have hstep1 : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∀ (h : MapsTo (𝟙 (TopCat.of (ULift.{u} (Disk ℓ)))) (ULift.down ⁻¹' diskSphere ℓ)
        {x : ULift.{u} (Disk ℓ) | a ≤ ‖x.down.1‖}),
      IsIso (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (ULift.{u} (Disk ℓ)))) h ℓ) := by
    intro a ha ha1 h
    let r : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ) := fun y => (max a ‖y‖)⁻¹ • y
    have hmax : ∀ y : EuclideanSpace ℝ (Fin ℓ), 0 < max a ‖y‖ := fun y => lt_max_of_lt_left ha
    have hrc : Continuous r :=
      ((continuous_const.max continuous_norm).inv₀ fun y => (hmax y).ne').smul continuous_id
    have hrn : ∀ y, ‖r y‖ = ‖y‖ / max a ‖y‖ := fun y => by
      simp only [r, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hmax y)]
      rw [inv_mul_eq_div]
    have hr1 : ∀ y, ‖r y‖ ≤ 1 := fun y => by
      rw [hrn, div_le_one (hmax y)]; exact le_max_right _ _
    have hrA : ∀ y : EuclideanSpace ℝ (Fin ℓ), a ≤ ‖y‖ → ‖r y‖ = 1 := fun y hy => by
      rw [hrn, max_eq_right hy, div_self (ha.trans_le hy).ne']
    have hrS : ∀ y : EuclideanSpace ℝ (Fin ℓ), ‖y‖ = 1 → r y = y := fun y hy => by
      simp only [r, hy, max_eq_right ha1, inv_one, one_smul]
    let rad : TopCat.of (ULift.{u} (Disk ℓ)) ⟶ TopCat.of (ULift.{u} (Disk ℓ)) :=
      TopCat.ofHom ⟨fun x => ULift.up ⟨r x.down.1, mem_closedBall_zero_iff.2 (hr1 _)⟩,
        continuous_uliftUp.comp ((hrc.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _)⟩
    have hg : MapsTo rad {x : ULift.{u} (Disk ℓ) | a ≤ ‖x.down.1‖} (ULift.down ⁻¹' diskSphere ℓ) :=
      fun x hx => by
        change r x.down.1 ∈ Metric.sphere 0 1
        rw [mem_sphere_zero_iff_norm]; exact hrA _ hx
    have hlin : ∀ (t : unitInterval) (x : ULift.{u} (Disk ℓ)),
        (1 - (t : ℝ)) • r x.down.1 + (t : ℝ) • x.down.1 ∈
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin ℓ)) 1 := fun t x => by
      have hx : ‖x.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.2
      have ht0 := t.2.1; have ht1 := t.2.2
      rw [mem_closedBall_zero_iff]
      calc ‖(1 - (t : ℝ)) • r x.down.1 + (t : ℝ) • x.down.1‖
          ≤ ‖(1 - (t : ℝ)) • r x.down.1‖ + ‖(t : ℝ) • x.down.1‖ := norm_add_le _ _
        _ = (1 - (t : ℝ)) * ‖r x.down.1‖ + (t : ℝ) * ‖x.down.1‖ := by
          rw [norm_smul (1 - (t : ℝ)), norm_smul (t : ℝ), Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (t : ℝ)), abs_of_nonneg ht0]
        _ ≤ 1 := by nlinarith [hr1 x.down.1]
    have hHc : Continuous fun q : unitInterval × ULift.{u} (Disk ℓ) =>
        (ULift.up ⟨(1 - (q.1 : ℝ)) • r q.2.down.1 + (q.1 : ℝ) • q.2.down.1, hlin q.1 q.2⟩ :
          ULift.{u} (Disk ℓ)) :=
      continuous_uliftUp.comp (Continuous.subtype_mk (by fun_prop) _)
    have H0 : ∀ x : ULift.{u} (Disk ℓ),
        (ULift.up ⟨(1 - ((0 : unitInterval) : ℝ)) • r x.down.1 + ((0 : unitInterval) : ℝ) • x.down.1,
          hlin 0 x⟩ : ULift.{u} (Disk ℓ)) = rad x := fun x => by
      apply ULift.ext; apply Subtype.ext
      simp [rad]
    have H1 : ∀ x : ULift.{u} (Disk ℓ),
        (ULift.up ⟨(1 - ((1 : unitInterval) : ℝ)) • r x.down.1 + ((1 : unitInterval) : ℝ) • x.down.1,
          hlin 1 x⟩ : ULift.{u} (Disk ℓ)) = x := fun x => by
      apply ULift.ext; apply Subtype.ext
      simp
    refine isIso_relativeHomologyMap_of_pairHomotopyEquiv (𝟙 _) rad h hg
      { toFun := fun q => ULift.up ⟨(1 - (q.1 : ℝ)) • r q.2.down.1 + (q.1 : ℝ) • q.2.down.1, hlin q.1 q.2⟩
        continuous_toFun := hHc
        map_zero_left := fun x => by rw [H0]; rfl
        map_one_left := H1 } ?_
      { toFun := fun q => ULift.up ⟨(1 - (q.1 : ℝ)) • r q.2.down.1 + (q.1 : ℝ) • q.2.down.1, hlin q.1 q.2⟩
        continuous_toFun := hHc
        map_zero_left := fun x => by rw [H0]; rfl
        map_one_left := H1 } ?_ ℓ
    · intro t x hx
      have hx1 : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
      change (1 - (t : ℝ)) • r x.down.1 + (t : ℝ) • x.down.1 ∈ Metric.sphere 0 1
      rw [hrS _ hx1, ← add_smul, sub_add_cancel, one_smul, mem_sphere_zero_iff_norm]
      exact hx1
    · intro t x hx
      have hx' : a ≤ ‖x.down.1‖ := hx
      have hpos : 0 < ‖x.down.1‖ := ha.trans_le hx'
      have ht0 := t.2.1; have ht1 := t.2.2
      change a ≤ ‖(1 - (t : ℝ)) • r x.down.1 + (t : ℝ) • x.down.1‖
      have e : (1 - (t : ℝ)) • r x.down.1 + (t : ℝ) • x.down.1 =
          ((1 - (t : ℝ)) * ‖x.down.1‖⁻¹ + t) • x.down.1 := by
        simp only [r, max_eq_right hx', smul_smul, add_smul]
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), add_mul, mul_assoc,
        inv_mul_cancel₀ hpos.ne', mul_one]
      nlinarith
  have hiso : ∀ ρ ρ' (h : ρ ∈ Ioo (0 : ℝ) 1) (h' : ρ' ∈ Ioo (0 : ℝ) 1) (hlt : ρ < ρ'),
      IsIso (relativeHomologyMap integerCoefficients (bm ρ' h') (hbmV ρ ρ' h' h.1.le hlt.le) ℓ) := by
    intro ρ ρ' h h' hlt
    have hspec := bigDisc_spec ℓ h'.1 h'.2
    set a := ρ / ρ' with ha_def
    have ha0 : 0 < a := div_pos h.1 h'.1
    have ha1 : a ≤ 1 := (div_le_one h'.1).2 hlt.le
    let Ann : Set (ULift.{u} (Disk ℓ)) := {x | a ≤ ‖x.down.1‖}
    have h1 : MapsTo (𝟙 (TopCat.of (ULift.{u} (Disk ℓ)))) (ULift.down ⁻¹' diskSphere ℓ) Ann :=
      fun x hx => by
        have hx1 : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
        change a ≤ ‖x.down.1‖
        rw [hx1]; exact ha1
    have hI1 := hstep1 a ha0 ha1 h1
    let U : Set (Sphere.liftedSphere.{u} ℓ) :=
      {x | Real.cos (ρ' * Real.pi) ≤ (x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0}
    have hφU : ∀ x : ULift.{u} (Disk ℓ),
        (ULift.up.{u} (⟨bigDisc ℓ ρ' x.down.1, hspec.1 x.down.2⟩ : unitSphere ℓ)) ∈ U := fun x => by
      change Real.cos (ρ' * Real.pi) ≤ bigDisc ℓ ρ' x.down.1 0
      rw [hspec.2.2.2.1]
      have hx : ‖x.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.2
      have := hcosle (ρ' * ‖x.down.1‖) ρ' (by positivity [h'.1.le])
        (mul_le_of_le_one_right h'.1.le hx) h'.2.le
      rw [mul_assoc, mul_comm ‖x.down.1‖, ← mul_assoc] at this
      exact this
    let φ : ULift.{u} (Disk ℓ) → ↥U := fun x =>
      ⟨ULift.up ⟨bigDisc ℓ ρ' x.down.1, hspec.1 x.down.2⟩, hφU x⟩
    have hφinj : Function.Injective φ := fun x x' hxx' => by
      have e : bigDisc ℓ ρ' x.down.1 = bigDisc ℓ ρ' x'.down.1 :=
        congrArg (fun z : ↥U => ((z.1.down : unitSphere ℓ) : EuclideanSpace ℝ (Fin (ℓ + 1)))) hxx'
      exact ULift.ext (Subtype.ext (hspec.2.1 x.down.2 x'.down.2 e))
    have hφsurj : Function.Surjective φ := fun z => by
      obtain ⟨y, hy, hyz⟩ := hspec.2.2.1 z.1.down.1 z.1.down.2 z.2
      refine ⟨ULift.up ⟨y, hy⟩, ?_⟩
      apply Subtype.ext; apply ULift.ext; apply Subtype.ext
      exact hyz
    have hφc : Continuous (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩) :=
      (continuous_uliftUp.comp ((hspec.2.2.2.2.2.1.comp
        (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _)).subtype_mk _
    let hh : ULift.{u} (Disk ℓ) ≃ₜ ↥U := hφc.homeoOfEquivCompactToT2
    have hiff : ∀ x, x ∈ Ann ↔ hh x ∈ (Subtype.val ⁻¹' V ρ : Set ↥U) := fun x => by
      change a ≤ ‖x.down.1‖ ↔ bigDisc ℓ ρ' x.down.1 0 ≤ Real.cos (ρ * Real.pi)
      rw [hspec.2.2.2.1]
      have hx : ‖x.down.1‖ ≤ 1 := mem_closedBall_zero_iff.1 x.down.2
      have hρy : ρ' * ‖x.down.1‖ ≤ 1 := (mul_le_of_le_one_right h'.1.le hx).trans h'.2.le
      have hρyπ := mul_le_mul_of_nonneg_right hρy Real.pi_pos.le
      rw [Real.strictAntiOn_cos.le_iff_ge ⟨by positivity [h'.1.le], by nlinarith [Real.pi_pos, h'.2]⟩
        ⟨by nlinarith [Real.pi_pos, h.1], by nlinarith [Real.pi_pos, h.2]⟩, ha_def,
        div_le_iff₀ h'.1]
      constructor
      · intro hh; nlinarith [Real.pi_pos]
      · intro hh; nlinarith [Real.pi_pos]
    have h2 : MapsTo (homeoHom hh) Ann (Subtype.val ⁻¹' V ρ) := fun x hx => (hiff x).1 hx
    have hI2 := isIso_relativeHomologyMap_homeoHom integerCoefficients hh (homeomorph_image_eq_of_mem_iff hh hiff) h2 ℓ
    have hcont0 : Continuous fun x : Sphere.liftedSphere.{u} ℓ =>
        (x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0 := by fun_prop
    have hcc : Real.cos (ρ' * Real.pi) < Real.cos (ρ * Real.pi) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos, h.1])
        (by nlinarith [Real.pi_pos, h'.2]) (by nlinarith [Real.pi_pos])
    have hcover : interior U ∪ interior (V ρ) = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      rcases lt_or_ge (Real.cos (ρ' * Real.pi)) ((x.down : EuclideanSpace ℝ (Fin (ℓ + 1))) 0) with hx | hx
      · left
        exact interior_maximal (fun y (hy : Real.cos (ρ' * Real.pi) < _) => hy.le)
          (isOpen_lt continuous_const hcont0) hx
      · right
        exact interior_maximal (fun y (hy : _ < Real.cos (ρ * Real.pi)) => hy.le)
          (isOpen_lt hcont0 continuous_const) (lt_of_le_of_lt hx hcc)
    have hI3 := excision integerCoefficients hcover ℓ
    have hfac : bm ρ' h' = 𝟙 _ ≫ (homeoHom hh ≫ incl (Sphere.liftedSphere.{u} ℓ) U) := rfl
    rw [relativeHomologyMap_eq_of_eq integerCoefficients hfac,
      relativeHomologyMap_comp integerCoefficients _ _ h1 (mapsTo_comp h2 (mapsTo_incl U (V ρ))),
      relativeHomologyMap_comp integerCoefficients _ _ h2 (mapsTo_incl U (V ρ))]
    infer_instance
  let e : ∀ ρ : ℝ, relativeHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ) ℓ := fun ρ => relπ integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ) ℓ gS
  let b : ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → relativeHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ) ℓ := fun ρ h =>
    relativeHomologyMap integerCoefficients (bm ρ h) (hbmV ρ ρ h h.1.le le_rfl) ℓ gD
  have hL : ∀ ρ (h : ρ ∈ Ioo (0 : ℝ) 1), (∀ m : ℤ, m • e ρ = 0 → m = 0) ∧
      ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ e ρ = σ • b ρ h := by
    intro ρ h
    have hc1 : Real.cos (ρ * Real.pi) < 1 := by
      have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
        (by nlinarith [Real.pi_pos, h.2] : ρ * Real.pi ≤ Real.pi) (by nlinarith [Real.pi_pos, h.1])
      rwa [Real.cos_zero] at this
    have hC : ContractibleSpace ↥(V ρ) := hcontr _ (Real.neg_one_le_cos _) hc1
    obtain ⟨hinj, hsurj⟩ := hrelπ (V ρ)
    have htors : ∀ m : ℤ, m • e ρ = 0 → m = 0 := by
      intro m hm
      apply hgS0
      apply hinj
      rw [map_zsmul, map_zero]
      exact hm
    have hgene : ∀ x : relativeHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ) ℓ, ∃ m : ℤ, x = m • e ρ := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨m, rfl⟩ := hgS y
      exact ⟨m, map_zsmul _ _ _⟩
    have h' : (ρ + 1) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [h.1], by linarith [h.2]⟩
    have hlt : ρ < (ρ + 1) / 2 := by linarith [h.2]
    have hI := hiso ρ ((ρ + 1) / 2) h h' hlt
    have hsurjb := (ConcreteCategory.bijective_of_isIso
      (relativeHomologyMap integerCoefficients (bm ((ρ + 1) / 2) h') (hbmV ρ ((ρ + 1) / 2) h' h.1.le hlt.le) ℓ)).2
    have hGb := hG ρ ((ρ + 1) / 2) h h' hlt.le
    have hgenb : ∀ x : relativeHomology integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ) ℓ, ∃ k : ℤ, x = k • b ρ h := by
      intro x
      obtain ⟨z, rfl⟩ := hsurjb x
      obtain ⟨k, rfl⟩ := hgD z
      refine ⟨k, ?_⟩
      rw [map_zsmul, hGb]
    obtain ⟨m, hm⟩ := hgenb (e ρ)
    obtain ⟨k, hk⟩ := hgene (b ρ h)
    have h0 : (m * k - 1) • e ρ = 0 := by
      rw [sub_zsmul, one_zsmul, mul_zsmul, ← hk, ← hm, add_neg_cancel]
    have hmk : m * k = 1 := by
      have := htors _ h0
      omega
    exact ⟨htors, m, Int.eq_one_or_neg_one_of_mul_eq_one hmk, hm⟩
  have hι : ∀ ρ₁ ρ₂ (h₁ : ρ₁ ∈ Ioo (0 : ℝ) 1) (h₂ : ρ₂ ∈ Ioo (0 : ℝ) 1) (h₁₂ : ρ₁ ≤ ρ₂),
      relativeHomologyMap integerCoefficients (𝟙 (Sphere.liftedSphere.{u} ℓ))
          (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le)) ℓ (e ρ₂) = e ρ₁ ∧
        relativeHomologyMap integerCoefficients (𝟙 (Sphere.liftedSphere.{u} ℓ))
          (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le)) ℓ (b ρ₂ h₂) = b ρ₁ h₁ := by
    intro ρ₁ ρ₂ h₁ h₂ h₁₂
    constructor
    · have hn := relπ_natural integerCoefficients (𝟙 (Sphere.liftedSphere.{u} ℓ))
        (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le)) ℓ
      rw [singularHomologyMap_id, Category.id_comp] at hn
      change (relπ integerCoefficients (Sphere.liftedSphere.{u} ℓ) (V ρ₂) ℓ ≫ relativeHomologyMap integerCoefficients (𝟙 (Sphere.liftedSphere.{u} ℓ))
          (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le)) ℓ) gS = _
      rw [hn]
    · change (relativeHomologyMap integerCoefficients (bm ρ₂ h₂) (hbmV ρ₂ ρ₂ h₂ h₂.1.le le_rfl) ℓ ≫ relativeHomologyMap integerCoefficients (𝟙 (Sphere.liftedSphere.{u} ℓ))
          (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le)) ℓ) gD = _
      rw [← relativeHomologyMap_comp integerCoefficients _ _ _ _ (mapsTo_comp (hbmV ρ₂ ρ₂ h₂ h₂.1.le le_rfl)
        (mapsTo_id_of_subset (hVsub ρ₁ ρ₂ h₁.1.le h₁₂ h₂.2.le))),
        relativeHomologyMap_eq_of_eq integerCoefficients (Category.comp_id (bm ρ₂ h₂))]
      exact congrArg (fun φ => φ gD) (hG ρ₁ ρ₂ h₁ h₂ h₁₂)
  have hmain : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ ρ (h : ρ ∈ Ioo (0 : ℝ) 1), e ρ = s • b ρ h := by
    have h12 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    obtain ⟨htors, s, hs, hes⟩ := hL (1 / 2) h12
    refine ⟨s, hs, fun ρ h => ?_⟩
    rcases le_or_gt ρ (1 / 2) with hρ | hρ
    · obtain ⟨he, hb⟩ := hι ρ (1 / 2) h h12 hρ
      rw [← he, hes, map_zsmul, hb]
    · obtain ⟨-, σ, hσ, heσ⟩ := hL ρ h
      obtain ⟨he, hb⟩ := hι (1 / 2) ρ h12 h hρ.le
      have h1 : e (1 / 2) = σ • b (1 / 2) h12 := by rw [← he, heσ, map_zsmul, hb]
      have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
      have hb' : b (1 / 2) h12 = s • e (1 / 2) := by
        rw [hes, smul_smul, hss, one_smul]
      have h0 : (σ * s - 1) • e (1 / 2) = 0 := by
        rw [sub_zsmul, one_zsmul, mul_zsmul, ← hb', ← h1, add_neg_cancel]
      have hσs : σ * s = 1 := by
        have := htors _ h0
        omega
      have hσ' : σ = s := by
        rcases hs with rfl | rfl <;> rcases hσ with rfl | rfl <;> omega
      rw [heσ, hσ']
  obtain ⟨s, hs, hsρ⟩ := hmain
  refine ⟨s, hs, ?_⟩
  intro X _ B A F ρ hρ hρ1 hF hFB hFA
  have h : ρ ∈ Ioo (0 : ℝ) 1 := ⟨hρ, hρ1⟩
  have hspec := bigDisc_spec ℓ hρ hρ1
  have hS : ContinuousOn F (unitSphere ℓ) ∧ MapsTo F (unitSphere ℓ) B := ⟨hF, hFB⟩
  have hD : ContinuousOn (F ∘ bigDisc ℓ ρ) (Metric.closedBall 0 1) ∧
      MapsTo (F ∘ bigDisc ℓ ρ) (Metric.closedBall 0 1) B ∧
      MapsTo (F ∘ bigDisc ℓ ρ) (Metric.sphere 0 1) A := by
    refine ⟨hF.comp hspec.2.2.2.2.2.1.continuousOn hspec.1, hFB.comp hspec.1, ?_⟩
    intro y hy
    apply hFA _ (hspec.1 (Metric.sphere_subset_closedBall hy))
    rw [hspec.2.2.2.1, mem_sphere_zero_iff_norm.1 hy, mul_one]
  have nat1 : ∀ (f : Sphere.liftedSphere.{u} ℓ ⟶ TopCat.of ↥B) (hf : MapsTo f (V ρ) (Subtype.val ⁻¹' A)),
      (singularHomologyMap integerCoefficients f ℓ ≫ relπ integerCoefficients (TopCat.of ↥B) (Subtype.val ⁻¹' A) ℓ) gS = relativeHomologyMap integerCoefficients f hf ℓ (e ρ) := by
    intro f hf
    rw [← relπ_natural]
    rfl
  have nat2 : ∀ (f : Sphere.liftedSphere.{u} ℓ ⟶ TopCat.of ↥B) (hf : MapsTo f (V ρ) (Subtype.val ⁻¹' A))
      (g : TopCat.of (ULift.{u} (Disk ℓ)) ⟶ TopCat.of ↥B)
      (hg : MapsTo g (ULift.down ⁻¹' diskSphere ℓ) (Subtype.val ⁻¹' A)), g = bm ρ h ≫ f →
      relativeHomologyMap integerCoefficients f hf ℓ (b ρ h) = relativeHomologyMap integerCoefficients g hg ℓ gD := by
    intro f hf g hg hfg
    subst hfg
    rw [relativeHomologyMap_comp integerCoefficients (bm ρ h) f (hbmV ρ ρ h h.1.le le_rfl) hf hg]
    rfl
  unfold sphereClass discClass
  rw [dite_eq_left hS, dite_eq_left hD]
  refine (nat1 _ ?_).trans ?_
  · intro x hx
    exact hFA _ x.down.2 hx
  · rw [hsρ ρ h, map_zsmul]
    congr 1
    exact nat2 _ _ _ _ rfl

theorem discClass_localize {X : Type u} [TopologicalSpace X] (B C : Set X) {m : ℕ}
    (F : EuclideanSpace ℝ (Fin m) → X) (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hFB : MapsTo F (Metric.closedBall 0 1) B) (Zs : Finset (EuclideanSpace ℝ (Fin m))) {r : ℝ}
    (hr : 0 < r) (hZ : ∀ z ∈ Zs, Metric.closedBall z r ⊆ Metric.ball 0 1)
    (hdisj : ∀ z ∈ Zs, ∀ z' ∈ Zs, z ≠ z' → Disjoint (Metric.closedBall z r) (Metric.closedBall z' r))
    (hC : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, F y ∈ C → y ∈ Zs)
    (g : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m) :
    discClass B (B \ C) F g = ∑ z ∈ Zs, discClass B (B \ C) (fun y => F (z + r • y)) g := by
  classical
  have hUniv : ∀ (Y : TopCat.{u}) (k : ℕ), Limits.IsZero (relativeHomology integerCoefficients Y Set.univ k) := by
    intro Y k
    have : IsIso (incl Y Set.univ) := by
      rw [show incl Y Set.univ = (TopCat.isoOfHomeo (Homeomorph.Set.univ Y)).hom from rfl]
      infer_instance
    have : IsIso (pair Y Set.univ).hom :=
      inferInstanceAs (IsIso (TopCat.toSSet.map (incl Y Set.univ)))
    exact (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map_isZero
      (SSetPair.isZero_chainComplex (pair Y Set.univ) integerCoefficients)
  have hcompId : ∀ (A A' A'' : Set (TopCat.of (EU.{u} m)))
      (h₁ : MapsTo (𝟙 (TopCat.of (EU.{u} m))) A A') (h₂ : MapsTo (𝟙 (TopCat.of (EU.{u} m))) A' A'')
      (h₃ : MapsTo (𝟙 (TopCat.of (EU.{u} m))) A A'') (α : relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) A m),
      relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) h₂ m (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) h₁ m α) =
        relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) h₃ m α := by
    intro A A' A'' h₁ h₂ h₃ α
    rw [← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients (𝟙 _) (𝟙 _) h₁ h₂ (mapsTo_comp h₁ h₂) m]
    exact congrArg (fun f : relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) A m ⟶ relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) A'' m =>
      f α) (relativeHomologyMap_eq_of_eq integerCoefficients (Category.id_comp (𝟙 (TopCat.of (EU.{u} m)))) _ m)
  have hstep : ∀ (A : Set (TopCat.of (EU.{u} m))) (p : TopCat.of (EU.{u} m)), IsClosed A → p ∉ A →
      (∀ α : relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) Aᶜ m,
        (∀ (x : TopCat.of (EU.{u} m)) (hx : x ∈ A), relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) (compl_mapsTo hx) m α = 0) →
          α = 0) →
      ∀ α : relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) ({p} ∪ A)ᶜ m,
        (∀ (x : TopCat.of (EU.{u} m)) (hx : x ∈ ({p} ∪ A : Set (TopCat.of (EU.{u} m)))), relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) (compl_mapsTo hx) m α = 0) →
          α = 0 := by
    intro A p hA hpA hInjA α hα
    have hP : IsOpen ({p}ᶜ : Set (TopCat.of (EU.{u} m))) := isClosed_singleton.isOpen_compl
    have hQ : IsOpen Aᶜ := hA.isOpen_compl
    have hmt : MapsTo (𝟙 (TopCat.of (EU.{u} m))) ({p} ∪ A)ᶜ ({p}ᶜ ∩ Aᶜ) :=
      mapsTo_id_of_subset (Set.compl_union _ _).le
    have hmt' : MapsTo (𝟙 (TopCat.of (EU.{u} m))) ({p}ᶜ ∩ Aᶜ) ({p} ∪ A)ᶜ :=
      mapsTo_id_of_subset (Set.compl_union _ _).ge
    have hinj : Function.Injective (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) hmt m) := by
      intro a b hab
      have := congrArg (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) hmt' m) hab
      rw [hcompId _ _ _ hmt hmt' (mapsTo_id_of_subset le_rfl),
        hcompId _ _ _ hmt hmt' (mapsTo_id_of_subset le_rfl), relativeHomologyMap_id] at this
      exact this
    apply hinj
    rw [map_zero]
    have hU : Limits.IsZero (relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) ({p}ᶜ ∪ Aᶜ) (m + 1)) := by
      have e : ({p}ᶜ ∪ Aᶜ : Set (TopCat.of (EU.{u} m))) = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        by_cases h : x = p
        · exact Or.inr (h ▸ hpA)
        · exact Or.inl h
      exact (hUniv _ (m + 1)).of_iso (relativeHomologyIsoOfEq integerCoefficients _ e (m + 1))
    refine relMV_injective integerCoefficients hP hQ m hU _ ?_ ?_
    · rw [hcompId _ _ _ hmt _ (compl_mapsTo (Or.inl rfl : p ∈ {p} ∪ A))]
      exact hα p (Or.inl rfl)
    · rw [hcompId _ _ _ hmt _
        (mapsTo_id_of_subset (Set.compl_subset_compl.2 Set.subset_union_right))]
      refine hInjA _ fun x hx => ?_
      rw [hcompId _ _ _ _ _ (compl_mapsTo (Or.inr hx : x ∈ {p} ∪ A))]
      exact hα x (Or.inr hx)
  have hpt : ∀ T : Finset (EuclideanSpace ℝ (Fin m)),
      ∀ α : relativeHomology integerCoefficients (TopCat.of (EU.{u} m))
        (ULift.down ⁻¹' (T : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ m,
        (∀ (x : TopCat.of (EU.{u} m)) (hx : x ∈ (ULift.down ⁻¹' (T : Set (EuclideanSpace ℝ (Fin m))) :
            Set (TopCat.of (EU.{u} m)))),
          relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) (compl_mapsTo hx) m α = 0) → α = 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro α _
      have e : (ULift.down ⁻¹' ((∅ : Finset (EuclideanSpace ℝ (Fin m))) :
          Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ = Set.univ := by
        ext x
        simp
      exact (ModuleCat.isZero_iff_subsingleton.1
        ((hUniv _ m).of_iso (relativeHomologyIsoOfEq integerCoefficients _ e m))).elim α 0
    | insert a T haT ih =>
      have e : (ULift.down ⁻¹' ((insert a T : Finset (EuclideanSpace ℝ (Fin m))) :
          Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m))) =
          {ULift.up a} ∪ ULift.down ⁻¹' (T : Set (EuclideanSpace ℝ (Fin m))) := by
        ext x
        simp [ULift.ext_iff]
      rw [e]
      exact hstep _ _ ((T.finite_toSet.isClosed).preimage continuous_uliftDown)
        (by simpa using haT) ih
  let ρ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun y => (max 1 ‖y‖)⁻¹ • y
  have hρc : Continuous ρ :=
    ((continuous_const.max continuous_norm).inv₀ fun y => by positivity).smul continuous_id
  have hρD : ∀ y, ρ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro y
    have h1 : (0 : ℝ) < max 1 ‖y‖ := by positivity
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [ρ, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h1]
    rw [inv_mul_le_iff₀ h1, mul_one]
    exact le_max_right _ _
  have hρid : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1, ρ y = y := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    simp only [ρ, max_eq_left hy, inv_one, one_smul]
  have hρfix : ∀ y, ‖ρ y‖ < 1 → ρ y = y := by
    intro y h
    by_cases hy : ‖y‖ ≤ 1
    · exact hρid y (by rwa [Metric.mem_closedBall, dist_zero_right])
    · exfalso
      replace hy : 1 < ‖y‖ := lt_of_not_ge hy
      have hn : ‖ρ y‖ = 1 := by
        simp only [ρ, max_eq_right hy.le, norm_smul, norm_inv, norm_norm]
        exact inv_mul_cancel₀ (by positivity)
      linarith
  have hZball : ∀ z ∈ Zs, ‖z‖ < 1 := fun z hz => by
    simpa using hZ z hz (Metric.mem_closedBall_self hr.le)
  let aff : EuclideanSpace ℝ (Fin m) → ℝ → (TopCat.of (ULift.{u} (Disk m)) ⟶ TopCat.of (EU.{u} m)) :=
    fun a s => TopCat.ofHom ⟨fun x => ULift.up (a + s • x.down.1),
      continuous_uliftUp.comp (continuous_const.add
        ((continuous_subtype_val.comp continuous_uliftDown).const_smul s))⟩
  let Ft : TopCat.of (EU.{u} m) ⟶ TopCat.of ↥B :=
    TopCat.ofHom ⟨fun w => ⟨F (ρ w.down), hFB (hρD _)⟩,
      (hF.comp_continuous (hρc.comp continuous_uliftDown) fun w => hρD _).subtype_mk _⟩
  have hFt : MapsTo Ft (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) :
      Set (TopCat.of (EU.{u} m)))ᶜ (Subtype.val ⁻¹' (B \ C)) := by
    intro w hw
    refine ⟨hFB (hρD _), fun hc => hw ?_⟩
    have h1 : ρ w.down ∈ Zs := hC _ (hρD _) hc
    have h2 := hρfix _ (hZball _ h1)
    change w.down ∈ (Zs : Set (EuclideanSpace ℝ (Fin m)))
    rw [← h2]
    exact h1
  have hL : ∀ (a : EuclideanSpace ℝ (Fin m)) (s : ℝ)
      (hD : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1,
        a + s • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)
      (h : MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m)
        (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ),
      discClass B (B \ C) (fun y => F (a + s • y)) g =
        relativeHomologyMap integerCoefficients Ft hFt m (relativeHomologyMap integerCoefficients (aff a s) h m g) := by
    intro a s hD h
    have hcont : ContinuousOn (fun y => F (a + s • y))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) :=
      hF.comp (continuous_const.add (continuous_id.const_smul s)).continuousOn hD
    have hmB : MapsTo (fun y => F (a + s • y))
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1) B :=
      fun y hy => hFB (hD y hy)
    have hmA : MapsTo (fun y => F (a + s • y))
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) (B \ C) := by
      intro y hy
      have hyD : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 :=
        Metric.sphere_subset_closedBall hy
      refine ⟨hFB (hD y hyD), fun hc => ?_⟩
      exact h (x := ULift.up ⟨y, hyD⟩) hy (hC _ (hD y hyD) hc)
    rw [discClass, dite_eq_left ⟨hcont, hmB, hmA⟩, ← ModuleCat.comp_apply,
      ← relativeHomologyMap_comp integerCoefficients (aff a s) Ft h hFt (mapsTo_comp h hFt) m]
    refine congrArg (fun φ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m ⟶
      relativeHomologyPair B (B \ C) m => φ g) (relativeHomologyMap_eq_of_eq integerCoefficients ?_ _ m)
    ext x
    change F (a + s • x.down.1) = F (ρ (a + s • x.down.1))
    rw [hρid _ (hD _ x.down.2)]
  have hS1 : MapsTo (aff 0 1) (ULift.down ⁻¹' diskSphere m)
      (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ := by
    intro x hx hK
    have hx' : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
    have : ‖(0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • x.down.1‖ < 1 := hZball _ hK
    rw [zero_add, one_smul, hx'] at this
    exact lt_irrefl _ this
  have hSz : ∀ z ∈ Zs, MapsTo (aff z r) (ULift.down ⁻¹' diskSphere m)
      (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ := by
    intro z hz x hx hK
    have hx' : ‖x.down.1‖ = 1 := by simpa [diskSphere] using hx
    have hK' : z + r • x.down.1 ∈ Zs := hK
    by_cases hzz : z + r • x.down.1 = z
    · have h0 : r • x.down.1 = 0 := by simpa using hzz
      have := congrArg norm h0
      rw [norm_smul, hx', Real.norm_eq_abs, abs_of_pos hr, norm_zero, mul_one] at this
      exact hr.ne' this
    · refine Set.disjoint_left.1 (hdisj _ hK' z hz hzz) (Metric.mem_closedBall_self hr.le) ?_
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hx',
        Real.norm_eq_abs, abs_of_pos hr, mul_one]
  have hD1 : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1,
      (0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro y hy
    rwa [zero_add, one_smul]
  have hDz : ∀ z ∈ Zs, ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1,
      z + r • y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 := by
    intro z hz y hy
    refine Metric.ball_subset_closedBall (hZ z hz ?_)
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr]
    nlinarith
  have hres : ∀ (a : EuclideanSpace ℝ (Fin m)) (s : ℝ)
      (h : MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m)
        (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ)
      (x : TopCat.of (EU.{u} m))
      (hx : x ∈ (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m))))
      (h' : MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m) {x}ᶜ),
      relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (EU.{u} m))) (compl_mapsTo hx) m (relativeHomologyMap integerCoefficients (aff a s) h m g) =
        relativeHomologyMap integerCoefficients (aff a s) h' m g := by
    intro a s h x hx h'
    rw [← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients (aff a s) (𝟙 _) h (compl_mapsTo hx)
      (mapsTo_comp h (compl_mapsTo hx)) m]
    exact congrArg (fun φ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m ⟶
      relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) {x}ᶜ m => φ g) (relativeHomologyMap_eq_of_eq integerCoefficients (Category.comp_id _) _ m)
  have hzero : ∀ (a : EuclideanSpace ℝ (Fin m)) (s : ℝ) (x : TopCat.of (EU.{u} m))
      (h' : MapsTo (aff a s) Set.univ {x}ᶜ) (h'' : MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m) {x}ᶜ),
      relativeHomologyMap integerCoefficients (aff a s) h'' m g = 0 := by
    intro a s x h' h''
    rw [relativeHomologyMap_eq_of_eq integerCoefficients (Category.id_comp (aff a s)).symm h'' m,
      relativeHomologyMap_comp integerCoefficients (𝟙 _) (aff a s) (Set.mapsTo_univ _ _) h' _ m, ModuleCat.comp_apply,
      (ModuleCat.isZero_iff_subsingleton.1 (hUniv _ m)).elim
        (relativeHomologyMap integerCoefficients (𝟙 (TopCat.of (ULift.{u} (Disk m)))) (Set.mapsTo_univ _ _) m g) 0, map_zero]
  have hhom : ∀ (x : TopCat.of (EU.{u} m))
      (hx : x ∈ (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m))))
      (h0' : MapsTo (aff 0 1) (ULift.down ⁻¹' diskSphere m) {x}ᶜ)
      (h1' : MapsTo (aff x.down r) (ULift.down ⁻¹' diskSphere m) {x}ᶜ),
      relativeHomologyMap integerCoefficients (aff 0 1) h0' m g = relativeHomologyMap integerCoefficients (aff x.down r) h1' m g := by
    intro x hx h0' h1'
    have hx1 : ‖x.down‖ < 1 := hZball _ hx
    let Hh : ContinuousMap.Homotopy (aff 0 1).hom (aff x.down r).hom :=
      ContinuousMap.Homotopy.mk
        ⟨fun q : unitInterval × ULift.{u} (Disk m) => ULift.up
          ((1 - (q.1 : ℝ)) • ((0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • q.2.down.1) +
            (q.1 : ℝ) • (x.down + r • q.2.down.1)), by fun_prop⟩
        (fun y => by simp [aff])
        (fun y => by simp [aff])
    refine congrArg (fun φ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk m))) (ULift.down ⁻¹' diskSphere m) m ⟶
      relativeHomology integerCoefficients (TopCat.of (EU.{u} m)) {x}ᶜ m => φ g)
      (relativeHomologyMap_eq_of_homotopy (aff 0 1) (aff x.down r) h0' h1' Hh ?_ m)
    intro t y hy heq
    have hy' : ‖y.down.1‖ = 1 := by simpa [diskSphere] using hy
    have heq' : (1 - (t : ℝ)) • ((0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • y.down.1) +
        (t : ℝ) • (x.down + r • y.down.1) = x.down := congrArg ULift.down heq
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    generalize y.down.1 = v at hy' heq'
    generalize (t : ℝ) = τ at ht0 ht1 heq'
    have hv : (1 - τ + τ * r) • v = (1 - τ) • x.down := by
      rw [← sub_eq_zero] at heq' ⊢
      rw [← heq']
      simp only [zero_add, one_smul, smul_add, add_smul, smul_smul, sub_smul]
      abel
    have hn := congrArg norm hv
    rw [norm_smul, norm_smul, hy', Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by nlinarith),
      abs_of_nonneg (by linarith), mul_one] at hn
    have hxn : 0 ≤ ‖x.down‖ := norm_nonneg _
    by_cases htt : τ ≤ 1 / 2
    · nlinarith
    · nlinarith
  let cls : EuclideanSpace ℝ (Fin m) → relativeHomology integerCoefficients (TopCat.of (EU.{u} m))
      (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ m :=
    fun z => if hz : z ∈ Zs then relativeHomologyMap integerCoefficients (aff z r) (hSz z hz) m g else 0
  have hM : relativeHomologyMap integerCoefficients (aff 0 1) hS1 m g = ∑ z ∈ Zs, cls z := by
    refine sub_eq_zero.1 (hpt Zs _ fun x hx => ?_)
    have hx0 : x.down ∈ Zs := hx
    have hmiss : ∀ (a : EuclideanSpace ℝ (Fin m)) (s : ℝ)
        (h : MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m)
          (ULift.down ⁻¹' (Zs : Set (EuclideanSpace ℝ (Fin m))) : Set (TopCat.of (EU.{u} m)))ᶜ),
        MapsTo (aff a s) (ULift.down ⁻¹' diskSphere m) {x}ᶜ :=
      fun a s h y hy (hyx : aff a s y = x) => h hy (hyx ▸ hx)
    rw [map_sub, map_sum, Finset.sum_eq_single_of_mem x.down hx0 ?_]
    · simp only [cls, dite_eq_left hx0]
      rw [hres 0 1 hS1 x hx (hmiss 0 1 hS1), hres x.down r (hSz x.down hx0) x hx
        (hmiss _ _ (hSz x.down hx0)), hhom x hx (hmiss 0 1 hS1) (hmiss _ _ (hSz x.down hx0)), sub_self]
    · intro z hz hzx
      simp only [cls, dite_eq_left hz]
      rw [hres z r (hSz z hz) x hx (hmiss _ _ (hSz z hz))]
      refine hzero z r x ?_ _
      intro y _ (hyx : aff z r y = x)
      have hyD := y.down.2
      rw [Metric.mem_closedBall, dist_zero_right] at hyD
      refine Set.disjoint_left.1 (hdisj z hz x.down hx0 hzx)
        (show z + r • y.down.1 ∈ Metric.closedBall z r from ?_) ?_
      · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr]
        nlinarith
      · rw [← congrArg ULift.down hyx]
        exact Metric.mem_closedBall_self hr.le
  have hLHS : discClass B (B \ C) F g =
      discClass B (B \ C) (fun y => F ((0 : EuclideanSpace ℝ (Fin m)) + (1 : ℝ) • y)) g := by
    congr 1
    funext y
    rw [zero_add, one_smul]
  rw [hLHS, hL 0 1 hD1 hS1, hM, map_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  simp only [cls, dite_eq_left hz]
  rw [hL z r (hDz z hz) (hSz z hz)]

def annulus (μ : ℕ) : Set (EuclideanSpace ℝ (Fin μ)) := {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}

def annulusBdry (μ : ℕ) : Set (EuclideanSpace ℝ (Fin μ)) := {z | ‖z‖ = 1 ∨ ‖z‖ = 2}

variable {X : Type u} [TopologicalSpace X]

open Classical in
def annulusClass (B A : Set X) {μ : ℕ} (F : EuclideanSpace ℝ (Fin μ) → X)
    (Γ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (annulus μ))) (ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry μ))
      μ) : relativeHomologyPair B A μ :=
  if h : ContinuousOn F (annulus μ) ∧ MapsTo F (annulus μ) B ∧
      MapsTo F (annulusBdry μ ∩ annulus μ) A then
    relativeHomologyMap integerCoefficients (TopCat.ofHom ⟨fun x : ULift.{u} (annulus μ) => (⟨F x.down.1, h.2.1 x.down.2⟩ : ↥B),
        (h.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
          (fun x => x.down.2)).subtype_mk _⟩)
      (fun x hx => h.2.2 ⟨hx, x.down.2⟩) μ Γ
  else 0

theorem inclPair_annulusClass {B A B' A' : Set X} (hB : B ⊆ B') (hA : A ⊆ A') {μ : ℕ}
    (F : EuclideanSpace ℝ (Fin μ) → X) (hF : ContinuousOn F (annulus μ))
    (hFB : MapsTo F (annulus μ) B) (hFA : MapsTo F (annulusBdry μ ∩ annulus μ) A)
    (Γ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (annulus μ))) (ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry μ))
      μ) :
    inclPair hB hA μ (annulusClass B A F Γ) = annulusClass B' A' F Γ := by
  have h : ContinuousOn F (annulus μ) ∧ MapsTo F (annulus μ) B ∧
      MapsTo F (annulusBdry μ ∩ annulus μ) A := ⟨hF, hFB, hFA⟩
  have h' : ContinuousOn F (annulus μ) ∧ MapsTo F (annulus μ) B' ∧
      MapsTo F (annulusBdry μ ∩ annulus μ) A' :=
    ⟨hF, hFB.mono_right hB, hFA.mono_right hA⟩
  have key : ∀ (f : TopCat.of (ULift.{u} (annulus μ)) ⟶ TopCat.of ↥B)
      (hf : MapsTo f (ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry μ)) (Subtype.val ⁻¹' A))
      (hf' : MapsTo (f ≫ inclOfLE (X := TopCat.of X) hB)
        (ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry μ)) (Subtype.val ⁻¹' A')),
      relativeHomologyMap integerCoefficients f hf μ ≫ relativeHomologyMap integerCoefficients (inclOfLE (X := TopCat.of X) hB)
        (mapsTo_inclOfLE_preimage hB hA) μ = relativeHomologyMap integerCoefficients (f ≫ inclOfLE (X := TopCat.of X) hB) hf' μ :=
    fun f hf hf' => (relativeHomologyMap_comp integerCoefficients f _ hf _ hf' μ).symm
  rw [annulusClass, annulusClass, dite_eq_left h, dite_eq_left h', inclPair,
    ← ModuleCat.comp_apply]
  exact CategoryTheory.ConcreteCategory.congr_hom (key _ _ _) Γ

def isAnnulusGen {μ : ℕ}
    (Γ : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (annulus (μ + 1))))
      (ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry (μ + 1))) (μ + 1))
    (gS : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} μ) μ)
    (gD : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (μ + 1)))) (ULift.down ⁻¹' diskSphere (μ + 1)) (μ + 1))
    (s : ℤ) : Prop :=
  (∀ {Y : Type u} [TopologicalSpace Y] (T S W : Set Y)
      (F : EuclideanSpace ℝ (Fin (μ + 1)) → Y),
      ContinuousOn F (annulus (μ + 1)) → MapsTo F (annulus (μ + 1)) W →
      MapsTo F (annulusBdry (μ + 1) ∩ annulus (μ + 1)) S →
      tripleBoundary T S W μ (annulusClass W S F Γ) =
        sphereClass S T (fun z => F ((2 : ℝ) • z)) gS - sphereClass S T F gS) ∧
  ∀ {Y : Type u} [TopologicalSpace Y] (B C : Set Y) (F : EuclideanSpace ℝ (Fin (μ + 1)) → Y)
    (z₀ : EuclideanSpace ℝ (Fin (μ + 1))) (r : ℝ), 0 < r →
    Metric.closedBall z₀ r ⊆ {z | 1 < ‖z‖ ∧ ‖z‖ < 2} →
    ContinuousOn F (annulus (μ + 1)) → MapsTo F (annulus (μ + 1)) B →
    (∀ y ∈ annulus (μ + 1), F y ∈ C → y = z₀) →
    annulusClass B (B \ C) F Γ = s • discClass B (B \ C) (fun y => F (z₀ + r • y)) gD

theorem exists_annulus_class (μ : ℕ) (hμ : 1 ≤ μ) (gS : SingularPair.singularHomology integerCoefficients (Sphere.liftedSphere.{u} μ) μ)
    (hgS : isGen gS)
    (gD : relativeHomology integerCoefficients (TopCat.of (ULift.{u} (Disk (μ + 1)))) (ULift.down ⁻¹' diskSphere (μ + 1)) (μ + 1))
    (hgD : isGen gD) :
    ∃ Γ s, (s = 1 ∨ s = -1) ∧ isAnnulusGen Γ gS gD s := by
  classical
  have HrelMap_congr : ∀ {X₁ Y₁ : TopCat.{u}} {A₁ : Set X₁} {B₁ : Set Y₁} (f g : X₁ ⟶ Y₁)
      (hf : MapsTo f A₁ B₁) (hg : MapsTo g A₁ B₁), f = g → ∀ n,
      relativeHomologyMap integerCoefficients f hf n = relativeHomologyMap integerCoefficients g hg n := by
    intro X₁ Y₁ A₁ B₁ f g hf hg hfg n
    subst hfg
    rfl
  have Hmap_congr : ∀ {X₁ Y₁ : TopCat.{u}} (f g : X₁ ⟶ Y₁), f = g → ∀ n,
      singularHomologyMap integerCoefficients f n = singularHomologyMap integerCoefficients g n := by
    intro X₁ Y₁ f g hfg n
    subst hfg
    rfl
  have hnorm1 : ∀ x : EuclideanSpace ℝ (Fin (μ + 1)), x ∈ unitSphere μ → ‖x‖ = 1 := by
    intro x hx
    simpa using hx
  have hsph_ann : ∀ x : EuclideanSpace ℝ (Fin (μ + 1)), x ∈ unitSphere μ → x ∈ annulus (μ + 1) := by
    intro x hx
    change 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2
    rw [hnorm1 x hx]
    norm_num
  have hsph2_ann : ∀ x : EuclideanSpace ℝ (Fin (μ + 1)), x ∈ unitSphere μ →
      (2 : ℝ) • x ∈ annulus (μ + 1) := by
    intro x hx
    change 1 ≤ ‖(2 : ℝ) • x‖ ∧ ‖(2 : ℝ) • x‖ ≤ 2
    rw [norm_smul, hnorm1 x hx]
    norm_num
  have hsph_bd : ∀ x : EuclideanSpace ℝ (Fin (μ + 1)), x ∈ unitSphere μ → x ∈ annulusBdry (μ + 1) := by
    intro x hx
    exact Or.inl (hnorm1 x hx)
  have hsph2_bd : ∀ x : EuclideanSpace ℝ (Fin (μ + 1)), x ∈ unitSphere μ →
      (2 : ℝ) • x ∈ annulusBdry (μ + 1) := by
    intro x hx
    right
    rw [norm_smul, hnorm1 x hx]
    norm_num
  let 𝕏 : TopCat.{u} := TopCat.of (ULift.{u} ↥(annulus (μ + 1)))
  let bd : Set 𝕏 := ULift.down ⁻¹' (Subtype.val ⁻¹' annulusBdry (μ + 1))
  let out : Sphere.liftedSphere.{u} μ ⟶ TopCat.of ↥bd :=
    TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere μ) =>
      ⟨ULift.up ⟨(2 : ℝ) • x.down.1, hsph2_ann _ x.down.2⟩, hsph2_bd _ x.down.2⟩, by fun_prop⟩
  let inn : Sphere.liftedSphere.{u} μ ⟶ TopCat.of ↥bd :=
    TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere μ) =>
      ⟨ULift.up ⟨x.down.1, hsph_ann _ x.down.2⟩, hsph_bd _ x.down.2⟩, by fun_prop⟩
  have hann_t : ∀ (t : unitInterval) (x : EuclideanSpace ℝ (Fin (μ + 1))), x ∈ unitSphere μ →
      (1 + (t : ℝ)) • x ∈ annulus (μ + 1) := by
    intro t x hx
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    change 1 ≤ ‖(1 + (t : ℝ)) • x‖ ∧ ‖(1 + (t : ℝ)) • x‖ ≤ 2
    rw [norm_smul, hnorm1 x hx, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    constructor <;> linarith
  let Hh : TopCat.Homotopy (inn ≫ SingularPair.incl 𝕏 bd) (out ≫ SingularPair.incl 𝕏 bd) :=
    { toFun := fun p => ULift.up ⟨(1 + (p.1 : ℝ)) • (p.2 : ULift.{u} (unitSphere μ)).down.1,
        hann_t p.1 _ (p.2 : ULift.{u} (unitSphere μ)).down.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun x => by
        apply ULift.ext
        apply Subtype.ext
        simp
        rfl
      map_one_left := fun x => by
        apply ULift.ext
        apply Subtype.ext
        norm_num
        rfl }
  have hHh : singularHomologyMap integerCoefficients (inn ≫ SingularPair.incl 𝕏 bd) μ = singularHomologyMap integerCoefficients (out ≫ SingularPair.incl 𝕏 bd) μ := by
    rw [singularHomologyMap_eq_homologyMap, singularHomologyMap_eq_homologyMap]
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor Hh integerCoefficients μ
  have hA : ∃ Γ : relativeHomology integerCoefficients 𝕏 bd (μ + 1), δ integerCoefficients 𝕏 bd μ Γ = singularHomologyMap integerCoefficients out μ gS - singularHomologyMap integerCoefficients inn μ gS := by
    have hex := (ShortComplex.moduleCat_exact_iff _).1 (les_exact₁ integerCoefficients 𝕏 bd μ)
    apply hex
    change inclMap integerCoefficients 𝕏 bd μ (singularHomologyMap integerCoefficients out μ gS - singularHomologyMap integerCoefficients inn μ gS) = 0
    rw [map_sub, inclMap_eq_singularHomologyMap, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← singularHomologyMap_comp,
      ← singularHomologyMap_comp, hHh, sub_self]
  obtain ⟨k, hk⟩ := isGen_boundaryGen hμ hgD gS
  obtain ⟨m, hm⟩ := hgS (boundaryGen gD)
  have hk1 : k = 1 ∨ k = -1 := by
    have hkm : (k * m) • gS = gS := by
      rw [mul_smul, ← hm, ← hk]
    let e := Sphere.singularHomologyTopLiftedSphereIso integerCoefficients μ (by omega)
    have hne : (e.hom gS).down ≠ 0 := by
      intro h0
      obtain ⟨j, hj⟩ := hgS (e.inv (ULift.up 1))
      have h1 : e.hom (e.inv (ULift.up 1)) = ULift.up 1 := by
        rw [← ModuleCat.comp_apply, e.inv_hom_id]
        rfl
      rw [hj, map_zsmul] at h1
      have h2 := congrArg ULift.down h1
      rw [ULift.smul_down, h0, smul_zero] at h2
      exact absurd h2 (by norm_num)
    have h3 := congrArg (fun v => (e.hom v).down) hkm
    simp only [map_zsmul, ULift.smul_down, smul_eq_mul] at h3
    have h4 : k * m = 1 := by
      have := mul_right_cancel₀ hne (h3.trans (one_mul _).symm)
      exact this
    exact Int.eq_one_or_neg_one_of_mul_eq_one h4
  obtain ⟨Γ, hΓ⟩ := hA
  have δnat : ∀ {X₁ Y₁ : TopCat.{u}} {A₁ : Set X₁} {B₁ : Set Y₁} (f : X₁ ⟶ Y₁)
      (hf : MapsTo f A₁ B₁) (x : relativeHomology integerCoefficients X₁ A₁ (μ + 1)),
      δ integerCoefficients Y₁ B₁ μ (relativeHomologyMap integerCoefficients f hf (μ + 1) x) = singularHomologyMap integerCoefficients (restr f hf) μ (δ integerCoefficients X₁ A₁ μ x) := by
    intro X₁ Y₁ A₁ B₁ f hf x
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, δ_natural]
  let B2 : Set (EU.{u} (μ + 1)) := ULift.down ⁻¹' Metric.closedBall 0 2
  let KS : Set (EU.{u} (μ + 1)) := {x | ‖x.down‖ ≤ 1 ∨ ‖x.down‖ = 2}
  have hB2contr : ContractibleSpace ↥B2 := by
    have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin (μ + 1))) 2).contractibleSpace
      ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
    exact (Homeomorph.subtype (p := fun x => x ∈ B2)
      (q := fun y => y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (μ + 1))) 2)
      Homeomorph.ulift (fun x => Iff.rfl)).contractibleSpace
  have hδinj : ∀ a b : relativeHomologyPair B2 KS (μ + 1),
      δ integerCoefficients (TopCat.of ↥B2) (Subtype.val ⁻¹' KS) μ a =
        δ integerCoefficients (TopCat.of ↥B2) (Subtype.val ⁻¹' KS) μ b → a = b := by
    intro a b hab
    have hex := (ShortComplex.moduleCat_exact_iff _).1
      (les_exact₃ integerCoefficients (TopCat.of ↥B2) (Subtype.val ⁻¹' KS) μ)
    obtain ⟨c, hc⟩ := hex (a - b) (by
      change δ integerCoefficients (TopCat.of ↥B2) (Subtype.val ⁻¹' KS) μ (a - b) = 0
      rw [map_sub, hab, sub_self])
    have hz := isZero_of_contractible integerCoefficients ↥B2 (μ + 1) (by omega)
    have hc0 : c = 0 := by
      have h : (𝟙 (singularHomology integerCoefficients (TopCat.of ↥B2) (μ + 1))) = 0 := hz.eq_of_src _ _
      have h' := congrArg
        (fun f : singularHomology integerCoefficients (TopCat.of ↥B2) (μ + 1) ⟶ singularHomology integerCoefficients (TopCat.of ↥B2) (μ + 1) => f c) h
      simpa using h'
    rw [hc0, map_zero] at hc
    exact sub_eq_zero.1 hc.symm
  have hann_norm : ∀ z ∈ annulus (μ + 1), 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2 := fun z hz => hz
  have hc1 : ContinuousOn (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1))
        (annulus (μ + 1)) ∧
      MapsTo (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1)) (annulus (μ + 1)) B2 ∧
      MapsTo (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1))
        (annulusBdry (μ + 1) ∩ annulus (μ + 1)) KS := by
    refine ⟨continuous_uliftUp.continuousOn, fun z hz => ?_, fun z hz => ?_⟩
    · change z ∈ Metric.closedBall 0 2
      rw [mem_closedBall_zero_iff]
      exact (hann_norm z hz).2
    · rcases hz.1 with h | h
      · exact Or.inl h.le
      · exact Or.inr h
  have hd1 : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) (Metric.closedBall 0 1) ∧
      MapsTo (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) (Metric.closedBall 0 1) B2 ∧
      MapsTo (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
        (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) (Metric.sphere 0 1) KS := by
    refine ⟨Continuous.continuousOn (by fun_prop), fun y hy => ?_, fun y hy => ?_⟩
    · change (2 : ℝ) • y ∈ Metric.closedBall 0 2
      rw [mem_closedBall_zero_iff] at hy ⊢
      rw [norm_smul]
      norm_num
      linarith
    · right
      change ‖(2 : ℝ) • y‖ = 2
      rw [mem_sphere_zero_iff_norm] at hy
      rw [norm_smul, hy]
      norm_num
  have hclaim : annulusClass B2 KS ULift.up Γ =
      k • discClass B2 KS (fun y => (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) gD := by
    obtain ⟨φ, hφ, hφeq, hφdef⟩ : ∃ (φ : 𝕏 ⟶ TopCat.of ↥B2)
        (hφ : MapsTo φ bd (Subtype.val ⁻¹' KS)),
        annulusClass B2 KS ULift.up Γ = relativeHomologyMap integerCoefficients φ hφ (μ + 1) Γ ∧
          ∀ x, (φ x).1 = ULift.up x.down.1 :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (annulus (μ + 1)) => ⟨ULift.up x.down.1, hc1.2.1 x.down.2⟩,
          (hc1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        fun x hx => hc1.2.2 ⟨hx, x.down.2⟩, by rw [annulusClass, dite_eq_left hc1], fun x => rfl⟩
    obtain ⟨ψ, hψ, hψeq, hψdef⟩ : ∃ (ψ : TopCat.of (ULift.{u} (Disk (μ + 1))) ⟶ TopCat.of ↥B2)
        (hψ : MapsTo ψ (ULift.down ⁻¹' diskSphere (μ + 1)) (Subtype.val ⁻¹' KS)),
        discClass B2 KS (fun y => (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) gD =
          relativeHomologyMap integerCoefficients ψ hψ (μ + 1) gD ∧ ∀ y, (ψ y).1 = ULift.up ((2 : ℝ) • y.down.1) :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (Disk (μ + 1)) =>
          ⟨(ULift.up ((2 : ℝ) • x.down.1) : EU.{u} (μ + 1)), hd1.2.1 x.down.2⟩,
          (hd1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        fun x hx => hd1.2.2 hx, by rw [discClass, dite_eq_left hd1]; try rfl, fun y => rfl⟩
    rw [hφeq, hψeq]
    apply hδinj
    rw [map_zsmul, δnat, δnat, hΓ, map_sub]
    have hin0 : singularHomologyMap integerCoefficients (restr φ hφ) μ (singularHomologyMap integerCoefficients inn μ gS) = 0 := by
      have hD1 : ContractibleSpace (ULift.{u} (Disk (μ + 1))) := by
        have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin (μ + 1))) 1).contractibleSpace
          ⟨0, Metric.mem_closedBall_self (by norm_num)⟩
        exact (Homeomorph.ulift).contractibleSpace
      have hzD := isZero_of_contractible integerCoefficients (ULift.{u} (Disk (μ + 1))) μ (by omega)
      let ι₁ : Sphere.liftedSphere.{u} μ ⟶ TopCat.of (ULift.{u} (Disk (μ + 1))) :=
        TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere μ) => ULift.up ⟨x.down.1, by
          rw [mem_closedBall_zero_iff, hnorm1 _ x.down.2]⟩, by fun_prop⟩
      let ι₂ : TopCat.of (ULift.{u} (Disk (μ + 1))) ⟶
          TopCat.of ↥(Subtype.val ⁻¹' KS : Set ↥B2) :=
        TopCat.ofHom ⟨fun y => ⟨⟨ULift.up y.down.1, by
          change y.down.1 ∈ Metric.closedBall 0 2
          have := y.down.2
          rw [mem_closedBall_zero_iff] at this ⊢
          linarith⟩, Or.inl (by
          have := y.down.2
          rw [mem_closedBall_zero_iff] at this
          exact this)⟩, by fun_prop⟩
      have hfac : inn ≫ restr φ hφ = ι₁ ≫ ι₂ := by
        refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
        apply Subtype.ext
        apply Subtype.ext
        exact hφdef _
      rw [← ModuleCat.comp_apply, ← singularHomologyMap_comp, hfac, singularHomologyMap_comp,
        hzD.eq_of_tgt (singularHomologyMap integerCoefficients ι₁ μ) 0, Limits.zero_comp]
      rfl
    let β : TopCat.of ↥(ULift.down ⁻¹' diskSphere (μ + 1) : Set (ULift.{u} (Disk (μ + 1)))) ⟶
        Sphere.liftedSphere.{u} μ :=
      TopCat.ofHom ⟨fun x => (ULift.up ⟨x.1.down.1, x.2⟩ : ULift.{u} (unitSphere μ)),
        continuous_uliftUp.comp ((continuous_subtype_val.comp
          (continuous_uliftDown.comp continuous_subtype_val)).subtype_mk _)⟩
    have hbG : boundaryGen gD = singularHomologyMap integerCoefficients β μ
        (δ integerCoefficients (TopCat.of (ULift.{u} (Disk (μ + 1)))) (ULift.down ⁻¹' diskSphere (μ + 1)) μ gD) := by
      rw [boundaryGen, ModuleCat.comp_apply]
    have hmap : restr ψ hψ = β ≫ out ≫ restr φ hφ := by
      refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
      apply Subtype.ext
      apply Subtype.ext
      exact (hψdef x.1).trans (hφdef (out (β x)).1).symm
    have hout : singularHomologyMap integerCoefficients (restr ψ hψ) μ (δ integerCoefficients _ _ μ gD) =
        singularHomologyMap integerCoefficients (restr φ hφ) μ (singularHomologyMap integerCoefficients out μ (boundaryGen gD)) := by
      rw [hbG, Hmap_congr (restr ψ hψ) (β ≫ out ≫ restr φ hφ) hmap μ, singularHomologyMap_comp, singularHomologyMap_comp,
        ModuleCat.comp_apply, ModuleCat.comp_apply]
    rw [hin0, sub_zero, hout, hk, map_zsmul, map_zsmul]
  refine ⟨Γ, k, hk1, ?_, ?_⟩
  · intro Y _ T S W F hFc hFW hFS
    have hc : ContinuousOn F (annulus (μ + 1)) ∧ MapsTo F (annulus (μ + 1)) W ∧
        MapsTo F (annulusBdry (μ + 1) ∩ annulus (μ + 1)) S := ⟨hFc, hFW, hFS⟩
    obtain ⟨φ, hφ, hφeq, hφdef⟩ : ∃ (φ : 𝕏 ⟶ TopCat.of ↥W)
        (hφ : MapsTo φ bd (Subtype.val ⁻¹' S)),
        annulusClass W S F Γ = relativeHomologyMap integerCoefficients φ hφ (μ + 1) Γ ∧ ∀ x, (φ x).1 = F x.down.1 :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (annulus (μ + 1)) => ⟨F x.down.1, hc.2.1 x.down.2⟩,
          (hc.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        fun x hx => hc.2.2 ⟨hx, x.down.2⟩, by rw [annulusClass, dite_eq_left hc]; try rfl,
        fun x => rfl⟩
    have hs2 : ContinuousOn (fun z => F ((2 : ℝ) • z)) (unitSphere μ) ∧
        MapsTo (fun z => F ((2 : ℝ) • z)) (unitSphere μ) S :=
      ⟨hFc.comp (continuous_const_smul (2 : ℝ)).continuousOn (fun z hz => hsph2_ann z hz),
        fun z hz => hFS ⟨hsph2_bd z hz, hsph2_ann z hz⟩⟩
    have hs1 : ContinuousOn F (unitSphere μ) ∧ MapsTo F (unitSphere μ) S :=
      ⟨hFc.mono (fun z hz => hsph_ann z hz), fun z hz => hFS ⟨hsph_bd z hz, hsph_ann z hz⟩⟩
    obtain ⟨G₂, hG₂eq, hG₂def⟩ : ∃ G₂ : Sphere.liftedSphere.{u} μ ⟶ TopCat.of ↥S,
        sphereClass S T (fun z => F ((2 : ℝ) • z)) gS =
          (singularHomologyMap integerCoefficients G₂ μ ≫ relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) μ) gS ∧
          ∀ x, (G₂ x).1 = F ((2 : ℝ) • x.down.1) :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere μ) => ⟨F ((2 : ℝ) • x.down.1), hs2.2 x.down.2⟩,
          (hs2.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        by rw [sphereClass, dite_eq_left hs2]; try rfl, fun x => rfl⟩
    obtain ⟨G₁, hG₁eq, hG₁def⟩ : ∃ G₁ : Sphere.liftedSphere.{u} μ ⟶ TopCat.of ↥S,
        sphereClass S T F gS =
          (singularHomologyMap integerCoefficients G₁ μ ≫ relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) μ) gS ∧
          ∀ x, (G₁ x).1 = F x.down.1 :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (unitSphere μ) => ⟨F x.down.1, hs1.2 x.down.2⟩,
          (hs1.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        by rw [sphereClass, dite_eq_left hs1]; try rfl, fun x => rfl⟩
    let ρ : TopCat.of ↥(Subtype.val ⁻¹' S : Set ↥W) ⟶ TopCat.of ↥S :=
      TopCat.ofHom ⟨fun x => (⟨x.1.1, x.2⟩ : ↥S),
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    have hρ : tripleBoundary T S W μ = δ integerCoefficients (TopCat.of ↥W) (Subtype.val ⁻¹' S) μ ≫ singularHomologyMap integerCoefficients ρ μ ≫
        relπ integerCoefficients (TopCat.of ↥S) (Subtype.val ⁻¹' T) μ := rfl
    have e2 : singularHomologyMap integerCoefficients ρ μ (singularHomologyMap integerCoefficients (restr φ hφ) μ (singularHomologyMap integerCoefficients out μ gS)) = singularHomologyMap integerCoefficients G₂ μ gS := by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← singularHomologyMap_comp, ← singularHomologyMap_comp,
        Hmap_congr (out ≫ restr φ hφ ≫ ρ) G₂ ?_ μ]
      refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
      apply Subtype.ext
      exact (hφdef _).trans (hG₂def x).symm
    have e1 : singularHomologyMap integerCoefficients ρ μ (singularHomologyMap integerCoefficients (restr φ hφ) μ (singularHomologyMap integerCoefficients inn μ gS)) = singularHomologyMap integerCoefficients G₁ μ gS := by
      rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← singularHomologyMap_comp, ← singularHomologyMap_comp,
        Hmap_congr (inn ≫ restr φ hφ ≫ ρ) G₁ ?_ μ]
      refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
      apply Subtype.ext
      exact (hφdef _).trans (hG₁def x).symm
    rw [hφeq, hG₂eq, hG₁eq, hρ, ModuleCat.comp_apply, ModuleCat.comp_apply, δnat, hΓ, map_sub,
      map_sub, map_sub, e2, e1, ModuleCat.comp_apply, ModuleCat.comp_apply]
  · intro Y _ B C F z₀ r hr hball hFc hFB hC
    have hz₀ : 1 < ‖z₀‖ ∧ ‖z₀‖ < 2 := hball (Metric.mem_closedBall_self hr.le)
    have hdisc_ball : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), y ∈ Metric.closedBall 0 1 →
        z₀ + r • y ∈ Metric.closedBall z₀ r := by
      intro y hy
      rw [mem_closedBall_zero_iff] at hy
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr]
      nlinarith
    have hdisc_ann : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), y ∈ Metric.closedBall 0 1 →
        z₀ + r • y ∈ annulus (μ + 1) := by
      intro y hy
      have h := hball (hdisc_ball y hy)
      exact ⟨h.1.le, h.2.le⟩
    have hbd_ne : ∀ z : EuclideanSpace ℝ (Fin (μ + 1)), z ∈ annulusBdry (μ + 1) → z ≠ z₀ := by
      intro z hz h
      rw [h] at hz
      rcases hz with h1 | h1
      · linarith [hz₀.1]
      · linarith [hz₀.2]
    have hsph_ne : ∀ y : EuclideanSpace ℝ (Fin (μ + 1)), y ∈ Metric.sphere 0 1 →
        z₀ + r • y ≠ z₀ := by
      intro y hy h
      rw [mem_sphere_zero_iff_norm] at hy
      have h2 : r • y = 0 := by
        have := congrArg (fun v => v - z₀) h
        simpa using this
      rw [smul_eq_zero] at h2
      rcases h2 with h2 | h2
      · exact hr.ne' h2
      · rw [h2, norm_zero] at hy
        exact zero_ne_one hy
    let P : Set 𝕏 := {x | x.down.1 ≠ z₀}
    have hbdP : MapsTo (𝟙 𝕏) bd P := fun x hx => hbd_ne _ hx
    let dz : TopCat.of (ULift.{u} (Disk (μ + 1))) ⟶ 𝕏 :=
      TopCat.ofHom ⟨fun y : ULift.{u} (Disk (μ + 1)) =>
        (ULift.up ⟨z₀ + r • y.down.1, hdisc_ann _ y.down.2⟩ : ULift.{u} (annulus (μ + 1))),
        by fun_prop⟩
    have hdzP : MapsTo dz (ULift.down ⁻¹' diskSphere (μ + 1)) P := fun y hy => hsph_ne _ hy
    have hloc : relativeHomologyMap integerCoefficients (𝟙 𝕏) hbdP (μ + 1) Γ = k • relativeHomologyMap integerCoefficients dz hdzP (μ + 1) gD := by
      let Bz : Set (EU.{u} (μ + 1)) := B2 \ {ULift.up z₀}
      have hKSBz : KS ⊆ Bz := by
        intro x hx
        refine ⟨?_, ?_⟩
        · change x.down ∈ Metric.closedBall 0 2
          rw [mem_closedBall_zero_iff]
          rcases hx with h | h <;> linarith
        · intro h
          rw [Set.mem_singleton_iff] at h
          have hx' : ‖z₀‖ ≤ 1 ∨ ‖z₀‖ = 2 := by
            rw [h] at hx
            exact hx
          rcases hx' with h' | h'
          · linarith [hz₀.1]
          · linarith [hz₀.2]
      let φz : 𝕏 ⟶ TopCat.of ↥B2 :=
        TopCat.ofHom ⟨fun x : ULift.{u} (annulus (μ + 1)) =>
          (⟨ULift.up x.down.1, hc1.2.1 x.down.2⟩ : ↥B2), by fun_prop⟩
      have hφzP : MapsTo φz P (Subtype.val ⁻¹' Bz) := fun x hx =>
        ⟨hc1.2.1 x.down.2, fun h => hx (congrArg ULift.down (Set.mem_singleton_iff.1 h))⟩
      have hinj : Function.Injective (relativeHomologyMap integerCoefficients φz hφzP (μ + 1)) := by
        let Zs : Set (TopCat.of ↥B2) := {x | ‖(x.1 : EU.{u} (μ + 1)).down‖ < 1}
        let As : Set (TopCat.of ↥B2) := Subtype.val ⁻¹' Bz
        have hZ : closure Zs ⊆ interior As := by
          have hcl : closure Zs ⊆ {x : ↥B2 | ‖(x.1 : EU.{u} (μ + 1)).down‖ ≤ 1} :=
            closure_minimal (fun x hx => by
                have hx' : ‖(x.1 : EU.{u} (μ + 1)).down‖ < 1 := hx
                exact le_of_lt hx')
              (isClosed_le (by fun_prop) continuous_const)
          have hU : IsOpen {x : ↥B2 | x.1 ≠ ULift.up z₀} :=
            isOpen_ne_fun continuous_subtype_val continuous_const
          refine hcl.trans (Set.Subset.trans ?_ (interior_maximal ?_ hU))
          · intro x hx h
            have hx' : ‖(x.1 : EU.{u} (μ + 1)).down‖ ≤ 1 := hx
            rw [h] at hx'
            linarith [hz₀.1]
          · intro x hx
            exact ⟨x.2, hx⟩
        have hexc := excision_closed integerCoefficients (X := TopCat.of ↥B2) Zs As hZ (μ + 1)
        have hmemZ : ∀ x : ULift.{u} (annulus (μ + 1)),
            (⟨ULift.up x.down.1, hc1.2.1 x.down.2⟩ : ↥B2) ∈ Zsᶜ := by
          intro x hx
          have hx' : ‖x.down.1‖ < 1 := hx
          linarith [(hann_norm _ x.down.2).1]
        let e : 𝕏 ⟶ TopCat.of ↥(Zsᶜ) :=
          TopCat.ofHom ⟨fun x : ULift.{u} (annulus (μ + 1)) =>
            (⟨⟨ULift.up x.down.1, hc1.2.1 x.down.2⟩, hmemZ x⟩ : ↥(Zsᶜ)), by fun_prop⟩
        have hmemA : ∀ y : ↥(Zsᶜ), (y.1.1 : EU.{u} (μ + 1)).down ∈ annulus (μ + 1) := by
          intro y
          have h1 : ¬ ‖(y.1.1 : EU.{u} (μ + 1)).down‖ < 1 := y.2
          have h2 : (y.1.1 : EU.{u} (μ + 1)).down ∈ Metric.closedBall 0 2 := y.1.2
          rw [mem_closedBall_zero_iff] at h2
          exact ⟨not_lt.1 h1, h2⟩
        let e' : TopCat.of ↥(Zsᶜ) ⟶ 𝕏 :=
          TopCat.ofHom ⟨fun y : ↥(Zsᶜ) =>
            (ULift.up ⟨(y.1.1 : EU.{u} (μ + 1)).down, hmemA y⟩ : ULift.{u} (annulus (μ + 1))),
            by fun_prop⟩
        have heP : MapsTo e P (Subtype.val ⁻¹' As) := fun x hx => hφzP hx
        have he'P : MapsTo e' (Subtype.val ⁻¹' As) P := by
          intro y hy h
          apply hy.2
          change y.1.1 = ULift.up z₀
          exact congrArg ULift.up h
        have hee' : e ≫ e' = 𝟙 𝕏 := ConcreteCategory.hom_ext _ _ (fun x => rfl)
        have hfac : φz = e ≫ SingularPair.incl (TopCat.of ↥B2) Zsᶜ :=
          ConcreteCategory.hom_ext _ _ (fun x => rfl)
        have hcomp : MapsTo (e ≫ SingularPair.incl (TopCat.of ↥B2) Zsᶜ) P As :=
          fun x hx => heP hx
        have hcomp' : MapsTo (e ≫ e') P P := fun x hx => he'P (heP hx)
        have hidP : MapsTo (𝟙 𝕏) P P := fun x hx => hx
        intro a b hab
        rw [HrelMap_congr φz _ hφzP hcomp hfac,
          relativeHomologyMap_comp integerCoefficients e (SingularPair.incl (TopCat.of ↥B2) Zsᶜ) heP (mapsTo_incl Zsᶜ As) hcomp,
          ModuleCat.comp_apply, ModuleCat.comp_apply] at hab
        have h1 := (ModuleCat.mono_iff_injective _).1 inferInstance hab
        have h2 := congrArg (relativeHomologyMap integerCoefficients e' he'P (μ + 1)) h1
        rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients e e' heP he'P hcomp',
          HrelMap_congr (e ≫ e') (𝟙 𝕏) hcomp' hidP hee', relativeHomologyMap_id] at h2
        simpa using h2
      have hcBz : ContinuousOn (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1))
            (annulus (μ + 1)) ∧
          MapsTo (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1))
            (annulus (μ + 1)) B2 ∧
          MapsTo (ULift.up : EuclideanSpace ℝ (Fin (μ + 1)) → EU.{u} (μ + 1))
            (annulusBdry (μ + 1) ∩ annulus (μ + 1)) Bz :=
        ⟨hc1.1, hc1.2.1, fun z hz => hKSBz (hc1.2.2 hz)⟩
      have hdBz : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
            (ULift.up (z₀ + r • y) : EU.{u} (μ + 1))) (Metric.closedBall 0 1) ∧
          MapsTo (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
            (ULift.up (z₀ + r • y) : EU.{u} (μ + 1))) (Metric.closedBall 0 1) B2 ∧
          MapsTo (fun y : EuclideanSpace ℝ (Fin (μ + 1)) =>
            (ULift.up (z₀ + r • y) : EU.{u} (μ + 1))) (Metric.sphere 0 1) Bz := by
        refine ⟨Continuous.continuousOn (by fun_prop), fun y hy => ?_, fun y hy => ⟨?_, ?_⟩⟩
        · exact hc1.2.1 (hdisc_ann y hy)
        · exact hc1.2.1 (hdisc_ann y (Metric.sphere_subset_closedBall hy))
        · intro h
          exact hsph_ne y hy (congrArg ULift.down (Set.mem_singleton_iff.1 h))
      have hcomp1 : MapsTo (𝟙 𝕏 ≫ φz) bd (Subtype.val ⁻¹' Bz) := fun x hx => hφzP (hbdP hx)
      have hcomp2 : MapsTo (dz ≫ φz) (ULift.down ⁻¹' diskSphere (μ + 1)) (Subtype.val ⁻¹' Bz) :=
        fun y hy => hφzP (hdzP hy)
      have hL : relativeHomologyMap integerCoefficients φz hφzP (μ + 1) (relativeHomologyMap integerCoefficients (𝟙 𝕏) hbdP (μ + 1) Γ) =
          annulusClass B2 Bz ULift.up Γ := by
        rw [← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients (𝟙 𝕏) φz hbdP hφzP hcomp1, annulusClass,
          dite_eq_left hcBz]
        rfl
      have hR : relativeHomologyMap integerCoefficients φz hφzP (μ + 1) (relativeHomologyMap integerCoefficients dz hdzP (μ + 1) gD) =
          discClass B2 Bz (fun y => (ULift.up (z₀ + r • y) : EU.{u} (μ + 1))) gD := by
        rw [← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients dz φz hdzP hφzP hcomp2, discClass,
          dite_eq_left hdBz]
        rfl
      have hloc2 : discClass B2 Bz (fun y => (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) gD =
          discClass B2 Bz (fun y => (ULift.up (z₀ + r • y) : EU.{u} (μ + 1))) gD := by
        have h := discClass_localize B2 {ULift.up z₀}
          (fun y => (ULift.up ((2 : ℝ) • y) : EU.{u} (μ + 1))) hd1.1 hd1.2.1
          {(1 / 2 : ℝ) • z₀} (r := r / 2) (by positivity) ?_ ?_ ?_ gD
        · rw [Finset.sum_singleton] at h
          refine h.trans ?_
          congr 1
          funext y
          congr 1
          rw [smul_add, smul_smul, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
            show (2 : ℝ) * (r / 2) = r by ring, one_smul]
        · intro z hz w hw
          rw [Finset.mem_singleton] at hz
          subst hz
          have h2w : (2 : ℝ) • w ∈ Metric.closedBall z₀ r := by
            rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
            have : (2 : ℝ) • w - z₀ = (2 : ℝ) • (w - (1 / 2 : ℝ) • z₀) := by
              rw [smul_sub, smul_smul]
              norm_num
            rw [this, norm_smul]
            norm_num
            linarith
          have h := hball h2w
          have h' : ‖(2 : ℝ) • w‖ < 2 := h.2
          rw [norm_smul] at h'
          rw [mem_ball_zero_iff]
          norm_num at h'
          linarith
        · intro z hz z' hz' hne
          rw [Finset.mem_singleton] at hz hz'
          exact absurd (hz.trans hz'.symm) hne
        · intro y _ hyC
          rw [Finset.mem_singleton]
          have h2 : (2 : ℝ) • y = z₀ := congrArg ULift.down (Set.mem_singleton_iff.1 hyC)
          rw [← h2, smul_smul]
          norm_num
      apply hinj
      rw [map_zsmul, hL, hR, ← hloc2,
        ← inclPair_annulusClass (subset_refl B2) hKSBz ULift.up hc1.1 hc1.2.1 hc1.2.2 Γ, hclaim,
        map_zsmul, inclPair_discClass (subset_refl B2) hKSBz _ hd1.1 hd1.2.1 hd1.2.2 gD]
    have hcA : ContinuousOn F (annulus (μ + 1)) ∧ MapsTo F (annulus (μ + 1)) B ∧
        MapsTo F (annulusBdry (μ + 1) ∩ annulus (μ + 1)) (B \ C) :=
      ⟨hFc, hFB, fun z hz => ⟨hFB hz.2, fun hzC => hbd_ne z hz.1 (hC z hz.2 hzC)⟩⟩
    have hdA : ContinuousOn (fun y => F (z₀ + r • y)) (Metric.closedBall 0 1) ∧
        MapsTo (fun y => F (z₀ + r • y)) (Metric.closedBall 0 1) B ∧
        MapsTo (fun y => F (z₀ + r • y)) (Metric.sphere 0 1) (B \ C) := by
      refine ⟨hFc.comp (Continuous.continuousOn (by fun_prop)) (fun y hy => hdisc_ann y hy),
        fun y hy => hFB (hdisc_ann y hy), fun y hy => ⟨hFB (hdisc_ann y
          (Metric.sphere_subset_closedBall hy)), fun hyC => hsph_ne y hy
            (hC _ (hdisc_ann y (Metric.sphere_subset_closedBall hy)) hyC)⟩⟩
    obtain ⟨φ, hφ, hφeq, hφdef⟩ : ∃ (φ : 𝕏 ⟶ TopCat.of ↥B)
        (hφ : MapsTo φ bd (Subtype.val ⁻¹' (B \ C))),
        annulusClass B (B \ C) F Γ = relativeHomologyMap integerCoefficients φ hφ (μ + 1) Γ ∧ ∀ x, (φ x).1 = F x.down.1 :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (annulus (μ + 1)) => ⟨F x.down.1, hcA.2.1 x.down.2⟩,
          (hcA.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        fun x hx => hcA.2.2 ⟨hx, x.down.2⟩, by rw [annulusClass, dite_eq_left hcA]; try rfl,
        fun x => rfl⟩
    obtain ⟨ψ, hψ, hψeq, hψdef⟩ : ∃ (ψ : TopCat.of (ULift.{u} (Disk (μ + 1))) ⟶ TopCat.of ↥B)
        (hψ : MapsTo ψ (ULift.down ⁻¹' diskSphere (μ + 1)) (Subtype.val ⁻¹' (B \ C))),
        discClass B (B \ C) (fun y => F (z₀ + r • y)) gD = relativeHomologyMap integerCoefficients ψ hψ (μ + 1) gD ∧
          ∀ y, (ψ y).1 = F (z₀ + r • y.down.1) :=
      ⟨TopCat.ofHom ⟨fun x : ULift.{u} (Disk (μ + 1)) => ⟨F (z₀ + r • x.down.1), hdA.2.1 x.down.2⟩,
          (hdA.1.comp_continuous (continuous_subtype_val.comp continuous_uliftDown)
            (fun x => x.down.2)).subtype_mk _⟩,
        fun x hx => hdA.2.2 hx, by rw [discClass, dite_eq_left hdA]; try rfl, fun y => rfl⟩
    have hφP : MapsTo φ P (Subtype.val ⁻¹' (B \ C)) := by
      intro x hx
      refine ⟨(φ x).2, fun hxC => hx ?_⟩
      have := hφdef x
      rw [← this] at *
      exact hC _ x.down.2 (by rw [← hφdef x]; exact hxC)
    have hcomp1 : MapsTo (𝟙 𝕏 ≫ φ) bd (Subtype.val ⁻¹' (B \ C)) := fun x hx => hφP (hbdP hx)
    have hcomp2 : MapsTo (dz ≫ φ) (ULift.down ⁻¹' diskSphere (μ + 1)) (Subtype.val ⁻¹' (B \ C)) :=
      fun y hy => hφP (hdzP hy)
    rw [hφeq, hψeq, HrelMap_congr φ (𝟙 𝕏 ≫ φ) hφ hcomp1 (Category.id_comp φ).symm,
      relativeHomologyMap_comp integerCoefficients (𝟙 𝕏) φ hbdP hφP hcomp1, ModuleCat.comp_apply, hloc,
      map_zsmul, ← ModuleCat.comp_apply, ← relativeHomologyMap_comp integerCoefficients dz φ hdzP hφP hcomp2,
      HrelMap_congr (dz ≫ φ) ψ hcomp2 hψ ?_]
    refine ConcreteCategory.hom_ext _ _ (fun y => ?_)
    apply Subtype.ext
    exact (hφdef _).trans (hψdef y).symm

end Handle

end

end DifferentialGeometry.Topology
