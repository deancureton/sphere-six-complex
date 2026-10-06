module

public import DifferentialGeometry.Topology.Homology.MayerVietoris

@[expose] public section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial
noncomputable section
universe u
namespace DifferentialGeometry.Homology

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)
  (X : TopCat.{u}) (s t : Set X)

private theorem mv_twoSetFamily_open (hs : IsOpen s) (ht : IsOpen t) :
    ∀ b, IsOpen (twoSetFamily X s t b) := by
  intro b
  cases b
  · exact ht
  · exact hs

private theorem mv_twoSetFamily_cover (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) :
    ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
  intro x
  rcases hcover x with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

private theorem homology_map_comp_apply
    {K L M : ChainComplex (ModuleCat.{u} k) ℕ} (f : K ⟶ L) (g : L ⟶ M)
    (n : ℕ) (a : K.homology n) :
    HomologicalComplex.homologyMap g n (HomologicalComplex.homologyMap f n a) =
      HomologicalComplex.homologyMap (f ≫ g) n a :=
  congrArg (fun h : K.homology n ⟶ M.homology n => h a)
    (HomologicalComplex.homologyMap_comp f g n).symm

private def homologyBiprodEquiv
    (K L : ChainComplex (ModuleCat.{u} k) ℕ) (n : ℕ) :
    (K ⊞ L).homology n ≃ (K.homology n × L.homology n) where
  toFun v := (HomologicalComplex.homologyMap (biprod.fst : K ⊞ L ⟶ K) n v,
    HomologicalComplex.homologyMap (biprod.snd : K ⊞ L ⟶ L) n v)
  invFun p := HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) n p.1 +
    HomologicalComplex.homologyMap (biprod.inr : L ⟶ K ⊞ L) n p.2
  left_inv v := by
    have h := congrArg (fun f : K ⊞ L ⟶ K ⊞ L => HomologicalComplex.homologyMap f n)
      (biprod.total (X := K) (Y := L))
    rw [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at h
    exact congrArg (fun f : (K ⊞ L).homology n ⟶ (K ⊞ L).homology n => f v) h
  right_inv p := by
    apply Prod.ext
    · dsimp
      rw [map_add, homology_map_comp_apply, homology_map_comp_apply,
        biprod.inl_fst, biprod.inr_fst, HomologicalComplex.homologyMap_id,
        HomologicalComplex.homologyMap_zero]
      exact add_zero _
    · dsimp
      rw [map_add, homology_map_comp_apply, homology_map_comp_apply,
        biprod.inl_snd, biprod.inr_snd, HomologicalComplex.homologyMap_id,
        HomologicalComplex.homologyMap_zero]
      exact zero_add _

def singularMayerVietorisDifferenceMap (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of (s ∩ t : Set X))).chainComplex R).homology n →ₗ[k]
      (((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).homology n ×
        ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).homology n) :=
  (HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map
    (subspaceInclusion X (show s ∩ t ⊆ s from Set.inter_subset_left))) R) n).hom.prod
    (-(HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map
      (subspaceInclusion X (show s ∩ t ⊆ t from Set.inter_subset_right))) R) n).hom)

def singularMayerVietorisSumMap (n : ℕ) :
    (((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).homology n ×
      ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).homology n) →ₗ[k]
      ((TopCat.toSSet.obj X).chainComplex R).homology n :=
  (HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) R) n).hom.coprod
    (HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map
      (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X)))) R) n).hom

private theorem homologyBiprodEquiv_difference (n : ℕ)
    (z : ((subspaceSmallShortComplex X s t R).X₁.homology n)) :
    homologyBiprodEquiv _ _ n
        (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).f n z) =
      singularMayerVietorisDifferenceMap R X s t n z := by
  apply Prod.ext
  · dsimp only [homologyBiprodEquiv, Equiv.coe_fn_mk]
    rw [homology_map_comp_apply]
    dsimp only [subspaceSmallShortComplex, DifferentialGeometry.ShortComplex.pushoutShortComplex]
    rw [biprod.lift_fst]
    rfl
  · dsimp only [homologyBiprodEquiv, Equiv.coe_fn_mk]
    rw [homology_map_comp_apply]
    dsimp only [subspaceSmallShortComplex, DifferentialGeometry.ShortComplex.pushoutShortComplex]
    rw [biprod.lift_snd, HomologicalComplex.homologyMap_neg]
    rfl

private theorem small_homology_sum (n : ℕ)
    (p : (((TopCat.toSSet.obj (TopCat.of s)).chainComplex R).homology n ×
      ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R).homology n)) :
    HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) n
      (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g n
        ((homologyBiprodEquiv _ _ n).symm p)) =
      singularMayerVietorisSumMap R X s t n p := by
  dsimp only [homologyBiprodEquiv, Equiv.symm, Equiv.coe_fn_mk,
    subspaceSmallShortComplex, DifferentialGeometry.ShortComplex.pushoutShortComplex]
  rw [map_add, homology_map_comp_apply, homology_map_comp_apply,
    biprod.inl_desc, biprod.inr_desc, map_add, homology_map_comp_apply,
    homology_map_comp_apply]
  have hf : SSet.chainComplexMap (firstSubspaceToSmall X s t) R ≫
      smallChainMap X (twoSetFamily X s t) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, X)))) R := by
    change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ = _
    rw [← Functor.map_comp, firstSubspaceToSmall_ι]
  have hg : SSet.chainComplexMap (secondSubspaceToSmall X s t) R ≫
      smallChainMap X (twoSetFamily X s t) R =
      SSet.chainComplexMap (TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(t, X)))) R := by
    change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ = _
    rw [← Functor.map_comp, secondSubspaceToSmall_ι]
  rw [hf, hg]
  rfl

theorem singularMayerVietoris_exact_sum
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    Function.Exact (singularMayerVietorisDifferenceMap R X s t n)
      (singularMayerVietorisSumMap R X s t n) := by
  let e := homologyBiprodEquiv ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R)
    ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R) n
  let i := smallChainHomologyIso X (twoSetFamily X s t) R
    (mv_twoSetFamily_open X s t hs ht) (mv_twoSetFamily_cover X s t hcover) n
  have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((subspaceSmallShortExact X s t R).homology_exact₂ n)
  intro p
  constructor
  · intro hp
    have hg : HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g n
        (e.symm p) = 0 := by
      apply i.toLinearEquiv.injective
      change HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) n
        (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g n
          (e.symm p)) = i.hom 0
      rw [map_zero, small_homology_sum]
      exact hp
    obtain ⟨z, hz⟩ := (hexact _).mp hg
    refine ⟨z, (homologyBiprodEquiv_difference R X s t n z).symm.trans ?_⟩
    exact (congrArg e hz).trans (e.apply_symm_apply p)
  · rintro ⟨z, rfl⟩
    rw [← small_homology_sum]
    rw [← homologyBiprodEquiv_difference]
    change i.hom (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g n
      (e.symm (e (HomologicalComplex.homologyMap
        (subspaceSmallShortComplex X s t R).f n z)))) = 0
    rw [e.symm_apply_apply, hexact.apply_apply_eq_zero, map_zero]

theorem singularMayerVietoris_exact_connecting
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    Function.Exact (singularMayerVietorisSumMap R X s t (n + 1))
      (singularMayerVietorisConnectingMap R X s t hs ht hcover n) := by
  let e := homologyBiprodEquiv ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R)
    ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R) (n + 1)
  let i := smallChainHomologyIso X (twoSetFamily X s t) R
    (mv_twoSetFamily_open X s t hs ht) (mv_twoSetFamily_cover X s t hcover) (n + 1)
  have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((subspaceSmallShortExact X s t R).homology_exact₃ (n + 1) n (by simp))
  intro x
  constructor
  · intro hx
    obtain ⟨w, hw⟩ := (hexact (i.inv x)).mp hx
    refine ⟨e w, ?_⟩
    rw [← small_homology_sum]
    change i.hom (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g
      (n + 1) (e.symm (e w))) = x
    rw [e.symm_apply_apply, hw]
    exact i.toLinearEquiv.apply_symm_apply x
  · rintro ⟨p, rfl⟩
    rw [← small_homology_sum]
    have h := congrArg (fun f => f
      (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g (n + 1)
        (e.symm p)))
      (small_inclusion_singularMayerVietorisConnectingMap R X s t hs ht hcover n)
    exact h.trans (hexact.apply_apply_eq_zero (e.symm p))

theorem singularMayerVietoris_exact_difference
    (hs : IsOpen s) (ht : IsOpen t) (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) (n : ℕ) :
    Function.Exact (singularMayerVietorisConnectingMap R X s t hs ht hcover n)
      (singularMayerVietorisDifferenceMap R X s t n) := by
  let e := homologyBiprodEquiv ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R)
    ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R) n
  let i := smallChainHomologyIso X (twoSetFamily X s t) R
    (mv_twoSetFamily_open X s t hs ht) (mv_twoSetFamily_cover X s t hcover) (n + 1)
  have hexact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((subspaceSmallShortExact X s t R).homology_exact₁ (n + 1) n (by simp))
  intro z
  constructor
  · intro hz
    have hf : HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).f n z = 0 := by
      apply e.injective
      rw [homologyBiprodEquiv_difference]
      exact hz.trans (by simp only [e, homologyBiprodEquiv, Equiv.coe_fn_mk, map_zero]; rfl)
    obtain ⟨c, hc⟩ := (hexact z).mp hf
    refine ⟨i.hom c, ?_⟩
    have h := congrArg (fun f => f c)
      (small_inclusion_singularMayerVietorisConnectingMap R X s t hs ht hcover n)
    exact h.trans hc
  · rintro ⟨x, rfl⟩
    rw [← homologyBiprodEquiv_difference]
    change e (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).f n
      ((subspaceSmallShortExact X s t R).δ (n + 1) n (by simp) (i.inv x))) = 0
    rw [hexact.apply_apply_eq_zero]
    simp [e, homologyBiprodEquiv]

theorem singularMayerVietorisSumMap_zero_surjective
    (hcover : ∀ x : X, x ∈ s ∨ x ∈ t) :
    Function.Surjective (singularMayerVietorisSumMap R X s t 0) := by
  let e := homologyBiprodEquiv ((TopCat.toSSet.obj (TopCat.of s)).chainComplex R)
    ((TopCat.toSSet.obj (TopCat.of t)).chainComplex R) 0
  have := (subspaceSmallShortExact X s t R).epi_g
  have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (subspaceSmallShortComplex X s t R).g 0 (by simp)
  have hsurj := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g 0)).mp
      inferInstance
  have := isIso_smallChainMap_f_zero X (twoSetFamily X s t) R
    (mv_twoSetFamily_cover X s t hcover)
  have := HomologicalComplex.epi_homologyMap_of_epi_of_not_rel
    (smallChainMap X (twoSetFamily X s t) R) 0 (by simp)
  have hsmall := (ModuleCat.epi_iff_surjective
    (HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) 0)).mp
      inferInstance
  intro x
  obtain ⟨c, hc⟩ := hsmall x
  obtain ⟨w, hw⟩ := hsurj c
  refine ⟨e w, ?_⟩
  rw [← small_homology_sum]
  change HomologicalComplex.homologyMap (smallChainMap X (twoSetFamily X s t) R) 0
    (HomologicalComplex.homologyMap (subspaceSmallShortComplex X s t R).g 0
      (e.symm (e w))) = x
  rw [e.symm_apply_apply, hw, hc]

end DifferentialGeometry.Homology
