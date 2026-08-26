module

public import SphereSixComplex.Geometry.Quotient
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product

/-!
# Fundamental-group classes from deck paths

For a path-connected space with a group action, a path from a point to one of its deck translates
projects to a based loop in the orbit quotient.  This elementary construction is shared by the
outer triangle-group quotient and the two finite affine elliptic filling quotients.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

open CategoryTheory

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]

/-- The preimage of a subset of the quotient is invariant under every deck transformation. -/
public def quotientCoveringPreimageSubMulAction
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (V : Set X) : SubMulAction G M where
  carrier := f ⁻¹' V
  smul_mem' g x hx := by
    change f (g • x) ∈ V
    rw [hf.map_smul]
    exact hx

/-- The restricted deck action on the preimage of a subset of the quotient. -/
@[instance_reducible] public def quotientCoveringPreimageMulAction
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (V : Set X) :
    MulAction G (f ⁻¹' V) :=
  SubMulAction.mulAction (quotientCoveringPreimageSubMulAction hf V)

/-- Restricting a quotient covering over an arbitrary target subset again gives a quotient
covering by the same deck group. -/
public theorem IsQuotientCoveringMap.restrictPreimage
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (V : Set X) :
    letI := quotientCoveringPreimageMulAction hf V
    IsQuotientCoveringMap (V.restrictPreimage f) G := by
  let _ := quotientCoveringPreimageMulAction hf V
  apply (isQuotientCoveringMap_iff_isCoveringMap_and
    (f := V.restrictPreimage f) (G := G)).mpr
  refine ⟨hf.isCoveringMap.restrictPreimage V,
    hf.surjective.restrictPreimage V, ?_, ?_, ?_⟩
  · exact ⟨fun g ↦ by
      apply Continuous.subtype_mk
        (hf.continuous_const_smul g |>.comp continuous_subtype_val)⟩
  · rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro g x hx
    apply hf.isCancelSMul.eq_one_of_smul (x := x.1)
    exact congrArg Subtype.val hx
  · intro x y
    rw [Subtype.ext_iff]
    change f x.1 = f y.1 ↔ _
    rw [hf.apply_eq_iff_mem_orbit, MulAction.mem_orbit_iff,
      MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, congrArg Subtype.val hg⟩

/-- If the images of `S` generate the target of a group homomorphism, then `S` together with
the kernel generates the source.  This is the algebraic step behind the covering-space
generation theorem below. -/
public theorem closure_union_ker_eq_top_of_image_closure_eq_top
    {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Set A)
    (himage : Subgroup.closure (f '' S) = ⊤) :
    Subgroup.closure (S ∪ (f.ker : Set A)) = ⊤ := by
  apply top_unique
  intro a _
  have hfa : f a ∈ Subgroup.closure (f '' S) := by
    rw [himage]
    trivial
  rw [← f.map_closure S] at hfa
  obtain ⟨c, hc, hfc⟩ := hfa
  have hc' : c ∈ Subgroup.closure (S ∪ (f.ker : Set A)) :=
    Subgroup.closure_mono Set.subset_union_left hc
  have hk : a * c⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfc]
    simp
  have hk' : a * c⁻¹ ∈ Subgroup.closure (S ∪ (f.ker : Set A)) :=
    Subgroup.subset_closure (Set.mem_union_right S hk)
  simpa using (Subgroup.closure (S ∪ (f.ker : Set A))).mul_mem hk' hc'

/-- A generating set maps to a generating set for the range of any group homomorphism. -/
public theorem closure_image_eq_range_of_closure_eq_top
    {A B : Type*} [Group A] [Group B] (f : A →* B) (S : Set A)
    (hgenerate : Subgroup.closure S = ⊤) :
    Subgroup.closure (f '' S) = f.range := by
  rw [← f.map_closure S, hgenerate, MonoidHom.range_eq_map]

/-- Include one factor of a product while holding the other coordinate fixed. -/
public def prodConstSection {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (y : Y) : C(X, X × Y) :=
  ⟨fun x ↦ (x, y), continuous_id.prodMk continuous_const⟩

/-- If the second factor is simply connected, the fixed-coordinate inclusion of the first factor
induces a surjection on fundamental groups. -/
public theorem fundamentalGroup_map_prodConstSection_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (x : X) (y : Y) :
    Function.Surjective (FundamentalGroup.map (prodConstSection y) x) := by
  intro q
  let qx : FundamentalGroup X x :=
    Path.Homotopic.Quotient.map q ⟨Prod.fst, continuous_fst⟩
  refine ⟨qx, ?_⟩
  change Path.Homotopic.Quotient.map qx (prodConstSection y) = q
  rw [← Path.Homotopic.prod_projLeft_projRight q]
  change Path.Homotopic.prod qx (.refl y) =
    Path.Homotopic.prod (Path.Homotopic.projLeft q)
      (Path.Homotopic.projRight q)
  congr 1
  exact Subsingleton.elim _ _

/-- The fixed-coordinate inclusion still induces a surjection after identifying its displayed
product basepoint with a propositionally equal named point. -/
public theorem fundamentalGroup_mapOfEq_prodConstSection_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (x : X) (y : Y) (z : X × Y)
    (h : (prodConstSection y) x = z) :
    Function.Surjective (FundamentalGroup.mapOfEq (prodConstSection y) h) := by
  intro q
  let q' : FundamentalGroup (X × Y) ((prodConstSection y) x) :=
    Path.Homotopic.Quotient.cast q h h
  obtain ⟨a, ha⟩ := fundamentalGroup_map_prodConstSection_surjective x y q'
  refine ⟨a, ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.map a (prodConstSection y) = q' at ha
  rw [ha]
  dsimp [q']
  rw [Path.Homotopic.Quotient.cast_cast]
  simp

/-- A homeomorphism induces a surjection on fundamental groups at corresponding basepoints. -/
public theorem fundamentalGroup_map_homeomorph_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Function.Surjective
      (FundamentalGroup.map (⟨e, e.continuous⟩ : C(X, Y)) x) := by
  intro q
  let inv := FundamentalGroup.mapOfEq
    (⟨e.symm, e.symm.continuous⟩ : C(Y, X)) (e.symm_apply_apply x)
  let a : FundamentalGroup X x := inv q
  refine ⟨a, ?_⟩
  change Path.Homotopic.Quotient.map a (⟨e, e.continuous⟩ : C(X, Y)) = q
  dsimp only [a, inv]
  rw [FundamentalGroup.mapOfEq_apply]
  induction q using Quotient.ind with
  | _ P =>
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact e.apply_symm_apply (P t)

/-- A homeomorphism also induces a surjection after identifying its image basepoint with a named
target point. -/
public theorem fundamentalGroup_mapOfEq_homeomorph_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (y : Y) (h : e x = y) :
    Function.Surjective
      (FundamentalGroup.mapOfEq (⟨e, e.continuous⟩ : C(X, Y)) h) := by
  intro q
  let q' : FundamentalGroup Y (e x) :=
    Path.Homotopic.Quotient.cast q h h
  obtain ⟨a, ha⟩ := fundamentalGroup_map_homeomorph_surjective e x q'
  refine ⟨a, ?_⟩
  rw [FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.map a (⟨e, e.continuous⟩ : C(X, Y)) = q' at ha
  rw [ha]
  dsimp [q']
  rw [Path.Homotopic.Quotient.cast_cast]
  simp

/-- Concatenate a continuously chosen path from each point to its image under `f`.  The result
records the lifted path through `n` successive iterates of `f`. -/
public def iteratedForwardPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (step : ∀ x, Path x (f x)) :
    ∀ (n : ℕ) (x : X), Path x (f^[n] x)
  | 0, x => Path.refl x
  | n + 1, x =>
      ((step x).trans (iteratedForwardPath f step n (f x))).cast rfl
        (Function.iterate_succ_apply f n x)

/-- Concatenate one path with its successive images under a continuous self-map.  Unlike
`iteratedForwardPath`, every later segment is the corresponding iterate of the first segment;
this is the lift that represents a power of the projected one-step loop. -/
public def iteratedMappedPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) {x : X}
    (P : Path x (f x)) : ∀ n : ℕ, Path x (f^[n] x)
  | 0 => Path.refl x
  | n + 1 =>
      (iteratedMappedPath f hf P n).trans
        ((P.map (hf.iterate n)).cast rfl (Function.iterate_succ_apply f n x))

/-- A map invariant under one application of `f` is invariant under every iterate of `f`. -/
public theorem map_iterate_eq_of_map_comp_eq {X Y : Type*}
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z) (n : ℕ) (z : X) :
    q (f^[n] z) = q z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (f z)).trans (hq z)

/-- Project a path from `x` to `f x` along an `f`-invariant map, obtaining a loop. -/
public def projectedForwardLoop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z)
    {x : X} (P : Path x (f x)) (hqcont : Continuous q) : Path (q x) (q x) :=
  (P.map hqcont).cast rfl (hq x).symm

/-- Project the successive images of a path to the invariant target and cast its final endpoint
back to the initial basepoint. -/
public def projectedIteratedMappedLoop {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) : Path (q x) (q x) :=
  ((iteratedMappedPath f hf P n).map hqcont).cast rfl
    (map_iterate_eq_of_map_comp_eq f q hq n x).symm

/-- A literal `n`-fold concatenation of one based loop. -/
public def repeatedLoop {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : ℕ → Path y y
  | 0 => Path.refl y
  | n + 1 => (repeatedLoop L n).trans L

/-- Regard a based path as its fundamental-group class. -/
public def pathLoopClass {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : FundamentalGroup Y y :=
  Path.Homotopic.Quotient.mk L

/-- Casting both endpoints of a loop along a point equality is the same as applying the
fundamental-group homomorphism induced by the identity map with that target basepoint. -/
public theorem pathLoopClass_cast_eq_mapOfEq_id
    {X : Type*} [TopologicalSpace X] {x y : X}
    (L : Path x x) (h : x = y) :
    pathLoopClass (L.cast h.symm h.symm) =
      FundamentalGroup.mapOfEq (ContinuousMap.id X) h (pathLoopClass L) := by
  have hm := FundamentalGroup.mapOfEq_apply (ContinuousMap.id X)
    (show (ContinuousMap.id X) x = y from h) (pathLoopClass L)
  rw [hm]
  rfl

/-- Transporting a local loop back along a path is represented by whiskering the loop with that
path and its reverse. -/
public def whiskeredLoopClass {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) : FundamentalGroup X x :=
  pathLoopClass (W.trans (L.trans W.symm))

/-- Changing the path used to transport a local loop changes its based class by conjugation
with the loop obtained by traversing the old whisker and returning along the new one. -/
public theorem whiskeredLoopClass_change_whisker
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W W₀ : Path x y) (L : Path y y) :
    whiskeredLoopClass W L =
      (pathLoopClass (W.trans W₀.symm))⁻¹ *
        whiskeredLoopClass W₀ L *
          pathLoopClass (W.trans W₀.symm) := by
  simp only [whiskeredLoopClass, pathLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    FundamentalGroup.inv_def, FundamentalGroup.mul_def]
  rw [show
    ((Path.Homotopic.Quotient.mk W).trans
      (Path.Homotopic.Quotient.mk W₀).symm).symm =
        (Path.Homotopic.Quotient.mk W₀).trans
          (Path.Homotopic.Quotient.mk W).symm by
    rw [← Path.Homotopic.Quotient.mk_symm W₀,
      ← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_symm,
      Path.trans_symm, Path.symm_symm,
      Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]]
  simp only [← Path.Homotopic.Quotient.trans_assoc]
  rw [Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk W)
      (Path.Homotopic.Quotient.mk W₀).symm
      (Path.Homotopic.Quotient.mk W₀),
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]
  rw [Path.Homotopic.Quotient.trans_assoc
      ((Path.Homotopic.Quotient.mk W).trans
        (Path.Homotopic.Quotient.mk L))
      (Path.Homotopic.Quotient.mk W₀).symm
      (Path.Homotopic.Quotient.mk W₀),
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.trans_refl]

/-- Functoriality of a whiskered loop when both displayed endpoint images are cast to named
target points.  This avoids having to compare the differently parenthesized mapped paths
pointwise. -/
public theorem mapOfEq_whiskeredLoopClass
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x y : X} {x' y' : Y} (f : C(X, Y))
    (hx : f x = x') (hy : f y = y')
    (W : Path x y) (L : Path y y) :
    FundamentalGroup.mapOfEq f hx (whiskeredLoopClass W L) =
      whiskeredLoopClass
        ((W.map f.continuous).cast hx.symm hy.symm)
        ((L.map f.continuous).cast hy.symm hy.symm) := by
  rw [whiskeredLoopClass, whiskeredLoopClass,
    FundamentalGroup.mapOfEq_apply]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_trans, Path.trans_apply, Path.map_coe,
    Function.comp_apply, Path.symm_apply]

/-- If the far endpoint of a whisker is identified with its starting point, Mathlib's reversed
path-composition convention writes geometric whiskering as inverse conjugation.  This is the
conversion needed when a paper presentation uses the usual left-to-right loop convention. -/
public theorem whiskeredLoopClass_eq_conjugate_cast
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) (h : y = x) :
    whiskeredLoopClass W L =
      (pathLoopClass (W.cast rfl h.symm))⁻¹ *
        pathLoopClass (L.cast h.symm h.symm) *
        pathLoopClass (W.cast rfl h.symm) := by
  subst h
  simp only [whiskeredLoopClass, pathLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rfl

public theorem fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm (pathLoopClass L) =
      whiskeredLoopClass W L := by
  rfl

/-- Basepoint transport preserves a conjugation identity. -/
public theorem whiskeredLoopClass_conjugation
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (D T T' : Path y y)
    (h : (pathLoopClass D)⁻¹ * pathLoopClass T * pathLoopClass D =
      pathLoopClass T') :
    (whiskeredLoopClass W D)⁻¹ * whiskeredLoopClass W T *
        whiskeredLoopClass W D = whiskeredLoopClass W T' := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have hm := congrArg e.symm h
  rw [← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W D,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T']
  simpa only [map_mul, map_inv] using hm

/-- Basepoint transport carries a local power relation to the corresponding whiskered loops. -/
public theorem whiskeredLoopClass_pow_eq
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L P : Path y y) (n : ℕ)
    (h : pathLoopClass L ^ n = pathLoopClass P) :
    whiskeredLoopClass W L ^ n = whiskeredLoopClass W P := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  calc
    whiskeredLoopClass W L ^ n = (e.symm (pathLoopClass L)) ^ n := by
      rw [fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass]
    _ = e.symm (pathLoopClass L ^ n) := (map_pow e.symm _ n).symm
    _ = e.symm (pathLoopClass P) := congrArg e.symm h
    _ = whiskeredLoopClass W P :=
      fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W P

/-- Literal repeated concatenation represents the corresponding group power.  The proof records
the reversal built into Mathlib's categorical convention for fundamental-group multiplication. -/
public theorem pathLoopClass_repeatedLoop {Y : Type*} [TopologicalSpace Y]
    {y : Y} (L : Path y y) (n : ℕ) :
    pathLoopClass (repeatedLoop L n) = pathLoopClass L ^ n := by
  induction n with
  | zero =>
      rw [repeatedLoop.eq_def, pow_zero]
      exact Path.Homotopic.Quotient.mk_refl y
  | succ n ih =>
      rw [repeatedLoop.eq_def, pathLoopClass, Path.Homotopic.Quotient.mk_trans,
        ← pathLoopClass, ih, pow_succ']
      rfl

/-- After projection along an invariant map, the concatenation of the successive images of a
path is literally the repeated projected loop. -/
public theorem projectedIteratedMappedLoop_eq_repeatedLoop
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    projectedIteratedMappedLoop f hf q hq P hqcont n =
      repeatedLoop (projectedForwardLoop f q hq P hqcont) n := by
  induction n with
  | zero =>
      apply Path.ext
      funext t
      rfl
  | succ n ih =>
      apply Path.ext
      funext t
      change q (((iteratedMappedPath f hf P n).trans
          ((P.map (hf.iterate n)).cast rfl
            (Function.iterate_succ_apply f n x))) t) =
        ((repeatedLoop (projectedForwardLoop f q hq P hqcont) n).trans
          (projectedForwardLoop f q hq P hqcont)) t
      rw [Path.trans_apply]
      rw [Path.trans_apply]
      split_ifs with ht
      · exact congrArg
          (fun Q : Path (q x) (q x) =>
            Q ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩) ih
      · change q ((f^[n])
            (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)) =
          q (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
        rw [map_iterate_eq_of_map_comp_eq f q hq]

/-- The projected successive-image path represents the `n`th power of its projected one-step
loop in the fundamental group. -/
public theorem pathLoopClass_projectedIteratedMappedLoop_eq_pow
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    pathLoopClass (projectedIteratedMappedLoop f hf q hq P hqcont n) =
      pathLoopClass (projectedForwardLoop f q hq P hqcont) ^ n := by
  rw [projectedIteratedMappedLoop_eq_repeatedLoop]
  exact pathLoopClass_repeatedLoop _ _

/-! ## Deck paths for an arbitrary quotient-covering target -/

/-- Project a specified path to a deck translate along an arbitrary quotient covering. -/
public def projectedQuotientDeckPath
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G)
    (P : Path x (g • x)) : Path (f x) (f x) :=
  (P.map hf.continuous).cast rfl (hf.map_smul g).symm

/-- The class of a projected deck path selected using path connectedness of the covering space. -/
public def quotientDeckClass
    {X : Type*} [TopologicalSpace X] {f : M → X}
    [PathConnectedSpace M] (hf : IsQuotientCoveringMap f G)
    (x : M) (g : G) : FundamentalGroup X (f x) :=
  pathLoopClass (projectedQuotientDeckPath hf x g
    (PathConnectedSpace.somePath x (g • x)))

/-- Covering monodromy sends a specified projected deck path to its deck label. -/
public theorem fundamentalGroupToMulOpposite_projectedQuotientDeckPath
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G)
    (P : Path x (g • x)) :
    hf.fundamentalGroupToMulOpposite
        (⟨x, rfl⟩ : f ⁻¹' {f x})
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) =
      MulOpposite.op g := by
  rw [hf.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let e : f ⁻¹' {f x} := ⟨x, rfl⟩
  let e' : f ⁻¹' {f x} := ⟨g • x, hf.map_smul g⟩
  have hm : hf.isCoveringMap.monodromy
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) e = e' :=
    hf.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk P) (by rfl)
  exact congrArg Subtype.val hm.symm

/-- For an arbitrary quotient-covering target, loop classes whose monodromy images generate the
deck group, together with the image of the covering-space fundamental group, generate the target
fundamental group. -/
public theorem quotientCovering_generators_and_cover_range_generate_general
    {X : Type*} [TopologicalSpace X] {f : M → X}
    [PathConnectedSpace M]
    (hf : IsQuotientCoveringMap f G) (x : M)
    (S : Set (FundamentalGroup X (f x)))
    (himage : Subgroup.closure
      (hf.fundamentalGroupToMulOpposite (⟨x, rfl⟩ : f ⁻¹' {f x}) '' S) = ⊤) :
    Subgroup.closure
      (S ∪ (FundamentalGroup.mapOfEq
        (⟨f, hf.continuous⟩ : C(M, X)) (x := x) (y := f x) rfl).range) = ⊤ := by
  let e : f ⁻¹' {f x} := ⟨x, rfl⟩
  let mon := hf.fundamentalGroupToMulOpposite e
  have hker : mon.ker =
      (FundamentalGroup.mapOfEq
        (⟨f, hf.continuous⟩ : C(M, X)) (x := x) (y := f x) rfl).range := by
    rw [hf.ker_fundamentalGroupToMulOpposite e,
      hf.ker_monodromyPerm e]
  rw [← hker]
  exact closure_union_ker_eq_top_of_image_closure_eq_top mon S himage

/-- All projected deck classes and the covering-space image generate the fundamental group of an
arbitrary quotient-covering target. -/
public theorem quotientCovering_all_deck_classes_and_cover_range_generate_general
    {X : Type*} [TopologicalSpace X] {f : M → X}
    [PathConnectedSpace M]
    (hf : IsQuotientCoveringMap f G) (x : M) :
    Subgroup.closure
      (Set.range (quotientDeckClass hf x) ∪
        (FundamentalGroup.mapOfEq
          (⟨f, hf.continuous⟩ : C(M, X)) (x := x) (y := f x) rfl).range) = ⊤ := by
  apply quotientCovering_generators_and_cover_range_generate_general hf x
    (Set.range (quotientDeckClass hf x))
  apply top_unique
  intro g _
  obtain ⟨g, rfl⟩ := MulOpposite.op_surjective g
  apply Subgroup.subset_closure
  refine ⟨quotientDeckClass hf x g, ⟨g, rfl⟩, ?_⟩
  exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath hf x g
    (PathConnectedSpace.somePath x (g • x))

/-- The continuous inclusion induced by a subset relation. -/
public def continuousSetInclusion
    {X : Type*} [TopologicalSpace X] {W V : Set X} (hWV : W ⊆ V) : C(W, V) :=
  ⟨fun x ↦ ⟨x.1, hWV x.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- Surjectivity on fundamental groups passes from an inclusion of covering spaces to the
corresponding inclusion of quotient-covering targets.  Deck paths can be chosen in the smaller
covering space because it is path connected; the remaining covering-space contribution is the
given surjective image. -/
public theorem quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) {W V : Set X} (hWV : W ⊆ V)
    (x : M) (hxW : f x ∈ W)
    [PathConnectedSpace (f ⁻¹' W)] [PathConnectedSpace (f ⁻¹' V)]
    (hsource : Function.Surjective
      (FundamentalGroup.map
        (continuousSetInclusion (fun _ hz ↦ hWV hz) :
          C(f ⁻¹' W, f ⁻¹' V)) (⟨x, hxW⟩ : f ⁻¹' W))) :
    Function.Surjective
      (FundamentalGroup.map (continuousSetInclusion hWV)
        (⟨f x, hxW⟩ : W)) := by
  let _ := quotientCoveringPreimageMulAction hf W
  let _ := quotientCoveringPreimageMulAction hf V
  let fW : f ⁻¹' W → W := W.restrictPreimage f
  let fV : f ⁻¹' V → V := V.restrictPreimage f
  let xW : f ⁻¹' W := ⟨x, hxW⟩
  let sourceIncl : C(f ⁻¹' W, f ⁻¹' V) :=
    continuousSetInclusion (fun _ hz ↦ hWV hz)
  let xV : f ⁻¹' V := sourceIncl xW
  let bW : W := fW xW
  let bV : V := fV xV
  let targetIncl : C(W, V) := continuousSetInclusion hWV
  let hpW : IsQuotientCoveringMap fW G :=
    SphereSixComplex.Geometry.IsQuotientCoveringMap.restrictPreimage hf W
  let hpV : IsQuotientCoveringMap fV G :=
    SphereSixComplex.Geometry.IsQuotientCoveringMap.restrictPreimage hf V
  let sourceMap := FundamentalGroup.map sourceIncl xW
  let targetMap := FundamentalGroup.map targetIncl bW
  let coverMapW := FundamentalGroup.mapOfEq
    (⟨fW, hpW.continuous⟩ : C(f ⁻¹' W, W))
    (x := xW) (y := bW) rfl
  let coverMapV := FundamentalGroup.mapOfEq
    (⟨fV, hpV.continuous⟩ : C(f ⁻¹' V, V))
    (x := xV) (y := bV) rfl
  let deckPathW (g : G) : Path xW (g • xW) :=
    PathConnectedSpace.somePath xW (g • xW)
  let deckPathV (g : G) : Path xV (g • xV) :=
    ((deckPathW g).map sourceIncl.continuous).cast
      (Subtype.ext rfl) (Subtype.ext rfl)
  let deckClassV (g : G) : FundamentalGroup V bV :=
    pathLoopClass (projectedQuotientDeckPath hpV xV g (deckPathV g))
  have hdeckImage : Subgroup.closure
      (hpV.fundamentalGroupToMulOpposite (⟨xV, rfl⟩ : fV ⁻¹' {fV xV}) ''
        Set.range deckClassV) = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨g, rfl⟩ := MulOpposite.op_surjective a
    apply Subgroup.subset_closure
    refine ⟨deckClassV g, ⟨g, rfl⟩, ?_⟩
    exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath
      hpV xV g (deckPathV g)
  have hgenerate := quotientCovering_generators_and_cover_range_generate_general
    hpV xV (Set.range deckClassV) hdeckImage
  let H : Subgroup (FundamentalGroup V bV) := targetMap.range
  have hdeckMem (g : G) : deckClassV g ∈ H := by
    let LW := projectedQuotientDeckPath hpW xW g (deckPathW g)
    refine ⟨pathLoopClass LW, ?_⟩
    change targetMap (pathLoopClass LW) = deckClassV g
    change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk LW) targetIncl =
      Path.Homotopic.Quotient.mk
        (projectedQuotientDeckPath hpV xV g (deckPathV g))
    rw [← Path.Homotopic.Quotient.mk_map]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    rfl
  have hcoverComm (a : FundamentalGroup (f ⁻¹' W) xW) :
      targetMap (coverMapW a) = coverMapV (sourceMap a) := by
    induction a using Quotient.ind with
    | _ P =>
        change targetMap (coverMapW (Path.Homotopic.Quotient.mk P)) =
          coverMapV (sourceMap (Path.Homotopic.Quotient.mk P))
        dsimp only [targetMap, coverMapW, coverMapV, sourceMap]
        rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
        apply congrArg Path.Homotopic.Quotient.mk
        apply Path.ext
        funext t
        rfl
  have hcoverMem (a : FundamentalGroup (f ⁻¹' V) xV) : coverMapV a ∈ H := by
    obtain ⟨c, hc⟩ := hsource a
    refine ⟨coverMapW c, ?_⟩
    rw [hcoverComm]
    change coverMapV (sourceMap c) = coverMapV a
    rw [hc]
  have hle : Subgroup.closure
      (Set.range deckClassV ∪ (coverMapV.range : Set _)) ≤ H := by
    apply (Subgroup.closure_le _).2
    intro a ha
    rcases ha with ha | ha
    · obtain ⟨g, rfl⟩ := ha
      exact hdeckMem g
    · obtain ⟨q, rfl⟩ := ha
      exact hcoverMem q
  have hgenerate' : Subgroup.closure
      (Set.range deckClassV ∪ (coverMapV.range : Set _)) = ⊤ := by
    simpa [coverMapV, fV, xV, bV] using hgenerate
  rw [hgenerate'] at hle
  intro q
  exact hle (by trivial)

/-- An equivariant map between path-connected quotient coverings inherits surjectivity on
fundamental groups from the map between their covering spaces.  This version allows the source
and target covering spaces, and their quotients, to be different types. -/
public theorem quotientCovering_equivariant_map_fundamentalGroup_surjective
    {MW MV XW XV : Type*}
    [TopologicalSpace MW] [TopologicalSpace MV]
    [TopologicalSpace XW] [TopologicalSpace XV]
    [MulAction G MW] [MulAction G MV]
    [PathConnectedSpace MW] [PathConnectedSpace MV]
    {fW : MW → XW} {fV : MV → XV}
    (hfW : IsQuotientCoveringMap fW G)
    (hfV : IsQuotientCoveringMap fV G)
    (sourceMap : C(MW, MV)) (targetMap : C(XW, XV))
    (hcomm : ∀ y, targetMap (fW y) = fV (sourceMap y))
    (hequiv : ∀ (g : G) y, sourceMap (g • y) = g • sourceMap y)
    (x : MW)
    (hsource : Function.Surjective (FundamentalGroup.map sourceMap x)) :
    Function.Surjective
      (FundamentalGroup.mapOfEq targetMap (hcomm x)) := by
  let xV : MV := sourceMap x
  let bW : XW := fW x
  let bV : XV := fV xV
  let sourceHom := FundamentalGroup.map sourceMap x
  let targetHom := FundamentalGroup.mapOfEq targetMap (hcomm x)
  let coverHomW := FundamentalGroup.mapOfEq
    (⟨fW, hfW.continuous⟩ : C(MW, XW)) (x := x) (y := bW) rfl
  let coverHomV := FundamentalGroup.mapOfEq
    (⟨fV, hfV.continuous⟩ : C(MV, XV)) (x := xV) (y := bV) rfl
  let deckPathW (g : G) : Path x (g • x) :=
    PathConnectedSpace.somePath x (g • x)
  let deckPathV (g : G) : Path xV (g • xV) :=
    ((deckPathW g).map sourceMap.continuous).cast rfl (hequiv g x).symm
  let deckClassV (g : G) : FundamentalGroup XV bV :=
    pathLoopClass (projectedQuotientDeckPath hfV xV g (deckPathV g))
  have hdeckImage : Subgroup.closure
      (hfV.fundamentalGroupToMulOpposite (⟨xV, rfl⟩ : fV ⁻¹' {fV xV}) ''
        Set.range deckClassV) = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨g, rfl⟩ := MulOpposite.op_surjective a
    apply Subgroup.subset_closure
    refine ⟨deckClassV g, ⟨g, rfl⟩, ?_⟩
    exact fundamentalGroupToMulOpposite_projectedQuotientDeckPath
      hfV xV g (deckPathV g)
  have hgenerate := quotientCovering_generators_and_cover_range_generate_general
    hfV xV (Set.range deckClassV) hdeckImage
  let H : Subgroup (FundamentalGroup XV bV) := targetHom.range
  have hdeckMem (g : G) : deckClassV g ∈ H := by
    let LW := projectedQuotientDeckPath hfW x g (deckPathW g)
    refine ⟨pathLoopClass LW, ?_⟩
    change targetHom (pathLoopClass LW) = deckClassV g
    dsimp only [targetHom]
    rw [FundamentalGroup.mapOfEq_apply]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact hcomm (deckPathW g t)
  have hcoverComm (a : FundamentalGroup MW x) :
      targetHom (coverHomW a) = coverHomV (sourceHom a) := by
    induction a using Quotient.ind with
    | _ P =>
        change targetHom (coverHomW (Path.Homotopic.Quotient.mk P)) =
          coverHomV (sourceHom (Path.Homotopic.Quotient.mk P))
        dsimp only [targetHom, coverHomW, coverHomV, sourceHom]
        rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
          FundamentalGroup.mapOfEq_apply]
        apply congrArg Path.Homotopic.Quotient.mk
        apply Path.ext
        funext t
        exact hcomm (P t)
  have hcoverMem (a : FundamentalGroup MV xV) : coverHomV a ∈ H := by
    obtain ⟨c, hc⟩ := hsource a
    refine ⟨coverHomW c, ?_⟩
    rw [hcoverComm]
    change coverHomV (sourceHom c) = coverHomV a
    rw [hc]
  have hle : Subgroup.closure
      (Set.range deckClassV ∪ (coverHomV.range : Set _)) ≤ H := by
    apply (Subgroup.closure_le _).2
    intro a ha
    rcases ha with ha | ha
    · obtain ⟨g, rfl⟩ := ha
      exact hdeckMem g
    · obtain ⟨q, rfl⟩ := ha
      exact hcoverMem q
  have hgenerate' : Subgroup.closure
      (Set.range deckClassV ∪ (coverHomV.range : Set _)) = ⊤ := by
    simpa [coverHomV, xV, bV] using hgenerate
  rw [hgenerate'] at hle
  intro q
  exact hle (by trivial)

/-- A propositionally renamed target basepoint does not affect surjectivity of the induced
fundamental-group map. -/
public theorem fundamentalGroup_map_surjective_of_mapOfEq_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (hsurj : Function.Surjective (FundamentalGroup.mapOfEq f h)) :
    Function.Surjective (FundamentalGroup.map f x) := by
  intro q
  let q' : FundamentalGroup Y y :=
    Path.Homotopic.Quotient.cast q h.symm h.symm
  obtain ⟨a, ha⟩ := hsurj q'
  refine ⟨a, ?_⟩
  have ha' := congrArg
    (fun z : FundamentalGroup Y y ↦
      Path.Homotopic.Quotient.cast z h h) ha
  rw [FundamentalGroup.mapOfEq_apply] at ha'
  simpa [q', Path.Homotopic.Quotient.cast_cast] using ha'

/-- A chosen path from a point to one of its translates in a path-connected action space. -/
public def orbitDeckPath [PathConnectedSpace M] (x : M) (g : G) : Path x (g • x) :=
  PathConnectedSpace.somePath _ _

/-- The canonical continuous projection to an orbit quotient. -/
public def orbitQuotientMap : C(M, OrbitQuotient (M := M) (G := G)) :=
  ⟨quotientProjection, continuous_quot_mk⟩

/-- A point and any of its translates have the same orbit-quotient image. -/
public theorem orbitQuotientMap_smul (x : M) (g : G) :
    orbitQuotientMap (G := G) (g • x) = orbitQuotientMap (G := G) x := by
  apply Quotient.sound
  change MulAction.orbitRel G M (g • x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

/-- Compose paths carrying `x` to its `g`- and `h`-translates.  The second path is first
translated by `g`, so the endpoint records the product `g * h` rather than merely forgetting the
deck labels after quotienting. -/
public def composedOrbitDeckPath (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    Path x ((g * h) • x) :=
  (Pg.trans (Ph.map hg)).cast rfl (mul_smul g h x)

/-- Project a specified path to a deck translate, rather than using the arbitrary path selected
by `orbitDeckPath`. -/
public def projectedOrbitDeckPath (x : M) (g : G) (Pg : Path x (g • x)) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  (Pg.map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- Projecting a composed deck path gives the literal concatenation of the two projected loops.
The second upstairs segment was translated by `g`, but orbit projection removes that translate. -/
public theorem projectedOrbitDeckPath_mul_eq
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    projectedOrbitDeckPath x (g * h)
        (composedOrbitDeckPath x g h Pg Ph hg) =
      (projectedOrbitDeckPath x g Pg).trans
        (projectedOrbitDeckPath x h Ph) := by
  apply Path.ext
  funext t
  unfold composedOrbitDeckPath projectedOrbitDeckPath
  change orbitQuotientMap (G := G) ((Pg.trans (Ph.map hg)) t) =
    ((projectedOrbitDeckPath x g Pg).trans
      (projectedOrbitDeckPath x h Ph)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · exact orbitQuotientMap_smul _ _

/-- Deck-path composition is contravariant in the fundamental group.  This theorem records the
precise order reversal: a path labelled `g * h` projects to the class labelled `h` times the class
labelled `g` in Mathlib's fundamental-group multiplication. -/
public theorem projectedOrbitDeckPath_mul
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    pathLoopClass (projectedOrbitDeckPath x (g * h)
      (composedOrbitDeckPath x g h Pg Ph hg)) =
      pathLoopClass (projectedOrbitDeckPath x h Ph) *
        pathLoopClass (projectedOrbitDeckPath x g Pg) := by
  rw [projectedOrbitDeckPath_mul_eq]
  rfl

/-- Rebase a deck path at `y` along `Q : x → y`.  The return path must be translated by `g`
upstairs; after orbit projection it becomes the ordinary reverse whisker. -/
public def rebasedOrbitDeckPath {x y : M} (g : G)
    (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) : Path x (g • x) :=
  Q.trans (D.trans (Q.symm.map hg))

/-- Projecting the genuinely rebased deck path is literally the usual whiskered loop: the
translated return path has the same orbit projection as the original reverse whisker. -/
public theorem projectedRebasedOrbitDeckPath_eq
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    projectedOrbitDeckPath x g (rebasedOrbitDeckPath g Q D hg) =
      (Q.map (orbitQuotientMap (G := G)).continuous).trans
        ((projectedOrbitDeckPath y g D).trans
          (Q.map (orbitQuotientMap (G := G)).continuous).symm) := by
  apply Path.ext
  funext t
  unfold projectedOrbitDeckPath rebasedOrbitDeckPath
  change orbitQuotientMap (G := G)
      ((Q.trans (D.trans (Q.symm.map hg))) t) =
    ((Q.map (orbitQuotientMap (G := G)).continuous).trans
      ((projectedOrbitDeckPath y g D).trans
        (Q.map (orbitQuotientMap (G := G)).continuous).symm)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs with hu
    · rfl
    · change orbitQuotientMap (G := G)
          (g • Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩) =
        orbitQuotientMap (G := G)
          (Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩)
      exact orbitQuotientMap_smul _ _

/-- The path equality above, expressed as the corresponding fundamental-group class. -/
public theorem projectedRebasedOrbitDeckPath_class
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    pathLoopClass (projectedOrbitDeckPath x g
      (rebasedOrbitDeckPath g Q D hg)) =
      whiskeredLoopClass
        (Q.map (orbitQuotientMap (G := G)).continuous)
        (projectedOrbitDeckPath y g D) :=
  congrArg pathLoopClass (projectedRebasedOrbitDeckPath_eq g Q D hg)

/-- Projecting a path to a deck translate gives a based loop in the orbit quotient. -/
public def orbitDeckLoop [PathConnectedSpace M] (x : M) (g : G) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  ((orbitDeckPath x g).map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- The fundamental-group class represented by a projected deck path. -/
public def orbitDeckClass [PathConnectedSpace M] (x : M) (g : G) :
    FundamentalGroup (OrbitQuotient (M := M) (G := G))
      (orbitQuotientMap (G := G) x) :=
  Path.Homotopic.Quotient.mk (orbitDeckLoop x g)

/-- Covering monodromy sends a projected path ending at the `g`-translate of its starting point
to the deck label `g`.  This statement accepts a specified path, so it applies both to the
arbitrary `orbitDeckPath` and to geometric deck paths constructed elsewhere. -/
public theorem fundamentalGroupToMulOpposite_projectedOrbitDeckPath
    (hp : IsQuotientCoveringMap
      (quotientProjection (M := M) (G := G)) G)
    (x : M) (g : G) (P : Path x (g • x)) :
    hp.fundamentalGroupToMulOpposite
        (⟨x, rfl⟩ : (quotientProjection (M := M) (G := G)) ⁻¹'
          {quotientProjection (M := M) (G := G) x})
        (pathLoopClass (projectedOrbitDeckPath x g P)) =
      MulOpposite.op g := by
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let e : (quotientProjection (M := M) (G := G)) ⁻¹'
      {quotientProjection (M := M) (G := G) x} := ⟨x, rfl⟩
  let e' : (quotientProjection (M := M) (G := G)) ⁻¹'
      {quotientProjection (M := M) (G := G) x} :=
    ⟨g • x, orbitQuotientMap_smul x g⟩
  have hm : hp.isCoveringMap.monodromy
        (pathLoopClass (projectedOrbitDeckPath x g P)) e = e' :=
    hp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk P) (by rfl)
  exact congrArg Subtype.val hm.symm

/-- The same monodromy computation after naming the quotient basepoint by an equality. -/
public theorem fundamentalGroupToMulOpposite_projectedOrbitDeckPath_of_eq
    (hp : IsQuotientCoveringMap
      (quotientProjection (M := M) (G := G)) G)
    (x : M) (y : OrbitQuotient (M := M) (G := G))
    (hxy : quotientProjection (M := M) (G := G) x = y)
    (g : G) (P : Path x (g • x)) :
    hp.fundamentalGroupToMulOpposite
        (⟨x, hxy⟩ : (quotientProjection (M := M) (G := G)) ⁻¹' {y})
        (pathLoopClass
          ((projectedOrbitDeckPath x g P).cast hxy.symm hxy.symm)) =
      MulOpposite.op g := by
  rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let e : (quotientProjection (M := M) (G := G)) ⁻¹' {y} := ⟨x, hxy⟩
  let e' : (quotientProjection (M := M) (G := G)) ⁻¹' {y} :=
    ⟨g • x, (orbitQuotientMap_smul x g).trans hxy⟩
  have hm : hp.isCoveringMap.monodromy
        (pathLoopClass ((projectedOrbitDeckPath x g P).cast hxy.symm hxy.symm)) e = e' :=
    hp.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk P) (by rfl)
  exact congrArg Subtype.val hm.symm

/-- For a path-connected quotient covering, any loop classes whose monodromy images generate the
deck group, together with the image of the covering space's fundamental group, generate the
fundamental group of the quotient.  This is the generation half of the usual covering exact
sequence, expressed only with Mathlib's established kernel and monodromy theorems. -/
public theorem quotientCovering_generators_and_cover_range_generate
    [PathConnectedSpace M]
    (hp : IsQuotientCoveringMap
      (quotientProjection (M := M) (G := G)) G)
    (x : M) (S : Set (FundamentalGroup
      (OrbitQuotient (M := M) (G := G))
      (quotientProjection (M := M) (G := G) x)))
    (himage : Subgroup.closure
      (hp.fundamentalGroupToMulOpposite
          (⟨x, rfl⟩ : (quotientProjection (M := M) (G := G)) ⁻¹'
            {quotientProjection (M := M) (G := G) x}) '' S) = ⊤) :
    Subgroup.closure
      (S ∪ (FundamentalGroup.mapOfEq
        (orbitQuotientMap (M := M) (G := G))
        (x := x) (y := quotientProjection (M := M) (G := G) x) rfl).range) = ⊤ := by
  let e : (quotientProjection (M := M) (G := G)) ⁻¹'
      {quotientProjection (M := M) (G := G) x} := ⟨x, rfl⟩
  let f := hp.fundamentalGroupToMulOpposite e
  have hker : f.ker =
      (FundamentalGroup.mapOfEq
        (orbitQuotientMap (M := M) (G := G))
        (x := x) (y := quotientProjection (M := M) (G := G) x) rfl).range := by
    rw [hp.ker_fundamentalGroupToMulOpposite e,
      hp.ker_monodromyPerm e]
    rfl
  rw [← hker]
  exact closure_union_ker_eq_top_of_image_closure_eq_top f S himage

/-- The covering-space generation theorem with an explicitly named target basepoint. -/
public theorem quotientCovering_generators_and_cover_range_generate_of_eq
    [PathConnectedSpace M]
    (hp : IsQuotientCoveringMap
      (quotientProjection (M := M) (G := G)) G)
    (x : M) (y : OrbitQuotient (M := M) (G := G))
    (hxy : quotientProjection (M := M) (G := G) x = y)
    (S : Set (FundamentalGroup (OrbitQuotient (M := M) (G := G)) y))
    (himage : Subgroup.closure
      (hp.fundamentalGroupToMulOpposite
        (⟨x, hxy⟩ : (quotientProjection (M := M) (G := G)) ⁻¹' {y}) '' S) = ⊤) :
    Subgroup.closure
      (S ∪ (FundamentalGroup.mapOfEq
        (orbitQuotientMap (M := M) (G := G))
        (x := x) (y := y) hxy).range) = ⊤ := by
  let e : (quotientProjection (M := M) (G := G)) ⁻¹' {y} := ⟨x, hxy⟩
  let f := hp.fundamentalGroupToMulOpposite e
  have hker : f.ker =
      (FundamentalGroup.mapOfEq
        (orbitQuotientMap (M := M) (G := G))
        (x := x) (y := y) hxy).range := by
    rw [hp.ker_fundamentalGroupToMulOpposite e,
      hp.ker_monodromyPerm e]
    rfl
  rw [← hker]
  exact closure_union_ker_eq_top_of_image_closure_eq_top f S himage

/-- Substitute one generating description into the range part of another. -/
public theorem closure_nested_generators_and_composite_range_eq_top
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : B →* C) (g : A →* B) (S : Set C) (T : Set B)
    (hout : Subgroup.closure (S ∪ (f.range : Set C)) = ⊤)
    (hin : Subgroup.closure (T ∪ (g.range : Set B)) = ⊤) :
    Subgroup.closure (S ∪ f '' T ∪ ((f.comp g).range : Set C)) = ⊤ := by
  apply top_unique
  rw [← hout]
  apply (Subgroup.closure_le _).2
  intro z hz
  rcases hz with hz | hz
  · exact Subgroup.subset_closure (Or.inl (Or.inl hz))
  · obtain ⟨b, rfl⟩ := hz
    change b ∈ (Subgroup.closure
      (S ∪ f '' T ∪ ((f.comp g).range : Set C))).comap f
    apply ((Subgroup.closure_le _).2 ?_ :
      Subgroup.closure (T ∪ (g.range : Set B)) ≤ _)
    · rw [hin]
      trivial
    · intro a ha
      rcases ha with ha | ha
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨a, ha, rfl⟩))
      · obtain ⟨x, rfl⟩ := ha
        exact Subgroup.subset_closure (Or.inr ⟨x, rfl⟩)

/-- In particular, all projected deck-path classes together with the image of the covering
space's fundamental group generate the quotient fundamental group. -/
public theorem quotientCovering_all_deck_classes_and_cover_range_generate
    [PathConnectedSpace M]
    (hp : IsQuotientCoveringMap
      (quotientProjection (M := M) (G := G)) G) (x : M) :
    Subgroup.closure
      (Set.range (orbitDeckClass x) ∪
        (FundamentalGroup.mapOfEq
          (orbitQuotientMap (M := M) (G := G))
          (x := x) (y := orbitQuotientMap (M := M) (G := G) x) rfl).range :
            Set (FundamentalGroup (OrbitQuotient (M := M) (G := G))
              (orbitQuotientMap (M := M) (G := G) x))) = ⊤ := by
  convert quotientCovering_generators_and_cover_range_generate hp x
      (Set.range (orbitDeckClass x)) ?_ using 1 <;> try rfl
  apply top_unique
  intro g _
  obtain ⟨g, rfl⟩ := MulOpposite.op_surjective g
  apply Subgroup.subset_closure
  refine ⟨orbitDeckClass x g, ⟨g, rfl⟩, ?_⟩
  change hp.fundamentalGroupToMulOpposite _
    (pathLoopClass (projectedOrbitDeckPath x g (orbitDeckPath x g))) = _
  exact fundamentalGroupToMulOpposite_projectedOrbitDeckPath hp x g (orbitDeckPath x g)

end SphereSixComplex.Geometry
