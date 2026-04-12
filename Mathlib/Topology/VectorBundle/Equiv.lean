/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Vector Bundle Homomorphisms and Equivalences

This file defines bundled continuous, fiberwise-linear maps between vector bundles
over possibly different base spaces.

A `VectorBundleHom` bundles a continuous map of total spaces with a family of linear
maps between fibers, covering a base map `baseMap : B₁ → B₂`. A `VectorBundleEquiv`
strengthens this to a homeomorphism of total spaces with fiberwise linear equivalences.

## Design notes

The base map `baseMap : B₁ → B₂` is stored as a field, even though it is determined
by the total space map (recovered by `baseMap_eq`). This is because `fiberLinearMap`
has type `∀ x, E₁ x →ₗ[𝕜] E₂ (baseMap x)`, which would become
`∀ x, E₁ x →ₗ[𝕜] E₂ ((toFun ⟨x, 0⟩).proj)` without the field — an unwieldy
dependent type. The constructor `mk'` derives the base map automatically for users
who prefer not to supply it.

## Main Definitions

* `VectorBundleHom 𝕜 F₁ E₁ F₂ E₂` : a continuous, fiberwise-linear map between
  vector bundles, covering a base map `baseMap : B₁ → B₂`.
* `VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂` : a homeomorphism of total spaces with fiberwise
  linear equivalences, covering a bijection of base spaces.
* `VectorBundleEquiv.ofFiberwiseLinearEquiv` : construct an equivalence from a family
  of fiberwise linear equivalences, given continuity of the induced total-space maps.
* `VectorBundleHom.toVectorBundleEquiv` : promote a bijective homomorphism to an
  equivalence, given that the base map is a homeomorphism.

## References

* [J. M. Lee, *Introduction to Smooth Manifolds*][lee2012] p. 261

## Tags

vector bundle, homomorphism, equivalence, isomorphism
-/

@[expose] public section

open Bundle

/-! ## Vector bundle homomorphisms -/

/-- A vector bundle homomorphism from `E₁` over `B₁` to `E₂` over `B₂`. -/
structure VectorBundleHom
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle homomorphism. -/
  baseMap : B₁ → B₂
  /-- The underlying continuous map between total spaces. -/
  toFun : TotalSpace F₁ E₁ → TotalSpace F₂ E₂
  /-- The total space map is continuous. -/
  continuous_toFun : Continuous toFun
  /-- A family of linear maps between the fibers. -/
  fiberLinearMap : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)
  /-- The map acts fiberwise via `fiberLinearMap`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toFun ⟨x, v⟩ = ⟨baseMap x, fiberLinearMap x v⟩

namespace VectorBundleHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleHom` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂) (hΦ : Continuous Φ)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toFun := Φ
  continuous_toFun := hΦ
  fiberLinearMap := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toFun = B.toFun) : A = B := by
  obtain ⟨f_A, Φ_A, _, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, _, φ_B, hB⟩ := B
  simp only at h
  subst h
  have hf : f_A = f_B := by
    ext x
    have h1 := hA x 0; have h2 := hB x 0
    simp only [map_zero] at h1 h2
    rw [h1] at h2
    exact congrArg TotalSpace.proj h2
  subst hf
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext x v
  have h1 := hA x v; rw [hB] at h1
  exact TotalSpace.mk_inj.mp h1.symm

instance : FunLike (VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe := toFun
  coe_injective' f g h := ext f g h

instance : ContinuousMapClass (VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous f := f.continuous_toFun

/-- The underlying `ContinuousMap` of a `VectorBundleHom`. -/
@[simps]
def toContinuousMap (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨f, f.continuous_toFun⟩

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    f.baseMap x = (f.toFun ⟨x, 0⟩).proj := by
  simp [f.fiber_compat, map_zero]

/-- The base map of a vector bundle homomorphism is continuous, since it factors as
`π₂ ∘ Φ ∘ zeroSection` and the zero section is continuous. -/
theorem continuous_baseMap
    [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
    [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) : Continuous f.baseMap := by
  have h : f.baseMap = TotalSpace.proj ∘ f.toFun ∘ zeroSection F₁ E₁ := by
    ext x; simp [baseMap_eq, zeroSection]
  rw [h]
  exact (FiberBundle.continuous_proj F₂ E₂).comp
    (f.continuous_toFun.comp (continuous_zeroSection 𝕜))

@[simp]
theorem proj_eq (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (f.toFun p).proj = f.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [f.fiber_compat]

@[simp]
theorem toFun_apply (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) (x : B₁) (v : E₁ x) :
    f.toFun ⟨x, v⟩ = ⟨f.baseMap x, f.fiberLinearMap x v⟩ :=
  f.fiber_compat x v

/-- The identity vector bundle homomorphism. -/
@[simps baseMap fiberLinearMap]
def id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toFun := _root_.id
  continuous_toFun := continuous_id
  fiberLinearMap _ := LinearMap.id
  fiber_compat _ _ := rfl

/-- Composition of vector bundle homomorphisms. -/
@[simps baseMap fiberLinearMap]
def comp (g : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃)
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := g.baseMap ∘ f.baseMap
  toFun := g.toFun ∘ f.toFun
  continuous_toFun := g.continuous_toFun.comp f.continuous_toFun
  fiberLinearMap x := (g.fiberLinearMap (f.baseMap x)).comp (f.fiberLinearMap x)
  fiber_compat x v := by
    simp only [Function.comp_apply, f.fiber_compat, g.fiber_compat]
    congr 1

@[simp]
theorem comp_id (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    f.comp id = f := ext _ _ rfl

@[simp]
theorem id_comp (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    id.comp f = f := ext _ _ rfl

theorem comp_assoc
    (h : VectorBundleHom 𝕜 F₃ E₃ F₁ E₁)
    (g : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃)
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    (h.comp g).comp f = h.comp (g.comp f) := ext _ _ rfl

@[simp]
theorem coe_id :
    ⇑(id : VectorBundleHom 𝕜 F₁ E₁ F₁ E₁) = _root_.id := rfl

@[simp]
theorem coe_comp (g : VectorBundleHom 𝕜 F₂ E₂ F₃ E₃)
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂) :
    ⇑(g.comp f) = ⇑g ∘ ⇑f := rfl

end VectorBundleHom

/-! ## Vector bundle equivalences -/

/-- A vector bundle equivalence between bundles `E₁` over `B₁` and `E₂` over `B₂`. -/
structure VectorBundleEquiv
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    {B₁ : Type*} [TopologicalSpace B₁] {B₂ : Type*} [TopologicalSpace B₂]
    (F₁ : Type*) [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    (E₁ : B₁ → Type*) [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)]
    (F₂ : Type*) [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    (E₂ : B₂ → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)] where
  /-- The base map covered by this bundle equivalence. -/
  baseMap : B₁ → B₂
  /-- The underlying homeomorphism between total spaces. -/
  toHomeomorph : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂
  /-- A family of linear equivalences between the fibers. -/
  fiberLinearEquiv : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ (baseMap x)
  /-- The homeomorphism acts fiberwise via `fiberLinearEquiv`. -/
  fiber_compat : ∀ (x : B₁) (v : E₁ x),
    toHomeomorph ⟨x, v⟩ = ⟨baseMap x, fiberLinearEquiv x v⟩

namespace VectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {B₃ : Type*} [TopologicalSpace B₃]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]
  {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {E₃ : B₃ → Type*} [∀ x, AddCommMonoid (E₃ x)] [∀ x, Module 𝕜 (E₃ x)]
  [TopologicalSpace (TotalSpace F₃ E₃)]

/-- Construct a `VectorBundleEquiv` without specifying the base map, deriving it as
`fun x => (Φ ⟨x, 0⟩).proj`. -/
def mk'
    (Φ : TotalSpace F₁ E₁ ≃ₜ TotalSpace F₂ E₂)
    (φ : ∀ x : B₁, E₁ x ≃ₗ[𝕜] E₂ ((Φ ⟨x, 0⟩).proj))
    (hcompat : ∀ (x : B₁) (v : E₁ x),
      Φ ⟨x, v⟩ = ⟨(Φ ⟨x, 0⟩).proj, φ x v⟩) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap x := (Φ ⟨x, 0⟩).proj
  toHomeomorph := Φ
  fiberLinearEquiv := φ
  fiber_compat := hcompat

@[ext]
theorem ext (A B : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (h : A.toHomeomorph = B.toHomeomorph) : A = B := by
  obtain ⟨f_A, Φ_A, φ_A, hA⟩ := A
  obtain ⟨f_B, Φ_B, φ_B, hB⟩ := B
  simp only at h; subst h
  have hf : f_A = f_B := by
    ext x
    have h₁ := hA x 0; have h₂ := hB x 0
    simp only [map_zero] at h₁ h₂
    rw [h₁] at h₂; exact congrArg TotalSpace.proj h₂
  subst hf; congr 1
  ext x v
  have h₁ := hA x v; rw [hB] at h₁
  exact TotalSpace.mk_inj.mp h₁.symm

instance : FunLike (VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  coe e := e.toHomeomorph
  coe_injective' f g h :=
    ext f g (Homeomorph.ext (congrFun h))

instance : ContinuousMapClass (VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (TotalSpace F₁ E₁) (TotalSpace F₂ E₂) where
  map_continuous e := e.toHomeomorph.continuous

/-- The underlying `ContinuousMap` of a `VectorBundleEquiv`. -/
@[simps]
def toContinuousMap (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    C(TotalSpace F₁ E₁, TotalSpace F₂ E₂) :=
  ⟨e, e.toHomeomorph.continuous⟩

/-- The base map equals the projection of the total space map on the zero section. -/
theorem baseMap_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (x : B₁) :
    e.baseMap x = (e.toHomeomorph ⟨x, 0⟩).proj := by
  simp [e.fiber_compat, map_zero]

/-- The base map of a vector bundle equivalence is bijective. -/
theorem baseMap_bijective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Bijective e.baseMap := by
  constructor
  · intro x₁ x₂ h
    have h₁ := e.fiber_compat x₁ 0
    have h₂ := e.fiber_compat x₂ 0
    simp only [map_zero] at h₁ h₂
    have hinj := e.toHomeomorph.injective (h₁.trans (by rw [h]) |>.trans h₂.symm)
    exact congrArg TotalSpace.proj hinj
  · intro y
    obtain ⟨⟨x, v⟩, hxv⟩ := e.toHomeomorph.surjective ⟨y, 0⟩
    have := e.fiber_compat x v
    rw [this] at hxv
    exact ⟨x, congrArg TotalSpace.proj hxv⟩

@[simp]
theorem proj_eq (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) (p : TotalSpace F₁ E₁) :
    (e.toHomeomorph p).proj = e.baseMap p.proj := by
  obtain ⟨x, v⟩ := p; simp [e.fiber_compat]

@[simp]
theorem toHomeomorph_apply (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (x : B₁) (v : E₁ x) :
    e.toHomeomorph ⟨x, v⟩ = ⟨e.baseMap x, e.fiberLinearEquiv x v⟩ :=
  e.fiber_compat x v

/-- A `VectorBundleEquiv` gives a `VectorBundleHom` in the forward direction. -/
@[simps baseMap fiberLinearMap]
def toVectorBundleHom (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := e.baseMap
  toFun := e.toHomeomorph
  continuous_toFun := e.toHomeomorph.continuous
  fiberLinearMap x := (e.fiberLinearEquiv x).toLinearMap
  fiber_compat x v := e.fiber_compat x v

/-- The identity vector bundle equivalence. -/
@[simps baseMap toHomeomorph fiberLinearEquiv]
def refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁ where
  baseMap := _root_.id
  toHomeomorph := Homeomorph.refl _
  fiberLinearEquiv x := LinearEquiv.refl 𝕜 (E₁ x)
  fiber_compat _ _ := rfl

/-- The inverse of a vector bundle equivalence. -/
def symm (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    VectorBundleEquiv 𝕜 F₂ E₂ F₁ E₁ where
  baseMap y := (e.toHomeomorph.symm ⟨y, 0⟩).proj
  toHomeomorph := e.toHomeomorph.symm
  fiberLinearEquiv y :=
    -- x := (Φ⁻¹ ⟨y, 0⟩).proj, and e.baseMap x = y
    let x := (e.toHomeomorph.symm ⟨y, 0⟩).proj
    have hx : e.baseMap x = y := by
      have := e.proj_eq (e.toHomeomorph.symm ⟨y, 0⟩)
      rw [e.toHomeomorph.apply_symm_apply] at this; exact this.symm
    (hx ▸ e.fiberLinearEquiv x).symm
  fiber_compat y v := by
    have key : ∀ (x : B₁) (hx : e.baseMap x = y),
        (⟨y, v⟩ : TotalSpace F₂ E₂) =
        ⟨e.baseMap x, e.fiberLinearEquiv x ((hx ▸ e.fiberLinearEquiv x).symm v)⟩ := by
      intro x hx; subst hx; simp [LinearEquiv.apply_symm_apply]
    apply e.toHomeomorph.injective
    rw [e.toHomeomorph.apply_symm_apply, e.toHomeomorph_apply]
    exact key _ _

/-- Composition of vector bundle equivalences. -/
def trans (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₃ E₃ where
  baseMap := e₂₃.baseMap ∘ e₁₂.baseMap
  toHomeomorph := e₁₂.toHomeomorph.trans e₂₃.toHomeomorph
  fiberLinearEquiv x :=
    (e₁₂.fiberLinearEquiv x).trans (e₂₃.fiberLinearEquiv (e₁₂.baseMap x))
  fiber_compat x v := by
    simp only [Homeomorph.trans_apply, e₁₂.fiber_compat, e₂₃.fiber_compat, Function.comp]
    congr 1

@[simp]
theorem refl_apply (p : TotalSpace F₁ E₁) :
    (refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁) p = p := rfl

@[simp]
theorem symm_apply_apply
    (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (p : TotalSpace F₁ E₁) :
    e.symm (e p) = p :=
  e.toHomeomorph.symm_apply_apply p

@[simp]
theorem apply_symm_apply
    (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (p : TotalSpace F₂ E₂) :
    e (e.symm p) = p :=
  e.toHomeomorph.apply_symm_apply p

@[simp]
theorem symm_symm (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    e.symm.symm = e :=
  ext _ _ (Homeomorph.ext (e.toHomeomorph.symm_symm ▸
    fun _ => rfl))

@[simp]
theorem symm_trans_self
    (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    e.symm.trans e = refl :=
  ext _ _ (Homeomorph.ext fun p =>
    e.toHomeomorph.apply_symm_apply p)

@[simp]
theorem self_trans_symm
    (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    e.trans e.symm = refl :=
  ext _ _ (Homeomorph.ext fun p =>
    e.toHomeomorph.symm_apply_apply p)

@[simp]
theorem trans_apply
    (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃)
    (p : TotalSpace F₁ E₁) :
    (e₁₂.trans e₂₃) p = e₂₃ (e₁₂ p) := rfl

@[simp]
theorem symm_apply (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (p : TotalSpace F₂ E₂) :
    e.symm p = e.toHomeomorph.symm p := rfl

theorem toVectorBundleHom_comp
    (e₁₂ : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂)
    (e₂₃ : VectorBundleEquiv 𝕜 F₂ E₂ F₃ E₃) :
    (e₁₂.trans e₂₃).toVectorBundleHom =
      e₂₃.toVectorBundleHom.comp e₁₂.toVectorBundleHom :=
  VectorBundleHom.ext _ _ rfl

@[simp]
theorem trans_refl (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    e.trans refl = e :=
  ext _ _ (Homeomorph.ext fun _ => rfl)

@[simp]
theorem refl_trans (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    refl.trans e = e :=
  ext _ _ (Homeomorph.ext fun _ => rfl)

theorem injective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Injective e :=
  e.toHomeomorph.injective

theorem surjective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Surjective e :=
  e.toHomeomorph.surjective

theorem bijective (e : VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂) :
    Function.Bijective e :=
  e.toHomeomorph.bijective

@[simp]
theorem toVectorBundleHom_id :
    toVectorBundleHom (refl : VectorBundleEquiv 𝕜 F₁ E₁ F₁ E₁)
      = VectorBundleHom.id :=
  VectorBundleHom.ext _ _ rfl

end VectorBundleEquiv

/-! ## Building equivalences from fiberwise data -/

section FiberwiseEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)]

/-- Package a fiberwise linear map family into a `VectorBundleHom`
covering an arbitrary base map, given a continuity proof for the
induced total-space map. -/
def VectorBundleHom.ofFiberwiseLinearMap
    {B₂ : Type*} [TopologicalSpace B₂]
    {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)]
      [∀ x, Module 𝕜 (E₂ x)]
    [TopologicalSpace (TotalSpace F₂ E₂)]
    (f : B → B₂)
    (φ : ∀ x : B, E₁ x →ₗ[𝕜] E₂ (f x))
    (h_cont : Continuous
      (fun p : TotalSpace F₁ E₁ =>
        (⟨f p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂))) :
    VectorBundleHom 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := f
  toFun p := ⟨f p.1, φ p.1 p.2⟩
  continuous_toFun := h_cont
  fiberLinearMap := φ
  fiber_compat _ _ := rfl

/-- Assemble a `VectorBundleEquiv` covering the identity from
two mutually-inverse `VectorBundleHom`s. Both directions of
continuity are supplied as input, so no finite-dimensional or
complete-space assumptions are needed. -/
noncomputable def VectorBundleEquiv.ofMutualInverseHoms
    (Φ : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (Ψ : VectorBundleHom 𝕜 F₂ E₂ F₁ E₁)
    (hΦ : Φ.baseMap = _root_.id)
    (hΨΦ : ∀ p, Ψ.toFun (Φ.toFun p) = p)
    (hΦΨ : ∀ p, Φ.toFun (Ψ.toFun p) = p) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  have hΨ : Ψ.baseMap = _root_.id := by
    funext y
    have h := congrArg TotalSpace.proj (hΦΨ ⟨y, 0⟩)
    rwa [Φ.proj_eq, Ψ.proj_eq, hΦ] at h
  match Φ, Ψ, hΦ, hΨ, hΨΦ, hΦΨ with
  | ⟨_, toFunΦ, hcΦ, φ, compatΦ⟩, ⟨_, toFunΨ, hcΨ, ψ, compatΨ⟩,
    rfl, rfl, hΨΦ, hΦΨ =>
    { baseMap := _root_.id
      toHomeomorph :=
        { toEquiv := ⟨toFunΦ, toFunΨ, hΨΦ, hΦΨ⟩
          continuous_toFun := hcΦ
          continuous_invFun := hcΨ }
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofLinear (φ x) (ψ x)
          (LinearMap.ext fun v => by
            have h := hΦΨ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
          (LinearMap.ext fun v => by
            have h := hΨΦ ⟨x, v⟩
            simp only [compatΦ, compatΨ] at h
            exact eq_of_heq (TotalSpace.mk.inj h).2)
      fiber_compat := compatΦ }

/-- Construct a `VectorBundleEquiv` covering the identity from
a fiberwise linear equivalence, together with continuity proofs
for the total-space maps induced by `φ` and `φ.symm`. -/
noncomputable def VectorBundleEquiv.ofFiberwiseLinearEquiv
    (φ : ∀ x : B, E₁ x ≃ₗ[𝕜] E₂ x)
    (h_cont : Continuous
      (fun p : TotalSpace F₁ E₁ =>
        (⟨p.1, φ p.1 p.2⟩ : TotalSpace F₂ E₂)))
    (h_cont_inv : Continuous
      (fun p : TotalSpace F₂ E₂ =>
        (⟨p.1, (φ p.1).symm p.2⟩ : TotalSpace F₁ E₁))) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ where
  baseMap := _root_.id
  toHomeomorph :=
    { toEquiv :=
        { toFun := fun p => ⟨p.1, φ p.1 p.2⟩
          invFun := fun p => ⟨p.1, (φ p.1).symm p.2⟩
          left_inv := fun ⟨_, _⟩ => by simp
          right_inv := fun ⟨_, _⟩ => by simp }
      continuous_toFun := h_cont
      continuous_invFun := h_cont_inv }
  fiberLinearEquiv := φ
  fiber_compat _ _ := rfl

end FiberwiseEquiv

/-! ## Trivialization Coordinates -/

section TrivializationCoord

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] in
/-- Given a family of fiberwise linear maps `φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)`
covering a base map `baseMap : B₁ → B₂`, and a base point `x : B₁`, the local representative
through the trivializations at `x` in `E₁` and at `baseMap x` in `E₂`: a continuous linear map
`F₁ →L[𝕜] F₂` defined on the overlap of base sets (and `0` otherwise). -/
noncomputable def trivializationCoord (baseMap : B₁ → B₂)
    (φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x))
    (x : B₁) : B₁ → (F₁ →L[𝕜] F₂) :=
  open Classical in fun q =>
  if hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
      baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet
  then
    let e₁ := (trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq.1
    let e₂ := (trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt 𝕜 (baseMap q) hq.2
    LinearMap.toContinuousLinearMap
      (e₂.toLinearMap.comp ((φ q).comp e₁.symm.toLinearMap))
  else 0

/-- Closed-form formula: the trivialization coordinate at `q` applied to `v` equals the
fiber coordinate of `Φ` on `e₁⁻¹ (q, v)` read through `e₂`. -/
lemma trivializationCoord_apply
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (x q : B₁)
    (hq₁ : q ∈ (trivializationAt F₁ E₁ x).baseSet)
    (hq₂ : baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet)
    (v : F₁) :
    trivializationCoord baseMap φ x q v =
      ((trivializationAt F₂ E₂ (baseMap x))
        (Φ ((trivializationAt F₁ E₁ x).toOpenPartialHomeomorph.symm (q, v)))).2 := by
  simp only [trivializationCoord,
    dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  conv_rhs =>
    rw [(trivializationAt F₁ E₁ x).symm_apply_eq_mk_continuousLinearEquivAt_symm
          (R := 𝕜) q hq₁ v,
        hcompat,
        congrArg Prod.snd
          ((trivializationAt F₂ E₂ (baseMap x)).apply_eq_prod_continuousLinearEquivAt
            𝕜 (baseMap q) hq₂ _)]
  rfl

/-- `trivializationCoord baseMap φ x q` is invertible on the overlap of the base sets
whenever each fiber map `φ q` is bijective. -/
lemma trivializationCoord_isInvertible
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x q : B₁)
    (hq : q ∈ (trivializationAt F₁ E₁ x).baseSet ∧
      baseMap q ∈ (trivializationAt F₂ E₂ (baseMap x)).baseSet) :
    (trivializationCoord baseMap φ x q : F₁ →L[𝕜] F₂).IsInvertible := by
  obtain ⟨hq₁, hq₂⟩ := hq
  simp only [trivializationCoord,
    dif_pos (show q ∈ _ ∧ baseMap q ∈ _ from ⟨hq₁, hq₂⟩)]
  have hbij_lm : Function.Bijective
      (((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
          𝕜 (baseMap q) hq₂).toLinearMap.comp
        ((φ q).comp
          ((trivializationAt F₁ E₁ x).continuousLinearEquivAt
            𝕜 q hq₁).symm.toLinearMap)) :=
    (((trivializationAt F₁ E₁ x).continuousLinearEquivAt 𝕜 q hq₁).symm.toLinearEquiv.trans
      (LinearEquiv.ofBijective (φ q) (hφ_bij q)) |>.trans
      ((trivializationAt F₂ E₂ (baseMap x)).continuousLinearEquivAt
        𝕜 (baseMap q) hq₂).toLinearEquiv).bijective
  exact ⟨(LinearEquiv.ofBijective _ hbij_lm).toContinuousLinearEquiv, by ext; rfl⟩

/-- On a neighborhood of `e₂ ⟨baseMap x, w⟩`, inverting
`trivializationCoord baseMap φ x` pointwise computes the second coordinate of
`e₁ ∘ Φ⁻¹ ∘ e₂⁻¹`. The base map is required to be a homeomorphism so that points
near `baseMap x` in `B₂` correspond, via the inverse, to points near `x` in `B₁`. -/
lemma trivializationCoord_inverse_eventuallyEq
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x))
    (x : B₁) (w : E₂ (baseMap x)) :
    (fun p : B₂ × F₂ =>
        ContinuousLinearMap.inverse
          (trivializationCoord baseMap φ x (baseMap.symm p.1)) p.2)
      =ᶠ[nhds ((trivializationAt F₂ E₂ (baseMap x)) ⟨baseMap x, w⟩)]
    (fun p : B₂ × F₂ => ((trivializationAt F₁ E₁ x)
      ((Equiv.ofBijective Φ hbij).symm
        ((trivializationAt F₂ E₂ (baseMap x)).toOpenPartialHomeomorph.symm p))).2) := by
  set e₁ := trivializationAt F₁ E₁ x
  set e₂ := trivializationAt F₂ E₂ (baseMap x)
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
  have hx₂ := mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
  have he₂_source : (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
    e₂.mem_source.mpr hx₂
  have hproj : ∀ p, (Φ_equiv.symm p).proj = baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p := Φ_equiv.apply_symm_apply p
    rw [hcompat (Φ_equiv.symm p).proj (Φ_equiv.symm p).snd] at h1
    have h := congrArg TotalSpace.proj h1
    simp only at h
    rw [← h, baseMap.symm_apply_apply]
  have hU : ((baseMap '' e₁.baseSet) ∩ e₂.baseSet) ×ˢ (Set.univ : Set F₂) ∈
      nhds (e₂ ⟨baseMap x, w⟩) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact ((baseMap.isOpenMap _ e₁.open_baseSet).inter e₂.open_baseSet).prod isOpen_univ
    · refine ⟨⟨⟨x, hx₁, ?_⟩, ?_⟩, Set.mem_univ _⟩
      · exact (e₂.coe_fst he₂_source).symm
      · exact e₂.coe_fst he₂_source ▸ hx₂
  filter_upwards [hU] with ⟨q', v⟩ ⟨⟨⟨q, hq₁, hq_eq⟩, hq₂'⟩, _⟩
  simp only at hq_eq hq₂'
  have hq : baseMap.symm q' = q := by rw [← hq_eq]; exact baseMap.symm_apply_apply q
  have hq₂ : baseMap (baseMap.symm q') ∈ e₂.baseSet := by
    rw [baseMap.apply_symm_apply]; exact hq₂'
  have hA_inv_q := trivializationCoord_isInvertible (baseMap := baseMap) hφ_bij x
    (baseMap.symm q') ⟨hq ▸ hq₁, hq₂⟩
  have hAG : trivializationCoord baseMap φ x (baseMap.symm q')
      ((e₁ (Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q', v)))).2) = v := by
    set p := Φ_equiv.symm (e₂.toOpenPartialHomeomorph.symm (q', v))
    have hp_proj : p.proj = baseMap.symm q' := by
      have h1 := hproj (e₂.toOpenPartialHomeomorph.symm (q', v))
      have h2 : (e₂.toOpenPartialHomeomorph.symm (q', v)).proj = q' :=
        e₂.proj_symm_apply (e₂.mem_target.mpr hq₂')
      rw [h2] at h1; exact h1
    have hp_mem : p ∈ e₁.source := e₁.mem_source.mpr (hp_proj ▸ hq ▸ hq₁)
    rw [trivializationCoord_apply hcompat x (baseMap.symm q') (hq ▸ hq₁) hq₂,
        show e₁.toOpenPartialHomeomorph.symm (baseMap.symm q', (e₁ p).2) = p from by
          conv_rhs => rw [← e₁.toOpenPartialHomeomorph.left_inv hp_mem]
          congr 1; exact Prod.ext (e₁.coe_fst hp_mem ▸ hp_proj).symm rfl,
        show Φ p = e₂.toOpenPartialHomeomorph.symm (q', v) from
          Φ_equiv.apply_symm_apply _,
        congrArg Prod.snd (e₂.apply_symm_apply' hq₂')]
  exact hA_inv_q.inverse_apply_eq.mpr hAG.symm

end TrivializationCoord

/-! ## Bijective bundle homomorphisms are equivalences -/

section ToVectorBundleEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B₁ : Type*} [TopologicalSpace B₁]
  {B₂ : Type*} [TopologicalSpace B₂]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B₁ → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B₂ → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] in
/-- If a fiberwise-linear bijection of total spaces covers a base map and acts as
`⟨x, v⟩ ↦ ⟨baseMap x, φ x v⟩`, then each fiber map `φ x` is bijective. The base map
itself need not be assumed bijective — it follows from `Φ` being bijective. -/
lemma fiberBijective_of_bijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    {baseMap : B₁ → B₂}
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ)
    (hbase_inj : Function.Injective baseMap)
    (x : B₁) :
    Function.Bijective (φ x) := by
  refine ⟨fun v w hvw => TotalSpace.mk_inj.mp
    (hbij.1 (by rw [hcompat x v, hcompat x w, hvw])), fun w => ?_⟩
  obtain ⟨⟨y, v⟩, hv⟩ := hbij.2 (⟨baseMap x, w⟩ : TotalSpace F₂ E₂)
  rw [hcompat y v] at hv
  have hy : y = x := hbase_inj (congrArg TotalSpace.proj hv)
  subst hy
  exact ⟨v, TotalSpace.mk_inj.mp hv⟩

/-- Pointwise continuity of a continuous-linear-map-valued map lifts to continuity when
the source is finite-dimensional, by embedding `F₁ →L[𝕜] F₂` into
`Fin (rank F₁) → F₂` via evaluation on a basis (a closed embedding in the
finite-dimensional setting).
TODO: move to `Mathlib.Topology.Algebra.Module.FiniteDimension`. -/
lemma continuousAt_clm_of_pointwise
    {X : Type*} [TopologicalSpace X]
    {A : X → (F₁ →L[𝕜] F₂)} {x : X}
    (h : ∀ v, ContinuousAt (fun q => A q v) x) :
    ContinuousAt A x := by
  haveI : FiniteDimensional 𝕜 (F₁ →L[𝕜] F₂) := ContinuousLinearMap.finiteDimensional
  let bF₁ := Module.finBasis 𝕜 F₁
  let evalBasis : (F₁ →L[𝕜] F₂) →L[𝕜] (Fin (Module.finrank 𝕜 F₁) → F₂) :=
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply 𝕜 F₂ (bF₁ i))
  have evalBasis_inj : Function.Injective evalBasis := fun L₁ L₂ heq => by
    ext v; rw [← bF₁.sum_equivFun v]; simp only [map_sum, map_smul]
    congr 1; ext i; exact congrArg _ (congrFun heq i)
  rw [(LinearMap.isClosedEmbedding_of_injective (f := evalBasis.toLinearMap)
    (LinearMap.ker_eq_bot.mpr evalBasis_inj)).isEmbedding.continuousAt_iff]
  exact continuousAt_pi.mpr fun i => h (bF₁ i)

/-- The inverse of a fiberwise-linear, fiberwise-bijective continuous bijection between
vector bundles over different bases is continuous, provided the base map is a
homeomorphism. The proof is local: through trivializations at a point, the transition map
is a family of continuous linear isomorphisms `A : B₁ → (F₁ →L[𝕜] F₂)`, continuous
in the parameter, so its pointwise inverse is also continuous by
`ContinuousLinearMap.inverse`. -/
lemma continuous_symm_of_fiberBijective'
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂}
    (hΦ_cont : Continuous Φ)
    (baseMap : B₁ ≃ₜ B₂)
    {φ : ∀ x : B₁, E₁ x →ₗ[𝕜] E₂ (baseMap x)}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨baseMap x, φ x v⟩)
    (hbij : Function.Bijective Φ)
    (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm := by
  set Φ_equiv := Equiv.ofBijective Φ hbij
  have hproj : ∀ p, (Φ_equiv.symm p).proj =
      baseMap.symm p.proj := fun p => by
    have h1 : Φ (Φ_equiv.symm p) = p :=
      Φ_equiv.apply_symm_apply p
    rw [hcompat] at h1
    rw [← congrArg TotalSpace.proj h1,
      baseMap.symm_apply_apply]
  rw [continuous_iff_continuousAt]
  rintro ⟨y, w⟩
  obtain ⟨x, rfl⟩ : ∃ x, baseMap x = y :=
    ⟨baseMap.symm y, baseMap.apply_symm_apply y⟩
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨?_, ?_⟩
  · simp only [hproj]
    exact (baseMap.symm.continuous.comp
      (FiberBundle.continuous_proj F₂ E₂)).continuousAt
  · simp only [hproj, Homeomorph.symm_apply_apply]
    set e₁ := trivializationAt F₁ E₁ x
    set e₂ := trivializationAt F₂ E₂ (baseMap x)
    have hx₁ := mem_baseSet_trivializationAt F₁ E₁ x
    have hx₂ :=
      mem_baseSet_trivializationAt F₂ E₂ (baseMap x)
    have he₂_source :
        (⟨baseMap x, w⟩ : TotalSpace F₂ E₂) ∈ e₂.source :=
      e₂.mem_source.mpr hx₂
    set A : B₁ → (F₁ →L[𝕜] F₂) :=
      trivializationCoord baseMap φ x with hA_def
    have hΦ_proj : ∀ p, (Φ p).proj = baseMap p.proj :=
      fun ⟨_, _⟩ => by simp [hcompat]
    have hA_cont : ContinuousAt A x := by
      apply continuousAt_clm_of_pointwise
      intro v
      suffices h : ContinuousAt
          (fun q => (e₂ (Φ
            (e₁.toOpenPartialHomeomorph.symm (q, v)))).2) x by
        refine h.congr (Filter.eventually_of_mem
          (IsOpen.mem_nhds (e₁.open_baseSet.inter
            (baseMap.continuous.isOpen_preimage _
              e₂.open_baseSet)) ⟨hx₁, ?_⟩) ?_)
        · exact hx₂
        · intro q ⟨hq₁, hq₂⟩
          exact (trivializationCoord_apply
            hcompat x q hq₁ hq₂ v).symm
      have he₁_tgt : (x, v) ∈ e₁.target := by
        rw [e₁.target_eq]; exact ⟨hx₁, Set.mem_univ _⟩
      set oph := e₁.toOpenPartialHomeomorph
      have he₁_symm_cont : ContinuousAt
          (fun q => oph.symm (q, v)) x := by
        refine ContinuousAt.comp ?_
          (ContinuousAt.prodMk continuousAt_id
            continuousAt_const)
        exact oph.continuousOn_symm.continuousAt
          (oph.open_target.mem_nhds he₁_tgt)
      have hpΦ :
          Φ (e₁.toOpenPartialHomeomorph.symm (x, v)) ∈
            e₂.source := by
        rw [e₂.mem_source, hΦ_proj,
          e₁.proj_symm_apply he₁_tgt]
        exact hx₂
      have he₂_at := e₂.continuousOn.continuousAt
        (e₂.open_source.mem_nhds hpΦ)
      have hcomp1 : ContinuousAt (fun q =>
          Φ (e₁.toOpenPartialHomeomorph.symm (q, v))) x := by
        exact ContinuousAt.comp hΦ_cont.continuousAt
          he₁_symm_cont
      have hcomp2 : ContinuousAt (fun q =>
          e₂ (Φ (e₁.toOpenPartialHomeomorph.symm (q, v))))
          x := by
        exact ContinuousAt.comp he₂_at hcomp1
      exact hcomp2.snd
    haveI : CompleteSpace F₁ :=
      FiniteDimensional.complete 𝕜 F₁
    have hA_inv_at_x :
        (A x : F₁ →L[𝕜] F₂).IsInvertible :=
      trivializationCoord_isInvertible
        (baseMap := baseMap) hφ_bij x x ⟨hx₁, hx₂⟩
    have hA_inv_cont :
        ContinuousAt (ContinuousLinearMap.inverse ∘ A) x :=
      (hA_inv_at_x.contDiffAt_map_inverse
        (n := 0)).continuousAt.comp hA_cont
    have hNice_cont : ContinuousAt
        (fun p : B₂ × F₂ => ContinuousLinearMap.inverse
          (A (baseMap.symm p.1)) p.2)
        (e₂ ⟨baseMap x, w⟩) := by
      have h1 : ContinuousAt
          (fun p : B₂ × F₂ => ContinuousLinearMap.inverse
            (A (baseMap.symm p.1)))
          (e₂ ⟨baseMap x, w⟩) := by
        have : ContinuousAt
            ((ContinuousLinearMap.inverse ∘ A) ∘
              (baseMap.symm ∘ Prod.fst))
            (e₂ ⟨baseMap x, w⟩) := by
          refine ContinuousAt.comp ?_
            (baseMap.symm.continuous.continuousAt.comp
              continuousAt_fst)
          convert hA_inv_cont using 1
          simp [e₂.coe_fst he₂_source]
        exact this
      exact h1.clm_apply continuousAt_snd
    exact ((hNice_cont.congr
      (trivializationCoord_inverse_eventuallyEq
        baseMap hcompat hbij hφ_bij x w)).comp
      (e₂.toOpenPartialHomeomorph.continuousAt
        he₂_source)).congr
      (by filter_upwards [e₂.open_source.mem_nhds
            he₂_source] with p hp
          exact congrArg (fun q => (e₁ (Φ_equiv.symm q)).2)
            (e₂.toOpenPartialHomeomorph.left_inv hp))

/-- A bijective vector bundle homomorphism whose base map is a homeomorphism is a vector
bundle equivalence. The base map being a homeomorphism cannot be derived from bijectivity of
the total-space map alone. See `toVectorBundleEquivId` for the identity-base special case. -/
noncomputable def VectorBundleHom.toVectorBundleEquiv
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (baseMap : B₁ ≃ₜ B₂)
    (hbase : f.baseMap = baseMap)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  match f, hbase, hbij with
  | ⟨_, Φ, hΦ_cont, φ, hcompat⟩, rfl, hbij =>
    let hφ_bij := fiberBijective_of_bijective'
      hcompat hbij baseMap.injective
    { baseMap := baseMap
      toHomeomorph := ⟨Equiv.ofBijective Φ hbij, hΦ_cont,
        continuous_symm_of_fiberBijective' hΦ_cont baseMap
          hcompat hbij hφ_bij⟩
      fiberLinearEquiv := fun x =>
        LinearEquiv.ofBijective (φ x) (hφ_bij x)
      fiber_compat := hcompat }

end ToVectorBundleEquiv

/-! ### Identity base map specialization -/

section ToVectorBundleEquivId

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [FiniteDimensional 𝕜 F₁]
  {E₁ : B → Type*} [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [FiniteDimensional 𝕜 F₂]
  {E₂ : B → Type*} [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]

/-- The inverse of a fiberwise-linear, fiberwise-bijective continuous bijection between
vector bundles over the same base (with identity base map) is continuous. This is the
special case of `continuous_symm_of_fiberBijective'` with `Homeomorph.refl B`. -/
lemma continuous_symm_of_fiberBijective
    {Φ : TotalSpace F₁ E₁ → TotalSpace F₂ E₂} (hΦ_cont : Continuous Φ)
    {φ : ∀ x, E₁ x →ₗ[𝕜] E₂ x}
    (hcompat : ∀ x v, Φ ⟨x, v⟩ = ⟨x, φ x v⟩)
    (hbij : Function.Bijective Φ) (hφ_bij : ∀ x, Function.Bijective (φ x)) :
    Continuous (Equiv.ofBijective Φ hbij).symm :=
  continuous_symm_of_fiberBijective' hΦ_cont (Homeomorph.refl B) hcompat hbij hφ_bij

/-- Special case of `VectorBundleHom.toVectorBundleEquiv` for the identity base map. -/
noncomputable def VectorBundleHom.toVectorBundleEquivId
    (f : VectorBundleHom 𝕜 F₁ E₁ F₂ E₂)
    (hid : f.baseMap = _root_.id)
    (hbij : Function.Bijective f.toFun) :
    VectorBundleEquiv 𝕜 F₁ E₁ F₂ E₂ :=
  f.toVectorBundleEquiv (Homeomorph.refl B) hid hbij

end ToVectorBundleEquivId

end
