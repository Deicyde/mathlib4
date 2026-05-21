/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-! # The vector bundle of continuous alternating maps is `C^n`

We show that the bundle of continuous alternating maps between two `C^n` vector bundles over a
common base is again a `C^n` vector bundle, parallel to what
`Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` does for the bundle of continuous linear maps.

The topological vector bundle structure on `fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x` is provided by
`Mathlib/Topology/VectorBundle/ContinuousAlternatingMap.lean`.

## Implementation notes

We restrict the smoothness exponent to `n : ℕ∞` (excluding the analytic case `n = ω`). The reason
is that smoothness of the coordinate change reduces to the fact that
`p ↦ ContinuousAlternatingMap.compContinuousLinearMapCLM p` is `C^n` as a function of `p`. The
proof in `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff` (in
`Mathlib/Analysis/Calculus/ContDiff/ContinuousAlternatingMap.lean`) factors through the
`LinearIsometry` embedding of alternating maps into multilinear maps and pulls back smoothness
via `LinearIsometry.contDiff_comp_iff_of_completeSpace`, which is established at non-analytic
smoothness levels for Banach codomains.

The analytic case `n = ω` is excluded because it requires extracting off-diagonal multilinear
coefficients from a power series, which in turn requires `1/n!` (or a continuous projection onto
the alternating subspace) — fails in characteristic `p` whenever `p ≤ Fintype.card ι`.
-/

public section

noncomputable section

open Bundle Set Bundle.Pretrivialization ContinuousAlternatingMap

open scoped Manifold Bundle Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]

variable {B F₁ F₂ : Type*} {n : ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [CompleteSpace F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [ContMDiffVectorBundle (n : WithTop ℕ∞) F₁ E₁ IB]
  [ContMDiffVectorBundle (n : WithTop ℕ∞) F₂ E₂ IB]

theorem Bundle.contMDiffOn_continuousAlternatingMapCoordChange
    {e₁ e₁' : Trivialization F₁ (π F₁ E₁)} {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) (n : WithTop ℕ∞)
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := (n : WithTop ℕ∞))
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := (n : WithTop ℕ∞))
  refine (h₁.mono ?_).cle_continuousAlternatingMapCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

/-- The prebundle of continuous alternating maps is `C^n`-smooth. -/
instance Bundle.ContinuousAlternatingMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle (𝕜 := 𝕜) (ι := ι)
      (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)).IsContMDiff IB (n : WithTop ℕ∞) where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Bundle.Pretrivialization.continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      Bundle.contMDiffOn_continuousAlternatingMapCoordChange,
      Bundle.Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- If `E₁` and `E₂` are `C^n` vector bundles, then the bundle of continuous `ι`-slot
alternating maps from `E₁` to `E₂` is also a `C^n` vector bundle. -/
instance ContMDiffVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle (n : WithTop ℕ∞) (F₁ [⋀^ι]→L[𝕜] F₂)
      (fun x ↦ E₁ x [⋀^ι]→L[𝕜] E₂ x) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle (𝕜 := 𝕜) (ι := ι)
    (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)).contMDiffVectorBundle IB

end
