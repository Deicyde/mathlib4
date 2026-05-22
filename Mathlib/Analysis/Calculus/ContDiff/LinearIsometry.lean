/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# `C^n`-smoothness through a linear isometric embedding

For `Φ : E →ₗᵢ[𝕜] F` with `E` complete, postcomposing with `Φ` preserves and reflects
`C^n`-smoothness for `n : ℕ∞`. This is the Banach generalization of
`ContinuousLinearMap.contDiff_comp_iff` (`FiniteDimension.lean`) at non-analytic smoothness
levels: the FD codomain hypothesis there is replaced by completeness of the domain here.

The argument: `range Φ` is closed (isometric embedding) and `Φ` is a topological isomorphism
onto it. Every Fréchet derivative of `Φ ∘ f` lands in `range Φ` (closed limits of difference
quotients) and pulls back through `Φ.equivRange.symm`. We iterate by induction on smoothness
order, recursing into the operator-level postcomposition
`Φ.postcomp : (G →L[𝕜] E) →ₗᵢ[𝕜] (G →L[𝕜] F)`.

The analytic case `n = ω` is not handled here. The induction never reaches `ω` (finite at every
step), and an alternative Faà-di-Bruno-style direct construction would need to extract
off-diagonal multilinear coefficients from a power series, which requires `1/n!` in
characteristic `p ≤ n`.

## Main results

* `LinearIsometry.hasFDerivAt_of_comp`: extract a Fréchet derivative of `f` from one of `Φ ∘ f`.
* `LinearIsometry.contDiff_comp_iff_of_completeSpace`: for `n : ℕ∞`, `Φ ∘ f` is `C^n` iff `f`
  is `C^n`.
* `ContinuousLinearMap.contDiff_comp_iff_of_isometry_completeSpace`: CLM-flavored version.
-/

public section

noncomputable section

open Set Function Filter
open scoped ContDiff

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace LinearIsometry

/-! ### Fréchet derivative extraction -/

variable [CompleteSpace E]

/-- For a linear isometry `Φ : E →ₗᵢ[𝕜] F` with `E` complete, every Fréchet derivative of `Φ ∘ f`
factors through `Φ`. -/
theorem hasFDerivAt_of_comp (Φ : E →ₗᵢ[𝕜] F)
    {f : G → E} {L : G →L[𝕜] F} {x : G}
    (h : HasFDerivAt (⇑Φ ∘ f) L x) :
    ∃ M : G →L[𝕜] E, HasFDerivAt f M x ∧ Φ.toContinuousLinearMap.comp M = L := by
  have hrange : IsClosed (LinearMap.range Φ.toLinearMap : Set F) :=
    Φ.isometry.isClosedEmbedding.isClosed_range
  -- Every value of `L` lies in `range Φ`, via `HasFDerivAt.lim`.
  have hL_mem : ∀ v, L v ∈ LinearMap.range Φ.toLinearMap := by
    intro v
    obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm 𝕜
    have hcn : Tendsto (fun n : ℕ ↦ ‖c ^ n‖) atTop atTop := by
      simpa [norm_pow] using tendsto_pow_atTop_atTop_of_one_lt hc
    refine hrange.mem_of_tendsto (h.lim v hcn) (.of_forall fun n ↦ ?_)
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ ⟨f _, rfl⟩ ⟨f x, rfl⟩)
  -- Codomain-restrict `L` to `range Φ`, then transport back to `E` via `Φ.equivRange.symm`.
  let L' : G →L[𝕜] LinearMap.range Φ.toLinearMap := L.codRestrict _ hL_mem
  let M : G →L[𝕜] E :=
    Φ.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp L'
  have hΦM : ∀ δ, Φ (M δ) = L δ := fun δ ↦ by
    have h1 : Φ.equivRange (Φ.equivRange.symm (L' δ)) = L' δ :=
      Φ.equivRange.apply_symm_apply _
    exact congrArg (Subtype.val : LinearMap.range Φ.toLinearMap → F) h1
  refine ⟨M, ?_, by ext δ; exact hΦM δ⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at h ⊢
  have heq : ∀ η, ‖f (x + η) - f x - M η‖ = ‖(⇑Φ ∘ f) (x + η) - (⇑Φ ∘ f) x - L η‖ := fun η ↦ by
    rw [← Φ.norm_map (f (x + η) - f x - M η)]
    simp [Function.comp_apply, map_sub, hΦM]
  simpa [Asymptotics.isLittleO_iff, heq] using h

/-! ### Main result -/

/-- Postcomposition with a linear isometry from a complete normed space reflects `C^k`-smoothness
for natural numbers `k`. Stated at a single universe because the structural recursion calls back
into the lemma at the operator-level postcomposition `Ψ.postcomp`. -/
private theorem contDiff_natCast_of_comp.{u} : ∀ (k : ℕ)
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E₀ F₀ G₀ : Type u} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [NormedSpace 𝕜 F₀]
    [NormedAddCommGroup G₀] [NormedSpace 𝕜 G₀] [CompleteSpace E₀]
    (Ψ : E₀ →ₗᵢ[𝕜] F₀) {g : G₀ → E₀},
    ContDiff 𝕜 (k : WithTop ℕ∞) (⇑Ψ ∘ g) → ContDiff 𝕜 (k : WithTop ℕ∞) g
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, Ψ, _, h => by
    rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 from rfl, contDiff_zero] at h ⊢
    exact Ψ.isometry.isClosedEmbedding.isInducing.continuous_iff.mpr h
  | k + 1, _, _, E₀, F₀, G₀, _, _, _, _, _, _, _, Ψ, g, h => by
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiff_succ_iff_fderiv] at h ⊢
    obtain ⟨hd, _, hfderiv⟩ := h
    have hg_diff : Differentiable _ g := fun x ↦
      (Ψ.hasFDerivAt_of_comp (hd x).hasFDerivAt).choose_spec.1.differentiableAt
    refine ⟨hg_diff, fun h_ω ↦ absurd h_ω WithTop.coe_ne_top, ?_⟩
    have h_chain : fderiv _ (⇑Ψ ∘ g) = ⇑(Ψ.postcomp : (G₀ →L[_] E₀) →ₗᵢ[_] _) ∘ fderiv _ g := by
      funext x
      exact (Ψ.toContinuousLinearMap.hasFDerivAt.comp x (hg_diff x).hasFDerivAt).fderiv
    rw [h_chain] at hfderiv
    exact contDiff_natCast_of_comp k _ hfderiv

/-- Postcomposition with a linear isometry from a complete normed space preserves and reflects
`C^n`-smoothness for `n : ℕ∞`. This is the Banach-generality version of
`ContinuousLinearMap.contDiff_comp_iff` at non-analytic smoothness levels.

The analytic case `n = ω` is excluded: see the file-level docstring. -/
theorem contDiff_comp_iff_of_completeSpace.{uE, uF, uG, uK}
    {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type uG} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {n : ℕ∞} (Φ : E →ₗᵢ[𝕜] F) {f : G → E} :
    ContDiff 𝕜 (n : WithTop ℕ∞) (⇑Φ ∘ f) ↔ ContDiff 𝕜 (n : WithTop ℕ∞) f := by
  refine ⟨fun h ↦ ?_, fun h ↦ Φ.toContinuousLinearMap.contDiff.comp h⟩
  rw [contDiff_iff_forall_nat_le] at h ⊢
  intro k hk
  -- Lift `E`, `F`, `G` to a common universe so the same-universe helper applies.
  let Eu : Type max uE uF uG := ULift.{max uF uG, uE} E
  let Fu : Type max uE uF uG := ULift.{max uE uG, uF} F
  let Gu : Type max uE uF uG := ULift.{max uE uF, uG} G
  let isoE : Eu ≃ₗᵢ[𝕜] E := LinearIsometryEquiv.ulift 𝕜 E
  let isoF : Fu ≃ₗᵢ[𝕜] F := LinearIsometryEquiv.ulift 𝕜 F
  let isoG : Gu ≃ₗᵢ[𝕜] G := LinearIsometryEquiv.ulift 𝕜 G
  let Φu : Eu →ₗᵢ[𝕜] Fu :=
    isoF.symm.toLinearIsometry.comp (Φ.comp isoE.toLinearIsometry)
  let fu : Gu → Eu := isoE.symm ∘ f ∘ isoG
  -- Transfer `Φ ∘ f` is `C^k` to the ULift version.
  have h_eq : isoF.symm ∘ (⇑Φ ∘ f) ∘ isoG = ⇑Φu ∘ fu := by funext x; simp [Φu, fu]
  have h_lift : ContDiff 𝕜 (k : WithTop ℕ∞) (⇑Φu ∘ fu) := by
    rw [← h_eq]
    exact (isoG.toContinuousLinearEquiv.contDiff_comp_iff).mpr
      (isoF.symm.toContinuousLinearEquiv.comp_contDiff_iff.mpr (h k hk))
  have h_fu : ContDiff 𝕜 (k : WithTop ℕ∞) fu := contDiff_natCast_of_comp k Φu h_lift
  -- Transfer back to `f`.
  have h_fu_eq : isoE ∘ fu ∘ isoG.symm = f := by funext x; simp [fu]
  rw [← h_fu_eq]
  exact (isoG.symm.toContinuousLinearEquiv.contDiff_comp_iff).mpr
    (isoE.toContinuousLinearEquiv.comp_contDiff_iff.mpr h_fu)

end LinearIsometry

namespace ContinuousLinearMap

/-- Postcomposition with an isometric continuous linear map from a complete normed space preserves
and reflects `C^n`-smoothness for `n : ℕ∞`. CLM-flavored version of
`LinearIsometry.contDiff_comp_iff_of_completeSpace`. -/
theorem contDiff_comp_iff_of_isometry_completeSpace [CompleteSpace E]
    (Φ : E →L[𝕜] F) (hΦ : ∀ x, ‖Φ x‖ = ‖x‖) {f : G → E} {n : ℕ∞} :
    ContDiff 𝕜 (n : WithTop ℕ∞) (⇑Φ ∘ f) ↔ ContDiff 𝕜 (n : WithTop ℕ∞) f :=
  ({ toLinearMap := Φ.toLinearMap, norm_map' := hΦ } :
    E →ₗᵢ[𝕜] F).contDiff_comp_iff_of_completeSpace

end ContinuousLinearMap
