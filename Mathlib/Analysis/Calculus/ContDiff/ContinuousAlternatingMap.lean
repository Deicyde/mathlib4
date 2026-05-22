/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.ContinuousMultilinearMap
public import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Smoothness of operations on continuous alternating maps

The pullback operator `compContinuousLinearMapCLM`, sending a continuous linear map
`p : E →L[𝕜] E'` to its action `Φ ↦ Φ ∘ p^{⊗ι}` on continuous `ι`-linear alternating maps, is
`C^∞`. In `[CharZero 𝕜]` we get the stronger statement that it is `C^ω` (analytic), obtained
by writing this degree-`Fintype.card ι` polynomial as the diagonal of an explicit continuous
multilinear lift via the polarization formula.

## Main results

* `ContinuousAlternatingMap.contDiff`: continuous alternating maps are `C^n`.
* `ContinuousMultilinearMap.alternatizationCLM`: the `AddMonoidHom` `alternatization` from
  Mathlib upgraded to a `ContinuousLinearMap`.
* `ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff`: `compContinuousLinearMapCLM`
  is `C^n` for all `n : WithTop ℕ∞`.
-/

public section

open ContinuousAlternatingMap ContinuousMultilinearMap
open scoped ContDiff

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞}

theorem ContinuousAlternatingMap.contDiff (f : E [⋀^ι]→L[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousMultilinearMap.contDiff

/-! ### Continuous-linear alternatization -/

section Alternatization

variable [DecidableEq ι]

/-- Continuous-linear-map upgrade of `ContinuousMultilinearMap.alternatization`, which Mathlib
provides only as an `AddMonoidHom`. The norm bound is `(Fintype.card ι)!`, attained by the sum
over `Equiv.Perm ι` where each summand `±1 • domDomCongr σ f` has norm `‖f‖`. -/
noncomputable def ContinuousMultilinearMap.alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := fun f g ↦ (ContinuousMultilinearMap.alternatization
        (R := 𝕜) (M := E) (N := F) (ι := ι)).map_add f g
      map_smul' c f := by
        ext v
        change (alternatization (c • f)) v = c • alternatization f v
        rw [alternatization_apply_apply, alternatization_apply_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun σ _ ↦ ?_
        rw [show (c • f) (v ∘ σ) = c • f (v ∘ σ) from rfl, smul_comm] }
    ⟨(Fintype.card ι).factorial, fun f ↦ by
      rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      change ‖∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • f.domDomCongr σ‖ ≤ _
      refine (norm_sum_le _ _).trans ?_
      rw [show ((Fintype.card ι).factorial : ℝ) * ‖f‖ = ∑ _σ : Equiv.Perm ι, ‖f‖ by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun σ _ ↦ ?_
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsgn | hsgn <;>
        simp [hsgn, Units.neg_smul, ContinuousMultilinearMap.norm_domDomCongr]⟩

end Alternatization

/-! ### Smoothness of `compContinuousLinearMapCLM` -/

variable [CompleteSpace F] [CharZero 𝕜]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']

section Polarization

variable [DecidableEq ι]

/-- The polarized continuous multilinear lift of `compContinuousLinearMapCLM`, whose diagonal at
`(p, p, …, p)` recovers `compContinuousLinearMapCLM p`. Built by post-composing the multi-target
version (`compContinuousLinearMapContinuousMultilinear`) with `alternatizationCLM`, scaled by
`(1/k!)` where `k = Fintype.card ι`. -/
private noncomputable def compContinuousLinearMapPolarized :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E →L[𝕜] E')
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  let pre : (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :=
    (ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)).flip
      (toContinuousMultilinearMapCLM 𝕜)
  let post : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
    ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (E [⋀^ι]→L[𝕜] F)
      (alternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (F := F))
  ((Fintype.card ι).factorial : 𝕜)⁻¹ • (post ∘L pre).compContinuousMultilinearMap
    (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      𝕜 (fun _ : ι ↦ E) (fun _ : ι ↦ E') F)

omit [CompleteSpace F] in
private theorem compContinuousLinearMapPolarized_diag (p : E →L[𝕜] E') :
    compContinuousLinearMapPolarized (E := E) (E' := E') (F := F) (ι := ι) (fun _ ↦ p) =
      compContinuousLinearMapCLM p := by
  classical
  ext Φ v
  -- The polarized sum at the diagonal collapses: each summand `sgn σ • Φ(p · (v ∘ σ))` equals
  -- `Φ(p · v)` (using `Φ`'s alternation in `v` and `sgn σ * sgn σ = 1`), so the sum over
  -- `Equiv.Perm ι` equals `k! • Φ(p · v)`, cancelling the `(1/k!)` factor.
  change ((Fintype.card ι).factorial : 𝕜)⁻¹ •
      alternatization (Φ.toContinuousMultilinearMap.compContinuousLinearMap (fun _ ↦ p)) v =
      Φ (fun i ↦ p (v i))
  have hperm (σ : Equiv.Perm ι) :
      Equiv.Perm.sign σ • Φ.toContinuousMultilinearMap.compContinuousLinearMap
        (fun _ : ι ↦ p) (v ∘ σ) = Φ (fun i ↦ p (v i)) := by
    change Equiv.Perm.sign σ • Φ ((fun i ↦ p (v i)) ∘ σ) = _
    rw [show Φ ((fun i ↦ p (v i)) ∘ σ) = Φ.toAlternatingMap ((fun i ↦ p (v i)) ∘ σ) from rfl,
      Φ.toAlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
    rfl
  rw [alternatization_apply_apply, Finset.sum_congr rfl (fun σ _ ↦ hperm σ), Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, ← Nat.cast_smul_eq_nsmul (R := 𝕜), smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)), one_smul]

end Polarization

omit [CompleteSpace F] in
theorem ContinuousAlternatingMap.compContinuousLinearMapCLM_contDiff :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  classical
  have heq : (compContinuousLinearMapCLM
      (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)) =
      compContinuousLinearMapPolarized ∘ fun p : E →L[𝕜] E' ↦ (fun _ : ι ↦ p) :=
    funext fun p ↦ (compContinuousLinearMapPolarized_diag p).symm
  rw [heq]
  exact (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.mpr fun _ ↦ contDiff_id)
