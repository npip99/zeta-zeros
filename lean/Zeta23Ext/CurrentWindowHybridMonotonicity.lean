/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.CurrentWindowFiniteCertificate

/-!
# Hybrid monotonicity certificates

Near the origin the second derivative has a comfortable negative margin;
farther out the first derivative itself has a large negative margin.  A
hybrid finite cover exploits both facts and can be dramatically smaller than
a uniform first-derivative grid.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.CurrentWindowHybridMonotonicity

open CurrentWindow
open CurrentWindowAdmissibility
open CurrentWindowFiniteCertificate

/-- A finite cover proving `v'' ≤ 0` up to a junction, followed by a finite
cover proving `v' ≤ 0` from the junction to `1/2`. -/
structure Certificate (nSecond nFirst : ℕ) where
  junction : ℝ
  junction_mem : junction ∈ Icc (0 : ℝ) (1 / 2)
  secondCells : Fin nSecond → DerivativeCell
  secondUpper : ∀ i,
    deriv (deriv window) (secondCells i).center +
      jerkBound * (secondCells i).radius ≤ 0
  secondCover : ∀ s ∈ Icc (0 : ℝ) junction,
    ∃ i, (secondCells i).Covers s
  firstCells : Fin nFirst → DerivativeCell
  firstUpper : ∀ i,
    deriv window (firstCells i).center +
      curvatureBound * (firstCells i).radius ≤ 0
  firstCover : ∀ s ∈ Icc junction (1 / 2),
    ∃ i, (firstCells i).Covers s

private lemma second_nonpos {nSecond nFirst : ℕ}
    (cert : Certificate nSecond nFirst) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) cert.junction) :
    deriv (deriv window) s ≤ 0 := by
  obtain ⟨i, hi⟩ := cert.secondCover s hs
  have hlip := deriv2_lipschitz (cert.secondCells i).center s
  have hdiff :
      deriv (deriv window) s -
          deriv (deriv window) (cert.secondCells i).center ≤
        jerkBound * (cert.secondCells i).radius := by
    calc
      deriv (deriv window) s -
          deriv (deriv window) (cert.secondCells i).center ≤
          |deriv (deriv window) s -
            deriv (deriv window) (cert.secondCells i).center| := le_abs_self _
      _ ≤ jerkBound * |s - (cert.secondCells i).center| := hlip
      _ ≤ jerkBound * (cert.secondCells i).radius :=
        mul_le_mul_of_nonneg_left hi jerkBound_nonneg
  linarith [cert.secondUpper i]

private lemma derivative_nonpos_before {nSecond nFirst : ℕ}
    (cert : Certificate nSecond nFirst) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) cert.junction) :
    deriv window s ≤ 0 := by
  have hanti : AntitoneOn (deriv window) (Icc (0 : ℝ) cert.junction) :=
    antitoneOn_of_deriv_nonpos (D := Icc (0 : ℝ) cert.junction)
      (convex_Icc _ _)
      ((window_contDiff.deriv' (n := 1)).continuous.continuousOn)
      ((window_contDiff.deriv' (n := 1)).differentiable
        (by norm_num)).differentiableOn
      (fun x hx => second_nonpos cert (interior_subset hx))
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) cert.junction :=
    ⟨le_rfl, cert.junction_mem.1⟩
  have h := hanti hzero hs hs.1
  rw [deriv_window_zero] at h
  exact h

private lemma derivative_nonpos_after {nSecond nFirst : ℕ}
    (cert : Certificate nSecond nFirst) {s : ℝ}
    (hs : s ∈ Icc cert.junction (1 / 2)) :
    deriv window s ≤ 0 := by
  obtain ⟨i, hi⟩ := cert.firstCover s hs
  have hlip := deriv_lipschitz (cert.firstCells i).center s
  have hdiff :
      deriv window s - deriv window (cert.firstCells i).center ≤
        curvatureBound * (cert.firstCells i).radius := by
    calc
      deriv window s - deriv window (cert.firstCells i).center ≤
          |deriv window s - deriv window (cert.firstCells i).center| :=
        le_abs_self _
      _ ≤ curvatureBound * |s - (cert.firstCells i).center| := hlip
      _ ≤ curvatureBound * (cert.firstCells i).radius :=
        mul_le_mul_of_nonneg_left hi curvatureBound_nonneg
  linarith [cert.firstUpper i]

theorem derivative_nonpos {nSecond nFirst : ℕ}
    (cert : Certificate nSecond nFirst) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : deriv window s ≤ 0 := by
  rcases le_total s cert.junction with hbefore | hafter
  · exact derivative_nonpos_before cert ⟨hs.1, hbefore⟩
  · exact derivative_nonpos_after cert ⟨hafter, hs.2⟩

theorem window_antitone {nSecond nFirst : ℕ}
    (cert : Certificate nSecond nFirst) :
    AntitoneOn window (Icc (0 : ℝ) (1 / 2)) := by
  apply antitoneOn_of_deriv_nonpos (D := Icc (0 : ℝ) (1 / 2))
    (convex_Icc _ _) continuous_window.continuousOn
    (window_contDiff.differentiable (by norm_num)).differentiableOn
  intro s hs
  exact derivative_nonpos cert (interior_subset hs)

end Zeta23Ext.CurrentWindowHybridMonotonicity

