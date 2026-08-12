/-
Copyright (c) 2026 Nicholas Pipitone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.SincJetCertificate
import Zeta23Ext.CurrentKernelDerivatives

/-!
# Checked sinc-jet rows for production cell 4376

This generated-style module keeps the large table instantiation separate from
the reusable semantics.  Each row has a Boolean rational jet check plus a
kernel-checked `pi` range reduction for its trigonometric center.
-/

noncomputable section

open Real Set

namespace Zeta23Ext.ProductionCell4376Jets

open SincDerivativeCertificate SincJetCertificate

private def reducedCenter : ℚ := 184814 / 625000

private def plusOneTrig : RationalTrigCell.Witness :=
  ⟨2, reducedCenter, 1 / 100000000, 1, 1 / 5000000⟩

/-- The periodic `j=1` plus argument, centered at `6.5788877`. -/
def plusOne : SincJetCertificate.Witness where
  q := 65788877 / 10000000
  radius := 1 / 2500
  upper := 65792877 / 10000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 1 / 5000000
  valueLower := 44239 / 1000000
  valueUpper := 44351 / 1000000
  firstLower := 138636 / 1000000
  firstUpper := 138707 / 1000000
  secondLower := -86529 / 1000000
  secondUpper := -43187 / 500000

theorem plusOne_checked : plusOne.check = true := by
  norm_num [plusOne, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusOne_reduction :
    |(((plusOne.q : ℝ) - (2 : ℝ) * Real.pi) -
      (plusOneTrig.center : ℝ))| ≤ (plusOneTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusOne, plusOneTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusOne_sin :
    |Real.sin (plusOne.q : ℝ) - (plusOne.sinApprox : ℝ)| ≤
      (plusOne.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusOneTrig)
    (by norm_num [plusOneTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusOne.q : ℝ)) plusOne_reduction
  simpa [plusOne, plusOneTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusOne_cos :
    |Real.cos (plusOne.q : ℝ) - (plusOne.cosApprox : ℝ)| ≤
      (plusOne.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusOneTrig)
    (by norm_num [plusOneTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusOne.q : ℝ)) plusOne_reduction
  simpa [plusOne, plusOneTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusOne_sound {y : ℝ}
    (hy : |y - (65788877 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((44239 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 44351 / 1000000) ∧
    ((138636 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 138707 / 1000000) ∧
    ((-86529 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -43187 / 500000) := by
  have hy' : |y - (plusOne.q : ℝ)| ≤ (plusOne.radius : ℝ) := by
    simpa [plusOne] using hy
  simpa [plusOne] using plusOne.sound plusOne_checked plusOne_sin plusOne_cos hy'

private def plusTwoTrig : RationalTrigCell.Witness :=
  ⟨3, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=2` plus argument, centered at `9.7204804`. -/
def plusTwo : SincJetCertificate.Witness where
  q := 24301201 / 2500000
  radius := 1 / 2500
  upper := 24302201 / 2500000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -30019 / 1000000
  valueUpper := -29939 / 1000000
  firstLower := -47674 / 500000
  firstUpper := -19061 / 200000
  secondLower := 49543 / 1000000
  secondUpper := 49643 / 1000000

theorem plusTwo_checked : plusTwo.check = true := by
  norm_num [plusTwo, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusTwo_reduction :
    |(((plusTwo.q : ℝ) - (3 : ℝ) * Real.pi) -
      (plusTwoTrig.center : ℝ))| ≤ (plusTwoTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusTwo, plusTwoTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusTwo_sin :
    |Real.sin (plusTwo.q : ℝ) - (plusTwo.sinApprox : ℝ)| ≤
      (plusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusTwoTrig)
    (by norm_num [plusTwoTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusTwo.q : ℝ)) plusTwo_reduction
  rw [show |Real.sin (plusTwo.q : ℝ) - (plusTwo.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusTwoTrig.k) * Real.sin (plusTwo.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusTwoTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusTwoTrig.k) = -1 by norm_num [plusTwoTrig]]
    norm_num [plusTwo, plusTwoTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusTwo_cos :
    |Real.cos (plusTwo.q : ℝ) - (plusTwo.cosApprox : ℝ)| ≤
      (plusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusTwoTrig)
    (by norm_num [plusTwoTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusTwo.q : ℝ)) plusTwo_reduction
  rw [show |Real.cos (plusTwo.q : ℝ) - (plusTwo.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusTwoTrig.k) * Real.cos (plusTwo.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusTwoTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusTwoTrig.k) = -1 by norm_num [plusTwoTrig]]
    norm_num [plusTwo, plusTwoTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusTwo_sound {y : ℝ}
    (hy : |y - (24301201 / 2500000 : ℝ)| ≤ 1 / 2500) :
    ((-30019 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -29939 / 1000000) ∧
    ((-47674 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -19061 / 200000) ∧
    ((49543 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 49643 / 1000000) := by
  have hy' : |y - (plusTwo.q : ℝ)| ≤ (plusTwo.radius : ℝ) := by
    simpa [plusTwo] using hy
  simpa [plusTwo] using plusTwo.sound plusTwo_checked plusTwo_sin plusTwo_cos hy'

end Zeta23Ext.ProductionCell4376Jets

end
