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

private def plusThreeTrig : RationalTrigCell.Witness :=
  ⟨4, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=3` plus argument, centered at `12.862073`. -/
def plusThree : SincJetCertificate.Witness where
  q := 12862073 / 1000000
  radius := 1 / 2500
  upper := 12862473 / 1000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := 22627 / 1000000
  valueUpper := 11343 / 500000
  firstLower := 36299 / 500000
  firstUpper := 36313 / 500000
  secondLower := -16991 / 500000
  secondUpper := -33913 / 1000000

theorem plusThree_checked : plusThree.check = true := by
  norm_num [plusThree, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusThree_reduction :
    |(((plusThree.q : ℝ) - (4 : ℝ) * Real.pi) -
      (plusThreeTrig.center : ℝ))| ≤ (plusThreeTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusThree, plusThreeTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusThree_sin :
    |Real.sin (plusThree.q : ℝ) - (plusThree.sinApprox : ℝ)| ≤
      (plusThree.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusThreeTrig)
    (by norm_num [plusThreeTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusThree.q : ℝ)) plusThree_reduction
  rw [show ((-1 : ℝ) ^ plusThreeTrig.k) = 1 by norm_num [plusThreeTrig]] at h
  simpa [plusThree, plusThreeTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusThree_cos :
    |Real.cos (plusThree.q : ℝ) - (plusThree.cosApprox : ℝ)| ≤
      (plusThree.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusThreeTrig)
    (by norm_num [plusThreeTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusThree.q : ℝ)) plusThree_reduction
  rw [show ((-1 : ℝ) ^ plusThreeTrig.k) = 1 by norm_num [plusThreeTrig]] at h
  simpa [plusThree, plusThreeTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusThree_sound {y : ℝ}
    (hy : |y - (12862073 / 1000000 : ℝ)| ≤ 1 / 2500) :
    ((22627 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 11343 / 500000) ∧
    ((36299 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 36313 / 500000) ∧
    ((-16991 / 500000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -33913 / 1000000) := by
  have hy' : |y - (plusThree.q : ℝ)| ≤ (plusThree.radius : ℝ) := by
    simpa [plusThree] using hy
  simpa [plusThree] using plusThree.sound plusThree_checked
    plusThree_sin plusThree_cos hy'

private def plusFourTrig : RationalTrigCell.Witness :=
  ⟨5, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=4` plus argument, centered at `16.0036657`. -/
def plusFour : SincJetCertificate.Witness where
  q := 160036657 / 10000000
  radius := 1 / 2500
  upper := 160040657 / 10000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -9117 / 500000
  valueUpper := -2273 / 125000
  firstLower := -7331 / 125000
  firstUpper := -3664 / 62500
  secondLower := 6377 / 250000
  secondUpper := 12783 / 500000

theorem plusFour_checked : plusFour.check = true := by
  norm_num [plusFour, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusFour_reduction :
    |(((plusFour.q : ℝ) - (5 : ℝ) * Real.pi) -
      (plusFourTrig.center : ℝ))| ≤ (plusFourTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusFour, plusFourTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusFour_sin :
    |Real.sin (plusFour.q : ℝ) - (plusFour.sinApprox : ℝ)| ≤
      (plusFour.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusFourTrig)
    (by norm_num [plusFourTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusFour.q : ℝ)) plusFour_reduction
  rw [show |Real.sin (plusFour.q : ℝ) - (plusFour.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusFourTrig.k) * Real.sin (plusFour.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusFourTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusFourTrig.k) = -1 by norm_num [plusFourTrig]]
    norm_num [plusFour, plusFourTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusFour_cos :
    |Real.cos (plusFour.q : ℝ) - (plusFour.cosApprox : ℝ)| ≤
      (plusFour.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusFourTrig)
    (by norm_num [plusFourTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusFour.q : ℝ)) plusFour_reduction
  rw [show |Real.cos (plusFour.q : ℝ) - (plusFour.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusFourTrig.k) * Real.cos (plusFour.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusFourTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusFourTrig.k) = -1 by norm_num [plusFourTrig]]
    norm_num [plusFour, plusFourTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusFour_sound {y : ℝ}
    (hy : |y - (160036657 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((-9117 / 500000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -2273 / 125000) ∧
    ((-7331 / 125000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -3664 / 62500) ∧
    ((6377 / 250000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 12783 / 500000) := by
  have hy' : |y - (plusFour.q : ℝ)| ≤ (plusFour.radius : ℝ) := by
    simpa [plusFour] using hy
  simpa [plusFour] using plusFour.sound plusFour_checked
    plusFour_sin plusFour_cos hy'

private def plusFiveTrig : RationalTrigCell.Witness :=
  ⟨6, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=5` plus argument, centered at `19.1452583`. -/
def plusFive : SincJetCertificate.Witness where
  q := 191452583 / 10000000
  radius := 1 / 2500
  upper := 191456583 / 10000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := 15201 / 1000000
  valueUpper := 15241 / 1000000
  firstLower := 24581 / 500000
  firstUpper := 49179 / 1000000
  secondLower := -20381 / 1000000
  secondUpper := -10167 / 500000

theorem plusFive_checked : plusFive.check = true := by
  norm_num [plusFive, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusFive_reduction :
    |(((plusFive.q : ℝ) - (6 : ℝ) * Real.pi) -
      (plusFiveTrig.center : ℝ))| ≤ (plusFiveTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusFive, plusFiveTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusFive_sin :
    |Real.sin (plusFive.q : ℝ) - (plusFive.sinApprox : ℝ)| ≤
      (plusFive.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusFiveTrig)
    (by norm_num [plusFiveTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusFive.q : ℝ)) plusFive_reduction
  rw [show ((-1 : ℝ) ^ plusFiveTrig.k) = 1 by norm_num [plusFiveTrig]] at h
  simpa [plusFive, plusFiveTrig, reducedCenter,
    TranscendentalBounds.sinTaylor7] using h

private theorem plusFive_cos :
    |Real.cos (plusFive.q : ℝ) - (plusFive.cosApprox : ℝ)| ≤
      (plusFive.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusFiveTrig)
    (by norm_num [plusFiveTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusFive.q : ℝ)) plusFive_reduction
  rw [show ((-1 : ℝ) ^ plusFiveTrig.k) = 1 by norm_num [plusFiveTrig]] at h
  simpa [plusFive, plusFiveTrig, reducedCenter,
    TranscendentalBounds.cosTaylor8] using h

theorem plusFive_sound {y : ℝ}
    (hy : |y - (191452583 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((15201 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 15241 / 1000000) ∧
    ((24581 / 500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 49179 / 1000000) ∧
    ((-20381 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -10167 / 500000) := by
  have hy' : |y - (plusFive.q : ℝ)| ≤ (plusFive.radius : ℝ) := by
    simpa [plusFive] using hy
  simpa [plusFive] using plusFive.sound plusFive_checked
    plusFive_sin plusFive_cos hy'

private def plusSixTrig : RationalTrigCell.Witness :=
  ⟨7, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The periodic `j=6` plus argument, centered at `22.286851`. -/
def plusSix : SincJetCertificate.Witness where
  q := 22286851 / 1000000
  radius := 1 / 2500
  upper := 22287251 / 1000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := -13093 / 1000000
  valueUpper := -6529 / 500000
  firstLower := -42343 / 1000000
  firstUpper := -5291 / 125000
  secondLower := 3371 / 200000
  secondUpper := 8447 / 500000

theorem plusSix_checked : plusSix.check = true := by
  norm_num [plusSix, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusSix_reduction :
    |(((plusSix.q : ℝ) - (7 : ℝ) * Real.pi) -
      (plusSixTrig.center : ℝ))| ≤ (plusSixTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusSix, plusSixTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusSix_sin :
    |Real.sin (plusSix.q : ℝ) - (plusSix.sinApprox : ℝ)| ≤
      (plusSix.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusSixTrig)
    (by norm_num [plusSixTrig, reducedCenter, RationalTrigCell.check])
    (x := (plusSix.q : ℝ)) plusSix_reduction
  rw [show |Real.sin (plusSix.q : ℝ) - (plusSix.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusSixTrig.k) * Real.sin (plusSix.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusSixTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusSixTrig.k) = -1 by norm_num [plusSixTrig]]
    norm_num [plusSix, plusSixTrig, reducedCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusSix_cos :
    |Real.cos (plusSix.q : ℝ) - (plusSix.cosApprox : ℝ)| ≤
      (plusSix.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusSixTrig)
    (by norm_num [plusSixTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := (plusSix.q : ℝ)) plusSix_reduction
  rw [show |Real.cos (plusSix.q : ℝ) - (plusSix.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusSixTrig.k) * Real.cos (plusSix.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusSixTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    rw [show ((-1 : ℝ) ^ plusSixTrig.k) = -1 by norm_num [plusSixTrig]]
    norm_num [plusSix, plusSixTrig, reducedCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusSix_sound {y : ℝ}
    (hy : |y - (22286851 / 1000000 : ℝ)| ≤ 1 / 2500) :
    ((-13093 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -6529 / 500000) ∧
    ((-42343 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -5291 / 125000) ∧
    ((3371 / 200000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 8447 / 500000) := by
  have hy' : |y - (plusSix.q : ℝ)| ≤ (plusSix.radius : ℝ) := by
    simpa [plusSix] using hy
  simpa [plusSix] using plusSix.sound plusSix_checked
    plusSix_sin plusSix_cos hy'

private lemma sincD1_neg (x : ℝ) : sincD1 (-x) = -sincD1 x := by
  simp only [sincD1, Real.cos_neg, Real.sin_neg]
  ring

private lemma sincD2_neg (x : ℝ) : sincD2 (-x) = sincD2 x := by
  simp only [sincD2, secondNumerator, Real.cos_neg, Real.sin_neg]
  ring

/-- The actual `j=1` minus argument is the negative of the delicate reduced
cell.  Parity turns the reusable positive-row certificate into its semantic
production enclosure. -/
theorem minusOne_sound {y : ℝ}
    (hy : |y - (-184814 / 625000 : ℝ)| ≤ 1 / 2500) :
    ((98545 / 100000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 985531 / 1000000) ∧
    ((243935 / 2500000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 97843 / 1000000) ∧
    ((-327341 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -40241 / 125000) := by
  have hy' : |-y - (184814 / 625000 : ℝ)| ≤ 1 / 2500 := by
    rw [show -y - (184814 / 625000 : ℝ) =
      -(y - (-184814 / 625000 : ℝ)) by ring, abs_neg]
    exact hy
  have h := SincJetCertificate.productionReducedWitness_sound hy'
  simp only [Real.sinc_neg, sincD1_neg, sincD2_neg] at h
  exact ⟨h.1, ⟨by linarith [h.2.1.2], by linarith [h.2.1.1]⟩, h.2.2⟩

private def minusTwoTrig : RationalTrigCell.Witness :=
  ⟨-1, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The reflected periodic `j=2` minus argument, centered at `2.8458902`. -/
def minusTwo : SincJetCertificate.Witness where
  q := 14229451 / 5000000
  radius := 1 / 2500
  upper := 14231451 / 5000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := 102248 / 1000000
  valueUpper := 102547 / 1000000
  firstLower := -372178 / 1000000
  firstUpper := -372049 / 1000000
  secondLower := 158904 / 1000000
  secondUpper := 159321 / 1000000

theorem minusTwo_checked : minusTwo.check = true := by
  norm_num [minusTwo, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusTwo_reduction :
    |((-(minusTwo.q : ℝ) - (minusTwoTrig.k : ℝ) * Real.pi) -
      (minusTwoTrig.center : ℝ))| ≤ (minusTwoTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusTwo, minusTwoTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusTwo_sin :
    |Real.sin (minusTwo.q : ℝ) - (minusTwo.sinApprox : ℝ)| ≤
      (minusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusTwoTrig)
    (by norm_num [minusTwoTrig, reducedCenter, RationalTrigCell.check])
    (x := -(minusTwo.q : ℝ)) minusTwo_reduction
  simpa [minusTwo, minusTwoTrig, reducedCenter, Real.sin_neg,
    TranscendentalBounds.sinTaylor7] using h

private theorem minusTwo_cos :
    |Real.cos (minusTwo.q : ℝ) - (minusTwo.cosApprox : ℝ)| ≤
      (minusTwo.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusTwoTrig)
    (by norm_num [minusTwoTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := -(minusTwo.q : ℝ)) minusTwo_reduction
  rw [show |Real.cos (minusTwo.q : ℝ) - (minusTwo.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ minusTwoTrig.k) * Real.cos (-(minusTwo.q : ℝ)) -
        TranscendentalBounds.cosTaylor8 (minusTwoTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusTwo, minusTwoTrig, reducedCenter, Real.cos_neg,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem minusTwo_sound {y : ℝ}
    (hy : |y - (14229451 / 5000000 : ℝ)| ≤ 1 / 2500) :
    ((102248 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 102547 / 1000000) ∧
    ((-372178 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -372049 / 1000000) ∧
    ((158904 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 159321 / 1000000) := by
  have hy' : |y - (minusTwo.q : ℝ)| ≤ (minusTwo.radius : ℝ) := by
    simpa [minusTwo] using hy
  simpa [minusTwo] using minusTwo.sound minusTwo_checked
    minusTwo_sin minusTwo_cos hy'

private def minusThreeTrig : RationalTrigCell.Witness :=
  ⟨-2, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The reflected periodic `j=3` minus argument, centered at `5.9874829`. -/
def minusThree : SincJetCertificate.Witness where
  q := 59874829 / 10000000
  radius := 1 / 2500
  upper := 59878829 / 10000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := -48738 / 1000000
  valueUpper := -24301 / 500000
  firstLower := 167891 / 1000000
  firstUpper := 167899 / 1000000
  secondLower := -7481 / 1000000
  secondUpper := -7343 / 1000000

theorem minusThree_checked : minusThree.check = true := by
  norm_num [minusThree, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusThree_reduction :
    |((-(minusThree.q : ℝ) - (minusThreeTrig.k : ℝ) * Real.pi) -
      (minusThreeTrig.center : ℝ))| ≤ (minusThreeTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusThree, minusThreeTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusThree_sin :
    |Real.sin (minusThree.q : ℝ) - (minusThree.sinApprox : ℝ)| ≤
      (minusThree.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusThreeTrig)
    (by norm_num [minusThreeTrig, reducedCenter, RationalTrigCell.check])
    (x := -(minusThree.q : ℝ)) minusThree_reduction
  rw [show |Real.sin (minusThree.q : ℝ) - (minusThree.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ minusThreeTrig.k) * Real.sin (-(minusThree.q : ℝ)) -
        TranscendentalBounds.sinTaylor7 (minusThreeTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusThree, minusThreeTrig, reducedCenter, Real.sin_neg,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem minusThree_cos :
    |Real.cos (minusThree.q : ℝ) - (minusThree.cosApprox : ℝ)| ≤
      (minusThree.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusThreeTrig)
    (by norm_num [minusThreeTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := -(minusThree.q : ℝ)) minusThree_reduction
  simpa [minusThree, minusThreeTrig, reducedCenter, Real.cos_neg,
    TranscendentalBounds.cosTaylor8] using h

theorem minusThree_sound {y : ℝ}
    (hy : |y - (59874829 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((-48738 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -24301 / 500000) ∧
    ((167891 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 167899 / 1000000) ∧
    ((-7481 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -7343 / 1000000) := by
  have hy' : |y - (minusThree.q : ℝ)| ≤ (minusThree.radius : ℝ) := by
    simpa [minusThree] using hy
  simpa [minusThree] using minusThree.sound minusThree_checked
    minusThree_sin minusThree_cos hy'

private def minusFourTrig : RationalTrigCell.Witness :=
  ⟨-3, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The reflected periodic `j=4` minus argument, centered at `9.1290756`. -/
def minusFour : SincJetCertificate.Witness where
  q := 22822689 / 2500000
  radius := 1 / 2500
  upper := 22823689 / 2500000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := 31877 / 1000000
  valueUpper := 31965 / 1000000
  firstLower := -108286 / 1000000
  firstUpper := -108279 / 1000000
  secondLower := -8244 / 1000000
  secondUpper := -8153 / 1000000

theorem minusFour_checked : minusFour.check = true := by
  norm_num [minusFour, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusFour_reduction :
    |((-(minusFour.q : ℝ) - (minusFourTrig.k : ℝ) * Real.pi) -
      (minusFourTrig.center : ℝ))| ≤ (minusFourTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusFour, minusFourTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusFour_sin :
    |Real.sin (minusFour.q : ℝ) - (minusFour.sinApprox : ℝ)| ≤
      (minusFour.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusFourTrig)
    (by norm_num [minusFourTrig, reducedCenter, RationalTrigCell.check])
    (x := -(minusFour.q : ℝ)) minusFour_reduction
  rw [show ((-1 : ℝ) ^ minusFourTrig.k) = -1 by norm_num [minusFourTrig]] at h
  simpa [minusFour, minusFourTrig, reducedCenter, Real.sin_neg,
    TranscendentalBounds.sinTaylor7] using h

private theorem minusFour_cos :
    |Real.cos (minusFour.q : ℝ) - (minusFour.cosApprox : ℝ)| ≤
      (minusFour.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusFourTrig)
    (by norm_num [minusFourTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := -(minusFour.q : ℝ)) minusFour_reduction
  rw [show |Real.cos (minusFour.q : ℝ) - (minusFour.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ minusFourTrig.k) * Real.cos (-(minusFour.q : ℝ)) -
        TranscendentalBounds.cosTaylor8 (minusFourTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusFour, minusFourTrig, reducedCenter, Real.cos_neg,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem minusFour_sound {y : ℝ}
    (hy : |y - (22822689 / 2500000 : ℝ)| ≤ 1 / 2500) :
    ((31877 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 31965 / 1000000) ∧
    ((-108286 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -108279 / 1000000) ∧
    ((-8244 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -8153 / 1000000) := by
  have hy' : |y - (minusFour.q : ℝ)| ≤ (minusFour.radius : ℝ) := by
    simpa [minusFour] using hy
  simpa [minusFour] using minusFour.sound minusFour_checked
    minusFour_sin minusFour_cos hy'

private def minusFiveTrig : RationalTrigCell.Witness :=
  ⟨-4, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The reflected periodic `j=5` minus argument, centered at `12.2706682`. -/
def minusFive : SincJetCertificate.Witness where
  q := 61353341 / 5000000
  radius := 1 / 2500
  upper := 61355341 / 5000000
  sinApprox := -(reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040)
  cosApprox := 1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320
  trigError := 3 / 10000000
  valueLower := -23781 / 1000000
  valueUpper := -23716 / 1000000
  firstLower := 79889 / 1000000
  firstUpper := 79899 / 1000000
  secondLower := 10693 / 1000000
  secondUpper := 10761 / 1000000

theorem minusFive_checked : minusFive.check = true := by
  norm_num [minusFive, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusFive_reduction :
    |((-(minusFive.q : ℝ) - (minusFiveTrig.k : ℝ) * Real.pi) -
      (minusFiveTrig.center : ℝ))| ≤ (minusFiveTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusFive, minusFiveTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusFive_sin :
    |Real.sin (minusFive.q : ℝ) - (minusFive.sinApprox : ℝ)| ≤
      (minusFive.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusFiveTrig)
    (by norm_num [minusFiveTrig, reducedCenter, RationalTrigCell.check])
    (x := -(minusFive.q : ℝ)) minusFive_reduction
  rw [show ((-1 : ℝ) ^ minusFiveTrig.k) = 1 by norm_num [minusFiveTrig]] at h
  rw [show |Real.sin (minusFive.q : ℝ) - (minusFive.sinApprox : ℝ)| =
      |Real.sin (-(minusFive.q : ℝ)) -
        TranscendentalBounds.sinTaylor7 (minusFiveTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusFive, minusFiveTrig, reducedCenter, Real.sin_neg,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  simpa [minusFive, minusFiveTrig] using h

private theorem minusFive_cos :
    |Real.cos (minusFive.q : ℝ) - (minusFive.cosApprox : ℝ)| ≤
      (minusFive.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusFiveTrig)
    (by norm_num [minusFiveTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := -(minusFive.q : ℝ)) minusFive_reduction
  rw [show ((-1 : ℝ) ^ minusFiveTrig.k) = 1 by norm_num [minusFiveTrig]] at h
  simpa [minusFive, minusFiveTrig, reducedCenter, Real.cos_neg,
    TranscendentalBounds.cosTaylor8] using h

theorem minusFive_sound {y : ℝ}
    (hy : |y - (61353341 / 5000000 : ℝ)| ≤ 1 / 2500) :
    ((-23781 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -23716 / 1000000) ∧
    ((79889 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 79899 / 1000000) ∧
    ((10693 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 10761 / 1000000) := by
  have hy' : |y - (minusFive.q : ℝ)| ≤ (minusFive.radius : ℝ) := by
    simpa [minusFive] using hy
  simpa [minusFive] using minusFive.sound minusFive_checked
    minusFive_sin minusFive_cos hy'

private def minusSixTrig : RationalTrigCell.Witness :=
  ⟨-5, reducedCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- The reflected periodic `j=6` minus argument, centered at `15.4122609`. -/
def minusSix : SincJetCertificate.Witness where
  q := 154122609 / 10000000
  radius := 1 / 2500
  upper := 154126609 / 10000000
  sinApprox := reducedCenter - reducedCenter ^ 3 / 6 +
    reducedCenter ^ 5 / 120 - reducedCenter ^ 7 / 5040
  cosApprox := -(1 - reducedCenter ^ 2 / 2 + reducedCenter ^ 4 / 24 -
    reducedCenter ^ 6 / 720 + reducedCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := 18882 / 1000000
  valueUpper := 18934 / 1000000
  firstLower := -63299 / 1000000
  firstUpper := -63289 / 1000000
  secondLower := -10722 / 1000000
  secondUpper := -10667 / 1000000

theorem minusSix_checked : minusSix.check = true := by
  norm_num [minusSix, reducedCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusSix_reduction :
    |((-(minusSix.q : ℝ) - (minusSixTrig.k : ℝ) * Real.pi) -
      (minusSixTrig.center : ℝ))| ≤ (minusSixTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusSix, minusSixTrig, reducedCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusSix_sin :
    |Real.sin (minusSix.q : ℝ) - (minusSix.sinApprox : ℝ)| ≤
      (minusSix.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusSixTrig)
    (by norm_num [minusSixTrig, reducedCenter, RationalTrigCell.check])
    (x := -(minusSix.q : ℝ)) minusSix_reduction
  rw [show ((-1 : ℝ) ^ minusSixTrig.k) = -1 by norm_num [minusSixTrig]] at h
  simpa [minusSix, minusSixTrig, reducedCenter, Real.sin_neg,
    TranscendentalBounds.sinTaylor7] using h

private theorem minusSix_cos :
    |Real.cos (minusSix.q : ℝ) - (minusSix.cosApprox : ℝ)| ≤
      (minusSix.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusSixTrig)
    (by norm_num [minusSixTrig, reducedCenter, RationalTrigCell.cosCheck])
    (x := -(minusSix.q : ℝ)) minusSix_reduction
  rw [show |Real.cos (minusSix.q : ℝ) - (minusSix.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ minusSixTrig.k) * Real.cos (-(minusSix.q : ℝ)) -
        TranscendentalBounds.cosTaylor8 (minusSixTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusSix, minusSixTrig, reducedCenter, Real.cos_neg,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem minusSix_sound {y : ℝ}
    (hy : |y - (154122609 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((18882 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 18934 / 1000000) ∧
    ((-63299 / 1000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -63289 / 1000000) ∧
    ((-10722 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ -10667 / 1000000) := by
  have hy' : |y - (minusSix.q : ℝ)| ≤ (minusSix.radius : ℝ) := by
    simpa [minusSix] using hy
  simpa [minusSix] using minusSix.sound minusSix_checked
    minusSix_sin minusSix_cos hy'

private def minusZeroCenter : ℚ := 1028511 / 2500000
private def minusZeroTrig : RationalTrigCell.Witness :=
  ⟨-1, minusZeroCenter, 1 / 10000000, 1, 3 / 10000000⟩

/-- Positive magnitude of the exceptional `sqrt 2` minus argument. -/
def minusZero : SincJetCertificate.Witness where
  q := 27301883 / 10000000
  radius := 1 / 2500
  upper := 27305883 / 10000000
  sinApprox := minusZeroCenter - minusZeroCenter ^ 3 / 6 +
    minusZeroCenter ^ 5 / 120 - minusZeroCenter ^ 7 / 5040
  cosApprox := -(1 - minusZeroCenter ^ 2 / 2 + minusZeroCenter ^ 4 / 24 -
    minusZeroCenter ^ 6 / 720 + minusZeroCenter ^ 8 / 40320)
  trigError := 3 / 10000000
  valueLower := 146316 / 1000000
  valueUpper := 146629 / 1000000
  firstLower := -3894181 / 10000000
  firstUpper := -3893065 / 10000000
  secondLower := 138547 / 1000000
  secondUpper := 2779259 / 20000000

theorem minusZero_checked : minusZero.check = true := by
  norm_num [minusZero, minusZeroCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem minusZero_reduction :
    |((-(minusZero.q : ℝ) - (minusZeroTrig.k : ℝ) * Real.pi) -
      (minusZeroTrig.center : ℝ))| ≤ (minusZeroTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [minusZero, minusZeroTrig, minusZeroCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem minusZero_sin :
    |Real.sin (minusZero.q : ℝ) - (minusZero.sinApprox : ℝ)| ≤
      (minusZero.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := minusZeroTrig)
    (by norm_num [minusZeroTrig, minusZeroCenter, RationalTrigCell.check])
    (x := -(minusZero.q : ℝ)) minusZero_reduction
  rw [show ((-1 : ℝ) ^ minusZeroTrig.k) = -1 by norm_num [minusZeroTrig]] at h
  simpa [minusZero, minusZeroTrig, minusZeroCenter, Real.sin_neg,
    TranscendentalBounds.sinTaylor7] using h

private theorem minusZero_cos :
    |Real.cos (minusZero.q : ℝ) - (minusZero.cosApprox : ℝ)| ≤
      (minusZero.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := minusZeroTrig)
    (by norm_num [minusZeroTrig, minusZeroCenter, RationalTrigCell.cosCheck])
    (x := -(minusZero.q : ℝ)) minusZero_reduction
  rw [show |Real.cos (minusZero.q : ℝ) - (minusZero.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ minusZeroTrig.k) * Real.cos (-(minusZero.q : ℝ)) -
        TranscendentalBounds.cosTaylor8 (minusZeroTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [minusZero, minusZeroTrig, minusZeroCenter, Real.cos_neg,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

private theorem minusZero_positive_sound {y : ℝ}
    (hy : |y - (27301883 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((146316 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 146629 / 1000000) ∧
    ((-3894181 / 10000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -3893065 / 10000000) ∧
    ((138547 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 2779259 / 20000000) := by
  have hy' : |y - (minusZero.q : ℝ)| ≤ (minusZero.radius : ℝ) := by
    simpa [minusZero] using hy
  simpa [minusZero] using minusZero.sound minusZero_checked
    minusZero_sin minusZero_cos hy'

/-- Semantic enclosure for the actual negative `j=0` minus argument. -/
theorem minusZero_sound {y : ℝ}
    (hy : |y - (-27301883 / 10000000 : ℝ)| ≤ 1 / 2500) :
    ((146316 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ 146629 / 1000000) ∧
    ((3893065 / 10000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ 3894181 / 10000000) ∧
    ((138547 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 2779259 / 20000000) := by
  have hy' : |-y - (27301883 / 10000000 : ℝ)| ≤ 1 / 2500 := by
    rw [show -y - (27301883 / 10000000 : ℝ) =
      -(y - (-27301883 / 10000000 : ℝ)) by ring, abs_neg]
    exact hy
  have h := minusZero_positive_sound hy'
  simp only [Real.sinc_neg, sincD1_neg, sincD2_neg] at h
  exact ⟨h.1, ⟨by linarith [h.2.1.2], by linarith [h.2.1.1]⟩, h.2.2⟩

private def plusZeroCenter : ℚ := 2507023 / 2500000
private def plusZeroTrig : RationalTrigCell.Witness :=
  ⟨1, plusZeroCenter, 1 / 10000000, 101 / 100, 21 / 100000⟩

/-- The exceptional `sqrt 2` plus argument, centered at `4.1444018`. -/
def plusZero : SincJetCertificate.Witness where
  q := 20722009 / 5000000
  radius := 1 / 2500
  upper := 20724009 / 5000000
  sinApprox := -(plusZeroCenter - plusZeroCenter ^ 3 / 6 +
    plusZeroCenter ^ 5 / 120 - plusZeroCenter ^ 7 / 5040)
  cosApprox := -(1 - plusZeroCenter ^ 2 / 2 + plusZeroCenter ^ 4 / 24 -
    plusZeroCenter ^ 6 / 720 + plusZeroCenter ^ 8 / 40320)
  trigError := 21 / 100000
  valueLower := -203486 / 1000000
  valueUpper := -203319 / 1000000
  firstLower := -404397 / 5000000
  firstUpper := -161119 / 2000000
  secondLower := 242120 / 1000000
  secondUpper := 2425923 / 10000000

theorem plusZero_checked : plusZero.check = true := by
  norm_num [plusZero, plusZeroCenter, SincJetCertificate.Witness.check,
    SincJetCertificate.Witness.secondApprox,
    SincJetCertificate.Witness.secondError,
    SincJetCertificate.Witness.secondAbs,
    SincJetCertificate.Witness.firstApprox,
    SincJetCertificate.Witness.firstError,
    SincJetCertificate.Witness.firstAbs,
    SincJetCertificate.Witness.valueApprox,
    SincJetCertificate.Witness.valueError]

private theorem plusZero_reduction :
    |(((plusZero.q : ℝ) - (plusZeroTrig.k : ℝ) * Real.pi) -
      (plusZeroTrig.center : ℝ))| ≤ (plusZeroTrig.radius : ℝ) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le]
  norm_num [plusZero, plusZeroTrig, plusZeroCenter] at hp ⊢
  constructor <;> linarith [hp.1, hp.2]

private theorem plusZero_sin :
    |Real.sin (plusZero.q : ℝ) - (plusZero.sinApprox : ℝ)| ≤
      (plusZero.trigError : ℝ) := by
  have h := RationalTrigCell.sin_sound
    (w := plusZeroTrig)
    (by norm_num [plusZeroTrig, plusZeroCenter, RationalTrigCell.check])
    (x := (plusZero.q : ℝ)) plusZero_reduction
  rw [show |Real.sin (plusZero.q : ℝ) - (plusZero.sinApprox : ℝ)| =
      |((-1 : ℝ) ^ plusZeroTrig.k) * Real.sin (plusZero.q : ℝ) -
        TranscendentalBounds.sinTaylor7 (plusZeroTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [plusZero, plusZeroTrig, plusZeroCenter,
      TranscendentalBounds.sinTaylor7]
    ring
  ]
  exact h

private theorem plusZero_cos :
    |Real.cos (plusZero.q : ℝ) - (plusZero.cosApprox : ℝ)| ≤
      (plusZero.trigError : ℝ) := by
  have h := RationalTrigCell.cos_sound
    (w := plusZeroTrig)
    (by norm_num [plusZeroTrig, plusZeroCenter, RationalTrigCell.cosCheck])
    (x := (plusZero.q : ℝ)) plusZero_reduction
  rw [show |Real.cos (plusZero.q : ℝ) - (plusZero.cosApprox : ℝ)| =
      |((-1 : ℝ) ^ plusZeroTrig.k) * Real.cos (plusZero.q : ℝ) -
        TranscendentalBounds.cosTaylor8 (plusZeroTrig.center : ℝ)| by
    apply abs_eq_abs.mpr
    right
    norm_num [plusZero, plusZeroTrig, plusZeroCenter,
      TranscendentalBounds.cosTaylor8]
    ring
  ]
  exact h

theorem plusZero_sound {y : ℝ}
    (hy : |y - (20722009 / 5000000 : ℝ)| ≤ 1 / 2500) :
    ((-203486 / 1000000 : ℝ) ≤ Real.sinc y ∧
      Real.sinc y ≤ -203319 / 1000000) ∧
    ((-404397 / 5000000 : ℝ) ≤ sincD1 y ∧
      sincD1 y ≤ -161119 / 2000000) ∧
    ((242120 / 1000000 : ℝ) ≤ sincD2 y ∧
      sincD2 y ≤ 2425923 / 10000000) := by
  have hy' : |y - (plusZero.q : ℝ)| ≤ (plusZero.radius : ℝ) := by
    simpa [plusZero] using hy
  simpa [plusZero] using plusZero.sound plusZero_checked
    plusZero_sin plusZero_cos hy'

/-! ## Actual production-argument cells -/

private def minusCenter : Fin 7 → ℝ
  | ⟨0, _⟩ => -27301883 / 10000000
  | ⟨1, _⟩ => -184814 / 625000
  | ⟨2, _⟩ => 14229451 / 5000000
  | ⟨3, _⟩ => 59874829 / 10000000
  | ⟨4, _⟩ => 22822689 / 2500000
  | ⟨5, _⟩ => 61353341 / 5000000
  | ⟨6, _⟩ => 154122609 / 10000000

private def plusCenter : Fin 7 → ℝ
  | ⟨0, _⟩ => 20722009 / 5000000
  | ⟨1, _⟩ => 65788877 / 10000000
  | ⟨2, _⟩ => 24301201 / 2500000
  | ⟨3, _⟩ => 12862073 / 1000000
  | ⟨4, _⟩ => 160036657 / 10000000
  | ⟨5, _⟩ => 191452583 / 10000000
  | ⟨6, _⟩ => 22286851 / 1000000

private theorem sqrt_two_tight :
    (14142135623 : ℝ) / 10000000000 ≤ Real.sqrt 2 ∧
      Real.sqrt 2 ≤ (3535533906 : ℝ) / 2500000000 := by
  apply TranscendentalBounds.sqrt_mem_interval (x := (2 : ℝ)) <;> norm_num

private theorem argument_cells {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (∀ j : Fin 7, |CurrentKernelDerivatives.minusArgument j x - minusCenter j| ≤
      1 / 2500) ∧
    (∀ j : Fin 7, |CurrentKernelDerivatives.plusArgument j x - plusCenter j| ≤
      1 / 2500) := by
  have hp := TranscendentalBounds.pi_rational_bounds
  let pLo : ℝ := 314159265358979323846 / 10 ^ 20
  let pHi : ℝ := 314159265358979323847 / 10 ^ 20
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hprodLo : pLo * ((4376 : ℝ) / 4000) ≤ Real.pi * x := by
    calc
      pLo * ((4376 : ℝ) / 4000) ≤ Real.pi * (4376 / 4000) := by
        exact mul_le_mul_of_nonneg_right hp.1.le (by norm_num)
      _ ≤ Real.pi * x := mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le
  have hprodHi : Real.pi * x ≤ pHi * ((4377 : ℝ) / 4000) := by
    calc
      Real.pi * x ≤ pHi * x := mul_le_mul_of_nonneg_right hp.2.le hx0
      _ ≤ pHi * (4377 / 4000) := by
        apply mul_le_mul_of_nonneg_left hx.2
        norm_num [pHi]
  have hs := sqrt_two_tight
  constructor <;> intro j <;> fin_cases j <;>
    simp only [CurrentKernelDerivatives.minusArgument,
      CurrentKernelDerivatives.plusArgument, CurrentWindow.frequency,
      minusCenter, plusCenter] <;> rw [abs_le] <;>
    constructor <;> norm_num [pLo, pHi] at hprodLo hprodHi hs ⊢ <;>
    linarith [hprodLo, hprodHi, hs.1, hs.2]

/-! ## Fourteen-row kernel composition -/

private def mid (a b : ℝ) : ℝ := (a + b) / 2
private def rad (a b : ℝ) : ℝ := (b - a) / 2

private lemma abs_sub_mid_le {a b v : ℝ} (h : a ≤ v ∧ v ≤ b) :
    |v - mid a b| ≤ rad a b := by
  rw [abs_le]
  exact ⟨by dsimp [mid, rad]; linarith [h.1],
    by dsimp [mid, rad]; linarith [h.2]⟩

private def productionRow : Fin 7 → CurrentKernelDerivatives.PairApprox
  | ⟨0, _⟩ => {
      minusValue := mid (146316/1000000) (146629/1000000)
      plusValue := mid (-203486/1000000) (-203319/1000000)
      minusFirst := mid (3893065/10000000) (3894181/10000000)
      plusFirst := mid (-404397/5000000) (-161119/2000000)
      minusSecond := mid (138547/1000000) (2779259/20000000)
      plusSecond := mid (242120/1000000) (2425923/10000000)
      minusValueError := rad (146316/1000000) (146629/1000000)
      plusValueError := rad (-203486/1000000) (-203319/1000000)
      minusFirstError := rad (3893065/10000000) (3894181/10000000)
      plusFirstError := rad (-404397/5000000) (-161119/2000000)
      minusSecondError := rad (138547/1000000) (2779259/20000000)
      plusSecondError := rad (242120/1000000) (2425923/10000000) }
  | ⟨1, _⟩ => {
      minusValue := mid (98545/100000) (985531/1000000)
      plusValue := mid (44239/1000000) (44351/1000000)
      minusFirst := mid (243935/2500000) (97843/1000000)
      plusFirst := mid (138636/1000000) (138707/1000000)
      minusSecond := mid (-327341/1000000) (-40241/125000)
      plusSecond := mid (-86529/1000000) (-43187/500000)
      minusValueError := rad (98545/100000) (985531/1000000)
      plusValueError := rad (44239/1000000) (44351/1000000)
      minusFirstError := rad (243935/2500000) (97843/1000000)
      plusFirstError := rad (138636/1000000) (138707/1000000)
      minusSecondError := rad (-327341/1000000) (-40241/125000)
      plusSecondError := rad (-86529/1000000) (-43187/500000) }
  | ⟨2, _⟩ => {
      minusValue := mid (102248/1000000) (102547/1000000)
      plusValue := mid (-30019/1000000) (-29939/1000000)
      minusFirst := mid (-372178/1000000) (-372049/1000000)
      plusFirst := mid (-47674/500000) (-19061/200000)
      minusSecond := mid (158904/1000000) (159321/1000000)
      plusSecond := mid (49543/1000000) (49643/1000000)
      minusValueError := rad (102248/1000000) (102547/1000000)
      plusValueError := rad (-30019/1000000) (-29939/1000000)
      minusFirstError := rad (-372178/1000000) (-372049/1000000)
      plusFirstError := rad (-47674/500000) (-19061/200000)
      minusSecondError := rad (158904/1000000) (159321/1000000)
      plusSecondError := rad (49543/1000000) (49643/1000000) }
  | ⟨3, _⟩ => {
      minusValue := mid (-48738/1000000) (-24301/500000)
      plusValue := mid (22627/1000000) (11343/500000)
      minusFirst := mid (167891/1000000) (167899/1000000)
      plusFirst := mid (36299/500000) (36313/500000)
      minusSecond := mid (-7481/1000000) (-7343/1000000)
      plusSecond := mid (-16991/500000) (-33913/1000000)
      minusValueError := rad (-48738/1000000) (-24301/500000)
      plusValueError := rad (22627/1000000) (11343/500000)
      minusFirstError := rad (167891/1000000) (167899/1000000)
      plusFirstError := rad (36299/500000) (36313/500000)
      minusSecondError := rad (-7481/1000000) (-7343/1000000)
      plusSecondError := rad (-16991/500000) (-33913/1000000) }
  | ⟨4, _⟩ => {
      minusValue := mid (31877/1000000) (31965/1000000)
      plusValue := mid (-9117/500000) (-2273/125000)
      minusFirst := mid (-108286/1000000) (-108279/1000000)
      plusFirst := mid (-7331/125000) (-3664/62500)
      minusSecond := mid (-8244/1000000) (-8153/1000000)
      plusSecond := mid (6377/250000) (12783/500000)
      minusValueError := rad (31877/1000000) (31965/1000000)
      plusValueError := rad (-9117/500000) (-2273/125000)
      minusFirstError := rad (-108286/1000000) (-108279/1000000)
      plusFirstError := rad (-7331/125000) (-3664/62500)
      minusSecondError := rad (-8244/1000000) (-8153/1000000)
      plusSecondError := rad (6377/250000) (12783/500000) }
  | ⟨5, _⟩ => {
      minusValue := mid (-23781/1000000) (-23716/1000000)
      plusValue := mid (15201/1000000) (15241/1000000)
      minusFirst := mid (79889/1000000) (79899/1000000)
      plusFirst := mid (24581/500000) (49179/1000000)
      minusSecond := mid (10693/1000000) (10761/1000000)
      plusSecond := mid (-20381/1000000) (-10167/500000)
      minusValueError := rad (-23781/1000000) (-23716/1000000)
      plusValueError := rad (15201/1000000) (15241/1000000)
      minusFirstError := rad (79889/1000000) (79899/1000000)
      plusFirstError := rad (24581/500000) (49179/1000000)
      minusSecondError := rad (10693/1000000) (10761/1000000)
      plusSecondError := rad (-20381/1000000) (-10167/500000) }
  | ⟨6, _⟩ => {
      minusValue := mid (18882/1000000) (18934/1000000)
      plusValue := mid (-13093/1000000) (-6529/500000)
      minusFirst := mid (-63299/1000000) (-63289/1000000)
      plusFirst := mid (-42343/1000000) (-5291/125000)
      minusSecond := mid (-10722/1000000) (-10667/1000000)
      plusSecond := mid (3371/200000) (8447/500000)
      minusValueError := rad (18882/1000000) (18934/1000000)
      plusValueError := rad (-13093/1000000) (-6529/500000)
      minusFirstError := rad (-63299/1000000) (-63289/1000000)
      plusFirstError := rad (-42343/1000000) (-5291/125000)
      minusSecondError := rad (-10722/1000000) (-10667/1000000)
      plusSecondError := rad (3371/200000) (8447/500000) }

private theorem production_value_errors {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (∀ j, |Real.sinc (CurrentKernelDerivatives.minusArgument j x) -
      (productionRow j).minusValue| ≤ (productionRow j).minusValueError) ∧
    (∀ j, |Real.sinc (CurrentKernelDerivatives.plusArgument j x) -
      (productionRow j).plusValue| ≤ (productionRow j).plusValueError) := by
  have hc := argument_cells hx
  constructor
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (minusZero_sound
        (by simpa [minusCenter] using hc.1 (0 : Fin 7))).1
    · exact abs_sub_mid_le (minusOne_sound
        (by simpa [minusCenter] using hc.1 (1 : Fin 7))).1
    · exact abs_sub_mid_le (minusTwo_sound
        (by simpa [minusCenter] using hc.1 (2 : Fin 7))).1
    · exact abs_sub_mid_le (minusThree_sound
        (by simpa [minusCenter] using hc.1 (3 : Fin 7))).1
    · exact abs_sub_mid_le (minusFour_sound
        (by simpa [minusCenter] using hc.1 (4 : Fin 7))).1
    · exact abs_sub_mid_le (minusFive_sound
        (by simpa [minusCenter] using hc.1 (5 : Fin 7))).1
    · exact abs_sub_mid_le (minusSix_sound
        (by simpa [minusCenter] using hc.1 (6 : Fin 7))).1
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (plusZero_sound
        (by simpa [plusCenter] using hc.2 (0 : Fin 7))).1
    · exact abs_sub_mid_le (plusOne_sound
        (by simpa [plusCenter] using hc.2 (1 : Fin 7))).1
    · exact abs_sub_mid_le (plusTwo_sound
        (by simpa [plusCenter] using hc.2 (2 : Fin 7))).1
    · exact abs_sub_mid_le (plusThree_sound
        (by simpa [plusCenter] using hc.2 (3 : Fin 7))).1
    · exact abs_sub_mid_le (plusFour_sound
        (by simpa [plusCenter] using hc.2 (4 : Fin 7))).1
    · exact abs_sub_mid_le (plusFive_sound
        (by simpa [plusCenter] using hc.2 (5 : Fin 7))).1
    · exact abs_sub_mid_le (plusSix_sound
        (by simpa [plusCenter] using hc.2 (6 : Fin 7))).1

private theorem production_first_errors {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (∀ j, |sincD1 (CurrentKernelDerivatives.minusArgument j x) -
      (productionRow j).minusFirst| ≤ (productionRow j).minusFirstError) ∧
    (∀ j, |sincD1 (CurrentKernelDerivatives.plusArgument j x) -
      (productionRow j).plusFirst| ≤ (productionRow j).plusFirstError) := by
  have hc := argument_cells hx
  constructor
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (minusZero_sound
        (by simpa [minusCenter] using hc.1 (0 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusOne_sound
        (by simpa [minusCenter] using hc.1 (1 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusTwo_sound
        (by simpa [minusCenter] using hc.1 (2 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusThree_sound
        (by simpa [minusCenter] using hc.1 (3 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusFour_sound
        (by simpa [minusCenter] using hc.1 (4 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusFive_sound
        (by simpa [minusCenter] using hc.1 (5 : Fin 7))).2.1
    · exact abs_sub_mid_le (minusSix_sound
        (by simpa [minusCenter] using hc.1 (6 : Fin 7))).2.1
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (plusZero_sound
        (by simpa [plusCenter] using hc.2 (0 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusOne_sound
        (by simpa [plusCenter] using hc.2 (1 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusTwo_sound
        (by simpa [plusCenter] using hc.2 (2 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusThree_sound
        (by simpa [plusCenter] using hc.2 (3 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusFour_sound
        (by simpa [plusCenter] using hc.2 (4 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusFive_sound
        (by simpa [plusCenter] using hc.2 (5 : Fin 7))).2.1
    · exact abs_sub_mid_le (plusSix_sound
        (by simpa [plusCenter] using hc.2 (6 : Fin 7))).2.1

private theorem production_second_errors {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (∀ j, |sincD2 (CurrentKernelDerivatives.minusArgument j x) -
      (productionRow j).minusSecond| ≤ (productionRow j).minusSecondError) ∧
    (∀ j, |sincD2 (CurrentKernelDerivatives.plusArgument j x) -
      (productionRow j).plusSecond| ≤ (productionRow j).plusSecondError) := by
  have hc := argument_cells hx
  constructor
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (minusZero_sound
        (by simpa [minusCenter] using hc.1 (0 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusOne_sound
        (by simpa [minusCenter] using hc.1 (1 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusTwo_sound
        (by simpa [minusCenter] using hc.1 (2 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusThree_sound
        (by simpa [minusCenter] using hc.1 (3 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusFour_sound
        (by simpa [minusCenter] using hc.1 (4 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusFive_sound
        (by simpa [minusCenter] using hc.1 (5 : Fin 7))).2.2
    · exact abs_sub_mid_le (minusSix_sound
        (by simpa [minusCenter] using hc.1 (6 : Fin 7))).2.2
  · intro j
    fin_cases j
    · exact abs_sub_mid_le (plusZero_sound
        (by simpa [plusCenter] using hc.2 (0 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusOne_sound
        (by simpa [plusCenter] using hc.2 (1 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusTwo_sound
        (by simpa [plusCenter] using hc.2 (2 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusThree_sound
        (by simpa [plusCenter] using hc.2 (3 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusFour_sound
        (by simpa [plusCenter] using hc.2 (4 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusFive_sound
        (by simpa [plusCenter] using hc.2 (5 : Fin 7))).2.2
    · exact abs_sub_mid_le (plusSix_sound
        (by simpa [plusCenter] using hc.2 (6 : Fin 7))).2.2

private theorem production_kernel_bounds {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (-27161 / 1000000 : ℝ) ≤ CurrentKernelFormula.closedKernel x ∧
      CurrentKernelFormula.closedKernel x ≤ 0 := by
  have he := production_value_errors hx
  have h := CurrentKernelDerivatives.abs_closedKernel_sub_approximateKernel_le
    x productionRow he.1 he.2
  rw [abs_le] at h
  norm_num [CurrentKernelDerivatives.approximateKernel,
    CurrentKernelDerivatives.kernelError, productionRow, mid, rad,
    CurrentWindow.coefficient, Fin.sum_univ_succ, Fin.succ] at h ⊢
  constructor <;> linarith [h.1, h.2]

private theorem production_kernelD1_bounds {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    CurrentKernelDerivatives.closedKernelD1 x ≤ -741272 / 1000000 ∧
      (-741272 / 1000000 : ℝ) ≤ 0 := by
  have he := production_first_errors hx
  have h := CurrentKernelDerivatives.abs_closedKernelD1_sub_approximateKernelD1_le
    x productionRow he.1 he.2
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le] at h
  norm_num [CurrentKernelDerivatives.approximateKernelD1,
    CurrentKernelDerivatives.kernelD1Error, productionRow, mid, rad,
    CurrentWindow.coefficient, Fin.sum_univ_succ, Fin.succ, abs_mul,
    abs_of_pos Real.pi_pos] at h ⊢
  have hpi : Real.pi <
      (314159265358979323847 : ℝ) / 10 ^ 20 := hp.2
  nlinarith [h.2]

private theorem production_kernelD2_bounds {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    0 ≤ CurrentKernelDerivatives.closedKernelD2 x ∧
      CurrentKernelDerivatives.closedKernelD2 x ≤ 1868189 / 1000000 := by
  have he := production_second_errors hx
  have h := CurrentKernelDerivatives.abs_closedKernelD2_sub_approximateKernelD2_le
    x productionRow he.1 he.2
  have hp := TranscendentalBounds.pi_rational_bounds
  rw [abs_le] at h
  norm_num [CurrentKernelDerivatives.approximateKernelD2,
    CurrentKernelDerivatives.kernelD2Error, productionRow, mid, rad,
    CurrentWindow.coefficient, Fin.sum_univ_succ, Fin.succ, abs_mul, abs_pow,
    abs_of_pos Real.pi_pos] at h ⊢
  have hpLo : (314159265358979323846 : ℝ) / 10 ^ 20 < Real.pi := hp.1
  have hpHi : Real.pi <
      (314159265358979323847 : ℝ) / 10 ^ 20 := hp.2
  constructor <;> nlinarith [h.1, h.2, Real.pi_pos]

private lemma sinc_nat_mul_pi_eq_zero (k : ℕ) (hk : k ≠ 0) :
    Real.sinc ((k : ℝ) * Real.pi) = 0 := by
  rw [Real.sinc_of_ne_zero]
  · rw [Real.sin_nat_mul_pi]
    norm_num
  · exact mul_ne_zero (Nat.cast_ne_zero.mpr hk) Real.pi_ne_zero

private theorem closedKernel_zero_eq :
    CurrentKernelFormula.closedKernel 0 = Real.sinc (Real.sqrt 2 / 2) := by
  unfold CurrentKernelFormula.closedKernel
  have h1 := sinc_nat_mul_pi_eq_zero 1 (by norm_num)
  have h2 := sinc_nat_mul_pi_eq_zero 2 (by norm_num)
  have h3 := sinc_nat_mul_pi_eq_zero 3 (by norm_num)
  have h4 := sinc_nat_mul_pi_eq_zero 4 (by norm_num)
  have h5 := sinc_nat_mul_pi_eq_zero 5 (by norm_num)
  have h6 := sinc_nat_mul_pi_eq_zero 6 (by norm_num)
  norm_num [CurrentWindow.frequency, CurrentWindow.coefficient,
    Fin.sum_univ_succ, Fin.succ] at h1 h2 h3 h4 h5 h6 ⊢
  simp only [show 2 * Real.pi * 3 / 2 = 3 * Real.pi by ring,
    show 2 * Real.pi * 4 / 2 = 4 * Real.pi by ring,
    show 2 * Real.pi * 5 / 2 = 5 * Real.pi by ring,
    show 2 * Real.pi * 6 / 2 = 6 * Real.pi by ring]
  rw [h1, h2, h3, h4, h5, h6]
  ring

/-- Full kernel-checked semantic replay of the production tangent row at cell
4376, from the fourteen sinc-jet witnesses through the final `w''` scalar
comparison. -/
theorem cell4376_semantic {x : ℝ}
    (hx : x ∈ Icc ((4376 : ℝ) / 4000) (4377 / 4000)) :
    (CurrentKernelDerivatives.cell4376Lower : ℝ) ≤
      CurrentKernelDerivatives.closedWeightD2 x := by
  have hk := production_kernel_bounds hx
  have hk1 := production_kernelD1_bounds hx
  have hk2 := production_kernelD2_bounds hx
  have hk0 := CurrentKernelDerivatives.sinc_sqrt_two_half_bounds
  have hk0' : (918707 / 1000000 : ℝ) ≤
      CurrentKernelFormula.closedKernel 0 ∧
      CurrentKernelFormula.closedKernel 0 ≤ 918744 / 1000000 := by
    simpa [closedKernel_zero_eq] using hk0
  apply CurrentKernelDerivatives.closedWeightD2_lower_of_sign_bounds
    (lower := (CurrentKernelDerivatives.cell4376Lower : ℝ))
    (kLower := (-27161 / 1000000 : ℝ))
    (k1Upper := (-741272 / 1000000 : ℝ))
    (k2Upper := (1868189 / 1000000 : ℝ))
    (k0Upper := (918744 / 1000000 : ℝ))
  · norm_num [CurrentKernelDerivatives.cell4376Lower]
  · exact hk.1
  · exact hk.2
  · exact hk1.1
  · exact hk1.2
  · exact hk2.1
  · exact hk2.2
  · linarith [hk0'.1]
  · exact hk0'.2
  · exact CurrentKernelDerivatives.cell4376_scalar_check

end Zeta23Ext.ProductionCell4376Jets

end
