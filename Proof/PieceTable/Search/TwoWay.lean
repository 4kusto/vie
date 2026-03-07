-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.SplitIfs
import ViE.Data.PieceTable.Tree

set_option linter.unnecessarySimpa false

namespace Proof.PieceTable.Search

open ViE
open Classical

def matchesRange (haystack needle : ByteArray) (pos start stop : Nat) : Prop :=
  ∀ j, start ≤ j → j < stop → haystack[pos + j]! = needle[j]!

noncomputable def matchesAt (haystack needle : ByteArray) (pos : Nat) : Bool :=
  decide (pos + needle.size ≤ haystack.size ∧ matchesRange haystack needle pos 0 needle.size)

def mismatchAt (haystack needle : ByteArray) (pos j : Nat) : Prop :=
  haystack[pos + j]! ≠ needle[j]!

noncomputable def firstMatchFrom (haystack needle : ByteArray) (start : Nat) : Option Nat :=
  if needle.size = 0 then
    some start
  else if haystack.size < needle.size || start + needle.size > haystack.size then
    none
  else
    let maxStart := haystack.size - needle.size
    let rec loop (i : Nat) : Option Nat :=
      if i > maxStart then
        none
      else if matchesAt haystack needle i then
        some i
      else
        loop (i + 1)
      termination_by maxStart + 1 - i
      decreasing_by
        omega
    loop start

inductive ShortStep where
  | stop
  | accept (pos : Nat)
  | period (nextI : Nat) (nextMem : Int)
  | shift (nextI : Nat)
  deriving Repr, DecidableEq

def ShortMemInv
    (haystack needle : ByteArray)
    (i n pNat : Nat) (mem : Int) : Prop :=
  mem = -1 ∨
    (mem = Int.ofNat (n - pNat - 1) ∧ matchesRange haystack needle i 0 (n - pNat))

def NeedlePeriodInv (needle : ByteArray) (n pNat : Nat) : Prop :=
  ∀ j, j < n - pNat → needle[j]! = needle[j + pNat]!

def ShortLoopInv
    (haystack needle : ByteArray)
    (i n pNat : Nat) (mem : Int) : Prop :=
  NeedlePeriodInv needle n pNat ∧ ShortMemInv haystack needle i n pNat mem

def ShortSavedPrefix
    (haystack needle : ByteArray)
    (i n pNat : Nat) : Prop :=
  matchesRange haystack needle i 0 (n - pNat)

def MaxSufStateInv (m ms j k p : Int) : Prop :=
  -1 ≤ ms ∧ ms < j ∧ 0 < k ∧ k ≤ p ∧ 0 < p ∧ p ≤ m ∧ ms < m

/-- Semantic invariant for maximal-suffix states: if the current split point
is still negative, then the candidate period already repeats across the prefix
explored so far. This weaker prefix-periodicity is the form that can actually
hold at the initial state `ms = -1, p = 1`. -/
def PrefixPeriodInv (x : ByteArray) (j p : Int) : Prop :=
  ∀ t : Nat, t + Int.toNat p < Int.toNat j -> x[t]! = x[t + Int.toNat p]!

/-- Semantic invariant for maximal-suffix states: a negative split point means
that the current candidate period is valid on the explored prefix `j`. -/
def MaxSufNegPeriodicInv (x : ByteArray) (ms j p : Int) : Prop :=
  ms < 0 -> PrefixPeriodInv x j p

/-- Full proof-side state invariant for maximal-suffix search: numeric bounds
plus the semantic fact needed when the split point is still negative. -/
def MaxSufFullInv (x : ByteArray) (m ms j k p : Int) : Prop :=
  MaxSufStateInv m ms j k p ∧ MaxSufNegPeriodicInv x ms j p

/-- At the initial maximal-suffix state the explored prefix is empty, so the
prefix-periodicity invariant holds vacuously. -/
theorem maxSufNegPeriodicInv_init
    (x : ByteArray) :
    MaxSufNegPeriodicInv x (-1) 0 1 := by
  intro _ t ht
  omega

/-- The standard initial maximal-suffix state satisfies both the numeric and
semantic invariants used by the proof development. -/
theorem maxSufFullInv_init
    (x : ByteArray) (m : Int)
    (hm : 0 < m) :
    MaxSufFullInv x m (-1) 0 1 1 := by
  constructor
  · dsimp [MaxSufStateInv]
    omega
  · exact maxSufNegPeriodicInv_init x

/-- Once prefix-periodicity reaches the full explored length `m`, it upgrades
to an actual period witness for the whole needle. -/
theorem needlePeriodInv_of_prefixPeriod_full
    (x : ByteArray) (m j p : Int)
    (hj : j = m)
    (hprefix : PrefixPeriodInv x j p) :
    NeedlePeriodInv x (Int.toNat m) (Int.toNat p) := by
  intro t ht
  have hltm : t + Int.toNat p < Int.toNat m := by
    omega
  have hlt : t + Int.toNat p < Int.toNat j := by
    simpa [hj] using hltm
  exact hprefix t hlt

inductive MaxSufStep where
  | stop
  | lt (ms' j' k' p' : Int)
  | eqExtend (ms' j' k' p' : Int)
  | eqJump (ms' j' k' p' : Int)
  | gt (ms' j' k' p' : Int)
  deriving Repr, DecidableEq

def MaxSufState := Int × Int × Int × Int

def maxSufNextState (step : MaxSufStep) : Option MaxSufState :=
  match step with
  | .stop => none
  | .lt ms' j' k' p' => some (ms', j', k', p')
  | .eqExtend ms' j' k' p' => some (ms', j', k', p')
  | .eqJump ms' j' k' p' => some (ms', j', k', p')
  | .gt ms' j' k' p' => some (ms', j', k', p')

def maxSufLoopStep
    (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (steps : Nat) : MaxSufStep :=
  if steps = 0 || ¬ (j + k < m) then
    .stop
  else
    let a := x[Int.toNat (j + k)]!
    let b := x[Int.toNat (ms + k)]!
    if useLe then
      if a < b then
        let jk := j + k
        .lt ms jk 1 (jk - ms)
      else if a == b then
        if k != p then
          .eqExtend ms j (k + 1) p
        else
          .eqJump ms (j + p) 1 p
      else
        .gt j (j + 1) 1 1
    else if a > b then
      let jk := j + k
      .lt ms jk 1 (jk - ms)
    else if a == b then
      if k != p then
        .eqExtend ms j (k + 1) p
      else
        .eqJump ms (j + p) 1 p
    else
      .gt j (j + 1) 1 1

def maxSufFollow
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat)
    (ms j k p : Int) : (Int × Int) :=
  if steps = 0 then
    (ms, p)
  else
    match maxSufNextState (maxSufLoopStep x useLe m ms j k p steps) with
    | none => (ms, p)
    | some (ms', j', k', p') => maxSufFollow x useLe m (steps - 1) ms' j' k' p'
  termination_by steps
  decreasing_by
    have hsteps : steps ≠ 0 := by assumption
    exact Nat.sub_lt (Nat.pos_of_ne_zero hsteps) (by decide : 0 < 1)

/-- The implementation-side maximal-suffix step computes the same successor
state as the proof-side step descriptor. The proof layer intentionally forgets
the exact branch tag and keeps only the next state. -/
theorem implMaxSufNextState_eq_maxSufLoopStep
    (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (steps : Nat) :
    (match ViE.PieceTree.maximalSuffixStep x useLe m steps ms j k p with
    | .stop => none
    | .next ms' j' k' p' => some (ms', j', k', p')) =
      maxSufNextState (maxSufLoopStep x useLe m ms j k p steps) := by
  unfold ViE.PieceTree.maximalSuffixStep maxSufLoopStep
  split_ifs <;> simp [maxSufNextState]
  all_goals
    split_ifs <;> simp

/-- The implementation-side maximal-suffix loop and the proof-side mirror
return the same split point and period from every initial state. -/
theorem maximalSuffixLoopCore_eq_maxSufFollow
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat) (ms j k p : Int) :
    ViE.PieceTree.maximalSuffixLoopCore x useLe m steps ms j k p =
      maxSufFollow x useLe m steps ms j k p := by
  induction steps generalizing ms j k p with
  | zero =>
      simp [ViE.PieceTree.maximalSuffixLoopCore, maxSufFollow]
  | succ steps ih =>
      unfold ViE.PieceTree.maximalSuffixLoopCore maxSufFollow
      simp
      have hbridge := implMaxSufNextState_eq_maxSufLoopStep x useLe m ms j k p (Nat.succ steps)
      cases himpl : ViE.PieceTree.maximalSuffixStep x useLe m (Nat.succ steps) ms j k p with
      | stop =>
          have hnext : maxSufNextState (maxSufLoopStep x useLe m ms j k p (Nat.succ steps)) = none := by
            simpa [himpl, maxSufNextState] using hbridge.symm
          simp [hnext]
      | next ms' j' k' p' =>
          have hnext : maxSufNextState (maxSufLoopStep x useLe m ms j k p (Nat.succ steps)) = some (ms', j', k', p') := by
            simpa [himpl, maxSufNextState] using hbridge.symm
          simp [hnext, ih ms' j' k' p']

/-- Proof-side wrapper for maximal-suffix search with the same initial state
and step budget as the implementation. -/
def maxSufMirror (x : ByteArray) (useLe : Bool) : Int × Int :=
  let m : Int := x.size
  let steps := ((Int.toNat m) + 1) * ((Int.toNat m) + 1) + 1
  maxSufFollow x useLe m steps (-1) 0 1 1

theorem maxSufStateInv_init
    (m : Int) (hm : 0 < m) :
    MaxSufStateInv m (-1) 0 1 1 := by
  dsimp [MaxSufStateInv]
  omega

/- The strict-less-than branch keeps the maximal-suffix loop inside the numeric
state invariant. -/
theorem maxSufStateInv_step_lt
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p)
    (hjk : j + k < m) :
    MaxSufStateInv m ms (j + k) 1 (j + k - ms) := by
  rcases hinv with ⟨hmslo, hmsj, hk, hkp, hp, hpm, hmsm⟩
  dsimp [MaxSufStateInv]
  omega

/- The equal-byte extension branch only increases the local comparison offset,
so the global bounds remain valid. -/
theorem maxSufStateInv_step_eq_extend
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p)
    (hneq : k != p) :
    MaxSufStateInv m ms j (k + 1) p := by
  rcases hinv with ⟨hmslo, hmsj, hk, hkp, hp, hpm, hmsm⟩
  have hkne : k ≠ p := by simpa using hneq
  have hklt : k < p := by omega
  dsimp [MaxSufStateInv]
  omega

/- Once a full period has matched, the jump branch restarts from `j + p`
without leaving the invariant region. -/
theorem maxSufStateInv_step_eq_jump
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p) :
    MaxSufStateInv m ms (j + p) 1 p := by
  rcases hinv with ⟨hmslo, hmsj, hk, hkp, hp, hpm, hmsm⟩
  dsimp [MaxSufStateInv]
  omega

/- Replacing the candidate split point with `j` re-enters the invariant with
the canonical local state `(j + 1, 1, 1)`. -/
theorem maxSufStateInv_step_gt
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p)
    (hjk : j < m) :
    MaxSufStateInv m j (j + 1) 1 1 := by
  rcases hinv with ⟨hmslo, hmsj, hk, hkp, hp, hpm, hmsm⟩
  dsimp [MaxSufStateInv]
  omega

/- The equal-extension branch does not change `ms`, `j`, or `p`, so the
negative-prefix periodicity invariant is preserved unchanged. -/
theorem maxSufNegPeriodicInv_step_eqExtend
    (x : ByteArray) (ms j p : Int)
    (hinv : MaxSufNegPeriodicInv x ms j p) :
    MaxSufNegPeriodicInv x ms j p := by
  exact hinv

/- Entering the `gt` branch replaces the split point with the nonnegative
index `j`, so the negative-periodicity invariant becomes vacuous. -/
theorem maxSufNegPeriodicInv_step_gt
    (x : ByteArray) (m ms j k p : Int)
    (hnum : MaxSufStateInv m ms j k p) :
    MaxSufNegPeriodicInv x j (j + 1) 1 := by
  intro hjneg
  rcases hnum with ⟨hmslo, hmsj, _, _, _, _, _⟩
  have hnonnegj : 0 ≤ j := by omega
  omega

/- The combined invariant is preserved immediately by the `eqExtend` branch. -/
theorem maxSufFullInv_step_eqExtend
    (x : ByteArray) (m ms j k p : Int)
    (hinv : MaxSufFullInv x m ms j k p)
    (hneq : k != p) :
    MaxSufFullInv x m ms j (k + 1) p := by
  rcases hinv with ⟨hnum, hsem⟩
  exact ⟨maxSufStateInv_step_eq_extend m ms j k p hnum hneq, maxSufNegPeriodicInv_step_eqExtend x ms j p hsem⟩

/- The combined invariant is also preserved immediately by the `gt` branch,
because the semantic part becomes vacuous after the split point turns
nonnegative. -/
theorem maxSufFullInv_step_gt
    (x : ByteArray) (m ms j k p : Int)
    (hinv : MaxSufFullInv x m ms j k p)
    (hjk : j < m) :
    MaxSufFullInv x m j (j + 1) 1 1 := by
  rcases hinv with ⟨hnum, _⟩
  exact ⟨maxSufStateInv_step_gt m ms j k p hnum hjk, maxSufNegPeriodicInv_step_gt x m ms j k p hnum⟩

/-- Under the numeric maximal-suffix invariant, a negative split point can only
be the sentinel value `-1`. This reduces all semantic reasoning about negative
states to a single concrete case. -/
theorem maxSufStateInv_neg_ms_eq_negOne
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p)
    (hms : ms < 0) :
    ms = -1 := by
  rcases hinv with ⟨hlo, _, _, _, _, _, _⟩
  omega

/-- Semantic payload required to preserve prefix periodicity across an
`eqJump` transition. The already-known prefix periodicity is not sufficient on
its own; one also needs equality on the newly exposed block. -/
def EqJumpBlockMatches (x : ByteArray) (j p : Int) : Prop :=
  ∀ t : Nat,
    Int.toNat j ≤ t ->
    t < Int.toNat j + Int.toNat p ->
    x[t - Int.toNat p]! = x[t]!

/-- Local comparison-window invariant for maximal-suffix search. In the actual
algorithm, `k` is the next offset to compare, so the already-matched offsets
are exactly `1 .. k-1`. This is the right abstraction for the PieceTree/B+tree
setting as well: the tree only exposes bytes, while the proof tracks equality
of the currently compared local windows. -/
def ComparedWindowInv (x : ByteArray) (ms j k : Int) : Prop :=
  ∀ t : Nat,
    t < Int.toNat k - 1 ->
    x[Int.toNat (ms + 1 + t)]! = x[Int.toNat (j + 1 + t)]!

/-- At the initial maximal-suffix state there are no already-matched offsets,
so the local window invariant is vacuous. -/
theorem comparedWindowInv_init
    (x : ByteArray) :
    ComparedWindowInv x (-1) 0 1 := by
  intro t ht
  omega

/-- Extending the local comparison window by one matching byte preserves the
window invariant. This is the semantic payload carried by the `eqExtend`
branch before the search decides whether to extend further or jump by a full
period. -/
theorem comparedWindowInv_step_eqExtend
    (x : ByteArray) (ms j k : Int)
    (hk : 0 < k)
    (hwin : ComparedWindowInv x ms j k)
    (hmatch : x[Int.toNat (ms + k)]! = x[Int.toNat (j + k)]!) :
    ComparedWindowInv x ms j (k + 1) := by
  intro t ht
  by_cases htk : t < Int.toNat k - 1
  · exact hwin t htk
  · have htEq : t = Int.toNat k - 1 := by omega
    subst htEq
    have hk0 : 0 ≤ k := by omega
    have hk_toNat : ((Int.toNat k : Nat) : Int) = k := by
      exact Int.toNat_of_nonneg hk0
    have hcast : ((Int.toNat k - 1 : Nat) : Int) = k - 1 := by
      calc
        (((Int.toNat k - 1 : Nat) : Int)) = ((Int.toNat k : Nat) : Int) - 1 := by
          omega
        _ = k - 1 := by simpa [hk_toNat]
    have hleft :
        Int.toNat (ms + 1 + (Int.toNat k - 1 : Nat)) = Int.toNat (ms + k) := by
      have hleftInt : ms + 1 + (Int.toNat k - 1 : Nat) = ms + k := by
        rw [hcast]
        omega
      exact congrArg Int.toNat hleftInt
    have hright :
        Int.toNat (j + 1 + (Int.toNat k - 1 : Nat)) = Int.toNat (j + k) := by
      have hrightInt : j + 1 + (Int.toNat k - 1 : Nat) = j + k := by
        rw [hcast]
        omega
      exact congrArg Int.toNat hrightInt
    simpa [hleft, hright] using hmatch

/-- The semantic content of the current maximal-suffix comparison window is
that the two segments `[ms+1, ms+k]` and `[j+1, j+k]` are bytewise equal. This
is the local fact that the PieceTree/B+tree search actually observes before any
global periodicity argument is applied. -/
def ComparedSegmentEq (x : ByteArray) (ms j k : Int) : Prop :=
  ∀ t : Nat,
    t < Int.toNat k ->
    x[Int.toNat (ms + 1 + t)]! = x[Int.toNat (j + 1 + t)]!

/-- In the negative-split case, the compared segment equality says that the new
block `[j+1, j+1+p)` matches the prefix block `[0, p)`. This is the exact
local fact exposed by the maximal-suffix step before it is translated into the
periodic block relation needed by the `eqJump` proof. -/
def PrefixBlockMatches (x : ByteArray) (j p : Int) : Prop :=
  ∀ t : Nat,
    Int.toNat (j + 1) ≤ t ->
    t < Int.toNat (j + 1) + Int.toNat p ->
    x[t - Int.toNat (j + 1)]! = x[t]!

/-- In the negative-split case, the boundary `j + 1` is the amount of prefix
that has already been validated. To turn a prefix block match into the suffix
block match needed by `eqJump`, one needs this boundary to be aligned to the
candidate period. -/
def PrefixBoundaryAligned (j p : Int) : Prop :=
  ∃ q : Nat, Int.toNat (j + 1) = q * Int.toNat p

/-- A local comparison window together with the current matching byte yields
full equality of the compared segments. This packages the exact information
produced by the `eqExtend`/`eqJump` tests before it is translated into
periodicity on the already explored prefix. -/
theorem comparedWindowInv_to_segmentEq
    (x : ByteArray) (ms j k : Int)
    (hk : 0 < k)
    (hwin : ComparedWindowInv x ms j k)
    (hmatch : x[Int.toNat (ms + k)]! = x[Int.toNat (j + k)]!) :
    ComparedSegmentEq x ms j k := by
  intro t ht
  by_cases hlt : t < Int.toNat k - 1
  · exact hwin t hlt
  · have htEq : t = Int.toNat k - 1 := by omega
    subst htEq
    have hk0 : 0 ≤ k := by omega
    have hk_toNat : ((Int.toNat k : Nat) : Int) = k := by
      exact Int.toNat_of_nonneg hk0
    have hcast : ((Int.toNat k - 1 : Nat) : Int) = k - 1 := by
      calc
        (((Int.toNat k - 1 : Nat) : Int)) = ((Int.toNat k : Nat) : Int) - 1 := by
          omega
        _ = k - 1 := by simpa [hk_toNat]
    have hleft :
        Int.toNat (ms + 1 + (Int.toNat k - 1 : Nat)) = Int.toNat (ms + k) := by
      have hleftInt : ms + 1 + (Int.toNat k - 1 : Nat) = ms + k := by
        rw [hcast]
        omega
      exact congrArg Int.toNat hleftInt
    have hright :
        Int.toNat (j + 1 + (Int.toNat k - 1 : Nat)) = Int.toNat (j + k) := by
      have hrightInt : j + 1 + (Int.toNat k - 1 : Nat) = j + k := by
        rw [hcast]
        omega
      exact congrArg Int.toNat hrightInt
    simpa [hleft, hright] using hmatch

/-- For the sentinel split point `ms = -1`, segment equality becomes equality
between the freshly exposed block and the prefix block of the same length. -/
theorem comparedSegmentEq_neg_to_prefixBlockMatches
    (x : ByteArray) (j p : Int)
    (hj1 : 0 ≤ j + 1)
    (hseg : ComparedSegmentEq x (-1) j p) :
    PrefixBlockMatches x j p := by
  intro t hlo hhi
  have hs_lt : t - Int.toNat (j + 1) < Int.toNat p := by
    omega
  have hseg' := hseg (t - Int.toNat (j + 1)) hs_lt
  have hleft :
      Int.toNat (-1 + 1 + (t - Int.toNat (j + 1) : Nat)) = t - Int.toNat (j + 1) := by
    simp
  have hright :
      Int.toNat (j + 1 + (t - Int.toNat (j + 1) : Nat)) = t := by
    have hsub : Int.toNat (j + 1) + (t - Int.toNat (j + 1)) = t := by
      omega
    have hj1_toNat : ((Int.toNat (j + 1) : Nat) : Int) = j + 1 := by
      exact Int.toNat_of_nonneg hj1
    have hrightInt : j + 1 + (t - Int.toNat (j + 1) : Nat) = t := by
      rw [← hj1_toNat] at hsub
      omega
    exact congrArg Int.toNat hrightInt
  simpa [hleft, hright] using hseg'

/-- If a prefix is `p`-periodic, then every position inside the prefix agrees
with the position obtained by repeatedly adding `p`, as long as the target
stays inside the validated prefix. -/
theorem prefixPeriodInv_iterate
    (x : ByteArray) (j p : Int)
    (hp : 0 < p)
    (hprefix : PrefixPeriodInv x j p)
    (s q : Nat)
    (hbound : q * Int.toNat p + s < Int.toNat j) :
    x[s]! = x[q * Int.toNat p + s]! := by
  induction q with
  | zero =>
      simp
  | succ q ih =>
      have hq : q * Int.toNat p + s < Int.toNat j := by
        have hpNat : 0 < Int.toNat p := by
          have hp0 : 0 ≤ p := by omega
          simpa [Int.toNat_of_nonneg hp0] using hp
        have hlt :
            q * Int.toNat p + s < q * Int.toNat p + s + Int.toNat p := by
          exact Nat.lt_add_of_pos_right hpNat
        have hplus : q * Int.toNat p + s + Int.toNat p < Int.toNat j := by
          simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
        exact lt_trans hlt hplus
      have hstep : q * Int.toNat p + s + Int.toNat p < Int.toNat j := by
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbound
      have hlocal : x[q * Int.toNat p + s]! = x[(q + 1) * Int.toNat p + s]! := by
        have := hprefix (q * Int.toNat p + s)
        simpa [Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this hstep
      exact Eq.trans (ih hq) hlocal

/-- If the newly exposed block matches the preceding one, prefix periodicity
extends from `j` to `j + p`. This isolates the exact remaining obligation of
the `eqJump` branch. -/
theorem prefixPeriodInv_extend_by_blockMatch
    (x : ByteArray) (j p : Int)
    (hprefix : PrefixPeriodInv x j p)
    (hblock : EqJumpBlockMatches x j p) :
    PrefixPeriodInv x (j + p) p := by
  intro t ht
  by_cases hlt : t + Int.toNat p < Int.toNat j
  · exact hprefix t hlt
  · have hge : Int.toNat j ≤ t + Int.toNat p := by omega
    have hupper : t + Int.toNat p < Int.toNat j + Int.toNat p := by omega
    simpa [Nat.add_sub_cancel] using hblock (t + Int.toNat p) hge hupper


/- In the `lt` branch, a negative split point must be `-1`, so the new period
`j + k - ms` is strictly larger than the new explored prefix `j + k`. Hence the
prefix-periodicity invariant becomes vacuous. -/
theorem maxSufNegPeriodicInv_step_lt
    (x : ByteArray) (m ms j k p : Int)
    (hnum : MaxSufStateInv m ms j k p)
    (_hjk : j + k < m) :
    MaxSufNegPeriodicInv x ms (j + k) (j + k - ms) := by
  intro hms
  have hms' : ms = -1 := maxSufStateInv_neg_ms_eq_negOne m ms j k p hnum hms
  intro t ht
  have hpbig : Int.toNat (j + k) < Int.toNat (j + k - ms) := by
    subst hms'
    omega
  omega

/- The combined invariant is preserved by the `lt` branch: numeric bounds come
from the existing arithmetic lemma, and the semantic part is vacuous in the
only negative case. -/
theorem maxSufFullInv_step_lt
    (x : ByteArray) (m ms j k p : Int)
    (hinv : MaxSufFullInv x m ms j k p)
    (hjk : j + k < m) :
    MaxSufFullInv x m ms (j + k) 1 (j + k - ms) := by
  rcases hinv with ⟨hnum, _⟩
  exact ⟨maxSufStateInv_step_lt m ms j k p hnum hjk, maxSufNegPeriodicInv_step_lt x m ms j k p hnum hjk⟩

/- The negative-prefix periodicity invariant is preserved by an `eqJump`
transition once the newly exposed block is known to match the previous one. -/
theorem maxSufNegPeriodicInv_step_eqJump
    (x : ByteArray) (m ms j k p : Int)
    (hinv : MaxSufFullInv x m ms j k p)
    (hblock : EqJumpBlockMatches x j p) :
    MaxSufNegPeriodicInv x ms (j + p) p := by
  rcases hinv with ⟨_, hsem⟩
  intro hms
  exact prefixPeriodInv_extend_by_blockMatch x j p (hsem hms) hblock

/- The combined invariant is preserved by the `eqJump` branch once the proof
supplies equality on the newly exposed block. This isolates the exact semantic
payload still missing from the preprocessing proof. -/
theorem maxSufFullInv_step_eqJump
    (x : ByteArray) (m ms j k p : Int)
    (hinv : MaxSufFullInv x m ms j k p)
    (hblock : EqJumpBlockMatches x j p) :
    MaxSufFullInv x m ms (j + p) 1 p := by
  rcases hinv with ⟨hnum, hsem⟩
  exact ⟨maxSufStateInv_step_eq_jump m ms j k p hnum, by
    intro hms
    exact prefixPeriodInv_extend_by_blockMatch x j p (hsem hms) hblock⟩

@[simp] theorem maxSufLoopStep_stop_of_stop
    (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (steps : Nat)
    (h : steps = 0 || ¬ (j + k < m)) :
    maxSufLoopStep x useLe m ms j k p steps = .stop := by
  unfold maxSufLoopStep
  rw [if_pos h]

@[simp] theorem maxSufLoopStep_lt_of_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : x[Int.toNat (j + k)]! < x[Int.toNat (ms + k)]!) :
    maxSufLoopStep x true m ms j k p steps = .lt ms (j + k) 1 (j + k - ms) := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab]

@[simp] theorem maxSufLoopStep_eqExtend_of_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (j + k)]! < x[Int.toNat (ms + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true)
    (hkp : k != p) :
    maxSufLoopStep x true m ms j k p steps = .eqExtend ms j (k + 1) p := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq, hkp]

@[simp] theorem maxSufLoopStep_eqJump_of_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (j + k)]! < x[Int.toNat (ms + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true)
    (hkp : ¬ k != p) :
    maxSufLoopStep x true m ms j k p steps = .eqJump ms (j + p) 1 p := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq, hkp]

@[simp] theorem maxSufLoopStep_gt_of_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (j + k)]! < x[Int.toNat (ms + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = false) :
    maxSufLoopStep x true m ms j k p steps = .gt j (j + 1) 1 1 := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq]

@[simp] theorem maxSufLoopStep_lt_of_not_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : x[Int.toNat (ms + k)]! < x[Int.toNat (j + k)]!) :
    maxSufLoopStep x false m ms j k p steps = .lt ms (j + k) 1 (j + k - ms) := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab]

@[simp] theorem maxSufLoopStep_eqExtend_of_not_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (ms + k)]! < x[Int.toNat (j + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true)
    (hkp : k != p) :
    maxSufLoopStep x false m ms j k p steps = .eqExtend ms j (k + 1) p := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq, hkp]

@[simp] theorem maxSufLoopStep_eqJump_of_not_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (ms + k)]! < x[Int.toNat (j + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true)
    (hkp : ¬ k != p) :
    maxSufLoopStep x false m ms j k p steps = .eqJump ms (j + p) 1 p := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq, hkp]

@[simp] theorem maxSufLoopStep_gt_of_not_useLe
    (x : ByteArray) (m ms j k p : Int) (steps : Nat)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m)))
    (hab : ¬ x[Int.toNat (ms + k)]! < x[Int.toNat (j + k)]!)
    (hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = false) :
    maxSufLoopStep x false m ms j k p steps = .gt j (j + 1) 1 1 := by
  unfold maxSufLoopStep
  rw [if_neg hStop]
  simp [hab, hEq]

theorem maxSufStateInv_preserved_by_step
    (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (steps : Nat)
    (hinv : MaxSufStateInv m ms j k p)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m))) :
    match maxSufLoopStep x useLe m ms j k p steps with
    | .stop => False
    | .lt ms' j' k' p' => MaxSufStateInv m ms' j' k' p'
    | .eqExtend ms' j' k' p' => MaxSufStateInv m ms' j' k' p'
    | .eqJump ms' j' k' p' => MaxSufStateInv m ms' j' k' p'
    | .gt ms' j' k' p' => MaxSufStateInv m ms' j' k' p' := by
  have hjk : j + k < m := by
    by_contra h
    exact hStop (by simp [h])
  have hinv' := hinv
  rcases hinv with ⟨_, _, hk, _, _, _⟩
  cases hUse : useLe with
  | false =>
    by_cases hab : x[Int.toNat (ms + k)]! < x[Int.toNat (j + k)]!
    · rw [maxSufLoopStep_lt_of_not_useLe x m ms j k p steps hStop hab]
      exact maxSufStateInv_step_lt m ms j k p hinv' hjk
    · by_cases hEq0 : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true
      · by_cases hkp : k != p
        · rw [maxSufLoopStep_eqExtend_of_not_useLe x m ms j k p steps hStop hab hEq0 hkp]
          exact maxSufStateInv_step_eq_extend m ms j k p hinv' hkp
        · rw [maxSufLoopStep_eqJump_of_not_useLe x m ms j k p steps hStop hab hEq0 hkp]
          exact maxSufStateInv_step_eq_jump m ms j k p hinv'
      · have hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = false := by
          cases hB : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) <;> simp [hB] at hEq0 ⊢
        rw [maxSufLoopStep_gt_of_not_useLe x m ms j k p steps hStop hab hEq]
        have hjm : j < m := by omega
        exact maxSufStateInv_step_gt m ms j k p hinv' hjm
  | true =>
    by_cases hab : x[Int.toNat (j + k)]! < x[Int.toNat (ms + k)]!
    · rw [maxSufLoopStep_lt_of_useLe x m ms j k p steps hStop hab]
      exact maxSufStateInv_step_lt m ms j k p hinv' hjk
    · by_cases hEq0 : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = true
      · by_cases hkp : k != p
        · rw [maxSufLoopStep_eqExtend_of_useLe x m ms j k p steps hStop hab hEq0 hkp]
          exact maxSufStateInv_step_eq_extend m ms j k p hinv' hkp
        · rw [maxSufLoopStep_eqJump_of_useLe x m ms j k p steps hStop hab hEq0 hkp]
          exact maxSufStateInv_step_eq_jump m ms j k p hinv'
      · have hEq : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) = false := by
          cases hB : (x[Int.toNat (j + k)]! == x[Int.toNat (ms + k)]!) <;> simp [hB] at hEq0 ⊢
        rw [maxSufLoopStep_gt_of_useLe x m ms j k p steps hStop hab hEq]
        have hjm : j < m := by omega
        exact maxSufStateInv_step_gt m ms j k p hinv' hjm

theorem maxSufStateInv_preserved_by_nextState
    (x : ByteArray) (useLe : Bool) (m ms j k p : Int) (steps : Nat)
    (hinv : MaxSufStateInv m ms j k p)
    (hStop : ¬ (steps = 0 || ¬ (j + k < m))) :
    match maxSufNextState (maxSufLoopStep x useLe m ms j k p steps) with
    | none => False
    | some (ms', j', k', p') => MaxSufStateInv m ms' j' k' p' := by
  let step := maxSufLoopStep x useLe m ms j k p steps
  have hstep := maxSufStateInv_preserved_by_step x useLe m ms j k p steps hinv hStop
  cases hs : step <;> simp [step, hs, maxSufNextState] at hstep ⊢
  all_goals exact hstep

@[simp] theorem maximalSuffixLoopCore_stop_of_stop
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat) (ms j k p : Int)
    (hStop : steps = 0 || ¬ (j + k < m)) :
    ViE.PieceTree.maximalSuffixLoopCore x useLe m steps ms j k p = (ms, p) := by
  unfold ViE.PieceTree.maximalSuffixLoopCore
  by_cases hzero : steps = 0
  · simp [hzero]
  · simp [hzero]
    have hjk : ¬ (j + k < m) := by
      have : ¬ (decide (steps = 0) = true) := by simp [hzero]
      simpa [hzero] using hStop
    have hstep : ViE.PieceTree.maximalSuffixStep x useLe m steps ms j k p = .stop := by
      simp [ViE.PieceTree.maximalSuffixStep, hzero, hjk]
    simp [hstep]

theorem maxSufStateInv_pair_bounds
    (m ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p) :
    -1 ≤ ms ∧ 0 < p ∧ p ≤ m ∧ ms < m := by
  rcases hinv with ⟨hmslo, _, _, _, hp, hpm, hmsm⟩
  exact ⟨hmslo, hp, hpm, hmsm⟩

/-- If the maximal-suffix loop stops immediately, the returned split point and
period inherit the basic numeric bounds from the current invariant. -/
theorem maximalSuffixLoopCore_stop_bounds
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat) (ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p)
    (hStop : steps = 0 || ¬ (j + k < m)) :
    let r := ViE.PieceTree.maximalSuffixLoopCore x useLe m steps ms j k p;
    -1 ≤ r.1 ∧ 0 < r.2 ∧ r.2 ≤ m ∧ r.1 < m := by
  rw [maximalSuffixLoopCore_stop_of_stop x useLe m steps ms j k p hStop]
  simpa using maxSufStateInv_pair_bounds m ms j k p hinv

@[simp] theorem maxSufFollow_stop_of_stop
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat) (ms j k p : Int)
    (hStop : steps = 0 || ¬ (j + k < m)) :
    maxSufFollow x useLe m steps ms j k p = (ms, p) := by
  unfold maxSufFollow
  by_cases hzero : steps = 0
  · simp [hzero]
  · simp [hzero, maxSufLoopStep_stop_of_stop x useLe m ms j k p steps hStop, maxSufNextState]

/-- The proof-side mirror of the maximal-suffix loop preserves the basic bounds
on the split point and period for every reachable state. -/
theorem maxSufFollow_result_bounds
    (x : ByteArray) (useLe : Bool) (m : Int) (steps : Nat) (ms j k p : Int)
    (hinv : MaxSufStateInv m ms j k p) :
    let r := maxSufFollow x useLe m steps ms j k p;
    -1 ≤ r.1 ∧ 0 < r.2 ∧ r.2 ≤ m ∧ r.1 < m := by
  induction steps generalizing ms j k p with
  | zero =>
      unfold maxSufFollow
      simp
      exact maxSufStateInv_pair_bounds m ms j k p hinv
  | succ steps ih =>
      unfold maxSufFollow
      simp
      by_cases hStop : Nat.succ steps = 0 || ¬ (j + k < m)
      · simp [maxSufLoopStep_stop_of_stop x useLe m ms j k p (Nat.succ steps) hStop, maxSufNextState]
        exact maxSufStateInv_pair_bounds m ms j k p hinv
      · have hnextInv :=
          maxSufStateInv_preserved_by_nextState x useLe m ms j k p (Nat.succ steps) hinv hStop
        cases hstep : maxSufLoopStep x useLe m ms j k p (Nat.succ steps) with
        | stop =>
            have : False := by simpa [hstep, maxSufNextState] using hnextInv
            exact False.elim this
        | lt ms' j' k' p' =>
            have hnextInv' : MaxSufStateInv m ms' j' k' p' := by
              simpa [hstep, maxSufNextState] using hnextInv
            simpa [hstep, maxSufNextState] using ih ms' j' k' p' hnextInv'
        | eqExtend ms' j' k' p' =>
            have hnextInv' : MaxSufStateInv m ms' j' k' p' := by
              simpa [hstep, maxSufNextState] using hnextInv
            simpa [hstep, maxSufNextState] using ih ms' j' k' p' hnextInv'
        | eqJump ms' j' k' p' =>
            have hnextInv' : MaxSufStateInv m ms' j' k' p' := by
              simpa [hstep, maxSufNextState] using hnextInv
            simpa [hstep, maxSufNextState] using ih ms' j' k' p' hnextInv'
        | gt ms' j' k' p' =>
            have hnextInv' : MaxSufStateInv m ms' j' k' p' := by
              simpa [hstep, maxSufNextState] using hnextInv
            simpa [hstep, maxSufNextState] using ih ms' j' k' p' hnextInv'

/-- Starting the proof-side maximal-suffix mirror from the standard initial
state yields a split point and period inside the valid numeric bounds. -/
theorem maxSufFollow_initial_bounds
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    let m : Int := x.size;
    let steps := ((Int.toNat m) + 1) * ((Int.toNat m) + 1) + 1;
    let r := maxSufFollow x useLe m steps (-1) 0 1 1;
    -1 ≤ r.1 ∧ 0 < r.2 ∧ r.2 ≤ x.size ∧ r.1 < x.size := by
  have hm : 0 < (x.size : Int) := by
    exact Int.natCast_pos.mpr (Nat.pos_of_ne_zero hne)
  simpa using
    (maxSufFollow_result_bounds x useLe x.size
      (((Int.toNat (x.size : Int)) + 1) * ((Int.toNat (x.size : Int)) + 1) + 1)
      (-1) 0 1 1 (maxSufStateInv_init x.size hm))

/-- The proof-side maximal-suffix wrapper returns a split point and period
inside the non-empty needle bounds. -/
theorem maxSufMirror_basic_bounds
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    let r := maxSufMirror x useLe;
    -1 ≤ r.1 ∧ 0 < r.2 ∧ r.2 ≤ x.size ∧ r.1 < x.size := by
  unfold maxSufMirror
  simpa using maxSufFollow_initial_bounds x useLe hne

/-- The implementation-side maximal-suffix wrapper satisfies the same basic
numeric bounds as the proof-side mirror. -/
theorem maximalSuffix_basic_bounds
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    let r := ViE.PieceTree.maximalSuffix x useLe;
    -1 ≤ r.1 ∧ 0 < r.2 ∧ r.2 ≤ x.size ∧ r.1 < x.size := by
  have hEq : ViE.PieceTree.maximalSuffix x useLe = maxSufMirror x useLe := by
    unfold ViE.PieceTree.maximalSuffix ViE.PieceTree.maximalSuffixLoop maxSufMirror
    simp [maximalSuffixLoopCore_eq_maxSufFollow]
  simpa [hEq] using maxSufMirror_basic_bounds x useLe hne

/-- The proof-side maximal-suffix wrapper never returns a split point below
the sentinel value `-1`. -/
theorem maxSufMirror_ms_lower_bound
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    -1 ≤ (maxSufMirror x useLe).1 := by
  have hbounds := maxSufMirror_basic_bounds x useLe hne
  exact hbounds.1

/-- The proof-side maximal-suffix wrapper always returns a strictly positive
period for a non-empty needle. -/
theorem maxSufMirror_period_pos
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    0 < (maxSufMirror x useLe).2 := by
  have hbounds := maxSufMirror_basic_bounds x useLe hne
  exact hbounds.2.1

/-- The proof-side maximal-suffix period never exceeds the needle length. -/
theorem maxSufMirror_period_le_size
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    (maxSufMirror x useLe).2 ≤ x.size := by
  have hbounds := maxSufMirror_basic_bounds x useLe hne
  exact hbounds.2.2.1

/-- The proof-side maximal-suffix split point always lies strictly inside the
needle length. -/
theorem maxSufMirror_ms_lt_size
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    (maxSufMirror x useLe).1 < x.size := by
  have hbounds := maxSufMirror_basic_bounds x useLe hne
  exact hbounds.2.2.2

/-- The implementation-side maximal-suffix split point always lies strictly
inside a non-empty needle. -/
theorem maximalSuffix_ms_lt_size
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    (ViE.PieceTree.maximalSuffix x useLe).1 < x.size := by
  have hbounds := maximalSuffix_basic_bounds x useLe hne
  exact hbounds.2.2.2

/-- The implementation-side maximal-suffix split point, viewed as a natural
number, still lies strictly inside a non-empty needle. -/
theorem maximalSuffix_msNat_lt_size
    (x : ByteArray) (useLe : Bool) (hne : x.size ≠ 0) :
    (ViE.PieceTree.maximalSuffix x useLe).1.toNat < x.size := by
  have hlt := maximalSuffix_ms_lt_size x useLe hne
  by_cases hneg : (ViE.PieceTree.maximalSuffix x useLe).1 < 0
  · have htoNat : (ViE.PieceTree.maximalSuffix x useLe).1.toNat = 0 := by
      exact Int.toNat_of_nonpos (by omega)
    simpa [htoNat] using Nat.pos_of_ne_zero hne
  · have hnonneg : 0 ≤ (ViE.PieceTree.maximalSuffix x useLe).1 := by omega
    have hlt' : (((ViE.PieceTree.maximalSuffix x useLe).1.toNat : Nat) : Int) < x.size := by
      simpa [Int.toNat_of_nonneg hnonneg] using hlt
    exact Int.ofNat_lt.mp hlt'




@[simp] theorem shortMemInv_init
    (haystack needle : ByteArray) (i n pNat : Nat) :
    ShortMemInv haystack needle i n pNat (-1) := by
  exact Or.inl rfl

@[simp] theorem shortMemInv_shift
    (haystack needle : ByteArray) (i n pNat shift : Nat)
    (_hshift : 0 < shift) :
    ShortMemInv haystack needle (i + shift) n pNat (-1) := by
  exact Or.inl rfl

theorem shortMemInv_cases
    (haystack needle : ByteArray) (i n pNat : Nat) (mem : Int)
    (hinv : ShortMemInv haystack needle i n pNat mem) :
    mem = -1 ∨ (mem = Int.ofNat (n - pNat - 1) ∧ matchesRange haystack needle i 0 (n - pNat)) := by
  exact hinv

/- The initial short-period search state starts with no remembered prefix. -/
@[simp] theorem shortLoopInv_init
    (haystack needle : ByteArray) (i n pNat : Nat)
    (hperiod : NeedlePeriodInv needle n pNat) :
    ShortLoopInv haystack needle i n pNat (-1) := by
  exact ⟨hperiod, shortMemInv_init haystack needle i n pNat⟩

/- A plain shift step keeps the period witness and resets the remembered prefix. -/
@[simp] theorem shortLoopInv_shift
    (haystack needle : ByteArray) (i n pNat shift : Nat)
    (hperiod : NeedlePeriodInv needle n pNat)
    (hshift : 0 < shift) :
    ShortLoopInv haystack needle (i + shift) n pNat (-1) := by
  exact ⟨hperiod, shortMemInv_shift haystack needle i n pNat shift hshift⟩

/- Saving the left prefix after a period jump produces the remembered-prefix
state expected by the short-period loop. -/
theorem shortMemInv_period_of_saved_prefix
    (haystack needle : ByteArray)
    (nextI n pNat : Nat)
    (hprefix : matchesRange haystack needle nextI 0 (n - pNat)) :
    ShortMemInv haystack needle nextI n pNat (Int.ofNat (n - pNat - 1)) := by
  exact Or.inr ⟨rfl, hprefix⟩

/- Combining the global period witness with a saved prefix yields the full
short-loop invariant after a period jump. -/
theorem shortLoopInv_period_of_saved_prefix
    (haystack needle : ByteArray)
    (nextI n pNat : Nat)
    (hperiod : NeedlePeriodInv needle n pNat)
    (hprefix : ShortSavedPrefix haystack needle nextI n pNat) :
    ShortLoopInv haystack needle nextI n pNat (Int.ofNat (n - pNat - 1)) := by
  exact ⟨hperiod, shortMemInv_period_of_saved_prefix haystack needle nextI n pNat hprefix⟩

def shortLoopStep
    (haystack needle : ByteArray)
    (_start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int) : ShortStep :=
  if i > maxStart then
    .stop
  else
    let j0 := max (Int.ofNat msNat) mem + 1
    let j := ViE.PieceTree.twoWayForward1 haystack needle i n j0
    if j >= n then
      let j2 := ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat)
      if j2 <= mem then
        .accept i
      else
        let nextI := i + pNat
        if nextI <= i then
          .stop
        else
          let nextMem := Int.ofNat (n - pNat - 1)
          .period nextI nextMem
    else
      let shift := Int.toNat (j - Int.ofNat msNat)
      if shift == 0 then
        .stop
      else
        let nextI := i + shift
        if nextI <= i then
          .stop
        else
          .shift nextI

@[simp] theorem shortLoopStep_stop_of_gt
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int)
    (h : i > maxStart) :
    shortLoopStep haystack needle start maxStart msNat pNat n i mem = .stop := by
  unfold shortLoopStep
  simp [h]

@[simp] theorem shortLoopStep_accept_of_accept_branch
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem) :
    shortLoopStep haystack needle start maxStart msNat pNat n i mem = .accept i := by
  unfold shortLoopStep
  dsimp
  split_ifs <;> grind

@[simp] theorem shortLoopStep_period_of_period_branch
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem)
    (hnext : ¬ i + pNat ≤ i) :
    shortLoopStep haystack needle start maxStart msNat pNat n i mem =
      .period (i + pNat) (Int.ofNat (n - pNat - 1)) := by
  unfold shortLoopStep
  rw [if_neg hgt]
  rw [if_pos hj]
  rw [if_neg hj2]
  rw [if_neg hnext]

@[simp] theorem shortLoopStep_shift_of_shift_branch
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n : Nat) (i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hshift : (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat ≠ 0)
    (hnext : ¬ i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) ≤ i) :
    shortLoopStep haystack needle start maxStart msNat pNat n i mem =
      .shift (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat)) := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward1] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward1Core haystack needle i n
          (Int.toNat (max (Int.ofNat msNat) mem + 1))) msNat)
  unfold shortLoopStep
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      ¬ (((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) == 0) = true := by
    simpa using hshift
  rw [if_neg hshift']
  rw [if_neg hnext]

@[simp] theorem firstMatchFrom_empty (haystack : ByteArray) (start : Nat) :
    firstMatchFrom haystack ByteArray.empty start = some start := by
  simp [firstMatchFrom]

@[simp] theorem twoWaySearch_empty (haystack : ByteArray) (start : Nat) :
    ViE.PieceTree.twoWaySearch haystack ByteArray.empty start = some start := by
  simp [ViE.PieceTree.twoWaySearch]

theorem twoWaySearch_haystack_too_short_none
    (haystack needle : ByteArray) (start : Nat)
    (h : haystack.size < needle.size) :
    ViE.PieceTree.twoWaySearch haystack needle start = none := by
  have hne : needle.size ≠ 0 := by omega
  simp [ViE.PieceTree.twoWaySearch, hne, h]

theorem twoWaySearch_start_out_of_range_none
    (haystack needle : ByteArray) (start : Nat)
    (h0 : needle.size ≠ 0)
    (h : start + needle.size > haystack.size) :
    ViE.PieceTree.twoWaySearch haystack needle start = none := by
  by_cases hshort : haystack.size < needle.size
  · simp [ViE.PieceTree.twoWaySearch, h0, hshort]
  · simp [ViE.PieceTree.twoWaySearch, h0, hshort, h]

theorem twoWaySearch_boundary_eq_spec
    (haystack needle : ByteArray) (start : Nat)
    (h : needle.size = 0 ∨ haystack.size < needle.size ∨ start + needle.size > haystack.size) :
    ViE.PieceTree.twoWaySearch haystack needle start = firstMatchFrom haystack needle start := by
  rcases h with hEmpty | hRest
  · simp [hEmpty, ViE.PieceTree.twoWaySearch, firstMatchFrom]
  · rcases hRest with hShort | hStart
    · have hne : needle.size ≠ 0 := by omega
      simp [ViE.PieceTree.twoWaySearch, firstMatchFrom, hne, hShort]
    · by_cases hzero : needle.size = 0
      · simp [ViE.PieceTree.twoWaySearch, firstMatchFrom, hzero]
      · by_cases hShort : haystack.size < needle.size
        · simp [ViE.PieceTree.twoWaySearch, firstMatchFrom, hzero, hShort]
        · simp [ViE.PieceTree.twoWaySearch, firstMatchFrom, hzero, hShort, hStart]

@[simp] theorem findPatternInBytes_eq_twoWaySearch
    (haystack needle : ByteArray) (start : Nat) :
    ViE.PieceTree.findPatternInBytes haystack needle start =
      ViE.PieceTree.twoWaySearch haystack needle start := by
  rfl

theorem matchesRange_refl_of_eq
    (haystack needle : ByteArray) (pos start stop : Nat)
    (h : ∀ j, start ≤ j → j < stop → haystack[pos + j]! = needle[j]!) :
    matchesRange haystack needle pos start stop := h

theorem matchesRange_mono_right
    (haystack needle : ByteArray) (pos start stop stop' : Nat)
    (hsub : stop' ≤ stop)
    (h : matchesRange haystack needle pos start stop) :
    matchesRange haystack needle pos start stop' := by
  intro j hj1 hj2
  exact h j hj1 (Nat.lt_of_lt_of_le hj2 hsub)

theorem mismatchAt_not_matchesRange
    (haystack needle : ByteArray) (pos start stop j : Nat)
    (hj1 : start ≤ j) (hj2 : j < stop)
    (hm : mismatchAt haystack needle pos j) :
    ¬ matchesRange haystack needle pos start stop := by
  intro hRange
  grind [mismatchAt, matchesRange]

theorem prefixEqual_true_eq_at
    (needle : ByteArray) (n : Nat) (ms : Int) (msNat pNat i : Nat)
    (hms : ¬ ms < 0)
    (hi : i ≤ msNat)
    (hib : i + pNat < n)
    (h : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat i = true) :
    needle[i]! = needle[i + pNat]! := by
  unfold ViE.PieceTree.twoWaySearch.prefixEqual at h
  rw [if_neg hms] at h
  have hnoti : ¬ i > msNat := by omega
  rw [if_neg hnoti] at h
  have hnotb : ¬ i + pNat ≥ n := by omega
  rw [if_neg hnotb] at h
  split_ifs at h with heq
  · simpa using heq

theorem prefixEqual_true_succ
    (needle : ByteArray) (n : Nat) (ms : Int) (msNat pNat i : Nat)
    (hms : ¬ ms < 0)
    (hi : i ≤ msNat)
    (hib : i + pNat < n)
    (h : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat i = true) :
    ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat (i + 1) = true := by
  unfold ViE.PieceTree.twoWaySearch.prefixEqual at h
  rw [if_neg hms] at h
  have hnoti : ¬ i > msNat := by omega
  rw [if_neg hnoti] at h
  have hnotb : ¬ i + pNat ≥ n := by omega
  rw [if_neg hnotb] at h
  split_ifs at h with heq
  · exact h

theorem prefixEqual_true_periodic
    (needle : ByteArray) (n : Nat) (ms : Int) (msNat pNat i : Nat)
    (hms : ¬ ms < 0)
    (hstop : msNat + pNat < n)
    (hi : i ≤ msNat)
    (h : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat i = true) :
    ∀ j, i ≤ j → j ≤ msNat → needle[j]! = needle[j + pNat]! := by
  let C : Nat → Prop :=
    fun curr => curr ≤ msNat →
      ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat curr = true →
      ∀ j, curr ≤ j → j ≤ msNat → needle[j]! = needle[j + pNat]!
  let _ : WellFoundedRelation Nat := measure (fun i => msNat + 1 - i)
  have hfix : ∀ i, C i := by
    refine WellFounded.fix (measure (fun i => msNat + 1 - i)).wf ?_
    intro curr ih hcurr hpeq j hij hjms
    by_cases hijEq : j = curr
    · subst hijEq
      exact prefixEqual_true_eq_at needle n ms msNat pNat j hms hjms (by omega) hpeq
    · have hi_lt_j : curr < j := by omega
      have hsucc : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat (curr + 1) = true := by
        exact prefixEqual_true_succ needle n ms msNat pNat curr hms hcurr (by omega) hpeq
      have hlt : WellFoundedRelation.rel (curr + 1) curr := by
        change msNat + 1 - (curr + 1) < msNat + 1 - curr
        omega
      exact ih (curr + 1) hlt (by omega) hsucc j (by omega) hjms
  exact hfix i hi h

theorem prefixEqual_true_periodic_from_zero
    (needle : ByteArray) (n : Nat) (ms : Int) (msNat pNat : Nat)
    (hms : ¬ ms < 0)
    (hstop : msNat + pNat < n)
    (h : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat 0 = true) :
    ∀ j, j ≤ msNat → needle[j]! = needle[j + pNat]! := by
  intro j hj
  exact prefixEqual_true_periodic needle n ms msNat pNat 0 hms hstop (Nat.zero_le _) h j (Nat.zero_le _) hj

/- If the prefix-equality precheck succeeds from zero, the needle satisfies the
periodicity invariant required by the short-period branch. -/
theorem needlePeriodInv_of_prefixEqual
    (needle : ByteArray) (n : Nat) (ms : Int) (msNat pNat : Nat)
    (hms : ¬ ms < 0)
    (hcover : n - pNat - 1 ≤ msNat)
    (hstop : msNat + pNat < n)
    (h : ViE.PieceTree.twoWaySearch.prefixEqual needle n ms msNat pNat 0 = true) :
    NeedlePeriodInv needle n pNat := by
  intro j hj
  have hj' : j ≤ n - pNat - 1 := by omega
  have hjms : j ≤ msNat := by omega
  exact prefixEqual_true_periodic_from_zero needle n ms msNat pNat hms hstop h j hjms

theorem twoWayForward1Core_unfold_lt
    (haystack needle : ByteArray) (i n j : Nat)
    (h : j < n) :
    ViE.PieceTree.twoWayForward1Core haystack needle i n j =
      if haystack[i + j]! = needle[j]! then
        ViE.PieceTree.twoWayForward1Core haystack needle i n (j + 1)
      else
        j := by
  rw [ViE.PieceTree.twoWayForward1Core]
  simp [Nat.not_le.mpr h]

theorem twoWayForward1Core_unfold_ge
    (haystack needle : ByteArray) (i n j : Nat)
    (h : n ≤ j) :
    ViE.PieceTree.twoWayForward1Core haystack needle i n j = j := by
  rw [ViE.PieceTree.twoWayForward1Core]
  simp [h]

theorem twoWayForward2Core_unfold_lt
    (haystack needle : ByteArray) (i n j : Nat)
    (h : j < n) :
    ViE.PieceTree.twoWayForward2Core haystack needle i n j =
      if haystack[i + j]! = needle[j]! then
        ViE.PieceTree.twoWayForward2Core haystack needle i n (j + 1)
      else
        j := by
  rw [ViE.PieceTree.twoWayForward2Core]
  simp [Nat.not_le.mpr h]

theorem twoWayForward2Core_unfold_ge
    (haystack needle : ByteArray) (i n j : Nat)
    (h : n ≤ j) :
    ViE.PieceTree.twoWayForward2Core haystack needle i n j = j := by
  rw [ViE.PieceTree.twoWayForward2Core]
  simp [h]

theorem twoWayBackward1Core_unfold_zero
    (haystack needle : ByteArray) (i : Nat) (mem : Int) :
    ViE.PieceTree.twoWayBackward1Core haystack needle i mem 0 = mem := by
  rw [ViE.PieceTree.twoWayBackward1Core]
  simp

theorem twoWayBackward2Core_unfold_zero
    (haystack needle : ByteArray) (i : Nat) :
    ViE.PieceTree.twoWayBackward2Core haystack needle i 0 = -1 := by
  rw [ViE.PieceTree.twoWayBackward2Core]
  simp

theorem twoWayShortLoopCore_none_of_gt
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (h : maxStart < i) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = none := by
  rw [ViE.PieceTree.twoWayShortLoopCore]
  simp [h]

theorem twoWayLongLoopCore_none_of_gt
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (h : maxStart < i) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = none := by
  rw [ViE.PieceTree.twoWayLongLoopCore]
  simp [h]

theorem twoWayForward1Core_bounds
    (haystack needle : ByteArray) (i n j : Nat)
    (hjn : j ≤ n) :
    let r := ViE.PieceTree.twoWayForward1Core haystack needle i n j
    j ≤ r ∧ r ≤ n := by
  by_cases hge : j ≥ n
  · have hEq : j = n := by omega
    subst hEq
    rw [ViE.PieceTree.twoWayForward1Core]
    simp
  · have hlt : j < n := by omega
    rw [ViE.PieceTree.twoWayForward1Core]
    simp [Nat.not_le.mpr hlt]
    by_cases hEq : haystack[i + j]! = needle[j]!
    · simp [hEq]
      have hnext : j + 1 ≤ n := by omega
      have hrec := twoWayForward1Core_bounds haystack needle i n (j + 1) hnext
      constructor
      · exact Nat.le_trans (Nat.le_succ j) hrec.1
      · exact hrec.2
    · simp [hEq]
      omega
  termination_by n - j
  decreasing_by
    omega

theorem twoWayForward2Core_bounds
    (haystack needle : ByteArray) (i n j : Nat)
    (hjn : j ≤ n) :
    let r := ViE.PieceTree.twoWayForward2Core haystack needle i n j
    j ≤ r ∧ r ≤ n := by
  by_cases hge : j ≥ n
  · have hEq : j = n := by omega
    subst hEq
    rw [ViE.PieceTree.twoWayForward2Core]
    simp
  · have hlt : j < n := by omega
    rw [ViE.PieceTree.twoWayForward2Core]
    simp [Nat.not_le.mpr hlt]
    by_cases hEq : haystack[i + j]! = needle[j]!
    · simp [hEq]
      have hnext : j + 1 ≤ n := by omega
      have hrec := twoWayForward2Core_bounds haystack needle i n (j + 1) hnext
      constructor
      · exact Nat.le_trans (Nat.le_succ j) hrec.1
      · exact hrec.2
    · simp [hEq]
      omega
  termination_by n - j
  decreasing_by
    omega

theorem twoWayBackward1Core_unfold_succ
    (haystack needle : ByteArray) (i : Nat) (mem : Int) (s : Nat) :
    ViE.PieceTree.twoWayBackward1Core haystack needle i mem (Nat.succ s) =
      let j := mem + Int.ofNat (Nat.succ s)
      if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        ViE.PieceTree.twoWayBackward1Core haystack needle i mem s
      else
        j := by
  rw [ViE.PieceTree.twoWayBackward1Core]
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.succ_sub_one]

theorem twoWayBackward2Core_unfold_succ
    (haystack needle : ByteArray) (i : Nat) (s : Nat) :
    ViE.PieceTree.twoWayBackward2Core haystack needle i (Nat.succ s) =
      let j := Int.ofNat (Nat.succ s) - 1
      if haystack[i + Int.toNat j]! == needle[Int.toNat j]! then
        ViE.PieceTree.twoWayBackward2Core haystack needle i s
      else
        j := by
  rw [ViE.PieceTree.twoWayBackward2Core]
  simp only [Nat.succ_ne_zero, ↓reduceDIte, Nat.succ_sub_one]

theorem twoWayBackward1Core_cases
    (haystack needle : ByteArray) (i : Nat) (mem : Int) (s : Nat) :
    ViE.PieceTree.twoWayBackward1Core haystack needle i mem (Nat.succ s) =
      if haystack[i + Int.toNat (mem + Int.ofNat (Nat.succ s))]! =
          needle[Int.toNat (mem + Int.ofNat (Nat.succ s))]! then
        ViE.PieceTree.twoWayBackward1Core haystack needle i mem s
      else
        mem + Int.ofNat (Nat.succ s) := by
  rw [twoWayBackward1Core_unfold_succ]
  by_cases h :
      haystack[i + Int.toNat (mem + Int.ofNat (Nat.succ s))]! =
        needle[Int.toNat (mem + Int.ofNat (Nat.succ s))]!
  · grind
  · grind

theorem twoWayBackward2Core_cases
    (haystack needle : ByteArray) (i : Nat) (s : Nat) :
    ViE.PieceTree.twoWayBackward2Core haystack needle i (Nat.succ s) =
      if haystack[i + Int.toNat (Int.ofNat (Nat.succ s) - 1)]! =
          needle[Int.toNat (Int.ofNat (Nat.succ s) - 1)]! then
        ViE.PieceTree.twoWayBackward2Core haystack needle i s
      else
        Int.ofNat (Nat.succ s) - 1 := by
  rw [twoWayBackward2Core_unfold_succ]
  by_cases h :
      haystack[i + Int.toNat (Int.ofNat (Nat.succ s) - 1)]! =
        needle[Int.toNat (Int.ofNat (Nat.succ s) - 1)]!
  · grind
  · grind

theorem twoWayBackward1Core_lower_bound
    (haystack needle : ByteArray) (i : Nat) (mem : Int) (steps : Nat) :
    let r := ViE.PieceTree.twoWayBackward1Core haystack needle i mem steps
    mem ≤ r := by
  induction steps with
  | zero =>
      rw [ViE.PieceTree.twoWayBackward1Core]
      simp
  | succ s ih =>
      rw [twoWayBackward1Core_unfold_succ]
      dsimp
      split_ifs with hMatch
      · exact ih
      · omega

theorem twoWayBackward2Core_lower_bound
    (haystack needle : ByteArray) (i : Nat) (steps : Nat) :
    let r := ViE.PieceTree.twoWayBackward2Core haystack needle i steps;
    -1 ≤ r := by
  induction steps with
  | zero =>
      rw [ViE.PieceTree.twoWayBackward2Core]
      simp
  | succ s ih =>
      rw [twoWayBackward2Core_unfold_succ]
      dsimp
      split_ifs with hMatch
      · exact ih
      · omega

theorem twoWayBackward1Core_upper_bound
    (haystack needle : ByteArray) (i : Nat) (mem : Int) (steps : Nat) :
    ViE.PieceTree.twoWayBackward1Core haystack needle i mem steps ≤ mem + Int.ofNat steps := by
  induction steps with
  | zero =>
      rw [ViE.PieceTree.twoWayBackward1Core]
      simp
  | succ s ih =>
      rw [twoWayBackward1Core_cases]
      by_cases h :
          haystack[i + Int.toNat (mem + Int.ofNat (Nat.succ s))]! =
            needle[Int.toNat (mem + Int.ofNat (Nat.succ s))]!
      · rw [if_pos h]
        have hs : ViE.PieceTree.twoWayBackward1Core haystack needle i mem s ≤ mem + Int.ofNat s := ih
        have hsucc : Int.ofNat (s + 1) = Int.ofNat s + 1 := by simp
        rw [hsucc]
        omega
      · rw [if_neg h]
        simp [Nat.succ_eq_add_one]

theorem twoWayBackward2Core_upper_bound
    (haystack needle : ByteArray) (i : Nat) (steps : Nat) :
    ViE.PieceTree.twoWayBackward2Core haystack needle i steps ≤ Int.ofNat steps - 1 := by
  induction steps with
  | zero =>
      rw [ViE.PieceTree.twoWayBackward2Core]
      simp
  | succ s ih =>
      rw [twoWayBackward2Core_cases]
      by_cases h :
          haystack[i + Int.toNat (Int.ofNat (Nat.succ s) - 1)]! =
            needle[Int.toNat (Int.ofNat (Nat.succ s) - 1)]!
      · rw [if_pos h]
        have hs : ViE.PieceTree.twoWayBackward2Core haystack needle i s ≤ Int.ofNat s - 1 := ih
        have hsucc : Int.ofNat (s + 1) - 1 = Int.ofNat s := by simp
        rw [hsucc]
        omega
      · rw [if_neg h]
        simp [Nat.succ_eq_add_one]

theorem twoWayShortLoopCore_accept_eq_some
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = some i := by
  unfold ViE.PieceTree.twoWayShortLoopCore
  dsimp
  split_ifs <;> grind

theorem twoWayShortLoopCore_period_eq
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem)
    (hnext : ¬ i + pNat ≤ i) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem =
      ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n
        (i + pNat) (Int.ofNat (n - pNat - 1)) := by
  rw [ViE.PieceTree.twoWayShortLoopCore]
  rw [if_neg hgt]
  rw [if_pos hj]
  rw [if_neg hj2]
  rw [if_neg hnext]

theorem twoWayShortLoopCore_shift_eq
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hshift : (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat ≠ 0)
    (hnext : ¬ i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) ≤ i) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem =
      ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n
        (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat)) (-1) := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward1] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward1Core haystack needle i n
          (Int.toNat (max (Int.ofNat msNat) mem + 1))) msNat)
  rw [ViE.PieceTree.twoWayShortLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      ¬ (((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) == 0) = true := by
    simpa using hshift
  rw [if_neg hshift']
  rw [if_neg hnext]

theorem twoWayShortLoopCore_none_of_period_nonprogress
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem)
    (hnext : i + pNat ≤ i) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = none := by
  rw [ViE.PieceTree.twoWayShortLoopCore]
  rw [if_neg hgt]
  rw [if_pos hj]
  rw [if_neg hj2]
  rw [if_pos hnext]

theorem twoWayShortLoopCore_none_of_shift_zero
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hshift : (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat = 0) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = none := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward1] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward1Core haystack needle i n
          (Int.toNat (max (Int.ofNat msNat) mem + 1))) msNat)
  rw [ViE.PieceTree.twoWayShortLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      (((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) == 0) = true := by
    simpa [Nat.beq_eq] using hshift
  rw [if_pos hshift']

theorem twoWayShortLoopCore_none_of_shift_nonprogress
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hshift : (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat ≠ 0)
    (hnext : i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) ≤ i) :
    ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = none := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward1] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward1Core haystack needle i n
          (Int.toNat (max (Int.ofNat msNat) mem + 1))) msNat)
  rw [ViE.PieceTree.twoWayShortLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      ¬ (((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) == 0) = true := by
    simpa using hshift
  rw [if_neg hshift']
  rw [if_pos hnext]

theorem twoWayShortLoopCore_accept_in_range
    (haystack needle : ByteArray)
    (_start maxStart msNat _pNat n i : Nat) (_mem : Int)
    (hgt : ¬ i > maxStart)
    (_hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) _mem + 1) >= n)
    (_hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i _mem (Int.ofNat msNat) <= _mem) :
    let r := i
    i ≤ r ∧ r ≤ maxStart := by
  grind

def shortLoopMeasure (maxStart : Nat) : Nat × Int → Nat
  | (i, _) => maxStart + 1 - i

theorem shortLoopMeasure_period_lt
    (maxStart i pNat n : Nat) (mem : Int)
    (hbound : ¬ i > maxStart)
    (hnext : ¬ i + pNat ≤ i) :
    shortLoopMeasure maxStart (i + pNat, Int.ofNat (n - pNat - 1)) <
      shortLoopMeasure maxStart (i, mem) := by
  simp [shortLoopMeasure]
  have hi : i ≤ maxStart := by omega
  have hp : 0 < pNat := by omega
  omega

theorem shortLoopMeasure_shift_lt
    (maxStart i shift : Nat) (mem : Int)
    (hbound : ¬ i > maxStart)
    (hshift : 0 < shift) :
    shortLoopMeasure maxStart (i + shift, mem) <
      shortLoopMeasure maxStart (i, mem) := by
  simp [shortLoopMeasure]
  have hi : i ≤ maxStart := by omega
  omega

theorem twoWayShortLoopCore_some_in_range
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int) (r : Nat)
    (hres : ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = some r) :
    i ≤ r ∧ r ≤ maxStart := by
  let C : Nat × Int → Prop :=
    fun x => ∀ r, ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n x.1 x.2 = some r →
      x.1 ≤ r ∧ r ≤ maxStart
  let _ : WellFoundedRelation (Nat × Int) := measure (shortLoopMeasure maxStart)
  let wf := (measure (shortLoopMeasure maxStart)).wf
  have hfix : ∀ x : Nat × Int, C x := by
    refine WellFounded.fix wf ?_
    intro x ih r hresx
    rcases x with ⟨i, mem⟩
    by_cases hgt : i > maxStart
    · rw [twoWayShortLoopCore_none_of_gt haystack needle start maxStart msNat pNat n i mem hgt] at hresx
      cases hresx
    · by_cases hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n
      · by_cases hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem
        · rw [twoWayShortLoopCore_accept_eq_some haystack needle start maxStart msNat pNat n i mem hgt hj hj2] at hresx
          cases hresx
          exact ⟨le_rfl, by omega⟩
        · by_cases hnext : i + pNat ≤ i
          · rw [twoWayShortLoopCore_none_of_period_nonprogress haystack needle start maxStart msNat pNat n i mem hgt hj hj2 hnext] at hresx
            cases hresx
          · rw [twoWayShortLoopCore_period_eq haystack needle start maxStart msNat pNat n i mem hgt hj hj2 hnext] at hresx
            have hlt : WellFoundedRelation.rel (i + pNat, Int.ofNat (n - pNat - 1)) (i, mem) := by
              change shortLoopMeasure maxStart (i + pNat, Int.ofNat (n - pNat - 1)) <
                shortLoopMeasure maxStart (i, mem)
              exact shortLoopMeasure_period_lt maxStart i pNat n mem hgt hnext
            have hrec := ih (i + pNat, Int.ofNat (n - pNat - 1)) hlt r hresx
            constructor
            · omega
            · exact hrec.2
      · by_cases hshift :
          ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) = 0
        · rw [twoWayShortLoopCore_none_of_shift_zero haystack needle start maxStart msNat pNat n i mem hgt hj hshift] at hresx
          cases hresx
        · by_cases hnext :
            i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) ≤ i
          · rw [twoWayShortLoopCore_none_of_shift_nonprogress haystack needle start maxStart msNat pNat n i mem hgt hj hshift hnext] at hresx
            cases hresx
          · rw [twoWayShortLoopCore_shift_eq haystack needle start maxStart msNat pNat n i mem hgt hj hshift hnext] at hresx
            have hpos :
                0 < (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
              exact Nat.pos_of_ne_zero hshift
            have hlt :
                WellFoundedRelation.rel
                  (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1))
                  (i, mem) := by
              change
                shortLoopMeasure maxStart
                  (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1)) <
                shortLoopMeasure maxStart (i, mem)
              exact shortLoopMeasure_shift_lt maxStart i
                ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat)
                mem hgt hpos
            have hrec := ih
              (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1))
              hlt r hresx
            constructor
            · omega
            · exact hrec.2
  exact hfix (i, mem) r hres

theorem twoWayLongLoopCore_accept_eq_some
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hj2 : ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = some i := by
  unfold ViE.PieceTree.twoWayLongLoopCore
  dsimp
  split_ifs <;> grind

theorem twoWayLongLoopCore_period_eq
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0)
    (hnext : ¬ i + pNat ≤ i) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i =
      ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n (i + pNat) := by
  rw [ViE.PieceTree.twoWayLongLoopCore]
  rw [if_neg hgt]
  rw [if_pos hj]
  rw [if_neg hj2]
  rw [if_neg hnext]

theorem twoWayLongLoopCore_shift_eq
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hshift : (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat ≠ 0)
    (hnext : ¬ i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) ≤ i) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i =
      ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n
        (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat)) := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward2] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward2Core haystack needle i n
          (Int.toNat (Int.ofNat (msNat + 1)))) msNat)
  rw [ViE.PieceTree.twoWayLongLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      ¬ (((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) == 0) = true := by
    simpa using hshift
  rw [if_neg hshift']
  rw [if_neg hnext]

theorem twoWayLongLoopCore_none_of_period_nonprogress
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0)
    (hnext : i + pNat ≤ i) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = none := by
  rw [ViE.PieceTree.twoWayLongLoopCore]
  rw [if_neg hgt]
  rw [if_pos hj]
  rw [if_neg hj2]
  rw [if_pos hnext]

theorem twoWayLongLoopCore_none_of_shift_zero
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hshift : (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat = 0) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = none := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward2] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward2Core haystack needle i n
          (Int.toNat (Int.ofNat (msNat + 1)))) msNat)
  rw [ViE.PieceTree.twoWayLongLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      (((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) == 0) = true := by
    simpa [Nat.beq_eq] using hshift
  rw [if_pos hshift']

theorem twoWayLongLoopCore_none_of_shift_nonprogress
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat)
    (hgt : ¬ i > maxStart)
    (hj : ¬ ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hshift : (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat ≠ 0)
    (hnext : i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) ≤ i) :
    ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = none := by
  have hshiftEq :
      (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) - Int.ofNat msNat).toNat =
        (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat := by
    simpa [ViE.PieceTree.twoWayForward2] using
      (Int.toNat_sub
        (ViE.PieceTree.twoWayForward2Core haystack needle i n
          (Int.toNat (Int.ofNat (msNat + 1)))) msNat)
  rw [ViE.PieceTree.twoWayLongLoopCore]
  rw [if_neg hgt]
  rw [if_neg hj]
  rw [hshiftEq]
  have hshift' :
      ¬ (((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) == 0) = true := by
    simpa using hshift
  rw [if_neg hshift']
  rw [if_pos hnext]

theorem twoWayLongLoopCore_some_in_range
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (r : Nat)
    (hres : ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = some r) :
    i ≤ r ∧ r ≤ maxStart := by
  let C : Nat → Prop :=
    fun i => ∀ r, ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = some r →
      i ≤ r ∧ r ≤ maxStart
  let _ : WellFoundedRelation Nat := measure (fun i => maxStart + 1 - i)
  have hfix : ∀ i, C i := by
    refine WellFounded.fix (measure (fun i => maxStart + 1 - i)).wf ?_
    intro i ih r hresx
    by_cases hgt : i > maxStart
    · rw [twoWayLongLoopCore_none_of_gt haystack needle start maxStart msNat pNat n i hgt] at hresx
      cases hresx
    · by_cases hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n
      · by_cases hj2 : ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0
        · rw [twoWayLongLoopCore_accept_eq_some haystack needle start maxStart msNat pNat n i hgt hj hj2] at hresx
          cases hresx
          exact ⟨le_rfl, by omega⟩
        · by_cases hnext : i + pNat ≤ i
          · rw [twoWayLongLoopCore_none_of_period_nonprogress haystack needle start maxStart msNat pNat n i hgt hj hj2 hnext] at hresx
            cases hresx
          · rw [twoWayLongLoopCore_period_eq haystack needle start maxStart msNat pNat n i hgt hj hj2 hnext] at hresx
            have hlt : WellFoundedRelation.rel (i + pNat) i := by
              change maxStart + 1 - (i + pNat) < maxStart + 1 - i
              have hp : 0 < pNat := by omega
              have hi : i ≤ maxStart := by omega
              omega
            have hrec := ih (i + pNat) hlt r hresx
            constructor
            · omega
            · exact hrec.2
      · by_cases hshift :
          ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) = 0
        · rw [twoWayLongLoopCore_none_of_shift_zero haystack needle start maxStart msNat pNat n i hgt hj hshift] at hresx
          cases hresx
        · by_cases hnext :
            i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) ≤ i
          · rw [twoWayLongLoopCore_none_of_shift_nonprogress haystack needle start maxStart msNat pNat n i hgt hj hshift hnext] at hresx
            cases hresx
          · rw [twoWayLongLoopCore_shift_eq haystack needle start maxStart msNat pNat n i hgt hj hshift hnext] at hresx
            have hpos :
                0 < (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat := by
              exact Nat.pos_of_ne_zero hshift
            have hlt : WellFoundedRelation.rel
                (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat)) i := by
              change
                maxStart + 1 - (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat))
                  < maxStart + 1 - i
              have hi : i ≤ maxStart := by omega
              omega
            have hrec := ih
              (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat))
              hlt r hresx
            constructor
            · omega
            · exact hrec.2
  exact hfix i r hres

theorem twoWaySearch_some_in_range
    (haystack needle : ByteArray) (start r : Nat)
    (hne : needle.size ≠ 0)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r) :
    start ≤ r ∧ r ≤ haystack.size - needle.size := by
  unfold ViE.PieceTree.twoWaySearch at hres
  have hempty : needle ≠ ByteArray.empty := by
    intro h
    simpa [h] using hne
  by_cases hbad : haystack.size < needle.size || start + needle.size > haystack.size
  · simp [hempty, hbad] at hres
  · by_cases hms :
      (ViE.PieceTree.maximalSuffix needle false).fst < (ViE.PieceTree.maximalSuffix needle true).fst
    · by_cases hshort :
        ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
          (ViE.PieceTree.maximalSuffix needle true).fst
          (ViE.PieceTree.maximalSuffix needle true).fst.toNat
          (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 = true
      · simp [hempty, hbad, hms, hshort] at hres
        simpa [ViE.PieceTree.twoWayShortLoop] using
          (twoWayShortLoopCore_some_in_range haystack needle start (haystack.size - needle.size)
            (ViE.PieceTree.maximalSuffix needle true).fst.toNat
            (ViE.PieceTree.maximalSuffix needle true).snd.toNat
            needle.size start (-1) r hres)
      · simp [hempty, hbad, hms, hshort] at hres
        simpa [ViE.PieceTree.twoWayLongLoop] using
          (twoWayLongLoopCore_some_in_range haystack needle start (haystack.size - needle.size)
            (ViE.PieceTree.maximalSuffix needle true).fst.toNat
            (ViE.PieceTree.maximalSuffix needle true).snd.toNat
            needle.size start r hres)
    · by_cases hshort :
        ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
          (ViE.PieceTree.maximalSuffix needle false).fst
          (ViE.PieceTree.maximalSuffix needle false).fst.toNat
          (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 = true
      · simp [hempty, hbad, hms, hshort] at hres
        simpa [ViE.PieceTree.twoWayShortLoop] using
          (twoWayShortLoopCore_some_in_range haystack needle start (haystack.size - needle.size)
            (ViE.PieceTree.maximalSuffix needle false).fst.toNat
            (ViE.PieceTree.maximalSuffix needle false).snd.toNat
            needle.size start (-1) r hres)
      · simp [hempty, hbad, hms, hshort] at hres
        simpa [ViE.PieceTree.twoWayLongLoop] using
          (twoWayLongLoopCore_some_in_range haystack needle start (haystack.size - needle.size)
            (ViE.PieceTree.maximalSuffix needle false).fst.toNat
            (ViE.PieceTree.maximalSuffix needle false).snd.toNat
            needle.size start r hres)

@[simp] theorem twoWayForward1_eq_core
    (haystack needle : ByteArray) (i n : Nat) (j : Int) :
    ViE.PieceTree.twoWayForward1 haystack needle i n j =
      Int.ofNat (ViE.PieceTree.twoWayForward1Core haystack needle i n (Int.toNat j)) := by
  rfl

@[simp] theorem twoWayForward2_eq_core
    (haystack needle : ByteArray) (i n : Nat) (j : Int) :
    ViE.PieceTree.twoWayForward2 haystack needle i n j =
      Int.ofNat (ViE.PieceTree.twoWayForward2Core haystack needle i n (Int.toNat j)) := by
  rfl

theorem twoWayForward1_bounds
    (haystack needle : ByteArray) (i n : Nat) (j : Int)
    (hj0 : 0 ≤ j)
    (hjn : Int.toNat j ≤ n) :
    let r := ViE.PieceTree.twoWayForward1 haystack needle i n j
    j ≤ r ∧ r ≤ Int.ofNat n := by
  have hcore := twoWayForward1Core_bounds haystack needle i n (Int.toNat j) hjn
  constructor
  · have hleNat : Int.toNat j ≤ ViE.PieceTree.twoWayForward1Core haystack needle i n (Int.toNat j) := hcore.1
    have hle' : Int.ofNat (Int.toNat j) ≤ Int.ofNat (ViE.PieceTree.twoWayForward1Core haystack needle i n (Int.toNat j)) := by
      exact Int.ofNat_le.mpr hleNat
    have hle : Int.ofNat (Int.toNat j) ≤ ViE.PieceTree.twoWayForward1 haystack needle i n j := by
      simpa [ViE.PieceTree.twoWayForward1] using hle'
    have hcast : Int.ofNat (Int.toNat j) = j := by
      simpa using (Int.toNat_of_nonneg hj0)
    rw [hcast] at hle
    exact hle
  · simpa [ViE.PieceTree.twoWayForward1] using hcore.2

theorem twoWayForward2_bounds
    (haystack needle : ByteArray) (i n : Nat) (j : Int)
    (hj0 : 0 ≤ j)
    (hjn : Int.toNat j ≤ n) :
    let r := ViE.PieceTree.twoWayForward2 haystack needle i n j
    j ≤ r ∧ r ≤ Int.ofNat n := by
  have hcore := twoWayForward2Core_bounds haystack needle i n (Int.toNat j) hjn
  constructor
  · have hleNat : Int.toNat j ≤ ViE.PieceTree.twoWayForward2Core haystack needle i n (Int.toNat j) := hcore.1
    have hle' : Int.ofNat (Int.toNat j) ≤ Int.ofNat (ViE.PieceTree.twoWayForward2Core haystack needle i n (Int.toNat j)) := by
      exact Int.ofNat_le.mpr hleNat
    have hle : Int.ofNat (Int.toNat j) ≤ ViE.PieceTree.twoWayForward2 haystack needle i n j := by
      simpa [ViE.PieceTree.twoWayForward2] using hle'
    have hcast : Int.ofNat (Int.toNat j) = j := by
      simpa using (Int.toNat_of_nonneg hj0)
    rw [hcast] at hle
    exact hle
  · simpa [ViE.PieceTree.twoWayForward2] using hcore.2

theorem twoWayBackward1_of_le_mem
    (haystack needle : ByteArray) (i : Nat) (mem j : Int)
    (h : j ≤ mem) :
    ViE.PieceTree.twoWayBackward1 haystack needle i mem j = j := by
  rw [ViE.PieceTree.twoWayBackward1]
  simp [h]

theorem twoWayBackward1_of_gt_mem
    (haystack needle : ByteArray) (i : Nat) (mem j : Int)
    (h : mem < j) :
    ViE.PieceTree.twoWayBackward1 haystack needle i mem j =
      ViE.PieceTree.twoWayBackward1Core haystack needle i mem (Int.toNat (j - mem)) := by
  rw [ViE.PieceTree.twoWayBackward1]
  simp [show ¬ j ≤ mem by omega]

theorem twoWayBackward2_of_neg
    (haystack needle : ByteArray) (i : Nat) (j : Int)
    (h : j < 0) :
    ViE.PieceTree.twoWayBackward2 haystack needle i j = j := by
  rw [ViE.PieceTree.twoWayBackward2]
  simp [h]

theorem twoWayBackward2_of_nonneg
    (haystack needle : ByteArray) (i : Nat) (j : Int)
    (h : 0 ≤ j) :
    ViE.PieceTree.twoWayBackward2 haystack needle i j =
      ViE.PieceTree.twoWayBackward2Core haystack needle i (Int.toNat (j + 1)) := by
  rw [ViE.PieceTree.twoWayBackward2]
  simp [show ¬ j < 0 by omega]

theorem twoWayForward2Core_eq_n_matchesRange
    (haystack needle : ByteArray) (i n j : Nat)
    (hjn : j ≤ n)
    (h : ViE.PieceTree.twoWayForward2Core haystack needle i n j = n) :
    matchesRange haystack needle i j n := by
  intro k hk1 hk2
  by_cases hlt : j < n
  · rw [twoWayForward2Core_unfold_lt haystack needle i n j hlt] at h
    by_cases heq : haystack[i + j]! = needle[j]!
    · rw [if_pos heq] at h
      by_cases hkj : k = j
      · subst hkj
        exact heq
      · have hkj' : j + 1 ≤ k := by omega
        exact twoWayForward2Core_eq_n_matchesRange haystack needle i n (j + 1) (by omega) h k hkj' hk2
    · rw [if_neg heq] at h
      omega
  · have hge : n ≤ j := by omega
    rw [twoWayForward2Core_unfold_ge haystack needle i n j hge] at h
    omega

theorem twoWayBackward2Core_lt_zero_matchesRange
    (haystack needle : ByteArray) (i steps : Nat)
    (h : ViE.PieceTree.twoWayBackward2Core haystack needle i steps < 0) :
    matchesRange haystack needle i 0 steps := by
  intro j hj1 hj2
  clear hj1
  induction steps with
  | zero =>
      omega
  | succ s ih =>
      rw [twoWayBackward2Core_cases] at h
      by_cases heq :
          haystack[i + Int.toNat (Int.ofNat (Nat.succ s) - 1)]! =
            needle[Int.toNat (Int.ofNat (Nat.succ s) - 1)]!
      · rw [if_pos heq] at h
        by_cases hlast : j = s
        · subst hlast
          simpa using heq
        · have hjlt : j < s := by omega
          exact ih h hjlt
      · rw [if_neg heq] at h
        have : ¬ Int.ofNat (Nat.succ s) - 1 < 0 := by
          simp
        omega

theorem matchesAt_true_of_range
    (haystack needle : ByteArray) (pos : Nat)
    (hbound : pos + needle.size ≤ haystack.size)
    (hrange : matchesRange haystack needle pos 0 needle.size) :
    matchesAt haystack needle pos = true := by
  simp [matchesAt, hbound, hrange]

theorem twoWayForward1Core_eq_n_matchesRange
    (haystack needle : ByteArray) (i n j : Nat)
    (hjn : j ≤ n)
    (h : ViE.PieceTree.twoWayForward1Core haystack needle i n j = n) :
    matchesRange haystack needle i j n := by
  intro k hk1 hk2
  by_cases hlt : j < n
  · rw [twoWayForward1Core_unfold_lt haystack needle i n j hlt] at h
    by_cases heq : haystack[i + j]! = needle[j]!
    · rw [if_pos heq] at h
      by_cases hkj : k = j
      · subst hkj
        exact heq
      · have hkj' : j + 1 ≤ k := by omega
        exact twoWayForward1Core_eq_n_matchesRange haystack needle i n (j + 1) (by omega) h k hkj' hk2
    · rw [if_neg heq] at h
      omega
  · have hge : n ≤ j := by omega
    rw [twoWayForward1Core_unfold_ge haystack needle i n j hge] at h
    omega

theorem twoWayBackward1Core_negOne_eq_backward2Core
    (haystack needle : ByteArray) (i steps : Nat) :
    ViE.PieceTree.twoWayBackward1Core haystack needle i (-1) steps =
      ViE.PieceTree.twoWayBackward2Core haystack needle i steps := by
  induction steps with
  | zero =>
      rw [twoWayBackward1Core_unfold_zero, twoWayBackward2Core_unfold_zero]
  | succ s ih =>
      rw [twoWayBackward1Core_cases, twoWayBackward2Core_cases, ih]
      congr

theorem twoWayBackward1_negOne_le_matchesRange
    (haystack needle : ByteArray) (i msNat : Nat)
    (h : ViE.PieceTree.twoWayBackward1 haystack needle i (-1) (Int.ofNat msNat) <= (-1 : Int)) :
    matchesRange haystack needle i 0 (msNat + 1) := by
  have hcore :
      ViE.PieceTree.twoWayBackward1Core haystack needle i (-1) (msNat + 1) <= (-1 : Int) := by
    have hwrap :
        ViE.PieceTree.twoWayBackward1 haystack needle i (-1) (Int.ofNat msNat) =
          ViE.PieceTree.twoWayBackward1Core haystack needle i (-1) (msNat + 1) := by
      have hgt : (-1 : Int) < Int.ofNat msNat := by
        have hnonneg : (0 : Int) ≤ Int.ofNat msNat := by simp
        omega
      simpa using twoWayBackward1_of_gt_mem haystack needle i (-1) (Int.ofNat msNat) hgt
    rw [hwrap] at h
    exact h
  have hcore' :
      ViE.PieceTree.twoWayBackward2Core haystack needle i (msNat + 1) < 0 := by
    rw [← twoWayBackward1Core_negOne_eq_backward2Core haystack needle i (msNat + 1)]
    omega
  exact twoWayBackward2Core_lt_zero_matchesRange haystack needle i (msNat + 1) hcore'

theorem short_accept_backward_range_of_negOne
    (haystack needle : ByteArray) (i msNat : Nat)
    (hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i (-1) (Int.ofNat msNat) <= (-1 : Int)) :
    matchesRange haystack needle i 0 (msNat + 1) := by
  exact twoWayBackward1_negOne_le_matchesRange haystack needle i msNat hj2

theorem short_period_branch_mem_is_negOne
    (haystack needle : ByteArray)
    (i msNat pNat n : Nat) (mem : Int)
    (hgap : msNat < n - pNat)
    (hinv : ShortMemInv haystack needle i n pNat mem)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem) :
    mem = -1 := by
  rcases hinv with hneg | ⟨hmem, _⟩
  · exact hneg
  · exfalso
    have hms_le : Int.ofNat msNat ≤ mem := by
      rw [hmem]
      exact Int.ofNat_le.mpr (by omega)
    have hback :
        ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) = Int.ofNat msNat := by
      exact twoWayBackward1_of_le_mem haystack needle i mem (Int.ofNat msNat) hms_le
    have hle : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem := by
      rw [hback]
      exact hms_le
    exact hj2 hle

theorem short_period_preserves_inv_of_saved_prefix
    (haystack needle : ByteArray)
    (i nextI _msNat pNat n : Nat) (mem : Int)
    (hinv : ShortLoopInv haystack needle i n pNat mem)
    (hmem : mem = -1)
    (hnext : nextI = i + pNat)
    (hsaved : ShortSavedPrefix haystack needle nextI n pNat) :
    ShortLoopInv haystack needle nextI n pNat (Int.ofNat (n - pNat - 1)) := by
  rcases hinv with ⟨hperiod, _⟩
  subst hmem
  subst hnext
  exact shortLoopInv_period_of_saved_prefix haystack needle (i + pNat) n pNat hperiod hsaved

theorem twoWayShortLoopCore_accept_matchesAt_of_saved_prefix
    (haystack needle : ByteArray)
    (_start maxStart msNat pNat n i : Nat)
    (_hgap : msNat < n - pNat)
    (hbound : i + needle.size ≤ haystack.size)
    (hn : n = needle.size)
    (hprefix : matchesRange haystack needle i 0 (n - pNat))
    (_hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (n - pNat)) >= n) :
    matchesAt haystack needle i = true := by
  have hfw_eq :
      ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (n - pNat)) = Int.ofNat n := by
    have hstart0 : 0 ≤ Int.ofNat (n - pNat) := Int.natCast_nonneg _
    have hstartLe : Int.toNat (Int.ofNat (n - pNat)) ≤ n := by
      simp
    have hbounds := twoWayForward1_bounds haystack needle i n (Int.ofNat (n - pNat)) hstart0 hstartLe
    apply Int.le_antisymm hbounds.2
    exact hj
  have hfw_range : matchesRange haystack needle i (n - pNat) n := by
    have hcore :
        ViE.PieceTree.twoWayForward1Core haystack needle i n (n - pNat) = n := by
      exact Int.ofNat.inj (by simpa [twoWayForward1_eq_core] using hfw_eq)
    exact twoWayForward1Core_eq_n_matchesRange haystack needle i n (n - pNat) (by omega) hcore
  have hall : matchesRange haystack needle i 0 n := by
    intro j hj1 hj2
    by_cases hsplit : j < n - pNat
    · exact hprefix j hj1 hsplit
    · exact hfw_range j (by omega) hj2
  have hbound' : i + n ≤ haystack.size := by simpa [hn] using hbound
  have hall' : matchesRange haystack needle i 0 needle.size := by simpa [hn] using hall
  exact matchesAt_true_of_range haystack needle i (by simpa [hn] using hbound') hall'

theorem twoWayShortLoopCore_accept_matchesAt
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int)
    (hinv : ShortLoopInv haystack needle i n pNat mem)
    (hgap : msNat < n - pNat)
    (hcover : msNat + 1 ≤ pNat)
    (hbound : i + needle.size ≤ haystack.size)
    (hn : n = needle.size)
    (hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem) :
    matchesAt haystack needle i = true := by
  rcases hinv with ⟨hperiod, hmeminv⟩
  rcases hmeminv with hneg | ⟨hmem, hprefix⟩
  · subst hneg
    have hstart :
        max (Int.ofNat msNat) (-1) + 1 = Int.ofNat (msNat + 1) := by
      cases msNat with
      | zero =>
          simp [Int.max_def]
      | succ k =>
          have hnot : ¬ Int.ofNat (Nat.succ k) ≤ (-1 : Int) := by
            have hlt : (-1 : Int) < Int.ofNat (Nat.succ k) := by
              calc
                (-1 : Int) < 0 := by simpa using Int.negSucc_lt_zero 0
                _ < Int.ofNat (Nat.succ k) := by simp
            exact Int.not_le.mpr hlt
          rw [Int.max_def, if_neg hnot]
          simp
    have hj' : ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (msNat + 1)) >= n := by
      rwa [hstart] at hj
    have hfw_eq :
        ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (msNat + 1)) = Int.ofNat n := by
      have hstart0 : 0 ≤ Int.ofNat (msNat + 1) := Int.natCast_nonneg _
      have hstartLe : Int.toNat (Int.ofNat (msNat + 1)) ≤ n := by
        simp
        exact le_trans (Nat.succ_le_of_lt hgap) (Nat.sub_le _ _)
      have hbounds := twoWayForward1_bounds haystack needle i n (Int.ofNat (msNat + 1)) hstart0 hstartLe
      apply Int.le_antisymm hbounds.2
      exact hj'
    have hfw_range : matchesRange haystack needle i (msNat + 1) n := by
      have hcore :
          ViE.PieceTree.twoWayForward1Core haystack needle i n (msNat + 1) = n := by
        exact Int.ofNat.inj (by simpa [twoWayForward1_eq_core] using hfw_eq)
      exact twoWayForward1Core_eq_n_matchesRange haystack needle i n (msNat + 1) (by omega) hcore
    have hbw_range : matchesRange haystack needle i 0 (msNat + 1) :=
      short_accept_backward_range_of_negOne haystack needle i msNat (by simpa using hj2)
    have hall : matchesRange haystack needle i 0 n := by
      intro j hj1 hj2
      by_cases hsplit : j < msNat + 1
      · exact hbw_range j hj1 hsplit
      · exact hfw_range j (by omega) hj2
    have hbound' : i + n ≤ haystack.size := by simpa [hn] using hbound
    have hall' : matchesRange haystack needle i 0 needle.size := by simpa [hn] using hall
    exact matchesAt_true_of_range haystack needle i (by simpa [hn] using hbound') hall'
  · have hmem_ge_ms : Int.ofNat msNat ≤ mem := by
      rw [hmem]
      exact Int.ofNat_le.mpr (by omega)
    have hstart :
        max (Int.ofNat msNat) mem + 1 = Int.ofNat (n - pNat) := by
      have hmax : max (Int.ofNat msNat) mem = mem := by
        by_cases hcmp : Int.ofNat msNat ≤ mem
        · rw [Int.max_def, if_pos hcmp]
        · exfalso
          omega
      rw [hmax, hmem]
      have hnat : n - pNat - 1 + 1 = n - pNat := by omega
      have hcast : Int.ofNat (n - pNat - 1) + 1 = Int.ofNat (n - pNat - 1 + 1) := by simp
      simpa [hnat] using hcast
    have hj' : ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (n - pNat)) >= n := by
      rwa [hstart] at hj
    exact twoWayShortLoopCore_accept_matchesAt_of_saved_prefix haystack needle start maxStart msNat pNat n i
      hgap hbound hn hprefix hgt hj'

theorem short_savedPrefix_of_periodic_suffix
    (haystack needle : ByteArray)
    (i n pNat : Nat)
    (hperiod : NeedlePeriodInv needle n pNat)
    (hsuffix : matchesRange haystack needle i pNat n)
    (j : Nat)
    (hj : j < n - pNat) :
    haystack[i + (j + pNat)]! = needle[j]!
    := by
  have hsuf : haystack[i + (j + pNat)]! = needle[j + pNat]! := by
    have hj1 : pNat ≤ j + pNat := by omega
    have hj2 : j + pNat < n := by omega
    simpa [Nat.add_assoc] using hsuffix (j + pNat) hj1 hj2
  have hper : needle[j]! = needle[j + pNat]! := hperiod j hj
  rw [hsuf]
  exact hper.symm

theorem short_savedPrefix_matchesRange_of_periodic_suffix
    (haystack needle : ByteArray)
    (i n pNat : Nat)
    (hperiod : NeedlePeriodInv needle n pNat)
    (hsuffix : matchesRange haystack needle i pNat n) :
    ShortSavedPrefix haystack needle (i + pNat) n pNat := by
  intro j hj1 hj2
  have hEq := short_savedPrefix_of_periodic_suffix haystack needle i n pNat hperiod hsuffix j hj2
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq

/- When the period branch is taken, the successful forward scan implies that the
entire suffix `[pNat, n)` already matches at the current haystack position. -/
theorem short_period_branch_suffix_matchesRange
    (haystack needle : ByteArray)
    (i msNat pNat n : Nat)
    (hgap : msNat < n - pNat)
    (hcover : msNat + 1 ≤ pNat)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (msNat + 1)) >= n) :
    matchesRange haystack needle i pNat n := by
  have hfw_eq :
      ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (msNat + 1)) = Int.ofNat n := by
    have hstart0 : 0 ≤ Int.ofNat (msNat + 1) := Int.natCast_nonneg _
    have hstartLe : Int.toNat (Int.ofNat (msNat + 1)) ≤ n := by
      simp
      have hsub : 0 < n - pNat := by omega
      have hnp : pNat < n := by omega
      exact le_trans hcover (Nat.le_of_lt hnp)
    have hbounds := twoWayForward1_bounds haystack needle i n (Int.ofNat (msNat + 1)) hstart0 hstartLe
    apply Int.le_antisymm hbounds.2
    exact hj
  have hfw_range : matchesRange haystack needle i (msNat + 1) n := by
    have hcore :
        ViE.PieceTree.twoWayForward1Core haystack needle i n (msNat + 1) = n := by
      exact Int.ofNat.inj (by simpa [twoWayForward1_eq_core] using hfw_eq)
    have hmsn : msNat + 1 ≤ n := by
      have hsub : 0 < n - pNat := by omega
      have hnp : pNat < n := by omega
      exact le_trans hcover (Nat.le_of_lt hnp)
    exact twoWayForward1Core_eq_n_matchesRange haystack needle i n (msNat + 1) hmsn hcore
  intro j hj1 hj2
  exact hfw_range j (le_trans hcover hj1) hj2

/-- The period branch of the short-period loop preserves the short-loop
invariant. -/
theorem shortLoopInv_period
    (haystack needle : ByteArray)
    (i msNat pNat n : Nat) (mem : Int)
    (hinv : ShortLoopInv haystack needle i n pNat mem)
    (hgap : msNat < n - pNat)
    (hcover : msNat + 1 ≤ pNat)
    (hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n)
    (hj2 : ¬ ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem) :
    ShortLoopInv haystack needle (i + pNat) n pNat (Int.ofNat (n - pNat - 1)) := by
  rcases hinv with ⟨hperiod, hmeminv⟩
  have hmem : mem = -1 := short_period_branch_mem_is_negOne haystack needle i msNat pNat n mem hgap hmeminv hj2
  have hstart :
      max (Int.ofNat msNat) mem + 1 = Int.ofNat (msNat + 1) := by
    rw [hmem]
    cases msNat with
    | zero =>
        simp [Int.max_def]
    | succ k =>
        have hnot : ¬ Int.ofNat (Nat.succ k) ≤ (-1 : Int) := by
          have hlt : (-1 : Int) < Int.ofNat (Nat.succ k) := by
            calc
              (-1 : Int) < 0 := by simpa using Int.negSucc_lt_zero 0
              _ < Int.ofNat (Nat.succ k) := by simp
          exact Int.not_le.mpr hlt
        rw [Int.max_def, if_neg hnot]
        simp
  have hj' : ViE.PieceTree.twoWayForward1 haystack needle i n (Int.ofNat (msNat + 1)) >= n := by
    rwa [hstart] at hj
  have hsuffix : matchesRange haystack needle i pNat n :=
    short_period_branch_suffix_matchesRange haystack needle i msNat pNat n hgap hcover hj'
  have hsaved : ShortSavedPrefix haystack needle (i + pNat) n pNat :=
    short_savedPrefix_matchesRange_of_periodic_suffix haystack needle i n pNat hperiod hsuffix
  have hinv' : ShortLoopInv haystack needle i n pNat mem := ⟨hperiod, hmeminv⟩
  exact short_period_preserves_inv_of_saved_prefix haystack needle i (i + pNat) msNat pNat n mem
    hinv' hmem rfl hsaved

/-- Soundness of the short-period recursive loop: every reported position is a
real match. -/
theorem twoWayShortLoopCore_sound
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i : Nat) (mem : Int) (r : Nat)
    (hinv : ShortLoopInv haystack needle i n pNat mem)
    (hgap : msNat < n - pNat)
    (hcover : msNat + 1 ≤ pNat)
    (hsize : needle.size ≤ haystack.size)
    (hmax : maxStart = haystack.size - needle.size)
    (hn : n = needle.size)
    (hres : ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n i mem = some r) :
    matchesAt haystack needle r = true := by
  let C : Nat × Int → Prop :=
    fun x => ∀ r,
      ShortLoopInv haystack needle x.1 n pNat x.2 →
      ViE.PieceTree.twoWayShortLoopCore haystack needle start maxStart msNat pNat n x.1 x.2 = some r →
      matchesAt haystack needle r = true
  let _ : WellFoundedRelation (Nat × Int) := measure (shortLoopMeasure maxStart)
  have hfix : ∀ x, C x := by
    refine WellFounded.fix (measure (shortLoopMeasure maxStart)).wf ?_
    intro x ih
    rcases x with ⟨i, mem⟩
    intro res hinvx hresx
    by_cases hgt : i > maxStart
    · rw [twoWayShortLoopCore_none_of_gt haystack needle start maxStart msNat pNat n i mem hgt] at hresx
      cases hresx
    · by_cases hj : ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1) >= n
      · by_cases hj2 : ViE.PieceTree.twoWayBackward1 haystack needle i mem (Int.ofNat msNat) <= mem
        · rw [twoWayShortLoopCore_accept_eq_some haystack needle start maxStart msNat pNat n i mem hgt hj hj2] at hresx
          cases hresx
          have hbound : i + needle.size ≤ haystack.size := by
            have hi : i ≤ maxStart := by omega
            calc
              i + needle.size ≤ maxStart + needle.size := Nat.add_le_add_right hi _
              _ = haystack.size := by rw [hmax, Nat.sub_add_cancel hsize]
          exact twoWayShortLoopCore_accept_matchesAt haystack needle start maxStart msNat pNat n i mem
            hinvx hgap hcover hbound hn hgt hj hj2
        · by_cases hnext : i + pNat ≤ i
          · rw [twoWayShortLoopCore_none_of_period_nonprogress haystack needle start maxStart msNat pNat n i mem hgt hj hj2 hnext] at hresx
            cases hresx
          · rw [twoWayShortLoopCore_period_eq haystack needle start maxStart msNat pNat n i mem hgt hj hj2 hnext] at hresx
            have hinv' : ShortLoopInv haystack needle (i + pNat) n pNat (Int.ofNat (n - pNat - 1)) := by
              exact shortLoopInv_period haystack needle i msNat pNat n mem hinvx hgap hcover hj hj2
            have hlt : WellFoundedRelation.rel (i + pNat, Int.ofNat (n - pNat - 1)) (i, mem) := by
              change shortLoopMeasure maxStart (i + pNat, Int.ofNat (n - pNat - 1)) < shortLoopMeasure maxStart (i, mem)
              exact shortLoopMeasure_period_lt maxStart i pNat n mem hgt hnext
            exact ih (i + pNat, Int.ofNat (n - pNat - 1)) hlt res hinv' hresx
      · by_cases hshift :
          ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) = 0
        · rw [twoWayShortLoopCore_none_of_shift_zero haystack needle start maxStart msNat pNat n i mem hgt hj hshift] at hresx
          cases hresx
        · by_cases hnext :
            i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat) ≤ i
          · rw [twoWayShortLoopCore_none_of_shift_nonprogress haystack needle start maxStart msNat pNat n i mem hgt hj hshift hnext] at hresx
            cases hresx
          · rw [twoWayShortLoopCore_shift_eq haystack needle start maxStart msNat pNat n i mem hgt hj hshift hnext] at hresx
            rcases hinvx with ⟨hperiod, _⟩
            have hpos :
                0 < (ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat := by
              exact Nat.pos_of_ne_zero hshift
            have hinv' :
                ShortLoopInv haystack needle
                  (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat))
                  n pNat (-1) := by
              exact shortLoopInv_shift haystack needle i n pNat
                ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat)
                hperiod hpos
            have hlt :
                WellFoundedRelation.rel
                  (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1))
                  (i, mem) := by
              change
                shortLoopMeasure maxStart
                  (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1)) <
                shortLoopMeasure maxStart (i, mem)
              exact shortLoopMeasure_shift_lt maxStart i
                ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat)
                mem hgt hpos
            exact ih
              (i + ((ViE.PieceTree.twoWayForward1 haystack needle i n (max (Int.ofNat msNat) mem + 1)).toNat - msNat), (-1))
              hlt res hinv' hresx
  exact hfix (i, mem) r hinv hres

/-- Soundness of the short-period wrapper used by two-way search. -/
theorem twoWayShortLoop_sound
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n r : Nat)
    (hinv : ShortLoopInv haystack needle start n pNat (-1))
    (hgap : msNat < n - pNat)
    (hcover : msNat + 1 ≤ pNat)
    (hsize : needle.size ≤ haystack.size)
    (hmax : maxStart = haystack.size - needle.size)
    (hn : n = needle.size)
    (hres : ViE.PieceTree.twoWayShortLoop haystack needle start maxStart msNat pNat n start (-1) = some r) :
    matchesAt haystack needle r = true := by
  simpa [ViE.PieceTree.twoWayShortLoop] using
    (twoWayShortLoopCore_sound haystack needle start maxStart msNat pNat n start (-1) r
      hinv hgap hcover hsize hmax hn hres)

/-- Acceptance in the long-period loop implies a full-pattern match at the
current position. -/
theorem twoWayLongLoopCore_accept_matchesAt
    (haystack needle : ByteArray)
    (_start maxStart msNat _pNat n i : Nat)
    (hms : msNat < n)
    (hbound : i + needle.size ≤ haystack.size)
    (hn : n = needle.size)
    (_hgt : ¬ i > maxStart)
    (hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n)
    (hj2 : ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0) :
    matchesAt haystack needle i = true := by
  have hfw_eq :
      ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) = Int.ofNat n := by
    have hstart0 : 0 ≤ Int.ofNat (msNat + 1) := Int.natCast_nonneg _
    have hstartLe : Int.toNat (Int.ofNat (msNat + 1)) ≤ n := by
      simp
      exact Nat.succ_le_of_lt hms
    have hbounds := twoWayForward2_bounds haystack needle i n (Int.ofNat (msNat + 1)) hstart0 hstartLe
    apply Int.le_antisymm hbounds.2
    simpa using hj
  have hfw_range :
      matchesRange haystack needle i (msNat + 1) n := by
    have hcore :
        ViE.PieceTree.twoWayForward2Core haystack needle i n (msNat + 1) = n := by
      exact Int.ofNat.inj (by simpa [twoWayForward2_eq_core] using hfw_eq)
    exact twoWayForward2Core_eq_n_matchesRange haystack needle i n (msNat + 1) (by omega) hcore
  have hbw_range :
      matchesRange haystack needle i 0 (msNat + 1) := by
    have hbw_core :
        ViE.PieceTree.twoWayBackward2Core haystack needle i (msNat + 1) < 0 := by
      simpa [twoWayBackward2_of_nonneg haystack needle i (Int.ofNat msNat) (by simp)] using hj2
    exact twoWayBackward2Core_lt_zero_matchesRange haystack needle i (msNat + 1) hbw_core
  have hall : matchesRange haystack needle i 0 n := by
    intro j hj1 hj2
    by_cases hsplit : j < msNat + 1
    · exact hbw_range j hj1 hsplit
    · exact hfw_range j (by omega) hj2
  have hbound' : i + n ≤ haystack.size := by simpa [hn] using hbound
  have hall' : matchesRange haystack needle i 0 needle.size := by simpa [hn] using hall
  exact matchesAt_true_of_range haystack needle i (by simpa [hn] using hbound') hall'

/-- Soundness of the long-period recursive loop: every reported position is a
real match. -/
theorem twoWayLongLoopCore_sound
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n i r : Nat)
    (hms : msNat < n)
    (hsize : needle.size ≤ haystack.size)
    (hmax : maxStart = haystack.size - needle.size)
    (hn : n = needle.size)
    (hres : ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = some r) :
    matchesAt haystack needle r = true := by
  let C : Nat → Prop :=
    fun i => ∀ r, ViE.PieceTree.twoWayLongLoopCore haystack needle start maxStart msNat pNat n i = some r →
      matchesAt haystack needle r = true
  let _ : WellFoundedRelation Nat := measure (fun i => maxStart + 1 - i)
  have hfix : ∀ i, C i := by
    refine WellFounded.fix (measure (fun i => maxStart + 1 - i)).wf ?_
    intro i ih r hresx
    by_cases hgt : i > maxStart
    · rw [twoWayLongLoopCore_none_of_gt haystack needle start maxStart msNat pNat n i hgt] at hresx
      cases hresx
    · by_cases hj : ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1)) >= n
      · by_cases hj2 : ViE.PieceTree.twoWayBackward2 haystack needle i (Int.ofNat msNat) < 0
        · rw [twoWayLongLoopCore_accept_eq_some haystack needle start maxStart msNat pNat n i hgt hj hj2] at hresx
          cases hresx
          have hbound : i + needle.size ≤ haystack.size := by
            have hi : i ≤ maxStart := by omega
            calc
              i + needle.size ≤ maxStart + needle.size := Nat.add_le_add_right hi _
              _ = haystack.size := by rw [hmax, Nat.sub_add_cancel hsize]
          exact twoWayLongLoopCore_accept_matchesAt haystack needle start maxStart msNat pNat n i
            hms hbound hn hgt hj hj2
        · by_cases hnext : i + pNat ≤ i
          · rw [twoWayLongLoopCore_none_of_period_nonprogress haystack needle start maxStart msNat pNat n i hgt hj hj2 hnext] at hresx
            cases hresx
          · rw [twoWayLongLoopCore_period_eq haystack needle start maxStart msNat pNat n i hgt hj hj2 hnext] at hresx
            have hlt : WellFoundedRelation.rel (i + pNat) i := by
              change maxStart + 1 - (i + pNat) < maxStart + 1 - i
              have hp : 0 < pNat := by omega
              have hi : i ≤ maxStart := by omega
              omega
            exact ih (i + pNat) hlt r hresx
      · by_cases hshift :
          ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) = 0
        · rw [twoWayLongLoopCore_none_of_shift_zero haystack needle start maxStart msNat pNat n i hgt hj hshift] at hresx
          cases hresx
        · by_cases hnext :
            i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat) ≤ i
          · rw [twoWayLongLoopCore_none_of_shift_nonprogress haystack needle start maxStart msNat pNat n i hgt hj hshift hnext] at hresx
            cases hresx
          · rw [twoWayLongLoopCore_shift_eq haystack needle start maxStart msNat pNat n i hgt hj hshift hnext] at hresx
            have hpos :
                0 < (ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat := by
              exact Nat.pos_of_ne_zero hshift
            have hlt : WellFoundedRelation.rel
                (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat)) i := by
              change
                maxStart + 1 - (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat))
                  < maxStart + 1 - i
              have hi : i ≤ maxStart := by omega
              omega
            exact ih
              (i + ((ViE.PieceTree.twoWayForward2 haystack needle i n (Int.ofNat (msNat + 1))).toNat - msNat))
              hlt r hresx
  exact hfix i r hres

/-- Soundness of the long-period wrapper used by two-way search. -/
theorem twoWayLongLoop_sound
    (haystack needle : ByteArray)
    (start maxStart msNat pNat n r : Nat)
    (hms : msNat < n)
    (hsize : needle.size ≤ haystack.size)
    (hmax : maxStart = haystack.size - needle.size)
    (hn : n = needle.size)
    (hres : ViE.PieceTree.twoWayLongLoop haystack needle start maxStart msNat pNat n start = some r) :
    matchesAt haystack needle r = true := by
  simpa [ViE.PieceTree.twoWayLongLoop] using
    (twoWayLongLoopCore_sound haystack needle start maxStart msNat pNat n start r
      hms hsize hmax hn hres)

theorem twoWaySearch_sound_of_long_true_branch
    (haystack needle : ByteArray) (start r : Nat)
    (hsize : needle.size ≤ haystack.size)
    (hstart : start + needle.size ≤ haystack.size)
    (hms :
      (ViE.PieceTree.maximalSuffix needle true).fst.toNat < needle.size)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle true).fst
        (ViE.PieceTree.maximalSuffix needle true).fst.toNat
        (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 = false)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r)
    (hchoose :
      (ViE.PieceTree.maximalSuffix needle false).fst <
        (ViE.PieceTree.maximalSuffix needle true).fst) :
    matchesAt haystack needle r = true := by
  have hne : needle.size ≠ 0 := by
    intro hz
    simpa [hz] using hms
  unfold ViE.PieceTree.twoWaySearch at hres
  have hempty : needle ≠ ByteArray.empty := by
    intro h
    simpa [h] using hne
  have hbad : ¬ (haystack.size < needle.size || start + needle.size > haystack.size) := by
    simp [hsize, hstart]
  simp [hempty, hbad, hchoose, hshort] at hres
  exact twoWayLongLoop_sound haystack needle start (haystack.size - needle.size)
    (ViE.PieceTree.maximalSuffix needle true).fst.toNat
    (ViE.PieceTree.maximalSuffix needle true).snd.toNat
    needle.size r
    hms hsize rfl rfl hres

theorem twoWaySearch_sound_of_long_false_branch
    (haystack needle : ByteArray) (start r : Nat)
    (hsize : needle.size ≤ haystack.size)
    (hstart : start + needle.size ≤ haystack.size)
    (hms :
      (ViE.PieceTree.maximalSuffix needle false).fst.toNat < needle.size)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle false).fst
        (ViE.PieceTree.maximalSuffix needle false).fst.toNat
        (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 = false)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r)
    (hchoose :
      ¬ ((ViE.PieceTree.maximalSuffix needle false).fst <
        (ViE.PieceTree.maximalSuffix needle true).fst)) :
    matchesAt haystack needle r = true := by
  have hne : needle.size ≠ 0 := by
    intro hz
    simpa [hz] using hms
  unfold ViE.PieceTree.twoWaySearch at hres
  have hempty : needle ≠ ByteArray.empty := by
    intro h
    simpa [h] using hne
  have hbad : ¬ (haystack.size < needle.size || start + needle.size > haystack.size) := by
    simp [hsize, hstart]
  simp [hempty, hbad, hchoose, hshort] at hres
  exact twoWayLongLoop_sound haystack needle start (haystack.size - needle.size)
    (ViE.PieceTree.maximalSuffix needle false).fst.toNat
    (ViE.PieceTree.maximalSuffix needle false).snd.toNat
    needle.size r
    hms hsize rfl rfl hres

/-- Prefix-side facts needed to turn a successful short-period precheck into a
true periodicity witness. -/
def TwoWayPrefixFacts (needle : ByteArray) (useLe : Bool) : Prop :=
  let ms := (ViE.PieceTree.maximalSuffix needle useLe).fst
  let msNat := ms.toNat
  let pNat := (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat
  (¬ ms < 0 ∧ needle.size - pNat - 1 ≤ msNat) ∨
    (ms < 0 ∧ NeedlePeriodInv needle needle.size pNat)

/-- Prefix facts either provide a nonnegative split point with enough prefix
coverage, or identify the degenerate `ms < 0` case together with a direct
periodicity witness for the whole needle. -/
theorem twoWayPrefixFacts_cases
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayPrefixFacts needle useLe) :
    (¬ (ViE.PieceTree.maximalSuffix needle useLe).fst < 0 ∧
      needle.size - (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat - 1 ≤
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat) ∨
    ((ViE.PieceTree.maximalSuffix needle useLe).fst < 0 ∧
      NeedlePeriodInv needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat) := by
  exact h

/-- Generic constructor for the prefix-side facts used by the short-period
branch. This isolates the remaining proof obligation to nonnegativity and the
prefix-cover bound for the chosen maximal suffix. -/
theorem twoWayPrefixFacts_intro
    (needle : ByteArray) (useLe : Bool)
    (hms :
      ¬ (ViE.PieceTree.maximalSuffix needle useLe).fst < 0)
    (hcover :
      needle.size - (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat - 1 ≤
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat) :
    TwoWayPrefixFacts needle useLe := by
  exact Or.inl ⟨hms, hcover⟩

/-- Alternate constructor for prefix facts in the degenerate case where the
maximal-suffix split point stays negative but the reported period is already
known to be valid for the whole needle. -/
theorem twoWayPrefixFacts_intro_neg_periodic
    (needle : ByteArray) (useLe : Bool)
    (hms :
      (ViE.PieceTree.maximalSuffix needle useLe).fst < 0)
    (hperiod :
      NeedlePeriodInv needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat) :
    TwoWayPrefixFacts needle useLe := by
  exact Or.inr ⟨hms, hperiod⟩

/-- Facts needed once the short-period precheck succeeds for a chosen
maximal-suffix ordering. -/
def TwoWayShortFacts (needle : ByteArray) (useLe : Bool) : Prop :=
  let msNat := (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
  let pNat := (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat
  TwoWayPrefixFacts needle useLe ∧
    msNat < needle.size - pNat ∧
    msNat + 1 ≤ pNat

/-- Short-period facts expose the prefix-side conditions needed to extract a
periodicity witness from `prefixEqual`. -/
theorem twoWayShortFacts_prefix
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayShortFacts needle useLe) :
    TwoWayPrefixFacts needle useLe := by
  exact h.1

/-- Short-period facts expose the short-branch gap bound on the split point. -/
theorem twoWayShortFacts_gap
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayShortFacts needle useLe) :
    (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat <
      needle.size - (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  exact h.2.1

/-- Short-period facts expose the cover inequality used by the period jump. -/
theorem twoWayShortFacts_cover
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayShortFacts needle useLe) :
    (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat + 1 ≤
      (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  exact h.2.2

/-- Generic constructor for the full short-period fact bundle. Once prefix
facts, the gap bound, and the cover inequality are available, the short branch
can be justified without any additional assumptions. -/
theorem twoWayShortFacts_intro
    (needle : ByteArray) (useLe : Bool)
    (hprefix : TwoWayPrefixFacts needle useLe)
    (hgap :
      (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat <
        needle.size - (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat)
    (hcover :
      (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat + 1 ≤
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat) :
    TwoWayShortFacts needle useLe := by
  exact ⟨hprefix, hgap, hcover⟩

/-- The short-branch gap bound immediately implies that the chosen period is
strictly smaller than the needle length. -/
theorem twoWayShortFacts_period_lt_size
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayShortFacts needle useLe) :
    (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat < needle.size := by
  have hgap := twoWayShortFacts_gap needle useLe h
  omega

/-- Short-period facts expose the periodicity witness needed to replay the
short branch. -/
theorem twoWayShortFacts_period
    (needle : ByteArray) (useLe : Bool)
    (h : TwoWayShortFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    NeedlePeriodInv needle needle.size (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  rcases twoWayPrefixFacts_cases needle useLe (twoWayShortFacts_prefix needle useLe h) with hnonneg | hneg
  · have hms := hnonneg.1
    have hprefixCover := hnonneg.2
    have hgap := twoWayShortFacts_gap needle useLe h
    have hstop :
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat +
            (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat <
          needle.size := by
      omega
    exact needlePeriodInv_of_prefixEqual
      needle needle.size
      (ViE.PieceTree.maximalSuffix needle useLe).fst
      (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
      (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat
      hms hprefixCover hstop hshort
  · rcases hneg with ⟨_, hpfull⟩
    exact hpfull

/-- Branch facts needed to justify either the short-period or long-period path
after choosing a maximal-suffix ordering. The long-period branch only needs the
basic split-point bound `msNat < needle.size`, while the short-period branch
additionally requires periodicity, gap, and cover once the precheck succeeds. -/
def TwoWayBranchFacts (needle : ByteArray) (useLe : Bool) : Prop :=
  let ms := (ViE.PieceTree.maximalSuffix needle useLe).fst
  let msNat := ms.toNat
  let pNat := (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat
  let short :=
    ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size ms msNat pNat 0 = true
  short -> TwoWayShortFacts needle useLe

/-- Generic constructor for branch facts. This isolates the remaining
maximal-suffix obligation to a basic bound on `ms` plus a way to build
short-branch facts when the prefix precheck succeeds. -/
theorem twoWayBranchFacts_intro
    (needle : ByteArray) (useLe : Bool)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true ->
      TwoWayShortFacts needle useLe) :
    TwoWayBranchFacts needle useLe := by
  exact hshort

/-- When the short-period precheck succeeds, branch facts supply the full
short-branch invariant package. -/
theorem twoWayBranchFacts_short
    (needle : ByteArray) (useLe : Bool)
    (hfacts : TwoWayBranchFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    TwoWayShortFacts needle useLe := by
  exact hfacts hshort

/-- Branch facts plus a successful short-period precheck are enough to recover
the periodicity witness needed by the short branch. -/
theorem twoWayBranchFacts_short_period
    (needle : ByteArray) (useLe : Bool)
    (hfacts : TwoWayBranchFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    NeedlePeriodInv needle needle.size (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  exact twoWayShortFacts_period needle useLe (twoWayBranchFacts_short needle useLe hfacts hshort) hshort

/-- Branch facts plus a successful short-period precheck recover the gap bound
used by the short-period loop. -/
theorem twoWayBranchFacts_short_gap
    (needle : ByteArray) (useLe : Bool)
    (hfacts : TwoWayBranchFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat <
      needle.size - (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  exact twoWayShortFacts_gap needle useLe (twoWayBranchFacts_short needle useLe hfacts hshort)

/-- Branch facts plus a successful short-period precheck recover the cover
inequality needed by the short-period loop. -/
theorem twoWayBranchFacts_short_cover
    (needle : ByteArray) (useLe : Bool)
    (hfacts : TwoWayBranchFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat + 1 ≤
      (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat := by
  exact twoWayShortFacts_cover needle useLe (twoWayBranchFacts_short needle useLe hfacts hshort)

/-- Branch facts plus a successful short-period precheck imply that the chosen
period is strictly smaller than the needle. -/
theorem twoWayBranchFacts_short_period_lt_size
    (needle : ByteArray) (useLe : Bool)
    (hfacts : TwoWayBranchFacts needle useLe)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle useLe).fst
        (ViE.PieceTree.maximalSuffix needle useLe).fst.toNat
        (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat 0 = true) :
    (ViE.PieceTree.maximalSuffix needle useLe).snd.toNat < needle.size := by
  exact twoWayShortFacts_period_lt_size needle useLe
    (twoWayBranchFacts_short needle useLe hfacts hshort)

theorem twoWaySearch_sound_of_short_true_branch
    (haystack needle : ByteArray) (start r : Nat)
    (hsize : needle.size ≤ haystack.size)
    (hstart : start + needle.size ≤ haystack.size)
    (hfacts : TwoWayBranchFacts needle true)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle true).fst
        (ViE.PieceTree.maximalSuffix needle true).fst.toNat
        (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 = true)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r)
    (hchoose :
      (ViE.PieceTree.maximalSuffix needle false).fst <
        (ViE.PieceTree.maximalSuffix needle true).fst) :
    matchesAt haystack needle r = true := by
  have hperiod := twoWayBranchFacts_short_period needle true hfacts hshort
  have hgap := twoWayBranchFacts_short_gap needle true hfacts hshort
  have hcover := twoWayBranchFacts_short_cover needle true hfacts hshort
  have hne : needle ≠ ByteArray.empty := by
    intro h
    have : needle.size = 0 := by simpa [h]
    omega
  unfold ViE.PieceTree.twoWaySearch at hres
  have hbad : ¬ (haystack.size < needle.size || start + needle.size > haystack.size) := by
    simp [hsize, hstart]
  simp [hne, hbad, hchoose, hshort] at hres
  have hinv : ShortLoopInv haystack needle start needle.size (ViE.PieceTree.maximalSuffix needle true).snd.toNat (-1) := by
    exact shortLoopInv_init haystack needle start needle.size (ViE.PieceTree.maximalSuffix needle true).snd.toNat hperiod
  exact twoWayShortLoop_sound haystack needle start (haystack.size - needle.size)
    (ViE.PieceTree.maximalSuffix needle true).fst.toNat
    (ViE.PieceTree.maximalSuffix needle true).snd.toNat
    needle.size r
    hinv hgap hcover hsize rfl rfl hres

theorem twoWaySearch_sound_of_short_false_branch
    (haystack needle : ByteArray) (start r : Nat)
    (hsize : needle.size ≤ haystack.size)
    (hstart : start + needle.size ≤ haystack.size)
    (hfacts : TwoWayBranchFacts needle false)
    (hshort :
      ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
        (ViE.PieceTree.maximalSuffix needle false).fst
        (ViE.PieceTree.maximalSuffix needle false).fst.toNat
        (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 = true)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r)
    (hchoose :
      ¬ ((ViE.PieceTree.maximalSuffix needle false).fst <
        (ViE.PieceTree.maximalSuffix needle true).fst)) :
    matchesAt haystack needle r = true := by
  have hperiod := twoWayBranchFacts_short_period needle false hfacts hshort
  have hgap := twoWayBranchFacts_short_gap needle false hfacts hshort
  have hcover := twoWayBranchFacts_short_cover needle false hfacts hshort
  have hne : needle ≠ ByteArray.empty := by
    intro h
    have : needle.size = 0 := by simpa [h]
    omega
  unfold ViE.PieceTree.twoWaySearch at hres
  have hbad : ¬ (haystack.size < needle.size || start + needle.size > haystack.size) := by
    simp [hsize, hstart]
  simp [hne, hbad, hchoose, hshort] at hres
  have hinv : ShortLoopInv haystack needle start needle.size (ViE.PieceTree.maximalSuffix needle false).snd.toNat (-1) := by
    exact shortLoopInv_init haystack needle start needle.size (ViE.PieceTree.maximalSuffix needle false).snd.toNat hperiod
  exact twoWayShortLoop_sound haystack needle start (haystack.size - needle.size)
    (ViE.PieceTree.maximalSuffix needle false).fst.toNat
    (ViE.PieceTree.maximalSuffix needle false).snd.toNat
    needle.size r
    hinv hgap hcover hsize rfl rfl hres

/-- Family of branch-specific facts required to justify the final soundness
theorem for both maximal-suffix orderings. -/
def TwoWayFacts (needle : ByteArray) : Prop :=
  ∀ useLe, TwoWayBranchFacts needle useLe

/-- Generic constructor for the full family of branch facts. Once each
maximal-suffix ordering can supply its own branch facts, the top-level soundness
theorem no longer needs to know how they were obtained. -/
theorem twoWayFacts_intro
    (needle : ByteArray)
    (htrue : TwoWayBranchFacts needle true)
    (hfalse : TwoWayBranchFacts needle false) :
    TwoWayFacts needle := by
  intro useLe
  cases useLe
  · simpa using hfalse
  · simpa using htrue

/-- Top-level soundness of the two-way search, assuming the remaining
maximal-suffix side conditions used to choose the short/long branch. -/
theorem twoWaySearch_sound
    (haystack needle : ByteArray) (start r : Nat)
    (hstart : start ≤ haystack.size)
    (hfacts : TwoWayFacts needle)
    (hres : ViE.PieceTree.twoWaySearch haystack needle start = some r) :
    matchesAt haystack needle r = true := by
  by_cases hzero : needle.size = 0
  · have hz : needle = ByteArray.empty := by
      cases needle
      simp at hzero
      simp [hzero]
    subst hz
    rw [twoWaySearch_empty] at hres
    cases hres
    simp [matchesAt, hstart, matchesRange]
  · have hsize : needle.size ≤ haystack.size := by
      by_cases hlt : haystack.size < needle.size
      · rw [twoWaySearch_haystack_too_short_none haystack needle start hlt] at hres
        cases hres
      · omega
    have hstart' : start + needle.size ≤ haystack.size := by
      by_cases hout : start + needle.size > haystack.size
      · rw [twoWaySearch_start_out_of_range_none haystack needle start hzero hout] at hres
        cases hres
      · omega
    have hfacts_true := hfacts true
    have hfacts_false := hfacts false
    have hshort_true_ms := maximalSuffix_msNat_lt_size needle true hzero
    have hshort_false_ms := maximalSuffix_msNat_lt_size needle false hzero
    by_cases hchoose :
        (ViE.PieceTree.maximalSuffix needle false).fst <
          (ViE.PieceTree.maximalSuffix needle true).fst
    · by_cases hshort :
        ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
          (ViE.PieceTree.maximalSuffix needle true).fst
          (ViE.PieceTree.maximalSuffix needle true).fst.toNat
          (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 = true
      · exact twoWaySearch_sound_of_short_true_branch haystack needle start r
          hsize hstart' hfacts_true
          hshort hres hchoose
      · have hshort' :
            ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
              (ViE.PieceTree.maximalSuffix needle true).fst
              (ViE.PieceTree.maximalSuffix needle true).fst.toNat
              (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 = false := by
          cases hEq :
            ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
              (ViE.PieceTree.maximalSuffix needle true).fst
              (ViE.PieceTree.maximalSuffix needle true).fst.toNat
              (ViE.PieceTree.maximalSuffix needle true).snd.toNat 0 <;> simp [hEq] at hshort ⊢
        exact twoWaySearch_sound_of_long_true_branch haystack needle start r
          hsize hstart' hshort_true_ms
          hshort' hres hchoose
    · by_cases hshort :
        ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
          (ViE.PieceTree.maximalSuffix needle false).fst
          (ViE.PieceTree.maximalSuffix needle false).fst.toNat
          (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 = true
      · exact twoWaySearch_sound_of_short_false_branch haystack needle start r
          hsize hstart' hfacts_false
          hshort hres hchoose
      · have hshort' :
            ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
              (ViE.PieceTree.maximalSuffix needle false).fst
              (ViE.PieceTree.maximalSuffix needle false).fst.toNat
              (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 = false := by
          cases hEq :
            ViE.PieceTree.twoWaySearch.prefixEqual needle needle.size
              (ViE.PieceTree.maximalSuffix needle false).fst
              (ViE.PieceTree.maximalSuffix needle false).fst.toNat
              (ViE.PieceTree.maximalSuffix needle false).snd.toNat 0 <;> simp [hEq] at hshort ⊢
        exact twoWaySearch_sound_of_long_false_branch haystack needle start r
          hsize hstart' hshort_false_ms
          hshort' hres hchoose

end Proof.PieceTable.Search
