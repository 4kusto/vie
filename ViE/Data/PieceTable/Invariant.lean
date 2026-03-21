-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.Data.PieceTable.Tree

namespace ViE
namespace PieceTree

mutual
  /-- Collect depths of all leaves, starting from depth `d`. -/
  def leafDepthsAux (t : PieceTree) (d : Nat) : List Nat :=
    match t with
    | .empty => []
    | .leaf _ _ _ => [d]
    | .internal children _ _ _ => leafDepthsAuxList children.toList (d + 1)

  def leafDepthsAuxList (children : List PieceTree) (d : Nat) : List Nat :=
    match children with
    | [] => []
    | c :: rest => leafDepthsAux c d ++ leafDepthsAuxList rest d
end

/-- Collect depths of all leaves. -/
def leafDepths (t : PieceTree) : List Nat :=
  leafDepthsAux t 0

/-- All leaves must have identical depth. -/
def uniformLeafDepth (t : PieceTree) : Prop :=
  match leafDepths t with
  | [] => True
  | d :: ds => ∀ d', d' ∈ ds → d' = d

/-- Generic monotonicity check for cumulative arrays. -/
def nondecreasingUInt64 (xs : Array UInt64) : Prop :=
  ∀ i j, i ≤ j → j < xs.size → xs[i]! ≤ xs[j]!

mutual
  /-- Arity constraints for B+tree-like node shape.
  Root can be empty, root leaf can be empty, root internal needs at least one child.
  Non-root leaves need at least one piece, non-root internal nodes need at least two children. -/
  def validNodeArity (t : PieceTree) (isRoot : Bool) : Prop :=
    match t with
    | .empty =>
        isRoot = true
    | .leaf pieces _ _ =>
        if isRoot then
          pieces.size ≤ NodeCapacity
        else
          1 ≤ pieces.size ∧ pieces.size ≤ NodeCapacity
    | .internal children _ _ _ =>
        let selfOk :=
          if isRoot then
            1 ≤ children.size ∧ children.size ≤ NodeCapacity
          else
            2 ≤ children.size ∧ children.size ≤ NodeCapacity
        selfOk ∧ validNodeArityList children.toList

  def validNodeArityList (children : List PieceTree) : Prop :=
    match children with
    | [] => True
    | c :: rest => validNodeArity c false ∧ validNodeArityList rest
end

mutual
  /-- Internal cumulative metadata must match child count and be nondecreasing. -/
  def internalMetaWellFormed : PieceTree → Prop
    | .empty => True
    | .leaf _ _ _ => True
    | .internal children _ _ imeta =>
        imeta.cumulativeBytes.size = children.size + 1 ∧
        imeta.cumulativeLines.size = children.size + 1 ∧
        imeta.cumulativeChars.size = children.size + 1 ∧
        imeta.cumulativeBytes[0]? = some 0 ∧
        imeta.cumulativeLines[0]? = some 0 ∧
        imeta.cumulativeChars[0]? = some 0 ∧
        nondecreasingUInt64 imeta.cumulativeBytes ∧
        nondecreasingUInt64 imeta.cumulativeLines ∧
        nondecreasingUInt64 imeta.cumulativeChars ∧
        internalMetaWellFormedList children.toList

  def internalMetaWellFormedList : List PieceTree → Prop
    | [] => True
    | c :: rest => internalMetaWellFormed c ∧ internalMetaWellFormedList rest
end

/-- Combined B+tree-style invariant for PieceTree. -/
def bplusInvariant (t : PieceTree) : Prop :=
  validNodeArity t true ∧
  uniformLeafDepth t ∧
  internalMetaWellFormed t

theorem bplusInvariant_intro
    (t : PieceTree)
    (hArity : validNodeArity t true)
    (hDepth : uniformLeafDepth t)
    (hMeta : internalMetaWellFormed t) :
    bplusInvariant t := by
  exact ⟨hArity, hDepth, hMeta⟩

theorem bplusInvariant_validNodeArity
    (t : PieceTree)
    (h : bplusInvariant t) :
    validNodeArity t true := by
  exact h.1

theorem bplusInvariant_uniformLeafDepth
    (t : PieceTree)
    (h : bplusInvariant t) :
    uniformLeafDepth t := by
  exact h.2.1

theorem bplusInvariant_internalMetaWellFormed
    (t : PieceTree)
    (h : bplusInvariant t) :
    internalMetaWellFormed t := by
  exact h.2.2

theorem bplusInvariant_empty : bplusInvariant PieceTree.empty := by
  simp [bplusInvariant, validNodeArity, uniformLeafDepth, leafDepths, leafDepthsAux, internalMetaWellFormed]

theorem bplusInvariant_leaf
    (pieces : Array Piece) (s : Stats) (m : SearchBloom)
    (hsize : pieces.size ≤ NodeCapacity) :
    bplusInvariant (.leaf pieces s m) := by
  simp [bplusInvariant, validNodeArity, uniformLeafDepth, leafDepths, leafDepthsAux, internalMetaWellFormed, hsize]

end PieceTree
end ViE
