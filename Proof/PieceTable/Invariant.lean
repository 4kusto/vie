-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.Data.PieceTable.Invariant

namespace Proof.PieceTable

open ViE

theorem bplusInvariant_empty : ViE.PieceTree.bplusInvariant ViE.PieceTree.empty := by
  simpa using ViE.PieceTree.bplusInvariant_empty

theorem bplusInvariant_leaf
    (pieces : Array ViE.Piece) (s : ViE.Stats) (m : ViE.SearchBloom)
    (hsize : pieces.size ≤ ViE.NodeCapacity) :
    ViE.PieceTree.bplusInvariant (.leaf pieces s m) := by
  simpa using ViE.PieceTree.bplusInvariant_leaf pieces s m hsize

theorem bplusInvariant_mkLeaf
    (pieces : Array ViE.Piece) (pt : ViE.PieceTable)
    (hsize : pieces.size ≤ ViE.NodeCapacity) :
    ViE.PieceTree.bplusInvariant (ViE.PieceTree.mkLeaf pieces pt) := by
  unfold ViE.PieceTree.mkLeaf
  by_cases hempty : pieces.size = 0
  · simp [hempty, bplusInvariant_empty]
  ·
    let s := pieces.foldl (fun acc p => acc + (ViE.Stats.ofPiece p)) ViE.Stats.empty
    let m := ViE.PieceTree.buildBloomForPieces pieces pt
    have hleaf : ViE.PieceTree.bplusInvariant (ViE.PieceTree.leaf pieces s m) := by
      simpa [s, m] using bplusInvariant_leaf pieces s m hsize
    simp [hempty, s, m, hleaf]

theorem bplusInvariant_intro
    (t : ViE.PieceTree)
    (hArity : ViE.PieceTree.validNodeArity t true)
    (hDepth : ViE.PieceTree.uniformLeafDepth t)
    (hMeta : ViE.PieceTree.internalMetaWellFormed t) :
    ViE.PieceTree.bplusInvariant t := by
  simpa using ViE.PieceTree.bplusInvariant_intro t hArity hDepth hMeta

theorem bplusInvariant_validNodeArity
    (t : ViE.PieceTree)
    (h : ViE.PieceTree.bplusInvariant t) :
    ViE.PieceTree.validNodeArity t true := by
  simpa using ViE.PieceTree.bplusInvariant_validNodeArity t h

theorem bplusInvariant_uniformLeafDepth
    (t : ViE.PieceTree)
    (h : ViE.PieceTree.bplusInvariant t) :
    ViE.PieceTree.uniformLeafDepth t := by
  simpa using ViE.PieceTree.bplusInvariant_uniformLeafDepth t h

theorem bplusInvariant_internalMetaWellFormed
    (t : ViE.PieceTree)
    (h : ViE.PieceTree.bplusInvariant t) :
    ViE.PieceTree.internalMetaWellFormed t := by
  simpa using ViE.PieceTree.bplusInvariant_internalMetaWellFormed t h

theorem validNodeArity_mkInternal_root_of_eq
    (children : Array ViE.PieceTree)
    (vc : Array ViE.PieceTree) (s : ViE.Stats) (sm : ViE.SearchBloom) (im : ViE.InternalMeta)
    (heq : ViE.PieceTree.mkInternal children = ViE.PieceTree.internal vc s sm im)
    (hsize : 1 ≤ vc.size ∧ vc.size ≤ ViE.NodeCapacity)
    (hchildren : ViE.PieceTree.validNodeArityList vc.toList) :
    ViE.PieceTree.validNodeArity (ViE.PieceTree.mkInternal children) true := by
  rw [heq]
  simp [ViE.PieceTree.validNodeArity, hsize, hchildren]

theorem validNodeArity_mkInternal_nonroot_of_eq
    (children : Array ViE.PieceTree)
    (vc : Array ViE.PieceTree) (s : ViE.Stats) (sm : ViE.SearchBloom) (im : ViE.InternalMeta)
    (heq : ViE.PieceTree.mkInternal children = ViE.PieceTree.internal vc s sm im)
    (hsize : 2 ≤ vc.size ∧ vc.size ≤ ViE.NodeCapacity)
    (hchildren : ViE.PieceTree.validNodeArityList vc.toList) :
    ViE.PieceTree.validNodeArity (ViE.PieceTree.mkInternal children) false := by
  rw [heq]
  simp [ViE.PieceTree.validNodeArity, hsize, hchildren]

end Proof.PieceTable
