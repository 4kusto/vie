-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViETest.Undo
import ViETest.Buffer
import ViETest.Layout
import ViETest.Integration
import ViETest.Keybinds
import ViETest.Mode
import ViETest.CursorReproduction
import ViETest.PasteReproduction
import ViETest.Workspace
import ViETest.PreviewData
import ViETest.WorkgroupExplorer
import ViETest.ExplorerPreview
import ViETest.PieceTable.Basic
import ViETest.PieceTable.UndoRedo
import ViETest.PieceTable.Appended
import ViETest.PieceTable.Stress
import ViETest.PieceTable.Search
import ViETest.MissingEol
import ViETest.Scroll
import ViETest.Checkpoint
import ViETest.SearchHighlight
import ViETest.TreeStats
import ViETest.SyntaxHighlight
import ViETest.InfoView
import ViETest.Lsp

def test : IO Unit := do
  IO.println "Running all tests..."
  ViETest.Undo.test
  ViETest.Buffer.test
  ViETest.Layout.test
  ViETest.Integration.test
  ViETest.Keybinds.test
  ViETest.Mode.test
  ViETest.CursorReproduction.test
  ViETest.PasteReproduction.test
  ViETest.Workspace.test
  ViETest.PreviewData.test
  ViETest.WorkgroupExplorer.test
  ViETest.ExplorerPreview.test
  ViETest.Scroll.test
  ViETest.PieceTable.Basic.test
  ViETest.PieceTable.UndoRedo.test
  ViETest.PieceTable.Appended.test
  ViETest.PieceTable.Stress.test
  ViETest.PieceTable.Search.test
  ViETest.MissingEol.test
  ViETest.Checkpoint.test
  ViETest.SearchHighlight.test
  ViETest.TreeStats.test
  ViETest.SyntaxHighlight.test
  ViETest.InfoView.test
  ViETest.Lsp.test
  IO.println "All tests finished."

def main : IO Unit := do
  test
