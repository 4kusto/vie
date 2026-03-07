-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import Bliku.Tui
import ViE.State
import ViE.Buffer.Content
import ViE.Color
import ViE.Unicode

namespace ViE.BlikuAdapter

private def toBlikuCursor (p : ViE.Point) : Bliku.Tui.Cursor :=
  { row := p.row.val, col := p.col.val }

private def toBlikuView (v : ViE.ViewState) : Bliku.Tui.ViewState :=
  {
    contentId := v.bufferId
    cursor := toBlikuCursor v.cursor
    scrollRow := v.scrollRow.val
    scrollCol := v.scrollCol.val
  }

private partial def toBlikuLayout (l : ViE.Layout) : Bliku.Tui.Layout :=
  match l with
  | .window id v => .pane id (toBlikuView v)
  | .hsplit left right ratio => .hsplit (toBlikuLayout left) (toBlikuLayout right) ratio
  | .vsplit top bottom ratio => .vsplit (toBlikuLayout top) (toBlikuLayout bottom) ratio

private def containsBoth (l : Bliku.Tui.Layout) (a b : Nat) : Bool :=
  l.containsWindow a && l.containsWindow b

private partial def wrapClusterSubtree
    (l : Bliku.Tui.Layout) (clusterId paneA paneB : Nat) : Bliku.Tui.Layout :=
  if !(containsBoth l paneA paneB) then
    l
  else
    match l with
    | .group gid body =>
        if containsBoth body paneA paneB then
          .group gid (wrapClusterSubtree body clusterId paneA paneB)
        else
          l
    | .hsplit left right ratio =>
        if containsBoth left paneA paneB then
          .hsplit (wrapClusterSubtree left clusterId paneA paneB) right ratio
        else if containsBoth right paneA paneB then
          .hsplit left (wrapClusterSubtree right clusterId paneA paneB) ratio
        else
          .group clusterId l
    | .vsplit top bottom ratio =>
        if containsBoth top paneA paneB then
          .vsplit (wrapClusterSubtree top clusterId paneA paneB) bottom ratio
        else if containsBoth bottom paneA paneB then
          .vsplit top (wrapClusterSubtree bottom clusterId paneA paneB) ratio
        else
          .group clusterId l
    | .pane _ _ => l

private def toBlikuConfig (c : ViE.EditorConfig) : Bliku.Tui.UiConfig :=
  let searchCursorStyle :=
    if c.searchHighlightCursorStyle.isEmpty then
      (ViE.Color.toBg .yellow) ++ (ViE.Color.toFg .black)
    else
      c.searchHighlightCursorStyle
  let visualSelectionStyle :=
    if c.visualSelectionStyle.isEmpty then "\x1b[7m" else c.visualSelectionStyle
  let cursorCharStyle :=
    if c.cursorCharStyle.isEmpty then
      (ViE.Color.toBg .white) ++ (ViE.Color.toFg .black)
    else
      c.cursorCharStyle
  let cursorSpaceStyle :=
    if c.cursorSpaceStyle.isEmpty then
      (ViE.Color.toBg .white) ++ (ViE.Color.toFg .black)
    else
      c.cursorSpaceStyle
  let floatingChromeActiveStyle :=
    if c.statusBarStyle.isEmpty then
      (ViE.Color.toFg .cyan)
    else
      c.statusBarStyle
  let floatingChromeInactiveStyle :=
    if c.statusBarStyle.isEmpty then
      (ViE.Color.toFg .white)
    else
      c.statusBarStyle
  {
    showLineNumbers := c.showLineNumbers
    vSplitStr := c.vSplitStr
    hSplitStr := c.hSplitStr
    emptyLineMarker := c.emptyLineMarker
    statusBarStyle := c.statusBarStyle
    resetStyle := c.resetStyle
    searchHighlightStyle := c.searchHighlightStyle
    searchHighlightCursorStyle := searchCursorStyle
    visualSelectionStyle := visualSelectionStyle
    cursorCharStyle := cursorCharStyle
    cursorSpaceStyle := cursorSpaceStyle
    floatingChromeActiveStyle := floatingChromeActiveStyle
    floatingChromeInactiveStyle := floatingChromeInactiveStyle
    tabStop := c.tabStop
  }

private def toBlikuOverlay (ov : ViE.FloatingOverlay) : Bliku.Tui.OverlayView :=
  {
    title := ov.title
    lines := ov.lines
    maxWidth := ov.maxWidth
    cursorRow := ov.cursorRow
    cursorCol := ov.cursorCol
  }

private def toBlikuCompletion (cp : ViE.CompletionPopup) : Bliku.Tui.CompletionView :=
  {
    items := cp.items.map (fun it => { label := it.label, insertText := it.insertText })
    selected := cp.selected
    anchorRow := cp.anchorRow
    anchorCol := cp.anchorCol
  }

private def bufferLines (buf : ViE.FileBuffer) : Array String := Id.run do
  let mut lines : Array String := #[]
  for i in [0:buf.lineCount] do
    lines := lines.push ((ViE.getLineFromBuffer buf ⟨i⟩).getD "")
  return lines

private def toBlikuBuffer (buf : ViE.FileBuffer) : Bliku.Tui.BufferState :=
  {
    id := buf.id
    filename := buf.filename
    lines := bufferLines buf
    missingEol := buf.missingEol
  }

private def explorerClusterSpecs (state : ViE.EditorState) : Array (Nat × Nat × Nat) := Id.run do
  let ws := state.getCurrentWorkspace
  let mut specs : Array (Nat × Nat × Nat) := #[]
  for (bufId, explorer) in state.explorers.reverse do
    match ws.layout.findWindowIdByBufferId bufId, explorer.previewWindowId with
    | some explorerWinId, some previewWinId =>
        if ws.layout.containsWindow previewWinId then
          specs := specs.push (bufId, explorerWinId, previewWinId)
    | _, _ => pure ()
  return specs

private def toBlikuDesktop (state : ViE.EditorState) : Bliku.DesktopLayout :=
  let ws := state.getCurrentWorkspace
  let clusterSpecs := explorerClusterSpecs state
  let groupedLayout :=
    clusterSpecs.foldl
      (fun acc (clusterId, explorerWinId, previewWinId) =>
        wrapClusterSubtree acc clusterId explorerWinId previewWinId)
      (toBlikuLayout ws.layout)
  let clusteredPaneIds := clusterSpecs.foldl (fun acc (_, explorerWinId, previewWinId) =>
    acc.push explorerWinId |>.push previewWinId) #[]
  let paneClusters :=
    ws.getFloatingWindowIds.foldl (fun acc wid =>
      if clusteredPaneIds.contains wid then
        acc
      else
        let (rowOff, colOff) := ws.getFloatingWindowOffset wid
        acc.push { root := .pane wid, rowOffset := rowOff, colOffset := colOff, sizePolicy := .default }) #[]
  let groupClusters :=
    clusterSpecs.map fun (clusterId, explorerWinId, _) =>
      let (rowOff, colOff) := ws.getFloatingWindowOffset explorerWinId
      {
        root := .group clusterId
        rowOffset := rowOff
        colOffset := colOff
        sizePolicy := .multiPane
        chrome := { kind := .bordered, title := some "Explorer" }
      }
  {
    layout := groupedLayout
    activePaneId := ws.activeWindowId
    floating := { clusters := paneClusters ++ groupClusters }
  }

private def toBlikuSelection (state : ViE.EditorState) : Option Bliku.Tui.SelectionState :=
  match state.selectionStart with
  | none => none
  | some anchor =>
      if state.mode == .visual || state.mode == .visualLine || state.mode == .visualBlock then
        let cursor :=
          if state.mode == .visualLine then
            let activeBuf := state.getActiveBuffer
            let anchorRow := anchor.row.val
            let cursorRow := state.getCursor.row.val
            let endRow := max anchorRow cursorRow
            let endLine := ViE.getLineFromBuffer activeBuf ⟨endRow⟩ |>.getD ""
            let endCol := ViE.Unicode.stringWidthWithTabStop endLine state.config.tabStop
            { row := endRow, col := endCol }
          else
            toBlikuCursor state.getCursor
        let anchor' :=
          if state.mode == .visualLine then
            let anchorRow := anchor.row.val
            let cursorRow := state.getCursor.row.val
            { row := min anchorRow cursorRow, col := 0 }
          else
            toBlikuCursor anchor
        some {
          anchor := anchor'
          cursor := cursor
          block := state.mode == .visualBlock
        }
      else
        none

private def toBlikuCommandLine (state : ViE.EditorState) : Option Bliku.Tui.CommandLineState :=
  let text := state.inputState.commandBuffer
  match state.mode with
  | .command => some { leader := ":", text := text, cursorCol := text.length }
  | .searchForward => some { leader := "/", text := text, cursorCol := text.length }
  | .searchBackward => some { leader := "?", text := text, cursorCol := text.length }
  | _ => none

private def statusLine (state : ViE.EditorState) : String :=
  let ws := state.getCurrentWorkspace
  let buf := state.getActiveBuffer
  let fileName := buf.filename.getD "[No Name]"
  let eolMark := if buf.missingEol then " [noeol]" else ""
  s!"-- {state.mode} -- {fileName}{eolMark} [W:{ws.activeWindowId} B:{buf.id}] [{state.getCurrentWorkgroup.name}] {ws.name}"

private def toRenderInput (state : ViE.EditorState) : Bliku.Tui.RenderInput :=
  {
    selection := toBlikuSelection state
    commandLine := toBlikuCommandLine state
    messageLine := state.message
    statusLine := statusLine state
    overlay := state.floatingOverlay.map toBlikuOverlay
    completion := state.completionPopup.map toBlikuCompletion
    hideTerminalCursor :=
      state.mode != .command &&
      state.mode != .searchForward &&
      state.mode != .searchBackward &&
      state.floatingOverlay.isNone
  }

def toModel (state : ViE.EditorState) : Bliku.Tui.Model :=
  let ws := state.getCurrentWorkspace
  {
    workspace := {
      name := ws.name
      desktop := toBlikuDesktop state
    }
    buffers := ws.buffers.toArray.map toBlikuBuffer
    config := toBlikuConfig state.config
    windowHeight := state.windowHeight
    windowWidth := state.windowWidth
    dirty := state.dirty
  }

def fromModel (state : ViE.EditorState) (model : Bliku.Tui.Model) : ViE.EditorState :=
  { state with
    windowHeight := model.windowHeight
    windowWidth := model.windowWidth
  }

def render (state : ViE.EditorState) : IO ViE.EditorState := do
  let model := toModel state
  let input := toRenderInput state
  let model' ← Bliku.Tui.renderWith model input
  pure (fromModel state model')

end ViE.BlikuAdapter
