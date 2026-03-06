import Bliku.Tui
import ViE.State
import ViE.Buffer.Content
import ViE.Color

namespace ViE.BlikuAdapter

private def toBlikuMode (m : ViE.Mode) : Bliku.Tui.Mode :=
  match m with
  | .normal => .normal
  | .insert => .insert
  | .command => .command
  | .searchForward => .searchForward
  | .searchBackward => .searchBackward
  | .visual => .visual
  | .visualBlock => .visualBlock

private def toBlikuCursor (p : ViE.Point) : Bliku.Tui.Cursor :=
  { row := p.row.val, col := p.col.val }

private def toBlikuView (v : ViE.ViewState) : Bliku.Tui.ViewState :=
  {
    bufferId := v.bufferId
    cursor := toBlikuCursor v.cursor
    scrollRow := v.scrollRow.val
    scrollCol := v.scrollCol.val
  }

private partial def toBlikuLayout (l : ViE.Layout) : Bliku.Tui.Layout :=
  match l with
  | .window id v => .window id (toBlikuView v)
  | .hsplit left right ratio => .hsplit (toBlikuLayout left) (toBlikuLayout right) ratio
  | .vsplit top bottom ratio => .vsplit (toBlikuLayout top) (toBlikuLayout bottom) ratio

private def toBlikuConfig (c : ViE.EditorConfig) : Bliku.Tui.UiConfig :=
  let searchCursorStyle :=
    if c.searchHighlightCursorStyle.isEmpty then
      (ViE.Color.toBg .yellow) ++ (ViE.Color.toFg .black)
    else
      c.searchHighlightCursorStyle
  let visualSelectionStyle :=
    if c.visualSelectionStyle.isEmpty then "\x1b[7m" else c.visualSelectionStyle
  let cursorCharStyle :=
    if c.cursorCharStyle.isEmpty then (ViE.Color.toBg .white) ++ (ViE.Color.toFg .black) else c.cursorCharStyle
  let cursorSpaceStyle :=
    if c.cursorSpaceStyle.isEmpty then (ViE.Color.toBg .white) ++ (ViE.Color.toFg .black) else c.cursorSpaceStyle
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
    tabStop := c.tabStop
  }

private def toBlikuOverlay (ov : ViE.FloatingOverlay) : Bliku.Tui.FloatingOverlay :=
  {
    title := ov.title
    lines := ov.lines
    maxWidth := ov.maxWidth
    cursorRow := ov.cursorRow
    cursorCol := ov.cursorCol
  }

private def toBlikuCompletion (cp : ViE.CompletionPopup) : Bliku.Tui.CompletionPopup :=
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

def toModel (state : ViE.EditorState) : Bliku.Tui.Model :=
  let ws := state.getCurrentWorkspace
  let wg := state.getCurrentWorkgroup
  {
    mode := toBlikuMode state.mode
    workgroupName := wg.name
    workspace := {
      name := ws.name
      layout := toBlikuLayout ws.layout
      activeWindowId := ws.activeWindowId
      floatingWindows := ws.floatingWindows
      floatingWindowOffsets := ws.floatingWindowOffsets
    }
    buffers := ws.buffers.toArray.map toBlikuBuffer
    selectionStart := state.selectionStart.map toBlikuCursor
    message := state.message
    commandBuffer := state.inputState.commandBuffer
    floatingOverlay := state.floatingOverlay.map toBlikuOverlay
    completionPopup := state.completionPopup.map toBlikuCompletion
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
  let model' ← Bliku.Tui.render model
  pure (fromModel state model')

end ViE.BlikuAdapter
