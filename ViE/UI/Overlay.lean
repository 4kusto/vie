import ViE.UI.Primitives
import ViE.Terminal
import ViE.Color

namespace ViE.UI
open ViE

def shouldRenderMessageAsFloat (msg : String) : Bool :=
  let m := msg.trimAscii.toString
  if m.isEmpty then
    false
  else
    m.startsWith "Error" ||
    m.startsWith "Cannot" ||
    m.startsWith "Invalid" ||
    m.startsWith "Unknown" ||
    m.startsWith "No " ||
    m.startsWith "Empty " ||
    m.startsWith "Usage:" ||
    m.startsWith "failed" ||
    m.startsWith "Failed" ||
    m.contains "not found"

def renderStatusBar (state : EditorState) : String :=
  let plainMessage := state.message.trimAscii.toString
  let floatMessage := shouldRenderMessageAsFloat plainMessage
  if state.mode == .command then
    s!":{state.inputState.commandBuffer}"
  else if state.mode == .searchForward then
    s!"/{state.inputState.commandBuffer}"
  else if state.mode == .searchBackward then
    s!"?{state.inputState.commandBuffer}"
  else if floatMessage then
    ""
  else
    plainMessage

def messageOverlayForState (state : EditorState) : Option FloatingOverlay :=
  let plainMessage := state.message.trimAscii.toString
  let floatMessage := shouldRenderMessageAsFloat plainMessage
  if state.floatingOverlay.isNone &&
      state.mode != .command &&
      state.mode != .searchForward &&
      state.mode != .searchBackward &&
      floatMessage then
    if plainMessage.isEmpty then
      none
    else
      some {
        title := "Message"
        lines := (plainMessage.splitOn "\n").toArray
        maxWidth := 0
        cursorRow := 0
        cursorCol := 0
      }
  else
    none

structure FloatingOverlayLayout where
  top : Nat
  left : Nat
  innerWidth : Nat
  titleRows : Nat
  contentRows : Nat
  deriving Inhabited

def computeFloatingOverlayLayout (rows cols : Nat) (tabStop : Nat) (overlay : FloatingOverlay) : Option FloatingOverlayLayout := Id.run do
  let availableRows := if rows > 1 then rows - 1 else rows
  if cols < 8 || availableRows < 4 then
    return none

  let lines := if overlay.lines.isEmpty then #[""] else overlay.lines
  let titleText := if overlay.title.isEmpty then "" else s!"[{overlay.title}]"
  let titleRows := if titleText.isEmpty then 0 else 1

  let naturalWidthContent := lines.foldl (fun acc ln => max acc (Unicode.stringWidthWithTabStop ln tabStop)) 0
  let naturalWidth := max naturalWidthContent (Unicode.stringWidthWithTabStop titleText tabStop)
  let maxInnerWidth := if cols > 8 then cols - 8 else 1
  let targetWidth :=
    if overlay.maxWidth > 0 then
      overlay.maxWidth
    else
      naturalWidth
  let innerWidth := max 1 (min targetWidth maxInnerWidth)

  let maxContentRows :=
    if availableRows > titleRows + 2 then
      availableRows - titleRows - 2
    else
      0
  if maxContentRows == 0 then
    return none
  let naturalRows := lines.size
  let targetRows := naturalRows
  let contentRows := max 1 (min targetRows maxContentRows)
  let boxHeight := contentRows + titleRows + 2
  let boxWidth := innerWidth + 4
  let top := (availableRows - boxHeight) / 2
  let left := (cols - boxWidth) / 2
  return some {
    top := top
    left := left
    innerWidth := innerWidth
    titleRows := titleRows
    contentRows := contentRows
  }

def renderFloatingOverlay (rows cols : Nat) (tabStop : Nat) (overlay : FloatingOverlay) : Array String := Id.run do
  let some layout := computeFloatingOverlayLayout rows cols tabStop overlay | return #[]
  let lines := if overlay.lines.isEmpty then #[""] else overlay.lines
  let titleText := if overlay.title.isEmpty then "" else s!"[{overlay.title}]"
  let top := layout.top
  let left := layout.left
  let innerWidth := layout.innerWidth
  let titleRows := layout.titleRows
  let contentRows := layout.contentRows
  let border := "+" ++ "".pushn '-' (innerWidth + 2) ++ "+"
  let style := (ViE.Color.toBg .brightBlack) ++ (ViE.Color.toFg .white)

  let mut out : Array String := #[]
  out := out.push (Terminal.moveCursorStr top left)
  out := out.push style
  out := out.push border

  if titleRows == 1 then
    out := out.push (Terminal.moveCursorStr (top + 1) left)
    let clippedTitle := Unicode.takeByDisplayWidthWithTabStop titleText.toRawSubstring tabStop innerWidth
    let titleW := Unicode.stringWidthWithTabStop clippedTitle tabStop
    let titlePad := if titleW < innerWidth then "".pushn ' ' (innerWidth - titleW) else ""
    out := out.push s!"| {clippedTitle}{titlePad} |"

  for i in [0:contentRows] do
    let raw := lines[i]?.getD ""
    let clipped := Unicode.takeByDisplayWidthWithTabStop raw.toRawSubstring tabStop innerWidth
    let clippedW := Unicode.stringWidthWithTabStop clipped tabStop
    let pad := if clippedW < innerWidth then "".pushn ' ' (innerWidth - clippedW) else ""
    let row := top + 1 + titleRows + i
    out := out.push (Terminal.moveCursorStr row left)
    out := out.push s!"| {clipped}{pad} |"

  let bottom := top + contentRows + titleRows + 1
  out := out.push (Terminal.moveCursorStr bottom left)
  out := out.push border
  out := out.push ViE.Color.reset
  return out

private def repeatStr (s : String) (n : Nat) : String :=
  Id.run do
    let mut out := ""
    for _ in [0:n] do
      out := out ++ s
    return out

def renderCompletionPopup (rows cols : Nat) (state : EditorState) (cursorPos : Option (Nat × Nat)) : Array String := Id.run do
  let some popup := state.completionPopup | return #[]
  let some (cursorRow, cursorCol) := cursorPos | return #[]
  if popup.items.isEmpty then
    return #[]
  let availableRows := if rows > 1 then rows - 1 else rows
  if availableRows < 4 || cols < 8 then
    return #[]

  let visibleMax := min 8 popup.items.size
  let labels := popup.items.extract 0 visibleMax |>.map (fun it => it.label)
  let naturalW := labels.foldl (fun acc s => max acc (ViE.Unicode.stringWidthWithTabStop s state.config.tabStop)) 0
  let innerWidth := max 8 (min 48 naturalW)
  let boxWidth := innerWidth + 2
  let boxHeight := visibleMax + 2

  let placeBelow := cursorRow + 1 + boxHeight <= availableRows
  let top :=
    if placeBelow then
      cursorRow + 1
    else if cursorRow >= boxHeight then
      cursorRow - boxHeight
    else
      0
  let left0 := cursorCol
  let left := if left0 + boxWidth < cols then left0 else cols - boxWidth

  let hline := repeatStr state.config.hSplitStr innerWidth
  let borderTop := state.config.vSplitStr ++ hline ++ state.config.vSplitStr
  let borderBottom := borderTop

  let mut out : Array String := #[]
  out := out.push (Terminal.moveCursorStr top left)
  out := out.push borderTop

  let selected := if popup.selected < visibleMax then popup.selected else 0
  for i in [0:visibleMax] do
    let label := labels[i]!
    let clipped := ViE.Unicode.takeByDisplayWidthWithTabStop label.toRawSubstring state.config.tabStop innerWidth
    let clippedW := ViE.Unicode.stringWidthWithTabStop clipped state.config.tabStop
    let pad := if clippedW < innerWidth then "".pushn ' ' (innerWidth - clippedW) else ""
    let row := top + 1 + i
    out := out.push (Terminal.moveCursorStr row left)
    out := out.push state.config.vSplitStr
    if i == selected then
      out := out.push state.config.searchHighlightCursorStyle
      out := out.push clipped
      out := out.push pad
      out := out.push state.config.resetStyle
    else
      out := out.push clipped
      out := out.push pad
    out := out.push state.config.vSplitStr

  out := out.push (Terminal.moveCursorStr (top + boxHeight - 1) left)
  out := out.push borderBottom
  return out

end ViE.UI
