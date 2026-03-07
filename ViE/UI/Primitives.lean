-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.State
import ViE.Unicode
import Bliku.Tui.Primitives

namespace ViE.UI
open ViE

abbrev leftPad := Bliku.Tui.leftPad
abbrev Rect := Bliku.Tui.Rect

def getWorkspaceBuffer (st : EditorState) (id : Nat) : FileBuffer :=
  let ws := st.getCurrentWorkspace
  ws.buffers.find? (fun b => b.id == id) |>.getD initialFileBuffer

end ViE.UI
