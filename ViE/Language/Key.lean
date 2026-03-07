-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.Language.Lean.Key

namespace ViE.Language.Key

open ViE

def handleInsertKey? (state : EditorState) (k : Key) : IO (Option EditorState) :=
  ViE.Language.Lean.Key.handleInsertKey? state k

end ViE.Language.Key
