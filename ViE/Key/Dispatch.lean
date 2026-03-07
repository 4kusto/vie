-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.State
import ViE.Types
import ViE.Window.Actions
import ViE.Key.Map

namespace ViE.Key

open ViE

def update (config : Config) (state : EditorState) (k : Key) : IO EditorState := do
  let newState ← match state.mode with
  | .normal => config.bindings.normal state k
  | .insert => config.bindings.insert state k
  | .command => config.bindings.command state k
  | .searchForward => ViE.Key.handleSearchInput state k
  | .searchBackward => ViE.Key.handleSearchInput state k
  | .visual => config.bindings.visual state k
  | .visualLine => config.bindings.visual state k
  | .visualBlock => config.bindings.visualBlock state k

  return ViE.Window.enforceScroll newState

end ViE.Key
