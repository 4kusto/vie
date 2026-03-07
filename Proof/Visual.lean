-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE.State.Visual
import ViE.State.Config

namespace Proof

open ViE

theorem startVisualMode_setsMode (s : EditorState) :
    (s.startVisualMode).mode = .visual := by
  simp [ViE.EditorState.startVisualMode]

theorem startVisualMode_setsSelectionStart (s : EditorState) :
    (s.startVisualMode).selectionStart = some (s.clampCursor.getCursor) := by
  simp [ViE.EditorState.startVisualMode]

theorem startVisualLineMode_setsMode (s : EditorState) :
    (s.startVisualLineMode).mode = .visualLine := by
  simp [ViE.EditorState.startVisualLineMode]

theorem startVisualLineMode_setsSelectionStart (s : EditorState) :
    (s.startVisualLineMode).selectionStart = some (s.clampCursor.getCursor) := by
  simp [ViE.EditorState.startVisualLineMode]

theorem startVisualBlockMode_setsMode (s : EditorState) :
    (s.startVisualBlockMode).mode = .visualBlock := by
  simp [ViE.EditorState.startVisualBlockMode]

theorem startVisualBlockMode_setsSelectionStart (s : EditorState) :
    (s.startVisualBlockMode).selectionStart = some (s.clampCursor.getCursor) := by
  simp [ViE.EditorState.startVisualBlockMode]

theorem exitVisualMode_clearsSelectionStart (s : EditorState) :
    (s.exitVisualMode).selectionStart = none := by
  simp [ViE.EditorState.exitVisualMode]

theorem exitVisualMode_setsNormalMode (s : EditorState) :
    (s.exitVisualMode).mode = .normal := by
  simp [ViE.EditorState.exitVisualMode]

theorem exitVisualMode_clearsMessage (s : EditorState) :
    (s.exitVisualMode).message = "" := by
  simp [ViE.EditorState.exitVisualMode]

theorem defaultConfig_explorerPreviewSplitRatio_nonnegative :
    0.0 <= ViE.defaultConfig.explorerPreviewSplitRatio := by
  native_decide

theorem defaultConfig_explorerPreviewSplitRatio_atMostOne :
    ViE.defaultConfig.explorerPreviewSplitRatio <= 1.0 := by
  native_decide

end Proof
