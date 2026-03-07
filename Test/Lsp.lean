-- SPDX-FileCopyrightText: 2026 Yuki Otsuka
--
-- SPDX-License-Identifier: BSD-3

import ViE
import Test.Utils

namespace Test.Lsp

open Test.Utils

def test : IO Unit := do
  IO.println "Starting LSP Test..."

  let leanBuf := { ViE.initialBuffer with filename := some "Main.lean" }
  let txtBuf := { ViE.initialBuffer with filename := some "notes.txt" }
  assertEqual "isLeanBuffer true for .lean" true (ViE.Lsp.Lean.isLeanBuffer leanBuf)
  assertEqual "isLeanBuffer false for non-.lean" false (ViE.Lsp.Lean.isLeanBuffer txtBuf)

  let uriAbs := ViE.Lsp.Lean.fileUri "/tmp/a b#c%.lean"
  assertEqual "fileUri percent-encodes reserved bytes" "file:///tmp/a%20b%23c%25.lean" uriAbs

  let uriRel := ViE.Lsp.Lean.fileUri "tmp/test.lean"
  assertEqual "fileUri normalizes relative path with leading slash" "file:///tmp/test.lean" uriRel
  let uriWs ← ViE.Lsp.Lean.fileUriWithWorkspace (some "/tmp/ws") "dir/a b.lean"
  assertEqual "fileUriWithWorkspace resolves relative path from workspace root" "file:///tmp/ws/dir/a%20b.lean" uriWs
  let uriWsAbs ← ViE.Lsp.Lean.fileUriWithWorkspace (some "/tmp/ws") "/tmp/alt/x.lean"
  assertEqual "fileUriWithWorkspace keeps absolute path priority" "file:///tmp/alt/x.lean" uriWsAbs

  let okResp : Lean.Json := Lean.Json.mkObj [("id", (12 : Lean.Json)), ("result", Lean.Json.null)]
  let errResp : Lean.Json := Lean.Json.mkObj [("id", (13 : Lean.Json)), ("error", Lean.Json.mkObj [("code", (1 : Lean.Json))])]
  let notif : Lean.Json := Lean.Json.mkObj [("method", .str "textDocument/publishDiagnostics"), ("params", Lean.Json.mkObj [])]

  assertEqual "responseId? parses result response id" (some 12) (ViE.Lsp.Lean.responseId? okResp)
  assertEqual "responseId? parses error response id" (some 13) (ViE.Lsp.Lean.responseId? errResp)
  assertEqual "responseId? is none for notifications" (none : Option Nat) (ViE.Lsp.Lean.responseId? notif)
  assertEqual "isResponseForRequest true for same id" true (ViE.Lsp.Lean.isResponseForRequest okResp 12)
  assertEqual "isResponseForRequest false for different id" false (ViE.Lsp.Lean.isResponseForRequest okResp 99)

  let s0 := ViE.initialState
  let sStatus ← ViE.Lsp.Lean.cmdLsp ["status"] s0
  assertEqual "lsp status reports stopped when no session" "LSP: stopped" sStatus.message
  let sStop ← ViE.Lsp.Lean.cmdLsp ["stop"] s0
  assertEqual "lsp stop reports not running when no session" "LSP is not running" sStop.message

  IO.println "LSP Test passed!"

end Test.Lsp
