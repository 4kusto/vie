import ViE.Buffer.LowIO
import ViE.State.Config
import ViE.State.Layout
import Test.Utils

namespace Test.PreviewData

open Test.Utils

def basePath : String := "Test/test_paths"

def testFiles : List String := [
  s!"{basePath}/file0.txt",
  s!"{basePath}/dir0/file0.txt",
  s!"{basePath}/dir0/file1.txt",
  s!"{basePath}/dir0/file2.txt",
  s!"{basePath}/dir0/file3.txt",
  s!"{basePath}/dir0/dir0/file0.txt",
  s!"{basePath}/dir0/dir1/file1.txt",
  s!"{basePath}/dir0/dir1/file2.txt",
  s!"{basePath}/dir0/dir1/file3.txt",
  s!"{basePath}/dir0/dir1/file4.txt",
  s!"{basePath}/dir0/dir1/file5.txt"
]

def test : IO Unit := do
  IO.println "Starting Preview Data Test..."

  for path in testFiles do
    let buf ← ViE.loadBufferByteArray path
    let content := buf.table.toString
    let byteLen := content.toUTF8.size
    assertEqual s!"{path} has content" true (content.length > 0)
    assertEqual s!"{path} has bytes" true (byteLen > 0)
    assertEqual s!"{path} has lines" true (buf.lineCount > 0)

    let firstLine := ViE.getLineFromBuffer buf 0 |>.getD ""
    assertEqual s!"{path} has first line" true (firstLine.length > 0)

  IO.println "PreviewDataTest passed!"

end Test.PreviewData
