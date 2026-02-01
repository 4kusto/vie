import ViE.Types
import ViE.Buffer

namespace ViE.Window

open ViE

def getAllWindowBounds (l : Layout) (h w : Nat) : List (Nat × Nat × Nat × Nat × Nat) :=
  let rec traverse (l : Layout) (r c h w : Nat) (acc : List (Nat × Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat × Nat × Nat) :=
    match l with
    | Layout.window id _ => (id, r, c, h, w) :: acc
    | Layout.hsplit left right ratio =>
      let leftW := (Float.ofNat w * ratio).toUInt64.toNat
      let acc' := traverse left r c h leftW acc
      traverse right r (c + leftW + 1) h (if w > leftW then w - leftW - 1 else 0) acc'
    | Layout.vsplit top bottom ratio =>
      let topH := (Float.ofNat h * ratio).toUInt64.toNat
      let acc' := traverse top r c topH w acc
      traverse bottom (r + topH + 1) c (if h > topH then h - topH - 1 else 0) w acc'
  traverse l 0 0 h w []

def getWindowIds (l : Layout) : List Nat :=
  match l with
  | Layout.window id _ => [id]
  | Layout.hsplit left right _ => getWindowIds left ++ getWindowIds right
  | Layout.vsplit top bottom _ => getWindowIds top ++ getWindowIds bottom
