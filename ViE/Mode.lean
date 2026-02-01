namespace ViE

inductive Mode where
  | normal
  | insert
  | command
  | visual
  | visualBlock
  deriving Repr, BEq, Inhabited

instance : ToString Mode where
  toString
    | .normal => "NORMAL"
    | .insert => "INSERT"
    | .command => "COMMAND"
    | .visual => "VISUAL"
    | .visualBlock => "VISUAL BLOCK"

end ViE
