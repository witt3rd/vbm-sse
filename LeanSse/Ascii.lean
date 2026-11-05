/-! # Writing a byte string in a source file

`ascii "data: x\n"` is the bytes of an ASCII (or any) string literal's code points taken one byte each; for writing examples and vectors, where every character is below 128. -/

namespace LeanSse

/-- The bytes of a string whose characters are all ASCII: one byte per character. -/
def ascii (s : String) : List UInt8 := s.toList.map fun c => c.toNat.toUInt8

end LeanSse
