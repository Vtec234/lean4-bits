/-! String encoding and manipulation utilities. -/

def hexdigits : Array Char :=
  #[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f' ]

def enhexByte (x : UInt8) : String :=
  ⟨[ hexdigits.get! $ UInt8.toNat $ (x.land 0xf0).shiftRight 4,
     hexdigits.get! $ UInt8.toNat $ x.land 0xf ]⟩

def enhex : List UInt8 → String
  | [] => ""
  | b::bs => enhexByte b ++ enhex bs

def isHex (c : Char) : Bool :=
  (c ≥ '0' && c ≤ '9')
  || (c ≥ 'A' && c ≤ 'F')
  || (c ≥ 'a' && c ≤ 'f')

def unhexChar (c : Char) : UInt8 :=
  UInt32.toUInt8 $ if c ≤ '9' then
    c.val - ('0').val
  else if c ≤ '8' then
    10 + (c.val - ('A').val)
  else
    10 + (c.val - ('a').val)

def unhexTwo (hi : Char) (lo : Char) : Option UInt8 :=
  if isHex hi && isHex lo then
    some (16*(unhexChar hi) + unhexChar lo)
  else
    none

def unhexAux : List Char → Option (List UInt8)
  | [] => some []
  | a::b::xs => OptionM.run do
    let n ← unhexTwo a b
    let ns ← unhexAux xs
    pure (n :: ns)
  | a::xs => none -- this matches the behaviour of binascii.hexlify which fails

def unhexOpt (s : String) : Option (List UInt8) :=
  unhexAux s.data

def unhex (s : String) : List UInt8 :=
  (unhexOpt s).get!

-- https://rosettacode.org/wiki/Base64_encode_data#Haskell
def alphaTable : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".data.toArray

def u : List UInt8 -> Nat
  | [a, b, c] =>
    let a := a.toNat
    let b := b.toNat
    let c := c.toNat
    (a.shiftLeft 16).lor $ (b.shiftLeft 8).lor c
  | [a, b] =>
    let a := a.toNat
    let b := b.toNat
    (a.shiftLeft 16).lor $ b.shiftLeft 8
  | [a] => (a.toNat).shiftLeft 16
  | _ => 0

partial def b64EncodeAux : List UInt8 → List Char
  | [] => []
  | xs =>
    let chunk := xs.take 3
    let _u := u chunk
    [ alphaTable.get! $ _u.shiftRight 18,
      alphaTable.get! $ (_u.shiftRight 12).land 63,
      if chunk.length < 2 then '='
      else alphaTable.get! $ (_u.shiftRight 6).land 63,
      if chunk.length < 3 then '='
      else alphaTable.get! $ _u.land 63 ] ++ (b64EncodeAux (xs.drop 3))

def b64Encode (bs : List UInt8) : String :=
  ⟨b64EncodeAux bs⟩

def hex2b64 (s : String):  Option String :=
  b64Encode <$> unhexOpt s

def cryptopals1 : Option String :=
  hex2b64 "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d"

#eval cryptopals1

def xorList (a b : List UInt8) : List UInt8 :=
  List.zipWith UInt8.xor a b

def decAscii (cs : List UInt8) : String :=
  ⟨cs.map (λ c => Char.ofNat c.toNat)⟩
def encAscii (s : String) : List UInt8 :=
  s.data.map (λ c => UInt32.toUInt8 c.val)

def xorHexStrs (a b : String) : String :=
  decAscii $ xorList (unhex a) (unhex b)

def cryptopals2 : String :=
  xorHexStrs "1c0111001f010100061a024b53535009181c" "686974207468652062756c6c277320657965"

#eval cryptopals2

-- English alphabet ordered by frequency of appearance
def freqAlpha :=
  "etaoinshrdlcumwfgypbvkjxqzETAOINSHRDLCUMWFGYPBVKJXQZ"
def freqScore (c : UInt8) :=
  if (0x41 ≤ c ∧ c ≤ 0x5a) ∨ (0x61 ≤ c ∧ c ≤ 0x7a)
  then freqAlpha.bsize - freqAlpha.posOf (Char.ofNat (UInt8.toNat c))
  else 0

-- Return the string for which total score is maximised when xor'd with a byte in range(256)
def cryptopals3 (s : String) : UInt8 :=
  let bs := encAscii s
  let scores := List.iota 256 |>.map fun n =>
    let n := UInt8.ofNat n
    let score := bs.foldl (init := 0) fun acc b => acc + freqScore (b ^^^ n)
    (n, score)
  scores.toArray.getMax? (fun a b => a.1 < b.1) |>.get! |>.fst