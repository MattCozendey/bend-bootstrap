import bendtt

-- Bytes
-- =====
--
-- AGENTS.md 3.1.3's list of bytes, as `bend -o` writes a value of Base's
-- List<&2, Word(8n)>: a constructor k{x, y} is the tuple (.k, x, y, ()) at
-- quantity 1, and a byte is its Word(8n), the lowest bit first.

open Quan Term

-- the constructor k with the fields fs
def ctor (k : String) (fs : List Term) : Term :=
  Tup Q1 (Lab k) (fs.foldr (Tup Q1) (Lab "()"))

-- the Word(n) of v
def bits : Nat → Nat → Term
  | 0, _ => ctor "WNil" []
  | n + 1, v => ctor "WCon" [ctor (if v % 2 = 1 then "True" else "False") [], bits n (v / 2)]

-- a list, as Base's List
def list : List Term → Term
  | [] => ctor "Nil" []
  | x :: xs => ctor "Con" [x, list xs]

def byte (b : UInt8) : Term := bits 8 b.toNat

-- Sharing
-- -------
-- A byte is 67 nodes, and a list of bytes holds one for each byte. Compiled
-- code takes each byte from byteTable, made once (byte_byteS), so equal bytes
-- are one term in memory: the terms are the same, only their copies change.
-- The machine shares the bytes that it builds the same way (Machine.share).

-- the 256 bytes
def byteTable : Array Term := Array.ofFn fun (i : Fin 256) => byte i.val.toUInt8

theorem byteTable_size : byteTable.size = 256 := Array.size_ofFn

-- byte, from byteTable
def byteS (b : UInt8) : Term := byteTable[b.toNat]'(by rw [byteTable_size]; exact b.toNat_lt)

@[csimp] theorem byte_byteS : @byte = @byteS := by
  funext b
  simp [byteS, byteTable]

def bytes (bs : List UInt8) : Term := list (bs.map byte)

-- the value of a Word(n)
def unbits : Nat → Term → Option Nat
  | 0, Tup Q1 (Lab "WNil") (Lab "()") => some 0
  | n + 1, Tup Q1 (Lab "WCon") (Tup Q1 (Tup Q1 (Lab b) (Lab "()")) (Tup Q1 w (Lab "()"))) =>
    if b = "True" then (unbits n w).map (2 * · + 1)
    else if b = "False" then (unbits n w).map (2 * ·)
    else none
  | _, _ => none

def unbytes : Term → Option (List UInt8)
  | Tup Q1 (Lab "Nil") (Lab "()") => some []
  | Tup Q1 (Lab "Con") (Tup Q1 w (Tup Q1 t (Lab "()"))) =>
    match unbits 8 w, unbytes t with
    | some v, some bs => some (v.toUInt8 :: bs)
    | _, _ => none
  | _ => none

-- a word reads back as its value modulo 2 ^ n
theorem unbits_bits : unbits n (bits n v) = some (v % 2 ^ n) := by
  induction n generalizing v with
  | zero => simp [bits, ctor, unbits, Nat.mod_one]
  | succ n ih =>
    have h : v % 2 ^ (n + 1) = v % 2 + 2 * (v / 2 % 2 ^ n) := by
      rw [Nat.pow_succ', Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one v with hv | hv <;>
      simp [bits, ctor, unbits, ih, h, hv] <;> omega

-- the bytes come back from their term
theorem unbytes_bytes : unbytes (bytes i) = some i := by
  induction i with
  | nil => simp [bytes, list, ctor, unbytes]
  | cons b bs ih =>
    have h : b.toNat % 2 ^ 8 = b.toNat := Nat.mod_eq_of_lt b.toNat_lt
    simp only [bytes] at ih
    simp [bytes, list, byte, ctor, unbytes, unbits_bits, h, ih]
