# the bytes in order: a merge sort of Base, with a closed template argument
import Base

def le(a: Word(8n), b: Word(8n)) -> Bool:
  Cmp.is_le(Word.cmp(8n, a, b))

def main(i: List<&2, Word(8n)>) -> List<&2, Word(8n)>:
  List.sort(~Word(8n), ~le, i)
