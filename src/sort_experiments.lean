import data.list.pairwise
namespace list

def stinsert  : ℕ → list ℕ → list ℕ 
| a  [] := [a]
| a  (b::l) := if a ≥  b then a::b::l else b::(stinsert a l)

def srt : list ℕ → list ℕ 
| [] := []
| (a::l) := stinsert a (srt l)



end list