import data.list.basic
import data.int.basic

-- following this outline from: https://www.geeksforgeeks.org/stack-set-4-evaluation-postfix-expression/
-- 1) Create a stack to store operands (or values).
-- 2) Scan the given expression and do the following for every scanned element.
-- …..a) If the element is a number, push it into the stack
-- …..b) If the element is an operator, pop operands for the operator from the stack. Evaluate the operator and push the result back to the stack
-- 3) When the expression is ended, the number in the stack is the final answer

-- this is a language of tokenised terms we will use, we do this because pattern matching on strings
-- isn't so nice in lean (roughly because strings are list of characters, which are given by nats
-- representing their ascii numeral)
inductive postfix_lang
| add : postfix_lang
| sub : postfix_lang
| mul : postfix_lang
| nat (n : ℤ) : postfix_lang

open postfix_lang

-- now we can make elements of this type like so
#check postfix_lang.add
#check postfix_lang.sub
#check postfix_lang.nat 2
-- every element is either one of these symbols or a natural number

-- converts a string token, either + - or * into the postfix lang
def of_string : string → postfix_lang
| "+" := add
| "-" := sub
| "*" := mul
| s   := nat (string.to_nat s) -- anything that doesn't match the above gets converted to a nat

-- the core of the algorithm, a recursive function that takes a list of tokens and stack of integers
-- so far and returns the new stack
def eval_postfix_aux : list postfix_lang → list ℤ → list ℤ
-- the next token is an add so we take the first two elements of the stack, add them and put it
-- back on the rest of the stack, and recurse with the remaining tokens and that stack
| (add :: r) (a :: b :: s) := eval_postfix_aux r ((b + a) :: s)
| (sub :: r) (a :: b :: s) := eval_postfix_aux r ((b - a) :: s)
| (mul :: r) (a :: b :: s) := eval_postfix_aux r ((b * a) :: s)
-- the next token is the natural number `n` so we put `n` on the stack (it is implicitly converted
-- to an integer)
| (nat n :: r) s := eval_postfix_aux r (n :: s)
| [] s := s -- if there are no operations left stop recursing and return the stack as is
| _ _ := [] -- if we see anything else there is probably a mistake

-- we can call this directly on a list of postfix_langs like so
#eval eval_postfix_aux [nat 2, nat 3, nat 1, mul, add, nat 9, sub] []
#eval eval_postfix_aux [nat 2, nat 3, nat 1, mul, add, nat 9, sub] [1] -- starting with a nonempty stack
#eval eval_postfix_aux [nat 2, nat 3, nat 1, mul, add, nat 9, sub, sub] [] -- nonsense case

-- but you asked for a function from strings to evaluations, we can do this like so:
-- call the above algorithm on a string by tokenising, running eval_postfix_aux and then taking the
-- head of the resulting list
def eval_postfix (s : string) : ℤ := (eval_postfix_aux ((s.split_on ' ').map of_string) []).head

#eval eval_postfix "2 3 1 * + 9 -"
#eval eval_postfix "2 3 1 * + 9 - 7 +"

-- we get zero if we do nonesense
#eval eval_postfix "2 3 1 * + 9 - - - -"
