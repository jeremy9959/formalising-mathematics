import data.nat.prime
import data.int.gcd
-- open well_founded
set_option trace.eqn_compiler.elim_match true
open nat

def mygcd : nat → nat → nat
| 0        y := y
| (succ x) y := have y % succ x < succ x, 
                from mod_lt y (succ_pos x),
                mygcd (y % succ x) (succ x)




#eval mygcd 120938 1231

#check nat.mod

 



