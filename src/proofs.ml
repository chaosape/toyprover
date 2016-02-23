(* -*- mode: tuareg; fill-column: 79; -*- *)
let av = Kernel.Var "a"
let bv = Kernel.Var "b"
let cv = Kernel.Var "c"

let mk_imp a b = Kernel.Imp (a,b)

(* PROOF: (a -> b -> c) -> b -> a -> c *)

(* fm1 = a -> b -> c) *) 
let fm1 = mk_imp av (mk_imp bv cv)
(* fm2 = b -> a -> c *)
let fm2 = mk_imp bv (mk_imp av cv)
(* fm3 = b -> c *)
let fm3 = mk_imp bv cv 
(* lem1 =  av, bv, fm1 |- fm3 *)
let _ = Prove.theorem [] (mk_imp fm1 fm2)
let _ = Prove.apply (Tactic.disch_tac)
let _ = Prove.apply (Tactic.disch_tac)
let _ = Prove.apply (Tactic.disch_tac)
let _ = Prove.apply (Tactic.mp_tac fm3)
let _ = Prove.apply (Tactic.mp_tac fm1)
let _ = Prove.apply (Tactic.assume_tac)
let _ = Prove.apply (Tactic.assume_tac)
let _ = Prove.apply (Tactic.assume_tac)
let thm = Prove.qed ();;
