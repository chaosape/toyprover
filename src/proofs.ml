(* -*- mode: tuareg; fill-column: 79; -*- *)
let av = Kernel.var "a"
let bv = Kernel.var "b"
let cv = Kernel.var "c"
 
(* Theorem impcom = (a -> b -> c) -> b -> a -> c *)
(* fm1 = a -> b -> c) *) 
let fm1 = Kernel.imp av (Kernel.imp bv cv)
(* fm2 = b -> a -> c *)
let fm2 = Kernel.imp bv (Kernel.imp av cv)
(* fm3 = b -> c *)
let fm3 = Kernel.imp bv cv 
let impcom = 
  begin
    Prove.theorem [] (Kernel.imp fm1 fm2);
    Prove.apply (Tactic.disch_tac);
    Prove.apply (Tactic.disch_tac);
    Prove.apply (Tactic.disch_tac);
    Prove.apply (Tactic.mp_tac bv);
    Prove.apply (Tactic.mp_tac av);
    Prove.apply (Tactic.assume_tac);
    Prove.apply (Tactic.assume_tac);
    Prove.apply (Tactic.assume_tac);
    Prove.qed ()
  end    
