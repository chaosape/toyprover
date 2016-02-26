(* -*- mode: tuareg; fill-column: 79; -*- *)
let av = var "a"
let bv = var "b"
let cv = var "c"
 
(* Theorem impcom = (a -> b -> c) -> b -> a -> c *)
(* fm1 = a -> b -> c) *) 
let fm1 = imp av (imp bv cv)
(* fm2 = b -> a -> c *)
let fm2 = imp bv (imp av cv)
(* fm3 = b -> c *)
let fm3 = imp bv cv 
let impcom = 
  begin
    theorem [] (imp fm1 fm2);
    apply (repeat_tac disch_tac);
    apply (thenL_tac 
             (mp_tac bv) 
             [ then_tac 
                 (mp_tac av)
                 assume_tac 
             ; assume_tac]);
    qed ()
  end 

(* Theorem imptrans = (a -> b) -> (b -> c) -> a -> c *)
(* fm1 = a -> b *)
let fm1 = imp av bv
(* fm2 = b -> c *)
let fm2 = imp bv cv
(* fm3 = a -> c *)
let fm3 = imp av cv
let imptrans = 
  begin
    theorem [] (imp fm1 (imp fm2 fm3));
    apply (repeat_tac disch_tac);
    apply (thenL_tac 
             (mp_tac bv)
             [ assume_tac
             ; then_tac (mp_tac av) (repeat_tac assume_tac) ]);
      qed ()
  end

(* Theorem scomb = (a -> b -> c) -> (a -> b) -> a -> c *)
(* fm1 = a -> b -> c) *) 
let fm1 = imp av (imp bv cv)
(* fm2 = a -> b *)
let fm2 = imp av bv
(* fm3 = a -> c *)
let fm3 = imp av cv
let scomb = 
  begin
    theorem [] (imp fm1 (imp fm2 fm3));
    apply (repeat_tac disch_tac);
    apply (thenL_tac 
             (mp_tac bv)
             [ then_tac (mp_tac av) (repeat_tac assume_tac)
             ; then_tac (mp_tac av) (repeat_tac assume_tac) ]);
      qed ()
  end

(* Theorem wcomb = (a -> a -> b) -> (a -> b) *)
(* fm1 = a -> b *)
let fm1 = imp av bv
(* fm2 = a -> a -> b) *) 
let fm2 = imp av fm1
let wcomb = 
  begin
    theorem [] (imp fm2 fm1);
    apply (repeat_tac disch_tac);
    apply (thenL_tac 
             (mp_tac av)
             [ then_tac (mp_tac av) (repeat_tac assume_tac)
             ; assume_tac ]);
    qed ()
  end
