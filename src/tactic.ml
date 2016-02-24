(* -*- mode: tuareg; fill-column: 79; -*- *)
module Tactic = struct 

  exception TacticFailure of string

  let disch_tac (tms,tm) = 
    let vf a thms =  
      match thms with 
      | [thm] -> Kernel.disch a thm
      | _ -> raise (TacticFailure "disch_tac: expected exactly one theorem.")
    in
    match tm with
    | Kernel.Imp(a,b) -> Prove.Partial ([Prove.Unproved (a::tms,b)],vf a)
    | _ -> raise 
      (TacticFailure "disch_tac: tactic can only be applied to implication.")

  let mp_tac ante (tms,tm) =
    let vf thms = 
      match thms with 
      | [thm1;thm2] -> Kernel.mp thm1 thm2
      | _ -> raise (TacticFailure "mp_tac: expected exactly two theorems.")
    in
    Prove.Partial ([ Prove.Unproved (tms,Kernel.imp ante tm)
                   ; Prove.Unproved (tms,ante)],vf)
      
  let assume_tac (tms,tm) = 
    let vf _ = 
      List.fold_left
        (fun thm tm -> Derived.weaken tm thm) 
        (Kernel.assume tm) 
        tms
    in
    if List.mem tm tms 
    then Prove.Partial ([],vf)
    else raise (TacticFailure "assume_tac: identity not found.")

  let succ_tac (tms,tm) = 
    let vf thms =  
      match thms with 
      | [thm] -> thm
      | _ -> raise (TacticFailure "succ_tac: expected exactly one theorem.")
    in
    Prove.Partial ([Prove.Unproved (tms,tm)],vf)
      
  let fail_tac _ = raise (TacticFailure "fail_tac: applied.")

  let or_tac tac1 tac2 x = 
    try tac1 x with
    | TacticFailure _ -> tac2 x

  let try_tac tac x = 
    try tac x with
    | TacticFailure _ -> succ_tac x
    
end
