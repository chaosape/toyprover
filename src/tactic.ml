(* -*- mode: tuareg; fill-column: 79; -*- *)
module Tactic = struct 

  let disch_tac (tms,tm) = 
    let vf a thms =  
      match thms with 
      | [thm] -> Kernel.disch a thm
      | _ -> failwith "disch_tac: expected exactly one theorem."
    in
    match tm with
    | Kernel.Imp(a,b) -> ([a::tms,b],vf a)
    | _ -> failwith "disch_tac: tactic can only be applied to implication."

  let mp_tac imp (tms,tm) =
    let vf thms = 
      match thms with 
      | [thm1;thm2] -> Kernel.mp thm1 thm2
      | _ -> failwith "mp_tac: expected exactly two theorems."
    in
    match imp with
    | Kernel.Imp (a,b) -> 
      if b = tm then ([(tms,imp);(tms,a)],vf)
      else failwith "mp_tac: antecedent of implication does not match with other goal." 
    | _ -> failwith "mp_tac: tactic can only be applied to implication."

      
  let assume_tac (tms,tm) = 
    if List.mem tm tms 
    then ([],fun _ -> List.fold_left (fun thm tm -> Derived.weaken tm thm) (Kernel.assume tm) tms)
    else failwith "assume_tac: identity not found."
end
