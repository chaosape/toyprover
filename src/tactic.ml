(* -*- mode: tuareg; fill-column: 79; -*- *)
module Tactic = struct 
  open Kernel
  open Prove
  open Derived 
  open List

  exception TacticFailure of string
  exception BackchainInvalidIndex

  let found_invalid tacname = 
    failwith (tacname ^ ": BUG - encountered invalid goal tree")

  let tacfail s = raise (TacticFailure s)

  let unproved = function
    | Unproved _ -> true
    | _ -> false

  let to_goal = function
    | Unproved x -> x
    | _ -> failwith "to_goal: BUG - found invalid constructor."


  let disch_tac (tms,tm) = 
    let vf a = function
      | [thm] -> disch a thm
      | _ -> tacfail "disch_tac: expected exactly one theorem."
    in
    match tm with
    | Imp(a,b) -> Subgoals ([Unproved (a::tms,b)],vf a)
    | _ -> tacfail "disch_tac: tactic can only be applied to implication."

  let mp_tac ante (tms,tm) =
    let vf = function 
      | [thm1;thm2] -> mp thm1 thm2
      | _ -> tacfail "mp_tac: expected exactly two theorems."
    in
    Subgoals ([ Unproved (tms,imp ante tm); Unproved (tms,ante)],vf)
      
  let assume_tac (tms,tm) = 
    let id = fold_left
      (fun thm tm -> Derived.weaken tm thm) 
      (assume tm) 
      tms
    in
    if mem tm tms then Subgoals ([],fun _ -> id)
    else tacfail "assume_tac: identity not found."

  let succ_tac goal = Unproved goal 

  let fail_tac _ = tacfail "fail_tac: applied."

  let or_tac tac1 tac2 x = 
    try tac1 x with
    | TacticFailure _ -> tac2 x

  let try_tac tac x = 
    try tac x with
    | TacticFailure _ -> succ_tac x

  let rec on_all tac = function
      | Unproved goal -> tac goal
      | Subgoals (gts,vf)  -> 
        Subgoals (map (fun x -> on_all tac x) gts, vf)
      | x -> x

  let then_tac tac1 tac2 goal = on_all tac2 (tac1 goal)

  let thenL_tac tac1 tacs goal = 
    let aux = function
      | Unproved goal ->
        if length tacs == 1 then (hd tacs) goal
        else tacfail "thenL_tac: incorrect number of tactics."
      | Subgoals (gts,vf)  -> 
        if length tacs == length gts
        then Subgoals (map (fun (t,g) -> on_all t g) (combine tacs gts), vf)
        else tacfail "thenL_tac: incorrect number of tactics."
      | _ -> failwith "then_tac: BUG - found ill-formed subgoals."
    in
    aux (tac1 goal)

  let rec repeat_tac tac goal = try_tac (then_tac tac (repeat_tac tac)) goal

  let backchain_tac ?index:(i=0) (hyps,goal) = 
    let rec vf clause = function
      | thm::[] -> Kernel.mp clause thm
      | thm::thms -> vf (Kernel.mp clause thm) thms
      | [] -> failwith "backchain_tac:vf: BUG - no theorems provided."
    in
    let rec head = function
      | Imp (a,c) -> head c
      | x -> x
    in
    let rec obligations = function
      | Imp (a,c) -> a :: obligations c
      | x -> []
    in
    let heads = List.map (fun x -> (head x,x)) hyps in
    let choices = List.filter (fun (x,y) -> x == goal) heads in
    let obligation_lists = List.map (fun (_,y) -> obligations y,y) choices in 
    let _ = 
      if i >= List.length obligation_lists 
      then raise BackchainInvalidIndex
      else ()
    in
    let obligations,clause = List.nth obligation_lists i in
    let clause = fold_left
      (fun thm tm -> Derived.weaken tm thm) 
      (assume clause) 
      hyps
    in
    Subgoals (List.map (fun x -> Unproved (hyps,x)) obligations,vf clause)

    let search_tac ?maxdepth:(maxdepth=10) goal = 
      let rec aux index depth goal = 
        if depth > maxdepth then 
          tacfail "search_tac:aux: Maximum depth exceeded."
        else
          try 
          then_tac 
            (repeat_tac disch_tac)
            (then_tac
               (repeat_tac assume_tac)
               (then_tac 
                     (backchain_tac ~index:index)
                     (aux 0 (depth+1))
               )
            ) goal
          with
          | TacticFailure _ -> aux (index+1) depth goal
          | BackchainInvalidIndex -> tacfail "search_tac: search failed."
      in
      try_tac (aux 0 0) goal

end
