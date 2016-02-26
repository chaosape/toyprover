(* -*- mode: tuareg; fill-column: 79; -*- *)
module Tactic = struct 
  open Kernel
  open Prove
  open Derived 
  open List

  exception TacticFailure of string

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

  let succ_tac (tms,tm) = 
    let vf = function
      | [thm] -> thm
      | _ -> tacfail "succ_tac: expected exactly one theorem."
    in
    Subgoals ([Unproved (tms,tm)],vf)
      
  let fail_tac _ = tacfail "fail_tac: applied."

  let or_tac tac1 tac2 x = 
    try tac1 x with
    | TacticFailure _ -> tac2 x

  let try_tac tac x = 
    try tac x with
    | TacticFailure _ -> succ_tac x

  let then_tac tac1 tac2 goal = 
    let aux = function
      | Unproved goal -> tac2 goal
      | Subgoals (gts,vf) when for_all unproved gts -> 
        Subgoals (map (fun x -> tac2 (to_goal x)) gts, vf)
      | _ -> failwith "then_tac: BUG - found ill-formed subgoals."
    in
    aux (tac1 goal)

  let thenL_tac tac1 tacs goal = 
    let aux = function
      | Unproved goal ->
        if length tacs == 1 then (hd tacs) goal
        else tacfail "thenL_tac: incorrect number of tactics."
      | Subgoals (gts,vf) when for_all unproved gts -> 
        if length tacs == length gts
        then Subgoals (map (fun (t,g) -> t (to_goal g)) (combine tacs gts), vf)
        else tacfail "thenL_tac: incorrect number of tactics."
      | _ -> failwith "then_tac: BUG - found ill-formed subgoals."
    in
    aux (tac1 goal)
  
  let repeat_tac tac goal =
    let rec list_aux = function
      | [] -> tacfail "repeat_tac:list_aux: Tactic could not be applied."
      | gt::gts -> 
        begin
          try (tree_aux gt)::gts with
          | TacticFailure _ -> gt::(list_aux gts)
        end
    and tree_aux = function
      | Unproved goal -> tac goal
      | Subgoals (goals,vf) -> Subgoals (list_aux goals,vf)
      | Invalid -> found_invalid "repeat_tac:tree_aux"
      |  _ -> tacfail "repeat_tac:list_aux: Tactic could not be applied."
    in
    let rec repeat gt = 
      try repeat (tree_aux gt) with
      | TacticFailure _ -> gt
    in
    repeat (succ_tac goal)

      

end
