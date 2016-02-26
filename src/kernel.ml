(* -*- mode: tuareg; fill-column: 79; -*- *)
open Set

module type KERNEL = sig

  type tm = private 
    Var  of string
  | Imp of tm * tm

  type thm

  val assume : tm -> thm

  val disch : tm -> thm -> thm

  val mp : thm -> thm -> thm

  val dest : thm -> tm list * tm

  val print_tm : Format.formatter -> tm -> unit
    
  val print_thm: Format.formatter -> thm -> unit

  val imp : tm -> tm -> tm

  val var : string -> tm


end

module Kernel : KERNEL = struct 

  type tm = Var  of string
            |Imp of tm * tm

  module Tms = Set.Make(
    struct 
      let compare = Pervasives.compare
      type t = tm
    end)

  type thm = Tms.t * tm

  let assume p = (Tms.singleton p,p)

  let disch tm (ctx,goal) = (Tms.remove tm ctx,Imp(tm,goal))
  
  let mp thm1 thm2 = 
    match thm1,thm2 with 
    | (ctxi,Imp(a,b)), (ctxh,goalh) -> 
      if a = goalh then (Tms.union ctxi ctxh,b)
      else failwith "mp: antecedent is not equal to consequent."
    | _ -> failwith "mp: attempt to eliminate non-implication."

  let dest = function
    | (tms,tm) -> (Tms.elements tms, tm)
  
  let rec print_tm ppf tm =
    match tm with
    | Var n -> Format.fprintf ppf "%s" n  
    | Imp (Imp _ as a, b) -> 
      Format.fprintf ppf "%s%a%s %s@ %a"
        "(" print_tm a  ")" "->" print_tm b 
    | Imp (a, b) -> 
      Format.fprintf ppf "%a %s@ %a"
       print_tm a "->" print_tm b 

  let print_thm ppf (tms,tm) =
    let rec aux ppf tms = 
      match tms with 
      | [] -> Format.fprintf ppf " |- %a" print_tm tm
      | [tm'] -> Format.fprintf ppf "%a%a" print_tm tm' aux []
      | tm'::tms -> Format.fprintf ppf "%a,@ %a" print_tm tm' aux tms 
     in
    Format.fprintf ppf "%a" aux (Tms.elements tms)

  let imp a b = Imp (a,b)
    
  let var s = Var s

end
