(* -*- mode: tuareg; fill-column: 79; -*- *)
module type PROVE  = sig

  type goal = Kernel.tm list * Kernel.tm

  type verifyfun = Kernel.thm list -> Kernel.thm

  type gt = 
    Proved of Kernel.thm
  | Partial of gt list * verifyfun
  | Leaf of goal
  | Invalid

  type tactic = goal -> gt * verifyfun

  (* Start a proof. *)
  val theorem : Kernel.thm list -> Kernel.thm -> unit 

  (* Apply a tactic. *)
  val apply : tactic -> unit

  (* Complete a proof. *) 
  val qed : unit -> unit

  (* Abort a proof attempt. *)
  val abort : unit -> unit 

  (* Undo the last tactic application. *)
  val undo : unit -> unit 

  (* Get current goaltree. *)
  val print_gt: Format.formatter -> gt -> unit

  val state : unit -> gt

end

module Prove = struct 
 
  type goal = Kernel.tm list * Kernel.tm

  type verifyfun = Kernel.thm list -> Kernel.thm

  type tactic = goal -> goal list * verifyfun
  
  type gt = 
    Proved of Kernel.thm
  | Partial of gt list * verifyfun
  | Unproved of goal
  | Invalid

  let goaltree = ref Invalid

  let history = ref []

  let print_goal ppf (tms,tm) =
    let rec aux ppf tms = 
      match tms with 
      | [] -> Format.fprintf ppf " |- %a" Kernel.print_tm tm
      | [tm'] -> Format.fprintf ppf "%a%a" Kernel.print_tm tm' aux []
      | tm'::tms -> Format.fprintf ppf "%a,@ %a" Kernel.print_tm tm' aux tms 
     in
    Format.fprintf ppf "%a" aux tms
    
  let print_gt ppf gt =
    let rec aux ppf gt = 
      match gt with 
      | Proved thm -> Format.fprintf ppf "Have: %a@\n" Kernel.print_thm thm
      | Unproved goal -> Format.fprintf ppf "Want: %a@\n" print_goal goal
      | Partial ([],_) -> () 
      | Partial (gt::gts,vf) -> 
        Format.fprintf ppf "%a%a" aux gt aux (Partial (gts,vf))
      | Invalid -> Format.fprintf ppf "Proof not in progress."
    in
    Format.fprintf ppf "State: @\n @[%a@]@." aux gt

  let theorem tms tm = 
    match !goaltree with
    | Invalid -> 
      goaltree := Unproved (tms,tm); 
      history := [];
      print_gt Format.std_formatter (!goaltree)
    | _  -> failwith "prove: proof alread in progress."
  
  (* Apply a tactic to the left most goal in a goaltree list. *)
  let rec app_on_gts tac gts =
    match gts with 
    | [] -> raise Not_found
    | (Partial _ as b) :: bs ->
      (try (app_on_gt tac b)::bs with | Not_found -> b::(app_on_gts tac bs))
    | (Unproved _ as l) :: bs -> (app_on_gt tac l)::bs
    | (Proved _ as p)::bs -> p::(app_on_gts tac bs)
    | Invalid::_ -> failwith "app_on_gts: BUG - found invalid goal tree."

  (* Apply a tactic to a goaltree. *)
  and app_on_gt tac gt =
    match gt with 
    | Proved _ -> raise Not_found
    | Unproved goal -> tac goal
    | Partial (gts,vf) -> Partial (app_on_gts tac gts,vf)
    | Invalid -> failwith "app_on_gt: BUG - found invalid goal tree."

  (* Normalize a goaltree. *)
  let rec norm_gt gt = 
    match gt with  
    | Partial (gts,vf) ->
      (* Simplify sub-goals. *)
      let gts = List.map norm_gt gts in
      let is_proved = function | Proved _ -> true | _ -> false in 
      let peel = function 
        | Proved x -> x 
        | _ -> failwith "norm_gt:peel: BUG - non-proved constructor found."
      in
      (* All sub-goals in a node are proved; apply verification function. *)
      if List.for_all is_proved gts then Proved (vf (List.map peel gts))
      (* O/w replace old node with a possible simplified node. *)
      else Partial (gts,vf)
    | Invalid -> failwith "norm_gt: BUG - found Invalid constructor."        
    | x -> x 

  let apply tac = 
    match !goaltree with
    | Invalid -> failwith "apply: No proof in progress."
    | _ -> 
      try 
        (* Backup current state. *)
        history := !goaltree :: !history;
        (* Try to apply the tactic. *)
        goaltree := norm_gt (app_on_gt tac !goaltree) ;
        print_gt Format.std_formatter (!goaltree)
      with
      (* Not_found should only be raised when there is nothin left to prove. *)
      | Not_found -> failwith "apply: proof complete."

  let qed () =
    match !goaltree with
    | Proved thm -> 
      goaltree := Invalid;
      history := [];
      thm
    | _ -> failwith "qed: proof is incomplete."
      
  let abort () = 
    goaltree := Invalid;
    history := []

  let undo () = 
    match !history with
    | lgt::history' -> 
      goaltree := lgt;
      history := history'
    | _ -> failwith "undo: at the beginning of the proof."

  let state () = !goaltree

end
