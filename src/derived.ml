(* -*- mode: tuareg; fill-column: 79; -*- *)
module Derived = struct

  let weaken : Kernel.tm -> Kernel.thm -> Kernel.thm = fun tm thm ->
    Kernel.mp (Kernel.disch tm thm) (Kernel.assume tm)

end
