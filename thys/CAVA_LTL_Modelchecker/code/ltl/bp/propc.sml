structure Propc : sig 
  datatype propc = CProp of char list 
                 | FProp of (char list * IntInf.int);

  val propcToString : propc -> string;
end = struct
  open BoolProgs_LTL_Conv;

  fun propcToString (CProp s) = implode s 
    | propcToString (FProp (s, i)) = (implode s) ^ " " ^ IntInf.toString i
end;
