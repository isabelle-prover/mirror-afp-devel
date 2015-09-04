signature PROP_LTL =
sig
  exception ParseError;
  val parse : int -> (int -> string) -> (string * int * int -> unit) -> string Ltl_Dt.ltlc;
end

functor Ltl (PLTL : PROP_LTL) : sig 
      val compile_from_file : string -> string Ltl_Dt.ltlc;
      val compile_from_string : string -> string Ltl_Dt.ltlc;
      val toString : string Ltl_Dt.ltlc -> string;
      exception LtlError of string;
end = struct

exception LtlError of string;

local
  open Ltl_Dt
in
  fun toString LTLcTrue = "true"
    | toString LTLcFalse = "false"
    | toString (LTLcProp p) = "p(" ^ p ^ ")"
    | toString (LTLcNeg f) = "(" ^ "~ " ^ toString f ^ ")"
    | toString (LTLcAnd (fl,fr)) = "(" ^ (toString fl) ^ " & " ^ (toString fr) ^ ")"
    | toString (LTLcOr (fl,fr)) = "(" ^ (toString fl) ^ " | " ^ (toString fr) ^ ")"
    | toString (LTLcImplies (fl,fr)) = "(" ^ (toString fl) ^ " --> " ^ (toString fr) ^ ")"
    | toString (LTLcIff (fl,fr)) = "(" ^ (toString fl) ^ " <--> " ^ (toString fr) ^ ")"
    | toString (LTLcNext f) = "(" ^ "X " ^ toString f ^ ")"
    | toString (LTLcFinal f) = "(" ^ "F " ^ toString f ^ ")"
    | toString (LTLcGlobal f) = "(" ^ "G " ^ toString f ^ ")"
    | toString (LTLcUntil (fl,fr)) = "(" ^ (toString fl) ^ " U " ^ (toString fr) ^ ")"
    | toString (LTLcRelease (fl,fr)) = "(" ^ (toString fl) ^ " V " ^ (toString fr) ^ ")";
end

fun compile grab =
  let 
    val maxLookAhead = 0 (* no error correction *)
    fun printError (msg,pos,_) = 
      let val posS = if pos = ~1 then "" else "(Pos "^Int.toString pos^") "
      in
        print (posS^msg^"\n")
      end
  in
    PLTL.parse maxLookAhead grab printError
    handle PLTL.ParseError => raise LtlError "Parsing error"
  end

fun compile_from_string str =
  let
    val substr = ref (Substring.full str)
    fun grab n = 
      if Substring.size (!substr) < n then
        let val s = !substr
        in
          substr := Substring.full "";
          Substring.string s
        end
      else
        let val (sl, sr) = Substring.splitAt(!substr, n)
        in
          substr := sr;
          Substring.string sl
        end
  in
    compile grab
  end

fun compile_from_file fileName =
  let 
    val inStream = TextIO.openIn fileName
    fun grab n =
      if TextIO.endOfStream inStream then ""
      else TextIO.inputN (inStream,n)
    val tree = compile grab
  in 
    TextIO.closeIn inStream;
    tree
  end
end;
