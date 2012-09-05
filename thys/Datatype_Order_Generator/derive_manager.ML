signature DERIVE_MANAGER =
sig
  (* identifier, description, (fn dtyp_name => register-method) *)
  val register_derive : string -> string -> (string -> theory -> theory) -> theory -> theory
  (* identifier, dtyp_name *)
  val derive : string -> string -> theory -> theory
  (* print all registered deriving-methods  *)
  val print_info : theory -> theory
end

structure Derive_Manager : DERIVE_MANAGER =
struct

structure Derive_Data = Theory_Data(
  type T = 
    (string * (string -> theory -> theory)) Symtab.table  (* descr * derive-fun *)
  
  val empty = Symtab.empty
  val extend = I
  fun merge (x,y) = Symtab.merge (K true) (x,y)
)


fun derive_options thy = 
  Derive_Data.get thy |> Symtab.dest |> map (fn (id,(descr,_)) => (id,descr))

fun print_info thy = let
  val _ = Output.writeln "The following sorts can be derived"
  val _ = derive_options thy |> map (fn (id,descr) => Output.writeln (id ^ ": " ^ descr)) 
  in thy end
  

fun register_derive id descr f thy = let
  val table = Derive_Data.get thy
  in if Symtab.defined table id then error ("Identifier " ^ quote id ^ " already in use for " ^ quote "deriving")
  else Symtab.update_new (id,(descr,f)) table 
    |> Derive_Data.put
    |> (fn x => x thy)
  end  

fun derive id dtname thy = 
  case (Derive_Data.get thy |> Symtab.lookup) id of
    NONE => error ("No handler to derive sort " ^ quote id ^ " is registered. Try " ^ quote "print_derives" ^ " to see available sorts.")
  | SOME (_,f) => f dtname thy

end

val _ =
  Outer_Syntax.command @{command_spec "print_derives"} "lists all registered sorts which can be derived"
    (Scan.succeed (Toplevel.theory (Derive_Manager.print_info)))

(* TODO: isn't there a nicer way to combine two parsers sequentially? *)
(* TODO: also check for alternative of fullname *)
(* TODO: replace hand-written parser *)
val _ = let 
  fun parse_pair p1 p2 = p1 #> (fn (x,ts) => p2 ts |> (fn (y,ts) => ((x,y),ts)))
  fun fullname thy dtyp_name = Syntax.parse_typ (Proof_Context.init_global thy) dtyp_name |> dest_Type |> fst
  fun one_word_parser xs = case xs of [] => Scan.fail xs | (x :: xs) => (Token.content_of x,xs) 
  val owp = one_word_parser
  in Outer_Syntax.command @{command_spec "derive"} "derives a sort for some datatype"
    (parse_pair owp owp >> (fn (s,dtname) => Toplevel.theory (
    fn thy => Derive_Manager.derive s (fullname thy dtname) thy
    )))
  end

