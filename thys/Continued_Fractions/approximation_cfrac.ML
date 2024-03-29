val _ = \<comment> \<open>Trusting the oracle \<close>@{oracle_name "holds_by_evaluation"}
signature CFRAC_APPROXIMATION_COMPUTATION = sig
val approx_cfrac: Proof.context -> term -> term
end

structure Cfrac_Approximation_Computation : CFRAC_APPROXIMATION_COMPUTATION = struct

  

  val mk_int = HOLogic.mk_number \<^typ>\<open>int\<close> o @{code integer_of_int};

  val term_of_int_list = map mk_int #> HOLogic.mk_list HOLogic.intT

  val approx_cfrac = @{computation "int list"
        terms: "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
           "(+)::nat\<Rightarrow>nat\<Rightarrow>nat" "(-)::nat\<Rightarrow>nat\<Rightarrow>nat" "(*)::nat\<Rightarrow>nat\<Rightarrow>nat"
           "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
           "(+)::int\<Rightarrow>int\<Rightarrow>int" "(-)::int\<Rightarrow>int\<Rightarrow>int" "(*)::int\<Rightarrow>int\<Rightarrow>int" "uminus::int\<Rightarrow>int"
           approx_cfrac
        datatypes: int integer "int list" num floatarith float}
    (fn _ => fn x => case x of SOME lst => term_of_int_list lst
      | NONE => error "Computation approx_cfrac failed.")

end


signature CFRAC_APPROXIMATION = sig
  val approx_cfrac : int -> Proof.context -> term -> term
end


structure Cfrac_Approximation : CFRAC_APPROXIMATION = struct

local
open Approximation

fun mk_approx_cfrac prec t =
  \<^const>\<open>approx_cfrac\<close> $ (HOLogic.mk_number HOLogic.natT prec) $ t

in

fun approx_cfrac prec ctxt t =
  realify t
     |> Thm.cterm_of ctxt
     |> (preproc_form_conv ctxt then_conv reify_form_conv ctxt)
     |> Thm.prop_of
     |> Logic.dest_equals |> snd
     |> dest_interpret |> fst
     |> mk_approx_cfrac prec
     |> Cfrac_Approximation_Computation.approx_cfrac ctxt
end

fun approximate_cfrac_cmd prec modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t =
      raw_t
      |> Syntax.parse_term ctxt 
      |> Type.constraint \<^typ>\<open>real\<close> 
      |> Syntax.check_term ctxt;
    val t' = approx_cfrac prec ctxt t;
    val ty' = Term.type_of t';
    val ctxt' = Proof_Context.augment t' ctxt;
  in
    Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ()
  end |> Pretty.writeln;

val opt_modes =
  Scan.optional (Args.$$$ "prec" |-- Args.colon |-- Parse.nat) 100 --
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>approximate_cfrac\<close>
    "print initial fragment of continued fraction of a real number by approximation"
    (opt_modes -- Parse.term
      >> (fn ((prec, modes), t) => Toplevel.keep (approximate_cfrac_cmd prec modes t)));

end