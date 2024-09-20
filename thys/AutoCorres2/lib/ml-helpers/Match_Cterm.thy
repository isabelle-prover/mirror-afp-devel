(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>ML Antiquotation to Match and Instantiate (recombine) cterms and terms\<close>

theory Match_Cterm
  imports 
    AutoCorres_Utils
    TermPatternAntiquote 
begin


ML \<open>
signature MATCH_CTERM =
sig
  val try_match: ('a -> 'b) -> 'a -> 'b option (* handles Match | Pattern.MATCH *)
  val switch: ('a -> 'b) list -> 'a ->  'b (* raises Match *)

  val cterm_match: cterm * cterm -> ctyp TVars.table * cterm Vars.table
  val cterm_first_order_match: cterm * cterm -> ctyp TVars.table * cterm Vars.table

  val match: theory -> term * term -> typ TVars.table * term Vars.table
  val first_order_match: theory -> term * term -> typ TVars.table * term Vars.table

  val pattern_vars: term -> term list
  val cterm_pattern_vars: cterm -> cterm list

  val cterm_instantiate: Position.T ->
       ctyp TVars.table * cterm Vars.table ->
         cterm list -> cterm list -> cterm -> cterm
  val instantiate: Position.T ->
       typ TVars.table * term Vars.table ->
         term list -> term list -> term -> term

  datatype mode = Higher_Order  | First_Order | ML_Pattern
  val parse_mode: Token.T list -> mode * Token.T list
  val parse_morph_mode: Token.T list -> mode * Token.T list
  val ml_match_term: {morph: bool, cert: bool} -> mode -> Proof.context -> Position.T -> string -> string
end

structure Match_Cterm: MATCH_CTERM =
struct

fun try_match f x = SOME (f x) handle Match => NONE | Pattern.MATCH => NONE
  
fun switch (c::cs) = (fn x => (* to allow partial evaluation on list elements *)
      (case try_match c x of 
         SOME v => v
      | NONE => switch cs x))
  | switch [] = raise Match

(* ML code composition *)
fun ml_val_binding (name, value) = implode_space ["val", name, "=", value];
fun ml_indent n str = String.concat (replicate n " ") ^ str

fun ml_let_binding vals body =  
  ["let"] @
     (map (ml_indent 2) vals) @ [
   "in",
     ml_indent 2 body,
   "end"]

fun ml_list elems   = enclose "[" "]" (space_implode ", " elems)
fun ml_tuple elems  = enclose "(" ")" (space_implode ", " elems)
fun ml_record elems = enclose "{" "}" (space_implode ", " elems)
val ml_atomic = enclose "(" ")"

fun triv_record_field name = implode_space [name, "=", name]
val triv_record_inst = map triv_record_field #> ml_record

fun ml_fun name args body = 
  implode_space (["fun", name] @ args @ ["="]) ::
  (map (ml_indent 2) body)

fun ml_fn args body = 
  implode_space (map (fn arg => implode_space ["fn", arg, "=>"]) args)::
  (map (ml_indent 2) body)

fun ml_apply f args = implode_space (f :: args)

fun ml_check_match term_pat args ct = (* apply to args to ommit warning on unused identifiers *)
  ml_apply 
    (ml_atomic (implode_space ["fn", term_pat, "=>", ml_tuple args, "| _ => raise Match" ]))
    [ml_atomic (ml_apply "Thm.term_of" [ct])]


(* Interface used by antiquotation *)
fun cterm_match (pat, obj) = Thm.match (pat, obj)  
  handle Pattern.MATCH => Exn.reraise Pattern.MATCH

fun cterm_first_order_match (pat, obj) = Thm.first_order_match (pat, obj)  
  handle Pattern.MATCH => Exn.reraise Pattern.MATCH

fun gen_match match thy (pat, obj) =
  let
    val (Tinsts, tinsts) = match thy (pat, obj) (Vartab.empty, Vartab.empty)
    fun mk_Tinst ((a, i), (S, T)) =
      (((a, i), S), T);
    fun mk_tinst ((x, i), (U, t)) =
      let val T = Envir.subst_type Tinsts U in
        (((x, i), T), t)
      end
  in
    (TVars.build (Vartab.fold (TVars.add o mk_Tinst) Tinsts),
     Vars.build (Vartab.fold (Vars.add o mk_tinst) tinsts))
  end

fun match thy (pat, obj) = gen_match Pattern.match thy (pat, obj)  
  handle Pattern.MATCH => Exn.reraise Pattern.MATCH

fun first_order_match thy (pat, obj) = gen_match Pattern.first_order_match thy (pat, obj)  
  handle Pattern.MATCH => Exn.reraise Pattern.MATCH

fun cterm_instantiate pos (tenv, env) vars vals pattern =
  let
    val insts = map (Term.dest_Var o Thm.term_of) vars ~~ vals
    fun upd var value = the_default value (AList.lookup (op =) insts var)
    val env' = Vars.map upd env
  in
    Thm.instantiate_cterm (tenv, env') pattern
  end
  handle 
    CTERM (msg, args) => 
            Exn.reraise (CTERM (msg ^ "\n from antiquotation Match_Cterm.cterm_instantiate here: " ^ Position.here pos, args));

fun instantiate pos (tenv, env) vars vals pattern =
  let
    val insts = map Term.dest_Var vars ~~ vals
    fun upd var value = the_default value (AList.lookup (op =) insts var)
    val env' = Vars.map upd env
  in
    Term_Subst.instantiate (tenv, env') pattern
  end
  handle 
    TERM (msg, args) => 
            Exn.reraise (TERM (msg ^ "\n from antiquotation Match_Cterm.instantiate here: " ^ Position.here pos, args));

(* Antiquotation *)

fun collect_vars t = fold_aterms (fn Var v => cons v | _ => I) t [] |> rev

fun pattern_vars pat = pat 
  |> collect_vars 
  |> filter_out (fn (("_dummy_", _), _) => true | _ => false)
  |> (distinct (op =)) |> map Var

fun cterm_pattern_vars cpat = 
  let
    val ctxt = cpat |> Thm.theory_of_cterm |> Proof_Context.init_global
  in
    cpat |> Thm.term_of |> pattern_vars |> map (Thm.cterm_of ctxt)
  end

datatype mode = Higher_Order | First_Order | ML_Pattern

fun ml_match_term (kind as {morph:bool, cert:bool}) (mode:mode) ctxt pos pattern_str =
  let
    val phiN = "phi_"
    val thyN = "thy_"

    val match = case (mode, kind) of
          (Higher_Order, {cert = true ,...}) => "Match_Cterm.cterm_match"
        | (Higher_Order, {cert = false,...}) => ml_apply "Match_Cterm.match"  [thyN]
        | (_           , {cert = true ,...}) => "Match_Cterm.cterm_first_order_match"
        | (_           , {cert = false,...}) => ml_apply "Match_Cterm.first_order_match" [thyN]

    val cterm_of = case kind of
          {morph = false, cert = true } => "Thm.cterm_of ML_context"
        | {morph = false, cert = false} => ""
        | {morph = true , cert = true }  => "(Morphism.cterm " ^ phiN ^ " o Thm.cterm_of ML_context)" 
        | {morph = true , cert = false}  => "Morphism.term " ^ phiN  

    val ctN = "ct_" val envN = "env_" val instN = "inst_" val patN = "pat_" val posN = "pos_" 

    val instantiateN = "instantiate"
    val reserved = [ctN, envN, instN, instantiateN, patN, posN, instantiateN]
    val pat = Proof_Context.read_term_pattern ctxt pattern_str
    val vars = collect_vars pat |> filter_out (fn (("_dummy_", _), _) => true | _ => false)
                |> (mode <> ML_Pattern) ? (distinct (op =))
    val names = map (#1 o #1) vars
    val dups = duplicates (op =) names
    val _ = if null dups then () 
            else error ("ml_match_cterm: duplicate variables in pattern: " ^ Position.here pos  ^ (commas (map quote dups)))
    val clashes = inter (op =) names reserved 
    val _ = if null clashes then () 
            else error ("ml_match_cterm: avoid internal name(s) in pattern: " ^ (commas (map quote clashes)))

    val names_var = map (suffix "_var") names
    
    val ml_pat = ml_apply cterm_of [ml_atomic (ML_Syntax.print_term pat)]   
    val ml_pattern_check = 
         if mode = ML_Pattern then 
           [ml_val_binding ("_", 
              ml_check_match (Term_Pattern_Antiquote.term_pattern_antiquote ctxt pattern_str) names ctN)]
         else [] 

    val pat_vars = case cert of
          true => "Match_Cterm.cterm_pattern_vars"
        | false => "Match_Cterm.pattern_vars"

    val inst = case cert of 
           true => "Thm.instantiate_cterm" 
         | false => "Term_Subst.instantiate"
    val instantiate = case cert of 
           true => "Match_Cterm.cterm_instantiate"
         | false => "Match_Cterm.instantiate"

    val vals = map ml_val_binding [
          (posN, ML_Syntax.print_position pos),
          (ml_list names_var, ml_apply pat_vars [patN]),
          (envN, ml_apply match [ml_tuple [patN, ctN]]),
          (ml_list names, 
            ml_apply "map" 
              [ml_atomic (ml_apply inst [envN]), ml_list names_var]),
          (ml_list names_var, 
            ml_apply "map" 
              [ml_atomic (ml_apply inst [ml_tuple [ml_apply "fst" [envN], "Vars.empty"]]), 
              ml_list names_var])]          
    val instantiate = ml_fun instantiateN [ml_record names] 
          [ml_apply instantiate [posN, envN, ml_list names_var, ml_list names, patN]]
    val inst = ml_val_binding (instN, triv_record_inst (names @ [instantiateN, ctN]))
    val pat_binding = map ml_val_binding [(patN, ml_pat)]
    val outer_args = if morph then [phiN] else []

    val body = ml_let_binding (ml_pattern_check @ vals @ instantiate @ [inst]) instN
    val args = (if cert then [] else [thyN]) @ [ctN]
    val res = ml_fn args body |> space_implode "\n"
    val outer_body = ml_let_binding pat_binding res (* partial application of phi to pattern *)
    val outer_res = ml_fn outer_args outer_body |> space_implode "\n"
    val _ = Utils.verbose_msg 5 ctxt (fn _ => "ml_match_cterm: " ^ outer_res)
  in
    outer_res
  end


val parse_mode = Scan.optional 
      (Args.parens (
         Args.$$$ "ho" >> K Higher_Order || 
         Args.$$$ "fo" >> K First_Order || 
         Args.$$$ "ml" >> K ML_Pattern)) 
      Higher_Order;

val parse_morph_mode = Scan.optional 
      (Args.parens (
         Args.$$$ "ho" >> K Higher_Order || 
         Args.$$$ "fo" >> K First_Order))
      Higher_Order;

end

val _ = Theory.setup 
   (ML_Antiquotation.value_embedded @{binding "cterm_match"}
      ((Args.context -- Scan.lift (Match_Cterm.parse_mode -- Parse.position Parse.embedded_inner_syntax)) 
         >> (fn (ctxt, (mode, (pattern_str, pos))) => 
               Match_Cterm.ml_match_term {morph = false, cert = true} mode ctxt pos pattern_str)) #>
   (ML_Antiquotation.value_embedded @{binding "cterm_morph_match"}
      ((Args.context -- Scan.lift (Match_Cterm.parse_morph_mode -- Parse.position Parse.embedded_inner_syntax)) 
         >> (fn (ctxt, (mode, (pattern_str, pos))) => 
               Match_Cterm.ml_match_term {morph = true, cert = true} mode ctxt pos pattern_str))) #>
   (ML_Antiquotation.value_embedded @{binding "match"}
      ((Args.context -- Scan.lift (Match_Cterm.parse_mode -- Parse.position Parse.embedded_inner_syntax)) 
         >> (fn (ctxt, (mode, (pattern_str, pos))) => 
               Match_Cterm.ml_match_term {morph = false, cert = false} mode ctxt pos pattern_str))) #>
   (ML_Antiquotation.value_embedded @{binding "morph_match"}
      ((Args.context -- Scan.lift (Match_Cterm.parse_morph_mode -- Parse.position Parse.embedded_inner_syntax)) 
         >> (fn (ctxt, (mode, (pattern_str, pos))) => 
               Match_Cterm.ml_match_term {morph = true, cert = false} mode ctxt pos pattern_str))))
\<close>


text \<open>The antiquotation yields a function that matches the schematic variables of a pattern with a 
@{ML_type cterm}. The matched parts are returned as @{ML_type cterm} in a record, where the 
field name is derived from the original schematic variable name. 
Moreover a function \<open>instantiate\<close> is returned that can be used to instantiate the matched pattern 
with other @{ML_type cterm}s.

The antiquotation makes use of the kernel operations @{ML Thm.match} / @{ML Thm.first_order_match}.
These operations are efficient in the sense that no costly re-certification of subterms has
to be performed.
\<close>

ML_val \<open>
val {f, g, instantiate, ct_} = @{cterm_match "\<lambda>x. ?f x + ?g x"} @{cterm "\<lambda>x. p x + q x"}
val twisted = instantiate {f = g, g = f}
\<close>


text \<open>Dummy pattern can also be supplied. The matched values for the dummy patterns are not
part of the matching result but still considered in \<open>instantiate\<close>.\<close>

ML_val \<open>
val {f, g, instantiate, ...} = @{cterm_match "\<lambda>x. ?f x + ?g x + _"} @{cterm "\<lambda>x. p x + q + r x"}
val twisted = instantiate {f = g, g = f}
\<close>


ML_val \<open>
val {f, g, ...} = @{cterm_match "\<lambda>x. ?f x + ?g x"} @{cterm "\<lambda>x. p x + q"}
\<close>


ML_val \<open>
val {f1, f2, ...} = @{cterm_match "\<lambda>x. ?f1.0 x + ?f2.0 x"} @{cterm "\<lambda>x. p x + q"}
\<close>


ML_val \<open>
val {f, ...} = @{cterm_match "\<lambda>x. ?f x"} @{cterm \<open>\<lambda>x. f\<close>}
\<close>

text \<open>There is also a variant for first-order-matching.\<close>
ML_val \<open>
let
  val _ = @{cterm_match (fo) "\<lambda>x. ?f x"} @{cterm \<open>\<lambda>x. f\<close>} 
in
  ()
end
handle Pattern.MATCH => tracing ("this is not first order")
\<close>

text \<open>There is also the corresponding antiquotations for plain terms.\<close>

ML_val \<open>
val {f, g, instantiate, ...} = @{match "\<lambda>x. ?f x + ?g x"} @{theory} @{term "\<lambda>x. p x + q x"}
val twisted = instantiate {f = g, g = f}
\<close>

text \<open>There you can also see the different workings of first-order-matching. Note the
eta expanded match result in the higher-order variant before.\<close>

ML_val \<open>
val {f, g, instantiate, ...} = @{match (fo) "\<lambda>x. ?f x + ?g x"} @{theory} @{term "\<lambda>x. p x + q x"}
val twisted = instantiate {f = g, g = f}
\<close>


text \<open>There is a variant for ML-pattern-matching. This means, that before using
  first-order-matching it is tested whether the term actually matches the underlying
  ML-pattern with ML-pattern matching. \<close>


ML_val \<open>
val {f, g, instantiate, ...} = @{cterm_match (ml) "\<lambda>x. ?f x + ?g x"} @{cterm "\<lambda>x. p x + q x"}
val twisted = instantiate {f = g, g = f}
\<close>

text \<open>Note that as with all ML-Patterns a variable might only appear once. So the following
example is a valid first-order or higher-order pattern but not a valid ML-pattern\<close>
ML_val \<open>
val {f, ...} = @{cterm_match "?f + ?f"} @{cterm "a + a"}
\<close>

text \<open>This is what happens conceptually in the expanded antiquotation.\<close>
ML_val \<open>
val ctxt = @{context}
val pat = Proof_Context.read_term_pattern ctxt "\<lambda>x. ?f x + ?g x" |> Thm.cterm_of ctxt
val [g_var, f_var] = Term.add_vars (Thm.term_of pat) [] |> map (Thm.cterm_of ctxt o Var)
val env = Thm.match (pat, @{cterm "\<lambda>x. a x + b"})
val [f, g] = map (Thm.instantiate_cterm env) [f_var, g_var]
val tenv = fst env
val [f_var, g_var] = map (Thm.instantiate_cterm (tenv, Vars.empty)) [f_var, g_var]
fun instantiate {f, g} = 
      Match_Cterm.cterm_instantiate Position.none env [f_var, g_var] [f, g]
val res = {f = f, g = g, instantiate = instantiate}
val x= instantiate {f=g, g=f}
\<close>

text \<open>With the verbose flag you can see the generated function.\<close>
declare [[verbose=5]]

ML_val \<open>
val X = @{cterm_match "?X + _"} @{cterm \<open>a + a\<close>}
\<close>

ML_val \<open>
val X = @{cterm_morph_match "?X + _"} Morphism.identity @{cterm \<open>a + a\<close>}
\<close>

ML_val \<open>
val X = @{morph_match "?X + _"} Morphism.identity @{theory} @{term \<open>a + a\<close>}
\<close>

ML_val \<open>
val X = @{cterm_match \<open>?X + _\<close>} @{cterm \<open>a + a\<close>}
\<close>


declare [[verbose=0]]

end