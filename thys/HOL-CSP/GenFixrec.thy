(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_Metric_Space - Seeing Processes as a Metric Space
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Core of Generic Fixrec Package
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)

chapter \<open>Generic Interface for a Fixrec 'language'\<close>

theory  "GenFixrec"
  imports Main
  keywords "Fixrec" :: thy_decl

begin

section\<open>Overview\<close>

text\<open>
The command \<^verbatim>\<open>Fixrec\<close> introduces constants by a system of (mutually) recursive equations
\<open>f\<^sub>i x\<^sub>i = E\<^sub>i\<close> in a readable syntax. The equations are tupled into one functional \<open>F\<close> over
the product of the function spaces; the tuple is defined as a fixpoint of \<open>F\<close>, and each \<open>f\<^sub>i\<close>
is defined as its projection. From this, the package derives the equations as stated (they
are not added to the simpset by default), an unfolding theorem for the tuple, and a 
fixpoint induction rule. In contrast to the \<^verbatim>\<open>fixrec\<close> package of HOLCF, the constants can be
ordinary total HOL functions; no continuous function spaces and no \<open>cpo\<close> instances of argument 
types are needed.

The package is generic in the underlying semantic domain or \<open>semantic space\<close> for giving semantics
to fixpoint operators \<open>Y\<close> satisfying the fixpoint equation: 

   @{cartouche [indent=10] \<open>Y F = F(Y F)\<close>}

or: 

   @{cartouche [indent=10] \<open>application_condition F \<Longrightarrow> Y F = F(Y F)\<close>}

since an arbitrary consistent \<open>Y\<close> of type \<^typ>\<open>('\<alpha> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<alpha>\<close> is impossible in HOL.
Classical fixpoint operators are \<^term>\<open>lfp\<close> or \<^term>\<open>gfp\<close> for set types.
 
Technically, the semantic space must be given to the package as a \<^emph>\<open>language\<close> (an ML record 
\<^verbatim>\<open>GenFixrec.language\<close>) providing the fixpoint operator and the tactics for the fixpoint
equation, the projections and the induction rule. The simplifier must be set up such that it
can solve the \<open>application_condition\<close> automatically. Languages are registered under a name;
\<open>Fixrec [L\<^sub>1, \<dots>, L\<^sub>n]\<close> tries them from left to right and takes the first one that succeeds.
There are two instances in the HOL-CSP project:
  \<^item> \<^verbatim>\<open>HOLCF\<close> (theory \<^verbatim>\<open>GenFixrec-HOLCF\<close>, session \<^verbatim>\<open>HOL-CSP\<close>): least fixpoints \<open>\<mu>\<close> in Scott
    domains; the side condition is continuity of \<open>F\<close>. This is the default language.
  \<^item> \<^verbatim>\<open>RS\<close> (theory \<^verbatim>\<open>GenFixrec-RS\<close>, session \<^verbatim>\<open>HOL-CSP_RS\<close>): unique fixpoints \<open>\<upsilon>\<close> in complete
    restriction spaces; the side condition is constructiveness (guardedness) of \<open>F\<close>, proved
    automatically with the constructiveness and non-destructiveness rules of the operators.
For functionals that are both continuous and constructive, the two fixpoints coincide.
\<open>Fixrec [RS, HOLCF]\<close> thus yields unique fixpoints where possible and falls back to \<open>\<mu>\<close>
otherwise, e.g. for unguarded recursion or recursion through hiding.
\<close>

section\<open>The Core\<close>


ML\<open>

structure GenFixrec =

struct

type language = {mk_fix    : term list -> term -> term,
                 dest_fix  : term -> term,
                 (* Domain-specific application/abstraction pair ("inner" shift).
                    Standard HOL application/abstraction  f x\<^sub>1 ... (y\<^sub>1,...,y\<^sub>m) ...  is handled
                    generically by the core (cartesian closedness assumed); a language may
                    additionally provide its own pair, e.g. HOLCF:  f\<cdot>x / \<Lambda> x. E  and
                    f\<cdot>(x\<^sub>1,...,x\<^sub>n) / \<Lambda>(x\<^sub>1,...,x\<^sub>n). E *)
                 lambda'   : term -> term -> term, 
                             (* lambda' pat E : abstraction over pat (a free variable or a
                                tuple of them) w.r.t. apply *)
                 apply     : term,  (* inner application constant (e.g. Rep_cfun);
                                       a dummy (no Const) if the language has none *)
                 shift_tac : {context: Proof.context, prems: thm list} -> tactic,
                 fix_tac   : {context: Proof.context, prems: thm list} -> tactic,
                             (* proves  rec = F rec ; prems = [rec_def] with
                                rec_def : rec \<equiv> mk_fix [] F  *)
                 proj_tac  : {proj_def : thm, projs : thm list, unfold : thm} ->
                             {context: Proof.context, prems: thm list} -> tactic,
                             (* proj's of the form c = E, (current) proj_def \<in> projs,
                                unfold is the current rec_unfold theorem (without combinator) *)
                 fixind_tac: {eqns: binding, 
                              varstab :  ((binding * typ * mixfix) * term) list, 
                              projs : thm list, 
                              rec_def: thm,
                              unfold : thm} ->
                             {context: Proof.context, prems: thm list} -> thm

                }; 


structure FixrecDataStore = Generic_Data
(
  type T = language Name_Space.table;
  val empty : T = Name_Space.empty_table "Fixrec language";
  fun merge data : T = Name_Space.merge_tables data;
);

fun update_language name lang ctxt = 
    ctxt |> FixrecDataStore.map (Name_Space.define ctxt false (name, lang) #> #2)

(* Function to retrieve FDR data by binding name *)
fun get_language name ctxt =
  case Name_Space.lookup (FixrecDataStore.get ctxt) name of
      NONE => error ("No FDR data found for binding: " ^ name)
    | SOME fdr_data => fdr_data;

fun get_languages ctxt = FixrecDataStore.get ctxt |> Name_Space.dest_table

fun get_languages_global thy = FixrecDataStore.get (Context.Theory thy) |> Name_Space.dest_table


fun cong (Const(s,_)) (Const(t,_)) = (s = t)
   |cong _ _ = false 

(* Decomposes a lhs  c a\<^sub>1 ... a\<^sub>n  into head and arguments, where an application may be
   either HOL application or an inner application of a language (e.g.  c\<cdot>a  in HOLCF,
   i.e. Rep_cfun c a). Arguments are tagged with true iff applied by an inner application.
   applyS are the inner application constants (only their names are relevant). *)
fun decompose applyS t = 
    let fun app (h, args) x = (h, args @ [x])
        fun dest ((Ap $ f) $ a) = if exists (cong Ap) applyS 
                                  then app (dest f) (a, true)
                                  else app (dest (Ap $ f)) (a, false)
           |dest (f $ a)       = app (dest f) (a, false)
           |dest t             = (t, [])
    in  dest t end; 



(* The equation system after reading (in the local theory): the declared constants are
   fixed variables (Frees) in the equations, free variables are the parameters. *)
type absy = {eqns_sys : binding,
             fixes    : ((binding * typ) * mixfix) list,
             eqns     : (Attrib.binding * term) list}

fun strip_alls t = (case try Logic.dest_all_global t of SOME (_, u) => strip_alls u | NONE => t)

fun is_pattern (Free _) = true
  | is_pattern (Const (\<^const_name>\<open>Pair\<close>, _) $ a $ b) = is_pattern a andalso is_pattern b
  | is_pattern _ = false

(* Reads declarations and equations jointly in the local theory (type inference, sorts,
   locale parameters as fixed variables) and checks the shape of the equations. *)
fun context_check (vars  : (binding * string option * mixfix) list,
                   specs : (bool * (Attrib.binding * string)) list) lthy : absy =
    let val _ = if exists (fn (_, T, _) => is_none T) vars 
                then error "Fixrec: type expected for all declared constants" else ()
        val ((fixes, spec), _) = 
              Specification.read_multi_specs vars (map (fn (_, s) => (s, [], [])) specs) lthy
        val names  = map (Binding.name_of o fst o fst) fixes
        val eqns   = map (apsnd (HOLogic.dest_Trueprop o strip_alls)) spec
        val applyS = get_languages (Context.Proof lthy) |> map (#apply o snd)
        fun check_eqn (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ _) =
              let val (hdt, targs) = decompose applyS lhs
                  val _ = case hdt of Free (n, _) => if member (op =) names n then () 
                                                     else err_head hdt
                                    | _ => err_head hdt
              in  if forall (is_pattern o fst) targs then ()
                  else error "args must be free variables or tuples of them."
              end
          | check_eqn _ = error "term must be equation"
        and err_head hdt = error ("lhs head must be one of the declared constants, but is "
                                  ^ Syntax.string_of_term lthy hdt
                                  ^ " (application not supported by the available languages?)")
        val _ = map (check_eqn o snd) eqns
        val name_rec = space_implode "_" names
    in {eqns_sys = Binding.make (name_rec, Binding.pos_of (fst (fst (hd fixes)))),
        fixes = fixes, eqns = eqns}
    end

(* Projection proofs are pure tuple reasoning, independent of the language: c = proj rec,
   rec = F rec, compute the projection of the tuple F rec with the pair rules only, fold the
   projections back, reflexivity. Independent of the size of the terms in the equations. *)
val fixrec_proj_aux2 = Goal.prove_global \<^theory> [] []
                         \<^prop>\<open>s = s' \<Longrightarrow> P s' = t \<Longrightarrow> P s = t\<close>
                         (fn {context, ...} => auto_tac context)
val fixrec_proj_aux2' = meta_eq_to_obj_eq RS fixrec_proj_aux2

fun structural_projection_tac defs unfold ctxt def =
       let val ss = put_simpset HOL_basic_ss ctxt
                    |> Simplifier.add_simps @{thms fst_conv snd_conv case_prod_beta}
       in  EVERY [resolve0_tac [def RS fixrec_proj_aux2'] 1,
                  resolve0_tac [unfold RS fixrec_proj_aux2] 1,
                  simp_tac ss 1,     (* may already solve non-recursive equations *)
                  TRY (Local_Defs.fold_tac ctxt defs),
                  TRY (resolve0_tac [@{thm refl}] 1),
                  COND (has_fewer_prems 1) all_tac no_tac]
       end

local open HOLogic in

fun parm_lifter (x:term) _ = error("illegal argument term: " ^ @{make_string} x)

fun tupled_lambda' (x as Free _) b = lambda x b
  | tupled_lambda' (x as Var _) b = lambda x b
  | tupled_lambda' (Const (\<^const_name>\<open>Product_Type.Pair\<close>, _) $ u $ v) b =
      mk_case_prod (tupled_lambda' u (tupled_lambda' v b))
  | tupled_lambda' (Const (\<^const_name>\<open>Product_Type.Unity\<close>, _)) b =
      Abs ("x", unitT, b)
  | tupled_lambda' (x as Const _) b = lambda x b
  | tupled_lambda' t _ = raise TERM ("tupled_lambda: bad tuple", [t]);

fun eqnS_convert (lang : language) ((_,head_args),rhs) = 
        fold_rev (fn (pat, true) => #lambda' lang pat
                   | (Free xt, false) => absfree xt
                   | (tpl as (Const(@{const_name\<open>Product_Type.Pair\<close>},_) $ _ $ _), false) => tupled_lambda tpl 
                   | (x, _) => parm_lifter x) head_args rhs; 

(* The construction for one language, as a local-theory transformation; works in theories,
   locales and other local contexts. Terms and theorems are passed along (no name lookups). *)
fun add_fixrec_cmd (lang : language) ({eqns_sys, fixes, eqns} : absy) (lthy : local_theory) =
    let val {mk_fix, dest_fix, fix_tac, proj_tac, fixind_tac, apply, ...} = lang
        val eqnsTS     = map ((apfst (decompose [apply])) o HOLogic.dest_eq o snd) eqns
        val lhsHeads   = mk_tuple (map (fst o fst) eqnsTS)
        val rhsTuple   = mk_tuple (map (eqnS_convert lang) eqnsTS)
        val fixrec_rhs = tupled_lambda' lhsHeads rhsTuple
        val rec_bdg    = Binding.suffix_name "_rec" eqns_sys

        (* the fixpoint of the system *)
        val ((rec_const, (_, rec_def)), lthy) = lthy
              |> Local_Theory.define ((rec_bdg, NoSyn), 
                                      ((Thm.def_binding rec_bdg, []), mk_fix [] fixrec_rhs))

        (* its unfolding, stated w.r.t. the functional as stored in the definition *)
        val F          = dest_fix (snd (Logic.dest_equals (Thm.prop_of rec_def)))
        val unfold_thm = Goal.prove lthy [] [] (mk_Trueprop (mk_eq (rec_const, F $ rec_const)))
                           (fn {context, ...} => fix_tac {context = context, prems = [rec_def]})
        val ((_, [unfold_thm]), lthy) = lthy 
                                        |> Local_Theory.note 
                                               ((Binding.suffix_name "_unfold" rec_bdg, []), 
                                                 [unfold_thm])

        (* the projections, i.e. the declared constants *)
        val n = length fixes
        fun projS i = (i <> n ? mk_fst) (funpow (i - 1) mk_snd rec_const)
        val (proj_res, lthy) = lthy
              |> fold_map (fn (((b, _), mx), i) => 
                             Local_Theory.define ((b, mx), ((Thm.def_binding b, []), projS i)))
                          (fixes ~~ (1 upto n))
        val consts     = map fst proj_res
        val proj_defs  = map (snd o snd) proj_res
        val inst       = map (fn ((b, T), _) => (Binding.name_of b, T)) fixes ~~ consts

        (* the equations as stated, proven by projection *)
        fun prove_eqn ((att, eq), i) lthy =
              let val eq'  = Term.subst_free (map (apfst Free) inst) eq
                  val xs   = Term.add_free_names eq' [] |> filter_out (Variable.is_fixed lthy)
                  val thm  = Goal.prove lthy xs [] (mk_Trueprop eq')
                               (fn {context, prems} => 
                                   proj_tac {proj_def = nth proj_defs i, projs = proj_defs, 
                                             unfold = unfold_thm}
                                            {context = context, prems = prems})
                  val (b, srcs) = att
              in  lthy |> Local_Theory.note ((b, map (Attrib.check_src lthy) srcs), [thm]) |> snd
              end
        val lthy = fold prove_eqn (eqns ~~ (0 upto n - 1)) lthy

        (* fixpoint induction *)
        val varstab = map (fn ((b, T), mx) => (b, T, mx)) fixes ~~ consts
        val induct  = fixind_tac {eqns = eqns_sys, varstab = varstab, projs = proj_defs,
                                  rec_def = rec_def, unfold = unfold_thm}
                                 {context = lthy, prems = []}
    in  lthy |> Local_Theory.note ((Binding.suffix_name "_induct" eqns_sys, []), [induct]) |> snd
    end

(* Try the languages in the given order; the first one for which the whole construction
   (definitions and proofs) succeeds is taken. *)
fun add_fixrec_langs_cmd (langs : (xstring * Position.T) list) spec (lthy : local_theory) =
    let val context = Context.Proof lthy
        val table = FixrecDataStore.get context
        val _ = if null langs then error "Fixrec: no language given" else ()
        val langs' = map (apfst Long_Name.base_name o Name_Space.check context table) langs
        val absy = context_check spec lthy
        fun try [] errs = error ("Fixrec: no language succeeded:\n" ^
                                 cat_lines (map (fn (n, msg) => n ^ ": " ^ msg) (rev errs)))
          | try ((name, lang) :: ls) errs =
               (if length langs' > 1 then writeln ("Fixrec: trying language " ^ name) else ();
                case Exn.result (add_fixrec_cmd lang absy) lthy of
                  Exn.Res lthy' => lthy'
                | Exn.Exn exn => (if null ls then ()
                                  else warning ("Fixrec: language " ^ name ^ " failed");
                                  try ls ((name, Runtime.exn_message exn) :: errs)))
    in  try langs' [] end

(* the same at theory level, e.g. for ML-level tests *)
fun add_fixrec_langs_global langs spec = Named_Target.theory_map (add_fixrec_langs_cmd langs spec)

end (* local *)

end (* Struct *)
\<close>

ML \<open> (* notation "(unchecked)" really needed ? Stems from other packages. *)

local 
val opt_thm_name' : (bool * Attrib.binding) parser =
  \<^keyword>\<open>(\<close> -- \<^keyword>\<open>unchecked\<close> -- \<^keyword>\<open>)\<close> >> K (true, Binding.empty_atts)
    || Parse_Spec.opt_thm_name ":" >> pair false

val spec' : (bool * (Attrib.binding * string)) parser =
  opt_thm_name' -- Parse.prop >> (fn ((a, b), c) => (a, (b, c)))

val multi_specs' : (bool * (Attrib.binding * string)) list parser =
  let val unexpected = Scan.ahead (Parse.name || \<^keyword>\<open>[\<close> || \<^keyword>\<open>(\<close>)
  in Parse.enum1 "|" (spec' --| Scan.option (unexpected -- Parse.!!! \<^keyword>\<open>|\<close>)) end

val parse_recsys_spec = Parse.vars -- (Parse.where_ |-- Parse.!!! multi_specs')

(* optional language selection: Fixrec [L1, ..., Ln] ... ; default is HOLCF *)
val default_fixrec_languages = [("HOLCF", Position.none)]

val parse_languages : (xstring * Position.T) list parser =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.!!! (Parse.list1 Parse.name_position --| \<^keyword>\<open>]\<close>))
                default_fixrec_languages

in
val _ = 
  Outer_Syntax.local_theory \<^command_keyword>\<open>Fixrec\<close> "define recursive functions"
    (parse_languages -- parse_recsys_spec 
      >> (fn (langs, spec) => GenFixrec.add_fixrec_langs_cmd langs spec))
end;
\<close>

end


