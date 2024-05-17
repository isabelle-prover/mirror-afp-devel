(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>The High-Level Interface to the Automata-Library\<close>

theory RegExpInterface
  imports "Functional-Automata.Execute"
  keywords
  "reflect_ML_exports" :: thy_decl

begin


text\<open> The implementation of the monitoring concept follows the following design decisions:
\<^enum> We re-use generated code from the AFP submissions @{theory "Regular-Sets.Regular_Set"} and 
  @{theory "Functional-Automata.Automata"}, converted by the code-generator into executable SML code
  (ports to future Isabelle versions should just reuse future versions of these)
\<^enum> Monitor-Expressions are regular expressions (in some adapted syntax) 
  over Document Class identifiers; they denote the language of all possible document object
  instances belonging to these classes
\<^enum> Instead of expanding the sub-class relation (and building the product automaton of all 
  monitor expressions), we convert the monitor expressions into automata over class-id's
  executed in parallel, in order to avoid blowup.
\<^enum> For efficiency reasons, the class-ids were internally abstracted to integers; the
  encoding table is called environment \<^verbatim>\<open>env\<close>.
\<^enum> For reusability reasons, we did NOT abstract the internal state representation in the
  deterministic automata construction (lists of lists of bits - sic !) by replacing them
  by unique keys via a suitable coding-table; rather, we opted for keeping the automatas small
  (no products, no subclass-expansion).
\<close>

section\<open>Monitor Syntax over RegExp - constructs\<close>

notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)

definition rep1 :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrace>(_)\<rbrace>\<^sup>+")
  where "\<lbrace>A\<rbrace>\<^sup>+ \<equiv>  A ~~ \<lbrace>A\<rbrace>\<^sup>*"
    
definition opt :: "'a rexp \<Rightarrow> 'a rexp" ("\<lbrakk>(_)\<rbrakk>")
   where "\<lbrakk>A\<rbrakk> \<equiv>  A || One"

value "Star (Conc(Alt (Atom(CHR ''a'')) (Atom(CHR ''b''))) (Atom(CHR ''c'')))"
text\<open>or better equivalently:\<close>
value "\<lbrace>(\<lfloor>CHR ''a''\<rfloor> || \<lfloor>CHR ''b''\<rfloor>) ~~ \<lfloor>CHR ''c''\<rfloor>\<rbrace>\<^sup>*"

section\<open>Some Standard and Derived Semantics\<close>
text\<open> This is just a reminder - already defined in @{theory "Regular-Sets.Regular_Exp"} 
as @{term lang}.\<close>

text\<open>In the following, we give a semantics for our regular expressions, which so far have
just been a term language (i.e. abstract syntax). The semantics is a ``denotational semantics'',
i.e. we give a direct meaning for regular expressions in some universe of ``denotations''. 

This universe of denotations is in our concrete case:\<close>

text\<open>Now the denotational semantics for regular expression can be defined on a post-card:\<close>

fun       Lang :: "'a rexp => 'a lang"
  where   L_Emp :   "Lang Zero        = {}"
         |L_One:    "Lang One         = {[]}"
         |L_Atom:   "Lang (\<lfloor>a\<rfloor>)       = {[a]}"
         |L_Un:     "Lang (el || er)  = (Lang el) \<union> (Lang er)"
         |L_Conc:   "Lang (el ~~ er)  = {xs@ys | xs ys. xs \<in> Lang el \<and> ys \<in> Lang er}"
         |L_Star:   "Lang (Star e)    = Regular_Set.star(Lang e)"


text\<open>A more useful definition is the sub-language - definition\<close>
fun       L\<^sub>s\<^sub>u\<^sub>b :: "'a::order rexp => 'a lang"
  where   L\<^sub>s\<^sub>u\<^sub>b_Emp:    "L\<^sub>s\<^sub>u\<^sub>b Zero        = {}"
         |L\<^sub>s\<^sub>u\<^sub>b_One:    "L\<^sub>s\<^sub>u\<^sub>b One         = {[]}"
         |L\<^sub>s\<^sub>u\<^sub>b_Atom:   "L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>a\<rfloor>)       = {z . \<forall>x. x \<le> a \<and> z=[x]}"
         |L\<^sub>s\<^sub>u\<^sub>b_Un:     "L\<^sub>s\<^sub>u\<^sub>b (el || er)  = (L\<^sub>s\<^sub>u\<^sub>b el) \<union> (L\<^sub>s\<^sub>u\<^sub>b er)"
         |L\<^sub>s\<^sub>u\<^sub>b_Conc:   "L\<^sub>s\<^sub>u\<^sub>b (el ~~ er)  = {xs@ys | xs ys. xs \<in> L\<^sub>s\<^sub>u\<^sub>b el \<and> ys \<in> L\<^sub>s\<^sub>u\<^sub>b er}"
         |L\<^sub>s\<^sub>u\<^sub>b_Star:   "L\<^sub>s\<^sub>u\<^sub>b (Star e)    = Regular_Set.star(L\<^sub>s\<^sub>u\<^sub>b e)"


definition XX where "XX = (rexp2na example_expression)"
definition YY where "YY = na2da(rexp2na example_expression)"
(* reminder from execute *)
value "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"
value "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"

section\<open>HOL - Adaptions and Export to SML\<close>

definition enabled :: "('a,'\<sigma> set)da  \<Rightarrow> '\<sigma> set \<Rightarrow> 'a list \<Rightarrow>  'a list" 
  where   "enabled A \<sigma> = filter (\<lambda>x. next A x \<sigma> \<noteq> {}) "


definition zero where "zero = (0::nat)"
definition one where "one = (1::nat)"

export_code   zero one Suc Int.nat  nat_of_integer int_of_integer  (* for debugging *)
             example_expression                                   (* for debugging *)

             Zero One     Atom     Plus  Times  Star              (* regexp abstract syntax *)

             rexp2na      na2da    enabled                        (* low-level automata interface *)
             NA.accepts   DA.accepts  
             in SML   module_name RegExpChecker 

subsection\<open>Infrastructure for Reflecting exported SML code\<close>
ML\<open>
  fun reflect_local_ML_exports args trans =  let
    fun eval_ML_context ctxt = let 
      fun is_sml_file f = String.isSuffix ".ML" (Path.implode (#path f))
      val files = (map (Generated_Files.check_files_in (Context.proof_of ctxt)) args) 
      val ml_files = filter is_sml_file (map #1 (maps Generated_Files.get_files_in files))
      val ml_content = map (fn f => Syntax.read_input (Bytes.content (#content f))) ml_files
      fun eval ml_content   = fold (fn sml => (ML_Context.exec 
                                           (fn () => ML_Context.eval_source ML_Compiler.flags sml))) 
                                   ml_content 
    in 
      (eval ml_content #> Local_Theory.propagate_ml_env) ctxt
    end
  in
    Toplevel.generic_theory eval_ML_context trans
  end


  val files_in_theory =
    (Parse.underscore >> K [] || Scan.repeat1 Parse.path_binding) --
      Scan.option (\<^keyword>\<open>(\<close> |-- Parse.!!! (\<^keyword>\<open>in\<close> 
                     |-- Parse.theory_name --| \<^keyword>\<open>)\<close>));

  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>reflect_ML_exports\<close> 
      "evaluate generated Standard ML files"
      (Parse.and_list1 files_in_theory  >> (fn args => reflect_local_ML_exports args));
\<close>



reflect_ML_exports _



section\<open>The Abstract Interface For Monitor Expressions\<close>
text\<open>Here comes the hic : The reflection of the HOL-Automata module into an SML module 
with an abstract interface hiding some generation artefacts like the internal states 
of the deterministic automata ...\<close>


ML\<open> 

structure RegExpInterface : sig
    type automaton
    type env 
    type cid
    val  alphabet    : term list -> env
    val  ext_alphabet: env -> term list -> env
    val  conv        : theory -> term -> env -> int RegExpChecker.rexp (* for debugging *)
    val  rexp_term2da: theory -> env -> term -> automaton
    val  enabled     : automaton -> env -> cid list  
    val  next        : automaton -> env -> cid -> automaton
    val  final       : automaton -> bool
    val  accepts     : automaton -> env -> cid list -> bool
  end
 =
struct
local open RegExpChecker in

  type state = bool list RegExpChecker.set
  type env = string list
  type cid = string

  type automaton = state * ((Int.int -> state -> state) * (state -> bool))

  val add_atom = fold_aterms (fn Const (c as (_, \<^Type>\<open>rexp _\<close>)) => insert (op=) c | _=> I);
  fun alphabet termS  =  rev(map fst (fold add_atom termS []));
  fun ext_alphabet env termS  =  
         let val res = rev(map fst (fold add_atom termS [])) @ env;
             val _ = if has_duplicates  (op=) res
                     then error("reject and accept alphabets must be disjoint!")
                     else ()
         in res end;

  fun conv _ \<^Const_>\<open>Regular_Exp.rexp.Zero _\<close> _ = Zero
     |conv _ \<^Const_>\<open>Regular_Exp.rexp.One _\<close> _ = Onea 
     |conv thy \<^Const_>\<open>Regular_Exp.rexp.Times _ for X Y\<close> env = Times(conv thy X env, conv thy Y env)
     |conv thy \<^Const_>\<open>Regular_Exp.rexp.Plus _ for X Y\<close> env = Plus(conv thy X env, conv thy Y env)
     |conv thy \<^Const_>\<open>Regular_Exp.rexp.Star _ for X\<close> env = Star(conv thy X env)
     |conv thy \<^Const_>\<open>RegExpInterface.opt _ for X\<close> env = Plus(conv thy X env, Onea)
     |conv thy \<^Const_>\<open>RegExpInterface.rep1 _ for X\<close> env = Times(conv thy X env, Star(conv thy X env))
     |conv _ (Const (s, \<^Type>\<open>rexp _\<close>)) env =
               let val n = find_index (fn x => x = s) env 
                   val _ = if n<0 then error"conversion error of regexp."  else ()
               in  Atom(n) end
     |conv thy S _ = error("conversion error of regexp:" ^ (Syntax.string_of_term_global thy S))

   val eq_int = {equal = curry(op =) : Int.int -> Int.int -> bool};
   val eq_bool_list = {equal = curry(op =) : bool list  -> bool list  -> bool};

   fun rexp_term2da thy env term = let val rexp = conv thy term env;
                                   val nda = RegExpChecker.rexp2na eq_int rexp;
                                   val da = RegExpChecker.na2da eq_bool_list nda;
                               in  da end;


   (* here comes the main interface of the module: 
      - "enabled" gives the part of the alphabet "env" for which the automatan does not
        go into a final state
      - next provides an automata transformation that produces an automaton that
        recognizes the rest of a word after a *)
   fun enabled (da as (state,(_,_))) env  = 
                              let val inds = RegExpChecker.enabled da state (0 upto (length env - 1))
                              in  map (fn i => nth env i) inds end

   fun next  (current_state, (step,fin)) env a =
                              let val index = find_index (fn x => x = a) env   
                              in  if index < 0 then error"undefined id for monitor"
                                  else (step index current_state,(step,fin))
                              end

   fun final (current_state, (_,fin)) = fin current_state

   fun accepts da env word = let fun index a = find_index (fn x => x = a) env   
                                 val indexL = map index word
                                 val _ = if forall (fn x => x >= 0) indexL then ()
                                         else error"undefined id for monitor"
                             in  RegExpChecker.accepts da indexL end

end; (* local *)
end  (* struct *)
\<close>

lemma regexp_sub : "a \<le> b \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>a\<rfloor>) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>b\<rfloor>)"
  using dual_order.trans by auto

lemma regexp_seq_mono:
      "Lang(a) \<subseteq> Lang (a') \<Longrightarrow> Lang(b) \<subseteq> Lang (b') \<Longrightarrow> Lang(a ~~ b) \<subseteq> Lang(a' ~~ b')"  by auto

lemma regexp_seq_mono':
      "L\<^sub>s\<^sub>u\<^sub>b(a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (a') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(a ~~ b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b(a' ~~ b')"  by auto

lemma regexp_alt_mono :"Lang(a) \<subseteq> Lang (a') \<Longrightarrow> Lang(a || b) \<subseteq> Lang(a' || b)"  by auto

lemma regexp_alt_mono' :"L\<^sub>s\<^sub>u\<^sub>b(a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (a') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(a || b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b(a' || b)"  by auto

lemma regexp_alt_commute : "Lang(a || b) = Lang(b || a)"  by auto

lemma regexp_alt_commute' : "L\<^sub>s\<^sub>u\<^sub>b(a || b) = L\<^sub>s\<^sub>u\<^sub>b(b || a)"  by auto

lemma regexp_unit_right : "Lang (a) = Lang (a ~~ One) " by simp 

lemma regexp_unit_right' : "L\<^sub>s\<^sub>u\<^sub>b (a) = L\<^sub>s\<^sub>u\<^sub>b (a ~~ One) " by simp 

lemma regexp_unit_left  : "Lang (a) = Lang (One ~~ a) " by simp 

lemma regexp_unit_left'  : "L\<^sub>s\<^sub>u\<^sub>b (a) = L\<^sub>s\<^sub>u\<^sub>b (One ~~ a) " by simp

lemma opt_star_incl :"Lang (opt a) \<subseteq> Lang (Star a)"  by (simp add: opt_def subset_iff)

lemma opt_star_incl':"L\<^sub>s\<^sub>u\<^sub>b (opt a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star a)"  by (simp add: opt_def subset_iff)

lemma rep1_star_incl:"Lang (rep1 a) \<subseteq> Lang (Star a)"
  unfolding rep1_def by(subst L_Star, subst L_Conc)(force)

lemma rep1_star_incl':"L\<^sub>s\<^sub>u\<^sub>b (rep1 a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star a)"
  unfolding rep1_def by(subst L\<^sub>s\<^sub>u\<^sub>b_Star, subst L\<^sub>s\<^sub>u\<^sub>b_Conc)(force)

lemma cancel_rep1 : "Lang (a) \<subseteq> Lang (rep1 a)"
  unfolding rep1_def by auto

lemma cancel_rep1' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (rep1 a)"
  unfolding rep1_def by auto

lemma seq_cancel_opt : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (opt b ~~ c)"
  by(subst regexp_unit_left, rule regexp_seq_mono)(simp_all add: opt_def)

lemma seq_cancel_opt' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (c) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (opt b ~~ c)"
  by(subst regexp_unit_left', rule regexp_seq_mono')(simp_all add: opt_def)

lemma seq_cancel_Star : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (Star b ~~ c)" 
  by auto

lemma seq_cancel_Star' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (c) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b ~~ c)" 
  by auto

lemma mono_Star : "Lang (a) \<subseteq> Lang (b) \<Longrightarrow> Lang (Star a) \<subseteq> Lang (Star b)" 
  by(auto)(metis in_star_iff_concat order.trans)

lemma mono_Star' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (Star a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b)" 
  by(auto)(metis in_star_iff_concat order.trans)

lemma mono_rep1_star:"Lang (a) \<subseteq> Lang (b) \<Longrightarrow> Lang (rep1 a) \<subseteq> Lang (Star b)"
  using mono_Star rep1_star_incl by blast

lemma mono_rep1_star':"L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (rep1 a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b)"
  using mono_Star' rep1_star_incl' by blast


no_notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
no_notation Plus  (infixr "||" 55)
no_notation Times (infixr "~~" 60)
no_notation Atom  ("\<lfloor>_\<rfloor>" 65)
no_notation rep1 ("\<lbrace>(_)\<rbrace>\<^sup>+")
no_notation opt  ("\<lbrakk>(_)\<rbrakk>")

ML\<open>
structure RegExpInterface_Notations =
struct
val Star = (\<^term>\<open>Regular_Exp.Star\<close>, Mixfix (Syntax.read_input "\<lbrace>(_)\<rbrace>\<^sup>*", [0], 100, Position.no_range))
val Plus = (\<^term>\<open>Regular_Exp.Plus\<close>, Infixr (Syntax.read_input "||", 55, Position.no_range))
val Times = (\<^term>\<open>Regular_Exp.Times\<close>, Infixr (Syntax.read_input "~~", 60, Position.no_range))
val Atom = (\<^term>\<open>Regular_Exp.Atom\<close>, Mixfix (Syntax.read_input "\<lfloor>_\<rfloor>", [], 65, Position.no_range))
val opt = (\<^term>\<open>RegExpInterface.opt\<close>, Mixfix (Syntax.read_input "\<lbrakk>(_)\<rbrakk>", [], 1000, Position.no_range))
val rep1 = (\<^term>\<open>RegExpInterface.rep1\<close>, Mixfix (Syntax.read_input "\<lbrace>(_)\<rbrace>\<^sup>+", [], 1000, Position.no_range))
val notations = [Star, Plus, Times, Atom, rep1, opt]
end
\<close>

end
  
