theory Natural_Functor \<^marker>\<open>contributor \<open>Balazs Toth\<close>\<close>
  imports Main
begin

locale natural_functor =
  fixes
    map :: "('a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'b" and
    to_set :: "'b \<Rightarrow> 'a set"
  assumes
    map_comp [simp]: "\<And>b f g. map f (map g b) = map (f o g) b" and
    map_ident [simp]: "\<And>b. map (\<lambda>x. x) b = b" and
    map_cong0 [cong]: "\<And>b f g. (\<And>a. a \<in> to_set b \<Longrightarrow> f a = g a) \<Longrightarrow> map f b = map g b" and
    to_set_map [simp]: "\<And>b f. to_set (map f b) = f ` to_set b"
begin

lemma map_comp' [simp]: "\<And>b f g. map f (map g b) = map (\<lambda>x. f (g x)) b"
  using map_comp
  by simp

lemma map_id [simp]: "map id b = b"
  using map_ident
  unfolding id_def .

lemma map_cong [cong]:
  assumes "b = b'" "\<And>a. a \<in> to_set b' \<Longrightarrow> f a = g a" 
  shows "map f b = map g b'"
  using map_cong0 assms
  by blast

lemma map_id_cong [simp]:
  assumes "\<And>a. a \<in> to_set b \<Longrightarrow> f a = a"
  shows "map f b = b"
  using assms
  by simp

lemma to_set_map_not_ident:
  assumes "a \<in> to_set b" "f a \<notin> to_set b"
  shows "map f b \<noteq> b"
  using assms
  by (metis rev_image_eqI to_set_map)

lemma map_in_to_set:
  assumes "map f b = b" "a \<in> to_set b"
  shows "f a \<in> to_set b"
  using assms 
  by (metis image_eqI to_set_map)

lemma to_set_const [simp]: "to_set b \<noteq> {} \<Longrightarrow> to_set (map (\<lambda>_. a) b) = {a}"
  by auto

lemma map_inverse: "(\<And>x. f (g x) = x) \<Longrightarrow> map f (map g b) = b"
  by simp

end

locale non_empty_natural_functor = natural_functor + 
  assumes exists_non_empty: "\<exists>b. to_set b \<noteq> {}"
begin

lemma exists_functor [intro]: "\<exists>b. a \<in> to_set b"
proof -

  obtain b where "to_set b \<noteq> {}"
    using exists_non_empty
    by blast

  then have "a \<in> to_set (map (\<lambda>_. a) b)"
    by auto
  
  then show ?thesis
    by blast
qed

end

locale finite_natural_functor = natural_functor +
  assumes finite_to_set [intro]: "\<And>b. finite (to_set b)"

locale non_empty_finite_natural_functor =
  non_empty_natural_functor + finite_natural_functor

(* TODO: Automate this as well *)
locale natural_functor_conversion =
  natural_functor +
  functor': natural_functor where map = map' and to_set = to_set'
  for map' :: "('b \<Rightarrow> 'b) \<Rightarrow> 'd \<Rightarrow> 'd" and to_set' :: "'d \<Rightarrow> 'b set" +
  fixes
    map_to :: "('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd" and
    map_from :: "('b \<Rightarrow> 'a) \<Rightarrow> 'd \<Rightarrow> 'c"
  assumes
    to_set_map_from [simp]: "\<And>f d. to_set (map_from f d) = f ` to_set' d" and
    to_set_map_to [simp]: "\<And>f c. to_set' (map_to f c) = f ` to_set c" and
    conversion_map_comp [simp]: "\<And>c f g. map_from f (map_to g c) = map (\<lambda>x. f (g x)) c" and
    conversion_map_comp' [simp]: "\<And>d f g. map_to f (map_from g d) = map' (\<lambda>x. f (g x)) d"

lemma non_empty_helper: "x \<in> to_set b \<Longrightarrow> \<exists>b. to_set b \<noteq> {}"
  by blast

ML \<open>
local

open BNF_Util;
open BNF_Def;
open BNF_Tactics;
open BNF_FP_Def_Sugar;

in

(* TODO: Is ignoring correct? *)
fun bnf_name_qualified bnf =
  (case T_of_bnf bnf of
     Type (name, _) => SOME name
   | _ => NONE)

structure Natural_Functor_Ignore :
sig
  val add_ignore : string -> theory -> theory
  val is_ignored : bnf -> Proof.context -> bool
end = struct

structure Data = Generic_Data
(
  type T = Symtab.set
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun add_ignore name thy =
  Context.theory_map (Data.map (Symtab.insert_set name)) thy

fun is_ignored bnf ctxt =
  (case bnf_name_qualified bnf of
     SOME name => Symtab.defined (Data.get (Context.Proof ctxt)) name
   | NONE => false)

end


(* TODO: Improve printing (done is sometimes wrong) *)
fun method_template name methods = Method.Basic (fn ctxt => METHOD (fn thms =>
  TRY (EVERY1 ([
    K (print_tac ctxt ("Interpreting " ^ name)),
    K (Locale.intro_locales_tac {strict = false, eager = true} ctxt thms)] @
    methods ctxt @
    [K (print_tac ctxt "done")]))))

fun method_base bnf name = method_template name (fn ctxt => [
  K (print_tac ctxt "map_comp"),
  rtac ctxt (map_comp_of_bnf bnf RS trans),
  SELECT_GOAL (unfold_thms_tac ctxt @{thms comp_def id_o o_id}),
  rtac ctxt refl,
  K (print_tac ctxt "map_ident"),
  rtac ctxt (map_ident_of_bnf bnf),
  K (print_tac ctxt "map_cong"),
  rtac ctxt (map_cong0_of_bnf bnf)
    THEN_ALL_NEW (Goal.assume_rule_tac ctxt ORELSE' rtac ctxt refl),
  K (print_tac ctxt "set_map"),
  resolve_tac ctxt (set_map_of_bnf bnf)])

fun method_non_empty (fp_sugar: fp_sugar) name =
  let
    val set_introssss = #set_introssss (#fp_bnf_sugar fp_sugar);
    val set_intros = flat (flat (flat set_introssss));
  in
    method_template name (fn ctxt =>
      [K (print_tac ctxt "non_empty"),
      rtac ctxt @{thm non_empty_helper},
      resolve_tac ctxt set_intros])
  end;

fun method_finite bnf name = (case set_finite_of_bnf bnf of
    NONE => Method.Basic (K (METHOD (K no_tac)))
  | SOME set_finite =>
    method_template name (fn ctxt => [
      K (print_tac ctxt "finite"),
      resolve_tac ctxt set_finite]))

fun interpret locale method bnf lthy =
  let
    fun interpret i map set lthy =
      let
        val index = if i <= 1 then "" else string_of_int i
        (* TODO: Check for name clashes (Like for inference) *)
        val name = Binding.name_of (name_of_bnf bnf) ^ "_functor" ^ index
        val expression = (Expression.Positional [SOME map, SOME set], [])
    
        val state = 
          Interpretation.isar_interpretation ([(locale, ((name, true), expression))], []) lthy;
    
        val lthy =
          Proof.global_terminal_proof ((method name, Position.no_range), NONE) state 
            handle ERROR _ => (tracing ("Could not interpret " ^ name) ; lthy);
    
       in lthy end;
   
    val live = live_of_bnf bnf
    and deads = deads_of_bnf bnf;

    val ((As, unsorted_Ds), _) = lthy
      |> mk_TFrees live
      ||>> mk_TFrees (length deads);
    val Ds = map2 (resort_tfree_or_tvar o Type.sort_of_atyp) deads unsorted_Ds;

    fun mk_map i =
      let
        val map_all = mk_map_of_bnf Ds As As bnf;
        fun id A = Abs ("x", A, Bound 0);
        val args = map_index (fn (j, A) => if i = j then Bound 0 else id A) As;
        val term = list_comb (map_all, args);
      in Abs ("x", nth As i --> nth As i, term) end

    val maps = map mk_map (0 upto live - 1);
    val sets = mk_sets_of_bnf (replicate live Ds) (replicate live As) bnf;

  in 
    if Natural_Functor_Ignore.is_ignored bnf (Local_Theory.target_of lthy)
    then lthy
    else @{fold 3} interpret (1 upto live) maps sets lthy
  end;

val natural_functor_setup =
  let
    val description = "interpret natural functor locale for BNFs";

    fun interpretation bnf = interpret @{locale natural_functor} (method_base bnf) bnf;

  in bnf_interpretation description interpretation end;

val non_empty_natural_functor_setup =
  let
    val description = "interpret nonempty natural functor locale for BNFs";

    fun interpretation sugar =
      interpret @{locale non_empty_natural_functor} (method_non_empty sugar) (#fp_bnf sugar);

  in fp_sugars_interpretation description (fold interpretation) end;
                               
val finite_natural_functor_setup =
  let
    val description = "interpret finite natural functor locale for BNFs";

    fun interpretation bnf = interpret @{locale finite_natural_functor} (method_finite bnf) bnf;

  in bnf_interpretation description interpretation end;

val natural_functor_setups =
  natural_functor_setup
  #> non_empty_natural_functor_setup
  #> finite_natural_functor_setup

fun natural_functor_ignore type_name =
  Natural_Functor_Ignore.add_ignore type_name

end\<close>


end
