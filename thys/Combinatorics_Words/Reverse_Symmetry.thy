(*  Title:      CoW/Reverse_Symmetry.thy
    Author:     Martin Raška, Charles University

Part of Combinatorics on Words Formalized. See https://gitlab.com/formalcow/combinatorics-on-words-formalized/
*)

theory Reverse_Symmetry
  imports Main
begin

chapter "Reverse symmetry"

text \<open>This theory deals with a mechanism which produces new facts on lists from already known facts
by the reverse symmetry of lists, induced by the mapping @{term rev}.
It constructs the rule attribute ``reversed'' which produces the symmetrical fact using so-called
reversal rules, which are rewriting rules that may be applied to obtain the symmetrical fact.
An example of such a reversal rule is the already existing @{thm rev_append[symmetric, no_vars]}.
Some additional reversal rules are given in this theory.

The symmetrical fact 'A[reversed]' is constructed from the fact 'A' in the following manner:
  1. each schematic variable @{term "xs::'a list"} of type @{typ "'a list"}
is instantiated by @{term "rev xs"};
  2. constant Nil is substituted by @{term "rev Nil"};
  3. each quantification of @{typ "'a list"} type variable @{term "\<And>(xs::'a list). P xs"}
is substituted by (logically equivalent) quantification @{term "\<And>xs. P (rev xs)"},
similarly for $\forall$, $\exists$ and $\exists!$ quantifiers; each bounded quantification of @{typ "'a list"} type
variable @{term "\<forall>(xs::'a list) \<in> A. P xs"} is substituted by (logically equivalent)
quantification @{term "\<forall>xs\<in>rev ` A. P (rev xs)"}, similarly for bounded $\exists$ quantifier;
  4. simultaneous rewrites according to a the current list of reversal rules are performed;
  5. final correctional rewrites related to reversion of @{const "Cons"} are performed.

List of reversal rules is maintained by declaration attribute ``reversal\_rule'' with standard
``add'' and ``del'' options.

See examples at the end of the file.
\<close>


section \<open>Quantifications and maps\<close>

lemma all_surj_conv: assumes "surj f" shows "(\<And>x. PROP P (f x)) \<equiv> (\<And>y. PROP P y)"
proof
  fix y assume "\<And>x. PROP P (f x)"
  then have "PROP P (f (inv f y))".
  then show "PROP P y" unfolding surj_f_inv_f[OF assms].
qed

lemma All_surj_conv: assumes "surj f" shows "(\<forall>x. P (f x)) \<longleftrightarrow> (\<forall>y. P y)"
proof (intro iffI allI)
  fix y assume "\<forall>x. P (f x)"
  then have "P (f (inv f y))"..
  then show "P y" unfolding surj_f_inv_f[OF assms].
qed simp

lemma Ex_surj_conv: assumes "surj f" shows "(\<exists>x. P (f x)) \<longleftrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then obtain x where "P (f x)"..
  then show "\<exists>x. P x"..
next
  assume "\<exists>y. P y"
  then obtain y where "P y"..
  then have "P (f (inv f y))" unfolding surj_f_inv_f[OF assms].
  then show "\<exists>x. P (f x)"..
qed

lemma Ex1_bij_conv: assumes "bij f" shows "(\<exists>!x. P (f x)) \<longleftrightarrow> (\<exists>!y. P y)"
proof
  have imp: "\<exists>!y. Q y" if bij: "bij g" and ex1: "\<exists>!x. Q (g x)" for g Q
  proof -
    from ex1E[OF ex1, rule_format]
    obtain x where ex: "Q (g x)" and uniq: "\<And>x'. Q (g x') \<Longrightarrow> x' = x" by blast
    {
      fix y assume "Q y"
      then have "Q (g (inv g y))" unfolding surj_f_inv_f[OF bij_is_surj[OF bij]].
      from uniq[OF this] have "x = inv g y"..
      then have "y = g x" unfolding bij_inv_eq_iff[OF bij]..
    }
    with ex show "\<exists>!y. Q y"..
  qed
  show "\<exists>!x. P (f x) \<Longrightarrow> \<exists>!y. P y" using imp[OF assms].
  assume "\<exists>!y. P y"
  then have "\<exists>!y. P (f (inv f y))" unfolding surj_f_inv_f[OF bij_is_surj[OF assms]].
  from imp[OF bij_imp_bij_inv[OF assms] this]
  show "\<exists>!x. P (f x)".
qed

lemma Ball_inj_conv: assumes "inj f" shows "(\<forall>y\<in>f ` A. P (inv f y)) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
  using ball_simps(9)[of f A "\<lambda>y. P (inv f y)"] unfolding inv_f_f[OF assms].

lemma Bex_inj_conv: assumes "inj f" shows "(\<exists>y\<in>f ` A. P (inv f y)) \<longleftrightarrow> (\<exists>x\<in>A. P x)"
  using bex_simps(7)[of f A "\<lambda>y. P (inv f y)"] unfolding inv_f_f[OF assms].

subsection \<open>Quantifications and reverse\<close>

lemma rev_involution': "rev \<circ> rev = id"
  by auto

lemma rev_inv: "inv rev = rev"
  using inv_unique_comp[OF rev_involution' rev_involution'].

section \<open>Attributes\<close>

context
begin

subsection \<open>Cons reversion\<close>

definition snocs :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "snocs xs ys  = xs @ ys"

subsection \<open>Final corrections\<close>

lemma snocs_snocs: "snocs (snocs xs (y # ys)) zs = snocs xs (y # snocs ys zs)"
  unfolding snocs_def by simp

lemma snocs_Nil: "snocs [] xs = xs"
  unfolding snocs_def by simp

lemma snocs_is_append: "snocs xs ys = xs @ ys"
  unfolding snocs_def..

private lemmas final_correct1 =
  snocs_snocs

private lemmas final_correct2 =
  snocs_Nil

private lemmas final_correct3 =
  snocs_is_append

subsection \<open>Declaration attribute \<open>reversal_rule\<close>\<close>

ML \<open>
structure Reversal_Rules =
  Named_Thms(
    val name = @{binding "reversal_rule"}
    val description = "Rules performing reverse-symmetry transformation on theorems on lists"
  )
\<close>

attribute_setup reversal_rule =
  \<open>Attrib.add_del
    (Thm.declaration_attribute Reversal_Rules.add_thm)
    (Thm.declaration_attribute Reversal_Rules.del_thm)\<close>
  "maintaining a list of reversal rules"

subsection \<open>Tracing attribute\<close>

ML \<open>
  val reversed_trace = Config.declare_bool ("reversed_trace", \<^here>) (K false);
  val enable_tracing = Config.put_generic reversed_trace true
  val tracing_attr = Thm.declaration_attribute (K enable_tracing)
  val tracing_parser : attribute context_parser = Scan.lift (Scan.succeed tracing_attr)
\<close>

attribute_setup reversed_trace = tracing_parser "reversed trace configuration"

subsection \<open>Rule attribute \<open>reversed\<close>\<close>

private lemma rev_Nil: "rev [] \<equiv> []"
  by simp

private lemma map_Nil: "map f [] \<equiv> []"
  by simp

private lemma image_empty: "f ` Set.empty \<equiv> Set.empty"
  by simp

definition COMP :: "('b \<Rightarrow> prop) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> prop" (infixl "oo" 55)
  where "F oo g \<equiv> (\<lambda>x. F (g x))"

lemma COMP_assoc: "F oo (f o g) \<equiv> (F oo f) oo g"
  unfolding COMP_def o_def.

private lemma image_comp_image: "(`) f \<circ> (`) g \<equiv> (`) (f \<circ> g)"
  unfolding comp_def image_comp.

private lemma rev_involution: "rev \<circ> rev \<equiv> id"
  unfolding comp_def rev_rev_ident id_def.

private lemma map_involution: assumes "f \<circ> f \<equiv> id" shows "(map f) \<circ> (map f) \<equiv> id"
  unfolding map_comp_map \<open>f \<circ> f \<equiv> id\<close> List.map.id.

private lemma image_involution: assumes "f \<circ> f \<equiv> id" shows "(image f) \<circ> (image f) \<equiv> id"
  unfolding image_comp_image \<open>f \<circ> f \<equiv> id\<close> image_id.

private lemma rev_map_comm: "rev \<circ> map f \<equiv> map f \<circ> rev"
  unfolding comp_def rev_map.

private lemma involut_comm_comp: assumes "f o f \<equiv> id" and "g o g \<equiv> id" and "f o g \<equiv> g o f"
  shows "(f \<circ> g) \<circ> (f \<circ> g) \<equiv> id"
  by (simp add: comp_assoc comp_assoc[symmetric] assms)

private lemma rev_map_involution: assumes "g o g \<equiv> id"
  shows "(rev \<circ> map g) \<circ> (rev \<circ> map g) \<equiv> id"
  using involut_comm_comp[OF rev_involution map_involution[OF \<open>g o g \<equiv> id\<close>] rev_map_comm].

private lemma prop_abs_subst: assumes "f o f \<equiv> id" shows "(\<lambda>x. F (f x)) oo f \<equiv> (\<lambda>x. F x)"
  unfolding COMP_def o_apply[symmetric] unfolding \<open>f o f \<equiv> id\<close> id_def.

private lemma prop_abs_subst_comm: assumes "f o f \<equiv> id" and "g o g \<equiv> id" and "f o g \<equiv> g o f"
  shows "(\<lambda>x. F (f (g x))) oo (f o g) \<equiv> (\<lambda>x. F x)"
  unfolding \<open>f o g \<equiv> g o f\<close> unfolding COMP_assoc
  unfolding prop_abs_subst[OF \<open>g o g \<equiv> id\<close>, of "\<lambda>x. F (f x)"] prop_abs_subst[OF \<open>f o f \<equiv> id\<close>].

private lemma prop_abs_subst_rev_map: assumes "g o g \<equiv> id"
  shows "(\<lambda>x. F (rev (map g x))) oo (rev o map g) \<equiv> (\<lambda>x. F x)"
  using prop_abs_subst_comm[OF rev_involution map_involution[OF \<open>g o g \<equiv> id\<close>] rev_map_comm].

private lemma obj_abs_subst: assumes "f o f \<equiv> id" shows "(\<lambda>x. F (f x)) o f \<equiv> (\<lambda>x. F x)"
  unfolding comp_def unfolding o_apply[of f, symmetric] \<open>f o f \<equiv> id\<close> id_def.

private lemma obj_abs_subst_comm: assumes "f o f \<equiv> id" and "g o g \<equiv> id" and "f o g \<equiv> g o f"
  shows "(\<lambda>x. F (f (g x))) o (f o g) \<equiv> (\<lambda>x. F x)"
  unfolding \<open>f o g \<equiv> g o f\<close> unfolding comp_assoc[symmetric]
  unfolding obj_abs_subst[OF \<open>g o g \<equiv> id\<close>, of "\<lambda>x. F (f x)"] obj_abs_subst[OF \<open>f o f \<equiv> id\<close>].

private lemma obj_abs_subst_rev_map: assumes "g o g \<equiv> id"
  shows "(\<lambda>x. F (rev (map g x))) o (rev o map g) \<equiv> (\<lambda>x. F x)"
  using obj_abs_subst_comm[OF rev_involution map_involution[OF \<open>g o g \<equiv> id\<close>] rev_map_comm].

ML \<open>

local
  fun comp_const T = Const(\<^const_name>\<open>comp\<close>, (T --> T) --> (T --> T) --> T --> T)
  fun rev_const T = Const(\<^const_name>\<open>rev\<close>, T --> T)
  fun map_const S T = Const(\<^const_name>\<open>map\<close>, (S --> S) --> T --> T)
  fun image_const S T = Const(\<^const_name>\<open>image\<close>, (S --> S) --> T --> T)

  val rev_Nil_thm = @{thm rev_Nil}
  val map_Nil_thm = @{thm map_Nil}
  val image_empty_thm = @{thm image_empty}
  val rev_involut_thm = @{thm rev_involution}
  val map_involut_thm = @{thm map_involution}
  val image_involut_thm = @{thm image_involution}
  val rev_map_comm_thm = @{thm rev_map_comm}
  val involut_comm_comp_thm = @{thm involut_comm_comp}
  fun abs_subst_thm T =
    if T = propT then @{thm prop_abs_subst} else @{thm obj_abs_subst}
  fun abs_subst_rev_map_thm T =
    if T = propT then @{thm prop_abs_subst_rev_map} else @{thm obj_abs_subst_rev_map}

  fun comp T f gs = fold (fn f => fn g =>
        (comp_const T $ f $ g)) gs f
  fun app ctxt gs ct = fold_rev (fn g => fn ct' =>
        Thm.apply (Thm.cterm_of ctxt g) ct') gs ct
in

  fun subst ctxt T ct =
    let
      fun tr (T as Type(\<^type_name>\<open>list\<close>, [S])) = [rev_const T] @ (
          case tr S of
            [] => []
          | (g :: gs') => [map_const S T $ comp S g gs'])
        | tr (T as Type(\<^type_name>\<open>set\<close>, [S])) = (
          case tr S of
            [] => []
          | (g :: gs') => [image_const S T $ comp S g gs'])
        | tr _ = []
    in app ctxt (tr T) ct end

  fun abs_cv T U ct =
    let
      fun tr_eq (T as Type(\<^type_name>\<open>list\<close>, [S])) =
            rev_involut_thm :: (
            case tr_eq S of
              [] => []
            | [f_eq] => [f_eq RS map_involut_thm]
            | [f_eq, g_eq] =>
                [([f_eq, g_eq, rev_map_comm_thm] MRS involut_comm_comp_thm) RS map_involut_thm])
        | tr_eq (T as Type(\<^type_name>\<open>set\<close>, [S])) = (
            case tr_eq S of
              [] => []
            | [f_eq] => [f_eq RS image_involut_thm]
            | [f_eq, g_eq] =>
                [([f_eq, g_eq, rev_map_comm_thm] MRS involut_comm_comp_thm) RS image_involut_thm])
        | tr_eq _ = []
    in case tr_eq T of
      [] => Thm.reflexive ct
    | [f_inv] =>
        [Thm.reflexive ct, Thm.symmetric (f_inv RS abs_subst_thm U)] MRS transitive_thm
    | [f_inv, g_inv] =>
        [Thm.reflexive ct, Thm.symmetric (g_inv RS abs_subst_rev_map_thm U)] MRS transitive_thm
    end;

  fun Nil_cv ctxt T ct =
    ((Conv.try_conv o Conv.arg_conv o Conv.rewr_conv) map_Nil_thm
    then_conv (Conv.try_conv o Conv.rewr_conv) rev_Nil_thm) (subst ctxt T ct)
      |> Thm.symmetric

  fun empty_cv ctxt T ct =
    (Conv.try_conv o Conv.rewr_conv) image_empty_thm (subst ctxt T ct)
      |> Thm.symmetric

end

fun initiate_cv ctxt ct =
  case Thm.term_of ct of
    _ $ _ => Conv.comb_conv (initiate_cv ctxt) ct
  | Abs(_, T, b) => (Conv.abs_conv (initiate_cv o snd) ctxt then_conv abs_cv T (fastype_of b)) ct
  | Const(\<^const_name>\<open>Nil\<close>, T) => Nil_cv ctxt T ct
  | Const(\<^const_name>\<open>bot\<close>, T as Type(\<^type_name>\<open>set\<close>, _)) => empty_cv ctxt T ct
  | _ => Thm.reflexive ct
\<close>

ML \<open>

fun trace_rule_prems_proof ctxt rule goals rule_prems rule' =
  if not (Config.get ctxt reversed_trace) then () else
    let
      val ctxt_prems = Raw_Simplifier.prems_of ctxt
      val np = Thm.nprems_of rule
      val np' = Thm.nprems_of rule'
      val pretty_term = Syntax.pretty_term ctxt
      val pretty_thm = pretty_term o Thm.prop_of
      val success = rule_prems |> List.all is_some
      val sendback = Active.make_markup Markup.sendbackN
        {implicit = false, properties = [Markup.padding_command]}
      val _ = [
        [
          "Trying to use conditional reverse rule:" |> Pretty.para,
          rule |> pretty_thm
        ] |> Pretty.fbreaks |> Pretty.block,
        [(if null ctxt_prems
          then "No context premises."
          else "Context premises:"
         ) |> Pretty.para
        ] @ (
          ctxt_prems |> map (Pretty.item o single o pretty_thm)
        ) |> Pretty.fbreaks |> Pretty.block,
        ( if success then [
          "Successfully derived unconditional reverse rule:" |> Pretty.para,
          rule' |> pretty_thm
        ] else [
          "Unable to prove " ^ string_of_int np ^ " out of " ^ string_of_int np' ^ " rule premises:\n"
            |> Pretty.para
        ] @ (
          (goals ~~ rule_prems) |> map_filter (
            fn (goal, NONE) => SOME ([
                "lemma" |> Pretty.str, Pretty.brk 1,
                goal |> pretty_term |> Pretty.quote, Pretty.fbrk,
                "sorry" |> Pretty.str
              ] |> curry Pretty.blk 0 |> Pretty.mark sendback |> single |> Pretty.item)
            | _ => NONE
          )
        )) |> Pretty.fbreaks |> Pretty.block
      ] |> Pretty.chunks |> Pretty.string_of |> tracing
    in () end

fun full_resolve ctxt prem i =
  let
    val tac = resolve_tac ctxt [prem] THEN_ALL_NEW blast_tac ctxt
  in rule_by_tactic ctxt (tac i) end

fun prover method ss ctxt rule =
  let
    val ctxt_prems = Raw_Simplifier.prems_of ctxt
    val rule_prems' = Logic.strip_imp_prems (Thm.prop_of rule)
    val goals = rule_prems' |> map (fn prem =>
      Logic.list_implies (map Thm.prop_of ctxt_prems, prem));
    val ctxt' = ctxt |> put_simpset ss
    fun prove t = SOME (Goal.prove ctxt' [] [] t
      (fn {context = goal_ctxt, prems} => NO_CONTEXT_TACTIC goal_ctxt (method goal_ctxt prems)))
      handle ERROR _ =>  NONE
    val ths = goals |> map prove
    val gen_ctxt_prems = map (Variable.gen_all ctxt) ctxt_prems
    fun full_resolve1 prem = full_resolve ctxt prem 1
    val rule_prems = ths |> (map o Option.map) (fold full_resolve1 gen_ctxt_prems)
    val rule' = (fold o curry) (
      fn (SOME th, rule') => rule' |> full_resolve1 th
      | (NONE, rule') => Drule.rotate_prems 1 rule'
      ) rule_prems rule
    val nprems = Thm.nprems_of rule'
    val _ = trace_rule_prems_proof ctxt rule goals rule_prems rule'
  in if nprems = 0 then SOME rule' else NONE end

fun rewrite _ _ [] = Thm.reflexive
  | rewrite method ctxt thms =
      let
        val p = prover method (simpset_of ctxt)
        val ctxt' = Raw_Simplifier.init_simpset thms ctxt
      in
        Raw_Simplifier.rewrite_cterm (true, true, true) p ctxt'
      end

fun rewrite_rule method ctxt = Conv.fconv_rule o rewrite method ctxt;

fun meta_reversal_rules ctxt extra =
  map (Local_Defs.meta_rewrite_rule ctxt) (extra @ Reversal_Rules.get ctxt)

fun reverse method extra_rules context th =
  let
    val ctxt = Context.proof_of context
    val final_correct1 = map (Local_Defs.meta_rewrite_rule ctxt) @{thms final_correct1}
    val final_correct2 = map (Local_Defs.meta_rewrite_rule ctxt) @{thms final_correct2}
    val final_correct3 = map (Local_Defs.meta_rewrite_rule ctxt) @{thms final_correct3}
    val rules = meta_reversal_rules ctxt extra_rules
    val cvars = Thm.add_vars th Vars.empty
    val cvars' = Vars.map ((subst ctxt o snd)) cvars
    val th_subst = Thm.instantiate (TVars.empty, cvars') th
    val ((_, [th_import]), ctxt') = Variable.import true [th_subst] ctxt
    val th_init = th_import |> Conv.fconv_rule (initiate_cv ctxt')
    val th_rev = th_init |> rewrite_rule method ctxt' rules
    val th_corr = th_rev
          |> Raw_Simplifier.rewrite_rule ctxt' final_correct1
          |> Raw_Simplifier.rewrite_rule ctxt' final_correct2
          |> Raw_Simplifier.rewrite_rule ctxt' final_correct3
    val th_export = th_corr |> singleton (Variable.export ctxt' ctxt)
  in
    Drule.zero_var_indexes th_export
  end

val default_method = SIMPLE_METHOD o CHANGED_PROP o auto_tac

val solve_arg = Args.$$$ "solve"

val extra_rules_parser = Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Attrib.thms) []

val solve_parser = Scan.lift (Scan.optional
    (solve_arg -- Args.colon |-- Method.parse >> (fst #> Method.evaluate)) default_method
  )

val reversed = extra_rules_parser -- solve_parser
  >> (fn (ths, method) => Thm.rule_attribute [] (reverse method ths))
\<close>

attribute_setup reversed =
  \<open>reversed\<close>
  "Transforms the theorem on lists to reverse-symmetric version"

end

section \<open>Declaration of basic reversal rules\<close>

subsection \<open>Pure\<close>

  \<comment> \<open>\<^const>\<open>Pure.all\<close>\<close>
lemma all_surj_conv' [reversal_rule]: assumes "surj f" shows "Pure.all (P oo f) \<equiv> Pure.all P"
  unfolding COMP_def using all_surj_conv[OF assms].

subsection \<open>\<^theory>\<open>HOL.HOL\<close>\<close>

  \<comment> \<open>\<^const>\<open>HOL.eq\<close>\<close>
lemmas [reversal_rule] = rev_is_rev_conv inj_eq

  \<comment> \<open>\<^const>\<open>All\<close>\<close>
lemma All_surj_conv' [reversal_rule]: assumes "surj f" shows "All (P o f) = All P"
  unfolding comp_def using All_surj_conv[OF assms].

  \<comment> \<open>\<^const>\<open>Ex\<close>\<close>
lemma Ex_surj_conv' [reversal_rule]: assumes "surj f" shows "Ex (P o f) \<longleftrightarrow> Ex P"
  unfolding comp_def using Ex_surj_conv[OF assms].

  \<comment> \<open>\<^const>\<open>Ex1\<close>\<close>
lemma Ex1_bij_conv' [reversal_rule]: assumes "bij f" shows "Ex1 (P o f) \<longleftrightarrow> Ex1 P"
  unfolding comp_def using Ex1_bij_conv[OF assms].

  \<comment> \<open>\<^const>\<open>If\<close>\<close>
lemma if_image [reversal_rule]: "(if P then f u else f v) = f (if P then u else v)"
  by simp

subsection \<open>\<^theory>\<open>HOL.Set\<close>\<close>

  \<comment> \<open>\<^const>\<open>Collect\<close>\<close>
lemma collect_image: "Collect (P \<circ> f) = f -` (Collect P)"
  by fastforce

lemma collect_image' [reversal_rule]: assumes "f \<circ> f = id" shows "Collect (P \<circ> f) = f ` (Collect P)"
  unfolding collect_image
  unfolding bij_vimage_eq_inv_image[OF o_bij[OF assms assms]]
  unfolding inv_unique_comp[OF assms assms]..

  \<comment> \<open>\<^const>\<open>Ball\<close>\<close>
lemma Ball_image [reversal_rule]: assumes "(g \<circ> f) ` A = A" shows "Ball (f ` A) (P \<circ> g) = Ball A P"
  unfolding Ball_image_comp[symmetric] image_comp \<open>(g \<circ> f) ` A = A\<close>..

  \<comment> \<open>\<^const>\<open>Bex\<close>\<close>
lemma Bex_image_comp: "Bex (f ` A) g = Bex A (g \<circ> f)"
  by simp

lemma Bex_image [reversal_rule]: assumes "(g \<circ> f) ` A = A" shows "Bex (f ` A) (P \<circ> g) = Bex A P"
  unfolding Bex_image_comp[symmetric] image_comp \<open>(g \<circ> f) ` A = A\<close>..

  \<comment> \<open>\<^const>\<open>insert\<close>\<close>
lemma insert_image [reversal_rule]: "insert (f x) (f ` X) = f ` (insert x X)"
  by blast

  \<comment> \<open>\<^const>\<open>List.member\<close>\<close>
lemmas [reversal_rule] = inj_image_mem_iff

  \<comment> \<open>\<^const>\<open>subset_eq\<close>\<close>
lemmas [reversal_rule] = inj_image_subset_iff

subsection \<open>\<^theory>\<open>HOL.List\<close>\<close>

  \<comment> \<open>\<^const>\<open>set\<close>\<close>
lemmas [reversal_rule] = set_rev set_map

  \<comment> \<open>\<^const>\<open>Cons\<close>\<close>
lemma Cons_rev: "a # rev u = rev (snocs u [a])"
  unfolding snocs_def by simp

lemma Cons_map: "(f x) # (map f xs) = map f (x # xs)"
  using list.simps(9)[symmetric].

lemmas [reversal_rule] = Cons_rev Cons_map

  \<comment> \<open>\<^const>\<open>hd\<close>\<close>
lemmas [reversal_rule] = hd_rev hd_map

  \<comment> \<open>\<^const>\<open>tl\<close>\<close>
lemma tl_rev: "tl (rev xs) = rev (butlast xs)"
  using butlast_rev[of "rev xs", symmetric] unfolding rev_swap rev_rev_ident.

lemmas [reversal_rule] = tl_rev map_tl[symmetric]

  \<comment> \<open>\<^const>\<open>last\<close>\<close>
lemmas [reversal_rule] = last_rev last_map

  \<comment> \<open>\<^const>\<open>butlast\<close>\<close>
lemmas [reversal_rule] = butlast_rev map_butlast[symmetric]

  \<comment> \<open>\<^const>\<open>List.coset\<close>\<close>
lemma coset_rev: "List.coset (rev xs) = List.coset xs"
  by simp

lemma coset_map: assumes "bij f" shows "List.coset (map f xs) =  f ` List.coset xs"
  using bij_image_Compl_eq[OF \<open>bij f\<close>, symmetric] unfolding coset_def set_map.

lemmas [reversal_rule] = coset_rev coset_map

  \<comment> \<open>\<^const>\<open>append\<close>\<close>
lemmas [reversal_rule] = rev_append[symmetric] map_append[symmetric]

  \<comment> \<open>\<^const>\<open>concat\<close>\<close>
lemma concat_rev_map_rev: "concat (rev (map rev xs)) = rev (concat xs)"
  using rev_concat[symmetric] unfolding rev_map.

lemma concat_rev_map_rev': "concat (rev (map (rev \<circ> f) xs)) = rev (concat (map f xs))"
  unfolding map_comp_map[symmetric] o_apply using concat_rev_map_rev.

lemmas [reversal_rule] = concat_rev_map_rev concat_rev_map_rev'

  \<comment> \<open>\<^const>\<open>drop\<close>\<close>
lemmas [reversal_rule] = drop_rev drop_map

  \<comment> \<open>\<^const>\<open>take\<close>\<close>
lemmas [reversal_rule] = take_rev take_map

  \<comment> \<open>\<^const>\<open>nth\<close>\<close>
lemmas [reversal_rule] = rev_nth nth_map

  \<comment> \<open>\<^const>\<open>List.insert\<close>\<close>
lemma list_insert_map [reversal_rule]:
  assumes "inj f" shows "List.insert (f  x) (map f xs) = map f (List.insert x xs)"
  unfolding List.insert_def set_map inj_image_mem_iff[OF \<open>inj f\<close>] Cons_map if_image..

  \<comment> \<open>\<^const>\<open>List.union\<close>\<close>
lemma list_union_map [reversal_rule]:
  assumes "inj f" shows "List.union (map f xs) (map f ys) = map f (List.union xs ys)"
proof (induction xs arbitrary: ys)
  case (Cons a xs)
  show ?case using Cons.IH unfolding List.union_def Cons_map[symmetric] fold.simps(2) o_apply
    unfolding list_insert_map[OF \<open>inj f\<close>].
qed (simp add: List.union_def)

  \<comment> \<open>\<^const>\<open>length\<close>\<close>
lemmas [reversal_rule] = length_rev length_map

  \<comment> \<open>\<^const>\<open>rotate\<close>\<close>
lemmas [reversal_rule] = rotate_rev rotate_map

  \<comment> \<open>\<^const>\<open>lists\<close>\<close>
lemma rev_in_lists: "rev u \<in> lists A \<longleftrightarrow> u \<in> lists A"
  by auto

lemma map_in_lists: "inj f \<Longrightarrow> map f u \<in> lists (f ` A) \<longleftrightarrow> u \<in> lists A"
  by (simp add: lists_image inj_image_mem_iff inj_mapI)

lemmas [reversal_rule] = rev_in_lists map_in_lists

  \<comment> \<open>\<^const>\<open>list_all\<close>\<close>
lemmas [reversal_rule] = list_all_rev

  \<comment> \<open>\<^const>\<open>list_ex\<close>\<close>
lemmas [reversal_rule] = list_ex_rev

subsection \<open>Reverse Symmetry\<close>

  \<comment> \<open>\<^const>\<open>snocs\<close>\<close>
lemma snocs_map [reversal_rule]: "snocs (map f u) [f a] = map f (snocs u [a])"
  unfolding snocs_def by simp

section \<open>\<close>

lemma bij_rev: "bij rev"
  using o_bij[OF rev_involution' rev_involution'].

lemma bij_map: "bij f \<Longrightarrow> bij (map f)"
  using bij_betw_def inj_mapI lists_UNIV lists_image by metis

lemma surj_map: "surj f \<Longrightarrow> surj (map f)"
  using lists_UNIV lists_image by metis

lemma bij_image: "bij f \<Longrightarrow> bij (image f)"
  using bij_betw_Pow by force

lemma inj_image: "inj f \<Longrightarrow> inj (image f)"
  by (simp add: inj_on_image)

lemma surj_image: "surj f \<Longrightarrow> surj (image f)"
  using Pow_UNIV image_Pow_surj by metis

lemmas [simp] =
  bij_rev
  bij_is_inj
  bij_is_surj
  bij_comp
  inj_compose
  comp_surj
  bij_map
  inj_mapI
  surj_map
  bij_image
  inj_image
  surj_image

section \<open>Examples\<close>

context
begin

subsection \<open>Cons and append\<close>

private lemma example_Cons_append:
  assumes "xs = [a, b]" and "ys = [b, a, b]"
  shows "xs @ xs @ xs = a # b # a # ys"
using assms by simp

thm
  example_Cons_append
  example_Cons_append[reversed]
  example_Cons_append[reversed, reversed]

thm
  not_Cons_self
  not_Cons_self[reversed]

thm
  neq_Nil_conv
  neq_Nil_conv[reversed]

subsection \<open>Induction rules\<close>

thm
  list_nonempty_induct
  list_nonempty_induct[reversed]   list_nonempty_induct[reversed, where P="\<lambda>x. P (rev x)" for P, unfolded rev_rev_ident]

thm
  list_induct2
  list_induct2[reversed]   list_induct2[reversed, where P="\<lambda>x y. P (rev x) (rev y)" for P, unfolded rev_rev_ident]

subsection \<open>hd, tl, last, butlast\<close>

thm
  hd_append
  hd_append[reversed]
  last_append

thm
  length_tl
  length_tl[reversed]
  length_butlast

thm
  hd_Cons_tl
  hd_Cons_tl[reversed]
  append_butlast_last_id
  append_butlast_last_id[reversed]

subsection \<open>set\<close>

thm
  hd_in_set
  hd_in_set[reversed]
  last_in_set

thm
  set_ConsD
  set_ConsD[reversed]

thm
  split_list_first
  split_list_first[reversed]

thm
  split_list_first_prop
  split_list_first_prop[reversed]
  split_list_first_prop[reversed, unfolded append_assoc append_Cons append_Nil]
  split_list_last_prop

thm
  split_list_first_propE
  split_list_first_propE[reversed]
  split_list_first_propE[reversed, unfolded append_assoc append_Cons append_Nil]
  split_list_last_propE

subsection \<open>rotate\<close>

private lemma rotate1_hd_tl: "xs \<noteq> [] \<Longrightarrow> rotate 1 xs = tl xs @ [hd xs]"
  by (cases xs) simp_all

thm
  rotate1_hd_tl
  rotate1_hd_tl[reversed]

end

end
