\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Examples and Brief Technical Overview for Zip\<close>
theory Zip_Examples
  imports
    Zip_Try0 (*import first such that zip is integrated in try0's schedule*)
    HOL.List
begin

paragraph \<open>Summary\<close>
text \<open>The @{method zip} method is a customisable general-purpose white-box prover based on the
Zippy framework. This theory begins with examples demonstrating some key features and concludes
with a brief technical overview for users interested in customising the method.

On a high-level, @{method zip} performs a proof tree search with customisable
expansion actions and search strategies. By default, it uses an \<open>A\<^sup>*\<close> search and integrates the
classical reasoner, simplifier, the blast and metis prover, and supports resolution with higher-order
and proof-producing unification \cite{ML_Unification-AFP}, conditional substitutions, case splitting
and induction, among other things.

In most cases, @{method zip} can be used as a drop-in replacement for Isabelle's classical methods
like @{method auto}, @{method fastforce}, @{method force}, @{method fast}, etc.,
as demonstrated in @{dir Benchmarks}. Note, however, that @{method zip} can be slower than those
methods due to a more general search procedure.

Like @{method auto}, @{method zip} supports non-terminal calls and interactive proof exploration.

@{method zip} comes with @{command try0} integration in @{file "../Zip_Try0.thy"}.
Import that theory as a first file to obtain the integration.
If you want to omit the integration, import @{file "../Zip_Metis.thy"} instead.\<close>

subsection \<open>Examples\<close>

text \<open>Note: some examples in this files are adapted from @{theory HOL.List}. Some original proofs
from @{theory HOL.List} are left in comments and tagged with "ORIG" for comparison.\<close>

experiment
begin

text \<open>You can use it like @{method auto}:\<close>

lemma "sorted_wrt (>) l \<longleftrightarrow> sorted (rev l) \<and> distinct l"
  by (induction l) (zip iff: antisym_conv1 simp: sorted_wrt_append)

lemma "sorted_wrt (>) l \<longleftrightarrow> sorted (rev l) \<and> distinct l"
  by (induction l) (zip iff: antisym_conv1 simp: sorted_wrt_append)

text \<open>You can use it for proof exploration (i.e. the method returns incomplete attempts):\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply zip
  back
  back
  oops

text \<open>Note that the method returned the goal @{prop "B \<Longrightarrow> Q"} but not @{prop "B \<Longrightarrow> P"}.
The reason is that, by default, the method only returns those incomplete attempts that only use
"promising" expansions on its search path, as further elaborated in the technical overview.
The simplifier, for instance, is marked as a "promising" expansion action.
For the classical reasoner, expansions with unsafe (introduction) rules are not marked as promising
while safe rules are.

One can instruct the method to return all attempts by changing its default strategy from
@{ML Zip.AStar.promising'} to @{ML Zip.AStar.all'}:\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply (zip run exec: Zip.AStar.all')
  oops

text \<open>Alternatively, the introduction rule can be marked as safe:\<close>

lemma
  assumes [intro!]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  apply zip
  oops

text \<open>Many explorations are possibly infinite or too large for an exhaustive search. In such cases,
one may limit the number of expansion steps. Below, we fuel the method with 20 steps:\<close>

lemma
  assumes [intro]: "P \<and> P \<Longrightarrow> P"
  shows "P"
  apply (zip 20 run exec: Zip.AStar.all') \<comment>\<open>Note: loops if no limit is passed\<close>
  oops

text \<open>One can also limit the maximum search depth, e.g. to depth 2:\<close>

lemma
  assumes [intro]: "P \<and> P \<Longrightarrow> P"
  shows "P"
  apply (zip run exec: "Zip.AStar.all 2") \<comment>\<open>Note: loops if no depth limit is passed\<close>
  oops

text \<open>You can perform case splits:\<close>

lemma "tl xs \<noteq> [] \<longleftrightarrow> xs \<noteq> [] \<and> \<not>(\<exists>x. xs = [x])"
  by (zip cases xs)

fun foo :: "nat \<Rightarrow> nat" where
  "foo 0 = 0"
| "foo (Suc 0) = 1"
| "foo (Suc (Suc n)) = 1"

lemma "foo n + foo m < 4"
  by (zip cases n rule: foo.cases and m rule: foo.cases)

text \<open>You may also use patterns of the shape (pattern - anti-patterns). All terms occurring in the
goal that (1) satisfy the pattern and (2) do not satisfy any of the anti-patterns are then taken as
instantiation candidates:\<close>

lemma "foo n + foo m < 4"
  \<comment> \<open>matches natural numbers, but no applications (e.g. @{term "foo n"})\<close>
  by (zip cases (pat) ("_ :: nat" - "_ _") rule: foo.cases)

text \<open>Note that for a function \<open>f\<close> with multiple arguments, the function package creates a cases
rule \<open>f.cases\<close> where \<open>f\<close>'s arguments are tupled and equated to a single variable. Example:\<close>

fun bar :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "bar 0 _ = 0"
| "bar (Suc 0) True = 1"
| "bar (Suc 0) False = 0"
| "bar (Suc (Suc n)) b = 1"

thm bar.cases (*put your cursor on the theorem*)

text \<open>As a result \<open>cases "n :: nat" "b :: bool" rule: bar.cases\<close> will raise an error:
The cases rule requires a @{typ "nat \<times> bool"} pair for instantiation. The right invocation is
\<open>cases "(n, b)" rule: bar.cases\<close>.

Moreover, the invocation \<open>cases (pat) "(?n :: nat, ?b :: nat)" rule: bar.cases\<close> will not find any
matches in a goal term @{term "bar n b < 2"} since no @{typ "nat \<times> bool"} pair occurs in the goal.
The solution is to transform the cases rule to the desired form with @{attribute deprod_cases}:
\<close>

thm bar.cases[deprod_cases] (*put your cursor on the theorem*)

lemma "bar n b < 2"
  by (zip cases (pat) "_ :: nat" "_ :: bool" rule: bar.cases[deprod_cases])
  (*below invocation does not work, as explained above*)
  (* by (zip cases (pat) "(?n :: nat, ?b :: nat)" rule: bar.cases) *)

text \<open>You may even use predicates on term zippers (see @{ML_structure Term_Zipper}):\<close>

lemma "foo n + foo m < 4"
  by (zip cases (pred) "fst #> member (op =) [@{term n}, @{term m}]" rule: foo.cases)

text \<open>You can use induction:\<close>

lemma "foo n + foo m < 4"
  by (zip induct rule: foo.induct)

text \<open>Again, you may also use patterns and predicates:\<close>

lemma "foo n + foo m < 4"
  by (zip induct (pat) ("_ :: nat" - "_ _") rule: foo.induct)

text \<open>Here are some more complex combinations (the original code from the standard library is marked
with ORIG in the following).  Note that configurations for different actions are separated by
\<^emph>\<open>where\<close>.\<close>

lemma list_induct2:
  "length xs = length ys \<Longrightarrow> P [] [] \<Longrightarrow>
   (\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (x#xs) (y#ys))
   \<Longrightarrow> P xs ys"
  by (zip induct xs arbitrary: ys where cases (pat) ("_ :: _ list" - "[]" "_ _"))
(*ORIG*)
(* proof (induct xs arbitrary: ys)
  case (Cons x xs ys) then show ?case by (cases ys) simp_all
qed simp *)

lemma list_induct2':
  "\<lbrakk> P [] [];
  \<And>x xs. P (x#xs) [];
  \<And>y ys. P [] (y#ys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#xs) (y#ys) \<rbrakk>
 \<Longrightarrow> P xs ys"
  by (zip induct xs arbitrary: ys where cases (pat) ("_ :: _ list" - "[]" "_ _"))
  (*ORIG*)
  (* by (induct xs arbitrary: ys) *)
  (* (case_tac x, auto) *)

text \<open>Data passed as method modifiers can also be stored in the context more generally:\<close>

fun gauss :: "nat \<Rightarrow> nat" where
  "gauss 0 = 0"
| "gauss (Suc n) = n + 1 + gauss n"

(*Note: induction rules are always applicable and should hence only be locally registered*)
context notes gauss.induct[zip_induct (pat) ("_ :: nat" - "_ _")]
begin
lemma "gauss n = (n * (n + 1)) div 2" by zip

lemma "gauss n < gauss (Suc n)" by zip

lemma "gauss n > 0 \<longleftrightarrow> n > 0" by zip
end

text \<open>In some cases, it is necessary (or advisable for performance reasons) to change the search
strategy from the default \<open>A\<^sup>*\<close> (@{ML_structure Zip.AStar}) search to breadth-first
(@{ML_structure Zip.Breadth_First}), depth-first (@{ML_structure Zip.Depth_First}),
or best-first (@{ML_structure Zip.Best_First}) search. You can either try them individually or use
@{ML_structure Zip.Try} to search for the fastest one in parallel. Note that @{ML_structure Zip.Try}
is only meant for exploration. It should be replaced by the discovered, most efficient strategy in
the final proof document!\<close>

lemma list_induct3:
  "length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P [] [] [] \<Longrightarrow>
   (\<And>x xs y ys z zs. length xs = length ys \<Longrightarrow> length ys = length zs \<Longrightarrow> P xs ys zs \<Longrightarrow> P (x#xs) (y#ys) (z#zs))
   \<Longrightarrow> P xs ys zs"
  by (induct xs arbitrary: ys zs)
  (* (zip cases (pat) ("_ :: _ list" - "[]") where run exec: Zip.Try.all') *) \<comment>\<open>this suggests Breadth\_First\<close>
  (zip cases (pat) ("_ :: _ list" - "[]") where run exec: Zip.Breadth_First.all')
(*ORIG*)
(* proof (induct xs arbitrary: ys zs)
  case Nil then show ?case by simp
next
  case (Cons x xs ys zs) then show ?case by (cases ys, simp_all)
    (cases zs, simp_all)
qed *)

text \<open>@{method zip} is also registered to @{command try0} for each search strategy:\<close>

lemma "map f xs = map g ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i<length ys. f (xs!i) = g (ys!i))"
  (*try0 simp: list_eq_iff_nth_eq*) \<comment>\<open>use the try0 command to see all successful attempts\<close>
  by (zip simp: list_eq_iff_nth_eq)

text \<open>One can use conditional substitution rules:\<close>

lemma filter_insort:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort_key f x xs) = insort_key f x (filter P xs)"
  by (induct xs)
  (zip subst insort_is_Cons where run exec: Zip.Best_First.all')
  (* (zip subst insort_is_Cons) *) \<comment>\<open>this also works, but it is slower\<close>
  (*ORIG*)
  (* (auto, subst insort_is_Cons, auto) *)

lemma rev_eq_append_conv: "rev xs = ys @ zs \<longleftrightarrow> xs = rev zs @ rev ys"
  by (zip subst rev_rev_ident[symmetric])
  (*ORIG*)
  (* by (metis rev_append rev_rev_ident) *)

lemma dropWhile_neq_rev: "\<lbrakk>distinct xs; x \<in> set xs\<rbrakk> \<Longrightarrow>
  dropWhile (\<lambda>y. y \<noteq> x) (rev xs) = x # rev (takeWhile (\<lambda>y. y \<noteq> x) xs)"
  by (zip induct xs where subst dropWhile_append2)
(*ORIG*)
(* proof (induct xs)
  case (Cons a xs)
  then show ?case
    by(auto, subst dropWhile_append2, auto)
qed simp *)

text \<open>Zip integrates the @{method blast} prover. In cases where @{method blast} loops or takes too
long, users may specify a limit on its search depth or disable it completely:\<close>

lemma "(\<forall>X. X \<subseteq> X) \<Longrightarrow> 1 + 1 = 2"
  (*Note: the following blast call loops*)
  (* by blast *)
  by (zip blast depth: 0) (*it is hence safer to disable blast here*)

text \<open>Zip also integrates the @{method metis} provers. Since @{method metis} easily loops, it is
only activated if
(1) users explicitly provide it some options and/or rules and
(2) @{method zip} is not expected to make any promising progress on the given goal node without
using @{method metis} (cf. the setup in @{theory Zippy.Zip_Metis}).
Users may pass several options/runs to metis using the separator \<open>and\<close>.

A typical workflow with @{method zip} looks as follows:

\<^enum> Check if @{method zip} is successful.
\<^enum> If it is unsuccessful but terminates:
  \<^enum> Check if there is a relevant lemma missing based on the returned goals.
    It might also be helpful to check non-promising attempts by switching from
    @{ML Zip.AStar.promising'} to @{ML Zip.AStar.all'} (or analogously for another search strategy).
  \<^enum> Call @{command sledgehammer} on the remaining goals and either add the metis calls to
    @{method zip} directly or check if there are some helpful lemmas in the @{method metis} call
    that you could add another way (e.g. as a simp or classical rule) such that the @{method metis}
    call becomes unnecessary.
    Hint: you may also want to use @{attribute metis_instantiate} for this step.
\<^enum> If it is unsuccessful and does not terminate:
  \<^enum> Check if @{method zip} is successful with a different strategy
    (e.g. by using @{ML_structure Zip.Try} or trying the strategies manually) and/or depth limit.
  \<^enum> If none of the above is successful:
    \<^enum> Limit @{method zip}'s search steps to a number such that the set of returned subgoals looks
      reasonable to you.
    \<^enum> Check which of the returned subgoals were not solvable by sequentially applying \<open>zip[1]\<close> to
      each subgoal. For each subgoal that is not solved: continue with step 2 of this workflow.
\<close>

lemma extract_Cons_code: "List.extract P (x # xs) = (if P x then Some ([], x, xs)
  else (case List.extract P xs of None \<Rightarrow> None | Some (ys, y, zs) \<Rightarrow> Some (x#ys, y, zs)))"
  (*1. The following call leaves us with one subgoal*)
  (* apply (zip simp add: extract_def comp_def split: list.splits) *)
  (*2. We call sledgehammer*)
  (*sledgehammer*)
  (*3. Sledgehammer proposes: "metis dropWhile_eq_Nil_conv list.distinct(1)"*)
  (*4. We integrate the call into zip. Result:*)
  apply (zip simp add: extract_def comp_def split: list.splits
    where metis dropWhile_eq_Nil_conv list.distinct(1))
  done
  (*ORIG*)
  (* by (auto simp add: extract_def comp_def split: list.splits)
  (metis dropWhile_eq_Nil_conv list.distinct(1)) *)

lemma longest_common_prefix:
  "\<exists>ps xs' ys'. xs = ps @ xs' \<and> ys = ps @ ys' \<and> (xs' = [] \<or> ys' = [] \<or> hd xs' \<noteq> hd ys')"
  apply (induct xs ys rule: list_induct2')
  (*1. The following call loops...*)
  (* apply zip *)
  (*2. ...we hence pass a it step limit, leaving us with three subgoals:*)
  (* apply (zip 100) *)
  (*2. We call sledgehammer*)
  (*sledgehammer*)
  (*3. Sledgehammer proposes: "metis append_eq_Cons_conv list.sel(1) self_append_conv"*)
  (*4. We integrate the call into zip. Result:*)
  apply (zip metis append_eq_Cons_conv list.sel(1) self_append_conv)
  (*Note: metis says that "self_append_conv" is unused, but in fact, metis is used more than once
  in above proof, where in some cases the theorem required and in others it is not.*)
  done
  (*ORIG*)
  (* by (induct xs ys rule: list_induct2')
   (blast, blast, blast,
    metis (no_types, opaque_lifting) append_Cons append_Nil list.sel(1)) *)

lemma not_distinct_decomp: "\<not> distinct ws \<Longrightarrow> \<exists>xs ys zs y. ws = xs@[y]@ys@[y]@zs"
proof (induct n \<equiv> "length ws" arbitrary:ws)
  case (Suc n ws)
  then show ?case using length_Suc_conv [of ws n]
    (*1. The following call loops...*)
    (* apply zip *)
    (*2. ...we hence pass a it step limit, leaving us with two subgoals:*)
    (* apply (zip 300) *)
    (*2. We call sledgehammer*)
    (*sledgehammer*)
    (*3. Sledgehammer proposes: "metis list.sel(1) self_append_conv" for the first goal
    and "metis append_Cons" for the second goal*)
    (*4. We integrate the calls into zip. Result:*)
    apply (zip metis append_Cons and split_list append_eq_append_conv2)
    done
    (*ORIG*)
    (* apply (auto simp: eq_commute)
    apply (metis append_Nil in_set_conv_decomp_first)
    by (metis append_Cons) *)
qed simp

lemma lexord_cons_cons:
  "(a # x, b # y) \<in> lexord r \<longleftrightarrow> (a = b \<and> (x,y)\<in> lexord r) \<or> (a,b)\<in> r" (is "?lhs = ?rhs")
  by (zip metis hd_append list.sel(1,3) tl_append2 and Cons_eq_append_conv)
(*ORIG*)
(* proof
  assume ?lhs
  then show ?rhs
    by (simp add: lexord_def) (metis hd_append list.sel(1) list.sel(3) tl_append2)
qed (auto simp add: lexord_def; (blast | meson Cons_eq_appendI)) *)

text \<open>One can pass (elim-/dest-/forward-)rules that should be resolved by Isabelle's standard
higher-order unifier, matcher, or a customisable proof-producing unifier (see @{session ML_Unification}).
In contrast to the rules passed to the classical reasoner, each such rule can be annotated with
individual data, e.g. priority, cost, and proof-producing unifier to be used.

Resolving rules with a proof-producing unifier is particularly useful in situations where equations do
not hold up to \<open>\<alpha>\<beta>\<eta>\<close>-equality but some stronger, provable equality (see the examples theories in
@{session ML_Unification} for more details). By default, the proof-producing unifier
@{ML Standard_Mixed_Comb_Unification.first_higherp_comb_unify} is used, which uses the simplifier
and unification hints (cf. @{theory ML_Unification.ML_Unification_Hints}), among other things.\<close>

lemma
  assumes "Q"
  and [simp]: "Q = P"
  shows "P"
  by (zip urule assms)
  (*below call does not work: P does not unify with Q*)
  (* by (zip rule assms) *)

text \<open>Passing rules to \<open>urule\<close> is particularly useful when dealing with definitions. In such
cases, theorems for the abbreviated concept can re-used for the new definition (without making the
definition opaque in general, as is the case with @{command abbreviation}):\<close>

definition "my_refl P \<equiv> reflp_on {x. P x}" \<comment>\<open>some derived concept\<close>

(*register a unification hint for the proof-producing unifier*)
lemma my_refl_uhint [uhint]:
  assumes "{x. P x} \<equiv> S"
  shows "my_refl P \<equiv> reflp_on S"
  using assms unfolding my_refl_def by simp

lemma "my_refl P Q \<Longrightarrow> P x \<Longrightarrow> \<exists>x. Q x x"
  by (zip urule (d) reflp_onD) \<comment>\<open>we can directly use @{thm reflp_onD} as a destruction rule\<close>

lemma
  assumes "\<And>Q. P (reflp_on {x. Q x \<and> True})"
  shows "True \<and> P (my_refl Q)"
  by (zip urule assms)

text \<open>For very fine-grained control, one can even specify individual functions to initialise the
proof trees linked to the rule's side conditions. By default, each such tree is again solved by all
expansion actions registered to @{method zip}. Below, we override that behaviour and let the
rule's second premise be solved by reflexivity instead. You may check the technical overview
section for more details about below code.\<close>

lemma
  assumes "P \<Longrightarrow> U = U \<Longrightarrow> Q"
  shows "A \<longrightarrow> Q"
  apply (zip rule assms updates: [2: \<open>fn i =>
    let open Zippy; open ZLPC Base_Data MU; open SC A
      val id = @{binding "refl"}
      val a_meta = AMeta.metadata (id, Lazy.value "proof by reflexivity")
      fun mk_aa_meta _ _ = AAMeta.metadata {cost = Cost.VERY_LOW, progress = AAMeta.P.Promising}
      fun ztac _ = Ctxt.with_ctxt (fn ctxt => arr (resolve_tac ctxt @{thms refl}
        |> Tac_AAM.lift_tac mk_aa_meta |> Tac_AAM.Tac.zSOME_GOAL_FOCUS))
    in
      Tac.cons_action_cluster Util.exn (ACMeta.no_descr id) [(GFocus.single i, {
        empty_action = Library.K Zippy.PAction.disable_action,
        meta = a_meta,
        result_action = Result_Action.action (Library.K (C.id ()))
          Result_Action.copy_update_data_empty_changed,
        presultsq = Zip.PResults.enum_scale_presultsq_default Cost.LOW,
        tac = ztac})]
      >>> (the #> Up3.morph)
    end\<close>])
  back
  oops

text \<open>Zippy and zip both use the @{ML_structure Logger} from @{theory ML_Unification.ML_Logger}.
You can use it to trace its search. Check the logger's examples theory in @{session ML_Unification}
for a demonstration how to filter and modify the logger's output.\<close>

lemma
  assumes [intro]: "P \<Longrightarrow> Q"
  and [simp]: "A = B"
  shows "A \<longrightarrow> Q"
  supply [[ML_map_context \<open>Logger.set_log_levels Zippy.Logging.logger Logger.DEBUG\<close>]]
  apply zip
  oops


subsection \<open>Technical Overview\<close>

text \<open>
The method @{method zip} is based on the Zippy framework. For a preprint about the latter see
\<^cite>\<open>zippy\<close>. On a high-level, the method has three phases:

\<^enum> Initialise the proof tree for a given goal.
\<^enum> Repeatedly expand and modify nodes of the proof tree.
\<^enum> Extract discovered theorems from the proof tree.

The particularities of the expansion (e.g. order of expansion, expansion rules, search bounds)
are largely customisable. Some configuration possibilities are demonstrated above.

During initialisation, the proof tree is (typically) augmented with action clusters. Each action
cluster stores a set of prioritised actions (short: \<^emph>\<open>pactions\<close>; cf. @{ML_functor Zippy_PAction_Mixin_Base}).
A paction consists of a priority and a function modifying the proof tree, called an \<^emph>\<open>action\<close>.
The paction's priority can be used to select action candidates during search.

By default, the tree is initialised with the set of initialisation functions registered in
@{ML_structure Zip.Run.Init_Goal_Cluster}. The current registrations can be seen as follows:
\<close>

ML_val\<open>Zip.Run.Init_Goal_Cluster.Data.get_table (Context.the_generic_context ())\<close>

text \<open>A registration requires an identifier and an initialisation function modifying the proof
tree in the desired way. Below, we register and delete an initialisation that adds an action cluster
with a single paction, capable of closing goals by reflexivity:\<close>

declare [[zip_init_gc \<open>
  let open Zippy; open ZLPC Base_Data MU; open A Mo
    val id = @{binding refl}
    (*action cluster metadata*)
    val ac_meta = Mixin_Base3.Meta.Meta.metadata (id, Lazy.value "reflexivity action cluster")
    (*action metadata*)
    val a_meta = Mixin_Base4.Meta.Meta.metadata (id, Lazy.value "proof by reflexivity")
    (*action application metadata*)
    fun mk_aa_meta _ _ = AAMeta.metadata {cost = Cost.VERY_LOW, (*cost of the action's result*)
      progress = AAMeta.P.Promising} (*is it a promising expansion?*)
    fun ztac _ = Ctxt.with_ctxt (fn ctxt => arr (resolve_tac ctxt @{thms refl}
      |> Tac_AAM.lift_tac mk_aa_meta |> Tac_AAM.Tac.zSOME_GOAL_FOCUS))
    val data = {
      (*disable the action once the tactic returns no results*)
      empty_action = Library.K Zippy.PAction.disable_action,
      meta = a_meta,
      (*attach a new node from the tactic's result and, for every remaining subgoal, copy the actions
      registered for those subgoals from the node's parent*)
      result_action = Result_Action.action (Library.K (C.id ()))
        Result_Action.copy_update_data_empty_changed,
      (*the sequence of priorities for each pull from the tactic's result sequence*)
      presultsq = Zip.PResults.enum_scale_presultsq_default Cost.LOW,
      tac = ztac}
    (*attach the action cluster and step back to the parent node*)
    fun init _ focus z = Tac.cons_action_cluster Util.exn (ACMeta.no_descr id) [(focus, data)] z
      >>= AC.opt (K z) Up3.morph
  in (id, init) end\<close>]]
declare [[zip_init_gc del: "@{binding refl}"]] (*delete it*)

text \<open>Since the kind of pactions tried by zip is extensible, the parser of @{method zip} is also
extensible. Each parser has to apply its desired changes to the context and return a unit:
\<close>

declare [[zip_parse add: \<open>(@{binding refl},
  apfst (Config.put_generic Unify.search_bound 5) (*change the search bound*)
  #> tap (fn _ => writeln "I got parsed!") #> Scan.succeed ())\<close>]]

lemma "x = x"
  by (zip refl) (*put your cursor on the method*)

declare [[zip_parse del: \<open>@{binding refl}\<close>]] (*delete it again*)

text \<open>The initialised proof tree can then be expanded. By default, an \<open>A\<^sup>*\<close> search is performed,
taking into consideration the pactions' user supplied priorities and the sum of costs of the path
leading to a paction. Other available search strategies are depth-first and breadth-first search
with \<open>A\<^sup>*\<close>-cost tiebreakers, and best-first search on the pactions' priorities. Other search
strategies may at will.

For more details, check the sources of the setup in @{theory Zippy.Zip_Pure} and
@{theory Zippy.Zip_HOL}.\<close>

end
end
