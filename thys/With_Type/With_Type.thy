section \<open>\<open>With_Type\<close> -- Setting up the \<^term>\<open>with_type\<close> mechanism\<close>

theory With_Type
  imports "HOL-Types_To_Sets.Types_To_Sets" Misc_With_Type "HOL-Eisbach.Eisbach"
  keywords "with_type_case" :: prf_asm % "proof"
begin

definition with_type_wellformed where
  \<comment> \<open>This states, roughly, that if operations \<^term>\<open>rp\<close> satisfy the axioms of the class,
      then they are in the domain of the relation between abstract/concrete operations.\<close>
  \<open>with_type_wellformed C S R \<longleftrightarrow> (\<forall>r rp. bi_unique r \<longrightarrow> right_total r \<longrightarrow> S = Collect (Domainp r) \<longrightarrow> C S rp \<longrightarrow> Domainp (R r) rp)\<close>
    for C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close>
    and S :: \<open>'rep set\<close>
    and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>

text \<open>
In the following definition, roughly speaking, \<^term>\<open>with_type C R S rep_ops P\<close> means that predicate \<^term>\<open>P\<close> holds whenever
type \<^typ>\<open>'abs\<close> (called the abstract type, and determined by the type of \<^term>\<open>P\<close>)
is an instance of the type class described by C,R, and is a stands in 1-1 correspondence 
to the subset \<^term>\<open>S\<close> of some concrete type \<^typ>\<open>'rep\<close> (i.e., as if defined by
\<open>typedef 'abs = S\<close>).

\<^term>\<open>S\<close> -- the carrier set of the representation of the type (concrete type)

\<^term>\<open>rep_ops\<close> -- operations on the concrete type (i.e., operations like addition or similar)

\<^term>\<open>C\<close> -- the properties that \<^term>\<open>S\<close> and \<^term>\<open>rep_ops\<close> are guaranteed to satisfy
(basically, the type-class definition)

\<^term>\<open>R\<close> -- transfers a relation \<^term>\<open>r\<close> between concrete/abstract type to a relation
between concrete/abstract operations (\<^term>\<open>r\<close> is always bi-unique and right-total)

\<^term>\<open>P\<close> -- the predicate that we claim holds.
It can work on the type \<^typ>\<open>'abs\<close> (which is type-classed) but it also gets \<^term>\<open>rep\<close> and \<^term>\<open>abs_ops\<close>
where \<^term>\<open>rep\<close> is an embedding of the abstract into the concrete type, and \<^term>\<open>abs_ops\<close> operations on the abstract type.

The intuitive meaning of \<^term>\<open>with_type C R S rep_ops P\<close> is that \<^term>\<open>P\<close> holds for
any type \<^typ>\<open>'t\<close> that that can be represented by a concrete representation \<^term>\<open>(S,rep_ops)\<close>
and that has a type class matching the specification \<^term>\<open>(C,R)\<close>.
\<close>
definition \<open>with_type = (\<lambda>C R S rep_ops P. S\<noteq>{} \<and> C S rep_ops \<and> with_type_wellformed C S R
    \<and> (\<forall>rep abs_ops. bij_betw rep UNIV S \<longrightarrow> (R (\<lambda>x y. x = rep y) rep_ops abs_ops) \<longrightarrow> 
            P rep abs_ops))\<close>
  for S :: \<open>'rep set\<close> and P :: \<open>('abs \<Rightarrow> 'rep) \<Rightarrow> 'abs_ops \<Rightarrow> bool\<close>
  and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
  and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close>
  and rep_ops :: \<open>'rep_ops\<close>

text \<open>For every type class that we want to use with \<^const>\<open>with_type\<close>, we need to define two
  constants specifying the axioms of the class (\<^term>\<open>WITH_TYPE_CLASS_classname\<close>) and
  specifying how a relation between concrete/abstract type is lifted to a relation between
  concrete/abstract operations (\<^term>\<open>WITH_TYPE_REL_classname\<close>). Here we give the
  trivial definitions for the default type class \<^class>\<open>type\<close>\<close>
definition \<open>WITH_TYPE_CLASS_type S ops = True\<close> for S :: \<open>'rep set\<close> and ops :: unit
definition \<open>WITH_TYPE_REL_type r = ((=) :: unit \<Rightarrow> _ \<Rightarrow> _)\<close> for r :: \<open>'rep \<Rightarrow> 'abs \<Rightarrow> bool\<close>

named_theorems with_type_intros
  \<comment> \<open>In this named fact collection, we collect introduction rules that are used to automatically
  discharge some simple premises in automated methods (currently only \<open>with_type_intro\<close>).\<close>

lemma [with_type_intros]: \<open>WITH_TYPE_CLASS_type S ops\<close>
  by (simp add: WITH_TYPE_CLASS_type_def)

text \<open>We need to show that \<^term>\<open>WITH_TYPE_CLASS_classname\<close> and \<^term>\<open>WITH_TYPE_REL_classname\<close>
  are wellbehaved. We do this here for class \<^class>\<open>type\<close>. We will need this lemma also for
  registering the type class \<^class>\<open>type\<close> later.\<close>
lemma with_type_wellformed_type[with_type_intros]:
  \<open>with_type_wellformed WITH_TYPE_CLASS_type S WITH_TYPE_REL_type\<close>
  by (simp add: WITH_TYPE_REL_type_def WITH_TYPE_CLASS_type_def with_type_wellformed_def Domainp_iff)

lemma with_type_simple: \<open>with_type WITH_TYPE_CLASS_type WITH_TYPE_REL_type S () P \<longleftrightarrow> S\<noteq>{} \<and> (\<forall>rep. bij_betw rep UNIV S \<longrightarrow> P rep ())\<close>
  \<comment> \<open>For class \<^class>\<open>type\<close>, \<^const>\<open>with_type\<close> can be rewritten in a much more compact and simpler way.\<close>
  by (auto simp: with_type_def WITH_TYPE_REL_type_def WITH_TYPE_CLASS_type_def with_type_wellformed_def)

lemma with_typeI:
  assumes \<open>S \<noteq> {}\<close>
  assumes \<open>C S p\<close>
  assumes \<open>with_type_wellformed C S R\<close>
  assumes main: \<open>\<And>(rep :: 'abs \<Rightarrow> 'rep) abs_ops. bij_betw rep UNIV S \<Longrightarrow> R (\<lambda>x y. x = rep y) p abs_ops \<Longrightarrow> P rep abs_ops\<close>
  shows \<open>with_type C R S p P\<close>
  using assms
  by (auto intro!: simp: with_type_def)

lemma with_type_mp:
  assumes \<open>with_type C R S p P\<close>
  assumes \<open>\<And>rep abs_ops. bij_betw rep UNIV S \<Longrightarrow> C S p \<Longrightarrow> P rep abs_ops \<Longrightarrow> Q rep abs_ops\<close>
  shows \<open>with_type C R S p Q\<close>
  using assms by (auto simp add: with_type_def case_prod_beta type_definition_bij_betw_iff)

lemma with_type_nonempty: \<open>with_type C R S p P \<Longrightarrow> S \<noteq> {}\<close>
  by (simp add: with_type_def case_prod_beta)

lemma with_type_prepare_cancel:
  \<comment> \<open>Auxiliary lemma used by the implementation of the \<open>cancel_with_type\<close>-mechanism (see below)\<close>
  fixes S :: \<open>'rep set\<close> and P :: bool
    and R :: \<open>('rep \<Rightarrow> 'abs \<Rightarrow> bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and C :: \<open>'rep set \<Rightarrow> 'rep_ops \<Rightarrow> bool\<close>
    and p :: \<open>'rep_ops\<close>
  assumes wt: \<open>with_type C R S p (\<lambda>(_::'abs\<Rightarrow>'rep) _. P)\<close>
  assumes ex: \<open>(\<exists>(rep::'abs\<Rightarrow>'rep) abs. type_definition rep abs S)\<close>
  shows P
proof -
  from ex
  obtain rep :: \<open>'abs \<Rightarrow> 'rep\<close> and abs where td: \<open>type_definition rep abs S\<close>
    by auto
  then have bij: \<open>bij_betw rep UNIV S\<close>
    by (simp add: bij_betw_def inj_on_def type_definition.Rep_inject type_definition.Rep_range)
  define r where \<open>r = (\<lambda>x y. x = rep y)\<close>
  have [simp]: \<open>bi_unique r\<close> \<open>right_total r\<close>
    using r_def td typedef_bi_unique apply blast
    by (simp add: r_def right_totalI)
  have aux1: \<open>(\<And>x. rep x \<in> S) \<Longrightarrow> x \<in> S \<Longrightarrow> x = rep (abs x)\<close> for x b
    using td type_definition.Abs_inverse by fastforce
  have Sr: \<open>S = Collect (Domainp r)\<close>
    using type_definition.Rep[OF td]
    by (auto simp: r_def intro!: DomainPI aux1)
  from wt have nice: \<open>with_type_wellformed C S R\<close> and \<open>C S p\<close>
    by (simp_all add: with_type_def case_prod_beta)
  from nice[unfolded with_type_wellformed_def, rule_format, OF \<open>bi_unique r\<close> \<open>right_total r\<close> Sr \<open>C S p\<close>]
  obtain abs_ops where abs_ops: \<open>R (\<lambda>x y. x = rep y) p abs_ops\<close>
    apply atomize_elim by (auto simp: r_def)
  from bij abs_ops wt
  show P
    by (auto simp: with_type_def case_prod_beta)
qed

lemma with_type_transfer_class:
  \<comment> \<open>Auxiliary lemma used by ML function \<open>cancel_with_type\<close>\<close>
  includes lifting_syntax
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and C S
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs_ops2 \<Rightarrow> bool)\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>with_type_wellformed C S R2\<close>
  assumes wt: \<open>with_type C R S p P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>\<exists>x::'abs_ops2. axioms x\<close>
proof -
  from ex obtain Rep :: \<open>'abs2\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r x y = (x = Rep y)\<close> for x y
  have bi_unique_r: \<open>bi_unique r\<close>
    using bi_unique_def td type_definition.Rep_inject r_def by fastforce
  have right_total_r: \<open>right_total r\<close>
    by (simp add: right_totalI r_def)
  have right_total_R[transfer_rule]: \<open>right_total (r ===> r ===> r)\<close>
    by (meson bi_unique_r right_total_r bi_unique_alt_def right_total_fun)
  note trans = trans[OF bi_unique_r, OF right_total_r, transfer_rule]

  from td
  have rS: \<open>Collect (Domainp r) = S\<close>
    by (auto simp: r_def Domainp_iff type_definition.Rep  elim!: type_definition.Rep_cases[where P=\<open>Ex _\<close>])

  from wt have sg: \<open>C S p\<close>
    by (simp_all add: with_type_def case_prod_beta)

  with nice have \<open>Domainp (R2 r) p\<close>
    by (simp add: bi_unique_r with_type_wellformed_def rS right_total_r)
  
  with sg
  have \<open>\<exists>x :: 'abs_ops2. axioms x\<close>
    apply (transfer' fixing: R2 S p)
    using apply_rsp' local.trans rS by fastforce
  
  then obtain abs_plus :: 'abs_ops2 
    where abs_plus: \<open>axioms abs_plus\<close>
    apply atomize_elim by auto

  then show ?thesis
    by auto
qed

lemma with_type_transfer_class2:
  \<comment> \<open>Auxiliary lemma used by ML function \<open>cancel_with_type\<close>\<close>
  includes lifting_syntax
  fixes Rep :: \<open>'abs \<Rightarrow> 'rep\<close>
    and C S
    and R :: \<open>('rep\<Rightarrow>'abs\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs itself \<Rightarrow> bool)\<close>
    and R2 :: \<open>('rep\<Rightarrow>'abs2\<Rightarrow>bool) \<Rightarrow> ('rep_ops \<Rightarrow> 'abs2 itself \<Rightarrow> bool)\<close>
  assumes trans: \<open>\<And>r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r ===> (\<longleftrightarrow>)) (C (Collect (Domainp r))) axioms\<close>
  assumes nice: \<open>with_type_wellformed C S R2\<close> (* Not used, but the ML-code expects it to be there currently. *)
  assumes rel_itself: \<open>\<And>(r :: 'rep \<Rightarrow> 'abs2 \<Rightarrow> bool) p. bi_unique r \<Longrightarrow> right_total r \<Longrightarrow> (R2 r) p TYPE('abs2)\<close>
  assumes wt: \<open>with_type C R S p P\<close>
  assumes ex: \<open>\<exists>(Rep :: 'abs2\<Rightarrow>'rep) Abs. type_definition Rep Abs S\<close>
  shows \<open>axioms TYPE('abs2)\<close>
proof -
  from ex obtain Rep :: \<open>'abs2\<Rightarrow>'rep\<close> and Abs where td: \<open>type_definition Rep Abs S\<close>
    by auto
  define r where \<open>r x y = (x = Rep y)\<close> for x y
  have bi_unique_r: \<open>bi_unique r\<close>
    using bi_unique_def td type_definition.Rep_inject r_def by fastforce
  have right_total_r: \<open>right_total r\<close>
    by (simp add: right_totalI r_def)
  have right_total_R[transfer_rule]: \<open>right_total (r ===> r ===> r)\<close>
    by (meson bi_unique_r right_total_r bi_unique_alt_def right_total_fun)

  from td
  have rS: \<open>Collect (Domainp r) = S\<close>
    by (auto simp: r_def Domainp_iff type_definition.Rep elim!: type_definition.Rep_cases[where P=\<open>Ex _\<close>])

  note trans = trans[OF bi_unique_r, OF right_total_r, unfolded rS, transfer_rule]

  note rel_itself = rel_itself[OF bi_unique_r, OF right_total_r, of p, transfer_rule]

  from wt have sg: \<open>C S p\<close>
    by (simp_all add: with_type_def case_prod_beta)
  then show \<open>axioms TYPE('abs2)\<close>
    by transfer
qed

text \<open>Syntactic constants for rendering \<^const>\<open>with_type\<close> nicely.\<close>
syntax "_with_type" :: "type \<Rightarrow> 'a => 'b \<Rightarrow> 'c" ("let _ = _ in _" [0,0,10] 10)
syntax "_with_type_with" :: "type \<Rightarrow> 'a => args \<Rightarrow> 'b \<Rightarrow> 'c" ("let _ = _ with _ in _" [0,0,10] 10)
syntax (output) "_with_type_sort_annotation" :: "type \<Rightarrow> sort \<Rightarrow> type" ("_::_")
  \<comment> \<open>An auxiliary syntactic constant used to enforce the printing of sort constraints in certain terms.\<close>

ML_file "with_type.ML"


text \<open>Register the type class \<^class>\<open>type\<close> with the \<^const>\<open>with_type\<close>-mechanism.
  This enables readable syntax, and contains information needed by various tools
  such as the \<open>cancel_with_type\<close> attribute.\<close>
setup \<open>
With_Type.add_with_type_info_global {
  class = \<^class>\<open>type\<close>,
  rep_class = \<^const_name>\<open>WITH_TYPE_CLASS_type\<close>,
  rep_rel = \<^const_name>\<open>WITH_TYPE_REL_type\<close>,
  with_type_wellformed = @{thm with_type_wellformed_type},
  param_names = [],
  transfer = NONE,
  rep_rel_itself = NONE
}\<close>

text \<open>Enabling input/output syntax for \<^const>\<open>with_type\<close>. This allows to write, e.g.,
  \<open>let 't::type = S in P\<close>, and the various relevant parameters such as \<^const>\<open>WITH_TYPE_CLASS_type\<close> etc.
  are automatically looked up based on the indicated type class.
  This only works with type classes that have been registered beforehand.

  Using the syntax when printing can be disabled by \<open>declare [[with_type_syntax=false]]\<close>.\<close>
parse_translation \<open>[
  (\<^syntax_const>\<open>_with_type\<close>, With_Type.with_type_parse_translation),
  (\<^syntax_const>\<open>_with_type_with\<close>, With_Type.with_type_parse_translation)
]\<close>
typed_print_translation \<open>[ (\<^const_syntax>\<open>with_type\<close>, With_Type.with_type_print_translation) ]\<close>


text \<open>Example of input syntax:\<close>
term \<open>let 't::type = N in rep_t = rep_t\<close>


text \<open>Removes a toplevel \<open>let 't=\<dots>\<close> from a proposition \<open>let 't=\<dots> in P\<close>.
  This only works if \<^term>\<open>P\<close> does not refer to the type \<^typ>\<open>'t\<close>.\<close>
attribute_setup cancel_with_type =
  \<open>Thm.rule_attribute [] (With_Type.cancel_with_type o Context.proof_of) |> Scan.succeed\<close>
  \<open>Transforms (let 't=\<dots> in P) into P\<close>


text \<open>Convenience method for proving a theorem of the form \<open>let 't=\<dots>\<close>.\<close>
method with_type_intro = rule with_typeI; (intro with_type_intros)?


text \<open>Method for doing a modus ponens inside \<open>let 't=\<dots>\<close>.
Use as: \<open>using PREMISE proof with_type_mp\<close>.
And inside the proof, use the command \<open>with_type_case\<close> before proving the main goal.
Try \<open>print_theorems\<close> after \<open>with_type_case\<close> to see what it sets up.
\<close>
method_setup with_type_mp = \<open>Scan.succeed () >> 
  (fn (_) => fn ctxt => CONTEXT_METHOD (fn facts =>
      Method.RUNTIME (With_Type.with_type_mp_tac \<^here> facts)))\<close>

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with_type_case\<close> "Sets up local proof after the \<^method>\<open>with_type_mp\<close> method (for the main goal)."
    (Scan.repeat (Parse.maybe Parse.binding) >> (fn args => Toplevel.proof (With_Type.with_type_case_cmd args)))
\<close>


end
