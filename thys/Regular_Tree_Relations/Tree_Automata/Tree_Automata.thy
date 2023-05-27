section \<open>Tree automaton\<close>

theory Tree_Automata
  imports FSet_Utils
    "HOL-Library.Product_Lexorder"
    "HOL-Library.Option_ord"
begin

subsection \<open>Tree automaton definition and functionality\<close>

datatype ('q, 'f) ta_rule = TA_rule (r_root: 'f) (r_lhs_states: "'q list") (r_rhs: 'q) ("_ _ \<rightarrow> _" [51, 51, 51] 52)
datatype ('q, 'f) ta = TA (rules: "('q, 'f) ta_rule fset") (eps: "('q \<times> 'q) fset")

text \<open>In many application we are interested in specific subset of all terms. If these
  can be captured by a tree automaton (identified by a state) then we say the set is regular.
  This gives the motivation for the following definition\<close>
datatype ('q, 'f) reg = Reg (fin: "'q fset") (ta: "('q, 'f) ta")


text \<open>The state set induced by a tree automaton is implicit in our representation.
  We compute it based on the rules and epsilon transitions of a given tree automaton\<close>

abbreviation rule_arg_states where "rule_arg_states \<Delta> \<equiv> |\<Union>| ((fset_of_list \<circ> r_lhs_states) |`| \<Delta>)"
abbreviation rule_target_states where "rule_target_states \<Delta> \<equiv> (r_rhs |`| \<Delta>)"
definition rule_states where "rule_states \<Delta> \<equiv> rule_arg_states \<Delta> |\<union>| rule_target_states \<Delta>"

definition eps_states where "eps_states \<Delta>\<^sub>\<epsilon> \<equiv> (fst |`| \<Delta>\<^sub>\<epsilon>) |\<union>| (snd |`| \<Delta>\<^sub>\<epsilon>)"
definition "\<Q> \<A> = rule_states (rules \<A>) |\<union>| eps_states (eps \<A>)"
abbreviation "\<Q>\<^sub>r \<A> \<equiv> \<Q> (ta \<A>)"

definition ta_rhs_states :: "('q, 'f) ta \<Rightarrow> 'q fset" where
  "ta_rhs_states \<A> \<equiv> {| q | p q. (p |\<in>| rule_target_states (rules \<A>)) \<and> (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)|}"

definition "ta_sig \<A> = (\<lambda> r. (r_root r, length (r_lhs_states r))) |`| (rules \<A>)"

subsubsection \<open>Rechability of a term induced by a tree automaton\<close>
(* The reachable states of some term. *)
fun ta_der :: "('q, 'f) ta \<Rightarrow> ('f, 'q) term \<Rightarrow> 'q fset" where
  "ta_der \<A> (Var q) = {|q' | q'. q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+| |}"
| "ta_der \<A> (Fun f ts) = {|q' | q' q qs.
    TA_rule f qs q |\<in>| (rules \<A>) \<and> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|) \<and> length qs = length ts \<and> 
    (\<forall> i < length ts. qs ! i |\<in>| ta_der \<A> (ts ! i))|}"

(* The reachable mixed terms of some term. *)
fun ta_der' :: "('q,'f) ta \<Rightarrow> ('f,'q) term \<Rightarrow> ('f,'q) term fset" where
  "ta_der' \<A> (Var p) = {|Var q | q. p = q \<or>  (p, q) |\<in>| (eps \<A>)|\<^sup>+| |}"
| "ta_der' \<A> (Fun f ts) = {|Var q | q. q |\<in>| ta_der \<A> (Fun f ts)|} |\<union>|
    {|Fun f ss | ss. length ss = length ts \<and>
      (\<forall>i < length ts. ss ! i |\<in>| ta_der' \<A> (ts ! i))|}"

text \<open>Sometimes it is useful to analyse a concrete computation done by a tree automaton.
  To do this we introduce the notion of run which keeps track which states are computed in each
  subterm to reach a certain state.\<close>

abbreviation "ex_rule_state \<equiv> fst \<circ> groot_sym"
abbreviation "ex_comp_state \<equiv> snd \<circ> groot_sym"

inductive run for \<A> where
  step: "length qs = length ts \<Longrightarrow> (\<forall> i < length ts. run \<A> (qs ! i) (ts ! i)) \<Longrightarrow>
    TA_rule f (map ex_comp_state qs) q |\<in>| (rules \<A>) \<Longrightarrow> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|) \<Longrightarrow> 
    run \<A> (GFun (q, q') qs) (GFun f ts)"


subsubsection \<open>Language acceptance\<close>

definition ta_lang :: "'q fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('f, 'v) terms" where
  [code del]: "ta_lang Q \<A> = {adapt_vars t | t. ground t \<and> Q |\<inter>| ta_der \<A> t \<noteq> {||}}"

definition gta_der where
  "gta_der \<A> t = ta_der \<A> (term_of_gterm t)"

definition gta_lang where
  "gta_lang Q \<A> = {t. Q |\<inter>| gta_der \<A> t \<noteq> {||}}"

definition \<L> where
  "\<L> \<A> = gta_lang (fin \<A>) (ta \<A>)"

definition reg_Restr_Q\<^sub>f where
  "reg_Restr_Q\<^sub>f R = Reg (fin R |\<inter>| \<Q>\<^sub>r R) (ta R)"

subsubsection \<open>Trimming\<close>

definition ta_restrict where
  "ta_restrict \<A> Q = TA {| TA_rule f qs q| f qs q. TA_rule f qs q |\<in>| rules \<A> \<and> fset_of_list qs |\<subseteq>| Q \<and> q |\<in>| Q |} (fRestr (eps \<A>) Q)"

definition ta_reachable :: "('q, 'f) ta \<Rightarrow> 'q fset" where
  "ta_reachable \<A> = {|q| q. \<exists> t. ground t \<and> q |\<in>| ta_der \<A> t |}"

definition ta_productive :: "'q fset \<Rightarrow> ('q,'f) ta \<Rightarrow> 'q fset" where
  "ta_productive P \<A> \<equiv> {|q| q q' C. q' |\<in>| ta_der \<A> (C\<langle>Var q\<rangle>) \<and> q' |\<in>| P |}"

text \<open>An automaton is trim if all its states are reachable and productive.\<close>
definition ta_is_trim :: "'q fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> bool" where
  "ta_is_trim P \<A> \<equiv> \<forall> q. q |\<in>| \<Q> \<A> \<longrightarrow> q |\<in>| ta_reachable \<A> \<and> q |\<in>| ta_productive P \<A>"

definition reg_is_trim :: "('q, 'f) reg \<Rightarrow> bool" where
  "reg_is_trim R \<equiv> ta_is_trim (fin R) (ta R)"

text \<open>We obtain a trim automaton by restriction it to reachable and productive states.\<close>
abbreviation ta_only_reach :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta" where
  "ta_only_reach \<A> \<equiv> ta_restrict \<A> (ta_reachable \<A>)"

abbreviation ta_only_prod :: "'q fset \<Rightarrow> ('q,'f) ta \<Rightarrow> ('q,'f) ta" where
  "ta_only_prod P \<A> \<equiv> ta_restrict \<A> (ta_productive P \<A>)"

definition reg_reach where
  "reg_reach R = Reg (fin R) (ta_only_reach (ta R))"

definition reg_prod where
  "reg_prod R = Reg (fin R) (ta_only_prod (fin R) (ta R))"

definition trim_ta :: "'q fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q, 'f) ta" where
  "trim_ta P \<A> = ta_only_prod P (ta_only_reach \<A>)"

definition trim_reg where
  "trim_reg R = Reg (fin R) (trim_ta (fin R) (ta R))"

subsubsection \<open>Mapping over tree automata\<close>

definition fmap_states_ta ::  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'f) ta \<Rightarrow> ('b, 'f) ta" where
  "fmap_states_ta f \<A> = TA (map_ta_rule f id |`| rules \<A>) (map_both f |`| eps \<A>)"

definition fmap_funs_ta :: "('f \<Rightarrow> 'g) \<Rightarrow> ('a, 'f) ta \<Rightarrow> ('a, 'g) ta" where
  "fmap_funs_ta f \<A> = TA (map_ta_rule id f |`| rules \<A>) (eps \<A>)"

definition fmap_states_reg ::  "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'f) reg \<Rightarrow> ('b, 'f) reg" where
  "fmap_states_reg f R = Reg (f |`| fin R) (fmap_states_ta f (ta R))"

definition fmap_funs_reg :: "('f \<Rightarrow> 'g) \<Rightarrow> ('a, 'f) reg \<Rightarrow> ('a, 'g) reg" where
  "fmap_funs_reg f R = Reg (fin R) (fmap_funs_ta f (ta R))"

subsubsection \<open>Product construction (language intersection)\<close>

definition prod_ta_rules :: "('q1,'f) ta \<Rightarrow> ('q2,'f) ta \<Rightarrow> ('q1 \<times> 'q2, 'f) ta_rule fset" where
  "prod_ta_rules \<A> \<B> = {| TA_rule f qs q | f qs q. TA_rule f (map fst qs) (fst q) |\<in>| rules \<A> \<and>
     TA_rule f (map snd qs) (snd q) |\<in>| rules \<B>|}"
declare prod_ta_rules_def [simp]


definition prod_epsLp where
  "prod_epsLp \<A> \<B> = (\<lambda> (p, q). (fst p, fst q) |\<in>| eps \<A> \<and> snd p = snd q \<and> snd q |\<in>| \<Q> \<B>)"
definition prod_epsRp where
  "prod_epsRp \<A> \<B> = (\<lambda> (p, q). (snd p, snd q) |\<in>| eps \<B> \<and> fst p = fst q \<and> fst q |\<in>| \<Q> \<A>)"

definition prod_ta :: "('q1,'f) ta \<Rightarrow> ('q2,'f) ta \<Rightarrow> ('q1 \<times> 'q2, 'f) ta" where
  "prod_ta \<A> \<B> = TA (prod_ta_rules \<A> \<B>)
    (fCollect (prod_epsLp \<A> \<B>) |\<union>| fCollect (prod_epsRp \<A> \<B>))"

definition reg_intersect where
  "reg_intersect R L = Reg (fin R |\<times>| fin L) (prod_ta (ta R) (ta L))"

subsubsection \<open>Union construction (language union)\<close>

definition ta_union where
  "ta_union \<A> \<B> = TA (rules \<A> |\<union>| rules \<B>) (eps \<A> |\<union>| eps \<B>)"

definition reg_union where
  "reg_union R L = Reg (Inl |`| (fin R |\<inter>| \<Q>\<^sub>r R) |\<union>| Inr |`| (fin L |\<inter>| \<Q>\<^sub>r L))
    (ta_union (fmap_states_ta Inl (ta R)) (fmap_states_ta Inr (ta L)))"


subsubsection \<open>Epsilon free and tree automaton accepting empty language\<close>

definition eps_free_rulep where
  "eps_free_rulep \<A> = (\<lambda> r. \<exists> f qs q q'. r = TA_rule f qs q' \<and> TA_rule f qs q |\<in>| rules \<A> \<and> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|))"

definition eps_free :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta" where
  "eps_free \<A> = TA (fCollect (eps_free_rulep \<A>)) {||}"

definition is_ta_eps_free :: "('q, 'f) ta \<Rightarrow> bool" where
  "is_ta_eps_free \<A> \<longleftrightarrow> eps \<A> = {||}"

definition ta_empty :: "'q fset \<Rightarrow> ('q,'f) ta \<Rightarrow> bool" where
  "ta_empty Q \<A> \<longleftrightarrow> ta_reachable \<A> |\<inter>| Q |\<subseteq>| {||}"

definition eps_free_reg where
  "eps_free_reg R = Reg (fin R) (eps_free (ta R))"

definition reg_empty where
  "reg_empty R = ta_empty (fin R) (ta R)"


subsubsection \<open>Relabeling tree automaton states to natural numbers\<close>

definition map_fset_to_nat :: "('a :: linorder) fset \<Rightarrow> 'a \<Rightarrow> nat" where
  "map_fset_to_nat X = (\<lambda>x. the (mem_idx x (sorted_list_of_fset X)))"

definition map_fset_fset_to_nat :: "('a :: linorder) fset fset \<Rightarrow> 'a fset \<Rightarrow> nat" where
  "map_fset_fset_to_nat X = (\<lambda>x. the (mem_idx (sorted_list_of_fset x) (sorted_list_of_fset (sorted_list_of_fset |`| X))))"

definition relabel_ta :: "('q :: linorder, 'f) ta \<Rightarrow> (nat, 'f) ta" where
  "relabel_ta \<A> = fmap_states_ta (map_fset_to_nat (\<Q> \<A>)) \<A>"

definition relabel_Q\<^sub>f :: "('q :: linorder) fset \<Rightarrow> ('q :: linorder, 'f) ta \<Rightarrow> nat fset" where
  "relabel_Q\<^sub>f Q \<A> = map_fset_to_nat (\<Q> \<A>) |`| (Q |\<inter>| \<Q> \<A>)"
definition relabel_reg  :: "('q :: linorder, 'f) reg \<Rightarrow> (nat, 'f) reg" where
  "relabel_reg R = Reg (relabel_Q\<^sub>f (fin R) (ta R)) (relabel_ta (ta R))"

\<comment> \<open>The instantiation of $<$ and $\leq$ for finite sets are $\mid \subset \mid$ and $\mid \subseteq \mid$
  which don't give rise to a total order and therefore it cannot be an instance of the type class linorder.
  However taking the lexographic order of the sorted list of each finite set gives rise
  to a total order. Therefore we provide a relabeling for tree automata where the states
  are finite sets. This allows us to relabel the well known power set construction.\<close>

definition relabel_fset_ta :: "(('q :: linorder) fset, 'f) ta \<Rightarrow> (nat, 'f) ta" where
  "relabel_fset_ta \<A> = fmap_states_ta (map_fset_fset_to_nat (\<Q> \<A>)) \<A>"

definition relabel_fset_Q\<^sub>f :: "('q :: linorder) fset fset \<Rightarrow> (('q :: linorder) fset, 'f) ta \<Rightarrow> nat fset" where
  "relabel_fset_Q\<^sub>f Q \<A> = map_fset_fset_to_nat (\<Q> \<A>) |`| (Q |\<inter>| \<Q> \<A>)"

definition relable_fset_reg  :: "(('q :: linorder) fset, 'f) reg \<Rightarrow> (nat, 'f) reg" where
  "relable_fset_reg R = Reg (relabel_fset_Q\<^sub>f (fin R) (ta R)) (relabel_fset_ta (ta R))"


definition "srules \<A> = fset (rules \<A>)"
definition "seps \<A> = fset (eps \<A>)"

lemma rules_transfer [transfer_rule]:
  "rel_fun (=) (pcr_fset (=)) srules rules" unfolding rel_fun_def
  by (auto simp add: cr_fset_def fset.pcr_cr_eq srules_def)

lemma eps_transfer [transfer_rule]:
  "rel_fun (=) (pcr_fset (=)) seps eps" unfolding rel_fun_def
  by (auto simp add: cr_fset_def fset.pcr_cr_eq seps_def)

lemma TA_equalityI:
  "rules \<A> = rules \<B> \<Longrightarrow> eps \<A> = eps \<B> \<Longrightarrow> \<A> = \<B>"
  using ta.expand by blast

lemma rule_states_code [code]:
  "rule_states \<Delta> = |\<Union>| ((\<lambda> r. finsert (r_rhs r) (fset_of_list (r_lhs_states r))) |`| \<Delta>)"
  unfolding rule_states_def
  by fastforce

lemma eps_states_code [code]:
  "eps_states \<Delta>\<^sub>\<epsilon> = |\<Union>| ((\<lambda> (q,q'). {|q,q'|}) |`| \<Delta>\<^sub>\<epsilon>)" (is "?Ls = ?Rs")
  unfolding eps_states_def
  by (force simp add: case_prod_beta')

lemma rule_states_empty [simp]:
  "rule_states {||} = {||}"
  by (auto simp: rule_states_def)

lemma eps_states_empty [simp]:
  "eps_states {||} = {||}"
  by (auto simp: eps_states_def)

lemma rule_states_union [simp]:
  "rule_states (\<Delta> |\<union>| \<Gamma>) = rule_states \<Delta> |\<union>| rule_states \<Gamma>"
  unfolding rule_states_def
  by fastforce

lemma rule_states_mono:
  "\<Delta> |\<subseteq>| \<Gamma> \<Longrightarrow> rule_states \<Delta> |\<subseteq>| rule_states \<Gamma>"
  unfolding rule_states_def
  by force

lemma eps_states_union [simp]:
  "eps_states (\<Delta> |\<union>| \<Gamma>) = eps_states \<Delta> |\<union>| eps_states \<Gamma>"
  unfolding eps_states_def
  by auto

lemma eps_states_image [simp]:
  "eps_states (map_both f |`| \<Delta>\<^sub>\<epsilon>) = f |`| eps_states \<Delta>\<^sub>\<epsilon>"
  unfolding eps_states_def map_prod_def
  by (force simp: fimage_iff)

lemma eps_states_mono:
  "\<Delta> |\<subseteq>| \<Gamma> \<Longrightarrow> eps_states \<Delta> |\<subseteq>| eps_states \<Gamma>"
  unfolding eps_states_def
  by transfer auto

lemma eps_statesI [intro]:
  "(p, q) |\<in>| \<Delta> \<Longrightarrow> p |\<in>| eps_states \<Delta>"
  "(p, q) |\<in>| \<Delta> \<Longrightarrow> q |\<in>| eps_states \<Delta>"
  unfolding eps_states_def
  by (auto simp add: rev_image_eqI)

lemma eps_statesE [elim]:
  assumes "p |\<in>| eps_states \<Delta>"
  obtains q where "(p, q) |\<in>| \<Delta> \<or> (q, p) |\<in>| \<Delta>" using assms
  unfolding eps_states_def
  by (transfer, auto)+

lemma rule_statesE [elim]:
  assumes "q |\<in>| rule_states \<Delta>"
  obtains f ps p where "TA_rule f ps p |\<in>| \<Delta>" "q |\<in>| (fset_of_list ps) \<or> q = p" using assms
proof -
  assume ass: "(\<And>f ps p. f ps \<rightarrow> p |\<in>| \<Delta> \<Longrightarrow> q |\<in>| fset_of_list ps \<or> q = p \<Longrightarrow> thesis)"
  from assms obtain r where "r |\<in>| \<Delta>" "q |\<in>| fset_of_list (r_lhs_states r) \<or> q = r_rhs r"
    by (auto simp: rule_states_def)
  then show thesis using ass
    by (cases r) auto
qed

lemma rule_statesI [intro]:
  assumes "r |\<in>| \<Delta>" "q |\<in>| finsert (r_rhs r) (fset_of_list (r_lhs_states r))"
  shows "q |\<in>| rule_states \<Delta>" using assms
  by (auto simp: rule_states_def)


text \<open>Destruction rule for states\<close>

lemma rule_statesD:
  "r |\<in>| (rules \<A>) \<Longrightarrow> r_rhs r |\<in>| \<Q> \<A>" "f qs \<rightarrow> q |\<in>| (rules \<A>) \<Longrightarrow> q |\<in>| \<Q> \<A>"
  "r |\<in>| (rules \<A>) \<Longrightarrow> p |\<in>| fset_of_list (r_lhs_states r) \<Longrightarrow> p |\<in>| \<Q> \<A>"
  "f qs \<rightarrow> q |\<in>| (rules \<A>) \<Longrightarrow> p |\<in>| fset_of_list qs \<Longrightarrow> p |\<in>| \<Q> \<A>"
  by (force simp: \<Q>_def rule_states_def fimage_iff)+

lemma eps_states [simp]: "(eps \<A>) |\<subseteq>| \<Q> \<A> |\<times>| \<Q> \<A>"
  unfolding \<Q>_def eps_states_def rule_states_def
  by (auto simp add: rev_image_eqI)

lemma eps_statesD: "(p, q) |\<in>| (eps \<A>) \<Longrightarrow> p |\<in>| \<Q> \<A> \<and> q |\<in>| \<Q> \<A>"
  using eps_states by (auto simp add: \<Q>_def)

lemma eps_trancl_statesD:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> p |\<in>| \<Q> \<A> \<and> q |\<in>| \<Q> \<A>"
  by (induct rule: ftrancl_induct) (auto dest: eps_statesD)

lemmas eps_dest_all = eps_statesD eps_trancl_statesD

text \<open>Mapping over function symbols/states\<close>

lemma finite_Collect_ta_rule:
  "finite {TA_rule f qs q | f qs q. TA_rule f qs q |\<in>| rules \<A>}" (is "finite ?S")
proof -
  have "{f qs \<rightarrow> q |f qs q. f qs \<rightarrow> q |\<in>| rules \<A>} \<subseteq> fset (rules \<A>)"
    by auto
  from finite_subset[OF this] show ?thesis by simp
qed

lemma map_ta_rule_finite:
  "finite \<Delta> \<Longrightarrow> finite {TA_rule (g h) (map f qs) (f q) | h qs q. TA_rule h qs q \<in> \<Delta>}"
proof (induct rule: finite.induct)
  case (insertI A a)
  have union: "{TA_rule (g h) (map f qs) (f q) |h qs q. TA_rule h qs q \<in> insert a A} =
    {TA_rule (g h) (map f qs) (f q) | h qs q. TA_rule h qs q = a} \<union> {TA_rule (g h) (map f qs) (f q) |h qs q. TA_rule h qs q \<in> A}"
    by auto
  have "finite {g h map f qs \<rightarrow> f q |h qs q. h qs \<rightarrow> q = a}"
    by (cases a) auto
  from finite_UnI[OF this insertI(2)] show ?case unfolding union .
qed auto

lemmas map_ta_rule_fset_finite [simp] = map_ta_rule_finite[of "fset \<Delta>" for \<Delta>, simplified]
lemmas map_ta_rule_states_finite [simp] = map_ta_rule_finite[of "fset \<Delta>" id for \<Delta>, simplified]
lemmas map_ta_rule_funsym_finite [simp] = map_ta_rule_finite[of "fset \<Delta>" _ id for \<Delta>, simplified]

lemma map_ta_rule_comp:
  "map_ta_rule f g \<circ> map_ta_rule f' g' = map_ta_rule (f \<circ> f') (g \<circ> g')"
  using ta_rule.map_comp[of f g]
  by (auto simp: comp_def)

lemma map_ta_rule_cases:
  "map_ta_rule f g r = TA_rule (g (r_root r)) (map f (r_lhs_states r)) (f (r_rhs r))"
  by (cases r) auto

lemma map_ta_rule_prod_swap_id [simp]:
  "map_ta_rule prod.swap prod.swap (map_ta_rule prod.swap prod.swap r) = r"
  by (auto simp: map_ta_rule_cases)


lemma rule_states_image [simp]:
  "rule_states (map_ta_rule f g |`| \<Delta>) = f |`| rule_states \<Delta>" (is "?Ls = ?Rs")
proof -
  {fix q assume "q |\<in>| ?Ls"
    then obtain r where "r |\<in>| \<Delta>"
      "q |\<in>| finsert (r_rhs (map_ta_rule f g r)) (fset_of_list (r_lhs_states (map_ta_rule f g r)))"
      by (auto simp: rule_states_def)
    then have "q |\<in>| ?Rs" by (cases r) (force simp: fimage_iff)}
  moreover
  {fix q assume "q |\<in>| ?Rs"
    then obtain r p where "r |\<in>| \<Delta>" "f p = q"
      "p |\<in>| finsert (r_rhs r) (fset_of_list (r_lhs_states r))"
      by (auto simp: rule_states_def)
    then have "q |\<in>| ?Ls" by (cases r) (force simp: fimage_iff)}
  ultimately show ?thesis by blast
qed

lemma \<Q>_mono:
  "(rules \<A>) |\<subseteq>| (rules \<B>) \<Longrightarrow> (eps \<A>) |\<subseteq>| (eps \<B>) \<Longrightarrow> \<Q> \<A> |\<subseteq>| \<Q> \<B>"
  using rule_states_mono eps_states_mono unfolding \<Q>_def
  by blast

lemma \<Q>_subseteq_I:
  assumes "\<And> r. r |\<in>| rules \<A> \<Longrightarrow> r_rhs r |\<in>| S"
    and "\<And> r. r |\<in>| rules \<A> \<Longrightarrow> fset_of_list (r_lhs_states r) |\<subseteq>| S"
    and "\<And> e. e |\<in>| eps \<A> \<Longrightarrow> fst e |\<in>| S \<and> snd e |\<in>| S"
  shows "\<Q> \<A> |\<subseteq>| S" using assms unfolding \<Q>_def
  by (auto simp: rule_states_def) blast

lemma finite_states:
  "finite {q. \<exists> f p ps. f ps \<rightarrow> p |\<in>| rules \<A> \<and> (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)}" (is "finite ?set")
proof -
  have "?set \<subseteq> fset (\<Q> \<A>)"
    by (intro subsetI, drule CollectD)
       (metis eps_trancl_statesD rule_statesD(2))
  from finite_subset[OF this] show ?thesis by auto
qed

text \<open>Collecting all states reachable from target of rules\<close>

lemma finite_ta_rhs_states [simp]:
  "finite {q. \<exists>p. p |\<in>| rule_target_states (rules \<A>) \<and> (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)}" (is "finite ?Set")
proof -
  have "?Set \<subseteq> fset (\<Q> \<A>)"
    by (auto dest: rule_statesD)
       (metis eps_trancl_statesD rule_statesD(1))+
  from finite_subset[OF this] show ?thesis
    by auto
qed

text \<open>Computing the signature induced by the rule set of given tree automaton\<close>



lemma ta_sigI [intro]:
  "TA_rule f qs q |\<in>| (rules \<A>) \<Longrightarrow> length qs = n \<Longrightarrow> (f, n) |\<in>| ta_sig \<A>" unfolding ta_sig_def
  using mk_disjoint_finsert by fastforce

lemma ta_sig_mono:
  "(rules \<A>) |\<subseteq>| (rules \<B>) \<Longrightarrow> ta_sig \<A> |\<subseteq>| ta_sig \<B>"
  by (auto simp: ta_sig_def)

lemma finite_eps:
  "finite {q. \<exists> f ps p. f ps \<rightarrow> p |\<in>| rules \<A> \<and> (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|)}" (is "finite ?S")
  by (intro finite_subset[OF _ finite_ta_rhs_states[of \<A>]]) (auto intro!: bexI)

lemma collect_snd_trancl_fset:
  "{p. (q, p) |\<in>| (eps \<A>)|\<^sup>+|} = fset (snd |`| (ffilter (\<lambda> x. fst x = q) ((eps \<A>)|\<^sup>+|)))"
  by (auto simp: image_iff) force

lemma ta_der_Var:
  "q |\<in>| ta_der \<A> (Var x) \<longleftrightarrow> x = q \<or> (x, q) |\<in>| (eps \<A>)|\<^sup>+|"
  by (auto simp: collect_snd_trancl_fset)

lemma ta_der_Fun:
  "q |\<in>| ta_der \<A> (Fun f ts) \<longleftrightarrow> (\<exists> ps p. TA_rule f ps p |\<in>| (rules \<A>) \<and>
      (p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+|) \<and> length ps = length ts \<and> 
      (\<forall> i < length ts. ps ! i |\<in>| ta_der \<A> (ts ! i)))" (is "?Ls \<longleftrightarrow> ?Rs")
  unfolding ta_der.simps
  by (intro iffI fCollect_memberI finite_Collect_less_eq[OF _ finite_eps[of \<A>]]) auto

declare ta_der.simps[simp del]
declare ta_der.simps[code del]
lemmas ta_der_simps [simp] = ta_der_Var ta_der_Fun

lemma ta_der'_Var:
  "Var q |\<in>| ta_der' \<A> (Var x) \<longleftrightarrow> x = q \<or> (x, q) |\<in>| (eps \<A>)|\<^sup>+|"
  by (auto simp: collect_snd_trancl_fset)

lemma ta_der'_Fun:
  "Var q |\<in>| ta_der' \<A> (Fun f ts) \<longleftrightarrow> q |\<in>| ta_der \<A> (Fun f ts)"
  unfolding ta_der'.simps
  by (intro iffI funionI1 fCollect_memberI)
     (auto simp del: ta_der_Fun ta_der_Var simp: fset_image_conv)

lemma ta_der'_Fun2:
  "Fun f ps |\<in>| ta_der' \<A> (Fun g ts) \<longleftrightarrow> f = g \<and> length ps = length ts \<and> (\<forall>i<length ts. ps ! i |\<in>| ta_der' \<A> (ts ! i))"
proof -
  have f: "finite {ss. set ss \<subseteq> fset ( |\<Union>| (fset_of_list (map (ta_der' \<A>) ts))) \<and> length ss = length ts}"
    by (intro finite_lists_length_eq) auto
  have "finite {ss. length ss = length ts \<and> (\<forall>i<length ts. ss ! i |\<in>| ta_der' \<A> (ts ! i))}"
    by (intro finite_subset[OF _ f])
       (force simp: in_fset_conv_nth simp flip: fset_of_list_elem)
  then show ?thesis unfolding ta_der'.simps
    by (intro iffI funionI2 fCollect_memberI)
       (auto simp del: ta_der_Fun ta_der_Var)
qed

declare ta_der'.simps[simp del]
declare ta_der'.simps[code del]
lemmas ta_der'_simps [simp] = ta_der'_Var ta_der'_Fun ta_der'_Fun2

text \<open>Induction schemes for the most used cases\<close>

lemma ta_der_induct[consumes 1, case_names Var Fun]:
  assumes reach: "q |\<in>| ta_der \<A> t"
  and VarI: "\<And> q v. v = q \<or> (v, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> P (Var v) q"
  and FunI: "\<And>f ts ps p q. f ps \<rightarrow> p |\<in>| rules \<A> \<Longrightarrow> length ts = length ps \<Longrightarrow> p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow>
    (\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der \<A> (ts ! i)) \<Longrightarrow>
    (\<And>i. i < length ts \<Longrightarrow> P (ts ! i) (ps ! i)) \<Longrightarrow> P (Fun f ts) q"
  shows "P t q" using assms(1)
  by (induct t arbitrary: q) (auto simp: VarI FunI)

lemma ta_der_gterm_induct[consumes 1, case_names GFun]:
  assumes reach: "q |\<in>| ta_der \<A> (term_of_gterm t)"
  and Fun: "\<And>f ts ps p q. TA_rule f ps p |\<in>| rules \<A> \<Longrightarrow> length ts = length ps \<Longrightarrow> p = q \<or> (p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow>
    (\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der \<A> (term_of_gterm (ts ! i))) \<Longrightarrow>
    (\<And>i. i < length ts \<Longrightarrow> P (ts ! i) (ps ! i)) \<Longrightarrow> P (GFun f ts) q"
  shows "P t q" using assms(1)
  by (induct t arbitrary: q) (auto simp: Fun)

lemma ta_der_rule_empty:
  assumes "q |\<in>| ta_der (TA {||} \<Delta>\<^sub>\<epsilon>) t"
  obtains p where "t = Var p" "p = q \<or> (p, q) |\<in>| \<Delta>\<^sub>\<epsilon>|\<^sup>+|"
  using assms by (cases t) auto

lemma ta_der_eps:
  assumes "(p, q) |\<in>| (eps \<A>)" and "p |\<in>| ta_der \<A> t"
  shows "q |\<in>| ta_der \<A> t" using assms
  by (cases t) (auto intro: ftrancl_into_trancl)

lemma ta_der_trancl_eps:
  assumes "(p, q) |\<in>| (eps \<A>)|\<^sup>+|" and "p |\<in>| ta_der \<A> t"
  shows "q |\<in>| ta_der \<A> t" using assms
  by (induct rule: ftrancl_induct) (auto intro: ftrancl_into_trancl ta_der_eps)

lemma ta_der_mono:
  "(rules \<A>) |\<subseteq>| (rules \<B>) \<Longrightarrow> (eps \<A>) |\<subseteq>| (eps \<B>) \<Longrightarrow> ta_der \<A> t |\<subseteq>| ta_der \<B> t"
proof (induct t)
  case (Var x) then show ?case
    by (auto dest: ftrancl_mono[of _ "eps \<A>" "eps \<B>"])
next
  case (Fun f ts)
  show ?case using Fun(1)[OF nth_mem Fun(2, 3)]
    by (auto dest!: fsubsetD[OF Fun(2)] ftrancl_mono[OF _ Fun(3)]) blast+
qed

lemma ta_der_el_mono:
  "(rules \<A>) |\<subseteq>| (rules \<B>) \<Longrightarrow> (eps \<A>) |\<subseteq>| (eps \<B>) \<Longrightarrow> q |\<in>| ta_der \<A> t \<Longrightarrow> q |\<in>| ta_der \<B> t"
  using ta_der_mono by blast

lemma ta_der'_ta_der:
  assumes "t |\<in>| ta_der' \<A> s" "p |\<in>| ta_der \<A> t"
  shows "p |\<in>| ta_der \<A> s" using assms
proof (induction arbitrary: p t rule: ta_der'.induct)
  case (2 \<A> f ts) show ?case using 2(2-)
  proof (induction t)
    case (Var x) then show ?case
      by auto (meson ftrancl_trans)
  next
    case (Fun g ss)
    have ss_props: "g = f" "length ss = length ts" "\<forall>i < length ts. ss ! i |\<in>| ta_der' \<A> (ts ! i)"
      using Fun(2) by auto
    then show ?thesis using Fun(1)[OF nth_mem] Fun(2-)
      by (auto simp: ss_props)
         (metis (no_types, lifting) "2.IH" ss_props(3))+  
  qed
qed (auto dest: ftrancl_trans simp: ta_der'.simps)

lemma ta_der'_empty:
  assumes "t |\<in>| ta_der' (TA {||} {||}) s"
  shows "t = s" using assms
  by (induct s arbitrary: t) (auto simp add: ta_der'.simps nth_equalityI)

lemma ta_der'_to_ta_der:
  "Var q |\<in>| ta_der' \<A> s \<Longrightarrow> q |\<in>| ta_der \<A> s"
  using ta_der'_ta_der by fastforce

lemma ta_der_to_ta_der':
  "q |\<in>| ta_der \<A> s \<longleftrightarrow> Var q |\<in>| ta_der' \<A> s "
  by (induct s arbitrary: q) auto

lemma ta_der'_poss:
  assumes "t |\<in>| ta_der' \<A> s"
  shows "poss t \<subseteq> poss s" using assms
proof (induct s arbitrary: t)
  case (Fun f ts)
  show ?case using Fun(2) Fun(1)[OF nth_mem, of i "args t ! i" for i]
    by (cases t) auto
qed (auto simp: ta_der'.simps)

lemma ta_der'_refl[simp]: "t |\<in>| ta_der' \<A> t"
  by (induction t) fastforce+

lemma ta_der'_eps:
  assumes "Var p |\<in>| ta_der' \<A> s" and "(p, q) |\<in>| (eps \<A>)|\<^sup>+|"
  shows "Var q |\<in>| ta_der' \<A> s" using assms
  by (cases s, auto dest: ftrancl_trans) (meson ftrancl_trans)

lemma ta_der'_trans:
  assumes "t |\<in>| ta_der' \<A> s" and "u |\<in>| ta_der' \<A> t"
  shows "u |\<in>| ta_der' \<A> s" using assms
proof (induct t arbitrary: u s)
  case (Fun f ts) note IS = Fun(2-) note IH = Fun(1)[OF nth_mem, of i "args s ! i" for i]
  show ?case
  proof (cases s)
    case (Var x1)
    then show ?thesis using IS by (auto simp: ta_der'.simps)
  next
    case [simp]: (Fun g ss)
    show ?thesis using IS IH
      by (cases u, auto) (metis ta_der_to_ta_der')+
  qed
qed (auto simp: ta_der'.simps ta_der'_eps)

text \<open>Connecting contexts to derivation definition\<close>

lemma ta_der_ctxt:
  assumes p: "p |\<in>| ta_der \<A> t" "q |\<in>| ta_der \<A> C\<langle>Var p\<rangle>"
  shows "q |\<in>| ta_der \<A> C\<langle>t\<rangle>" using assms(2)
proof (induct C arbitrary: q)
  case Hole then show ?case using assms
    by (auto simp: ta_der_trancl_eps)
next
  case (More f ss C ts)
  from More(2) obtain qs r where
    rule: "f qs \<rightarrow> r |\<in>| rules \<A>" "length qs = Suc (length ss + length ts)" and
    reach: "\<forall> i < Suc (length ss + length ts). qs ! i |\<in>| ta_der \<A> ((ss @ C\<langle>Var p\<rangle> # ts) ! i)" "r = q \<or> (r, q) |\<in>| (eps \<A>)|\<^sup>+|"
    by auto
  have "i < Suc (length ss + length ts) \<Longrightarrow> qs ! i |\<in>| ta_der \<A> ((ss @ C\<langle>t\<rangle> # ts) ! i)" for i
    using More(1)[of "qs ! length ss"] assms rule(2) reach(1)
    unfolding nth_append_Cons by presburger
  then show ?case using rule reach(2) by auto
qed

lemma ta_der_eps_ctxt:
  assumes "p |\<in>| ta_der A C\<langle>Var q'\<rangle>" and "(q, q') |\<in>| (eps A)|\<^sup>+|"
  shows "p |\<in>| ta_der A C\<langle>Var q\<rangle>"
  using assms by (meson ta_der_Var ta_der_ctxt) 

lemma rule_reachable_ctxt_exist:
  assumes rule: "f qs \<rightarrow> q |\<in>| rules \<A>" and "i < length qs"
  shows "\<exists> C. q |\<in>| ta_der \<A> (C \<langle>Var (qs ! i)\<rangle>)" using assms
  by (intro exI[of _ "More f (map Var (take i qs)) \<box> (map Var (drop (Suc i) qs))"])
     (auto simp: min_def nth_append_Cons intro!: exI[of _ q] exI[of _ qs])

lemma ta_der_ctxt_decompose:
  assumes "q |\<in>| ta_der \<A> C\<langle>t\<rangle>"
  shows "\<exists> p . p |\<in>| ta_der \<A> t \<and> q |\<in>| ta_der \<A> C\<langle>Var p\<rangle>" using assms
proof (induct C arbitrary: q)
  case (More f ss C ts)
  from More(2) obtain qs r where
    rule: "f qs \<rightarrow> r |\<in>| rules \<A>" "length qs = Suc (length ss + length ts)" and
    reach: "\<forall> i < Suc (length ss + length ts). qs ! i |\<in>| ta_der \<A> ((ss @ C\<langle>t\<rangle> # ts) ! i)"
       "r = q \<or> (r, q) |\<in>| (eps \<A>)|\<^sup>+|"
    by auto
  obtain p where p: "p |\<in>| ta_der \<A> t" "qs ! length ss |\<in>| ta_der \<A> C\<langle>Var p\<rangle>"
    using More(1)[of "qs ! length ss"] reach(1) rule(2)
    by (metis less_add_Suc1 nth_append_length)
  have "i < Suc (length ss + length ts) \<Longrightarrow> qs ! i |\<in>| ta_der \<A> ((ss @ C\<langle>Var p\<rangle> # ts) ! i)" for i
    using reach rule(2) p by (auto simp: p(2) nth_append_Cons)
  then have "q |\<in>| ta_der \<A> (More f ss C ts)\<langle>Var p\<rangle>" using rule reach
    by auto
  then show ?case using p(1) by (intro exI[of _ p]) blast
qed auto

\<comment> \<open>Relation between reachable states and states of a tree automaton\<close>

lemma ta_der_states:
  "ta_der \<A> t |\<subseteq>| \<Q> \<A> |\<union>| fvars_term t"
proof (induct t)
  case (Var x) then show ?case
    by (auto simp: eq_onp_same_args) 
       (metis eps_trancl_statesD)
  case (Fun f ts) then show ?case
    by (auto simp: rule_statesD(2) eps_trancl_statesD)
qed

lemma ground_ta_der_states:
  "ground t \<Longrightarrow> ta_der \<A> t |\<subseteq>| \<Q> \<A>"
  using ta_der_states[of \<A> t] by auto

lemmas ground_ta_der_statesD = fsubsetD[OF ground_ta_der_states]

lemma gterm_ta_der_states [simp]:
  "q |\<in>| ta_der \<A> (term_of_gterm t) \<Longrightarrow> q |\<in>| \<Q> \<A>"
  by (intro ground_ta_der_states[THEN fsubsetD, of "term_of_gterm t"]) simp

lemma ta_der_states':
  "q |\<in>| ta_der \<A> t \<Longrightarrow> q |\<in>| \<Q> \<A> \<Longrightarrow> fvars_term t |\<subseteq>| \<Q> \<A>"
proof (induct rule: ta_der_induct)
  case (Fun f ts ps p r)
  then have "i < length ts \<Longrightarrow> fvars_term (ts ! i) |\<subseteq>| \<Q> \<A>" for i
    by (auto simp: in_fset_conv_nth dest!: rule_statesD(3))
  then show ?case by (force simp: in_fset_conv_nth)
qed (auto simp: eps_trancl_statesD)

lemma ta_der_not_stateD:
  "q |\<in>| ta_der \<A> t \<Longrightarrow> q |\<notin>| \<Q> \<A> \<Longrightarrow> t = Var q"
  using fsubsetD[OF ta_der_states, of q \<A> t]
  by (cases t) (auto dest: rule_statesD eps_trancl_statesD)

lemma ta_der_is_fun_stateD:
  "is_Fun t \<Longrightarrow> q |\<in>| ta_der \<A> t \<Longrightarrow> q |\<in>| \<Q> \<A>"
  using ta_der_not_stateD[of q \<A> t]
  by (cases t) auto

lemma ta_der_is_fun_fvars_stateD:
  "is_Fun t \<Longrightarrow> q |\<in>| ta_der \<A> t \<Longrightarrow> fvars_term t |\<subseteq>| \<Q> \<A>"
  using ta_der_is_fun_stateD[of t q \<A>]
  using ta_der_states'[of q \<A> t]
  by (cases t) auto

lemma ta_der_not_reach:
  assumes "\<And> r. r |\<in>| rules \<A> \<Longrightarrow> r_rhs r \<noteq> q"
    and "\<And> e. e |\<in>| eps \<A> \<Longrightarrow> snd e \<noteq> q"
  shows "q |\<notin>| ta_der \<A> (term_of_gterm t)" using assms
  by (cases t) (fastforce dest!: assms(1) ftranclD2[of _ q])


lemma ta_rhs_states_subset_states: "ta_rhs_states \<A> |\<subseteq>| \<Q> \<A>"
  by (auto simp: ta_rhs_states_def dest: rtranclD rule_statesD eps_trancl_statesD)

(* a resulting state is always some rhs of a rule (or epsilon transition) *)
lemma ta_rhs_states_res: assumes "is_Fun t" 
  shows "ta_der \<A> t |\<subseteq>| ta_rhs_states \<A>"
proof
  fix q assume q: "q |\<in>| ta_der \<A> t"
  from \<open>is_Fun t\<close> obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from q[unfolded t] obtain q' qs where "TA_rule f qs q' |\<in>| rules \<A>" 
    and q: "q' = q \<or> (q', q) |\<in>| (eps \<A>)|\<^sup>+|" by auto
  then show "q |\<in>| ta_rhs_states \<A>" unfolding ta_rhs_states_def
    by (auto intro!: bexI)
qed

text \<open>Reachable states of ground terms are preserved over the @{const adapt_vars} function\<close>

lemma ta_der_adapt_vars_ground [simp]:
  "ground t \<Longrightarrow> ta_der A (adapt_vars t) = ta_der A t"
  by (induct t) auto

lemma gterm_of_term_inv':
  "ground t \<Longrightarrow> term_of_gterm (gterm_of_term t) = adapt_vars t"
  by (induct t) (auto 0 0 intro!: nth_equalityI)

lemma map_vars_term_term_of_gterm:
  "map_vars_term f (term_of_gterm t) = term_of_gterm t"
  by (induct t) auto

lemma adapt_vars_term_of_gterm:
  "adapt_vars (term_of_gterm t) = term_of_gterm t"
  by (induct t) auto

(* a term can be reduced to a state, only if all symbols appear in the automaton *)
lemma ta_der_term_sig:
  "q |\<in>| ta_der \<A> t \<Longrightarrow> ffunas_term t |\<subseteq>| ta_sig \<A>"
proof (induct rule: ta_der_induct)
  case (Fun f ts ps p q)
  show ?case using Fun(1 - 4) Fun(5)[THEN fsubsetD]
    by (auto simp: in_fset_conv_nth)
qed auto

lemma ta_der_gterm_sig:
  "q |\<in>| ta_der \<A> (term_of_gterm t) \<Longrightarrow> ffunas_gterm t |\<subseteq>| ta_sig \<A>"
  using ta_der_term_sig ffunas_term_of_gterm_conv
  by fastforce

text \<open>@{const ta_lang} for terms with arbitrary variable type\<close>

lemma ta_langE: assumes "t \<in> ta_lang Q \<A>"
  obtains t' q where "ground t'" "q |\<in>| Q" "q |\<in>| ta_der \<A> t'" "t = adapt_vars t'"
  using assms unfolding ta_lang_def by blast

lemma ta_langI: assumes "ground t'" "q |\<in>| Q" "q |\<in>| ta_der \<A> t'" "t = adapt_vars t'"
  shows "t \<in> ta_lang Q \<A>"
  using assms unfolding ta_lang_def by blast

lemma ta_lang_def2: "(ta_lang Q (\<A> :: ('q,'f)ta) :: ('f,'v)terms) = {t. ground t \<and> Q |\<inter>| ta_der \<A> (adapt_vars t) \<noteq> {||}}"
  by (auto elim!: ta_langE) (metis adapt_vars_adapt_vars ground_adapt_vars ta_langI)

text \<open>@{const ta_lang} for @{const gterms}\<close>

lemma ta_lang_to_gta_lang [simp]:
  "ta_lang Q \<A> = term_of_gterm ` gta_lang Q \<A>" (is "?Ls = ?Rs")
proof -
  {fix t assume "t \<in> ?Ls"
    from ta_langE[OF this] obtain q t' where "ground t'" "q |\<in>| Q" "q |\<in>| ta_der \<A> t'" "t = adapt_vars t'"
      by blast
    then have "t \<in> ?Rs" unfolding gta_lang_def gta_der_def
      by (auto simp: image_iff gterm_of_term_inv' intro!: exI[of _ "gterm_of_term t'"])}
  moreover
  {fix t assume "t \<in> ?Rs" then have "t \<in> ?Ls"
      using ta_langI[OF ground_term_of_gterm _ _  gterm_of_term_inv'[OF ground_term_of_gterm]]
      by (force simp: gta_lang_def gta_der_def)}
  ultimately show ?thesis by blast
qed

lemma term_of_gterm_in_ta_lang_conv:
  "term_of_gterm t \<in> ta_lang Q \<A> \<longleftrightarrow> t \<in> gta_lang Q \<A>"
  by (metis (mono_tags, lifting) image_iff ta_lang_to_gta_lang term_of_gterm_inv)

lemma gta_lang_def_sym:
  "gterm_of_term ` ta_lang Q \<A> = gta_lang Q \<A>"
  (* this is nontrivial because the lhs has a more general type than the rhs of gta_lang_def *)
  unfolding gta_lang_def image_def
  by (intro Collect_cong) (simp add: gta_lang_def)

lemma gta_langI [intro]:
  assumes "q |\<in>| Q" and "q |\<in>| ta_der \<A> (term_of_gterm t)"
  shows "t \<in> gta_lang Q \<A>" using assms
  by (metis adapt_vars_term_of_gterm ground_term_of_gterm ta_langI term_of_gterm_in_ta_lang_conv)

lemma gta_langE [elim]:
  assumes "t \<in> gta_lang Q \<A>"
  obtains q where "q |\<in>| Q" and "q |\<in>| ta_der \<A> (term_of_gterm t)" using assms
  by (metis adapt_vars_adapt_vars adapt_vars_term_of_gterm ta_langE term_of_gterm_in_ta_lang_conv) 

lemma gta_lang_mono:
  assumes "\<And> t. ta_der \<A> t |\<subseteq>| ta_der \<BB> t" and "Q\<^sub>\<A> |\<subseteq>| Q\<^sub>\<BB>"
  shows "gta_lang Q\<^sub>\<A> \<A> \<subseteq> gta_lang Q\<^sub>\<BB> \<BB>"
  using assms by (auto elim!: gta_langE intro!: gta_langI)

lemma gta_lang_term_of_gterm [simp]:
  "term_of_gterm t \<in> term_of_gterm ` gta_lang Q \<A> \<longleftrightarrow> t \<in> gta_lang Q \<A>"
  by (auto elim!: gta_langE intro!: gta_langI) (metis term_of_gterm_inv)

(* terms can be accepted, only if all their symbols appear in the automaton *)
lemma gta_lang_subset_rules_funas:
  "gta_lang Q \<A> \<subseteq> \<T>\<^sub>G (fset (ta_sig \<A>))"
  using ta_der_gterm_sig[THEN fsubsetD]
  by (force simp: \<T>\<^sub>G_equivalent_def ffunas_gterm.rep_eq)

lemma reg_funas:
  "\<L> \<A> \<subseteq> \<T>\<^sub>G (fset (ta_sig (ta \<A>)))" using gta_lang_subset_rules_funas
  by (auto simp: \<L>_def)

lemma ta_syms_lang: "t \<in> ta_lang Q \<A> \<Longrightarrow> ffunas_term t |\<subseteq>| ta_sig \<A>"
  using gta_lang_subset_rules_funas ffunas_gterm_gterm_of_term ta_der_gterm_sig ta_lang_def2
  by fastforce

lemma gta_lang_Rest_states_conv:
  "gta_lang Q \<A> = gta_lang (Q |\<inter>| \<Q> \<A>) \<A>"
  by (auto elim!: gta_langE)

lemma reg_Rest_fin_states [simp]:
  "\<L> (reg_Restr_Q\<^sub>f \<A>) = \<L> \<A>"
  using gta_lang_Rest_states_conv
  by (auto simp: \<L>_def reg_Restr_Q\<^sub>f_def)

text \<open>Deterministic tree automatons\<close>

definition ta_det :: "('q,'f) ta \<Rightarrow> bool" where
  "ta_det \<A> \<longleftrightarrow> eps \<A> = {||} \<and> 
    (\<forall> f qs q q'. TA_rule f qs q |\<in>| rules \<A> \<longrightarrow> TA_rule f qs q' |\<in>| rules \<A> \<longrightarrow> q = q')"

definition "ta_subset \<A> \<B> \<longleftrightarrow> rules \<A> |\<subseteq>| rules \<B> \<and> eps \<A> |\<subseteq>| eps \<B>"

(* determinism implies unique results *)
lemma ta_detE[elim, consumes 1]: assumes det: "ta_det \<A>"
  shows "q |\<in>| ta_der \<A> t \<Longrightarrow> q' |\<in>| ta_der \<A> t \<Longrightarrow> q = q'" using assms
  by (induct t arbitrary: q q') (auto simp: ta_det_def, metis nth_equalityI nth_mem)


lemma ta_subset_states: "ta_subset \<A> \<B> \<Longrightarrow> \<Q> \<A> |\<subseteq>| \<Q> \<B>"
  using \<Q>_mono by (auto simp: ta_subset_def)

lemma ta_subset_refl[simp]: "ta_subset \<A> \<A>" 
  unfolding ta_subset_def by auto

lemma ta_subset_trans: "ta_subset \<A> \<B> \<Longrightarrow> ta_subset \<B> \<CC> \<Longrightarrow> ta_subset \<A> \<CC>"
  unfolding ta_subset_def by auto

lemma ta_subset_det: "ta_subset \<A> \<B> \<Longrightarrow> ta_det \<B> \<Longrightarrow> ta_det \<A>"
  unfolding ta_det_def ta_subset_def by blast

lemma ta_der_mono': "ta_subset \<A> \<B> \<Longrightarrow> ta_der \<A> t |\<subseteq>| ta_der \<B> t"
  using ta_der_mono unfolding ta_subset_def by auto

lemma ta_lang_mono': "ta_subset \<A> \<B> \<Longrightarrow> Q\<^sub>\<A> |\<subseteq>| Q\<^sub>\<B> \<Longrightarrow> ta_lang Q\<^sub>\<A> \<A> \<subseteq> ta_lang Q\<^sub>\<B> \<B>"
  using gta_lang_mono[of \<A> \<B>] ta_der_mono'[of \<A> \<B>]
  by auto blast

(* the restriction of an automaton to a given set of states *)
lemma ta_restrict_subset: "ta_subset (ta_restrict \<A> Q) \<A>"
  unfolding ta_subset_def ta_restrict_def
  by auto

lemma ta_restrict_states_Q: "\<Q> (ta_restrict \<A> Q) |\<subseteq>| Q"
  by (auto simp: \<Q>_def ta_restrict_def rule_states_def eps_states_def dest!: fsubsetD)

lemma ta_restrict_states: "\<Q> (ta_restrict \<A> Q) |\<subseteq>| \<Q> \<A>"
  using ta_subset_states[OF ta_restrict_subset] by fastforce 

lemma ta_restrict_states_eq_imp_eq [simp]:
  assumes eq: "\<Q> (ta_restrict \<A> Q) = \<Q> \<A>"
  shows "ta_restrict \<A> Q = \<A>" using assms
  apply (auto simp: ta_restrict_def
              intro!: ta.expand finite_subset[OF _ finite_Collect_ta_rule, of _ \<A>])
  apply (metis (no_types, lifting) eq fsubsetD fsubsetI rule_statesD(1) rule_statesD(4) ta_restrict_states_Q ta_rule.collapse)
  apply (metis eps_statesD eq fin_mono ta_restrict_states_Q)
  by (metis eps_statesD eq fsubsetD ta_restrict_states_Q)

lemma ta_der_ta_derict_states:
  "fvars_term t |\<subseteq>| Q \<Longrightarrow> q |\<in>| ta_der (ta_restrict \<A> Q) t \<Longrightarrow> q |\<in>| Q"
  by (induct t arbitrary: q) (auto simp: ta_restrict_def elim: ftranclE)

lemma ta_derict_ruleI [intro]:
  "TA_rule f qs q |\<in>| rules \<A> \<Longrightarrow> fset_of_list qs |\<subseteq>| Q \<Longrightarrow> q |\<in>| Q \<Longrightarrow> TA_rule f qs q |\<in>| rules (ta_restrict \<A> Q)"
  by (auto simp: ta_restrict_def intro!: ta.expand finite_subset[OF _ finite_Collect_ta_rule, of _ \<A>])

text \<open>Reachable and productive states: There always is a trim automaton\<close>

lemma finite_ta_reachable [simp]:
  "finite {q. \<exists>t. ground t \<and> q |\<in>| ta_der \<A> t}"
proof -
  have "{q. \<exists>t. ground t \<and> q |\<in>| ta_der \<A> t} \<subseteq> fset (\<Q> \<A>)"
    using ground_ta_der_states[of _ \<A>]
    by auto
  from finite_subset[OF this] show ?thesis by auto
qed

lemma ta_reachable_states:
  "ta_reachable \<A> |\<subseteq>| \<Q> \<A>"
  unfolding ta_reachable_def using ground_ta_der_states
  by force

lemma ta_reachableE:
  assumes "q |\<in>| ta_reachable \<A>"
  obtains t where "ground t" "q |\<in>| ta_der \<A> t"
  using assms[unfolded ta_reachable_def] by auto

lemma ta_reachable_gtermE [elim]:
  assumes "q |\<in>| ta_reachable \<A>"
  obtains t where "q |\<in>| ta_der \<A> (term_of_gterm t)"
  using ta_reachableE[OF assms]
  by (metis ground_term_to_gtermD) 

lemma ta_reachableI [intro]:
  assumes "ground t" and "q |\<in>| ta_der \<A> t"
  shows "q |\<in>| ta_reachable \<A>"
  using assms finite_ta_reachable
  by (auto simp: ta_reachable_def)

lemma ta_reachable_gtermI [intro]:
  "q |\<in>| ta_der \<A> (term_of_gterm t) \<Longrightarrow> q |\<in>| ta_reachable \<A>"
  by (intro ta_reachableI[of "term_of_gterm t"]) simp

lemma ta_reachableI_rule:
  assumes sub: "fset_of_list qs |\<subseteq>| ta_reachable \<A>"
    and rule: "TA_rule f qs q |\<in>| rules \<A>"
  shows "q |\<in>| ta_reachable \<A>"
    "\<exists> ts. length qs = length ts \<and> (\<forall> i < length ts. ground (ts ! i)) \<and>
      (\<forall> i < length ts. qs ! i |\<in>| ta_der \<A> (ts ! i))" (is "?G")
proof -
  {
    fix i
    assume i: "i < length qs"
    then have "qs ! i |\<in>| fset_of_list qs" by auto
    with sub have "qs ! i |\<in>| ta_reachable \<A>" by auto
    from ta_reachableE[OF this] have "\<exists> t. ground t \<and> qs ! i |\<in>| ta_der \<A> t" by auto
  }
  then have "\<forall> i. \<exists> t. i < length qs \<longrightarrow> ground t \<and> qs ! i |\<in>| ta_der \<A> t" by auto
  from choice[OF this] obtain ts where ts: "\<And> i. i < length qs \<Longrightarrow> ground (ts i) \<and> qs ! i |\<in>| ta_der \<A> (ts i)" by blast
  let ?t = "Fun f (map ts [0 ..< length qs])"
  have gt: "ground ?t" using ts by auto
  have r: "q |\<in>| ta_der \<A> ?t" unfolding ta_der_Fun using rule ts
    by (intro exI[of _ qs] exI[of _ q]) simp
  with gt show "q |\<in>| ta_reachable \<A>" by blast
  from gt ts show ?G by (intro exI[of _ "map ts [0..<length qs]"]) simp
qed

lemma ta_reachable_rule_gtermE:
  assumes "\<Q> \<A> |\<subseteq>| ta_reachable \<A>"
    and "TA_rule f qs q |\<in>| rules \<A>"
  obtains t where "groot t = (f, length qs)" "q |\<in>| ta_der \<A> (term_of_gterm t)"
proof -
  assume *: "\<And>t. groot t = (f, length qs) \<Longrightarrow> q |\<in>| ta_der \<A> (term_of_gterm t) \<Longrightarrow> thesis"
  from assms have "fset_of_list qs |\<subseteq>| ta_reachable \<A>"
    by (auto dest: rule_statesD(3))
  from ta_reachableI_rule[OF this assms(2)] obtain ts where args: "length qs = length ts"
    "\<forall> i < length ts. ground (ts ! i)" "\<forall> i < length ts. qs ! i |\<in>| ta_der \<A> (ts ! i)"
    using assms by force
  then show ?thesis using assms(2)
    by (intro *[of "GFun f (map gterm_of_term ts)"]) auto
qed

lemma ta_reachableI_eps':
  assumes reach: "q |\<in>| ta_reachable \<A>"
    and eps: "(q, q') |\<in>| (eps \<A>)|\<^sup>+|"  
  shows "q' |\<in>| ta_reachable \<A>"
proof -
  from ta_reachableE[OF reach] obtain t where g: "ground t" and res: "q |\<in>| ta_der \<A> t" by auto
  from ta_der_trancl_eps[OF eps res] g show ?thesis by blast
qed

lemma ta_reachableI_eps:
  assumes reach: "q |\<in>| ta_reachable \<A>"
    and eps: "(q, q') |\<in>| eps \<A>"  
  shows "q' |\<in>| ta_reachable \<A>"
  by (rule ta_reachableI_eps'[OF reach], insert eps, auto)

\<comment> \<open>Automata are productive on a set P if all states can reach a state in P\<close>


lemma finite_ta_productive:
  "finite {p. \<exists>q q' C. p = q \<and> q' |\<in>| ta_der \<A> C\<langle>Var q\<rangle> \<and> q' |\<in>| P}"
proof -
  {fix x q C assume ass: "x \<notin> fset P" "q |\<in>| P" "q |\<in>| ta_der \<A> C\<langle>Var x\<rangle>"
    then have "x \<in> fset (\<Q> \<A>)"
    proof (cases "is_Fun C\<langle>Var x\<rangle>")
      case True
      then show ?thesis using ta_der_is_fun_fvars_stateD[OF _ ass(3)]
        by auto
    next
      case False
      then show ?thesis using ass
        by (cases C, auto, (metis eps_trancl_statesD)+)
    qed}
  then have "{q | q q' C. q' |\<in>| ta_der \<A> (C\<langle>Var q\<rangle>) \<and> q' |\<in>| P} \<subseteq> fset (\<Q> \<A>) \<union> fset P" by auto
  from finite_subset[OF this] show ?thesis by auto
qed

lemma ta_productiveE: assumes "q |\<in>| ta_productive P \<A>"
  obtains q' C where "q' |\<in>| ta_der \<A> (C\<langle>Var q\<rangle>)" "q' |\<in>| P" 
  using assms[unfolded ta_productive_def] by auto

lemma ta_productiveI:
  assumes "q' |\<in>| ta_der \<A> (C\<langle>Var q\<rangle>)" "q' |\<in>| P" 
  shows "q |\<in>| ta_productive P \<A>"
  using assms unfolding ta_productive_def
  using finite_ta_productive
  by auto

lemma ta_productiveI': 
  assumes "q |\<in>| ta_der \<A> (C\<langle>Var p\<rangle>)" "q |\<in>| ta_productive P \<A>" 
  shows "p |\<in>| ta_productive P \<A>"
  using assms unfolding ta_productive_def
  by auto (metis (mono_tags, lifting) ctxt_ctxt_compose ta_der_ctxt)

lemma ta_productive_setI:
  "q |\<in>| P \<Longrightarrow> q |\<in>| ta_productive P \<A>"
  using ta_productiveI[of q \<A> \<box> q]
  by simp


lemma ta_reachable_empty_rules [simp]:
  "rules \<A> = {||} \<Longrightarrow> ta_reachable \<A> = {||}"
  by (auto simp: ta_reachable_def)
     (metis ground.simps(1) ta.exhaust_sel ta_der_rule_empty)

lemma ta_reachable_mono:
  "ta_subset \<A> \<B> \<Longrightarrow> ta_reachable \<A> |\<subseteq>| ta_reachable \<B>" using ta_der_mono'
  by (auto simp: ta_reachable_def) blast

lemma ta_reachabe_rhs_states: 
  "ta_reachable \<A> |\<subseteq>| ta_rhs_states \<A>"
proof -
  {fix q assume "q |\<in>| ta_reachable \<A>"
    then obtain t where "ground t" "q |\<in>| ta_der \<A> t"
      by (auto simp: ta_reachable_def)
    then have "q |\<in>| ta_rhs_states \<A>"
      by (cases t) (auto simp: ta_rhs_states_def intro!: bexI)}
  then show ?thesis by blast
qed

lemma ta_reachable_eps:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> p |\<in>| ta_reachable \<A> \<Longrightarrow> (p, q) |\<in>| (fRestr (eps \<A>) (ta_reachable \<A>))|\<^sup>+|"
proof (induct rule: ftrancl_induct)
  case (Base a b)
  then show ?case
    by (metis fSigmaI finterI fr_into_trancl ta_reachableI_eps)
next
  case (Step p q r)
  then have "q |\<in>| ta_reachable \<A>" "r |\<in>| ta_reachable \<A>"
    by (metis ta_reachableI_eps ta_reachableI_eps')+
  then show ?case using Step
    by (metis fSigmaI finterI ftrancl_into_trancl)
qed

(* major lemma to show that one can restrict to reachable states *)
lemma ta_der_only_reach:
  assumes "fvars_term t |\<subseteq>| ta_reachable \<A>"
  shows "ta_der \<A> t = ta_der (ta_only_reach \<A>) t" (is "?LS = ?RS")
proof -
  have "?RS |\<subseteq>| ?LS" using ta_der_mono'[OF ta_restrict_subset]
    by fastforce
  moreover
  {fix q assume "q |\<in>| ?LS"
    then have "q |\<in>| ?RS" using assms
    proof (induct rule: ta_der_induct)
      case (Fun f ts ps p q)
      from Fun(2, 6) have ta_reach [simp]: "i < length ps \<Longrightarrow> fvars_term (ts ! i) |\<subseteq>| ta_reachable \<A>" for i
        by auto (metis ffUnionI fimage_fset fnth_mem funionI2 length_map nth_map sup.orderE) 
      from Fun have r: "i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der (ta_only_reach \<A>) (ts ! i)"
        "i < length ts \<Longrightarrow> ps ! i |\<in>| ta_reachable \<A>" for i
        by (auto) (metis ta_reach ta_der_ta_derict_states)+
      then have "f ps \<rightarrow> p |\<in>| rules (ta_only_reach \<A>)"
        using Fun(1, 2)
        by (intro ta_derict_ruleI)
           (fastforce simp: in_fset_conv_nth intro!: ta_reachableI_rule[OF _ Fun(1)])+
      then show ?case using ta_reachable_eps[of p q] ta_reachableI_rule[OF _ Fun(1)] r Fun(2, 3)
        by (auto simp: ta_restrict_def intro!: exI[of _ p] exI[of _ ps])
    qed (auto simp: ta_restrict_def intro: ta_reachable_eps)}
  ultimately show ?thesis by blast
qed

lemma ta_der_gterm_only_reach:
  "ta_der \<A> (term_of_gterm t) = ta_der (ta_only_reach \<A>) (term_of_gterm t)"
  using ta_der_only_reach[of "term_of_gterm t" \<A>]
  by simp

lemma ta_reachable_ta_only_reach [simp]:
  "ta_reachable (ta_only_reach \<A>) = ta_reachable \<A>"  (is "?LS = ?RS")
proof -
  have "?LS |\<subseteq>| ?RS" using ta_der_mono'[OF ta_restrict_subset]
    by (auto simp: ta_reachable_def) fastforce
  moreover
  {fix t assume "ground (t :: ('b, 'a) term)"
    then have "ta_der \<A> t = ta_der (ta_only_reach \<A>) t" using ta_der_only_reach[of t \<A>]
      by simp}
  ultimately show ?thesis unfolding ta_reachable_def
    by auto
qed

lemma ta_only_reach_reachable:
  "\<Q> (ta_only_reach \<A>) |\<subseteq>| ta_reachable (ta_only_reach \<A>)"
  using ta_restrict_states_Q[of \<A> "ta_reachable \<A>"]
  by auto

(* It is sound to restrict to reachable states. *)
lemma gta_only_reach_lang:
  "gta_lang Q (ta_only_reach \<A>) = gta_lang Q \<A>"
  using ta_der_gterm_only_reach
  by (auto elim!: gta_langE intro!: gta_langI) force+


lemma \<L>_only_reach: "\<L> (reg_reach R) = \<L> R"
  using gta_only_reach_lang
  by (auto simp: \<L>_def reg_reach_def)

lemma ta_only_reach_lang:
  "ta_lang Q (ta_only_reach \<A>) = ta_lang Q \<A>"
  using gta_only_reach_lang
  by (metis ta_lang_to_gta_lang)


lemma ta_prod_epsD:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> q |\<in>| ta_productive P \<A> \<Longrightarrow> p |\<in>| ta_productive P \<A>"
  using ta_der_ctxt[of q \<A> "\<box>\<langle>Var p\<rangle>"]
  by (auto simp: ta_productive_def ta_der_trancl_eps)

lemma ta_only_prod_eps:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> q |\<in>| ta_productive P \<A> \<Longrightarrow> (p, q) |\<in>| (eps (ta_only_prod P \<A>))|\<^sup>+|"
proof (induct rule: ftrancl_induct)
  case (Base p q)
  then show ?case
    by (metis (no_types, lifting) fSigmaI finterI fr_into_trancl ta.sel(2) ta_prod_epsD ta_restrict_def)
next
  case (Step p q r) note IS = this
  show ?case using IS(2 - 4) ta_prod_epsD[OF fr_into_trancl[OF IS(3)] IS(4)] 
    by (auto simp: ta_restrict_def) (simp add: ftrancl_into_trancl)
qed

(* Major lemma to show that it is sound to restrict to productive states. *)
lemma ta_der_only_prod: 
  "q |\<in>| ta_der \<A> t \<Longrightarrow> q |\<in>| ta_productive P \<A> \<Longrightarrow> q |\<in>| ta_der (ta_only_prod P \<A>) t"
proof (induct rule: ta_der_induct)
  case (Fun f ts ps p q)
  let ?\<A> = "ta_only_prod P \<A>"
  have pr: "p |\<in>| ta_productive P \<A>" "i < length ts \<Longrightarrow> ps ! i |\<in>| ta_productive P \<A>" for i
    using Fun(2) ta_prod_epsD[of p q] Fun(3, 6) rule_reachable_ctxt_exist[OF Fun(1)]
    using ta_productiveI'[of p \<A> _ "ps ! i" P]
    by auto
  then have "f ps \<rightarrow> p |\<in>| rules ?\<A>" using Fun(1, 2) unfolding ta_restrict_def
    by (auto simp: in_fset_conv_nth intro: finite_subset[OF _ finite_Collect_ta_rule, of _ \<A>])
  then show ?case using pr Fun ta_only_prod_eps[of p q \<A> P] Fun(3, 6)
    by auto
qed (auto intro: ta_only_prod_eps)

lemma ta_der_ta_only_prod_ta_der:
  "q |\<in>| ta_der (ta_only_prod P \<A>) t \<Longrightarrow> q |\<in>| ta_der \<A> t"
  by (meson ta_der_el_mono ta_restrict_subset ta_subset_def)


(* It is sound to restrict to productive states. *)
lemma gta_only_prod_lang:
  "gta_lang Q (ta_only_prod Q \<A>) = gta_lang Q \<A>" (is "gta_lang Q ?\<A> = _")
proof
  show "gta_lang Q ?\<A> \<subseteq> gta_lang Q \<A>"
    using gta_lang_mono[OF ta_der_mono'[OF ta_restrict_subset]]
    by blast
next
  {fix t assume "t \<in> gta_lang Q \<A>"
    from gta_langE[OF this] obtain q where
      reach: "q |\<in>| ta_der \<A> (term_of_gterm t)" "q |\<in>| Q" .
    from ta_der_only_prod[OF reach(1) ta_productive_setI[OF reach(2)]] reach(2)
    have "t \<in> gta_lang Q ?\<A>" by (auto intro: gta_langI)}
  then show "gta_lang Q \<A> \<subseteq> gta_lang Q ?\<A>" by blast
qed

lemma \<L>_only_prod: "\<L> (reg_prod R) = \<L> R"
  using gta_only_prod_lang
  by (auto simp: \<L>_def reg_prod_def)

lemma ta_only_prod_lang:
  "ta_lang Q (ta_only_prod Q \<A>) = ta_lang Q \<A>"
  using gta_only_prod_lang
  by (metis ta_lang_to_gta_lang)

(* the productive states are also productive w.r.t. the new automaton *)
lemma ta_prodictive_ta_only_prod [simp]:
  "ta_productive P (ta_only_prod P \<A>) = ta_productive P \<A>"  (is "?LS = ?RS")
proof -
  have "?LS |\<subseteq>| ?RS" using ta_der_mono'[OF ta_restrict_subset]
    using finite_ta_productive[of \<A> P]
    by (auto simp: ta_productive_def) fastforce
  moreover have "?RS |\<subseteq>| ?LS" using ta_der_only_prod
    by (auto elim!: ta_productiveE)
       (smt (z3) ta_der_only_prod ta_productiveI ta_productive_setI)
  ultimately show ?thesis by blast
qed

lemma ta_only_prod_productive:
  "\<Q> (ta_only_prod P \<A>) |\<subseteq>| ta_productive P (ta_only_prod P \<A>)"
  using ta_restrict_states_Q by force

lemma ta_only_prod_reachable:
  assumes all_reach: "\<Q> \<A> |\<subseteq>| ta_reachable \<A>"
  shows "\<Q> (ta_only_prod P \<A>) |\<subseteq>| ta_reachable (ta_only_prod P \<A>)" (is "?Ls |\<subseteq>| ?Rs")
proof -
  {fix q assume "q |\<in>| ?Ls"
    then obtain t where "ground t" "q |\<in>| ta_der \<A> t" "q |\<in>| ta_productive P \<A>"
      using fsubsetD[OF ta_only_prod_productive[of \<A> P]]
      using fsubsetD[OF fsubset_trans[OF ta_restrict_states all_reach, of "ta_productive P \<A>"]]
      by (auto elim!: ta_reachableE)
    then have "q |\<in>| ?Rs"
      by (intro ta_reachableI[where ?\<A> = "ta_only_prod P \<A>" and ?t = t]) (auto simp: ta_der_only_prod)}
  then show ?thesis by blast
qed

lemma ta_prod_reach_subset:
  "ta_subset (ta_only_prod P (ta_only_reach \<A>)) \<A>"
  by (rule ta_subset_trans, (rule ta_restrict_subset)+)

lemma ta_prod_reach_states:
  "\<Q> (ta_only_prod P (ta_only_reach \<A>)) |\<subseteq>| \<Q> \<A>"
  by (rule ta_subset_states[OF ta_prod_reach_subset])

(* If all states are reachable then there exists a ground context for all productive states *)
lemma ta_productive_aux:
  assumes "\<Q> \<A> |\<subseteq>| ta_reachable \<A>" "q |\<in>| ta_der \<A> (C\<langle>t\<rangle>)"
  shows "\<exists>C'. ground_ctxt C' \<and> q |\<in>| ta_der \<A> (C'\<langle>t\<rangle>)" using assms(2)
proof (induct C arbitrary: q)
  case Hole then show ?case by (intro exI[of _ "\<box>"]) auto
next
  case (More f ts1 C ts2)
  from More(2) obtain qs q' where q': "f qs \<rightarrow> q' |\<in>| rules \<A>" "q' = q \<or> (q', q) |\<in>| (eps \<A>)|\<^sup>+|"
    "qs ! length ts1 |\<in>| ta_der \<A> (C\<langle>t\<rangle>)" "length qs = Suc (length ts1 + length ts2)"
    by simp (metis less_add_Suc1 nth_append_length)
  { fix i assume "i < length qs"
    then have "qs ! i |\<in>| \<Q> \<A>" using q'(1)
      by (auto dest!: rule_statesD(4))
    then have "\<exists>t. ground t \<and> qs ! i |\<in>| ta_der \<A> t" using assms(1)
      by (simp add: ta_reachable_def) force}
  then obtain ts where ts: "i < length qs \<Longrightarrow> ground (ts i) \<and> qs ! i |\<in>| ta_der \<A> (ts i)" for i by metis
  obtain C' where C: "ground_ctxt C'" "qs ! length ts1 |\<in>| ta_der \<A> C'\<langle>t\<rangle>" using More(1)[OF q'(3)] by blast
  define D where "D \<equiv> More f (map ts [0..<length ts1]) C' (map ts [Suc (length ts1)..<Suc (length ts1 + length ts2)])"
  have "ground_ctxt D" unfolding D_def using ts C(1) q'(4) by auto
  moreover have "q |\<in>| ta_der \<A> D\<langle>t\<rangle>" using ts C(2) q' unfolding D_def
    by (auto simp: nth_append_Cons not_le not_less le_less_Suc_eq Suc_le_eq intro!: exI[of _ qs] exI[of _ q'])
  ultimately show ?case by blast
qed

lemma ta_productive_def':
  assumes "\<Q> \<A> |\<subseteq>| ta_reachable \<A>"
  shows "ta_productive Q \<A> = {| q| q q' C. ground_ctxt C \<and> q' |\<in>| ta_der \<A> (C\<langle>Var q\<rangle>) \<and> q' |\<in>| Q |}"
  using ta_productive_aux[OF assms]
  by (auto simp: ta_productive_def intro!: finite_subset[OF _ finite_ta_productive, of _ \<A> Q]) force+

(* turn a finite automaton into a trim one, by removing
   first all unreachable and then all non-productive states *)

lemma trim_gta_lang: "gta_lang Q (trim_ta Q \<A>) = gta_lang Q \<A>"
  unfolding trim_ta_def gta_only_reach_lang gta_only_prod_lang ..

lemma trim_ta_subset: "ta_subset (trim_ta Q \<A>) \<A>"
  unfolding trim_ta_def by (rule ta_prod_reach_subset)

theorem trim_ta: "ta_is_trim Q (trim_ta Q \<A>)" unfolding ta_is_trim_def
  by (metis fin_mono ta_only_prod_reachable ta_only_reach_reachable
      ta_prodictive_ta_only_prod ta_restrict_states_Q trim_ta_def)


lemma reg_is_trim_trim_reg [simp]: "reg_is_trim (trim_reg R)"
  unfolding reg_is_trim_def trim_reg_def
  by (simp add: trim_ta)

lemma trim_reg_reach [simp]:
  "\<Q>\<^sub>r (trim_reg A) |\<subseteq>| ta_reachable (ta (trim_reg A))"
  by (auto simp: trim_reg_def) (meson ta_is_trim_def trim_ta)

lemma trim_reg_prod [simp]:
  "\<Q>\<^sub>r (trim_reg A) |\<subseteq>| ta_productive (fin (trim_reg A)) (ta (trim_reg A))"
  by (auto simp: trim_reg_def) (meson ta_is_trim_def trim_ta)

(* Proposition 7: every tree automaton can be turned into an  equivalent trim one *)
lemmas obtain_trimmed_ta = trim_ta trim_gta_lang ta_subset_det[OF trim_ta_subset]

(* Trim tree automaton signature *)
lemma \<L>_trim_ta_sig:
  assumes "reg_is_trim R" "\<L> R \<subseteq> \<T>\<^sub>G (fset \<F>)"
  shows "ta_sig (ta R) |\<subseteq>| \<F>"
proof -
  {fix r assume r: "r |\<in>| rules (ta R)"
    then obtain f ps p where [simp]: "r = f ps \<rightarrow> p" by (cases r) auto
    from r assms(1) have "fset_of_list ps |\<subseteq>| ta_reachable (ta R)"
      by (auto simp add: rule_statesD(4) reg_is_trim_def ta_is_trim_def)
    from ta_reachableI_rule[OF this, of f p] r
    obtain ts where ts: "length ts = length ps" "\<forall> i < length ps. ground (ts ! i)"
      "\<forall> i < length ps. ps ! i |\<in>| ta_der (ta R) (ts ! i)"
      by auto
    obtain C q where ctxt: "ground_ctxt C" "q |\<in>| ta_der (ta R) (C\<langle>Var p\<rangle>)" "q |\<in>| fin R"
      using assms(1) unfolding reg_is_trim_def
      by (metis \<open>r = f ps \<rightarrow> p\<close> fsubsetI r rule_statesD(2) ta_productiveE ta_productive_aux ta_is_trim_def)
    from ts ctxt r have reach: "q |\<in>| ta_der (ta R) C\<langle>Fun f ts\<rangle>"
      by auto (metis ta_der_Fun ta_der_ctxt)
    have gr: "ground C\<langle>Fun f ts\<rangle>" using ts(1, 2) ctxt(1)
      by (auto simp: in_set_conv_nth)
    then have "C\<langle>Fun f ts\<rangle> \<in> ta_lang (fin R) (ta R)" using ctxt(1, 3) ts(1, 2)
      apply (intro ta_langI[OF _ _ reach, of "fin R" "C\<langle>Fun f ts\<rangle>"])
      apply (auto simp del: adapt_vars_ctxt)
      by (metis gr adapt_vars2 adapt_vars_adapt_vars)
    then have *: "gterm_of_term C\<langle>Fun f ts\<rangle> \<in> \<L> R" using gr
      by (auto simp: \<L>_def)
    then have "funas_gterm (gterm_of_term C\<langle>Fun f ts\<rangle>) \<subseteq> fset \<F>" using assms(2) gr
      by (auto simp: \<T>\<^sub>G_equivalent_def)
    moreover have "(f, length ps) \<in> funas_gterm (gterm_of_term C\<langle>Fun f ts\<rangle>)"
      using ts(1) by (auto simp: funas_gterm_gterm_of_term[OF gr])
    ultimately have "(r_root r, length (r_lhs_states r)) |\<in>| \<F>"
      by auto}
  then show ?thesis
    by (auto simp: ta_sig_def)
qed

text \<open>Map function over TA rules which change states/signature\<close>

lemma map_ta_rule_iff:
  "map_ta_rule f g |`| \<Delta> = {|TA_rule (g h) (map f qs) (f q) | h qs q. TA_rule h qs q |\<in>| \<Delta>|}"
  apply (intro fequalityI fsubsetI)
  apply (auto simp add: rev_image_eqI)
  apply (metis map_ta_rule_cases ta_rule.collapse)
  done

lemma \<L>_trim: "\<L> (trim_reg R) = \<L> R"
  by (auto simp: trim_gta_lang \<L>_def trim_reg_def)


lemma fmap_funs_ta_def':
  "fmap_funs_ta h \<A> = TA {|(h f) qs \<rightarrow> q |f qs q. f qs \<rightarrow> q |\<in>| rules \<A>|} (eps \<A>)"
  unfolding fmap_funs_ta_def map_ta_rule_iff by auto

lemma fmap_states_ta_def':
  "fmap_states_ta h \<A> = TA {|f (map h qs) \<rightarrow> h q |f qs q. f qs \<rightarrow> q |\<in>| rules \<A>|} (map_both h |`| eps \<A>)"
  unfolding fmap_states_ta_def map_ta_rule_iff by auto

lemma fmap_states [simp]:
  "\<Q> (fmap_states_ta h \<A>) = h |`| \<Q> \<A>"
  unfolding fmap_states_ta_def \<Q>_def
  by auto

lemma fmap_states_ta_sig [simp]:
  "ta_sig (fmap_states_ta f \<A>) = ta_sig \<A>"
  by (auto simp: fmap_states_ta_def ta_sig_def ta_rule.map_sel intro: fset.map_cong0)

lemma fmap_states_ta_eps_wit:
  assumes "(h p, q) |\<in>| (map_both h |`| eps \<A>)|\<^sup>+|" "finj_on h (\<Q> \<A>)" "p |\<in>| \<Q> \<A>"
  obtains q' where "q = h q'" "(p, q') |\<in>| (eps \<A>)|\<^sup>+|" "q' |\<in>| \<Q> \<A>"
  using assms(1)[unfolded ftrancl_map_both_fsubset[OF assms(2), of "eps \<A>", simplified]]
  using \<open>finj_on h (\<Q> \<A>)\<close>[unfolded finj_on_def', rule_format, OF \<open>p |\<in>| \<Q> \<A>\<close>]
  by (metis Pair_inject eps_trancl_statesD prod_fun_fimageE)

lemma ta_der_fmap_states_inv_superset:
  assumes "\<Q> \<A> |\<subseteq>| \<B>" "finj_on h \<B>"
    and  "q |\<in>| ta_der (fmap_states_ta h \<A>) (term_of_gterm t)"
  shows "the_finv_into \<B> h q |\<in>| ta_der \<A> (term_of_gterm t)" using assms(3)
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  from assms(1, 2) have inj: "finj_on h (\<Q> \<A>)" using fsubset_finj_on by blast
  have "x |\<in>| \<Q> \<A> \<Longrightarrow> the_finv_into (\<Q> \<A>) h (h x) = the_finv_into \<B> h (h x)" for x
    using assms(1, 2) by (metis fsubsetD inj the_finv_into_f_f) 
  then show ?case using GFun the_finv_into_f_f[OF inj] assms(1)
    by (auto simp: fmap_states_ta_def' finj_on_def' rule_statesD eps_statesD
      elim!: fmap_states_ta_eps_wit[OF _ inj]
      intro!: exI[of _ "the_finv_into \<B> h p"])
qed

lemma ta_der_fmap_states_inv:
  assumes "finj_on h (\<Q> \<A>)" "q |\<in>| ta_der (fmap_states_ta h \<A>) (term_of_gterm t)"
  shows "the_finv_into (\<Q> \<A>) h q |\<in>| ta_der \<A> (term_of_gterm t)"
  by (simp add: ta_der_fmap_states_inv_superset assms)

lemma ta_der_to_fmap_states_der:
  assumes "q |\<in>| ta_der \<A> (term_of_gterm t)"
  shows "h q |\<in>| ta_der (fmap_states_ta h \<A>) (term_of_gterm t)" using assms
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  then show ?case
    using ftrancl_map_prod_mono[of h "eps \<A>"]
    by (auto simp: fmap_states_ta_def' intro!: exI[of _ "h p"] exI[of _ "map h ps"])
qed

lemma ta_der_fmap_states_conv:
  assumes "finj_on h (\<Q> \<A>)"
  shows "ta_der (fmap_states_ta h \<A>) (term_of_gterm t) =  h |`| ta_der \<A> (term_of_gterm t)"
  using ta_der_to_fmap_states_der[of _ \<A> t] ta_der_fmap_states_inv[OF assms]
  using f_the_finv_into_f[OF assms] finj_on_the_finv_into[OF assms]
  using gterm_ta_der_states
  by (auto intro!: rev_fimage_eqI) fastforce

lemma fmap_states_ta_det:
  assumes "finj_on f (\<Q> \<A>)"
  shows "ta_det (fmap_states_ta f \<A>) = ta_det \<A>" (is "?Ls = ?Rs")
proof
  {fix g ps p q assume ass: "?Ls" "TA_rule g ps p |\<in>| rules \<A>" "TA_rule g ps q |\<in>| rules \<A>"
    then have "TA_rule g (map f ps) (f p) |\<in>| rules (fmap_states_ta f \<A>)"
       "TA_rule g (map f ps) (f q) |\<in>| rules (fmap_states_ta f \<A>)"
      by (force simp: fmap_states_ta_def)+
    then have "p = q" using ass finj_on_eq_iff[OF assms]
      by (auto simp: ta_det_def) (meson rule_statesD(2))} 
  then show "?Ls \<Longrightarrow> ?Rs"
    by (auto simp: ta_det_def fmap_states_ta_def')
next
  {fix g ps qs p q assume ass: "?Rs" "TA_rule g ps p |\<in>| rules \<A>" "TA_rule g qs q |\<in>| rules \<A>"
    then have "map f ps = map f qs \<Longrightarrow> ps = qs" using finj_on_eq_iff[OF assms]
      by (auto simp: map_eq_nth_conv in_fset_conv_nth dest!: rule_statesD(4) intro!: nth_equalityI)}
  then show "?Rs \<Longrightarrow> ?Ls" using finj_on_eq_iff[OF assms]
    by (auto simp: ta_det_def fmap_states_ta_def') blast
qed

lemma fmap_states_ta_lang:
  "finj_on f (\<Q> \<A>) \<Longrightarrow> Q |\<subseteq>| \<Q> \<A> \<Longrightarrow> gta_lang (f |`| Q) (fmap_states_ta f \<A>) = gta_lang Q \<A>"
  using ta_der_fmap_states_conv[of f \<A>]
  by (auto simp: finj_on_def' finj_on_eq_iff fsubsetD elim!: gta_langE intro!: gta_langI)

lemma fmap_states_ta_lang2:
  "finj_on f (\<Q> \<A> |\<union>| Q) \<Longrightarrow> gta_lang (f |`| Q) (fmap_states_ta f \<A>) = gta_lang Q \<A>"
  using ta_der_fmap_states_conv[OF fsubset_finj_on[of f "\<Q> \<A> |\<union>| Q" "\<Q> \<A>"]] 
  by (auto simp: finj_on_def' elim!: gta_langE intro!: gta_langI) fastforce


definition funs_ta :: "('q, 'f) ta \<Rightarrow> 'f fset" where
  "funs_ta \<A> = {|f |f qs q. TA_rule f qs q |\<in>| rules \<A>|}"

lemma funs_ta[code]:
  "funs_ta \<A> = (\<lambda> r. case r of TA_rule f ps p \<Rightarrow> f) |`| (rules \<A>)" (is "?Ls = ?Rs")
  by (force simp: funs_ta_def rev_fimage_eqI simp flip: fset.set_map
     split!: ta_rule.splits intro!: finite_subset[of "{f. \<exists>qs q. TA_rule f qs q |\<in>| rules \<A>}" "fset ?Rs"])

lemma finite_funs_ta [simp]:
  "finite {f. \<exists>qs q. TA_rule f qs q |\<in>| rules \<A>}"
  by (intro finite_subset[of "{f. \<exists>qs q. TA_rule f qs q |\<in>| rules \<A>}" "fset (funs_ta \<A>)"])
     (auto simp: funs_ta rev_fimage_eqI simp flip: fset.set_map split!: ta_rule.splits)

lemma funs_taE [elim]:
  assumes "f |\<in>| funs_ta \<A>"
  obtains ps p where "TA_rule f ps p |\<in>| rules \<A>" using assms
  by (auto simp: funs_ta_def)

lemma funs_taI [intro]:
  "TA_rule f ps p |\<in>| rules \<A> \<Longrightarrow> f |\<in>| funs_ta \<A>"
  by (auto simp: funs_ta_def)

lemma fmap_funs_ta_cong:
  "(\<And>x. x |\<in>| funs_ta \<A> \<Longrightarrow> h x = k x) \<Longrightarrow> \<A> = \<B> \<Longrightarrow> fmap_funs_ta h \<A> = fmap_funs_ta k \<B>"
  by (force simp: fmap_funs_ta_def')

lemma [simp]: "{|TA_rule f qs q |f qs q. TA_rule f qs q |\<in>| X|} = X"
  by (intro fset_eqI; case_tac x) auto

lemma fmap_funs_ta_id [simp]:
  "fmap_funs_ta id \<A> = \<A>" by (simp add: fmap_funs_ta_def')

lemma fmap_states_ta_id [simp]:
  "fmap_states_ta id \<A> = \<A>"
  by (auto simp: fmap_states_ta_def map_ta_rule_iff prod.map_id0)

lemmas fmap_funs_ta_id' [simp] = fmap_funs_ta_id[unfolded id_def]

lemma fmap_funs_ta_comp:
  "fmap_funs_ta h (fmap_funs_ta k A) = fmap_funs_ta (h \<circ> k) A"
proof -
  have "r |\<in>| rules A \<Longrightarrow> map_ta_rule id h (map_ta_rule id k r) = map_ta_rule id (\<lambda>x. h (k x)) r" for r
    by (cases r) (auto)
  then show ?thesis
    by (force simp: fmap_funs_ta_def fimage_iff cong: fmap_funs_ta_cong)
qed

lemma fmap_funs_reg_comp:
  "fmap_funs_reg h (fmap_funs_reg k A) = fmap_funs_reg (h \<circ> k) A"
  using fmap_funs_ta_comp unfolding fmap_funs_reg_def
  by auto

lemma fmap_states_ta_comp:
  "fmap_states_ta h (fmap_states_ta k A) = fmap_states_ta (h \<circ> k) A"
  by (auto simp: fmap_states_ta_def ta_rule.map_comp comp_def id_def prod.map_comp)

lemma funs_ta_fmap_funs_ta [simp]:
  "funs_ta (fmap_funs_ta f A) = f |`| funs_ta A"
  by (auto simp: funs_ta fmap_funs_ta_def' comp_def fimage_iff
    split!: ta_rule.splits) force+

lemma ta_der_funs_ta:
  "q |\<in>| ta_der A t \<Longrightarrow> ffuns_term t |\<subseteq>| funs_ta A"
proof (induct t arbitrary: q)
  case (Fun f ts)
  then have "f |\<in>| funs_ta A" by (auto simp: funs_ta_def)
  then show ?case using Fun(1)[OF nth_mem, THEN fsubsetD] Fun(2)
    by (auto simp: in_fset_conv_nth) blast+
qed auto

lemma ta_der_fmap_funs_ta:
  "q |\<in>| ta_der A t \<Longrightarrow> q |\<in>| ta_der (fmap_funs_ta f A) (map_funs_term f t)"
  by (induct t arbitrary: q) (auto 0 4 simp: fmap_funs_ta_def')

lemma ta_der_fmap_states_ta:
  assumes "q |\<in>| ta_der A t"
  shows "h q |\<in>| ta_der (fmap_states_ta h A) (map_vars_term h t)"
proof -
  have [intro]: "(q, q') |\<in>| (eps A)|\<^sup>+| \<Longrightarrow> (h q, h q') |\<in>| (eps (fmap_states_ta h A))|\<^sup>+|" for q q'
    by (force intro!: ftrancl_map[of "eps A"] simp: fmap_states_ta_def)
  show ?thesis using assms
  proof (induct rule: ta_der_induct)
    case (Fun f ts ps p q)
    have "f (map h ps) \<rightarrow> h p |\<in>| rules (fmap_states_ta h A)"
      using Fun(1) by (force simp: fmap_states_ta_def')
    then show ?case using Fun by (auto 0 4)
  qed auto
qed

lemma ta_der_fmap_states_ta_mono:
  shows "f |`| ta_der A (term_of_gterm s) |\<subseteq>| ta_der (fmap_states_ta f A) (term_of_gterm s)"
  using ta_der_fmap_states_ta[of _ A "term_of_gterm s" f]
  by (simp add: fimage_fsubsetI ta_der_to_fmap_states_der)

lemma ta_der_fmap_states_ta_mono2:
  assumes "finj_on f (\<Q> A)"
  shows "ta_der (fmap_states_ta f A) (term_of_gterm s) |\<subseteq>| f |`| ta_der A (term_of_gterm s)"
  using ta_der_fmap_states_conv[OF assms] by auto

lemma fmap_funs_ta_der':
  "q |\<in>| ta_der (fmap_funs_ta h A) t \<Longrightarrow> \<exists>t'. q |\<in>| ta_der A t' \<and> map_funs_term h t' = t"
proof (induct rule: ta_der_induct)
  case (Var q v)
  then show ?case by (auto simp: fmap_funs_ta_def intro!: exI[of _ "Var v"])
next
  case (Fun f ts ps p q)
  obtain f' ts' where root: "f = h f'" "f' ps \<rightarrow> p |\<in>| rules A" and
    "\<And>i. i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der A (ts' i) \<and> map_funs_term h (ts' i) = ts ! i"
    using Fun(1, 5) unfolding fmap_funs_ta_def'
    by auto metis
  note [simp] = conjunct1[OF this(3)] conjunct2[OF this(3), unfolded id_def]
  have [simp]: "p = q \<Longrightarrow> f' ps \<rightarrow> q |\<in>| rules A" using root(2) by auto
  show ?case using Fun(3)
    by (auto simp: comp_def Fun root fmap_funs_ta_def'
      intro!: exI[of _ "Fun f' (map ts' [0..<length ts])"] exI[of _ ps] exI[of _ p] nth_equalityI)
qed

lemma fmap_funs_gta_lang:
  "gta_lang Q (fmap_funs_ta h \<A>) = map_gterm h ` gta_lang Q \<A>" (is "?Ls = ?Rs")
proof -
  {fix s assume "s \<in> ?Ls" then obtain q where
    lang: "q |\<in>| Q" "q |\<in>| ta_der (fmap_funs_ta h \<A>) (term_of_gterm s)"
      by auto
    from fmap_funs_ta_der'[OF this(2)] obtain t where
    t: "q |\<in>| ta_der \<A> t" "map_funs_term h t = term_of_gterm s" "ground t"
      by (metis ground_map_term ground_term_of_gterm)
    then have "s \<in> ?Rs" using map_gterm_of_term[OF t(3), of h id] lang
      by (auto simp: gta_lang_def gta_der_def image_iff)
         (metis fempty_iff finterI ground_term_to_gtermD map_term_of_gterm term_of_gterm_inv)}
  moreover have "?Rs \<subseteq> ?Ls" using ta_der_fmap_funs_ta[of _ \<A> _ h]
    by (auto elim!: gta_langE intro!: gta_langI) fastforce
  ultimately show ?thesis by blast
qed

lemma fmap_funs_\<L>:
  "\<L> (fmap_funs_reg h R) =  map_gterm h ` \<L> R"
  using fmap_funs_gta_lang[of "fin R" h]
  by (auto simp: fmap_funs_reg_def \<L>_def)

lemma ta_states_fmap_funs_ta [simp]: "\<Q> (fmap_funs_ta f A) = \<Q> A"
  by (auto simp: fmap_funs_ta_def \<Q>_def)
 
lemma ta_reachable_fmap_funs_ta [simp]:
  "ta_reachable (fmap_funs_ta f A) = ta_reachable A" unfolding ta_reachable_def
  by (metis (mono_tags, lifting) fmap_funs_ta_der' ta_der_fmap_funs_ta ground_map_term)


lemma fin_in_states:
  "fin (reg_Restr_Q\<^sub>f R) |\<subseteq>| \<Q>\<^sub>r (reg_Restr_Q\<^sub>f R)"
  by (auto simp: reg_Restr_Q\<^sub>f_def)

lemma fmap_states_reg_Restr_Q\<^sub>f_fin:
  "finj_on f (\<Q> \<A>) \<Longrightarrow> fin (fmap_states_reg f (reg_Restr_Q\<^sub>f R)) |\<subseteq>| \<Q>\<^sub>r (fmap_states_reg f (reg_Restr_Q\<^sub>f R))"
  by (auto simp: fmap_states_reg_def reg_Restr_Q\<^sub>f_def)

lemma \<L>_fmap_states_reg_Inl_Inr [simp]:
  "\<L> (fmap_states_reg Inl R) = \<L> R"
  "\<L> (fmap_states_reg Inr R) = \<L> R"
  unfolding \<L>_def fmap_states_reg_def
  by (auto simp: finj_Inl_Inr intro!: fmap_states_ta_lang2)

lemma finite_Collect_prod_ta_rules:
  "finite {f qs \<rightarrow> (a, b) |f qs a b. f map fst qs \<rightarrow> a |\<in>| rules \<A> \<and> f map snd qs \<rightarrow> b |\<in>| rules \<BB>}" (is "finite ?set")
proof -
  have "?set \<subseteq> (\<lambda> (ra, rb). case ra of f ps \<rightarrow> p \<Rightarrow> case rb of g qs \<rightarrow> q \<Rightarrow> f (zip ps qs) \<rightarrow> (p, q)) ` (srules \<A> \<times> srules \<BB>)"
    by (auto simp: srules_def image_iff split!: ta_rule.splits)
       (metis ta_rule.inject zip_map_fst_snd)
  from finite_imageI[of "srules \<A> \<times> srules \<BB>", THEN finite_subset[OF this]]
  show ?thesis by (auto simp: srules_def)
qed

\<comment> \<open>The product automaton of the automata A and B is constructed
 by applying the rules on pairs of states\<close>

lemmas prod_eps_def = prod_epsLp_def prod_epsRp_def

lemma finite_prod_epsLp:
  "finite (Collect (prod_epsLp \<A> \<B>))"
  by (intro finite_subset[of "Collect (prod_epsLp \<A> \<B>)" "fset ((\<Q> \<A> |\<times>| \<Q> \<B>) |\<times>| \<Q> \<A> |\<times>| \<Q> \<B>)"])
     (auto simp: prod_epsLp_def dest: eps_statesD)

lemma finite_prod_epsRp:
  "finite (Collect (prod_epsRp \<A> \<B>))"
  by (intro finite_subset[of "Collect (prod_epsRp \<A> \<B>)" "fset ((\<Q> \<A> |\<times>| \<Q> \<B>) |\<times>| \<Q> \<A> |\<times>| \<Q> \<B>)"])
     (auto simp: prod_epsRp_def dest: eps_statesD)
lemmas finite_prod_eps [simp] = finite_prod_epsLp[unfolded prod_epsLp_def] finite_prod_epsRp[unfolded prod_epsRp_def]

lemma [simp]: "f qs \<rightarrow> q |\<in>| rules (prod_ta \<A> \<B>) \<longleftrightarrow> f qs \<rightarrow> q |\<in>| prod_ta_rules \<A> \<B>"
  "r |\<in>| rules (prod_ta \<A> \<B>) \<longleftrightarrow> r |\<in>| prod_ta_rules \<A> \<B>"
  by (auto simp: prod_ta_def)

lemma prod_ta_states:
  "\<Q> (prod_ta \<A> \<B>) |\<subseteq>| \<Q> \<A> |\<times>| \<Q> \<B>"
proof -
  {fix q assume "q |\<in>| rule_states (rules (prod_ta \<A> \<B>))"
    then obtain f ps p where "f ps \<rightarrow> p |\<in>| rules (prod_ta \<A> \<B>)" and "q |\<in>| fset_of_list ps \<or> p = q"
      by (metis rule_statesE)
    then have "fst q |\<in>| \<Q> \<A> \<and> snd q |\<in>| \<Q> \<B>"
      using rule_statesD(2, 4)[of f "map fst ps" "fst p" \<A>]
      using rule_statesD(2, 4)[of f "map snd ps" "snd p" \<B>]
      by auto}
  moreover
  {fix q assume "q |\<in>| eps_states (eps (prod_ta \<A> \<B>))" then have "fst q |\<in>| \<Q> \<A> \<and> snd q |\<in>| \<Q> \<B>"
      by (auto simp: eps_states_def prod_ta_def prod_eps_def dest: eps_statesD)}
  ultimately show ?thesis
    by (auto simp: \<Q>_def) blast+
qed

lemma prod_ta_det:
  assumes "ta_det \<A>" and "ta_det \<B>"
  shows "ta_det (prod_ta \<A> \<B>)"
  using assms unfolding ta_det_def prod_ta_def prod_eps_def
  by auto

lemma prod_ta_sig:
  "ta_sig (prod_ta \<A> \<B>) |\<subseteq>| ta_sig \<A> |\<union>| ta_sig \<B>"
proof (rule fsubsetI)
  fix x
  assume "x |\<in>| ta_sig (prod_ta \<A> \<B>)"
  hence "x |\<in>| ta_sig \<A> \<or> x |\<in>| ta_sig \<B>"
    unfolding ta_sig_def prod_ta_def
    using image_iff by fastforce
  thus "x |\<in>| ta_sig (prod_ta \<A> \<B>) \<Longrightarrow> x |\<in>| ta_sig \<A> |\<union>| ta_sig \<B>"
    by simp
qed

lemma from_prod_eps:
  "(p, q) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+| \<Longrightarrow> (snd p, snd q) |\<notin>| (eps \<B>)|\<^sup>+| \<Longrightarrow> snd p = snd q \<and> (fst p, fst q) |\<in>| (eps \<A>)|\<^sup>+|"
  "(p, q) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+| \<Longrightarrow> (fst p, fst q) |\<notin>| (eps \<A>)|\<^sup>+| \<Longrightarrow> fst p = fst q \<and> (snd p, snd q) |\<in>| (eps \<B>)|\<^sup>+|"
  apply (induct rule: ftrancl_induct) 
  apply (auto simp: prod_ta_def prod_eps_def intro: ftrancl_into_trancl )
  apply (simp add: fr_into_trancl not_ftrancl_into)+
  done

lemma to_prod_eps\<A>:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> r |\<in>| \<Q> \<B> \<Longrightarrow> ((p, r), (q, r)) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|"
  by (induct rule: ftrancl_induct)
     (auto simp: prod_ta_def prod_eps_def intro: fr_into_trancl ftrancl_into_trancl)

lemma to_prod_eps\<B>:
  "(p, q) |\<in>| (eps \<B>)|\<^sup>+| \<Longrightarrow> r |\<in>| \<Q> \<A> \<Longrightarrow> ((r, p), (r, q)) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|"
  by (induct rule: ftrancl_induct)
     (auto simp: prod_ta_def prod_eps_def intro: fr_into_trancl ftrancl_into_trancl)

lemma to_prod_eps:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> (p', q') |\<in>| (eps \<B>)|\<^sup>+| \<Longrightarrow> ((p, p'), (q, q')) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|"
proof (induct rule: ftrancl_induct)
  case (Base a b)
  show ?case using Base(2, 1)
  proof (induct rule: ftrancl_induct)
    case (Base c d)
    then have "((a, c), b, c) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|" using finite_prod_eps
      by (auto simp: prod_ta_def prod_eps_def dest: eps_statesD intro!: fr_into_trancl ftrancl_into_trancl)
    moreover have "((b, c), b, d) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|" using finite_prod_eps Base
      by (auto simp: prod_ta_def prod_eps_def dest: eps_statesD intro!: fr_into_trancl ftrancl_into_trancl)
    ultimately show ?case
      by (auto intro: ftrancl_trans)
  next
    case (Step p q r)
    then have "((b, q), b, r) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|" using finite_prod_eps
      by (auto simp: prod_ta_def prod_eps_def dest: eps_statesD intro!: fr_into_trancl)
    then show ?case using Step
      by (auto intro: ftrancl_trans)
  qed
next
  case (Step a b c)
  from Step have "q' |\<in>| \<Q> \<B>"
    by (auto dest: eps_trancl_statesD)
  then have "((b, q'), (c,q')) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|" 
    using Step(3) finite_prod_eps
    by (auto simp: prod_ta_def prod_eps_def intro!: fr_into_trancl)
  then show ?case using ftrancl_trans Step
    by auto
qed

lemma prod_ta_der_to_\<A>_\<B>_der1:
  assumes "q |\<in>| ta_der (prod_ta \<A> \<B>) (term_of_gterm t)"
  shows "fst q |\<in>| ta_der \<A> (term_of_gterm t)" using assms
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  then show ?case
    by (auto dest: from_prod_eps intro!: exI[of _ "map fst ps"] exI[of _ "fst p"])
qed

lemma prod_ta_der_to_\<A>_\<B>_der2:
  assumes "q |\<in>| ta_der (prod_ta \<A> \<B>) (term_of_gterm t)"
  shows  "snd q |\<in>| ta_der \<B> (term_of_gterm t)" using assms
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  then show ?case
    by (auto dest: from_prod_eps intro!: exI[of _ "map snd ps"] exI[of _ "snd p"])
qed

lemma \<A>_\<B>_der_to_prod_ta:
  assumes "fst q |\<in>| ta_der \<A> (term_of_gterm t)" "snd q |\<in>| ta_der \<B> (term_of_gterm t)"
  shows "q |\<in>| ta_der (prod_ta \<A> \<B>) (term_of_gterm t)" using assms
proof (induct t arbitrary: q)
  case (GFun f ts)
  from GFun(2, 3) obtain ps qs p q' where
    rules: "f ps \<rightarrow> p |\<in>| rules \<A>" "f qs \<rightarrow> q' |\<in>| rules \<B>" "length ps = length ts" "length ps = length qs" and
    eps: "p = fst q \<or> (p, fst q) |\<in>| (eps \<A>)|\<^sup>+|" "q' = snd q \<or> (q', snd q) |\<in>| (eps \<B>)|\<^sup>+|" and
    steps: "\<forall> i < length qs. ps ! i |\<in>| ta_der \<A> (term_of_gterm (ts ! i))"
      "\<forall> i < length qs. qs ! i |\<in>| ta_der \<B> (term_of_gterm (ts ! i))"
    by auto
  from rules have st: "p |\<in>| \<Q> \<A>" "q' |\<in>| \<Q> \<B>" by (auto dest: rule_statesD)
  have "(p, snd q) = q \<or> ((p, q'), q) |\<in>| (eps (prod_ta \<A> \<B>))|\<^sup>+|" using eps st
    using to_prod_eps\<B>[of q' "snd q" \<B> "fst q" \<A>]
    using to_prod_eps\<A>[of p "fst q" \<A> "snd q" \<B>]
    using to_prod_eps[of p "fst q" \<A> q' "snd q" \<B>]
    by (cases "p = fst q"; cases "q' = snd q") (auto simp: prod_ta_def)
  then show ?case using rules eps steps GFun(1) st
    by (cases "(p, snd q) = q")
       (auto simp: finite_Collect_prod_ta_rules dest: to_prod_eps\<B> intro!: exI[of _ p] exI[of _ q'] exI[of _ "zip ps qs"])
qed

lemma prod_ta_der:
  "q |\<in>| ta_der (prod_ta \<A> \<B>) (term_of_gterm t) \<longleftrightarrow>
     fst q |\<in>| ta_der \<A> (term_of_gterm t) \<and> snd q |\<in>| ta_der \<B> (term_of_gterm t)"
  using prod_ta_der_to_\<A>_\<B>_der1 prod_ta_der_to_\<A>_\<B>_der2 \<A>_\<B>_der_to_prod_ta
  by blast

lemma intersect_ta_gta_lang:
 "gta_lang (Q\<^sub>\<A> |\<times>| Q\<^sub>\<B>) (prod_ta \<A> \<B>) = gta_lang Q\<^sub>\<A> \<A> \<inter> gta_lang Q\<^sub>\<B> \<B>"
  by (auto simp: prod_ta_der elim!: gta_langE intro: gta_langI)


lemma \<L>_intersect: "\<L> (reg_intersect R L) = \<L> R \<inter> \<L> L"
  by (auto simp: intersect_ta_gta_lang \<L>_def reg_intersect_def)

lemma intersect_ta_ta_lang:
 "ta_lang (Q\<^sub>\<A> |\<times>| Q\<^sub>\<B>) (prod_ta \<A> \<B>) = ta_lang Q\<^sub>\<A> \<A> \<inter> ta_lang Q\<^sub>\<B> \<B>"
  using intersect_ta_gta_lang[of Q\<^sub>\<A> Q\<^sub>\<B> \<A> \<B>]
  by auto (metis IntI imageI term_of_gterm_inv)

\<comment>  \<open>Union of tree automata\<close>

lemma ta_union_ta_subset:
  "ta_subset \<A> (ta_union \<A> \<B>)" "ta_subset \<B> (ta_union \<A> \<B>)"
  unfolding ta_subset_def ta_union_def
  by auto

lemma ta_union_states [simp]:
  "\<Q> (ta_union \<A> \<B>) = \<Q> \<A> |\<union>| \<Q> \<B>"
  by (auto simp: ta_union_def \<Q>_def)

lemma ta_union_sig [simp]:
  "ta_sig (ta_union \<A> \<B>) = ta_sig \<A> |\<union>| ta_sig \<B>"
  by (auto simp: ta_union_def ta_sig_def)

lemma ta_union_eps_disj_states:
  assumes "\<Q> \<A> |\<inter>| \<Q> \<B> = {||}" and "(p, q) |\<in>| (eps (ta_union \<A> \<B>))|\<^sup>+|"
  shows "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<or> (p, q) |\<in>| (eps \<B>)|\<^sup>+|" using assms(2, 1)
  by (induct rule: ftrancl_induct)
     (auto simp: ta_union_def ftrancl_into_trancl dest: eps_statesD eps_trancl_statesD)

lemma eps_ta_union_eps [simp]:
  "(p, q) |\<in>| (eps \<A>)|\<^sup>+| \<Longrightarrow> (p, q) |\<in>| (eps (ta_union \<A> \<B>))|\<^sup>+|"
  "(p, q) |\<in>| (eps \<B>)|\<^sup>+| \<Longrightarrow> (p, q) |\<in>| (eps (ta_union \<A> \<B>))|\<^sup>+|"
  by (auto simp add: in_ftrancl_UnI ta_union_def)


lemma disj_states_eps [simp]:
  "\<Q> \<A> |\<inter>| \<Q> \<B> = {||} \<Longrightarrow> f ps \<rightarrow> p |\<in>| rules \<A> \<Longrightarrow> (p, q) |\<in>| (eps \<B>)|\<^sup>+| \<longleftrightarrow> False"
  "\<Q> \<A> |\<inter>| \<Q> \<B> = {||} \<Longrightarrow> f ps \<rightarrow> p |\<in>| rules \<B> \<Longrightarrow> (p, q) |\<in>| (eps \<A>)|\<^sup>+| \<longleftrightarrow>  False"
  by (auto simp: rtrancl_eq_or_trancl dest: rule_statesD eps_trancl_statesD)

lemma ta_union_der_disj_states:
  assumes "\<Q> \<A> |\<inter>| \<Q> \<B> = {||}" and "q |\<in>| ta_der (ta_union \<A> \<B>) t"
  shows "q |\<in>| ta_der \<A> t \<or> q |\<in>| ta_der \<B> t" using assms(2)
proof (induct rule: ta_der_induct)
  case (Var q v)
  then show ?case using ta_union_eps_disj_states[OF assms(1)]
    by auto
next
  case (Fun f ts ps p q)
  have dist: "fset_of_list ps |\<subseteq>| \<Q> \<A> \<Longrightarrow> i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der \<A> (ts ! i)"
    "fset_of_list ps |\<subseteq>| \<Q> \<B> \<Longrightarrow> i < length ts \<Longrightarrow> ps ! i |\<in>| ta_der \<B> (ts ! i)" for i
    using Fun(2) Fun(5)[of i] assms(1)
    by (auto dest!: ta_der_not_stateD fsubsetD)
  from Fun(1) consider (a) "fset_of_list ps |\<subseteq>| \<Q> \<A>" | (b) "fset_of_list ps |\<subseteq>| \<Q> \<B>"
    by (auto simp: ta_union_def dest: rule_statesD)
  then show ?case using dist Fun(1, 2) assms(1) ta_union_eps_disj_states[OF assms(1), of p q] Fun(3)
    by (cases) (auto simp: fsubsetI rule_statesD ta_union_def intro!: exI[of _ p] exI[of _ ps])   
qed

lemma ta_union_der_disj_states':
  assumes "\<Q> \<A> |\<inter>| \<Q> \<B> = {||}"
  shows "ta_der (ta_union \<A> \<B>) t = ta_der \<A> t |\<union>| ta_der \<B> t"
  using ta_union_der_disj_states[OF assms] ta_der_mono' ta_union_ta_subset
  by (auto, fastforce) blast

lemma ta_union_gta_lang:
  assumes "\<Q> \<A> |\<inter>| \<Q> \<B> = {||}" and "Q\<^sub>\<A> |\<subseteq>| \<Q> \<A>" and "Q\<^sub>\<B> |\<subseteq>| \<Q> \<B>"
  shows"gta_lang (Q\<^sub>\<A> |\<union>| Q\<^sub>\<B>) (ta_union \<A> \<B>) = gta_lang Q\<^sub>\<A> \<A> \<union> gta_lang Q\<^sub>\<B> \<B>" (is "?Ls = ?Rs")
proof -
  {fix s assume "s \<in> ?Ls" then obtain q
      where w: "q |\<in>| Q\<^sub>\<A> |\<union>| Q\<^sub>\<B>" "q |\<in>| ta_der (ta_union \<A> \<B>) (term_of_gterm s)"
      by (auto elim: gta_langE)
    from ta_union_der_disj_states[OF assms(1) w(2)] consider
      (a)  "q |\<in>| ta_der \<A> (term_of_gterm s)" | "q |\<in>| ta_der \<B> (term_of_gterm s)" by blast
    then have "s \<in> ?Rs" using w(1) assms
      by (cases, auto simp: gta_langI)
         (metis fempty_iff finterI funion_iff gterm_ta_der_states sup.orderE)}
  moreover have "?Rs \<subseteq> ?Ls" using ta_union_der_disj_states'[OF assms(1)]
    by (auto elim!: gta_langE intro!: gta_langI)
  ultimately show ?thesis by blast
qed


lemma \<L>_union: "\<L> (reg_union R L) = \<L> R \<union> \<L> L"
proof -
  let ?inl = "Inl :: 'b \<Rightarrow> 'b + 'c" let ?inr = "Inr :: 'c \<Rightarrow> 'b + 'c"
  let ?fr = "?inl |`| (fin R |\<inter>| \<Q>\<^sub>r R)" let ?fl = "?inr |`| (fin L |\<inter>| \<Q>\<^sub>r L)"
  have [simp]:"gta_lang (?fr |\<union>| ?fl) (ta_union (fmap_states_ta ?inl (ta R)) (fmap_states_ta ?inr (ta L))) =
   gta_lang ?fr (fmap_states_ta ?inl (ta R)) \<union> gta_lang ?fl (fmap_states_ta ?inr (ta L))"
    by (intro ta_union_gta_lang) (auto simp: fimage_iff)
  have [simp]: "gta_lang ?fr (fmap_states_ta ?inl (ta R)) = gta_lang (fin R |\<inter>| \<Q>\<^sub>r R) (ta R)"
    by (intro fmap_states_ta_lang) (auto simp: finj_Inl_Inr)
  have [simp]: "gta_lang ?fl (fmap_states_ta ?inr (ta L)) = gta_lang (fin L |\<inter>| \<Q>\<^sub>r L) (ta L)"
    by (intro fmap_states_ta_lang) (auto simp: finj_Inl_Inr)
  show ?thesis
    using gta_lang_Rest_states_conv
    by (auto simp: \<L>_def reg_union_def ta_union_gta_lang) fastforce
qed

lemma reg_union_states:
  "\<Q>\<^sub>r (reg_union A B) = (Inl |`| \<Q>\<^sub>r A) |\<union>| (Inr |`| \<Q>\<^sub>r B)"
  by (auto simp: reg_union_def)

\<comment> \<open>Deciding emptiness\<close>

lemma ta_empty [simp]:
  "ta_empty Q \<A> = (gta_lang Q \<A> = {})"
  by (auto simp: ta_empty_def elim!: gta_langE ta_reachable_gtermE
    intro: ta_reachable_gtermI gta_langI)


lemma reg_empty [simp]:
  "reg_empty R = (\<L> R = {})"
  by (simp add: \<L>_def reg_empty_def)

text \<open>Epsilon free automaton\<close>

lemma finite_eps_free_rulep [simp]:
  "finite (Collect (eps_free_rulep \<A>))"
proof -
  let ?par = "(\<lambda> r. case r of f qs \<rightarrow> q \<Rightarrow> (f, qs)) |`| (rules \<A>)"
  let ?st = "(\<lambda> (r, q). case r of (f, qs) \<Rightarrow> TA_rule f qs q) |`| (?par |\<times>| \<Q> \<A>)"
  show ?thesis using rule_statesD eps_trancl_statesD
    by (intro finite_subset[of "Collect (eps_free_rulep \<A>)" "fset ?st"])
       (auto simp: eps_free_rulep_def fimage_iff
             simp flip: fset.set_map
             split!: ta_rule.splits, fastforce+)
qed

lemmas finite_eps_free_rule [simp] = finite_eps_free_rulep[unfolded eps_free_rulep_def]

lemma ta_res_eps_free:
  "ta_der (eps_free \<A>) (term_of_gterm t) = ta_der \<A> (term_of_gterm t)" (is "?Ls = ?Rs")
proof -
  {fix q assume "q |\<in>| ?Ls" then have "q |\<in>| ?Rs"
      by (induct rule: ta_der_gterm_induct)
         (auto simp: eps_free_def eps_free_rulep_def)}
  moreover
  {fix q assume "q |\<in>| ?Rs" then have "q |\<in>| ?Ls"
    proof (induct rule: ta_der_gterm_induct)
      case (GFun f ts ps p q)
      then show ?case
        by (auto simp: eps_free_def eps_free_rulep_def intro!: exI[of _ ps])
    qed}
  ultimately show ?thesis by blast
qed

lemma ta_lang_eps_free [simp]:
  "gta_lang Q (eps_free \<A>) = gta_lang Q \<A>"
  by (auto simp add: ta_res_eps_free elim!: gta_langE intro: gta_langI)

lemma \<L>_eps_free: "\<L> (eps_free_reg R) = \<L> R"
  by (auto simp: \<L>_def eps_free_reg_def)

text \<open>Sufficient criterion for containment\<close>
  (* sufficient criterion to check whether automaton accepts at least T_g(F) where F is a subset of
   the signature *) 

definition ta_contains_aux :: "('f \<times> nat) set \<Rightarrow> 'q fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q fset \<Rightarrow> bool" where
  "ta_contains_aux \<F> Q\<^sub>1 \<A> Q\<^sub>2 \<equiv> (\<forall> f qs. (f, length qs) \<in> \<F> \<and> fset_of_list qs |\<subseteq>| Q\<^sub>1 \<longrightarrow>
     (\<exists> q q'. TA_rule f qs q |\<in>| rules \<A> \<and> q' |\<in>| Q\<^sub>2 \<and> (q = q' \<or> (q, q') |\<in>| (eps \<A>)|\<^sup>+|)))"

lemma ta_contains_aux_state_set:
  assumes "ta_contains_aux \<F> Q \<A> Q" "t \<in> \<T>\<^sub>G \<F>"
  shows "\<exists> q. q |\<in>| Q \<and> q |\<in>| ta_der \<A> (term_of_gterm t)" using assms(2)
proof (induct rule: \<T>\<^sub>G.induct)
  case (const a)
  then show ?case using assms(1)
    by (force simp: ta_contains_aux_def)
next
  case (ind f n ss)
  obtain qs where "fset_of_list qs |\<subseteq>| Q" "length ss = length qs"
    "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (term_of_gterm (ss ! i))"
    using ind(4) Ex_list_of_length_P[of "length ss" "\<lambda> q i. q |\<in>| Q \<and> q |\<in>| ta_der \<A> (term_of_gterm (ss ! i))"]
    by (auto simp: fset_list_fsubset_eq_nth_conv) metis
  then show ?case using ind(1 - 3) assms(1)
    by (auto simp: ta_contains_aux_def) blast
qed

lemma ta_contains_aux_mono:
  assumes "ta_subset \<A> \<B>" and "Q\<^sub>2 |\<subseteq>| Q\<^sub>2'"
  shows "ta_contains_aux \<F> Q\<^sub>1 \<A> Q\<^sub>2 \<Longrightarrow> ta_contains_aux \<F> Q\<^sub>1 \<B> Q\<^sub>2'"
  using assms unfolding ta_contains_aux_def ta_subset_def
  by (meson fin_mono ftrancl_mono)
 
definition ta_contains :: "('f \<times> nat) set \<Rightarrow> ('f \<times> nat) set \<Rightarrow> ('q, 'f) ta \<Rightarrow> 'q fset \<Rightarrow> 'q fset \<Rightarrow> bool"
  where "ta_contains \<F> \<G> \<A> Q Q\<^sub>f \<equiv> ta_contains_aux \<F> Q \<A> Q \<and> ta_contains_aux \<G> Q \<A> Q\<^sub>f"

lemma ta_contains_mono:
  assumes "ta_subset \<A> \<B>" and "Q\<^sub>f |\<subseteq>| Q\<^sub>f'"
  shows "ta_contains \<F> \<G> \<A> Q Q\<^sub>f \<Longrightarrow> ta_contains \<F> \<G> \<B> Q Q\<^sub>f'"
  unfolding ta_contains_def 
  using ta_contains_aux_mono[OF assms(1) fsubset_refl]
  using ta_contains_aux_mono[OF assms]
  by blast

lemma ta_contains_both: 
  assumes contain: "ta_contains \<F> \<G> \<A> Q Q\<^sub>f"
  shows "\<And> t. groot t \<in> \<G> \<Longrightarrow> \<Union> (funas_gterm ` set (gargs t)) \<subseteq> \<F> \<Longrightarrow> t \<in> gta_lang Q\<^sub>f \<A>"
proof -
  fix t :: "'a gterm"
  assume F: "\<Union> (funas_gterm ` set (gargs t)) \<subseteq> \<F>" and G: "groot t \<in> \<G>"
  obtain g ss where t[simp]: "t = GFun g ss" by (cases t, auto)
  then have "\<exists> qs. length qs = length ss \<and> (\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (term_of_gterm (ss ! i)) \<and> qs ! i |\<in>| Q)"
    using contain ta_contains_aux_state_set[of \<F> Q \<A> "ss ! i" for i] F
    unfolding ta_contains_def \<T>\<^sub>G_funas_gterm_conv
    using Ex_list_of_length_P[of "length ss" "\<lambda> q i. q |\<in>| Q \<and> q |\<in>| ta_der \<A> (term_of_gterm (ss ! i))"]
    by auto (metis SUP_le_iff nth_mem)
  then obtain qs where " length qs = length ss"
    "\<forall> i < length qs. qs ! i |\<in>| ta_der \<A> (term_of_gterm (ss ! i))"
    "\<forall> i < length qs. qs ! i |\<in>| Q"
    by blast
  then obtain q where "q |\<in>| Q\<^sub>f" "q |\<in>| ta_der \<A> (term_of_gterm t)"
    using conjunct2[OF contain[unfolded ta_contains_def]] G
    by (auto simp: ta_contains_def ta_contains_aux_def fset_list_fsubset_eq_nth_conv) metis
  then show "t \<in> gta_lang Q\<^sub>f \<A>"
    by (intro gta_langI) simp
qed

lemma ta_contains: 
  assumes contain: "ta_contains \<F> \<F> \<A> Q Q\<^sub>f"
  shows "\<T>\<^sub>G \<F> \<subseteq> gta_lang Q\<^sub>f \<A>" (is "?A \<subseteq> _")
proof -
  have [simp]: "funas_gterm t \<subseteq> \<F> \<Longrightarrow> groot t \<in> \<F>" for t by (cases t) auto
  have [simp]: "funas_gterm t \<subseteq> \<F> \<Longrightarrow> \<Union> (funas_gterm ` set (gargs t)) \<subseteq> \<F>" for t
    by (cases t) auto
  show ?thesis using ta_contains_both[OF contain]
    by (auto simp: \<T>\<^sub>G_equivalent_def)
qed

text \<open>Relabeling, map finite set to natural numbers\<close>


lemma map_fset_to_nat_inj:
  assumes "Y |\<subseteq>| X"
  shows "finj_on (map_fset_to_nat X) Y"
proof -
  { fix x y assume "x |\<in>| X" "y |\<in>| X"
    then have "x |\<in>| fset_of_list (sorted_list_of_fset X)" "y |\<in>| fset_of_list (sorted_list_of_fset X)"
      by simp_all
    note this[unfolded mem_idx_fset_sound]
    then have "x = y" if "map_fset_to_nat X x = map_fset_to_nat X y"
      using that nth_eq_iff_index_eq[OF distinct_sorted_list_of_fset[of X]]
      by (force dest: mem_idx_sound_output simp: map_fset_to_nat_def) }
  then show ?thesis using assms
    by (auto simp add: finj_on_def' fBall_def)
qed

lemma map_fset_fset_to_nat_inj:
  assumes "Y |\<subseteq>| X"
  shows "finj_on (map_fset_fset_to_nat X) Y" using assms
proof -
  let ?f = "map_fset_fset_to_nat X"
  { fix x y assume "x |\<in>| X" "y |\<in>| X"
    then have "sorted_list_of_fset x |\<in>| fset_of_list (sorted_list_of_fset (sorted_list_of_fset |`| X))"
      "sorted_list_of_fset y |\<in>| fset_of_list (sorted_list_of_fset (sorted_list_of_fset |`| X))"
        unfolding map_fset_fset_to_nat_def by auto
    note this[unfolded mem_idx_fset_sound]
    then have "x = y" if "?f x = ?f y"
      using that nth_eq_iff_index_eq[OF distinct_sorted_list_of_fset[of "sorted_list_of_fset |`| X"]]
      by (auto simp: map_fset_fset_to_nat_def)
         (metis mem_idx_sound_output sorted_list_of_fset_simps(1))+}
  then show ?thesis using assms
    by (auto simp add: finj_on_def' fBall_def)
qed


lemma relabel_gta_lang [simp]:
  "gta_lang (relabel_Q\<^sub>f Q \<A>) (relabel_ta \<A>) = gta_lang Q \<A>"
proof -
  have "gta_lang (relabel_Q\<^sub>f Q \<A>) (relabel_ta \<A>) = gta_lang (Q |\<inter>| \<Q> \<A>) \<A>"
    unfolding relabel_ta_def relabel_Q\<^sub>f_def
    by (intro fmap_states_ta_lang2 map_fset_to_nat_inj) simp
  then show ?thesis by fastforce
qed


lemma \<L>_relable [simp]: "\<L> (relabel_reg R) = \<L> R"
  by (auto simp: \<L>_def relabel_reg_def)

lemma relabel_ta_lang [simp]:
  "ta_lang (relabel_Q\<^sub>f Q \<A>) (relabel_ta \<A>) = ta_lang Q \<A>"
  unfolding ta_lang_to_gta_lang
  using relabel_gta_lang
  by simp



lemma relabel_fset_gta_lang [simp]:
  "gta_lang (relabel_fset_Q\<^sub>f Q \<A>) (relabel_fset_ta \<A>) = gta_lang Q \<A>"
proof -
  have "gta_lang (relabel_fset_Q\<^sub>f Q \<A>) (relabel_fset_ta \<A>) = gta_lang (Q |\<inter>| \<Q> \<A>) \<A>"
    unfolding relabel_fset_Q\<^sub>f_def relabel_fset_ta_def
    by (intro fmap_states_ta_lang2 map_fset_fset_to_nat_inj) simp
  then show ?thesis by fastforce
qed


lemma \<L>_relable_fset [simp]: "\<L> (relable_fset_reg R) = \<L> R"
  by (auto simp: \<L>_def relable_fset_reg_def)

lemma ta_states_trim_ta:
  "\<Q> (trim_ta Q \<A>) |\<subseteq>| \<Q> \<A>"
  unfolding trim_ta_def using ta_prod_reach_states .

lemma trim_ta_reach: "\<Q> (trim_ta Q \<A>) |\<subseteq>| ta_reachable (trim_ta Q \<A>)"
  unfolding trim_ta_def using ta_only_prod_reachable ta_only_reach_reachable
  by metis

lemma trim_ta_prod: "\<Q> (trim_ta Q A) |\<subseteq>| ta_productive Q (trim_ta Q A)"
  unfolding trim_ta_def using ta_only_prod_productive
  by metis

lemma empty_gta_lang:
  "gta_lang Q (TA {||} {||}) = {}"
  using ta_reachable_gtermI
  by (force simp: gta_lang_def gta_der_def elim!: ta_langE)

abbreviation empty_reg where
  "empty_reg \<equiv> Reg {||} (TA {||} {||})"

lemma \<L>_epmty:
  "\<L> empty_reg = {}"
  by (auto simp: \<L>_def empty_gta_lang)

lemma const_ta_lang:
  "gta_lang {|q|} (TA  {| TA_rule f [] q |} {||}) = {GFun f []}"
proof -
  have [dest!]: "q' |\<in>| ta_der (TA  {| TA_rule f [] q |} {||}) t' \<Longrightarrow> ground t' \<Longrightarrow> t' = Fun f []" for t' q'
    by (induct t') auto
  show ?thesis
    by (auto simp: gta_lang_def gta_der_def elim!: gta_langE)
       (metis gterm_of_term.simps list.simps(8) term_of_gterm_inv)
qed


lemma run_argsD:
  "run \<A> s t \<Longrightarrow> length (gargs s) = length (gargs t) \<and> (\<forall> i < length (gargs t). run \<A> (gargs s ! i) (gargs t ! i))"
  using run.cases by fastforce

lemma run_root_rule:
  "run \<A> s t \<Longrightarrow> TA_rule (groot_sym t) (map ex_comp_state (gargs s)) (ex_rule_state s) |\<in>| (rules \<A>) \<and>
     (ex_rule_state s = ex_comp_state s \<or> (ex_rule_state s, ex_comp_state s) |\<in>| (eps \<A>)|\<^sup>+|)"
  by (cases s; cases t) (auto elim: run.cases)

lemma run_poss_eq: "run \<A> s t \<Longrightarrow> gposs s = gposs t"
  by (induct rule: run.induct) auto

lemma run_gsubt_cl:
  assumes "run \<A> s t" and "p \<in> gposs t"
  shows "run \<A> (gsubt_at s p) (gsubt_at t p)" using assms
proof (induct p arbitrary: s t)
  case (Cons i p) show ?case using Cons(1) Cons(2-)
    by (cases s; cases t) (auto dest: run_argsD)
qed auto

lemma run_replace_at:
  assumes "run \<A> s t" and "run \<A> u v" and "p \<in> gposs s"
    and "ex_comp_state (gsubt_at s p) = ex_comp_state u"
  shows "run \<A> s[p \<leftarrow> u]\<^sub>G t[p \<leftarrow> v]\<^sub>G" using assms
proof (induct p arbitrary: s t)
  case (Cons i p)
  obtain r q qs f ts where [simp]: "s = GFun (r, q) qs" "t = GFun f ts" by (cases s, cases t) auto
  have *: "j < length qs \<Longrightarrow> ex_comp_state (qs[i := (qs ! i)[p \<leftarrow> u]\<^sub>G] ! j) = ex_comp_state (qs ! j)" for j
    using Cons(5) by (cases "i = j", cases p) auto
  have [simp]: "map ex_comp_state (qs[i := (qs ! i)[p \<leftarrow> u]\<^sub>G]) = map ex_comp_state qs" using Cons(5)
    by (auto simp: *[unfolded comp_def] intro!: nth_equalityI)
  have "run \<A> (qs ! i)[p \<leftarrow> u]\<^sub>G (ts ! i)[p \<leftarrow> v]\<^sub>G" using Cons(2-)
    by (intro Cons(1)) (auto dest: run_argsD)
  moreover have "i < length qs" "i < length ts" using Cons(4) run_poss_eq[OF Cons(2)]
    by force+
  ultimately show ?case using Cons(2) run_root_rule[OF Cons(2)]
    by (fastforce simp: nth_list_update dest: run_argsD intro!: run.intros)
qed simp

text \<open>relating runs to derivation definition\<close>

lemma run_to_comp_st_gta_der:
  "run \<A> s t \<Longrightarrow> ex_comp_state s |\<in>| gta_der \<A> t"
proof (induct s arbitrary: t)
  case (GFun q qs)
  show ?case using GFun(1)[OF nth_mem, of i "gargs t ! i" for i]
    using run_argsD[OF GFun(2)] run_root_rule[OF GFun(2-)]
    by (cases t) (auto simp: gta_der_def intro!: exI[of _ "map ex_comp_state qs"] exI[of _ "fst q"])
qed

lemma run_to_rule_st_gta_der:
  assumes "run \<A> s t" shows "ex_rule_state s |\<in>| gta_der \<A> t"
proof (cases s)
  case [simp]: (GFun q qs)
  have "i < length qs \<Longrightarrow> ex_comp_state (qs ! i) |\<in>| gta_der \<A> (gargs t ! i)" for i
    using run_to_comp_st_gta_der[of \<A>] run_argsD[OF assms] by force
  then show ?thesis using conjunct1[OF run_argsD[OF assms]] run_root_rule[OF assms]
    by (cases t) (auto simp: gta_der_def intro!: exI[of _ "map ex_comp_state qs"] exI[of _ "fst q"])
qed

lemma run_to_gta_der_gsubt_at:
  assumes "run \<A> s t" and "p \<in> gposs t"
  shows "ex_rule_state (gsubt_at s p) |\<in>| gta_der \<A> (gsubt_at t p)"
    "ex_comp_state (gsubt_at s p) |\<in>| gta_der \<A> (gsubt_at t p)"
  using assms run_gsubt_cl[THEN run_to_comp_st_gta_der] run_gsubt_cl[THEN run_to_rule_st_gta_der]
  by blast+

lemma gta_der_to_run:
  "q |\<in>| gta_der \<A> t \<Longrightarrow> (\<exists> p qs. run \<A> (GFun (p, q) qs) t)" unfolding gta_der_def
proof (induct rule: ta_der_gterm_induct)
  case (GFun f ts ps p q)
  from GFun(5) Ex_list_of_length_P[of "length ts" "\<lambda> qs i. run \<A> (GFun (fst qs, ps ! i) (snd qs)) (ts ! i)"]
  obtain qss where mid: "length qss = length ts" "\<forall> i < length ts .run \<A> (GFun (fst (qss ! i), ps ! i) (snd (qss ! i))) (ts ! i)"
    by auto
  have [simp]: "map (ex_comp_state \<circ> (\<lambda>(qs, y). GFun (fst y, qs) (snd y))) (zip ps qss) = ps" using GFun(2) mid(1)
    by (intro nth_equalityI) auto
  show ?case using mid GFun(1 - 4)
    by (intro exI[of _ p] exI[of _ "map2 (\<lambda> f args. GFun (fst args, f) (snd args)) ps qss"])
       (auto intro: run.intros)
qed

lemma run_ta_der_ctxt_split1:
  assumes "run \<A> s t" "p \<in> gposs t"
  shows "ex_comp_state s |\<in>| ta_der \<A> (ctxt_at_pos (term_of_gterm t) p)\<langle>Var (ex_comp_state (gsubt_at s p))\<rangle>"
  using assms
proof (induct p arbitrary: s t)
  case (Cons i p)
  obtain q f qs ts where [simp]: "s = GFun q qs" "t = GFun f ts" and l: "length qs = length ts"
    using run_argsD[OF Cons(2)] by (cases s, cases t) auto
  from Cons(2, 3) l have "ex_comp_state (qs ! i) |\<in>| ta_der \<A> (ctxt_at_pos (term_of_gterm (ts ! i)) p)\<langle>Var (ex_comp_state (gsubt_at (qs ! i) p))\<rangle>"
    by (intro Cons(1)) (auto dest: run_argsD)
  then show ?case using Cons(2-) l
    by (fastforce simp: nth_append_Cons min_def dest: run_root_rule run_argsD
    intro!: exI[of _ "map ex_comp_state (gargs s)"]  exI[of _ "ex_rule_state s"]
            run_to_comp_st_gta_der[of \<A> "qs ! i" "ts ! i" for i, unfolded comp_def gta_der_def])
qed auto


lemma run_ta_der_ctxt_split2:
  assumes "run \<A> s t" "p \<in> gposs t"
  shows "ex_comp_state s |\<in>| ta_der \<A> (ctxt_at_pos (term_of_gterm t) p)\<langle>Var (ex_rule_state (gsubt_at s p))\<rangle>"
proof (cases "ex_rule_state (gsubt_at s p) = ex_comp_state (gsubt_at s p)")
  case False then show ?thesis
    using run_root_rule[OF run_gsubt_cl[OF assms]]
    by (intro ta_der_eps_ctxt[OF run_ta_der_ctxt_split1[OF assms]]) auto
qed (auto simp: run_ta_der_ctxt_split1[OF assms, unfolded comp_def])

end