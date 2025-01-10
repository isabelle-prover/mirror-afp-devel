theory Resource
  imports
    ResTerm
    ResNormCompare
begin

section\<open>Resources\<close>

text\<open>
  We define resources as the quotient of resource terms by their equivalence.
  To decide the equivalence we use resource term normalisation procedures, primarily the one based
  on rewriting.
\<close>

subsection\<open>Quotient Type\<close>

text\<open>
  Resource term mapper satisfies the functor assumptions: it commutes with function composition and
  mapping identities is itself identity
\<close>
functor map_res_term
proof
  fix f g and f' :: "'u \<Rightarrow> 'x" and g' :: "'v \<Rightarrow> 'y" and x :: "('a, 'b) res_term"
  show "(map_res_term f' g' \<circ> map_res_term f g) x = map_res_term (f' \<circ> f) (g' \<circ> g) x"
    by (induct x ; simp add: comp_def)
next
  show "map_res_term id id = id"
    by (standard, simp add: id_def res_term.map_ident)
qed

text\<open>Resources are resource terms modulo their equivalence\<close>
quotient_type ('a, 'b) resource = "('a, 'b) res_term" / res_term_equiv
  using res_term_equiv.equivp .

lemma abs_resource_eqI [intro]:
  "x \<sim> y \<Longrightarrow> abs_resource x = abs_resource y"
  using resource.abs_eq_iff by blast
lemma abs_resource_eqE [elim]:
  "\<lbrakk>abs_resource x = abs_resource y; x \<sim> y \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  using resource.abs_eq_iff by blast

text\<open>Resource representation then abstraction is identity\<close>
lemmas resource_abs_of_rep [simp] = Quotient3_abs_rep[OF Quotient3_resource]

text\<open>Lifted normalisation gives a normalised representative term for a resource\<close>
lift_definition of_resource :: "('a, 'b) resource \<Rightarrow> ('a, 'b) res_term" is normal_rewr
  by (rule res_term_equiv_imp_normal_rewr)

lemma of_resource_absorb_normal_rewr [simp]:
  "normal_rewr (of_resource x) = of_resource x"
  by (simp add: of_resource.rep_eq)

lemma of_resource_absorb_normal_dir [simp]:
  "normal_dir (of_resource x) = of_resource x"
  by (simp add: normal_rewr_is_normal_dir[symmetric] of_resource.rep_eq)

text\<open>Equality of resources can be characterised by equality of representative terms\<close>
instantiation resource :: (equal, equal) equal
begin

definition equal_resource :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool"
  where "equal_resource a b = (of_resource a = of_resource b)"

instance
proof
  fix x y :: "('a ,'b) resource"
  have "(of_resource x = of_resource y) = (x = y)"
    by transfer (metis res_term_equiv_is_normal_rewr)
  then show "equal_class.equal x y = (x = y)"
    unfolding equal_resource_def .
qed
end

subsection\<open>Lifting Bounded Natural Functor Structure\<close>

text\<open>Equivalent terms have equal atom sets\<close>
lemma res_term_equiv_set1 [simp]:
  "x \<sim> y \<Longrightarrow> set1_res_term x = set1_res_term y"
proof (induct rule: res_term_equiv.induct)
     case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next case nil then show ?case by simp
next case (singleton a) then show ?case by simp
next case (merge x y z) then show ?case by (simp add: Un_left_commute)
next case (parallel xs ys) then show ?case by (induct rule: list_all2_induct ; simp)
next case (nondet x y u v) then show ?case by simp
next case (executable x y u v) then show ?case by simp
next case (repeatable x y u v) then show ?case by simp
next case (sym x y) then show ?case by simp
next case (trans x y z) then show ?case by simp
qed

lemma res_term_equiv_set2 [simp]:
  "x \<sim> y \<Longrightarrow> set2_res_term x = set2_res_term y"
proof (induct rule: res_term_equiv.induct)
     case empty then show ?case by simp
next case anything then show ?case by simp
next case (res x) then show ?case by simp
next case (copyable x) then show ?case by simp
next case nil then show ?case by simp
next case (singleton a) then show ?case by simp
next case (merge x y z) then show ?case by (simp add: Un_left_commute)
next case (parallel xs ys) then show ?case by (induct rule: list_all2_induct ; simp)
next case (nondet x y u v) then show ?case by simp
next case (executable x y u v) then show ?case by simp
next case (repeatable x y u v) then show ?case by simp
next case (sym x y) then show ?case by simp
next case (trans x y z) then show ?case by simp
qed

text\<open>
  BNF structure can be lifted.
  Proof inspired by F{\"u}rer et al.~\<^cite>\<open>"fuerer_et_al-2020"\<close>.
\<close>
lift_bnf ('a, 'b) resource
proof safe
  fix R1 :: "'a \<Rightarrow> 'u \<Rightarrow> bool"
  and R2 :: "'b \<Rightarrow> 'v \<Rightarrow> bool"
  and S1 :: "'u \<Rightarrow> 'x \<Rightarrow> bool"
  and S2 :: "'v \<Rightarrow> 'y \<Rightarrow> bool"
  and x :: "('a, 'b) res_term"
  and y y' :: "('u, 'v) res_term"
  and z :: "('x, 'y) res_term"

  assume assms:
    "R1 OO S1 \<noteq> bot"
    "R2 OO S2 \<noteq> bot"
    "rel_res_term R1 R2 x y"
    "y \<sim> y'"
    "rel_res_term S1 S2 y' z"

  obtain u where ux: "x = map_res_term fst fst u" and uy: "y = map_res_term snd snd u"
     and u_set: "set1_res_term u \<subseteq> {(x, y). R1 x y}" "set2_res_term u \<subseteq> {(x, y). R2 x y}"
    using res_term.in_rel[THEN iffD1, OF assms(3)] by blast
  obtain v where vy': "y' = map_res_term fst fst v" and vz: "z = map_res_term snd snd v"
      and v_set: "set1_res_term v \<subseteq> {(x, y). S1 x y}" "set2_res_term v \<subseteq> {(x, y). S2 x y}"
    using res_term.in_rel[THEN iffD1, OF assms(5)] by blast

  obtain w where wy: "w = normal_rewr y" and wy': "w = normal_rewr y'"
    using assms(4) res_term_equiv_imp_normal_rewr by blast

  obtain u' where uu': "u \<sim> u'" and u'w: "w = map_res_term snd snd u'"
    by (metis res_term_equiv_normal_rewr normal_rewr_map uy wy)
  obtain v' where vv': "v \<sim> v'" and v'w: "w = map_res_term fst fst v'"
    by (metis res_term_equiv_normal_rewr normal_rewr_map vy' wy')

  obtain x' where xx': "x \<sim> x'" and u'x': "x' = map_res_term fst fst u'"
    using map_res_term_preserves_equiv uu' ux by blast
  obtain z' where zz': "z \<sim> z'" and v'z': "z' = map_res_term snd snd v'"
    using map_res_term_preserves_equiv vv' vz by blast

  have "rel_res_term R1 R2 x' w"
    using res_term.in_rel u'x' u'w uu' u_set by force
  moreover have "rel_res_term S1 S2 w z'"
    using res_term.in_rel v'z' v'w vv' v_set by force
  ultimately have "rel_res_term (R1 OO S1) (R2 OO S2) x' z'"
    using res_term.rel_compp relcompp.relcompI by metis
  then show "((\<sim>) OO rel_res_term (R1 OO S1) (R2 OO S2) OO (\<sim>)) x z"
    using xx' zz'[symmetric] by (meson relcompp.relcompI)
next
  show "\<And>Ss1 x xa xb.
       \<lbrakk>x \<in> (\<Inter>As1\<in>Ss1. {(x, x'). x \<sim> x'} `` {x. set1_res_term x \<subseteq> As1});
        x \<notin> {(x, x'). x \<sim> x'} `` {x. set1_res_term x \<subseteq> \<Inter> Ss1}; xa \<in> Ss1; xa \<notin> {};
        xb \<in> \<Inter> Ss1\<rbrakk>
       \<Longrightarrow> xb \<in> {}"
    by simp (metis Inf_greatest res_term_equiv_set1)
next
  show "\<And>Ss2 x xa xb.
       \<lbrakk>x \<in> (\<Inter>As2\<in>Ss2. {(x, x'). x \<sim> x'} `` {x. set2_res_term x \<subseteq> As2});
        x \<notin> {(x, x'). x \<sim> x'} `` {x. set2_res_term x \<subseteq> \<Inter> Ss2}; xa \<in> Ss2; xa \<notin> {};
        xb \<in> \<Inter> Ss2\<rbrakk>
       \<Longrightarrow> xb \<in> {}"
    by simp (metis Inf_greatest res_term_equiv_set2)
qed

text\<open>Resource map can be given a code equation through the term map\<close>
lemma map_resource_code [code]:
  "map_resource f g (abs_resource x) = abs_resource (map_res_term f g x)"
  by transfer simp

text\<open>Atom sets of a resource are those sets of its representative term\<close>
lemma set1_resource:
  fixes x :: "('a, 'b) resource"
  shows "set1_resource x = set1_res_term (of_resource x)"
proof transfer
  fix x :: "('a, 'b) res_term"

  let ?InrL = "Inr :: 'a \<Rightarrow> unit + 'a"
  let ?InrC = "Inr :: 'b \<Rightarrow> unit + 'b"

  have
    " (\<Inter>mx \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x)). \<Union> (Basic_BNFs.setr ` set1_res_term mx))
    = (\<Union>x :: unit + 'a \<in> set1_res_term (map_res_term ?InrL ?InrC (normal_rewr x)). {xa. x = Inr xa})"
  proof (subst Inter_all_same)
    show "\<Union> (Basic_BNFs.setr ` set1_res_term u) = \<Union> (Basic_BNFs.setr ` set1_res_term v)"
       if "u \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      and "v \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      for u v
      using that by (metis mem_Collect_eq res_term_equiv_set1)
    show "map_res_term ?InrL ?InrC (normal_rewr x) \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      by (metis CollectI map_res_term_preserves_equiv res_term_equiv_normal_rewr)
    show
      " \<Union> (Basic_BNFs.setr ` set1_res_term (map_res_term ?InrL ?InrC (normal_rewr x)))
      = (\<Union>x\<in>set1_res_term (map_res_term ?InrL ?InrC (normal_rewr x)). {xa. x = Inr xa})"
      by (simp add: setr_def setrp.simps)
  qed
  then show
    " (\<Inter>mx\<in>Collect ((\<sim>) (map_res_term ?InrL ?InrC x)). \<Union> (Basic_BNFs.setr ` set1_res_term mx))
    = set1_res_term (normal_rewr x)"
    by (simp add: res_term.set_map setr_def setrp.simps)
qed
lemma set2_resource:
  fixes x :: "('a, 'b) resource"
  shows "set2_resource x = set2_res_term (of_resource x)"
proof transfer
  fix x :: "('a, 'b) res_term"

  let ?InrL = "Inr :: 'a \<Rightarrow> unit + 'a"
  let ?InrC = "Inr :: 'b \<Rightarrow> unit + 'b"

  have
    " (\<Inter>mx \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x)). \<Union> (Basic_BNFs.setr ` set2_res_term mx))
    = (\<Union>x :: unit + 'b \<in> set2_res_term (map_res_term ?InrL ?InrC (normal_rewr x)). {xa. x = Inr xa})"
  proof (subst Inter_all_same)
    show "\<Union> (Basic_BNFs.setr ` set2_res_term u) = \<Union> (Basic_BNFs.setr ` set2_res_term v)"
       if "u \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      and "v \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      for u v
      using that by (metis mem_Collect_eq res_term_equiv_set2)
    show "map_res_term ?InrL ?InrC (normal_rewr x) \<in> Collect ((\<sim>) (map_res_term ?InrL ?InrC x))"
      by (metis CollectI map_res_term_preserves_equiv res_term_equiv_normal_rewr)
    show
      " \<Union> (Basic_BNFs.setr ` set2_res_term (map_res_term ?InrL ?InrC (normal_rewr x)))
      = (\<Union>x\<in>set2_res_term (map_res_term ?InrL ?InrC (normal_rewr x)). {xa. x = Inr xa})"
      by (simp add: setr_def setrp.simps)
  qed
  then show
    " (\<Inter>mx\<in>Collect ((\<sim>) (map_res_term ?InrL ?InrC x)). \<Union> (Basic_BNFs.setr ` set2_res_term mx))
    = set2_res_term (normal_rewr x)"
    by (simp add: res_term.set_map setr_def setrp.simps)
qed

subsection\<open>Lifting Constructors\<close>

text\<open>All term constructors are easily lifted thanks to the term equivalence being a congruence\<close>
lift_definition Empty :: "('a, 'b) resource"
  is res_term.Empty .
lift_definition Anything :: "('a, 'b) resource"
  is res_term.Anything .
lift_definition Res :: "'a \<Rightarrow> ('a, 'b) resource"
  is res_term.Res .
lift_definition Copyable :: "'b \<Rightarrow> ('a, 'b) resource"
  is res_term.Copyable .
lift_definition Parallel :: "('a, 'b) resource list \<Rightarrow> ('a, 'b) resource"
  is res_term.Parallel using res_term_equiv.parallel .
lift_definition NonD :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource"
  is res_term.NonD using res_term_equiv.nondet .
lift_definition Executable :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource"
  is res_term.Executable using res_term_equiv.executable .
lift_definition Repeatable :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource"
  is res_term.Repeatable using res_term_equiv.repeatable .

lemmas resource_constr_abs_eq =
  Empty.abs_eq Anything.abs_eq Res.abs_eq Copyable.abs_eq Parallel.abs_eq NonD.abs_eq
  Executable.abs_eq Repeatable.abs_eq

text\<open>Resources can be split into cases like terms\<close>
lemma resource_cases:
  fixes r :: "('a, 'b) resource"
  obtains
    (Empty) "r = Empty"
  | (Anything) "r = Anything"
  | (Res) a where "r = Res a"
  | (Copyable) x where "r = Copyable x"
  | (Parallel) xs where "r = Parallel xs"
  | (NonD) x y where "r = NonD x y"
  | (Executable) x y where "r = Executable x y"
  | (Repeatable) x y where "r = Repeatable x y"
proof transfer
  fix r :: "('a, 'b) res_term" and thesis
  assume "r \<sim> res_term.Empty \<Longrightarrow> thesis"
     and "r \<sim> res_term.Anything \<Longrightarrow> thesis"
     and "\<And>a. r \<sim> res_term.Res a \<Longrightarrow> thesis"
     and "\<And>x. r \<sim> res_term.Copyable x \<Longrightarrow> thesis"
     and "\<And>xs. r \<sim> res_term.Parallel xs \<Longrightarrow> thesis"
     and "\<And>x y. r \<sim> res_term.NonD x y \<Longrightarrow> thesis"
     and "\<And>x y. r \<sim> res_term.Executable x y \<Longrightarrow> thesis"
     and "\<And>x y. r \<sim> res_term.Repeatable x y \<Longrightarrow> thesis"
  note a = this

  show thesis
    using a by (cases r) (blast intro: res_term_equiv.refl)+
qed

text\<open>Resources can be inducted over like terms\<close>
lemma resource_induct [case_names Empty Anything Res Copyable Parallel NonD Executable Repeatable]:
  assumes "P Empty"
      and "P Anything"
      and "\<And>a. P (Res a)"
      and "\<And>x. P (Copyable x)"
      and "\<And>xs. (\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> P (Parallel xs)"
      and "\<And>x y. \<lbrakk>P x; P y\<rbrakk> \<Longrightarrow> P (NonD x y)"
      and "\<And>x y. \<lbrakk>P x; P y\<rbrakk> \<Longrightarrow> P (Executable x y)"
      and "\<And>x y. \<lbrakk>P x; P y\<rbrakk> \<Longrightarrow> P (Repeatable x y)"
    shows "P x"
  using res_term.induct[of "\<lambda>x. P (abs_resource x)" "rep_resource x", unfolded resource_abs_of_rep]
  using assms
  by (smt (verit, del_insts) resource_constr_abs_eq imageE list.set_map)

text\<open>Representative terms of the lifted constructors apart from @{const Parallel} are known\<close>
lemma of_resource_simps [simp]:
  "of_resource Empty = res_term.Empty"
  "of_resource Anything = res_term.Anything"
  "of_resource (Res a) = res_term.Res a"
  "of_resource (Copyable b) = res_term.Copyable b"
  "of_resource (NonD x y) = res_term.NonD (of_resource x) (of_resource y)"
  "of_resource (Executable x y) = res_term.Executable (of_resource x) (of_resource y)"
  "of_resource (Repeatable x y) = res_term.Repeatable (of_resource x) (of_resource y)"
  by (transfer, simp add: normal_rewr_nondet normal_rewr_executable normal_rewr_repeatable)+

text\<open>Basic resource term equivalences become resource equalities\<close>
lemma [simp]:
  shows resource_empty: "Parallel [] = Empty"
    and resource_singleton: "Parallel [x] = x"
    and resource_merge: "Parallel (xs @ [Parallel ys] @ zs) = Parallel (xs @ ys @ zs)"
    and resource_drop: "Parallel (xs @ [Empty] @ zs) = Parallel (xs @ zs)"
  by ( transfer
     , intro res_term_equiv.nil res_term_equiv.singleton res_term_equiv.merge res_term_equiv.drop)+

lemma resource_parallel_nested [simp]:
  "Parallel (Parallel xs # ys) = Parallel (xs @ ys)"
  using resource_merge[of Nil] by simp

lemma resource_decompose:
  assumes "Parallel xs = Parallel ys"
      and "Parallel us = Parallel vs"
    shows "Parallel (xs @ us) = Parallel (ys @ vs)"
  using assms by (metis append_Nil append_Nil2 resource_merge)

lemma resource_drop_list:
  "(\<And>y. y \<in> set ys \<Longrightarrow> y = Empty) \<Longrightarrow> Parallel (xs @ ys @ zs) = Parallel (xs @ zs)"
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case
    by simp (metis Cons_eq_appendI resource_drop self_append_conv2)
qed

text\<open>Equality of resources except @{const Parallel} implies equality of their children\<close>
lemma
  shows resource_res_eq: "Res x = Res y \<Longrightarrow> x = y"
    and resource_copyable_eq: "Copyable x = Copyable y \<Longrightarrow> x = y"
  by (transfer, simp add: res_term_equiv_is_normal_rewr)+

lemma resource_nondet_eq:
  "NonD a b = NonD x y \<Longrightarrow> a = x"
  "NonD a b = NonD x y \<Longrightarrow> b = y"
  by (transfer, simp add: normal_rewr_nondet res_term_equiv_is_normal_rewr)+

lemma resource_executable_eq:
  "Executable a b = Executable x y \<Longrightarrow> a = x"
  "Executable a b = Executable x y \<Longrightarrow> b = y"
  by (transfer, simp add: normal_rewr_executable res_term_equiv_is_normal_rewr)+

lemma resource_repeatable_eq:
  "Repeatable a b = Repeatable x y \<Longrightarrow> a = x"
  "Repeatable a b = Repeatable x y \<Longrightarrow> b = y"
  by (transfer, simp add: normal_rewr_repeatable res_term_equiv_is_normal_rewr)+

text\<open>Many resource inequalities not involving @{const Parallel} are simple to prove\<close>
lemma resource_neq [simp]:
  "Empty \<noteq> Anything"
  "Empty \<noteq> Res a"
  "Empty \<noteq> Copyable b"
  "Empty \<noteq> NonD x y"
  "Empty \<noteq> Executable x y"
  "Empty \<noteq> Repeatable x y"
  "Anything \<noteq> Res a"
  "Anything \<noteq> Copyable b"
  "Anything \<noteq> NonD x y"
  "Anything \<noteq> Executable x y"
  "Anything \<noteq> Repeatable x y"
  "Res a \<noteq> Copyable b"
  "Res a \<noteq> NonD x y"
  "Res a \<noteq> Executable x y"
  "Res a \<noteq> Repeatable x y"
  "Copyable b \<noteq> NonD x y"
  "Copyable b \<noteq> Executable x y"
  "Copyable b \<noteq> Repeatable x y"
  "NonD x y \<noteq> Executable u v"
  "NonD x y \<noteq> Repeatable u v"
  "Executable x y \<noteq> Repeatable u v"
  by (transfer, simp add: res_term_equiv_is_normal_dir)+

text\<open>Resource map of lifted constructors can be simplified\<close>
lemma map_resource_simps [simp]:
  "map_resource f g Empty = Empty"
  "map_resource f g Anything = Anything"
  "map_resource f g (Res a) = Res (f a)"
  "map_resource f g (Copyable b) = Copyable (g b)"
  "map_resource f g (Parallel xs) = Parallel (map (map_resource f g) xs)"
  "map_resource f g (NonD x y) = NonD (map_resource f g x) (map_resource f g y)"
  "map_resource f g (Executable x y) = Executable (map_resource f g x) (map_resource f g y)"
  "map_resource f g (Repeatable x y) = Repeatable (map_resource f g x) (map_resource f g y)"
  by (transfer, simp)+

text\<open>
  Note that resource term size doesn't lift, because @{term "res_term.Parallel [res_term.Empty]"}
  is equivalent to @{term Empty} but their sizes are 2 and 1 respectively.\<close>

subsection\<open>Parallel Product\<close>

text\<open>We introduce infix syntax for binary @{term Parallel}, forming a resource product\<close>
definition resource_par :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource"
    (infixr "\<odot>" 120)
  where "x \<odot> y = Parallel [x, y]"

text\<open>For the purposes of code generation we act as if we lifted it\<close>
lemma resource_par_code [code]:
  "abs_resource x \<odot> abs_resource y = abs_resource (ResTerm.Parallel [x, y])"
  unfolding resource_par_def by transfer simp

text\<open>Parallel product can be merged with @{const Parallel} resources on either side or around it\<close>
lemma resource_par_is_parallel [simp]:
  "x \<odot> Parallel xs = Parallel (x # xs)"
  "Parallel xs \<odot> x = Parallel (xs @ [x])"
  using resource_merge[of "[x]" xs Nil] by (simp_all add: resource_par_def)

lemma resource_par_nested_start [simp]:
  "Parallel (x \<odot> y # zs) = Parallel (x # y # zs)"
  by (metis append_Cons append_Nil resource_merge resource_par_is_parallel(1) resource_singleton)

lemma resource_par_nested [simp]:
  "Parallel (xs @ a \<odot> b # ys) = Parallel (xs @ a # b # ys)"
  using resource_decompose resource_par_nested_start by blast

text\<open>
  Lifted constructor @{const Parallel}, which does not have automatic code equations, can be given
  code equations using this resource product
\<close>
lemmas [code] = resource_empty resource_par_is_parallel(1)[symmetric]

text\<open>
  This resource product sometimes leads to overly long expressions when generating code for
  formalised models, but these can be limited by code unfolding
\<close>
lemma resource_par_res [code_unfold]:
  "Res x \<odot> y = Parallel [Res x, y]"
  by (simp add: resource_par_def)
lemma resource_parallel_res [code_unfold]:
  "Parallel [Res x, Parallel ys] = Parallel (Res x # ys)"
  by (metis resource_par_is_parallel(1) resource_par_res)

text\<open>We show that this resource product is a monoid, meaning it is unital and associative\<close>
lemma resource_par_unitL [simp]:
  "Empty \<odot> x = x"
proof -
  have "Parallel [Empty, x] = x"
    by (metis append_Nil resource_empty resource_parallel_nested resource_singleton)
  then show ?thesis
    by (simp add: resource_par_def)
qed

lemma resource_par_unitR [simp]:
  "x \<odot> Empty = x"
proof -
  have "Parallel [x, Empty] = x"
    by (metis resource_empty resource_par_is_parallel(1) resource_singleton)
  then show ?thesis
    by (simp add: resource_par_def)
qed

lemma resource_par_assoc [simp]:
  "(a \<odot> b) \<odot> c = a \<odot> (b \<odot> c)"
  by (metis resource_par_def resource_par_is_parallel(1) resource_par_nested_start)

text\<open>Resource map passes through resource product\<close>
lemma resource_par_map [simp]:
  "map_resource f g (resource_par a b) = resource_par (map_resource f g a) (map_resource f g b)"
  by (simp add: resource_par_def)

text\<open>
  Representative of resource product is normalised @{const res_term.Parallel} term of the two
  children's representations
\<close>
lemma of_resource_par:
  "of_resource (resource_par x y) = normal_rewr (res_term.Parallel [of_resource x, of_resource y])"
  unfolding resource_par_def
  by transfer
     (meson res_term_equiv_normal_rewr res_term_parallel_cons res_term_equiv.singleton_both
            res_term_equiv_imp_normal_rewr)

subsection\<open>Lifting Parallel Parts\<close>

lift_definition parallel_parts :: "('a, 'b) resource \<Rightarrow> ('a, 'b) resource list"
  is ResTerm.parallel_parts by (simp add: equiv_parallel_parts)

text\<open>Parallel parts of the lifted constructors can be simplified like the term version\<close>
lemma parallel_parts_simps:
  "parallel_parts Empty = []"
  "parallel_parts Anything = [Anything]"
  "parallel_parts (Res a) = [Res a]"
  "parallel_parts (Copyable b) = [Copyable b]"
  "parallel_parts (Parallel xs) = concat (map parallel_parts xs)"
  "parallel_parts (NonD x y) = [NonD x y]"
  "parallel_parts (Executable x y) = [Executable x y]"
  "parallel_parts (Repeatable x y) = [Repeatable x y]"
proof -
  show "parallel_parts Empty = []"
    by (simp add: parallel_parts.abs_eq resource_constr_abs_eq)
  show "parallel_parts Anything = [Anything]"
    by (simp add: parallel_parts.abs_eq resource_constr_abs_eq)
  show "parallel_parts (Res a) = [Res a]"
    by (simp add: parallel_parts.abs_eq resource_constr_abs_eq)
  show "parallel_parts (Copyable b) = [Copyable b]"
    by (simp add: parallel_parts.abs_eq Copyable_def)
  show "parallel_parts (Parallel xs) = concat (map parallel_parts xs)"
  proof (induct xs)
    case Nil
    then show ?case
      by (simp add: parallel_parts.abs_eq Empty_def)
  next
    case (Cons a xs)
    then show ?case
      by (simp add: parallel_parts.abs_eq Parallel_def, simp add: parallel_parts_def)
  qed
  show "parallel_parts (NonD x y) = [NonD x y]"
    by (simp add: parallel_parts.abs_eq NonD_def)
  show "parallel_parts (Executable x y) = [Executable x y]"
    by (simp add: parallel_parts.abs_eq Executable_def)
  show "parallel_parts (Repeatable x y) = [Repeatable x y]"
    by (simp add: parallel_parts.abs_eq Repeatable_def)
qed

text\<open>Every resource is the same as @{const Parallel} resource formed from its parallel parts\<close>
lemma resource_eq_parallel_parts:
  "x = Parallel (parallel_parts x)"
  by transfer (rule parallel_parts_eq)

text\<open>Resources with equal parallel parts are equal\<close>
lemma parallel_parts_cong:
  "parallel_parts x = parallel_parts y \<Longrightarrow> x = y"
  by (metis resource_eq_parallel_parts)

text\<open>Parallel parts of the resource product are the two resources' parallel parts\<close>
lemma parallel_parts_par:
  "parallel_parts (a \<odot> b) = parallel_parts a @ parallel_parts b"
  by (simp add: resource_par_def parallel_parts_simps)

subsection\<open>Lifting Parallelisation\<close>

lift_definition parallelise :: "('a, 'b) resource list \<Rightarrow> ('a, 'b) resource"
  is ResTerm.parallelise
  by (metis equiv_parallel_parts res_term_equiv.parallel parallel_parts_parallelise_eq)

text\<open>Parallelisation of the lifted constructors can be simplified like the term version\<close>
lemma parallelise_resource_simps [code]:
  "parallelise [] = Empty"
  "parallelise [x] = x"
  "parallelise (x#y#zs) = Parallel (x#y#zs)"
  by (transfer, simp)+

subsection\<open>Representative of Parallel Resource\<close>

text\<open>
  By relating to direct normalisation, representative term for @{const Parallel} is parallelisation
  of representatives of its parallel parts
\<close>
lemma of_resource_parallel:
  " of_resource (Parallel xs)
  = ResTerm.parallelise (merge_all_parallel (remove_all_empty (map of_resource xs)))"
  by transfer (simp add: normal_rewr_is_normal_dir)

text\<open>Equality of @{const Parallel} resources implies equality of their parallel parts\<close>
lemma resource_parallel_eq:
  "Parallel xs = Parallel ys \<Longrightarrow> concat (map parallel_parts xs) = concat (map parallel_parts ys)"
  by (fastforce simp add: parallel_parts_simps(5)[symmetric])

text\<open>With this, we can prove simplification equations for atom sets\<close>
lemma set1_resource_simps [simp]:
  "set1_resource Empty = {}"
  "set1_resource Anything = {}"
  "set1_resource (Res a) = {a}"
  "set1_resource (Copyable b) = {}"
  "set1_resource (Parallel xs) = \<Union>(set1_resource ` set xs)"
  "set1_resource (NonD x y) = set1_resource x \<union> set1_resource y"
  "set1_resource (Executable x y) = set1_resource x \<union> set1_resource y"
  "set1_resource (Repeatable x y) = set1_resource x \<union> set1_resource y"
  by (simp_all add: set1_resource of_resource_parallel)
lemma set2_resource_simps [simp]:
  "set2_resource Empty = {}"
  "set2_resource Anything = {}"
  "set2_resource (Res a) = {}"
  "set2_resource (Copyable b) = {b}"
  "set2_resource (Parallel xs) = \<Union>(set2_resource ` set xs)"
  "set2_resource (NonD x y) = set2_resource x \<union> set2_resource y"
  "set2_resource (Executable x y) = set2_resource x \<union> set2_resource y"
  "set2_resource (Repeatable x y) = set2_resource x \<union> set2_resource y"
  by (simp_all add: set2_resource of_resource_parallel)

subsection\<open>Replicated Resources\<close>

text\<open>Replicate a resource several times in a @{const Parallel}\<close>
fun nres_term :: "nat \<Rightarrow> ('a, 'b) res_term \<Rightarrow> ('a, 'b) res_term"
  where "nres_term n x = ResTerm.Parallel (replicate n x)"

lift_definition nresource :: "nat \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource"
  is nres_term by (simp add: res_term_equiv.parallel list_all2I)

text\<open>At the resource level this can be simplified just like at the term level\<close>
lemma nresource_simp:
  "nresource n x = Parallel (replicate n x)"
  by (transfer, simp)

text\<open>Parallel product of replications is a replication for the combined amount\<close>
lemma nresource_par:
  "nresource x a \<odot> nresource y a = nresource (x+y) a"
  by (simp add: nresource_simp replicate_add)

subsection\<open>Lifting Resource Refinement\<close>

lift_definition refine_resource
  :: "('a \<Rightarrow> ('x, 'y) resource) \<Rightarrow> ('b \<Rightarrow> 'y) \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('x, 'y) resource"
  is refine_res_term by (simp add: refine_res_term_eq)

text\<open>Refinement of lifted constructors can be simplified like the term version\<close>
lemma refine_resource_simps [simp]:
  "refine_resource f g Empty = Empty"
  "refine_resource f g Anything = Anything"
  "refine_resource f g (Res a) = f a"
  "refine_resource f g (Copyable b) = Copyable (g b)"
  "refine_resource f g (Parallel xs) = Parallel (map (refine_resource f g) xs)"
  "refine_resource f g (NonD x y) = NonD (refine_resource f g x) (refine_resource f g y)"
  "refine_resource f g (Executable x y) =
    Executable (refine_resource f g x) (refine_resource f g y)"
  "refine_resource f g (Repeatable x y) =
    Repeatable (refine_resource f g x) (refine_resource f g y)"
  by (transfer, simp)+

text\<open>Code for refinement performs the term-level refinement on the normalised representative\<close>
lemma refine_resource_code [code]:
  "refine_resource f g (abs_resource x) = abs_resource (refine_res_term (of_resource \<circ> f) g x)"
  by transfer (simp add: res_term_equiv_normal_rewr refine_res_term_eq)

text\<open>Refinement passes through resource product\<close>
lemma refine_resource_par:
  "refine_resource f g (x \<odot> y) = refine_resource f g x \<odot> refine_resource f g y"
  by (simp add: resource_par_def)

end