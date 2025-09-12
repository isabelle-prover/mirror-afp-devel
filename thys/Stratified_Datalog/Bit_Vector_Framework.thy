theory Bit_Vector_Framework imports Program_Graph begin

\<comment> \<open>We encode the Bit Vector Framework into Datalog. \<close>

section \<open>Bit-Vector Framework\<close>

subsection \<open>Definitions\<close>

datatype pred =
  the_may
  | the_must
  | the_kill
  | the_gen
  | the_init
  | the_anadom

datatype var =
  the_\<uu>

abbreviation "may == PosLit the_may"
abbreviation "must == PosLit the_must"
abbreviation NegLit_BV ("\<^bold>\<not>may") where
  "\<^bold>\<not>may \<equiv> NegLit the_may"
abbreviation "kill == PosLit the_kill"
abbreviation NegLit_kill ("\<^bold>\<not>kill") where
  "\<^bold>\<not>kill \<equiv> NegLit the_kill"
abbreviation "gen == PosLit the_gen"
abbreviation "init == PosLit the_init"
abbreviation "anadom == PosLit the_anadom"

fun s_BV :: "pred \<Rightarrow> nat" where 
  "s_BV the_kill = 0"
| "s_BV the_gen = 0"
| "s_BV the_init = 0"
| "s_BV the_anadom = 0"
| "s_BV the_may = 1"
| "s_BV the_must = 2"

datatype ('n,'a,'d) cst =
  is_Node: Node (the_Node: 'n)
  | is_Elem: Elem (the_Elem: 'd)
  | is_Action: Action (the_Action: "'a")

abbreviation may_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("may\<langle>_\<rangle> :- _ .") where
   "may\<langle>ids\<rangle> :- ls. \<equiv> Cls the_may ids ls"

abbreviation must_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("must\<langle>_\<rangle> :- _ .") where
  "must\<langle>ids\<rangle> :- ls. \<equiv> Cls the_must ids ls"

abbreviation init_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("init\<langle>_\<rangle> :- _ .") where 
  "init\<langle>ids\<rangle> :- ls. \<equiv> Cls the_init ids ls"

abbreviation anadom_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("anadom\<langle>_\<rangle> :- _ .") where 
  "anadom\<langle>ids\<rangle> :- ls. \<equiv> Cls the_anadom ids ls"

abbreviation kill_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("kill\<langle>_\<rangle> :- _ .") where 
  "kill\<langle>ids\<rangle> :- ls. \<equiv> Cls the_kill ids ls"

abbreviation gen_Cls 
  :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) rh list \<Rightarrow> 
      (pred, var, ('n,'v,'d) cst) clause" ("gen\<langle>_\<rangle> :- _ .") where 
  "gen\<langle>ids\<rangle> :- ls. \<equiv> Cls the_gen ids ls"

abbreviation BV_lh :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" 
  ("may\<langle>_\<rangle>.") where  
  "may\<langle>ids\<rangle>. \<equiv> (the_may, ids)"

abbreviation must_lh :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" 
  ("must\<langle>_\<rangle>.") where 
  "must\<langle>ids\<rangle>. \<equiv> (the_must, ids)"

abbreviation init_lh :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" 
  ("init\<langle>_\<rangle>.") where
  "init\<langle>ids\<rangle>. \<equiv> (the_init, ids)"

abbreviation dom_lh :: "(var, ('n,'v,'d) cst) id list \<Rightarrow> (pred, var, ('n,'v,'d) cst) lh" 
  ("anadom\<langle>_\<rangle>.") where
  "anadom\<langle>ids\<rangle>. \<equiv> (the_anadom, ids)"

abbreviation \<uu> :: "(var, 'a) id" where
  "\<uu> == Var the_\<uu>"

abbreviation Cst\<^sub>N :: "'n \<Rightarrow> (var, ('n, 'a, 'd) cst) id" where
  "Cst\<^sub>N q == Cst (Node q)"

abbreviation Cst\<^sub>E :: "'d \<Rightarrow> (var, ('n, 'a, 'd) cst) id" where
  "Cst\<^sub>E e == Cst (Elem e)"

abbreviation Cst\<^sub>A :: "'a \<Rightarrow> (var, ('n, 'a, 'd) cst) id" where
  "Cst\<^sub>A \<alpha> == Cst (Action \<alpha>)"

abbreviation the_Node\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> 'n" where
  "the_Node\<^sub>i\<^sub>d ident == the_Node (the_Cst ident)"

abbreviation the_Elem\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> 'd" where
  "the_Elem\<^sub>i\<^sub>d ident == the_Elem (the_Cst ident)"

abbreviation the_Action\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> 'a" where
  "the_Action\<^sub>i\<^sub>d ident == the_Action (the_Cst ident)"

abbreviation is_Elem\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> bool" where
  "is_Elem\<^sub>i\<^sub>d ident == is_Cst ident \<and> is_Elem (the_Cst ident)"

abbreviation is_Node\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> bool" where
  "is_Node\<^sub>i\<^sub>d ident == is_Cst ident \<and> is_Node (the_Cst ident)"

abbreviation is_Action\<^sub>i\<^sub>d :: "(var, ('n, 'a, 'd) cst) id \<Rightarrow> bool" where
  "is_Action\<^sub>i\<^sub>d ident == is_Cst ident \<and> is_Action (the_Cst ident)"


subsection \<open>Forward may-analysis\<close>       

locale analysis_BV_forward_may = finite_program_graph pg 
  for pg :: "('n::finite,'a) program_graph" +
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
  assumes "\<forall>e. gen_set e \<subseteq> analysis_dom"
  assumes "\<forall>e. kill_set e \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
      analysis_BV_forward_may_def rev_finite_subset)

interpretation LTS edges .

definition "S_hat" :: "('n,'a) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "d1 \<subseteq> d2"
  shows "S^\<^sub>E\<lbrakk>e\<rbrakk> d1 \<subseteq> S^\<^sub>E\<lbrakk>e\<rbrakk> d2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'a) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "S^\<^sub>E\<^sub>s\<lbrakk>e # \<pi>\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> (S^\<^sub>E\<lbrakk>e\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldl (\<lambda>a b. S^\<^sub>E\<lbrakk>b\<rbrakk> a) R \<pi>"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S^\<^sub>E\<^sub>s\<lbrakk>xs @ ys\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    using assms by auto
next
  case (snoc x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'a list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

lemma S_hat_path_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

fun ana_kill_edge_d :: "('n, 'a) edge \<Rightarrow> 'd \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_kill_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = kill\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_kill_edge :: "('n, 'a) edge \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause set" where
  "ana_kill_edge e = ana_kill_edge_d e ` (kill_set e)"

lemma kill_set_eq_kill_set_inter_analysis_dom: "kill_set e = kill_set e \<inter> analysis_dom"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
      analysis_BV_forward_may_def inf.orderE)

fun ana_gen_edge_d :: "('n, 'a) edge \<Rightarrow> 'd \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_gen_edge_d (q\<^sub>o, \<alpha>, q\<^sub>s) d = gen\<langle>[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]\<rangle> :- []."

definition ana_gen_edge :: "('n, 'a) edge \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause set" where
  "ana_gen_edge e = ana_gen_edge_d e ` (gen_set e)"

lemma gen_set_eq_gen_set_inter_analysis_dom: "gen_set e = gen_set e \<inter> analysis_dom"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
      analysis_BV_forward_may_def inf.orderE)

definition ana_init :: "'d \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_init d = init\<langle>[Cst\<^sub>E d]\<rangle> :- []."

definition ana_anadom :: "'d \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_anadom d = anadom\<langle>[Cst\<^sub>E d]\<rangle> :- []."

definition ana_entry_node :: "(pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_entry_node = may\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]]."

fun ana_edge :: "('n, 'a) edge \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause set" where
  "ana_edge (q\<^sub>o, \<alpha>, q\<^sub>s) =
     {
        may\<langle>[Cst\<^sub>N q\<^sub>s, \<uu>]\<rangle> :-
          [
            may[Cst\<^sub>N q\<^sub>o, \<uu>],
            \<^bold>\<not>kill[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, \<uu>]
          ].
        ,
        may\<langle>[Cst\<^sub>N q\<^sub>s, \<uu>]\<rangle> :- [gen[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, \<uu>]].
     }"

definition ana_must :: "'n \<Rightarrow> (pred, var, ('n, 'a, 'd) cst) clause" where
  "ana_must q = must\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q,\<uu>], anadom[\<uu>]]."

lemma ana_must_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s must\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q,\<uu>], anadom[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s must\<langle>[Cst\<^sub>N q,v]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q,v], anadom[v]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := v)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((must\<langle>[Cst\<^sub>N q,\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q,\<uu>], anadom[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_lemma by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

definition ana_pg_fw_may :: "(pred, var, ('n, 'a, 'd) cst) clause set" where
  "ana_pg_fw_may = \<Union>(ana_edge ` edges)
               \<union> ana_init ` d_init
               \<union> ana_anadom ` analysis_dom
               \<union> \<Union>(ana_kill_edge ` edges)
               \<union> \<Union>(ana_gen_edge ` edges)
               \<union> ana_must ` UNIV
               \<union> {ana_entry_node}"

lemma ana_entry_node_meta_var:
  assumes "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]]."
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N start,u]\<rangle> :- [init[u]]."
proof -
  define \<mu> where "\<mu> = Var(the_\<uu> := u)"
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s ((may\<langle>[Cst\<^sub>N start,\<uu>]\<rangle> :- [init[\<uu>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu>)"
    using assms substitution_lemma by blast
  then show ?thesis
    unfolding \<mu>_def by auto
qed

definition summarizes_fw_may :: "(pred, ('n, 'a, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_fw_may \<rho> \<longleftrightarrow> 
     (\<forall>\<pi> d. \<pi> \<in> path_with_word_from start \<longrightarrow> d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init \<longrightarrow> 
        \<rho> \<Turnstile>\<^sub>l\<^sub>h (may\<langle>[Cst\<^sub>N (LTS.end_of \<pi>), Cst\<^sub>E d]\<rangle>.))"

lemma S_hat_path_append:
  assumes "length qs = length w"                               
  shows "S^\<^sub>P\<lbrakk>(qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init =
    S^\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (S^\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
proof -
  have "S^\<^sub>P\<lbrakk> (qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init = 
        S^\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1, qn], w @ [\<alpha>]))\<rbrakk> d_init"
    unfolding S_hat_path_def by auto
  moreover
  have "S^\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1, qn], w @ [\<alpha>]))\<rbrakk> d_init =
        S^\<^sub>E\<^sub>s\<lbrakk>(transition_list (qs @ [qnminus1], w) @ [(qnminus1, \<alpha>, qn)])\<rbrakk> d_init"
    using transition_list_reversed_simp[of qs w] assms
    by auto
  moreover
  have 
    "... = S^\<^sub>E\<^sub>s\<lbrakk>[(qnminus1, \<alpha>, qn)]\<rbrakk> (S_hat_edge_list (transition_list (qs @ [qnminus1], w)) d_init)"
    using S_hat_edge_list_append[of "transition_list (qs @ [qnminus1], w)" "[(qnminus1, \<alpha>, qn)]" d_init]
    by auto
  moreover
  have "... = S^\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (S^\<^sub>P\<lbrakk> (qs @ [qnminus1], w)\<rbrakk> d_init)"
    unfolding S_hat_path_def by auto
  ultimately show ?thesis
    by blast
qed

lemma ana_pg_fw_may_stratified: "strat_wf s_BV ana_pg_fw_may"
  unfolding ana_pg_fw_may_def strat_wf_def ana_init_def ana_anadom_def ana_gen_edge_def 
    ana_must_def ana_entry_node_def  ana_kill_edge_def by auto

lemma finite_ana_edge_edgeset: "finite (\<Union> (ana_edge ` edges))"
proof -
  have "finite edges"
    using finite_program_graph_axioms finite_program_graph_def by blast
  moreover
  have "\<forall>e \<in> edges. finite (ana_edge e)"
    by force
  ultimately
  show ?thesis
    by blast
qed

lemma finite_ana_kill_edgeset: "finite (\<Union> (ana_kill_edge ` edges))"
proof -
  have "finite edges"
    using finite_program_graph_axioms finite_program_graph_def by blast
  moreover
  have "\<forall>e \<in> edges. finite (ana_kill_edge e)"
    by (metis ana_kill_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
        analysis_BV_forward_may_def finite_Int finite_imageI kill_set_eq_kill_set_inter_analysis_dom)
  ultimately
  show ?thesis
    by blast
qed

lemma finite_ana_gen_edgeset: "finite (\<Union> (ana_gen_edge ` edges))"
proof -
  have "finite edges"
    using finite_program_graph_axioms finite_program_graph_def by blast
  moreover
  have "\<forall>e \<in> edges. finite (ana_gen_edge e)"
    by (metis ana_gen_edge_def analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
        analysis_BV_forward_may_def finite_imageI rev_finite_subset)
  ultimately
  show ?thesis
    by blast
qed

lemma finite_ana_anadom_edgeset: "finite (ana_anadom ` analysis_dom)"
  by (meson analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def 
      analysis_BV_forward_may_def finite_imageI)

lemma ana_pg_fw_may_finite: "finite ana_pg_fw_may"
  unfolding ana_pg_fw_may_def using finite_ana_edge_edgeset finite_d_init
    finite_ana_anadom_edgeset finite_ana_kill_edgeset finite_ana_gen_edgeset by auto

fun vars_lh :: "('p,'x,'e) lh \<Rightarrow> 'x set" where
  "vars_lh (p,ids) = vars_ids ids"

lemma not_kill:
  fixes \<rho> :: "(pred, ('n, 'a, 'd) cst) pred_val"
  assumes "d \<notin> kill_set(q\<^sub>o, \<alpha>, q\<^sub>s)"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]"
proof -
  have "finite ana_pg_fw_may"
    by (simp add: ana_pg_fw_may_finite)
  moreover
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
    using assms(2) by blast
  moreover
  have "strat_wf s_BV ana_pg_fw_may"
    by (simp add: ana_pg_fw_may_stratified)
  moreover
  have "\<forall>c\<in>ana_pg_fw_may. 
           \<forall>\<sigma>'. 
             (the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d])) 
               \<longrightarrow> \<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
  proof (rule, rule, rule)
    fix c \<sigma>'
    assume c_dl: "c \<in> (ana_pg_fw_may)"
    assume "(the_lh c \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = ((the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]))"
    moreover
    from c_dl have "c \<in> (ana_pg_fw_may)"
      by auto
    ultimately
    show "\<not> \<lbrakk>the_rhs c\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
      unfolding ana_pg_fw_may_def ana_init_def ana_anadom_def ana_kill_edge_def 
        ana_gen_edge_def ana_must_def ana_entry_node_def using assms(1) by fastforce
  qed
  then have "\<not> (\<exists>c\<in>ana_pg_fw_may.
                  lh_consequence \<rho> c (the_kill, [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]))"
    using lh_consequence_def by metis
  ultimately
  show "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]"
    using solves_NegLit_least[of ana_pg_fw_may \<rho> s_BV "[Cst\<^sub>N q\<^sub>o, Cst\<^sub>A \<alpha>, Cst\<^sub>N q\<^sub>s, Cst\<^sub>E d]" the_kill] 
    by auto
qed

lemma S_hat_edge_list_subset_analysis_dom:
  assumes "d \<in> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d_init"
  shows "d \<in> analysis_dom"
  using assms
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by (metis S_hat_edge_list.simps(1) analysis_BV_forward_may.axioms(2) 
        analysis_BV_forward_may_axioms analysis_BV_forward_may_axioms_def subsetD)

next
  case (snoc e \<pi>)
  have "gen_set e \<inter> analysis_dom \<subseteq> analysis_dom"
    by fastforce
  then show ?case
    using S_hat_def gen_set_eq_gen_set_inter_analysis_dom snoc by auto
qed

lemma S_hat_path_subset_analysis_dom:
  assumes "d \<in> S^\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init"
  shows "d \<in> analysis_dom"
  using assms S_hat_path_def S_hat_edge_list_subset_analysis_dom by auto

lemma S_hat_path_last:
  assumes "length qs = length w"
  shows "S^\<^sub>P\<lbrakk>(qs @ [qnminus1, qn], w @ [\<alpha>])\<rbrakk> d_init =
         S^\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (S^\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
  using assms transition_list_reversed_simp unfolding S_hat_path_def by force

lemma gen_sound:
  assumes "d \<in> gen_set (q, \<alpha>, q')"
  assumes "(q, \<alpha>, q') \<in> edges"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] ."
proof -
  have "gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] . \<in> ana_pg_fw_may"
    using assms(1,2) unfolding ana_pg_fw_may_def ana_gen_edge_def by fastforce
  then show "?thesis"
    using \<open>gen\<langle>[Cst\<^sub>N q, Cst\<^sub>A \<alpha>, Cst\<^sub>N q', Cst\<^sub>E d]\<rangle> :- [] . \<in> ana_pg_fw_may\<close> assms(3) 
      least_solution_def solves_program_def by blast
qed

lemma sound_ana_pg_fw_may':
  assumes "(ss,w) \<in> path_with_word_from start"
  assumes "d \<in> S^\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (LTS.end_of (ss, w)), Cst\<^sub>E d]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_from_induct_reverse[OF assms(1)])
  case (1 s)
  have \<rho>_soultion: "\<rho> \<Turnstile>\<^sub>d\<^sub>l ana_pg_fw_may"
    using assms(3) unfolding least_solution_def by auto

  from 1(1) have start_end: "LTS.end_of ([s], []) = start"
    by (simp add: LTS.end_of_def LTS.start_of_def)

  from 1 have "S^\<^sub>P\<lbrakk>([s], [])\<rbrakk> d_init = d_init"
    unfolding S_hat_path_def by auto
  then have "d \<in> d_init"
    using 1(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s init\<langle>[Cst\<^sub>E d]\<rangle> :- [] ."
    using \<rho>_soultion unfolding ana_pg_fw_may_def ana_init_def solves_program_def by auto
  moreover
  have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N start, \<uu>]\<rangle> :- [init[\<uu>]]."
    by (metis Un_insert_right ana_entry_node_def analysis_BV_forward_may.ana_pg_fw_may_def 
        analysis_BV_forward_may_axioms \<rho>_soultion insertI1 solves_program_def)
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [init[Cst\<^sub>E d]]."
    using ana_entry_node_meta_var by blast
  ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N start, Cst\<^sub>E d]\<rangle> :- [] ."
    using prop_inf_only_from_cls_cls_to_cls by metis
  then show ?case
    using start_end solves_lh_lh by metis
next
  case (2 qs qnminus1 w \<alpha> qn)
  then have len: "length qs = length w"
    using path_with_word_lengths by blast
  
  have "d \<in> S^\<^sub>E\<lbrakk>(qnminus1, \<alpha>, qn)\<rbrakk> (S^\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init)"
    using "2.prems"(2) S_hat_path_last len by blast
  then have "d \<in> (S^\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init) - kill_set (qnminus1, \<alpha>, qn) \<or>
             d \<in> gen_set (qnminus1, \<alpha>, qn)"
    unfolding S_hat_def by simp
  then show ?case
  proof 
    assume dSnotkill: "d \<in> (S^\<^sub>P\<lbrakk>(qs @ [qnminus1], w)\<rbrakk> d_init) - kill_set (qnminus1, \<alpha>, qn)"
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>E d]\<rangle>."
      using 2(1,3,6) by (auto simp add: LTS.end_of_def)
    moreover
    from dSnotkill have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]"
      using not_kill[of d qnminus1 \<alpha> qn \<rho>] 2(6) by auto
    moreover
    have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [may [Cst\<^sub>N qnminus1, \<uu>],
                                      \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]]."
      using 2(6) "2.hyps"(2) 
      by (force simp add: ana_pg_fw_may_def solves_program_def least_solution_def)
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [may [Cst\<^sub>N qnminus1, Cst\<^sub>E d], 
                                               \<^bold>\<not>kill [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]]."
      using substitution_lemma[of \<rho> _ "\<lambda>u. Cst\<^sub>E d"] by force
    ultimately 
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      by (metis (no_types, lifting) Cons_eq_appendI prop_inf_last_from_cls_rh_to_cls modus_ponens_rh 
          self_append_conv2)
    then show "?case"
      by (auto simp add: LTS.end_of_def)
  next
    assume d_gen: "d \<in> gen_set (qnminus1, \<alpha>, qn)"

    have "\<forall>c\<in>ana_edge (qnminus1, \<alpha>, qn). \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      using 2(6) "2.hyps"(2) unfolding ana_pg_fw_may_def solves_program_def least_solution_def 
      by blast
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N qn, \<uu>]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, \<uu>]] ."
      by auto
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s may\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [gen [Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]] ."
      using substitution_lemma[of \<rho> _ "\<lambda>u. Cst\<^sub>E d" ]
      by force
    moreover
    have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s gen\<langle>[Cst\<^sub>N qnminus1, Cst\<^sub>A \<alpha>, Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle> :- [] ."
      using d_gen "2.hyps"(2) 2(6) gen_sound by auto
    ultimately
    have "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N qn, Cst\<^sub>E d]\<rangle>."
      by (meson modus_ponens_rh solves_lh_lh)
    then show ?case
      by (auto simp add: LTS.end_of_def)
  qed
qed

theorem sound_ana_pg_fw_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_may s_BV"
  shows "summarizes_fw_may \<rho>"
  using sound_ana_pg_fw_may' assms unfolding summarizes_fw_may_def by (cases pg) fastforce

end


subsection \<open>Backward may-analysis\<close>

locale analysis_BV_backward_may = finite_program_graph pg
  for pg :: "('n::finite,'a) program_graph" +
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite edges"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
  assumes "\<forall>e. gen_set e \<subseteq> analysis_dom"
  assumes "\<forall>e. kill_set e \<subseteq> analysis_dom"
begin



interpretation LTS edges .

definition S_hat :: "('n,'a) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> S^\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'a) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "S^\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = S^\<^sub>E\<lbrakk>e\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldr S_hat \<pi> R"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S^\<^sub>E\<^sub>s\<lbrakk>(xs @ ys)\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "d1 \<subseteq> d2"
  shows "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d1 \<subseteq> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d2"
proof(induction \<pi>)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'a list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>(transition_list \<pi>)\<rbrakk> R"

definition summarizes_bw_may :: "(pred, ('n, 'a, 'd) cst) pred_val \<Rightarrow> bool" where
  "summarizes_bw_may \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> path_with_word_to end \<longrightarrow> d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init \<longrightarrow> 
                             \<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (start_of \<pi>), Cst\<^sub>E d]\<rangle>.)"

lemma kill_subs_analysis_dom: "(kill_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may_axioms analysis_BV_backward_may_axioms_def 
      analysis_BV_backward_may_def)

lemma gen_subs_analysis_dom: "(gen_set (rev_edge e)) \<subseteq> analysis_dom"
  by (meson analysis_BV_backward_may.axioms(2) analysis_BV_backward_may_axioms 
      analysis_BV_backward_may_axioms_def)

interpretation fw_may: analysis_BV_forward_may 
  pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_may_def finite_pg_rev analysis_BV_backward_may_axioms 
    analysis_BV_backward_may_def
  by (metis (no_types, lifting) analysis_BV_backward_may_axioms_def 
      analysis_BV_forward_may_axioms_def finite_program_graph_def program_graph.edges_def)
 
abbreviation ana_pg_bw_may where
  "ana_pg_bw_may == fw_may.ana_pg_fw_may"

lemma rev_end_is_start:
  assumes "ss \<noteq> []"
  assumes "end_of (ss, w) = end"
  shows "start_of (rev ss, rev w) = fw_may.start"
  using assms
  unfolding end_of_def LTS.start_of_def fw_may.start_def pg_rev_def fw_may.start_def
  using hd_rev by (metis fw_may.start_def fst_conv pg_rev_def snd_conv) 

lemma S_hat_edge_list_forward_backward:
  "S^\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init = fw_may.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons e es)
  have "S^\<^sub>E\<^sub>s\<lbrakk>e # es\<rbrakk> d_init = S^\<^sub>E\<lbrakk>e\<rbrakk> S^\<^sub>E\<^sub>s\<lbrakk>es\<rbrakk> d_init"
    by simp
  also 
  have "... = fw_may.S_hat (rev_edge e) (foldr fw_may.S_hat (map rev_edge es) d_init)"
    unfolding foldr_conv_foldl fw_may.S_hat_edge_list_def2[symmetric]
    unfolding rev_edge_list_def[symmetric] fw_may.S_hat_def S_hat_def
    using Cons by simp
  also
  have "... = fw_may.S_hat_edge_list (rev_edge_list (e # es)) d_init"
    unfolding rev_edge_list_def fw_may.S_hat_edge_list_def2 foldl_conv_foldr
    by simp
  finally
  show ?case
    by metis
qed

lemma S_hat_path_forward_backward:
  assumes "(ss,w) \<in> path_with_word"
  shows "S^\<^sub>P\<lbrakk>(ss, w)\<rbrakk> d_init = fw_may.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fw_may.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_bw_may_forward_backward':
  assumes "(ss,w) \<in> path_with_word"
  assumes "end_of (ss,w) = end"
  assumes "d \<in> S^\<^sub>P\<lbrakk>(ss,w)\<rbrakk> d_init"
  assumes "fw_may.summarizes_fw_may \<rho>"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (start_of (ss, w)), Cst\<^sub>E d]\<rangle>."
proof -
  have rev_in_edges: "(rev ss, rev w) \<in> LTS.path_with_word fw_may.edges"
    using assms(1) rev_path_in_rev_pg[of ss w] fw_may.edges_def pg_rev_def by auto 
  moreover
  have "LTS.start_of (rev ss, rev w) = fw_may.start"
    using assms(1,2) rev_end_is_start by (metis LTS.path_with_word_not_empty)
  moreover
  have "d \<in> fw_may.S_hat_path (rev ss, rev w) d_init"
    using assms(3)
    using assms(1) S_hat_path_forward_backward by auto
  ultimately
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (LTS.end_of (rev ss, rev w)), Cst\<^sub>E d]\<rangle>."
    using assms(4) fw_may.summarizes_fw_may_def by blast
  then show ?thesis
    by (metis LTS.end_of_def LTS.start_of_def fst_conv hd_rev rev_rev_ident)
qed

lemma summarizes_dl_BV_forward_backward:
  assumes "fw_may.summarizes_fw_may \<rho>"
  shows "summarizes_bw_may \<rho>"
  unfolding summarizes_bw_may_def
proof(rule; rule ; rule; rule)
  fix \<pi> d
  assume "\<pi> \<in> {\<pi> \<in> path_with_word. LTS.end_of \<pi> = end}"
  moreover
  assume "d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
  ultimately
  show "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (LTS.start_of \<pi>), Cst\<^sub>E d]\<rangle>."
    using summarizes_bw_may_forward_backward'[of "fst \<pi>" "snd \<pi>" d \<rho>] using assms by auto
qed

theorem sound_ana_pg_bw_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_may s_BV"
  shows "summarizes_bw_may \<rho>"
  using assms fw_may.sound_ana_pg_fw_may[of \<rho>] summarizes_dl_BV_forward_backward by metis

end


subsection \<open>Forward must-analysis\<close>
                                            
locale analysis_BV_forward_must = finite_program_graph pg
  for pg :: "('n::finite,'a) program_graph" +
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_forward_must.axioms(2) analysis_BV_forward_must_axioms 
      analysis_BV_forward_must_axioms_def rev_finite_subset)

interpretation LTS edges .

definition S_hat :: "('n,'a) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> S^\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'a) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "S^\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> (S^\<^sub>E\<lbrakk>e\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldl (\<lambda>a b. S^\<^sub>E\<lbrakk>b\<rbrakk> a) R \<pi>"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S^\<^sub>E\<^sub>s\<lbrakk>(xs @ ys)\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    using assms by auto
next
  case (snoc x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'a list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

lemma S_hat_path_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R2"
  unfolding S_hat_path_def using assms S_hat_edge_list_mono by auto

definition summarizes_fw_must :: "(pred, ('n, 'a, 'd) cst) pred_val \<Rightarrow> bool" where
   "summarizes_fw_must \<rho> \<longleftrightarrow>
     (\<forall>q d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>. \<longrightarrow>
           (\<forall>\<pi>. \<pi> \<in> path_with_word \<longrightarrow>
                start_of \<pi> = start \<longrightarrow>
                end_of \<pi> = the_Node\<^sub>i\<^sub>d q \<longrightarrow>
                (the_Elem\<^sub>i\<^sub>d d) \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init))"

interpretation fw_may: analysis_BV_forward_may 
  pg analysis_dom "\<lambda>e. analysis_dom - (kill_set e)" "(\<lambda>e. analysis_dom - gen_set e)" 
  "analysis_dom - d_init"
  using analysis_BV_forward_may.intro[of pg] analysis_BV_forward_must_def[of pg] 
    analysis_BV_forward_may_axioms_def analysis_BV_forward_must_axioms 
    analysis_BV_forward_must_axioms_def by (metis Diff_subset)
  
abbreviation ana_pg_fw_must where
  "ana_pg_fw_must == fw_may.ana_pg_fw_may"

lemma opposite_lemma:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> fw_may.S_hat_edge_list \<pi> (analysis_dom - d_init)"
  shows "d \<in> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> d_init"
  using assms proof (induction \<pi> rule: List.rev_induct)
  case Nil
  then show ?case
    by auto
next
  case (snoc x xs)
  then show ?case
    unfolding fw_may.S_hat_edge_list_def2
    by (simp add: S_hat_def fw_may.S_hat_def)
qed

lemma opposite_lemma_path:
  assumes "d \<in> analysis_dom"
  assumes "\<not>d \<in> fw_may.S_hat_path \<pi> (analysis_dom - d_init)"
  shows "d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
  using S_hat_path_def fw_may.S_hat_path_def assms opposite_lemma by metis

lemma the_must_only_ana_must: "the_must \<notin> preds_dl (ana_pg_fw_must - (fw_may.ana_must ` UNIV))"
  unfolding fw_may.ana_pg_fw_may_def preds_dl_def preds_dl_def fw_may.ana_init_def
    preds_dl_def fw_may.ana_anadom_def preds_dl_def fw_may.ana_kill_edge_def preds_dl_def
    fw_may.ana_gen_edge_def fw_may.ana_entry_node_def by auto 

lemma agree_off_rh:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_rh rh"
  shows "\<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>rh\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
  using assms proof (cases rh)
  case (Eql a a')
  then show ?thesis
    by auto 
next
  case (Neql a a')
  then show ?thesis 
    by auto 
next
  case (PosLit p ids)
  then show ?thesis
    using assms by auto 
next
  case (NegLit p ids)
  then show ?thesis 
    using assms by auto 
qed

definition preds_rhs where
  "preds_rhs rhs = \<Union>(preds_rh ` set rhs)"

lemma preds_cls_preds_rhs: "preds_cls (Cls p ids rhs) = {p} \<union> preds_rhs rhs"
  by (simp add: preds_rhs_def)

lemma agree_off_rhs:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_rhs rhs"
  shows "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
  using assms agree_off_rh[of p' \<rho>' \<rho> _ \<sigma>] unfolding preds_rhs_def by auto

lemma agree_off_lh:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_lh lh"
  shows "\<lbrakk>lh\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>lh\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
proof (cases lh)
  case (Pair p ids)
  then show ?thesis
    using assms by auto
qed

lemma agree_off_cls:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_cls c"
  shows "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma> \<longleftrightarrow> \<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
proof (cases c)
  case (Cls p ids rhs)
  show ?thesis
  proof
    assume "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
      unfolding Cls meaning_cls.simps
    proof
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
      then have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
        using agree_off_rhs
        by (metis Cls assms(1) assms(2) clause.simps(6) insert_iff preds_rhs_def)
      then show"\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho> \<sigma>"
        using Cls \<open>\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>\<close> assms(1) assms(2) by auto
    qed
  next
    assume "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    show "\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho>' \<sigma>"
    unfolding Cls meaning_cls.simps
    proof
      assume "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho>' \<sigma>"
      then have "\<lbrakk>rhs\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
        using agree_off_rhs
        by (metis Cls assms(1) assms(2) clause.simps(6) insert_iff preds_rhs_def)
      then show"\<lbrakk>(p, ids)\<rbrakk>\<^sub>l\<^sub>h \<rho>' \<sigma>"
        using Cls \<open>\<lbrakk>c\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>\<close> assms(1) assms(2) by auto
    qed
  qed
qed

lemma agree_off_solves_cls:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_cls c"
  shows "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
proof (cases c)
  case (Cls p ids rhs)
  then show ?thesis
    by (metis (mono_tags, opaque_lifting) agree_off_cls assms solves_cls_def)
qed

lemma agree_off_dl:
  assumes "\<forall>p. p \<noteq> p' \<longrightarrow> \<rho>' p = \<rho> p"
  assumes "p' \<notin> preds_dl dl"
  shows "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl \<longleftrightarrow> \<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
proof 
  assume "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl"
  show "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume "c \<in> dl"
    have "p' \<notin> preds_cls c"
      using \<open>c \<in> dl\<close> assms(2) preds_dl_def by fastforce
    show "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      by (metis \<open>\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl\<close> \<open>c \<in> dl\<close> \<open>p' \<notin> preds_cls c\<close> agree_off_solves_cls assms(1) 
          solves_program_def)
  qed
next 
  assume "\<rho> \<Turnstile>\<^sub>d\<^sub>l dl"
  show "\<rho>' \<Turnstile>\<^sub>d\<^sub>l dl"
    unfolding solves_program_def
  proof
    fix c
    assume "c \<in> dl"
    have "p' \<notin> preds_cls c"
      using \<open>c \<in> dl\<close> assms(2) preds_dl_def by fastforce
    show "\<rho>' \<Turnstile>\<^sub>c\<^sub>l\<^sub>s c"
      by (metis \<open>\<rho> \<Turnstile>\<^sub>d\<^sub>l dl\<close> \<open>c \<in> dl\<close> \<open>p' \<notin> preds_cls c\<close> agree_off_solves_cls assms(1) 
          solves_program_def)
  qed
qed

lemma is_Cst_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d]\<rangle>."
  shows "is_Cst d"
proof (rule ccontr)
  assume "\<not> is_Cst d"
  then have du: "d = \<uu>"
    by (metis (full_types) id.disc(1) id.exhaust_disc id.expand var.exhaust)
  then have "\<lbrakk>init\<langle>[d]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<lambda>x. Action undefined)" 
    using assms
    by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined)]\<rangle>."
    using solves_lh_substv_lh_if_meaning_lh[of "init\<langle>[d]\<rangle>." \<rho> "(\<lambda>x. Action undefined)"] du by auto
  moreover
  have "is_Cst (Cst\<^sub>A undefined)"
    by auto
  moreover
  have "is_Cst (d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined))"
    by (metis id.disc(4) substv_id.elims)
  ultimately
  have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (init\<langle>[Cst\<^sub>A undefined]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV] du
    by (simp add: assms(1) fw_may.ana_pg_fw_may_finite fw_may.ana_pg_fw_may_stratified)
  then show False
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_init_def fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def by auto
qed

lemma is_Cst_if_anadom:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  shows "is_Cst d"
proof (rule ccontr)
  assume "\<not> is_Cst d"
  then have du: "d = \<uu>"
    by (metis (full_types) id.disc(1) id.exhaust_disc id.expand var.exhaust)
  then have "\<lbrakk>anadom\<langle>[d]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<lambda>x. Action undefined)" 
    using assms
    by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined)]\<rangle>."
    using solves_lh_substv_lh_if_meaning_lh[of "anadom\<langle>[d]\<rangle>." \<rho> "(\<lambda>x. Action undefined)"] du by auto
  moreover
  have "is_Cst (Cst\<^sub>A undefined)"
    by auto
  moreover
  have "is_Cst (d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined))"
    by (metis id.disc(4) substv_id.elims)
  ultimately
  have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (anadom\<langle>[Cst\<^sub>A undefined]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV] du
    by (simp add: assms(1) fw_may.ana_pg_fw_may_finite fw_may.ana_pg_fw_may_stratified)
  then show False
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_init_def fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def by auto
qed

lemma if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d]\<rangle>."
  shows "is_Elem\<^sub>i\<^sub>d d \<and> the_Elem\<^sub>i\<^sub>d d \<in> (analysis_dom - d_init)"
proof -
  have d_Cst: "is_Cst d"
    using assms(1) assms(2) is_Cst_if_init by blast

  from assms(1,2) d_Cst have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (init\<langle>[d]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV "[d]"] fw_may.ana_pg_fw_may_finite
      fw_may.ana_pg_fw_may_stratified by fastforce

  then obtain c where 
    "c \<in> ana_pg_fw_must"
    "lh_consequence \<rho> c (init\<langle>[d]\<rangle>.)"
    by auto
  from this have "\<exists>d' \<in> (analysis_dom - d_init). c = init\<langle>[Cst\<^sub>E d']\<rangle> :- []."
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def fw_may.ana_init_def by auto
  then obtain d' where "d' \<in> analysis_dom - d_init \<and> c = init\<langle>[Cst\<^sub>E d']\<rangle> :- []."
    by auto
  have "lh_consequence \<rho> (init\<langle>[Cst\<^sub>E d']\<rangle> :- [].) (init\<langle>[d]\<rangle>.)"
    using \<open>d' \<in> analysis_dom - d_init \<and> c = init\<langle>[Cst\<^sub>E d']\<rangle> :- [] .\<close>
      \<open>lh_consequence \<rho> c init\<langle>[d]\<rangle>.\<close> by fastforce
  then have "\<exists>\<sigma>. (init\<langle>[Cst\<^sub>E d']\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = init\<langle>[d]\<rangle>."
    unfolding lh_consequence_def by auto
  then obtain \<sigma> where \<sigma>_p:
    "(init\<langle>[Cst\<^sub>E d']\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = init\<langle>[d]\<rangle>."
    by auto
  then have "d = Cst\<^sub>E d'"
    by auto
  then have "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom - d_init \<and> is_Elem\<^sub>i\<^sub>d d"
    using \<open>d' \<in> analysis_dom - d_init \<and> c = init\<langle>[Cst\<^sub>E d']\<rangle> :- [] .\<close> by auto
  then show ?thesis
    by auto
qed

lemma if_anadom:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  shows "is_Elem\<^sub>i\<^sub>d d \<and> the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom"
proof -
  have d_Cst: "is_Cst d"
    using assms(1) assms(2) is_Cst_if_anadom by blast

  from assms(1,2) d_Cst have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (anadom\<langle>[d]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV "[d]"] fw_may.ana_pg_fw_may_finite
      fw_may.ana_pg_fw_may_stratified by fastforce
  then obtain c where 
    "c \<in> ana_pg_fw_must"
    "lh_consequence \<rho> c (anadom\<langle>[d]\<rangle>.)"
    by auto
  from this have "\<exists>d' \<in> analysis_dom. c = anadom\<langle>[Cst\<^sub>E d']\<rangle> :- []."
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def fw_may.ana_init_def by auto
  then obtain d' where "d' \<in> analysis_dom \<and> c = anadom\<langle>[Cst\<^sub>E d']\<rangle> :- []."
    by auto
  have "lh_consequence \<rho> (anadom\<langle>[Cst\<^sub>E d']\<rangle> :- [].) (anadom\<langle>[d]\<rangle>.)"
    using \<open>d' \<in> analysis_dom \<and> c = anadom\<langle>[Cst\<^sub>E d']\<rangle> :- [] .\<close>
      \<open>lh_consequence \<rho> c anadom\<langle>[d]\<rangle>.\<close> by fastforce
  then have "\<exists>\<sigma>. (anadom\<langle>[Cst\<^sub>E d']\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = anadom\<langle>[d]\<rangle>."
    unfolding lh_consequence_def by auto
  then obtain \<sigma> where \<sigma>_p:
    "(anadom\<langle>[Cst\<^sub>E d']\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = anadom\<langle>[d]\<rangle>."
    by auto
  then have "d = Cst\<^sub>E d'"
    by auto
  then have "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom \<and> is_Elem\<^sub>i\<^sub>d d"
    using \<open>d' \<in> analysis_dom \<and> c = anadom\<langle>[Cst\<^sub>E d']\<rangle> :- [] .\<close> by auto
  then show ?thesis
    by auto
qed

lemma is_elem_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst d]\<rangle>."
  shows "is_Elem d"
  by (metis if_init assms id.sel(2))

lemma not_init_node:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>N q]\<rangle>."
  by (metis if_init assms cst.collapse(2) cst.disc(1) cst.disc(2) id.sel(2))

lemma not_init_action:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>A q]\<rangle>."
  by (metis assms cst.collapse(2) cst.simps(9) id.sel(2) if_init)

lemma in_analysis_dom_if_init':
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[Cst\<^sub>E d]\<rangle>."
  shows "d \<in> analysis_dom"
  using assms if_init by force

lemma in_analysis_dom_if_init:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h init\<langle>[d]\<rangle>."
  shows "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom"
  using assms if_init by force

lemma not_anadom_node:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>N q]\<rangle>."
  by (metis assms cst.collapse(2) cst.disc(1) cst.disc(2) id.sel(2) if_anadom)

lemma not_anadom_action:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>A q]\<rangle>."
  by (metis assms cst.collapse(2) cst.simps(9) id.sel(2) if_anadom)

lemma in_analysis_dom_if_anadom':
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[Cst\<^sub>E d]\<rangle>."
  shows "d \<in> analysis_dom"
  using assms if_anadom by force

lemma in_analysis_dom_if_anadom:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  shows "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom \<and> is_Elem\<^sub>i\<^sub>d d"
  using assms if_anadom by force

lemma must_fst_id_is_Cst:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q,d]\<rangle>."
  shows "is_Cst q"
proof (rule ccontr)
  assume "\<not> is_Cst q"
  then have qu: "q = \<uu>"
    by (metis (full_types) id.disc(1) id.exhaust_disc id.expand var.exhaust)
  then have "\<lbrakk>must\<langle>[q,d]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<lambda>x. Action undefined)" 
    using assms
    by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[Cst\<^sub>A undefined, d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined)]\<rangle>."
    using solves_lh_substv_lh_if_meaning_lh[of "must\<langle>[q, d]\<rangle>." \<rho> "(\<lambda>x. Action undefined)"] qu by auto
  moreover
  have "is_Cst (Cst\<^sub>A undefined)"
    by auto
  moreover
  have "is_Cst (d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined))"
    by (metis id.disc(4) substv_id.elims)
  ultimately
  have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (must\<langle>[Cst\<^sub>A undefined, d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined)]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV "[Cst\<^sub>A undefined, d \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined)]"
        the_must]
    by (simp add: assms(1) fw_may.ana_pg_fw_may_finite fw_may.ana_pg_fw_may_stratified)
  then show False
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_init_def fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def by auto
qed

lemma must_snd_id_is_Cst:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q,d]\<rangle>."
  shows "is_Cst d"
proof (rule ccontr)
  assume "\<not> is_Cst d"
  then have du: "d = \<uu>"
    by (metis (full_types) id.disc(1) id.exhaust_disc id.expand var.exhaust)
  then have "\<lbrakk>must\<langle>[q,d]\<rangle>.\<rbrakk>\<^sub>l\<^sub>h \<rho> (\<lambda>x. Action undefined)" 
    using assms
    by auto
  then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>."
    using solves_lh_substv_lh_if_meaning_lh[of "must\<langle>[q, d]\<rangle>." \<rho> "(\<lambda>x. Action undefined)"] du by auto
  moreover
  have "is_Cst (Cst\<^sub>A undefined)"
    by auto
  moreover
  have "is_Cst (q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined))"
    by (metis id.disc(4) substv_id.elims)
  ultimately
  have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV "[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]"
        the_must]
    by (simp add: assms(1) fw_may.ana_pg_fw_may_finite fw_may.ana_pg_fw_may_stratified)
    then obtain c where c_p:
    "c \<in> ana_pg_fw_must"
    "lh_consequence \<rho> c (must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>.)"
    by auto
  from this have "\<exists>q'. c = must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]]."
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_init_def fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def by auto
  then obtain q' where "c = must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]]."
    by auto
  then have "lh_consequence \<rho> (must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]].) 
                              (must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>.)"
    using c_p(2) by auto
  then have "\<exists>\<sigma>'. (must\<langle>[Cst\<^sub>N q', \<uu>]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>.
                  \<and> \<lbrakk>[\<^bold>\<not>may[Cst\<^sub>N q', \<uu>], anadom[\<uu>]]\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
    unfolding lh_consequence_def using the_lh.simps clause.sel(3) by metis
  then obtain \<sigma>' where \<sigma>'_p:
    "(must\<langle>[Cst\<^sub>N q', \<uu>]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>') = must\<langle>[q \<cdot>\<^sub>v\<^sub>i\<^sub>d (\<lambda>x. Action undefined), Cst\<^sub>A undefined]\<rangle>."
    "\<lbrakk>[\<^bold>\<not>may[Cst\<^sub>N q', \<uu>], anadom[\<uu>]]\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>'"
    by metis
  then have "\<sigma>' the_\<uu> = Action undefined"
    by auto
  then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h anadom[(Cst\<^sub>A undefined)]"
    using \<sigma>'_p(2) solves_rh_substv_rh_if_meaning_rh  by auto
  then show False
    using assms(1) not_anadom_action by auto
qed

lemma if_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q,d]\<rangle>."
  shows 
    "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>may[q, d] \<and> \<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>. \<and> is_Node\<^sub>i\<^sub>d q \<and>is_Elem\<^sub>i\<^sub>d d \<and> the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom"
proof -
  have Csts: "is_Cst q" "is_Cst d"
    using must_fst_id_is_Cst must_snd_id_is_Cst using assms by auto

  from assms(1,2) Csts have "\<exists>c \<in> ana_pg_fw_must. lh_consequence \<rho> c (must\<langle>[q,d]\<rangle>.)"
    using solves_lh_least[of ana_pg_fw_must \<rho> s_BV "[q,d]" the_must] fw_may.ana_pg_fw_may_finite
      fw_may.ana_pg_fw_may_stratified by fastforce

  then obtain c where 
    "c \<in> ana_pg_fw_must"
    "lh_consequence \<rho> c (must\<langle>[q,d]\<rangle>.)"
    by auto
  from this have "\<exists>q'. c = must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]]."
    unfolding fw_may.ana_pg_fw_may_def fw_may.ana_entry_node_def lh_consequence_def
      fw_may.ana_init_def fw_may.ana_anadom_def fw_may.ana_kill_edge_def fw_may.ana_gen_edge_def
      fw_may.ana_must_def by auto
    
  then obtain q' where "c = must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]]."
    by auto
  have "lh_consequence \<rho> (must\<langle>[Cst\<^sub>N q',\<uu>]\<rangle> :- [\<^bold>\<not>may[Cst\<^sub>N q',\<uu>], anadom[\<uu>]].) (must\<langle>[q,d]\<rangle>.)"
    using \<open>c = must\<langle>[Cst\<^sub>N q', \<uu>]\<rangle> :- [\<^bold>\<not>may [Cst\<^sub>N q', \<uu>], anadom [\<uu>]] .\<close> 
      \<open>lh_consequence \<rho> c must\<langle>[q, d]\<rangle>.\<close> by fastforce
  then have "\<exists>\<sigma>. (must\<langle>[Cst\<^sub>N q', \<uu>]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = must\<langle>[q, d]\<rangle>. \<and> \<lbrakk>[\<^bold>\<not>may[Cst\<^sub>N q', \<uu>], anadom[\<uu>]]\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
    unfolding lh_consequence_def by auto
  then obtain \<sigma> where \<sigma>_p:
    "(must\<langle>[Cst\<^sub>N q', \<uu>]\<rangle>. \<cdot>\<^sub>v\<^sub>l\<^sub>h \<sigma>) = must\<langle>[q, d]\<rangle>."
    "\<lbrakk>[\<^bold>\<not>may[Cst\<^sub>N q', \<uu>], anadom[\<uu>]]\<rbrakk>\<^sub>r\<^sub>h\<^sub>s \<rho> \<sigma>"
    by auto
  then have "q = Cst\<^sub>N q'"
    by auto
  from \<sigma>_p have "\<exists>d'. \<sigma> the_\<uu> = d' \<and> d = Cst d'"
    by auto
  then obtain d' where 
    "\<sigma> the_\<uu> = d'"
    "d = Cst d'"
    by auto
  from \<sigma>_p(2) have "\<lbrakk>\<^bold>\<not>may[Cst\<^sub>N q', \<uu>]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    by auto
  then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>may[q, d]"
    using solves_rh_substv_rh_if_meaning_rh \<open>\<sigma> the_\<uu> = d'\<close> \<open>d = Cst d'\<close> \<open>q = Cst\<^sub>N q'\<close> by force 
  have "\<lbrakk>anadom[\<uu>]\<rbrakk>\<^sub>r\<^sub>h \<rho> \<sigma>"
    using \<sigma>_p(2) by auto
  then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h anadom[d]"
    using solves_rh_substv_rh_if_meaning_rh \<open>\<sigma> the_\<uu> = d'\<close> \<open>d = Cst d'\<close> \<open>q = Cst\<^sub>N q'\<close> by force
  then have "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom \<and> is_Elem\<^sub>i\<^sub>d d"
    using in_analysis_dom_if_anadom[of \<rho> d] assms by fastforce
  show ?thesis 
    using \<open>\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>may [q, d]\<close> \<open>\<rho> \<Turnstile>\<^sub>r\<^sub>h anadom [d]\<close> \<open>q = Cst\<^sub>N q'\<close>
      \<open>the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom \<and> is_Elem\<^sub>i\<^sub>d d\<close> by auto
qed

lemma not_must_and_may:
  assumes "[Node q, Elem d] \<in> \<rho> the_must"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "[Node q, Elem d] \<in> \<rho> the_may"                  
  shows False
proof -
  have "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
    using assms(1) by auto
  then have "\<rho> \<Turnstile>\<^sub>r\<^sub>h \<^bold>\<not>may [Cst\<^sub>N q, Cst\<^sub>E d]"
    using if_must assms(2) by metis
  then show False
    using assms(3) by auto
qed

lemma not_solves_must_and_may:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N q, Cst\<^sub>E d]\<rangle>."
  shows "False"
proof -
  have "[Node q, Elem d] \<in> \<rho> the_must"
    using assms(2)
    unfolding solves_lh.simps
    unfolding meaning_lh.simps
    by auto
  moreover
  have "[Node q, Elem d] \<in> \<rho> the_may"
    using assms(3)
    unfolding solves_lh.simps
    unfolding meaning_lh.simps
    by auto
  ultimately
  show "False"
    using not_must_and_may[of q d \<rho>] assms(1) by auto
qed

lemma anadom_if_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h anadom\<langle>[d]\<rangle>."
  using assms(1) assms(2) if_must by blast

lemma not_must_action:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[Cst\<^sub>A q,d]\<rangle>."
  by (metis assms cst.disc(3) id.sel(2) if_must)

lemma is_encode_elem_if_must_right_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  shows "\<exists>d'. d = Cst\<^sub>E d'"
  by (metis assms(1) assms(2) cst.collapse(2) id.collapse(2) if_must)

lemma not_must_element: 
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "\<not>\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[Cst\<^sub>E q,d]\<rangle>."
  by (metis assms cst.disc(2) id.sel(2) if_must)

lemma is_encode_node_if_must_left_arg:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  shows "\<exists>q'. q = Cst\<^sub>N q'"
  by (metis assms(1) assms(2) cst.collapse(1) id.collapse(2) if_must)

lemma in_analysis_dom_if_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  shows "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom"
  using assms(1) assms(2) if_must by blast

lemma sound_ana_pg_fw_must':
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  assumes "\<pi> \<in> path_with_word_from_to start (the_Node\<^sub>i\<^sub>d q)"
  shows "the_Elem\<^sub>i\<^sub>d d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
proof -
  have d_ana: "the_Elem\<^sub>i\<^sub>d d \<in> analysis_dom"
    using assms(1) assms(2) in_analysis_dom_if_must by auto

  have \<pi>e: "q = Cst\<^sub>N (end_of \<pi>)"
    using assms(1) assms(2) assms(3) is_encode_node_if_must_left_arg by fastforce

  have d_encdec: "d = Cst\<^sub>E (the_Elem\<^sub>i\<^sub>d d)"
    by (metis cst.sel(2) assms(1) assms(2) id.sel(2) is_encode_elem_if_must_right_arg)

  have not_may: "\<not> \<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (end_of \<pi>), d]\<rangle>."
    using not_solves_must_and_may[OF assms(1), of "(end_of \<pi>)" "the_Elem\<^sub>i\<^sub>d d"] assms(2) \<pi>e d_encdec 
    by force
  have "\<not>the_Elem\<^sub>i\<^sub>d d \<in> fw_may.S_hat_path \<pi> (analysis_dom - d_init)"
    using fw_may.sound_ana_pg_fw_may assms(1)
    unfolding fw_may.summarizes_fw_may_def
     edges_def start_def assms(2) edges_def start_def
    using assms(3)  d_encdec edges_def not_may start_def by (metis (mono_tags) mem_Collect_eq) 
  then show "the_Elem\<^sub>i\<^sub>d d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
    using opposite_lemma_path
    using assms(1)
    using d_ana by blast 
qed

theorem sound_ana_pg_fw_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_fw_must s_BV"
  shows "summarizes_fw_must \<rho>"
  using assms unfolding summarizes_fw_must_def using sound_ana_pg_fw_must' by auto

end


subsection \<open>Backward must-analysis\<close>

locale analysis_BV_backward_must = finite_program_graph pg
  for pg :: "('n::finite,'a) program_graph" +
  fixes analysis_dom :: "'d set"
  fixes kill_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes gen_set :: "('n,'a) edge \<Rightarrow> 'd set"
  fixes d_init :: "'d set"
  assumes "finite analysis_dom"
  assumes "d_init \<subseteq> analysis_dom"
begin

lemma finite_d_init: "finite d_init"
  by (meson analysis_BV_backward_must.axioms(2) analysis_BV_backward_must_axioms 
      analysis_BV_backward_must_axioms_def rev_finite_subset)

interpretation LTS edges .

definition S_hat :: "('n,'a) edge \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<lbrakk>e\<rbrakk> R = (R - kill_set e) \<union> gen_set e"

lemma S_hat_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<lbrakk>e\<rbrakk> R1 \<subseteq> S^\<^sub>E\<lbrakk>e\<rbrakk> R2"
  using assms unfolding S_hat_def by auto

fun S_hat_edge_list :: "('n,'a) edge list \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>E\<^sub>s\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>E\<^sub>s\<lbrakk>[]\<rbrakk> R = R" |
  "S^\<^sub>E\<^sub>s\<lbrakk>(e # \<pi>)\<rbrakk> R = S^\<^sub>E\<lbrakk>e\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R)"

lemma S_hat_edge_list_def2:
  "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R = foldr S_hat \<pi> R"
proof (induction \<pi> arbitrary: R)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<pi>)
  then show ?case
    by simp
qed

lemma S_hat_edge_list_append[simp]:
  "S^\<^sub>E\<^sub>s\<lbrakk>xs @ ys\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>xs\<rbrakk> (S^\<^sub>E\<^sub>s\<lbrakk>ys\<rbrakk> R)"
  unfolding S_hat_edge_list_def2 foldl_append by auto

lemma S_hat_edge_list_mono:
  assumes "R1 \<subseteq> R2"
  shows "S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R1 \<subseteq> S^\<^sub>E\<^sub>s\<lbrakk>\<pi>\<rbrakk> R2"
proof(induction \<pi>)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms by (simp add: S_hat_mono)
qed

definition S_hat_path :: "('n list \<times> 'a list) \<Rightarrow> 'd set \<Rightarrow> 'd set" ("S^\<^sub>P\<lbrakk>_\<rbrakk> _") where
  "S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> R = S^\<^sub>E\<^sub>s\<lbrakk>LTS.transition_list \<pi>\<rbrakk> R"

definition summarizes_bw_must :: "(pred, ('n, 'v, 'd) cst) pred_val \<Rightarrow> bool" where
   "summarizes_bw_must \<rho> \<longleftrightarrow>
     (\<forall>q d.
         \<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>. \<longrightarrow>
          (\<forall>\<pi>. \<pi> \<in> path_with_word_from_to (the_Node\<^sub>i\<^sub>d q) end \<longrightarrow> the_Elem\<^sub>i\<^sub>d d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init))"

interpretation fw_must: analysis_BV_forward_must 
  pg_rev analysis_dom "\<lambda>e. (kill_set (rev_edge e))" "(\<lambda>e. gen_set (rev_edge e))" d_init
  using analysis_BV_forward_must_def finite_pg_rev analysis_BV_backward_must_axioms
    analysis_BV_backward_must_def analysis_BV_backward_must_axioms_def
    analysis_BV_forward_must_axioms.intro finite_program_graph.intro
    program_graph.edges_def by metis


abbreviation ana_pg_bw_must where
  "ana_pg_bw_must == fw_must.ana_pg_fw_must"

lemma rev_end_is_start:
  assumes "ss \<noteq> []"
  assumes "end_of (ss, w) = end"
  shows "start_of (rev ss, rev w) = fw_must.start"
  using assms
  unfolding LTS.end_of_def LTS.start_of_def fw_must.start_def pg_rev_def fw_must.start_def
  using hd_rev by (metis fw_must.start_def fst_conv pg_rev_def snd_conv) 

lemma S_hat_edge_list_forward_backward:
  "S^\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init = fw_must.S_hat_edge_list (rev_edge_list ss) d_init"
proof (induction ss)
  case Nil
  then show ?case
    unfolding rev_edge_list_def by auto
next
  case (Cons a ss)
  have "S^\<^sub>E\<^sub>s\<lbrakk>a # ss\<rbrakk> d_init = S^\<^sub>E\<lbrakk>a\<rbrakk> S^\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init"
    by simp
  also
  have "... = (((S^\<^sub>E\<^sub>s\<lbrakk>ss\<rbrakk> d_init) - kill_set a) \<union> gen_set a)"
    using S_hat_def by auto
  also
  have "... = fw_must.S_hat_edge_list (rev_edge_list ss) d_init - kill_set a \<union> gen_set a"
    using Cons by auto
  also
  have "... = fw_must.S_hat_edge_list (rev_edge_list ss) d_init - kill_set (rev_edge (rev_edge a)) 
                \<union> gen_set (rev_edge (rev_edge a))"
    by simp
  also
  have "... = fw_must.S_hat (rev_edge a) (fw_must.S_hat_edge_list (rev_edge_list ss) d_init)"
    using fw_must.S_hat_def by auto
  also
  have "... = fw_must.S_hat (rev_edge a) (fw_must.S_hat_edge_list (rev (map rev_edge ss)) d_init)"
    by (simp add: rev_edge_list_def)
  also
  have "... = fw_must.S_hat (rev_edge a) (foldl (\<lambda>x y. fw_must.S_hat y x) d_init (rev (map rev_edge ss)))"
    using fw_must.S_hat_edge_list_def2 by force
  also
  have "... = fw_must.S_hat (rev_edge a) (foldr fw_must.S_hat (map rev_edge ss) d_init)"
    by (simp add: foldr_conv_foldl)
  also
  have "... = foldr fw_must.S_hat (rev (rev (map rev_edge (a # ss)))) d_init"
    by force
  also
  have "... = foldl (\<lambda>a b. fw_must.S_hat b a) d_init (rev (map rev_edge (a # ss)))"
    by (simp add: foldr_conv_foldl)
  also
  have "... = fw_must.S_hat_edge_list (rev (map rev_edge (a # ss))) d_init"
    using fw_must.S_hat_edge_list_def2 by auto
  also
  have "... = fw_must.S_hat_edge_list (rev_edge_list (a # ss)) d_init"
    by (simp add: rev_edge_list_def)
  finally
  show ?case
    by auto
qed

lemma S_hat_path_forward_backward:
  assumes "(ss,w) \<in> path_with_word"
  shows "S^\<^sub>P\<lbrakk>(ss, w)\<rbrakk> d_init = fw_must.S_hat_path (rev ss, rev w) d_init"
  using S_hat_edge_list_forward_backward unfolding S_hat_path_def fw_must.S_hat_path_def
  by (metis transition_list_rev_edge_list assms)

lemma summarizes_fw_must_forward_backward':
  assumes "fw_must.summarizes_fw_must \<rho>"
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>h must\<langle>[q, d]\<rangle>."
  assumes "\<pi> \<in> path_with_word_from_to (the_Node\<^sub>i\<^sub>d q) end"
  shows "the_Elem\<^sub>i\<^sub>d d \<in> S^\<^sub>P\<lbrakk>\<pi>\<rbrakk> d_init"
proof -
  define rev_\<pi> where "rev_\<pi> = (rev (fst \<pi>), rev (snd \<pi>))"
  have rev_\<pi>_path: "rev_\<pi> \<in> LTS.path_with_word fw_must.edges"
    using rev_\<pi>_def assms(3) fw_must.edges_def pg_rev_def rev_path_in_rev_pg
    by (metis (no_types, lifting) fst_conv mem_Collect_eq  prod.collapse)
  have rev_\<pi>_start: "start_of rev_\<pi> = fw_must.start"
    using  rev_\<pi>_def analysis_BV_backward_must_axioms
      assms(3) pg_rev_def start_of_def edges_def end_of_def hd_rev  
      by (metis (mono_tags, lifting) fw_must.start_def mem_Collect_eq prod.sel)
  have rev_\<pi>_start_end: "end_of rev_\<pi> = the_Node\<^sub>i\<^sub>d q"
    using assms(3) rev_\<pi>_def end_of_def last_rev start_of_def
    by (metis (mono_tags, lifting) mem_Collect_eq prod.sel(1))
  have "the_Elem\<^sub>i\<^sub>d d \<in> fw_must.S_hat_path (rev (fst \<pi>), rev (snd \<pi>)) d_init"
    using rev_\<pi>_def rev_\<pi>_path rev_\<pi>_start_end rev_\<pi>_start assms(1) assms(2) 
      fw_must.summarizes_fw_must_def by blast
  then show ?thesis
    by (metis (no_types, lifting) S_hat_path_forward_backward assms(3) mem_Collect_eq prod.collapse)
qed
 

lemma summarizes_bw_must_forward_backward:
  assumes "fw_must.summarizes_fw_must \<rho>"
  shows "summarizes_bw_must \<rho>"
  unfolding summarizes_bw_must_def
  using assms summarizes_fw_must_forward_backward' by auto

theorem sound_ana_pg_bw_must:
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t ana_pg_bw_must s_BV"
  shows "summarizes_bw_must \<rho>"
  using assms fw_must.sound_ana_pg_fw_must[of \<rho>] summarizes_bw_must_forward_backward by metis

end

end
