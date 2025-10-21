theory Reaching_Definitions imports Bit_Vector_Framework begin

\<comment> \<open>We encode the Reaching Definitions analysis into Datalog. First we define the analysis, then
    we encode the analysis directly into Datalog and prove the encoding correct. Hereafter we
    encode it into Datalog again, but this time using our Bit-Vector Framework locale. We also prove 
    this encoding correct. This latter encoding is described in our SAC 2024 paper. \<close>


section \<open>Reaching Definitions\<close>

type_synonym ('n,'v) def = "'v * 'n option * 'n"

type_synonym ('n,'v) analysis_assignment = "'n \<Rightarrow> ('n,'v) def set"


subsection \<open>What is defined on a path\<close>

fun def_action :: "'v action \<Rightarrow> 'v set" where
  "def_action (x ::= a) = {x}"
| "def_action (Bool b) = {}"
| "def_action Skip = {}"

abbreviation def_edge :: "('n,'v action) edge \<Rightarrow> 'v set" where
  "def_edge == \<lambda>(q1, \<alpha>, q2). def_action \<alpha>"

definition def_of :: "'v \<Rightarrow> ('n,'v action) edge \<Rightarrow> ('n,'v) def" where
  "def_of == (\<lambda>x (q1, \<alpha>, q2). (x, Some q1, q2))"

definition def_var :: "('n,'v action) edge list \<Rightarrow> 'v \<Rightarrow> 'n \<Rightarrow> ('n,'v) def" where
  "def_var \<pi> x start = (if (\<exists>e \<in> set \<pi>. x \<in> def_edge e)
                        then (def_of x (last (filter (\<lambda>e. x \<in> def_edge e) \<pi>)))
                        else (x, None, start))"

definition def_path :: "('n list \<times> 'v action list) \<Rightarrow> 'n \<Rightarrow> ('n,'v) def set" where
  "def_path \<pi> start = ((\<lambda>x. def_var (LTS.transition_list \<pi>) x start) ` UNIV)"


subsection \<open>Reaching Definitions in Datalog\<close>

\<comment> \<open>Direct encoding of Reaching Definitions into Datalog.\<close>

datatype ('n,'v) RD_elem =
  RD_Node 'n
  | RD_Var 'v
  | Questionmark

datatype RD_var =
  the_\<u>
  | the_\<v>
  | the_\<w>

datatype RD_pred =
  the_RD
  | the_VAR

abbreviation Cst\<^sub>R\<^sub>D\<^sub>N :: "'n \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>N q == Cst (RD_Node q)"

fun Cst\<^sub>R\<^sub>D\<^sub>N_Q :: "'n option \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>N_Q (Some q) = Cst (RD_Node q)"
| "Cst\<^sub>R\<^sub>D\<^sub>N_Q None = Cst Questionmark"

abbreviation Cst\<^sub>R\<^sub>D\<^sub>V :: "'v \<Rightarrow> (RD_var, ('n, 'v) RD_elem) id" where
  "Cst\<^sub>R\<^sub>D\<^sub>V v == Cst (RD_Var v)"

abbreviation RD_Cls :: "(RD_var, ('n, 'v) RD_elem) id list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) rh list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("RD\<langle>_\<rangle> :- _ .") where 
  "RD\<langle>args\<rangle> :- ls. \<equiv> Cls the_RD args ls"

abbreviation VAR_Cls :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) clause" ("VAR\<langle>_\<rangle> :-.") where
  "VAR\<langle>x\<rangle> :-. == Cls the_VAR [Cst\<^sub>R\<^sub>D\<^sub>V x] []"

abbreviation RD_lh :: "(RD_var, ('n, 'v) RD_elem) id list \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) lh" ("RD\<langle>_\<rangle>.") where 
  "RD\<langle>args\<rangle>. \<equiv> (the_RD, args)"

abbreviation VAR_lh :: "'v \<Rightarrow> (RD_pred, RD_var, ('n, 'v) RD_elem) lh" ("VAR\<langle>_\<rangle>.") where 
  "VAR\<langle>x\<rangle>. \<equiv> (the_VAR, [Cst\<^sub>R\<^sub>D\<^sub>V x])"


abbreviation "RD == PosLit the_RD"
abbreviation "VAR == PosLit the_VAR"

abbreviation \<u> :: "(RD_var, 'aa) id" where
  "\<u> == Var the_\<u>"

abbreviation \<v> :: "(RD_var, 'aa) id" where
  "\<v> == Var the_\<v>"

abbreviation \<w> :: "(RD_var, 'aa) id" where
  "\<w> == Var the_\<w>"

fun ana_edge :: "('n, 'v action) edge \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_edge (q\<^sub>o, x ::= a, q\<^sub>s) =
     {
        RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V x)
          ].
        ,
        RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s]\<rangle> :- [].
     }"
| "ana_edge (q\<^sub>o, Bool b, q\<^sub>s) =
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"
| "ana_edge (q\<^sub>o, Skip, q\<^sub>s) =
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>s, \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N q\<^sub>o, \<u>, \<v>, \<w>]
         ].
     }"

definition ana_entry_node :: "'n \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_entry_node start = 
     {
       RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :-
         [
           VAR[\<u>]
         ].
     }"


fun ana_RD :: "('n, 'v action) program_graph \<Rightarrow> (RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "ana_RD (es,start,end) = \<Union>(ana_edge ` es) \<union> ana_entry_node start"

definition var_contraints :: "(RD_pred, RD_var, ('n,'v) RD_elem) clause set" where
  "var_contraints = VAR_Cls ` UNIV"

type_synonym ('n,'v) quadruple = "'n *'v * 'n option * 'n"

fun summarizes_RD :: "(RD_pred,('n,'v) RD_elem) pred_val \<Rightarrow> ('n,'v action) program_graph \<Rightarrow> bool" where
  "summarizes_RD \<rho> (es, start, end) =
    (\<forall>\<pi> x q1 q2.
       \<pi> \<in> LTS.path_with_word_from es start \<longrightarrow>
       (x, q1, q2) \<in> def_path \<pi> start \<longrightarrow> 
       \<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.end_of \<pi>), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>.)"

lemma def_var_x: "fst (def_var ts x start) = x"
  unfolding def_var_def by (simp add: case_prod_beta def_of_def)

lemma last_def_transition:
  assumes "length ss = length w"
  assumes "x \<in> def_action \<alpha>"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [\<alpha>]) start"
  shows "Some s = q1 \<and> s' = q2"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, \<alpha>, s')]) y start"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  show ?thesis
  proof (cases "y = x")
    case True
    then show ?thesis 
      using assms y_p unfolding def_var_def def_of_def by auto
  next
    case False
    then show ?thesis
      by (metis y_p def_var_x fst_conv)
  qed
qed

lemma not_last_def_transition:
  assumes "length ss = length w"
  assumes "x \<notin> def_action \<alpha>"
  assumes "(x, q1, q2) \<in> def_path (ss @ [s, s'], w @ [\<alpha>]) start"
  shows "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
proof -
  obtain y where y_p: "(x, q1, q2) = def_var (transition_list (ss @ [s], w) @ [(s, \<alpha>, s')]) y start"
    by (metis (no_types, lifting) assms(1) assms(3) def_path_def imageE transition_list_reversed_simp)
  have "(x, q1, q2) \<in> range (\<lambda>x. def_var (transition_list (ss @ [s], w)) x start)"
  proof (cases "y = x")
    case True
    then show ?thesis 
      using assms y_p unfolding def_var_def def_of_def by auto
  next
    case False
    then show ?thesis
      by (metis y_p def_var_x fst_conv)
  qed
  then show ?thesis
    by (simp add: def_path_def)
qed

theorem RD_sound': 
  assumes "(ss,w) \<in> LTS.path_with_word_from es start"
  assumes "(x,q1,q2) \<in> def_path (ss,w) start"
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
  shows "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.end_of (ss, w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
  using assms 
proof (induction rule: LTS.path_with_word_from_induct_reverse[OF assms(1)])
  case (1 s)
  have "VAR\<langle>x\<rangle> :-. \<in> var_contraints"
    unfolding var_contraints_def by auto
  from assms(3) this have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s VAR\<langle>x\<rangle> :-."
    unfolding solves_program_def by auto  
  then have "\<forall>y. \<lbrakk>(VAR\<langle>x\<rangle> :-.)\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> y"
    unfolding solves_cls_def by auto
  then have x_sat: "[RD_Var x] \<in> \<rho> the_VAR"
    by auto

  have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :-
         [
           VAR[\<u>]
         ]. \<in> ana_RD (es, start, end)"
    by (simp add: ana_entry_node_def)
  then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] ."
    using assms(3) unfolding solves_program_def by auto 
  then have "\<forall>\<sigma>. \<lbrakk>RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> \<sigma>"
    unfolding solves_cls_def by metis
  then have "\<lbrakk>RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N start, \<u>, Cst Questionmark, Cst\<^sub>R\<^sub>D\<^sub>N start]\<rangle> :- [VAR [\<u>]] .\<rbrakk>\<^sub>c\<^sub>l\<^sub>s \<rho> (\<lambda>v. RD_Var x)"
    by presburger
  then have "[RD_Var x] \<in> \<rho> the_VAR \<longrightarrow> [RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD"
    by simp
  then have "[RD_Node start, RD_Var x, Questionmark, RD_Node start] \<in> \<rho> the_RD"
    using x_sat by auto

  from this 1 show ?case
    unfolding LTS.LTS.end_of_def def_path_def def_var_def LTS.start_of_def by auto
next
  case (2 ss s w \<alpha> s')
  from 2(1) have len: "length ss = length w"
    using LTS.path_with_word_length by force
  show ?case 
  proof(cases "x \<in> def_action \<alpha>")
    case True
    then have sq: "Some s = q1 \<and> s' = q2" using 2(5)
      using last_def_transition[of ss w x \<alpha> q1 q2 s s'] len by auto
    from True have "\<exists>e. (s,x ::= e,s') \<in> es"
      using "2.hyps"(2) by (cases \<alpha>) auto
    then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- []. \<in> ana_RD (es, start, end)"
      using True ana_RD.simps sq by fastforce
    then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
      using 2(6) unfolding solves_program_def by auto
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N q2, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
      using solves_lh_lh by metis 
    then show ?thesis
      by (simp add: LTS.end_of_def sq)
  next
    case False
    then have x_is_def: "(x, q1, q2) \<in> def_path (ss @ [s], w) start" using 2(5)
      using not_last_def_transition len by force
    then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.end_of (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
    proof -
      have "(ss @ [s], w) \<in> LTS.path_with_word es"
        using 2(1) by auto
      moreover
      have "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD (es, start, end))"
        using 2(6) by auto
      moreover
      have "LTS.start_of (ss @ [s], w) = start"
        using "2.hyps"(1) by auto
      moreover
      have "(x, q1, q2) \<in> def_path (ss @ [s], w) start"
        using x_is_def by auto
      ultimately
      show "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N (LTS.end_of (ss @ [s], w)), Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using 2(3) by auto
    qed
    then have ind: "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
      by (simp add: LTS.end_of_def)
    define \<mu> where "\<mu> = undefined(the_\<u> := Cst\<^sub>R\<^sub>D\<^sub>V x, the_\<v> := Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, the_\<w> := Cst\<^sub>R\<^sub>D\<^sub>N q2)"
    show ?thesis
    proof (cases \<alpha>)
      case (Asg y e)
      have xy: "x \<noteq> y"
        using False Asg by auto
      then have xy': "\<rho> \<Turnstile>\<^sub>r\<^sub>h (Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y)"
        by auto
      have "(s, y ::= e, s') \<in> es"
        using "2.hyps"(2) Asg by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V y)
          ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      from this False have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>], \<u> \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        by (meson "2.prems"(3) UnCI solves_program_def)
      moreover have 
        "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
          [
            RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>],
            \<u> \<^bold>\<noteq> (Cst\<^sub>R\<^sub>D\<^sub>V y)
          ].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> = 
          RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :-
          [
            RD [Cst\<^sub>R\<^sub>D\<^sub>N s,  Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2], 
            Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        unfolding \<mu>_def by auto
      ultimately
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>
                    :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2], Cst\<^sub>R\<^sub>D\<^sub>V x \<^bold>\<noteq> Cst\<^sub>R\<^sub>D\<^sub>V y] ."
        unfolding solves_cls_def by (metis substitution_lemma_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                         :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        using xy' by (simp add: prop_inf_last_from_cls_rh_to_cls)
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- [] ."
        using ind by (metis meaning_cls.simps modus_ponens_rh solves_cls_def solves_lh.simps)
      then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using solves_lh_lh by metis
      then show ?thesis
        by (simp add: LTS.end_of_def)
    next
      case (Bool b)
      have "(s, Bool b, s') \<in> es"
        using "2.hyps"(2) Bool by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]
         ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(3) UnCI solves_program_def)
      moreover 
      have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]].) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
            RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :- 
              [RD[Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                               :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_lemma)
      then have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        using ind
        by (meson prop_inf_only)
      then show ?thesis
        by (simp add: LTS.end_of_def)
    next
      case Skip
      have "(s, Skip, s') \<in> es"
        using "2.hyps"(2) Skip by auto
      then have "RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :-
         [
           RD[Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]
         ]. \<in> ana_RD (es,start,end)"
        unfolding ana_RD.simps by force
      then have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] ."
        by (meson "2.prems"(3) UnCI solves_program_def)
      moreover
      have "(RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', \<u>, \<v>, \<w>]\<rangle> :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, \<u>, \<v>, \<w>]] .) \<cdot>\<^sub>c\<^sub>l\<^sub>s \<mu> =
            RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> :-
              [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]]."
        unfolding \<mu>_def by auto
      ultimately 
      have "\<rho> \<Turnstile>\<^sub>c\<^sub>l\<^sub>s RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle> 
                    :- [RD [Cst\<^sub>R\<^sub>D\<^sub>N s, Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]] ."
        by (metis substitution_lemma)
      from modus_ponens_rh[OF this ind] have "\<rho> \<Turnstile>\<^sub>l\<^sub>h RD\<langle>[Cst\<^sub>R\<^sub>D\<^sub>N s', Cst\<^sub>R\<^sub>D\<^sub>V x, Cst\<^sub>R\<^sub>D\<^sub>N_Q q1, Cst\<^sub>R\<^sub>D\<^sub>N q2]\<rangle>."
        .
      then show ?thesis
        by (simp add: LTS.end_of_def)
    qed
  qed
qed

theorem RD_sound:
  assumes "\<rho> \<Turnstile>\<^sub>d\<^sub>l (var_contraints \<union> ana_RD pg)"
  shows "summarizes_RD \<rho> pg"
  using assms RD_sound' by (cases pg) force


subsection \<open>Reaching Definitions as Bit-Vector Framework analysis\<close>

\<comment> \<open>Encoding of Reaching Definitions into Datalog using the Bit-Vector Framework.\<close>

locale analysis_RD = finite_program_graph pg
  for pg :: "('n::finite,'v::finite action) program_graph" +
  assumes "finite edges"
begin

interpretation LTS edges .

definition analysis_dom_RD :: "('n,'v) def set" where
  "analysis_dom_RD = UNIV \<times> UNIV \<times> UNIV"

fun kill_set_RD :: "('n,'v action) edge \<Rightarrow> ('n,'v) def set" where
  "kill_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> UNIV \<times> UNIV"
| "kill_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "kill_set_RD (v, Skip, vc) = {}"

fun gen_set_RD :: "('n,'v action) edge \<Rightarrow> ('n,'v) def set" where
  "gen_set_RD (q\<^sub>o, x ::= a, q\<^sub>s) = {x} \<times> {Some q\<^sub>o} \<times> {q\<^sub>s}"
| "gen_set_RD (q\<^sub>o, Bool b, q\<^sub>s) = {}"
| "gen_set_RD (v, Skip, vc) = {} "

definition d_init_RD :: " ('n,'v) def set" where
  "d_init_RD = (UNIV \<times> {None} \<times> {start})"


lemma finite_analysis_dom_RD: "finite analysis_dom_RD"
  by auto

lemma d_init_RD_subset_analysis_dom_RD:
  "d_init_RD \<subseteq> analysis_dom_RD"
  unfolding d_init_RD_def analysis_dom_RD_def by auto

lemma gen_RD_subset_analysis_dom: "gen_set_RD e \<subseteq> analysis_dom_RD"
  unfolding analysis_dom_RD_def by auto

lemma kill_RD_subset_analysis_dom: "kill_set_RD e \<subseteq> analysis_dom_RD"
  unfolding analysis_dom_RD_def by auto

interpretation fw_may: analysis_BV_forward_may pg analysis_dom_RD kill_set_RD gen_set_RD d_init_RD 
  using analysis_BV_forward_may_def analysis_RD_axioms analysis_RD_def
    d_init_RD_subset_analysis_dom_RD finite_analysis_dom_RD gen_RD_subset_analysis_dom 
    kill_RD_subset_analysis_dom analysis_BV_forward_may_axioms.intro by metis

lemma def_var_def_edge_S_hat:
  assumes "def_var \<pi> x start \<in> R"
  assumes "x \<notin> def_edge t"
  shows "def_var \<pi> x start \<in> fw_may.S_hat t R"
proof -
  define q1 where "q1 = fst t"
  define \<alpha> where "\<alpha> = fst (snd t)"
  define q2 where "q2 = snd (snd t)"
  have t_def: "t = (q1, \<alpha>, q2)"
    by (simp add: \<alpha>_def q1_def q2_def)

  from assms(2) have x_not_def: "x \<notin> def_edge (q1, \<alpha>, q2)"
    unfolding t_def by auto

  have "def_var \<pi> x start \<in> fw_may.S_hat (q1, \<alpha>, q2) R"
  proof (cases \<alpha>)
    case (Asg y exp)
    then show ?thesis
      by (metis (no_types, lifting) DiffI Un_iff assms(1) x_not_def def_action.simps(1) def_var_x fw_may.S_hat_def kill_set_RD.simps(1) mem_Sigma_iff old.prod.case prod.collapse)
  next
    case (Bool b)
    then show ?thesis
      by (simp add: fw_may.S_hat_def assms(1))
  next
    case Skip
    then show ?thesis
      by (simp add: fw_may.S_hat_def assms(1))
  qed
  then show ?thesis
    unfolding t_def by auto
qed

lemma def_var_S_hat_edge_list: "(def_var \<pi>) x start \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    unfolding def_var_def d_init_RD_def by auto
next
  case (snoc t \<pi>)
  then show ?case
  proof (cases "x \<in> def_edge t")
    case True
    then have "def_var (\<pi> @[t]) x start = def_var [t] x start"
      by (simp add: def_var_def)
    moreover
    have "fw_may.S_hat_edge_list (\<pi> @ [t]) d_init_RD = fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      unfolding fw_may.S_hat_edge_list_def2 by simp
    moreover
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    moreover
    have "def_var [t] x start \<in> fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      unfolding fw_may.S_hat_def def_var_def def_of_def using True t_split by (cases \<alpha>) auto
    ultimately
    show ?thesis by auto
  next
    case False
    obtain q1 \<alpha> q2 where t_split: "t = (q1, \<alpha>, q2)"
      using prod_cases3 by blast
    from False have "def_var (\<pi> @ [t]) x start = def_var \<pi> x start"
      by (simp add: def_var_def)
    moreover
    from snoc.IH have "def_var \<pi> x start \<in> fw_may.S_hat t (fw_may.S_hat_edge_list \<pi> d_init_RD)"
      by (simp add: False def_var_def_edge_S_hat)
    then have "def_var \<pi> x start \<in> fw_may.S_hat_edge_list (\<pi> @ [t]) d_init_RD"
      unfolding fw_may.S_hat_edge_list_def2 by simp
    ultimately
    show ?thesis
      using snoc by auto
  qed
qed

lemma last_overwrites:
  "def_var (\<pi> @ [(q1, x ::= exp, q2)]) x start = (x, Some q1, q2)"
proof -
  have "x \<in> def_edge (q1, x ::= exp, q2)"
    by auto
  then have "\<exists>e\<in>set (\<pi> @ [(q1, x ::= exp, q2)]). x \<in> def_edge e"
    by auto
  have "def_var (\<pi> @ [(q1, x ::= exp, q2)]) x start = def_of x (last (filter (\<lambda>e. x \<in> def_edge e) (\<pi> @ [(q1, x ::= exp, q2)])))"
    unfolding def_var_def by auto
  also
  have "... = def_of x (q1, x ::= exp, q2)"
    by auto
  also
  have "... = (x, Some q1, q2)"
    unfolding def_of_def by auto
  finally
  show ?thesis
    .
qed

lemma S_hat_edge_list_last: "fw_may.S_hat_edge_list (\<pi> @ [e]) d_init_RD = fw_may.S_hat e (fw_may.S_hat_edge_list \<pi> d_init_RD)"
  using fw_may.S_hat_edge_list_def2 foldl_conv_foldr by simp

lemma def_var_if_S_hat:
  assumes "(x,q1,q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
  shows "(x,q1,q2) = (def_var \<pi>) x start"
  using assms
proof (induction \<pi> rule: rev_induct)
  case Nil
  then show ?case
    by (metis append_is_Nil_conv d_init_RD_def def_var_def in_set_conv_decomp fw_may.S_hat_edge_list.simps(1) list.distinct(1) mem_Sigma_iff singletonD)
next
  case (snoc e \<pi>)

  from snoc(2) have "(x, q1, q2) \<in> fw_may.S_hat e (fw_may.S_hat_edge_list \<pi> d_init_RD)"
    using S_hat_edge_list_last by blast     

  then have "(x, q1, q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e \<or> (x, q1, q2) \<in> gen_set_RD e"
    unfolding fw_may.S_hat_def by auto
  then show ?case
  proof
    assume a: "(x, q1, q2) \<in> fw_may.S_hat_edge_list \<pi> d_init_RD - kill_set_RD e"
    then have "(x, q1, q2) = def_var \<pi> x start"
      using snoc by auto
    moreover
    from a have "(x, q1, q2) \<notin> kill_set_RD e"
      by auto
    then have "def_var (\<pi> @ [e]) x start = def_var \<pi> x start"
    proof -
      assume def_not_kill: "(x, q1, q2) \<notin> kill_set_RD e"
      obtain q q' \<alpha> where "e = (q, \<alpha>, q')"
        by (cases e) auto
      then have "x \<notin> def_edge e"
        using def_not_kill by (cases \<alpha>) auto
      then show ?thesis
        by (simp add: def_var_def)
    qed
    ultimately
    show ?case
      by auto
  next
    assume a: "(x, q1, q2) \<in> gen_set_RD e"
    obtain q q' \<alpha> where "e = (q, \<alpha>, q')"
      by (cases e) auto
    then have "\<exists>exp theq1. e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      using a by (cases \<alpha>) auto
    then obtain exp theq1 where exp_theq1_p: "e = (theq1, x ::= exp, q2) \<and> q1 = Some theq1"
      by auto
    then have "(x, q1, q2) = def_var (\<pi> @ [(theq1, x ::= exp, q2)]) x start"
      using last_overwrites[of \<pi> theq1 x exp q2] by auto
    then show ?case
      using exp_theq1_p by auto
  qed
qed

lemma def_var_UNIV_S_hat_edge_list: "(\<lambda>x. def_var \<pi> x start) ` UNIV = fw_may.S_hat_edge_list \<pi> d_init_RD"
proof (rule; rule)
  fix x
  assume "x \<in> range (\<lambda>x. def_var \<pi> x start)"
  then show "x \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
    using def_var_S_hat_edge_list by blast
next
  fix x
  assume "x \<in> fw_may.S_hat_edge_list \<pi> d_init_RD"
  then show "x \<in> range (\<lambda>x. def_var \<pi> x start)"
    by (metis def_var_if_S_hat prod.collapse range_eqI)
qed

lemma def_path_S_hat_path: "def_path \<pi> start = fw_may.S_hat_path \<pi> d_init_RD"
  using fw_may.S_hat_path_def def_path_def def_var_UNIV_S_hat_edge_list by metis

definition summarizes_RD :: "(pred, ('n,'v action,('n,'v) def) cst) pred_val \<Rightarrow> bool" where
  "summarizes_RD \<rho> \<longleftrightarrow> (\<forall>\<pi> d. \<pi> \<in> path_with_word_from start \<longrightarrow> d \<in> def_path \<pi> start \<longrightarrow> 
                        \<rho> \<Turnstile>\<^sub>l\<^sub>h may\<langle>[Cst\<^sub>N (end_of \<pi>), Cst\<^sub>E d]\<rangle>.)"

theorem RD_sound: 
  assumes "\<rho> \<Turnstile>\<^sub>l\<^sub>s\<^sub>t fw_may.ana_pg_fw_may s_BV"
  shows "summarizes_RD \<rho>"
  using assms def_path_S_hat_path fw_may.sound_ana_pg_fw_may unfolding fw_may.summarizes_fw_may_def summarizes_RD.simps
  using edges_def in_mono edges_def start_def start_def summarizes_RD_def by fastforce 

end

end