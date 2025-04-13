section\<open>Implementation of First Order Rewriting\<close>

theory Trs_Impl
  imports
    Trs
    First_Order_Rewriting.Term_Impl
    First_Order_Terms.Matching
    First_Order_Rewriting.Abstract_Rewriting_Impl
    Option_Util
    "Transitive-Closure.RBT_Map_Set_Extension"
begin

subsection \<open>Implementation of the Rewrite Relation\<close>
subsubsection\<open>Generate All Rewrites\<close>

type_synonym ('f, 'v) rules = "('f, 'v) rule list"

context fixes R :: "('f,'v)rules" 
begin

definition rrewrite :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list"
  where
    "rrewrite s = List.maps (\<lambda> (l, r) . case match s l of
      None \<Rightarrow> []
    | Some \<sigma> \<Rightarrow> [r \<cdot> \<sigma>]) R"

lemma rrewrite_sound: "t \<in> set (rrewrite s) \<Longrightarrow> (s,t) \<in> rrstep (set R)" 
  unfolding rrewrite_def List.maps_def using match_matches[of s]
  by force

lemma rrewrite_complete: assumes "(s,t) \<in> rrstep (set R)"
  shows "\<exists> u. u \<in> set (rrewrite s)"
proof -
  from assms obtain l r \<sigma> where lr: "(l,r) \<in> set R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" 
    by (rule rrstepE)
  from match_complete'[OF s[symmetric]] obtain \<tau> where match: "match s l = Some \<tau>" 
    by auto
  with lr match have "r \<cdot> \<tau> \<in> set (rrewrite s)" unfolding rrewrite_def List.maps_def by force
  thus ?thesis ..
qed

lemma rrewrite: assumes "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term l \<supseteq> vars_term r" 
  shows "set (rrewrite s) = {t. (s,t) \<in> rrstep (set R)}"
proof (standard; clarify)
  fix t
  assume "(s,t) \<in> rrstep (set R)" 
  then obtain l r \<sigma> where lr: "(l,r) \<in> set R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" 
    by (rule rrstepE)
  from match_complete'[OF s[symmetric]] obtain \<tau> where match: "match s l = Some \<tau>" 
    and vars: "\<And> x. x \<in> vars_term l \<Longrightarrow> \<sigma> x = \<tau> x" by auto
  have vars': "\<And> x. x \<in> vars_term r \<Longrightarrow> \<sigma> x = \<tau> x" using assms[OF lr] vars by auto
  have t: "t = r \<cdot> \<tau>" unfolding t using vars' by (intro term_subst_eq, auto)
  with lr match show "t \<in> set (rrewrite s)" unfolding rrewrite_def List.maps_def by force
qed (rule rrewrite_sound)

fun rewrite :: "('f, 'v) term \<Rightarrow> ('f, 'v) term list" where
  "rewrite s = (rrewrite s @ (case s of Var _ \<Rightarrow> [] | Fun f ss \<Rightarrow> 
    concat (map (\<lambda> (i, si). map (\<lambda> ti. Fun f (ss[i := ti])) (rewrite si))
     (zip [0..< length ss] ss))))"

declare rewrite.simps[simp del]

lemma rewrite_sound: "t \<in> set (rewrite s) \<Longrightarrow> (s,t) \<in> rstep (set R)"
proof (induct s arbitrary: t rule: rewrite.induct)
  case (1 s t)
  note [simp] = rewrite.simps[of s]
  from 1(2) consider (root) "t \<in> set (rrewrite s)" | 
    (arg) f ss ti i where "s = Fun f ss" "i < length ss" "ti \<in> set (rewrite (ss ! i))" "t = Fun f (ss[i := ti])" 
    by (auto simp: set_zip)
  thus ?case
  proof cases
    case root
    with rrewrite_sound[of t s] have "(s,t) \<in> rrstep (set R)" by auto
    thus ?thesis by (rule rrstep_imp_rstep)
  next
    case (arg f ss ti i)
    from arg(2) have mem: "(i, ss ! i) \<in> set (zip [0..<length ss] ss)" by (force simp: set_zip)
    from 1(1)[OF arg(1) mem refl arg(3)] 
    have IH: "(ss ! i, ti) \<in> rstep (set R)" .
    with arg have "(s,t) \<in> nrrstep (set R)" 
      unfolding nrrstep_iff_arg_rstep by blast
    thus ?thesis by (rule nrrstep_imp_rstep)
  qed
qed


lemma rewrite: assumes "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term l \<supseteq> vars_term r" 
  shows "set (rewrite s) = {t. (s,t) \<in> rstep (set R)}"
proof (standard; clarify)
  fix t
  assume "(s,t) \<in> rstep (set R)" 
  then obtain C u v where s: "s = C\<langle>u\<rangle>" and t: "t = C\<langle>v\<rangle>" and step: "(u,v) \<in> rrstep (set R)" 
    by blast
  from rrewrite[OF assms, of u] step have step: "v \<in> set (rrewrite u)" by auto
  show "t \<in> set (rewrite s)" unfolding s t
  proof (induct C)
    case Hole
    then show ?case using step by (auto simp: rewrite.simps[of u])
  next
    case (More f bef C aft)
    show ?case 
      apply (simp add: rewrite.simps[of "Fun f _"] set_zip)
      apply (intro disjI2)
      apply (intro exI[of _ "C\<langle>u\<rangle>"] exI)
      apply (intro conjI exI[of _ "length bef"])
      using More by (auto simp: nth_append)
  qed
qed (rule rewrite_sound)

lemma rewrite_complete: assumes "(s,t) \<in> rstep (set R)"
  shows "\<exists> w. w \<in> set (rewrite s)" 
proof -
  from assms obtain C u v where s: "s = C\<langle>u\<rangle>" and t: "t = C\<langle>v\<rangle>" and step: "(u,v) \<in> rrstep (set R)" 
    by blast
  from rrewrite_complete[OF step] obtain v where step: "v \<in> set (rrewrite u)" by auto
  have "C\<langle>v\<rangle> \<in> set (rewrite s)" unfolding s 
  proof (induct C)
    case Hole
    then show ?case using step by (auto simp: rewrite.simps[of u])
  next
    case (More f bef C aft)
    show ?case 
      apply (simp add: rewrite.simps[of "Fun f _"] set_zip)
      apply (intro disjI2)
      apply (intro exI[of _ "C\<langle>u\<rangle>"] exI)
      apply (intro conjI exI[of _ "length bef"])
      using More by (auto simp: nth_append)
  qed
  thus ?thesis by blast
qed
end


lemma rrewrite_mono: "set R \<subseteq> set S \<Longrightarrow> set (rrewrite R s) \<subseteq> set (rrewrite S s)" 
  unfolding rrewrite_def List.maps_def by auto 

lemma Union_image_mono: "(\<And> x. x \<in> A \<Longrightarrow> f x \<subseteq> g x) \<Longrightarrow> \<Union> (f ` A) \<subseteq> \<Union> (g ` A)"
  by blast

lemma rewrite_mono: assumes "set R \<subseteq> set S"
  shows "set (rewrite R s) \<subseteq> set (rewrite S s)" 
proof -
  note rrewrite = rrewrite_mono[OF assms]
  show ?thesis
  proof (induct s)
    case (Var x)
    thus ?case using rrewrite unfolding rewrite.simps[of _ "Var x"] by auto
  next
    case (Fun f ss)
    show ?case unfolding rewrite.simps[of _ "Fun f ss"]
        set_append term.simps set_concat set_map image_comp set_zip o_def
      apply (intro Un_mono, rule rrewrite)
      by (intro Union_image_mono, insert Fun, force simp: set_conv_nth[of ss])
  qed
qed


definition first_rewrite :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term option"
  where "first_rewrite R s \<equiv> case rewrite R s of Nil \<Rightarrow> None | Cons t _ \<Rightarrow> Some t"


subsubsection\<open>Checking a Single Rewrite Step\<close>

definition is_root_step :: "('f, 'v)trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "is_root_step R s t = (\<exists> (l, r) \<in> R. case match_list Var [(l,s),(r,t)] of
      None \<Rightarrow> False
    | Some _ \<Rightarrow> True)"

lemma rrstep_code[code_unfold]: "(s,t) \<in> rrstep R \<longleftrightarrow> is_root_step R s t"
proof
  show "is_root_step R s t \<Longrightarrow> (s, t) \<in> rrstep R"  
    unfolding is_root_step_def rrstep_def rstep_r_p_s_def'
    by (auto split: option.splits) (force dest: match_list_matches)
  assume "(s, t) \<in> rrstep R"
  then obtain \<sigma> l r where lr: "(l,r) \<in> R" and id: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" 
    by (metis rrstepE)
  show "is_root_step R s t" unfolding id
    unfolding is_root_step_def 
    by (cases "match_list Var [(l, l \<cdot> \<sigma>), (r, r \<cdot> \<sigma>)]",
        auto intro!: bexI[OF _ lr] dest!: match_list_complete)
qed

lemma is_root_step: "is_root_step R s t \<Longrightarrow> (s, t) \<in> rrstep R"
  unfolding rrstep_code .

fun is_rstep :: "('f,'v)trs \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool" where
  "is_rstep R (Fun f ts) (Fun g ss) = (
     f = g \<and> length ts = length ss \<and> (\<exists> i \<in> set [0..<length ss].
        ss = ts[i := ss ! i] \<and> is_rstep R (ts ! i) (ss ! i))
     \<or> (Fun f ts, Fun g ss) \<in> rrstep R)" 
| "is_rstep R s t = ((s,t) \<in> rrstep R)" 

lemma is_rstep_sound: "is_rstep R s t \<Longrightarrow> (s,t) \<in> rstep R" 
proof (induct R s t rule: is_rstep.induct)
  case (1 R f ts g ss)
  show ?case
  proof (cases "(Fun f ts, Fun g ss) \<in> rrstep R")
    case True
    thus ?thesis using rrstep_imp_rstep by auto
  next
    case False
    with 1(2) obtain i where
      i: "i < length ss" and
      gf: "g = f" and len: "length ts = length ss" and id: "ss = ts[i := ss ! i]" 
      and rec: "is_rstep R (ts ! i) (ss ! i)"
      by auto
    from 1(1)[OF _ rec] i have "(ts ! i, ss ! i) \<in> rstep R" by auto
    thus ?thesis unfolding gf using id i len
      by (metis nrrstep_iff_arg_rstep nrrstep_imp_rstep)
  qed
qed (insert rrstep_imp_rstep, auto)

lemma is_rstep_complete: assumes "(s,t) \<in> rstep R" 
  shows "is_rstep R s t" 
proof -
  from rstepE[OF assms] obtain C s' t' where 
    id: "s = C \<langle>s'\<rangle>" "t = C\<langle>t'\<rangle>" and step: "(s',t') \<in> rrstep R" 
    using rrstepI by metis
  show ?thesis unfolding id
  proof (induct C)
    case Hole
    then show ?case using step by (cases s'; cases t', auto)
  next
    case (More f bef C aft)
    show ?case unfolding intp_actxt.simps is_rstep.simps
      by (intro disjI1 conjI bexI[of _ "length bef"], insert More, auto)
  qed
qed

lemma is_rstep[simp]: "is_rstep R s t \<longleftrightarrow> (s,t) \<in> rstep R" 
  using is_rstep_sound is_rstep_complete by auto

lemma in_rstep_code[code_unfold]: 
  "st \<in> rstep R \<longleftrightarrow> (case st of (s,t) \<Rightarrow> is_rstep R s t)" 
  by (cases st, auto)

subsection\<open>Computation of a Normal Form\<close>


definition compute_rstep_NF :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term option"
  where "compute_rstep_NF R s \<equiv> compute_NF (first_rewrite R) s"

lemma compute_rstep_NF_sound:
  assumes res: "compute_rstep_NF R s = Some t"
  shows "(s, t) \<in> (rstep (set R))^*" using res[unfolded compute_rstep_NF_def]
proof (rule compute_NF_sound)
  fix s t
  assume "first_rewrite R s = Some t"
  from this[unfolded first_rewrite_def] obtain ts where "rewrite R s = t # ts"
    by (cases "rewrite R s", auto)
  then have t: "t \<in> set (rewrite R s)" by simp
  from rewrite_sound[OF this] show "(s,t) \<in> rstep (set R)" .
qed

lemma compute_rstep_NF_complete: assumes res: "compute_rstep_NF R s = Some t"
  shows "t \<in> NF (rstep (set R))" using res[unfolded compute_rstep_NF_def]
proof (rule compute_NF_complete)
  fix s
  assume "first_rewrite R s = None"
  from this[unfolded first_rewrite_def] have empty: "rewrite R s = []" 
    by (cases "rewrite R s", auto)
  have False if "(s,t) \<in> rstep (set R)" for t 
    using rewrite_complete[OF that] arg_cong[OF empty, of set] by auto
  thus "s \<in> NF (rstep (set R))" by blast
qed

lemma compute_rstep_NF_SN: assumes SN: "SN (rstep (set R))"
  shows "\<exists> t. compute_rstep_NF R s = Some t"
proof -
  have "\<exists> t. compute_NF (first_rewrite R) s = Some t"
  proof (rule compute_NF_SN[OF SN])
    fix s t
    assume "first_rewrite R s = Some t"
    from this[unfolded first_rewrite_def] have
      rewrite: "t \<in> set (rewrite R s)" by (auto split: list.splits)
    from rewrite_sound[OF this]
    show "(s,t) \<in> rstep (set R)" .
  qed  
  then show ?thesis unfolding compute_rstep_NF_def .
qed

subsubsection\<open>Computing Reachable Terms with Limit on Derivation Length\<close>

fun reachable_terms :: 
  "('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> nat \<Rightarrow> ('f, 'v) term list"
  where 
    "reachable_terms R s 0 = [s]"
  | "reachable_terms R s (Suc n) = (
  let ts = (reachable_terms R s n) in
    remdups (ts@(concat (map (\<lambda> t. rewrite R t) ts)))
  )"

lemma reachable_terms_nat:
  assumes "t \<in> set (reachable_terms R s i)"
  shows "\<exists> j. j \<le> i \<and> (s,t) \<in> (rstep (set R))^^j"
  using assms
proof (induct i arbitrary: t)
  case 0 
  then show ?case by auto
next
  case (Suc i) 
  let ?R = "\<lambda> j. (rstep (set R))^^j"
  from Suc(2)
  have "t \<in> set (reachable_terms R s i)
    \<or> (\<exists> u \<in> set (reachable_terms R s i). t \<in> set (rewrite R u))" by (simp add: Let_def)
  then show ?case
  proof
    assume "t \<in> set (reachable_terms R s i)"
    from Suc(1)[OF this] obtain j where "j \<le> i" and "(s,t) \<in> ?R j" by auto 
    then show ?thesis by (intro exI[of _ j], auto)
  next
    assume "\<exists> u \<in> set (reachable_terms R s i). t \<in> set (rewrite R u)"
    then obtain u where u: "u \<in> set (reachable_terms R s i)"
      and 1: "t \<in> set (rewrite R u)" by auto
    from rewrite_sound[OF 1] have ut: "(u,t) \<in> rstep (set R)" .
    from Suc(1)[OF u] obtain j where j: "j \<le> i" and su: "(s,u) \<in> ?R j" by auto
    from su ut have "(s,t) \<in> ?R (Suc j)" by auto
    with j show ?thesis by (intro exI[of _ "Suc j"], auto)
  qed
qed

lemma reachable_terms:
  assumes "t \<in> set (reachable_terms R s i)"
  shows "(s,t) \<in> (rstep (set R))^*"
  using reachable_terms_nat[OF assms] by (metis relpow_imp_rtrancl)

lemma reachable_terms_one:
  assumes "t \<in> set (reachable_terms R s (Suc 0))"
  shows "(s,t) \<in> (rstep (set R))^="
proof -
  from reachable_terms_nat[OF assms] obtain j where "j \<le> 1"
    and "(s,t) \<in> (rstep (set R))^^j" by auto
  then show ?thesis by (cases j, auto)
qed

subsubsection\<open>Algorithms to Ensure Joinability\<close>

definition
  check_join_NF ::
  "('f :: showl, 'v :: showl) rules \<Rightarrow> 
     ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  where
    "check_join_NF R s t \<equiv> case (compute_rstep_NF R s, compute_rstep_NF R t) of
      (Some s', Some t') \<Rightarrow> 
     check (s' = t') (
    showsl (STR ''the normal form '') \<circ> showsl s' \<circ> showsl (STR '' of '') \<circ> showsl s 
      \<circ> showsl (STR '' differs from\<newline>the normal form '') \<circ> showsl t' \<circ> showsl (STR '' of '') \<circ> showsl t)
       |  _ \<Rightarrow> error (showsl (STR ''strange error in normal form computation''))"

lemma check_join_NF_sound:
  assumes ok: "isOK (check_join_NF R s t)"
  shows "(s, t) \<in> join (rstep (set R))"
proof -
  note ok = ok[unfolded check_join_NF_def]
  from ok obtain s' where s: "compute_rstep_NF R s = Some s'" by force
  note ok = ok[unfolded s]
  from ok obtain t' where t: "compute_rstep_NF R t = Some t'" by force
  from ok[unfolded t] have id: "s' = t'" by simp
  note seq = compute_rstep_NF_sound
  from seq[OF s] seq[OF t]
  show ?thesis unfolding id by auto
qed


function iterative_join_search_main ::
  "('f,'v) rules \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where
    "iterative_join_search_main R s t i n = (if i \<le> n then
  (((list_inter (reachable_terms R s i) (reachable_terms R t i)) \<noteq> []) \<or> (iterative_join_search_main R s t (Suc i) n)) else False)"
  by pat_completeness auto

termination by (relation "measure ( \<lambda> (R,s,t,i,n). Suc n - i)") auto

lemma iterative_join_search_main: 
  "iterative_join_search_main R s t i n \<Longrightarrow> (s,t) \<in> join (rstep (set R))"
proof (induction rule: iterative_join_search_main.induct)
  case (1 R s t i n)
  from 1(2) have i_n: "i \<le> n" by (simp split: if_splits)
  note IH = 1(1)[OF i_n]
  let ?I = "list_inter (reachable_terms R s i) (reachable_terms R t i)"
  from 1(2) i_n have "?I \<noteq> [] \<or> iterative_join_search_main R s t (Suc i) n" by auto
  then show ?case
  proof
    assume a: "?I \<noteq> []"
    then obtain u us where u: "?I = u # us" by (cases ?I, auto)
    then have d: "u \<in> set ?I" by auto
    from this[simplified] reachable_terms[of u _ _ i] have c: "(s, u) \<in> (rstep (set R))\<^sup>*" by auto
    from d[simplified] reachable_terms[of u _ _ i] have e: "(t,u) \<in> (rstep (set R))^*" by auto
    from c e show ?thesis by auto
  next
    assume b: "iterative_join_search_main R s t (Suc i) n"
    from  IH[OF this] show ?thesis .
  qed
qed

definition iterative_join_search where 
  "iterative_join_search R s t n \<equiv> iterative_join_search_main R s t 0 n"

lemma iterative_join_search: "iterative_join_search R s t n \<Longrightarrow> (s,t) \<in> join (rstep (set R))"
  by (rule iterative_join_search_main, unfold iterative_join_search_def)

definition
  check_join_BFS_limit ::
  "nat \<Rightarrow> ('f :: showl, 'v :: showl) rules \<Rightarrow> 
     ('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> showsl check"
  where
    "check_join_BFS_limit n R s t \<equiv> check (iterative_join_search R s t n) 
    (showsl (STR ''could not find a joining sequence of length at most '') \<circ> 
     showsl n \<circ> showsl (STR '' for the terms '') \<circ> showsl s \<circ> 
     showsl (STR '' and '') \<circ> showsl t \<circ> showsl_nl)"

lemma check_join_BFS_limit_sound:
  assumes ok: "isOK (check_join_BFS_limit n R s t)"
  shows "(s, t) \<in> join (rstep (set R))"
  by (rule iterative_join_search, insert ok[unfolded check_join_BFS_limit_def], simp)

definition map_funs_rules :: "('f \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('g, 'v) rules" where
  "map_funs_rules fg R = map (map_funs_rule fg) R"

lemma map_funs_rules_sound[simp]:
  "set (map_funs_rules fg R) = map_funs_trs fg (set R)"
  unfolding map_funs_rules_def map_funs_trs.simps by simp

subsubsection \<open>Displaying TRSs as Strings\<close>

fun showsl_rule' :: "('f \<Rightarrow> showsl) \<Rightarrow> ('v \<Rightarrow> showsl) \<Rightarrow> String.literal \<Rightarrow> ('f, 'v) rule \<Rightarrow> showsl"
  where
    "showsl_rule' fun var arr (l, r) =
    showsl_term' fun var l \<circ> showsl arr \<circ> showsl_term' fun var r"

definition "showsl_rule \<equiv> showsl_rule' showsl showsl (STR '' -> '')"
definition "showsl_weak_rule \<equiv> showsl_rule' showsl showsl (STR '' ->= '')"

definition
  showsl_rules' :: "('f \<Rightarrow> showsl) \<Rightarrow> ('v \<Rightarrow> showsl) \<Rightarrow> String.literal \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl"
  where
    "showsl_rules' fun var arr trs =
    showsl_list_gen (showsl_rule' fun var arr) (STR '''') (STR '''') (STR ''\<newline>'') (STR '''') trs \<circ> showsl_nl"

definition "showsl_rules \<equiv> showsl_rules' showsl showsl (STR '' -> '')"
definition "showsl_weak_rules \<equiv> showsl_rules' showsl showsl (STR '' ->= '')"

definition
  showsl_trs' :: "('f \<Rightarrow> showsl) \<Rightarrow> ('v \<Rightarrow> showsl) \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl"
  where
    "showsl_trs' fun var name arr R = showsl name \<circ> showsl (STR ''\<newline>\<newline>'') \<circ> showsl_rules' fun var arr R"

definition "showsl_trs \<equiv> showsl_trs' showsl showsl (STR ''rewrite system:'') (STR '' -> '')"


subsubsection\<open>Computing Syntactic Properties of TRSs\<close>

definition add_vars_rule :: "('f, 'v) rule \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
    "add_vars_rule r xs = add_vars_term (fst r) (add_vars_term (snd r) xs)"

definition add_funs_rule :: "('f, 'v) rule \<Rightarrow> 'f list \<Rightarrow> 'f list"
  where
    "add_funs_rule r fs = add_funs_term (fst r) (add_funs_term (snd r) fs)"

definition add_funas_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "add_funas_rule r fs = add_funas_term (fst r) (add_funas_term (snd r) fs)"

definition add_roots_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "add_roots_rule r fs = root_list (fst r) @ root_list (snd r) @ fs"

definition add_funas_args_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "add_funas_args_rule r fs = add_funas_args_term (fst r) (add_funas_args_term (snd r) fs)"

lemma add_vars_rule_vars_rule_list_conv [simp]:
  "add_vars_rule r xs = vars_rule_list r @ xs"
  by (simp add: add_vars_rule_def vars_rule_list_def)

lemma add_funs_rule_funs_rule_list_conv [simp]:
  "add_funs_rule r fs = funs_rule_list r @ fs"
  by (simp add: add_funs_rule_def funs_rule_list_def)

lemma add_funas_rule_funas_rule_list_conv [simp]:
  "add_funas_rule r fs = funas_rule_list r @ fs"
  by (simp add: add_funas_rule_def funas_rule_list_def)

lemma add_roots_rule_roots_rule_list_conv [simp]:
  "add_roots_rule r fs = roots_rule_list r @ fs"
  by (simp add: add_roots_rule_def roots_rule_list_def)

lemma add_funas_args_rule_funas_args_rule_list_conv [simp]:
  "add_funas_args_rule r fs = funas_args_rule_list r @ fs"
  by (simp add: add_funas_args_rule_def funas_args_rule_list_def)

definition insert_vars_rule :: "('f, 'v) rule \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
    "insert_vars_rule r xs = insert_vars_term (fst r) (insert_vars_term (snd r) xs)"

definition insert_funs_rule :: "('f, 'v) rule \<Rightarrow> 'f list \<Rightarrow> 'f list"
  where
    "insert_funs_rule r fs = insert_funs_term (fst r) (insert_funs_term (snd r) fs)"

definition insert_funas_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_rule r fs = insert_funas_term (fst r) (insert_funas_term (snd r) fs)"

definition insert_roots_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_roots_rule r fs =
    foldr List.insert (option_to_list (root (fst r)) @ option_to_list (root (snd r))) fs"

definition insert_funas_args_rule :: "('f, 'v) rule \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_args_rule r fs = insert_funas_args_term (fst r) (insert_funas_args_term (snd r) fs)"

lemma set_insert_vars_rule [simp]:
  "set (insert_vars_rule r xs) = vars_term (fst r) \<union> vars_term (snd r) \<union> set xs"
  by (simp add: insert_vars_rule_def ac_simps)

lemma set_insert_funs_rule [simp]:
  "set (insert_funs_rule r xs) = funs_term (fst r) \<union> funs_term (snd r) \<union> set xs"
  by (simp add: insert_funs_rule_def ac_simps)

lemma set_insert_funas_rule [simp]:
  "set (insert_funas_rule r xs) = funas_term (fst r) \<union> funas_term (snd r) \<union> set xs"
  by (simp add: insert_funas_rule_def ac_simps)

lemma set_insert_roots_rule [simp]:
  "set (insert_roots_rule r xs) = root_set (fst r) \<union> root_set (snd r) \<union> set xs"
  by (cases "fst r" "snd r" rule: term.exhaust [case_product term.exhaust])
    (auto simp: insert_roots_rule_def ac_simps)

lemma set_insert_funas_args_rule [simp]:
  "set (insert_funas_args_rule r xs) = funas_args_term (fst r) \<union> funas_args_term (snd r) \<union> set xs"
  by (simp add: insert_funas_args_rule_def ac_simps funas_args_term_def)

abbreviation "vars_rule_impl r \<equiv> insert_vars_rule r []"
abbreviation "funs_rule_impl r \<equiv> insert_funs_rule r []"
abbreviation "funas_rule_impl r \<equiv> insert_funas_rule r []"
abbreviation "roots_rule_impl r \<equiv> insert_roots_rule r []"
abbreviation "funas_args_rule_impl r \<equiv> insert_funas_args_rule r []"

lemma set_vars_rule_impl:
  "set (vars_rule_impl r) = vars_rule r"
  by (simp add: vars_rule_def)

lemma xxx_rule_list_code[code]:
  "vars_rule_list r = add_vars_rule r []"
  "funs_rule_list r = add_funs_rule r []"
  "funas_rule_list r = add_funas_rule r []"
  "roots_rule_list r = add_roots_rule r []"
  "funas_args_rule_list r = add_funas_args_rule r []"
  by (simp_all add: vars_rule_list_def funs_rule_list_def funas_rule_list_def
      roots_rule_list_def funas_args_rule_list_def)

lemma xxx_trs_list_code[code]:
  "vars_trs_list trs = foldr add_vars_rule trs []"
  "funs_trs_list trs = foldr add_funs_rule trs []"
  "funas_trs_list trs = foldr add_funas_rule trs []"
  "funas_args_trs_list trs = foldr add_funas_args_rule trs []"
  by (induct trs)
    (simp_all add: vars_trs_list_def funs_trs_list_def funas_trs_list_def
      roots_trs_list_def funas_args_trs_list_def)

definition insert_vars_trs :: "('f, 'v) rule list \<Rightarrow> 'v list \<Rightarrow> 'v list"
  where
    "insert_vars_trs trs = foldr insert_vars_rule trs"

definition insert_funs_trs :: "('f, 'v) rule list \<Rightarrow> 'f list \<Rightarrow> 'f list"
  where
    "insert_funs_trs trs = foldr insert_funs_rule trs"

definition insert_funas_trs :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_trs trs = foldr insert_funas_rule trs"

definition insert_roots_trs :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_roots_trs trs = foldr insert_roots_rule trs"

definition insert_funas_args_trs :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list"
  where
    "insert_funas_args_trs trs = foldr insert_funas_args_rule trs"

lemma set_insert_vars_trs [simp]:
  "set (insert_vars_trs trs xs) = (\<Union>r \<in> set trs. vars_rule r) \<union> set xs"
  by (induct trs arbitrary: xs) (simp_all add: insert_vars_trs_def ac_simps vars_rule_def)

lemma set_insert_funs_trs [simp]:
  "set (insert_funs_trs trs fs) = (\<Union>r \<in> set trs. funs_rule r) \<union> set fs"
  by (induct trs arbitrary: fs) (simp_all add: insert_funs_trs_def ac_simps funs_rule_def)

lemma set_insert_funas_trs [simp]:
  "set (insert_funas_trs trs fs) = (\<Union>r \<in> set trs. funas_rule r) \<union> set fs"
  by (induct trs arbitrary: fs) (simp_all add: insert_funas_trs_def ac_simps funas_rule_def)

lemma set_insert_roots_trs [simp]:
  "set (insert_roots_trs trs fs) = (\<Union>r \<in> set trs. roots_rule r) \<union> set fs"
  by (induct trs arbitrary: fs) (simp_all add: insert_roots_trs_def ac_simps roots_rule_def)

lemma set_insert_funas_args_trs [simp]:
  "set (insert_funas_args_trs trs fs) = (\<Union>r \<in> set trs. funas_args_rule r) \<union> set fs"
  by (induct trs arbitrary: fs)
    (simp_all add: insert_funas_args_trs_def ac_simps funas_args_rule_def)

abbreviation "vars_trs_impl trs \<equiv> insert_vars_trs trs []"
abbreviation "funs_trs_impl trs \<equiv> insert_funs_trs trs []"
abbreviation "funas_trs_impl trs \<equiv> insert_funas_trs trs []"
abbreviation "roots_trs_impl trs \<equiv> insert_roots_trs trs []"
abbreviation "funas_args_trs_impl trs \<equiv> insert_funas_args_trs trs []"

definition defined_list :: "('f, 'v) rule list \<Rightarrow> ('f \<times> nat) list"
  where
    "defined_list R = [the (root l). (l, r) \<leftarrow> R, is_Fun l]"

lemma set_defined_list [simp]:
  "set (defined_list R) = {fn. defined (set R) fn}"
  by (force simp: defined_list_def defined_def elim!: root_Some)

definition check_left_linear_trs :: "('f :: showl, 'v :: showl) rules \<Rightarrow> showsl check"
  where
    "check_left_linear_trs trs =
     check_all (\<lambda>r. linear_term (fst r)) trs
       <+? (\<lambda> _. showsl_trs trs \<circ> showsl (STR ''\<newline>is not left-linear\<newline>''))"

lemma check_left_linear_trs [simp]:
  "isOK (check_left_linear_trs R) = left_linear_trs (set R)"
  unfolding check_left_linear_trs_def left_linear_trs_def
  by auto

definition check_varcond_subset :: "(_,_) rules \<Rightarrow> showsl check"
  where
    "check_varcond_subset R =
    check_allm (\<lambda>rule. 
      check_subseteq (vars_term_impl (snd rule)) (vars_term_impl (fst rule))
      <+? (\<lambda>x. showsl (STR ''free variable '') \<circ> showsl x
        \<circ> showsl (STR '' in right-hand side of rule '') \<circ> showsl_rule rule \<circ> showsl_nl)
    ) R"

lemma check_varcond_subset [simp]:
  "isOK (check_varcond_subset R) = (\<forall> (l, r) \<in> set R. vars_term r \<subseteq> vars_term l)"
  unfolding check_varcond_subset_def by force+

definition "check_varcond_no_Var_lhs =
  check_allm (\<lambda>rule.
    check (is_Fun (fst rule))
      (showsl (STR ''variable left-hand side in rule '') \<circ> showsl_rule rule \<circ> showsl_nl))"

lemma check_varcond_no_Var_lhs [simp]:
  "isOK (check_varcond_no_Var_lhs R) \<longleftrightarrow> (\<forall>(l, r) \<in> set R. is_Fun l)"
  by (auto simp: check_varcond_no_Var_lhs_def)

definition check_wf_trs :: "(_,_) rules \<Rightarrow> showsl check"
  where
    "check_wf_trs R = do {
    check_varcond_no_Var_lhs R;
    check_varcond_subset R
  } <+? (\<lambda>e. showsl (STR ''the TRS is not well-formed\<newline>'') \<circ> e)"

lemma check_wf_trs_conf [simp]:
  "isOK (check_wf_trs R) = wf_trs (set R)"
  by (force simp: check_wf_trs_def wf_trs_def)

definition check_not_wf_trs :: "(_,_) rules \<Rightarrow> showsl check" where
  "check_not_wf_trs R = check (\<not> isOK (check_wf_trs R)) (showsl (STR ''The TRS is well formed\<newline>''))"

lemma check_not_wf_trs:
  assumes "isOK(check_not_wf_trs R)"
  shows "\<not> SN (rstep (set R))"
proof -
  from assms have "\<not> wf_trs (set R)" unfolding check_not_wf_trs_def by auto
  with SN_rstep_imp_wf_trs show ?thesis by auto
qed

lemma instance_rule_code[code]:
  "instance_rule lr st \<longleftrightarrow> match_list (\<lambda> _. fst lr) [(fst st, fst lr), (snd st, snd lr)] \<noteq> None"
  (is "?l = (match_list ?d ?list \<noteq> None)")
proof
  assume ?l
  then obtain \<sigma> where "fst lr = fst st \<cdot> \<sigma>"
    and "snd lr = snd st \<cdot> \<sigma>" by (auto simp: instance_rule_def)
  then have "\<And>l t. (l, t) \<in> set ?list \<Longrightarrow> l \<cdot> \<sigma> = t" by (auto)
  then have "matchers (set ?list) \<noteq> {}" by (auto simp: matchers_def)
  with match_list_complete
  show "match_list ?d ?list \<noteq> None" by blast
next
  assume "match_list ?d ?list \<noteq> None"
  then obtain \<tau> where "match_list ?d ?list = Some \<tau>" by auto
  from match_list_sound [OF this]
  have "fst lr = fst st \<cdot> \<tau>" and "snd lr = snd st \<cdot> \<tau>" by auto
  then show ?l by (auto simp: instance_rule_def)
qed

definition
  check_CS_subseteq :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rule check"
  where
    "check_CS_subseteq R S \<equiv> check_allm (\<lambda> (l,r). check (Bex (set S) (instance_rule (l,r))) (l,r)) R"

lemma check_CS_subseteq [simp]:
  "isOK (check_CS_subseteq R S) \<longleftrightarrow> subst.closure (set R) \<subseteq> subst.closure (set S)" (is "?l = ?r")
proof
  assume ?l
  show ?r
  proof
    fix x y
    assume "(x,y) \<in> subst.closure (set R)"    
    then show "(x,y) \<in> subst.closure (set S)"
    proof (induct)
      case (subst s t \<sigma>)
      with \<open>?l\<close>[unfolded check_CS_subseteq_def]
      obtain l r \<delta> where lr: "(l,r) \<in> set S" and s: "s = l \<cdot> \<delta>" and t: "t = r \<cdot> \<delta>"
        by (auto simp add: instance_rule_def)
      show ?case unfolding s t
        using subst.closure.intros[OF lr, of "\<delta> \<circ>\<^sub>s \<sigma>"]
        by auto
    qed
  qed
next
  assume ?r
  {
    fix lr
    assume mem: "lr \<in> set R"
    obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
    with mem have "(l,r) \<in> subst.closure (set R)" using subst.subset_closure by auto
    with \<open>?r\<close> have "(l,r) \<in> subst.closure (set S)" by auto
    then have "Bex (set S) (instance_rule lr)" unfolding lr
    proof (induct)
      case (subst s t \<sigma>)
      then show ?case unfolding instance_rule_def by force
    qed
  }
  thus ?l unfolding check_CS_subseteq_def by auto
qed


definition reverse_rules :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules" where
  "reverse_rules rs \<equiv> map prod.swap rs"

lemma reverse_rules[simp]: "set (reverse_rules R) = (set R)^-1" unfolding reverse_rules_def by force

definition
  map_funs_rules_wa :: "('f \<times> nat \<Rightarrow> 'g) \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('g, 'v) rules"
  where
    "map_funs_rules_wa fg R = map (\<lambda>(l, r). (map_funs_term_wa fg l, map_funs_term_wa fg r)) R"

lemma map_funs_rules_wa: "set (map_funs_rules_wa fg R) = map_funs_trs_wa fg (set R)"
  unfolding map_funs_rules_wa_def map_funs_trs_wa_def by auto

lemma wf_rule [code]:
  "wf_rule r \<longleftrightarrow>
    is_Fun (fst r) \<and> (\<forall> x \<in> set (vars_term_impl (snd r)). x \<in> set (vars_term_impl (fst r)))"
  unfolding wf_rule_def by auto

definition wf_rules_impl :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
  where
    "wf_rules_impl R = filter wf_rule R"

lemma wf_rules_impl [simp]:
  "set (wf_rules_impl R) = wf_rules (set R)"
  unfolding wf_rules_impl_def wf_rules_def by auto

fun check_wf_reltrs :: "(_,_) rules \<times> (_,_) rules \<Rightarrow> showsl check" where
  "check_wf_reltrs (R, S) = (do {
     check_wf_trs R;
     if R = [] then succeed
     else check_varcond_subset S
   })"

lemma check_wf_reltrs[simp]:
  "isOK (check_wf_reltrs (R, S)) = wf_reltrs (set R) (set S)"
  by (cases R) auto

declare check_wf_reltrs.simps[simp del]

definition check_linear_trs :: "(_,_) rules \<Rightarrow> showsl check" where
  "check_linear_trs R \<equiv>
     check_all (\<lambda> (l,r). (linear_term l) \<and> (linear_term r)) R
       <+? (\<lambda> _. showsl_trs R \<circ> showsl (STR ''\<newline>is not linear\<newline>''))"

lemma check_linear_trs [simp]:
  "isOK (check_linear_trs R) \<longleftrightarrow> linear_trs (set R)"
  unfolding check_linear_trs_def linear_trs_def by auto

definition "non_collapsing_impl R = list_all (is_Fun o snd) R"

lemma non_collapsing_impl[simp]: "non_collapsing_impl R = non_collapsing (set R)"
  unfolding non_collapsing_impl_def non_collapsing_def list_all_iff by auto


type_synonym ('f, 'v) term_map = "'f \<times> nat \<Rightarrow> ('f, 'v) term list"

definition term_map :: "('f::compare_order, 'v) term list \<Rightarrow> ('f, 'v) term_map" where
  "term_map ts = fun_of_map (rm.\<alpha> (elem_list_to_rm (the \<circ> root) ts)) []"

definition
  is_NF_main :: "bool \<Rightarrow> bool \<Rightarrow> ('f::compare_order, 'v) term_map \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "is_NF_main var_cond R_empty m = (if var_cond then (\<lambda>_. False) 
     else if R_empty then (\<lambda>_. True)
     else (\<lambda>t. \<forall>u\<in>set (supteq_list t).
       if is_Fun u then
         \<forall>l\<in>set (m (the (root u))). \<not> matches u l
       else True))"

lemma neq_root_no_match:
  assumes "is_Fun l" and "the (root l) \<noteq> the (root t)"
  shows "\<not> matches t l"
  using assms by (cases t) (force iff: matches_iff)+

lemma all_not_conv: "(\<forall>x \<in> A. \<not> P x) = (\<not> (\<exists>x \<in> A. P x))" by auto

lemma efficient_supteq_list_do_not_match:
  assumes "\<forall>l\<in>set ls. \<forall>u\<in>set (supteq_list t). the (root l) \<noteq> the (root u) \<longrightarrow> \<not> matches u l"
  shows
    "(\<forall>l\<in>set ls. \<forall>u\<in>set (supteq_list t). \<not> matches u l) \<longleftrightarrow>
     (\<forall>u\<in>set (supteq_list t). \<forall>l\<in>set (term_map ls (the (root u))).
       \<not> matches u l)"
    (is "?lhs \<longleftrightarrow> ?rhs" is "_ \<longleftrightarrow> (\<forall>u\<in>set ?subs. \<forall>l\<in>set (?ls u). \<not> matches u l)")
proof (intro iffI ballI)
  fix u l assume "\<forall>l\<in>set ls. \<forall>u\<in>set ?subs. \<not> matches u l" and "u \<in> set ?subs"
    and "l \<in> set (?ls u)"
  then show "\<not> matches u l"
    using elem_list_to_rm.rm_set_lookup[of "the \<circ> root" ls "the (root u)"]
    by (auto simp: o_def term_map_def rm_set_lookup_def)
next
  fix l u assume 1: "\<forall>u\<in>set ?subs. \<forall>l\<in>set (?ls u). \<not> matches u l"
    and "l \<in> set ls" and "u \<in> set ?subs"
  with assms have "the (root l) \<noteq> the (root u) \<longrightarrow> \<not> matches u l"
    and "\<forall>l\<in>set (?ls u). \<not> matches u l " by simp+
  with elem_list_to_rm.rm_set_lookup[of "the \<circ> root" ls "the (root u)"]
    and \<open>l \<in> set ls\<close>
  show "\<not> matches u l" by (auto simp: o_def term_map_def rm_set_lookup_def)
qed

lemma supteq_list_ex:
  "(\<exists>u\<in>set (supteq_list l). \<exists>\<sigma>. t \<cdot> \<sigma> = u) \<longleftrightarrow> (\<exists>\<sigma>. l \<unrhd> t \<cdot> \<sigma>)"
  unfolding supteq_list by auto

definition "is_NF_trs R = is_NF_main (\<exists>r\<in>set R. is_Var (fst r)) (R = []) (term_map (map fst R))"
definition "is_NF_terms Q = is_NF_main (\<exists>q\<in>set Q. is_Var q) (Q = []) (term_map Q)"

lemma is_NF_main_NF_trs_conv:
  "is_NF_main (\<exists>r\<in>set R. is_Var (fst r)) (R = []) (term_map (map fst R)) t \<longleftrightarrow>
    t \<in> NF_trs (set R)"
  (is "is_NF_main ?var ?R ?map t \<longleftrightarrow> _")
proof (intro iffI allI)
  assume is_NF_main: "is_NF_main ?var ?R ?map t"
  show "t \<in> NF_trs (set R)"
  proof (cases "\<exists>r\<in>set R. is_Var (fst r)")
    case True with is_NF_main[unfolded is_NF_main_def] show ?thesis by simp
  next
    case False
    let ?ts = "map fst R"
    from False have allfun: "\<forall>s\<in>set ?ts. is_Fun s" by simp
    with neq_root_no_match
    have no_match: "\<forall>s\<in>set ?ts. \<forall>u\<in>set (supteq_list t). the (root s) \<noteq> the (root u)
        \<longrightarrow> \<not> matches u s" by blast
    note is_NF_main = is_NF_main[unfolded is_NF_main_def if_not_P[OF False]]
    show ?thesis
    proof (cases "R = []")
      case False
      then have False: "(R = []) = False" by simp
      have "\<forall>u\<in>set (supteq_list t). \<forall>l\<in>set (term_map ?ts (the (root u))). \<not> matches u l"
      proof
        fix u
        assume mem: "u \<in> set (supteq_list t)"
        show "\<forall>l\<in>set (term_map ?ts (the (root u))). \<not> matches u l"
        proof (cases u)
          case (Var x)
          show ?thesis
          proof
            fix l
            assume "l \<in> set (term_map ?ts (the (root u))) "
            with elem_list_to_rm.rm_set_lookup[of "the \<circ> root" ?ts "the (root u)"]
            have "l \<in> set ?ts" by (auto simp: o_def term_map_def rm_set_lookup_def)
            then have "is_Fun l" using allfun by auto
            then have "(\<forall>\<sigma>. l \<cdot> \<sigma> \<noteq> u)" using Var by auto
            then show "\<not> matches u l" using matches_iff by blast
          qed
        next
          case (Fun f us)
          with mem is_NF_main[unfolded False] show ?thesis by auto
        qed
      qed
      then show ?thesis
        unfolding efficient_supteq_list_do_not_match[OF no_match, symmetric]
        unfolding all_not_conv matches_iff
        unfolding supteq_list_ex by auto
    qed auto
  qed
next
  assume NF_trs: "t \<in> NF_trs (set R)"
  show "is_NF_main (\<exists>r\<in>set R. is_Var (fst r)) (R = []) (term_map (map fst R)) t"
  proof (cases "\<exists>r\<in>set R. is_Var (fst r)")
    case True
    then obtain l where "l \<in> lhss (set R)" and "is_Var l" by auto
    from lhs_var_not_NF[OF this] and NF_trs show ?thesis by simp
  next
    case False note oFalse = this
    let ?ts = "map fst R"
    from False have "\<forall>s\<in>set ?ts. is_Fun s" by auto
    with neq_root_no_match
    have
      no_match: "\<forall>s\<in>set ?ts. \<forall>u\<in>set (supteq_list t). the (root s) \<noteq> the (root u)
      \<longrightarrow> \<not> matches u s" by blast
    show ?thesis
    proof (cases "R = []")
      case True then show ?thesis unfolding is_NF_main_def by auto
    next
      case False
      then have False: "(R = []) = False" by simp
      from NF_trs
      show ?thesis
        unfolding is_NF_main_def False if_False if_not_P[OF oFalse]
        using efficient_supteq_list_do_not_match[OF no_match, symmetric]
        unfolding all_not_conv matches_iff
        unfolding supteq_list_ex set_map by fastforce
    qed
  qed
qed

lemma is_NF_trs [simp]:
  "is_NF_trs R = (\<lambda> t. t \<in> NF_trs (set R))"
  by (rule ext, unfold is_NF_trs_def is_NF_main_NF_trs_conv, simp)

lemma is_NF_terms [simp]:
  "is_NF_terms Q = (\<lambda> t. t \<in> NF_terms (set Q))"
proof (rule ext)
  fix t
  let ?Q = "map (\<lambda>t. (t, t)) Q"
  have 1: "(\<exists>t\<in>set Q. is_Var t) = (\<exists>t\<in>set ?Q. is_Var (fst t))"
    by (induct Q) (auto simp: o_def)
  have 2: "map fst ?Q = Q" by (induct Q) simp_all
  have 3: "term_map Q = term_map (map fst ?Q)" unfolding 2 ..
  have 4: "set ?Q = Id_on (set Q)" by (induct Q) (auto simp: o_def)
  from is_NF_main_NF_trs_conv[of "?Q" t]
  show "is_NF_terms Q t = (t \<in> NF_terms (set Q))"
    unfolding is_NF_terms_def 1 3 4 unfolding 2 by auto
qed

subsubsection\<open>Grouping TRS-Rules by Function Symbols\<close>


type_synonym ('f,'v)rule_map = "(('f \<times> nat) \<Rightarrow> ('f,'v)rules)option"


fun computeRuleMapH :: "('f,'v)rules \<Rightarrow> (('f \<times> nat) \<times> ('f,'v)rules)list option"
  where "computeRuleMapH [] = Some []"
  | "computeRuleMapH ((Fun f ts,r) # rules) = (let n = length ts in case computeRuleMapH rules of None \<Rightarrow> None | Some rm \<Rightarrow> 
            (case List.extract (\<lambda> (fa,rls). fa = (f,n)) rm of 
                None \<Rightarrow> Some (((f,n), [(Fun f ts,r)]) # rm)
              | Some (bef,(fa,rls),aft) \<Rightarrow>  Some  ((fa,(Fun f ts,r) # rls) # bef @ aft)))"
  | "computeRuleMapH ((Var _, _) # rules) = None"

definition computeRuleMap :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rule_map" where
  "computeRuleMap rls \<equiv>
    (case computeRuleMapH rls of
      None \<Rightarrow> None
    | Some rm \<Rightarrow> Some (\<lambda>f.
      (case map_of rm f of
        None \<Rightarrow> []
      | Some rls \<Rightarrow> rls)))"

lemma computeRuleMapHSound2: "(computeRuleMapH R = None) = (\<exists> (l, r) \<in> set R. root l = None)"
proof (induct R)
  case (Cons rule rules)
  obtain l r where rule: "rule = (l,r)" by force
  show ?case 
  proof (cases l)
    case (Fun f ts)
    show ?thesis
      using rule Cons
    proof (cases "computeRuleMapH rules")
      case (Some rm) note oSome = this
      let ?e = "List.extract (\<lambda> (fa,rls). fa = (f,length ts)) rm"
      from Some Fun rule Cons show ?thesis 
      proof (cases ?e)
        case (Some res)
        then obtain bef aft g rls where "?e = Some (bef, (g,rls), aft)" by (cases res, force) 
        with extract_SomeE[OF this] have rm: "rm = bef @ ((f, length ts),rls) # aft" and e: "?e = Some (bef, ((f,length ts),rls), aft)"
          by auto
        show ?thesis using Cons
          by (simp add: rule Fun Let_def oSome e)
      qed auto
    qed (insert, auto simp: rule Fun)
  qed (auto simp: rule)
qed (auto simp: rule)

lemma computeRuleMapSound2: "(computeRuleMap R = None) = (\<exists> (l, r) \<in> set R. root l = None)"
  unfolding computeRuleMap_def
  by (simp only: computeRuleMapHSound2[symmetric], cases "computeRuleMapH R", auto)


lemma computeRuleMapHSound: assumes "computeRuleMapH R = Some rm"
  shows "(\<lambda> (f,rls). (f,set rls)) ` set rm = {((f,n),{(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)}) | f n. {(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)} \<noteq> {}} \<and> distinct_eq (\<lambda> (f,rls) (g,rls'). f = g) rm"
  using assms
proof (induct R arbitrary: rm)
  case (Cons rule rules)
  let ?setl = "\<lambda> rm. (\<lambda> (f,rls). (f,set rls)) ` set rm"
  let ?setr = "\<lambda> R. {((f,n),{(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)}) | f n. {(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)} \<noteq> {}}"
  obtain l r where Pair: "rule = (l,r)" by force
  show ?case
  proof (cases l)
    case (Var v)
    with Cons Pair show ?thesis by simp
  next
    case (Fun f ts)
    with Cons Pair show ?thesis 
    proof (cases "computeRuleMapH rules")
      case (Some rrm) note oSome = this
      let ?dis = "distinct_eq (\<lambda> (f,rls) (g,rls'). f = g)"
      from Cons(1)[OF Some] have drrm: "?dis rrm" and srrm: "?setl rrm = ?setr rules" by auto
      show ?thesis
      proof (cases "List.extract (\<lambda> (fa,rls). fa = (f,length ts)) rrm")
        case None
        let ?e = "((f,length ts), [(Fun f ts,r)])"
        let ?e' = "((f,length ts), {(Fun f ts,r)})"
        from None Cons(2) have rm: "rm = ?e # rrm" by (simp add: Fun Pair Some None)
        from None[unfolded extract_None_iff] have rrm: "\<And> g n rl. ((g,n),rl) \<in> set rrm \<Longrightarrow> (f,length ts) \<noteq> (g,n)" by auto
        then have rrm': "\<And> g n rl. ((g,n),rl) \<in> ?setr rules \<Longrightarrow> (f,length ts) \<noteq> (g,n)" by (simp only: srrm[symmetric], auto)
        then have  id: " {(Fun f ts, r)} = {(l, ra). (l = Fun f ts \<and> ra = r \<or> (l, ra) \<in> set rules) \<and> root l = Some (f, length ts)}"  by force
        from rrm have dis: "?dis rm" 
          by (simp add: rm drrm, auto)
        have "?setl rm = insert ?e' (?setl rrm)" by (simp add: rm)
        also have "\<dots> = insert ?e' (?setr rules)" by (simp add: srrm)
        also have "\<dots> = ?setr ( (Fun f ts,r) # rules)" 
        proof (rule set_eqI, clarify)
          fix g n rls
          show "(((g,n),rls) \<in> insert ?e' (?setr rules)) = (((g,n),rls) \<in> ?setr ((Fun f ts,r) # rules))"
          proof (cases "(g,n) = (f,length ts)")
            case False
            then have "(((g,n),rls) \<in> insert ?e' (?setr rules)) = (((g,n),rls) \<in> ?setr rules)" by auto
            also have "\<dots> = (((g,n),rls) \<in> ?setr ((Fun f ts,r) # rules))" using False by auto
            finally show ?thesis .
          next
            case True note oTrue = this
            show ?thesis 
            proof (cases "rls = {(Fun f ts, r)}")
              case True
              with oTrue show ?thesis by (simp add: id, force)
            next
              case False
              show ?thesis using rrm'[of g n rls] True False by (simp add: False True id, auto)
            qed
          qed
        qed
        finally show ?thesis
          by (simp only: dis drrm, simp add: Pair Fun)
      next
        case (Some res)
        obtain bef fg rls aft where "res = (bef,(fg,rls),aft)" by (cases res, force)
        from extract_SomeE[OF Some[simplified this]] Some[simplified this] have rrm: "rrm = bef @ ((f,length ts), rls) # aft" 
          and e: "List.extract (\<lambda> (fa, rls). fa = (f,length ts)) rrm = Some (bef, ((f,length ts),rls),aft)" by auto
        let ?e = "((f,length ts), (Fun f ts,r) # rls)"
        let ?e' = "((f,length ts), insert (Fun f ts,r) (set rls))"
        have "((f,length ts),set rls) \<in> ?setl rrm" unfolding rrm by auto
        then have rls: "set rls = {(l, r) |l r. (l, r) \<in> set rules \<and> root l = Some (f, length ts)}" using Cons(1)[OF oSome] by auto
        obtain ba where ba: "ba = bef @ aft" by auto
        from Cons(2) e ba have rm: "rm = ?e # ba" by (simp add: Fun Pair oSome e)
        from drrm[simplified rrm] have dis: "?dis ba"  unfolding distinct_eq_append ba by auto
        from drrm[simplified rrm] have dis: "?dis rm" unfolding rm distinct_eq_append ba by (auto simp: dis[simplified ba])
        from drrm[simplified rrm distinct_eq_append] 
        have diff: "(\<forall>x\<in>set ba. \<not> (\<lambda>(g, rls). (f,length ts) = g) x)" by (auto simp: ba)
        have "?setl [((f, length ts),rls)] \<union> ?setl ba = ?setl rrm" using rrm ba by auto
        also have "\<dots> = ?setr rules" by (rule srrm)
        finally have id: "?setl [((f, length ts),rls)] \<union> ?setl ba = ?setr rules" .          
        have "?setl rm = insert ?e' (?setl ba)" by (simp add: rm)
        also have "\<dots> = ?setr ((Fun f ts,r) # rules)" 
        proof (rule set_eqI, clarify)
          fix g n rl 
          show "(((g,n),rl) \<in> insert ?e' (?setl ba)) = (((g,n),rl) \<in> ?setr ((Fun f ts,r) # rules))"
          proof (cases "(g,n) = (f,length ts)")
            case False 
            then have "(((g,n),rl) \<in> insert ?e' (?setl ba)) = (((g,n),rl) \<in> ?setl ba)" by auto
            also have "\<dots> = (((g,n),rl) \<in> ?setr rules)" using False by (simp only: id[symmetric], auto)
            also have "\<dots> = (((g,n),rl) \<in> ?setr ((Fun f ts,r) # rules))" using False by auto
            finally show ?thesis .
          next
            case True note oTrue = this
            show ?thesis 
            proof (cases "rl = insert (Fun f ts, r) (set rls)")
              case True
              then have "(((g,n),rl) \<in> insert ?e' (?setl ba)) = True" using oTrue by auto
              also have "\<dots> = (((g,n),rl) \<in> ?setr ((Fun f ts,r) # rules))" unfolding True rls using oTrue by force
              finally show ?thesis .
            next
              case False
              then have "(((g,n),rl) \<in> insert ?e' (?setl ba)) = False" using diff by (simp add: True, auto)
              also have "\<dots> = (((g,n),rl) \<in> ?setr ((Fun f ts,r) # rules))" 
              proof (rule ccontr)
                assume "\<not> ?thesis"
                with True have "((f,length ts),rl) \<in> ?setr ((Fun f ts,r) # rules)" by simp
                then have "rl = {(l, ra) |l ra. (l, ra) \<in> set ((Fun f ts, r) # rules) \<and> root l = Some (f, length ts)}" by simp
                with False rls show False by auto
              qed                              
              finally show ?thesis .
            qed
          qed
        qed
        also have "\<dots> = ?setr (rule # rules)" by (simp add: Pair Fun)
        finally show ?thesis by (simp add: dis)
      qed
    qed simp
  qed
qed force

lemma computeRuleMapSound:
  assumes "computeRuleMap R = Some rm" 
  shows "(set (rm (f,n))) = {(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)}"
proof (cases "computeRuleMapH R")
  case None
  then show ?thesis using assms unfolding computeRuleMap_def by auto
next
  case (Some rrm)
  note rrm = computeRuleMapHSound[OF this] 
  note rm = assms[unfolded computeRuleMap_def, simplified Some, simplified, symmetric]
  show ?thesis
  proof (cases "map_of rrm (f, n)")
    case (Some rls)
    from map_of_SomeD[OF this] have "((f,n),set rls) \<in> (\<lambda> (f,rls). (f, set rls)) ` set rrm"
      by auto
    then have "set rls = {(l,r) | l r. (l,r) \<in> set R \<and> root l = Some (f, n)}"
      by (simp only: rrm, simp) 
    then show ?thesis by (simp add: rm Some)
  next
    case None
    have id: "{(l, r) |l r. (l, r) \<in> set R \<and> root l = Some (f, n)} = {}" (is "?set = {}")
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain l r where "(l, r) \<in> set R \<and> root l = Some (f, n)" by auto
      with rrm have "(((f,n), ?set)) \<in> (\<lambda> (f,rls). (f, set rls)) ` set rrm" by auto
      with None[unfolded map_of_eq_None_iff] show False by force
    qed
    then show ?thesis by (simp only: rm None id, auto)
  qed
qed



lemma computeRuleMap_left_vars:
  shows "(computeRuleMap R \<noteq> None) = (\<forall> lr \<in> set R. \<forall> x. fst lr \<noteq> Var x)"
proof (cases "computeRuleMap R")
  case None
  from None computeRuleMapSound2 have "\<exists> (l,r) \<in> set R. root l = None" by auto
  from this obtain l r where "(l,r) \<in> set R \<and> root l = None" by auto
  from this have "(l,r) \<in> set R \<and> \<not> (\<forall> x. fst (l,r) \<noteq> Var x)" by (cases l, auto)
  with None show ?thesis by blast
next
  case (Some rm)
  then have left: "computeRuleMap R \<noteq> None" by auto
  from Some computeRuleMapSound2 have "\<forall> (l,r) \<in> set R. root l \<noteq> None" by force
  then have "\<forall> lr \<in> set R. \<forall> x. fst lr \<noteq> Var x" by auto
  with left show ?thesis by blast
qed

lemma computeRuleMap_defined: fixes R :: "('f,'v)rules"
  assumes "computeRuleMap R = Some rm"
  shows "(rm (f,n) = []) = (\<not> defined (set R) (f,n))"
proof -
  from assms computeRuleMapSound have rm: "\<And>(f::'f) n. set (rm (f,n)) = {(l,r) | l r. (l, r) \<in> set R \<and> root l = Some (f, n)}" by force
  show ?thesis
  proof (cases "rm (f,n)")
    case Nil
    with rm have "\<not> defined (set R) (f,n)" unfolding defined_def by force
    with Nil show ?thesis by blast
  next
    case (Cons lr RR)
    then have left: "rm (f,n) \<noteq> []" by auto
    from Cons rm[where f = f and n = n] have "defined (set R) (f,n)" unfolding defined_def by (cases lr, force)
    with left show ?thesis by blast
  qed
qed


lemma computeRuleMap_None_not_SN:
  assumes "computeRuleMap R = None"
  shows "\<not> SN_on (rstep (set R)) {t}"
proof -
  from assms computeRuleMap_left_vars[of R] obtain x r where "(Var x,r) \<in> set R" by auto
  from left_var_imp_not_SN[OF this] show ?thesis .
qed

end