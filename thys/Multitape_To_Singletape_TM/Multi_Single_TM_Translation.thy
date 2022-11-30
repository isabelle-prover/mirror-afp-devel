section \<open>Translating Multitape TMs to Singletape TMs\<close>

text \<open>In this section we define the mapping from a multitape Turing machine to a singletape
       Turing machine. We further define soundness of the translation via several relations
      which establish a connection between configurations of both kinds of Turing machines.

  The translation works both for deterministic and non-deterministic TMs. Moreover,
  we verify a quadratic overhead in runtime. 
\<close>

(* potential extension: add right-end marker, so that final phase can write original symbols of first tape onto tape, i.e.
   replace tuple-symbols by original symbols; this could be useful if TMs with output are considered, i.e., 
   where functions need to be computed *)

theory Multi_Single_TM_Translation
  imports  
    Multitape_TM
    Singletape_TM
    STM_Renaming
begin

subsection \<open>Definition of the Translation\<close>

datatype 'a tuple_symbol = NO_HAT "'a" | HAT "'a"
datatype ('a, 'k) st_tape_symbol = ST_LE ("\<turnstile>") | TUPLE "'k \<Rightarrow> 'a tuple_symbol" | INP "'a"
datatype 'a sym_or_bullet = SYM "'a" | BULLET ("\<bullet>")

datatype ('a,'q,'k) st_states = 
  R\<^sub>1 "'a sym_or_bullet" |
  R\<^sub>2 |
  S\<^sub>0 'q |
  S  "'q" "'k \<Rightarrow> 'a sym_or_bullet" |
  S\<^sub>1  "'q" "'k \<Rightarrow> 'a" |
  E\<^sub>0  "'q" "'k \<Rightarrow> 'a" "'k \<Rightarrow> dir" |
  E  "'q" "'k \<Rightarrow> 'a sym_or_bullet" "'k \<Rightarrow> dir" |
  Er "'q" "'k \<Rightarrow> 'a sym_or_bullet" "'k \<Rightarrow> dir" "'k set" |
  El "'q" "'k \<Rightarrow> 'a sym_or_bullet" "'k \<Rightarrow> dir" "'k set" |
  Em "'q" "'k \<Rightarrow> 'a sym_or_bullet" "'k \<Rightarrow> dir" "'k set"

type_synonym ('a,'q,'k)mt_rule = "'q \<times> ('k \<Rightarrow> 'a) \<times> 'q \<times> ('k \<Rightarrow> 'a) \<times> ('k \<Rightarrow> dir)" 

context multitape_tm
begin

definition R1_Set where "R1_Set = SYM ` \<Sigma> \<union> {\<bullet>}" 

definition gamma_set :: "('k \<Rightarrow> 'a tuple_symbol) set" where
  "gamma_set = (UNIV :: 'k set) \<rightarrow> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>" 

definition \<Gamma>' :: "('a, 'k) st_tape_symbol set" where 
  "\<Gamma>' = TUPLE ` gamma_set \<union> INP ` \<Sigma> \<union> {\<turnstile>}" 

definition "func_set = (UNIV :: 'k set) \<rightarrow> SYM ` \<Gamma> \<union> {\<bullet>}" 

definition blank' :: "('a, 'k) st_tape_symbol" where "blank' = TUPLE (\<lambda> _. NO_HAT blank)" 
definition hatLE' :: "('a, 'k) st_tape_symbol" where "hatLE' = TUPLE (\<lambda> _. HAT LE)" 
definition encSym :: "'a \<Rightarrow> ('a, 'k) st_tape_symbol" where "encSym a = (TUPLE (\<lambda> i. if i = 0 then NO_HAT a else NO_HAT blank))" 

definition add_inp :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet) \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet)" where
  "add_inp inp inp2 = (\<lambda> k. case inp k of HAT s \<Rightarrow> SYM s | _ \<Rightarrow> inp2 k)" 

definition project_inp :: "('k \<Rightarrow> 'a sym_or_bullet) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "project_inp inp = (\<lambda> k. case inp k of SYM s \<Rightarrow> s)" 

definition compute_idx_set :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet)  \<Rightarrow> 'k set" where
  "compute_idx_set tup ys = {i . tup i \<in> HAT ` \<Gamma> \<and> ys i \<in> SYM ` \<Gamma>}"

definition update_ys :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet)  \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet)" where
  "update_ys tup ys = (\<lambda> k. if k \<in> (compute_idx_set tup ys) then \<bullet> else ys k)"

definition replace_sym :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> 'a sym_or_bullet)  \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol)" where
  "replace_sym tup ys = (\<lambda> k. if k \<in> (compute_idx_set tup ys) 
                              then (case ys k of SYM a \<Rightarrow> NO_HAT a) 
                              else tup k)"

definition place_hats_to_dir :: "dir \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> dir) \<Rightarrow>'k set \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol)" where
  "place_hats_to_dir dir tup ds I = (\<lambda> k. (case tup k of 
                                      NO_HAT a \<Rightarrow> if k \<in> I \<and> ds k = dir 
                                                  then HAT a
                                                  else NO_HAT a 
                                      | HAT a \<Rightarrow> HAT a )) "

definition place_hats_R :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> dir) \<Rightarrow>'k set \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol)" where
  "place_hats_R = place_hats_to_dir dir.R"

definition place_hats_M :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> dir) \<Rightarrow>'k set \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol)" where
  "place_hats_M = place_hats_to_dir dir.N"

definition place_hats_L :: "('k \<Rightarrow> 'a tuple_symbol) \<Rightarrow> ('k \<Rightarrow> dir) \<Rightarrow>'k set \<Rightarrow> ('k \<Rightarrow> 'a tuple_symbol)" where
  "place_hats_L = place_hats_to_dir dir.L"

definition \<delta>' :: 
  "(('a, 'q, 'k) st_states \<times> ('a, 'k) st_tape_symbol \<times> ('a, 'q, 'k) st_states \<times> ('a, 'k) st_tape_symbol \<times> dir)set"  
  where
    "\<delta>' = ({(R\<^sub>1 \<bullet>, \<turnstile>, R\<^sub>1 \<bullet>, \<turnstile>, dir.R)}) 
    \<union> (\<lambda> x. (R\<^sub>1 \<bullet>, INP x, R\<^sub>1 (SYM x), hatLE', dir.R)) ` \<Sigma>
    \<union> (\<lambda> (a,x). (R\<^sub>1 (SYM a), INP x, R\<^sub>1 (SYM x), encSym a, dir.R)) ` (\<Sigma> \<times> \<Sigma>)
    \<union> {(R\<^sub>1 \<bullet>, blank', R\<^sub>2, hatLE', dir.L)}
    \<union> (\<lambda> a. (R\<^sub>1 (SYM a), blank', R\<^sub>2, encSym a, dir.L)) ` \<Sigma>
    \<union> (\<lambda> x. (R\<^sub>2, x, R\<^sub>2, x, dir.L)) ` (\<Gamma>' - { \<turnstile> })
    \<union> {(R\<^sub>2, \<turnstile>, S\<^sub>0 s, \<turnstile>, dir.N)}
    \<union> (\<lambda> q. (S\<^sub>0 q, \<turnstile>, S q (\<lambda> _. \<bullet>), \<turnstile>, dir.R)) ` (Q - {t,r})
    \<union> (\<lambda> (q,inp,t). (S q inp, TUPLE t, S q (add_inp t inp), TUPLE t, dir.R)) ` (Q \<times> (func_set - (UNIV \<rightarrow> SYM ` \<Gamma>)) \<times> gamma_set)
    \<union> (\<lambda> (q,inp,a). (S q inp, a, S\<^sub>1 q (project_inp inp), a, dir.L)) ` (Q \<times> (UNIV \<rightarrow> SYM ` \<Gamma>) \<times> (\<Gamma>' - { \<turnstile> }))
    \<union> (\<lambda> ((q,a,q',b,d),t). (S\<^sub>1 q a, t, E\<^sub>0 q' b d, t, dir.N)) ` (\<delta> \<times> \<Gamma>')
    \<union> (\<lambda> ((q,a,d),t). (E\<^sub>0 q a d, t, E q (SYM o a) d, t, dir.N)) ` ((Q \<times> (UNIV \<rightarrow> \<Gamma>) \<times> UNIV) \<times> \<Gamma>')
    \<union> (\<lambda> (q,d). (E q (\<lambda> _. \<bullet>) d, \<turnstile>, S\<^sub>0 q, \<turnstile>, dir.N)) ` (Q \<times> UNIV)
    \<union> (\<lambda> (q,ys,ds,t).   (E  q ys ds,   TUPLE t, Er q (update_ys t ys) ds (compute_idx_set t ys), TUPLE(replace_sym t ys), dir.R)) ` (Q \<times> func_set \<times> UNIV \<times> gamma_set)
    \<union> (\<lambda> (q,ys,ds,I,t). (Er q ys ds I, TUPLE t, Em q ys ds I, TUPLE (place_hats_R t ds I), dir.L)) ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set)
    \<union> (\<lambda> (q,ys,ds,I,t). (Em q ys ds I, TUPLE t, El q ys ds I, TUPLE (place_hats_M t ds I), dir.L)) ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set)
    \<union> (\<lambda> (q,ys,ds,I,t). (El q ys ds I, TUPLE t, E  q ys ds,   TUPLE (place_hats_L t ds I), dir.N)) ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set)
    \<union> (\<lambda> (q,ys,ds,I).   (El q ys ds I, \<turnstile>, E q ys ds, \<turnstile>, dir.N)) ` (Q \<times> func_set \<times> UNIV \<times> Pow(UNIV)) \<comment> \<open> first switch into E state, so E phase is always finished in E state\<close>
  "

definition "Q' = 
  R\<^sub>1 ` R1_Set \<union> {R\<^sub>2} \<union> 
  S\<^sub>0 ` Q \<union> (\<lambda> (q,inp). S q inp) ` (Q \<times> func_set) \<union> (\<lambda> (q,a). S\<^sub>1 q a) ` (Q \<times> (UNIV \<rightarrow> \<Gamma>)) \<union>
  (\<lambda> (q,a,d). E\<^sub>0 q a d) ` (Q \<times> (UNIV \<rightarrow> \<Gamma>) \<times> UNIV) \<union> 
  (\<lambda> (q,a,d). E q a d) ` (Q \<times> func_set \<times> UNIV) \<union>
  (\<lambda> (q,a,d,I). Er q a d I) ` (Q \<times> func_set \<times> UNIV \<times> UNIV) \<union>
  (\<lambda> (q,a,d,I). Em q a d I) ` (Q \<times> func_set \<times> UNIV \<times> UNIV) \<union>
  (\<lambda> (q,a,d,I). El q a d I) ` (Q \<times> func_set \<times> UNIV \<times> UNIV)"

lemma compute_idx_range[simp,intro]:
  assumes "tup \<in> gamma_set"
  assumes "ys \<in> func_set"
  shows "compute_idx_set tup ys \<in> UNIV"
  by auto

lemma update_ys_range[simp,intro]:
  assumes "tup \<in> gamma_set"
  assumes "ys \<in> func_set"
  shows "update_ys tup ys \<in> func_set"
  by (insert assms, fastforce simp: update_ys_def func_set_def)

lemma replace_sym_range[simp,intro]:
  assumes "tup \<in> gamma_set"
  assumes "ys \<in> func_set"
  shows "replace_sym tup ys \<in> gamma_set"
proof -
  have "\<forall> k. (if k \<in> compute_idx_set tup ys then case ys k of SYM x \<Rightarrow> NO_HAT x else tup k) \<in> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>"
    by(intro allI, insert assms, cases "k \<in> compute_idx_set tup ys", auto simp: func_set_def compute_idx_set_def gamma_set_def replace_sym_def)
  then show ?thesis
    using assms unfolding replace_sym_def gamma_set_def by blast
qed

lemma tup_hat_content:
  assumes "tup \<in> gamma_set"
  assumes "tup x = HAT a"
  shows "a \<in> \<Gamma>"
proof - 
  have "range tup \<subseteq> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>" 
    using assms gamma_set_def by auto
  then show ?thesis 
    using assms(2)
    by (metis UNIV_I Un_iff image_iff image_subset_iff tuple_symbol.distinct(1) tuple_symbol.inject(2))
qed

lemma tup_no_hat_content:
  assumes "tup \<in> gamma_set"
  assumes "tup x = NO_HAT a"
  shows "a \<in> \<Gamma>"
proof - 
  have "range tup \<subseteq> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>" 
    using assms gamma_set_def by auto
  then show ?thesis 
    using assms(2)
    by (metis UNIV_I Un_iff image_iff image_subset_iff tuple_symbol.inject(1) tuple_symbol.simps(4))
qed

lemma place_hats_to_dir_range[simp, intro]:
  assumes "tup \<in> gamma_set"
  shows "place_hats_to_dir d tup ds I \<in> gamma_set"
proof -
  have "\<forall> k. (case tup k of NO_HAT a \<Rightarrow> if k \<in> I \<and> ds k = d then HAT a else NO_HAT a | HAT x \<Rightarrow> HAT x)
    \<in>  NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>"
  proof 
    fix k 
    show "(case tup k of NO_HAT a \<Rightarrow> if k \<in> I \<and> ds k = d then HAT a else NO_HAT a | HAT x \<Rightarrow> HAT x)
    \<in>  NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>"
      by(cases "tup k", insert tup_hat_content[OF assms(1)] tup_no_hat_content[OF assms(1)], auto simp: gamma_set_def)
  qed
  then show ?thesis
    using assms
    unfolding place_hats_to_dir_def gamma_set_def
    by auto
qed

lemma place_hats_range[simp,intro]:
  assumes "tup \<in> gamma_set"
  shows "place_hats_R tup ds I \<in> gamma_set" and 
    "place_hats_L tup ds I \<in> gamma_set" and 
    "place_hats_M tup ds I \<in> gamma_set"
  by(insert assms, auto simp: place_hats_R_def place_hats_L_def place_hats_M_def)

lemma fin_R1_Set[intro,simp]: "finite R1_Set" 
  unfolding R1_Set_def using fin_\<Sigma> by auto

lemma fin_gamma_set[intro,simp]: "finite gamma_set" 
  unfolding gamma_set_def using fin_\<Gamma> 
  by (intro fin_funcsetI, auto)

lemma fin_\<Gamma>'[intro,simp]: "finite \<Gamma>'" 
  unfolding \<Gamma>'_def using fin_\<Sigma> by auto

lemma fin_func_set[simp,intro]: "finite func_set" 
  unfolding func_set_def using fin_\<Gamma> by auto

lemma memberships[simp,intro]: "\<turnstile> \<in> \<Gamma>'" 
  "\<bullet> \<in> R1_Set" 
  "x \<in> \<Sigma> \<Longrightarrow> SYM x \<in> R1_Set" 
  "x \<in> \<Sigma> \<Longrightarrow> encSym x \<in> \<Gamma>'"
  "blank' \<in> \<Gamma>'" 
  "hatLE' \<in> \<Gamma>'" 
  "x \<in> \<Sigma> \<Longrightarrow> INP x \<in> \<Gamma>'" 
  "y \<in> gamma_set \<Longrightarrow> TUPLE y \<in> \<Gamma>'" 
  "(\<lambda>_. \<bullet>) \<in> func_set" 
  "f \<in> UNIV \<rightarrow> SYM ` \<Gamma> \<Longrightarrow> f \<in> func_set" 
  "g \<in> UNIV \<rightarrow> \<Gamma> \<Longrightarrow> SYM \<circ> g \<in> func_set" 
  "f \<in> UNIV \<rightarrow> SYM ` \<Gamma> \<Longrightarrow> project_inp f k \<in> \<Gamma>" 
  unfolding R1_Set_def \<Gamma>'_def blank'_def hatLE'_def gamma_set_def encSym_def func_set_def project_inp_def
  using LE blank tm funcset_mem[of f UNIV "SYM ` \<Gamma>" k] by (auto split: sym_or_bullet.splits)

lemma add_inp_func_set[simp,intro]: "b \<in> gamma_set \<Longrightarrow> a \<in> func_set \<Longrightarrow> add_inp b a \<in> func_set"
  unfolding func_set_def gamma_set_def
proof
  fix x
  assume a: "a \<in> UNIV \<rightarrow> SYM ` \<Gamma> \<union> {\<bullet>}" and b: "b \<in> UNIV \<rightarrow> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>" 
  from a have a: "a x \<in> SYM ` \<Gamma> \<union> {\<bullet>}" by auto
  from b have b: "b x \<in> NO_HAT ` \<Gamma> \<union> HAT ` \<Gamma>" by auto
  show "add_inp b a x \<in> SYM ` \<Gamma> \<union> {\<bullet>}" using a b
    unfolding add_inp_def by (cases "b x", auto simp: gamma_set_def)
qed


lemma automation[simp]: "\<And> a b A B. (S a b \<in> (\<lambda>x. case x of (x1, x2) \<Rightarrow> S x1 x2) ` (A \<times> B)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B)"
  "\<And> a b A B. (S\<^sub>1 a b \<in> (\<lambda>x. case x of (x1, x2) \<Rightarrow> S\<^sub>1 x1 x2) ` (A \<times> B)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B)"
  "\<And> a b c A B C. (E\<^sub>0 a b c \<in> (\<lambda>x. case x of (x1, x2, x3) \<Rightarrow> E\<^sub>0 x1 x2 x3) ` (A \<times> B \<times> C)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B \<and> c \<in> C)"
  "\<And> a b c A B C. (E a b c \<in> (\<lambda>x. case x of (x1, x2, x3) \<Rightarrow> E x1 x2 x3) ` (A \<times> B \<times> C)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B \<and> c \<in> C)"
  "\<And> a b c d A B C. (Er a b c d \<in> (\<lambda>x. case x of (x1, x2, x3, x4) \<Rightarrow> Er x1 x2 x3 x4) ` (A \<times> B \<times> C)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B \<and> (c,d) \<in> C)"
  "\<And> a b c d A B C. (Em a b c d \<in> (\<lambda>x. case x of (x1, x2, x3, x4) \<Rightarrow> Em x1 x2 x3 x4) ` (A \<times> B \<times> C)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B \<and> (c,d) \<in> C)"
  "\<And> a b c d A B C. (El a b c d \<in> (\<lambda>x. case x of (x1, x2, x3, x4) \<Rightarrow> El x1 x2 x3 x4) ` (A \<times> B \<times> C)) \<longleftrightarrow> (a \<in> A \<and> b \<in> B \<and> (c,d) \<in> C)"
  "blank' \<noteq> \<turnstile>" 
  "\<turnstile> \<noteq> blank'" 
  "blank' \<noteq> INP x" 
  "INP x \<noteq> blank'" 
  by (force simp: blank'_def)+

interpretation st: singletape_tm Q' "(INP ` \<Sigma>)" \<Gamma>' blank' \<turnstile> \<delta>' "R\<^sub>1 \<bullet>" "S\<^sub>0 t" "S\<^sub>0 r"
proof 
  show "finite Q'" 
    unfolding Q'_def using fin_Q fin_\<Gamma>
    by (intro finite_UnI finite_imageI finite_cartesian_product, auto)
  show "finite \<Gamma>'" by (rule fin_\<Gamma>')
  show "S\<^sub>0 t \<in> Q'" unfolding Q'_def using tQ by auto
  show "S\<^sub>0 r \<in> Q'" unfolding Q'_def using rQ by auto
  show "S\<^sub>0 t \<noteq> S\<^sub>0 r" using tr by auto
  show "blank' \<notin> INP ` \<Sigma>" unfolding blank'_def by auto
  show "R\<^sub>1 \<bullet> \<in> Q'" unfolding Q'_def by auto
  show "\<delta>' \<subseteq> (Q' - {S\<^sub>0 t, S\<^sub>0 r}) \<times> \<Gamma>' \<times> Q' \<times> \<Gamma>' \<times> UNIV" 
    unfolding \<delta>'_def Q'_def using tm
    by (auto dest: \<delta>)
  show "(q, \<turnstile>, q', a', d) \<in> \<delta>' \<Longrightarrow> a' = \<turnstile> \<and> d \<in> {dir.N, dir.R}" for q q' a' d
    unfolding \<delta>'_def by (auto simp: hatLE'_def blank'_def)
qed auto

lemma valid_st: "singletape_tm Q' (INP ` \<Sigma>) \<Gamma>' blank' \<turnstile> \<delta>' (R\<^sub>1 \<bullet>) (S\<^sub>0 t) (S\<^sub>0 r)" ..

text \<open>Determinism is preserved.\<close>

lemma det_preservation: "deterministic \<Longrightarrow> st.deterministic" 
  unfolding deterministic_def st.deterministic_def unfolding \<delta>'_def
  by auto


subsection \<open>Soundness of the Translation\<close>

lemma range_mt_pos: 
  "\<exists> i. Max (range (mt_pos cm)) = mt_pos cm i" 
  "finite (range (mt_pos (cm :: ('a, 'q, 'k) mt_config)))" 
  "range (mt_pos cm) \<noteq> {}"
proof -
  show "finite (range (mt_pos cm))" by auto
  moreover show "range (mt_pos cm) \<noteq> {}" by auto
  ultimately show "\<exists> i. Max (range (mt_pos cm)) = mt_pos cm i"
    by (meson Max_in imageE)
qed

lemma max_mt_pos_step: assumes "(cm,cm') \<in> step" 
  shows "Max (range (mt_pos cm')) \<le> Suc (Max (range (mt_pos cm)))" 
proof -
  from range_mt_pos(1)[of cm'] obtain i'
    where max1: "Max (range (mt_pos cm')) = mt_pos cm' i'" by auto
  hence "Max (range (mt_pos cm')) \<le> mt_pos cm' i'" by auto
  also have "\<dots> \<le> Suc (mt_pos cm i')" using assms
  proof (cases)
    case (step q ts n q' a dir)
    then show ?thesis by (cases "dir i'", auto)
  qed
  also have "\<dots> \<le> Suc (Max (range (mt_pos cm)))" using range_mt_pos[of cm] by simp
  finally show ?thesis .
qed

lemma max_mt_pos_init: "Max (range (mt_pos (init_config w))) = 0" 
  unfolding init_config_def by auto

lemma INP_D: assumes "set x \<subseteq> INP ` \<Sigma>" 
  shows "\<exists> w. x = map INP w \<and> set w \<subseteq> \<Sigma>" 
  using assms 
proof (induct x)
  case (Cons x xs)
  then obtain w where "xs = map INP w \<and> set w \<subseteq> \<Sigma>" by auto
  moreover from Cons(2) obtain a where "x = INP a" and "a \<in> \<Sigma>" by auto
  ultimately show ?case by (intro exI[of _ "a # w"], auto)
qed auto


subsubsection \<open>R-Phase\<close>

fun enc :: "('a, 'q, 'k) mt_config \<Rightarrow> nat \<Rightarrow> ('a, 'k) st_tape_symbol"
  where "enc (Config\<^sub>M q tc p) n = TUPLE (\<lambda> k. if p k = n then HAT (tc k n) else NO_HAT (tc k n))"

inductive rel_R\<^sub>1 :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where 
  "n = length w \<Longrightarrow> 
  tc' 0 = \<turnstile> \<Longrightarrow> 
  p' \<le> n \<Longrightarrow> 
  (\<And> i. i < p' \<Longrightarrow> enc (init_config w) i = tc' (Suc i)) \<Longrightarrow>
  (\<And> i. i \<ge> p' \<Longrightarrow> tc' (Suc i) = (if i < n then INP (w ! i) else blank')) \<Longrightarrow>
  (p' = 0 \<Longrightarrow> q' = \<bullet>) \<Longrightarrow>
  (\<And> p. p' = Suc p \<Longrightarrow> q' = SYM (w ! p)) \<Longrightarrow>
  rel_R\<^sub>1 (Config\<^sub>S (R\<^sub>1 q') tc' (Suc p')) w p'" 


lemma rel_R\<^sub>1_init: shows "\<exists> cs1. (st.init_config (map INP w), cs1) \<in> st.dstep \<and> rel_R\<^sub>1 cs1 w 0" 
proof -
  let ?INP = "INP :: 'a \<Rightarrow> ('a, 'k) st_tape_symbol" 
  have mem: "(R\<^sub>1 \<bullet>, \<turnstile>, R\<^sub>1 \<bullet>, \<turnstile>, dir.R) \<in> \<delta>'" unfolding \<delta>'_def by auto
  let ?cs1 = "Config\<^sub>S (R\<^sub>1 \<bullet>) (\<lambda>n. if n = 0 then \<turnstile> else if n \<le> length (map ?INP w) then map ?INP w ! (n - 1) else blank') (Suc 0)" 
  have "(st.init_config (map INP w), ?cs1) \<in> st.dstep" 
    unfolding st.init_config_def by (rule st.dstepI[OF mem], auto simp: \<delta>'_def blank'_def)
  moreover have "rel_R\<^sub>1 ?cs1 w 0" 
    by (intro rel_R\<^sub>1.intros[OF refl], auto)
  ultimately show ?thesis by blast
qed

lemma rel_R\<^sub>1_R\<^sub>1: assumes "rel_R\<^sub>1 cs0 w j"
  and "j < length w" 
  and "set w \<subseteq> \<Sigma>" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_R\<^sub>1 cs1 w (Suc j)" 
  using assms(1)
proof (cases rule: rel_R\<^sub>1.cases)
  case (1 n tc' q')
  note cs0 = 1(1)
  from assms have wj: "w ! j \<in> \<Sigma>" by auto
  show ?thesis
  proof (cases j)
    case 0
    with 1 have q': "q' = \<bullet>" by auto
    from 1(6)[of 0] 0 assms 1 have tc'1: "tc' (Suc 0) = INP (w ! 0)" by auto
    have mem: "(R\<^sub>1 \<bullet>, INP (w ! 0), R\<^sub>1 (SYM (w ! 0)), hatLE', dir.R) \<in> \<delta>'" unfolding \<delta>'_def
      using wj 0 by auto
    let ?cs1 = "Config\<^sub>S (R\<^sub>1 (SYM (w ! 0))) (tc'(Suc 0 := hatLE')) (Suc (Suc 0))" 
    have enc: "enc (init_config w) 0 = hatLE'" unfolding init_config_def hatLE'_def by auto
    have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0 0
      by (intro st.dstepI[OF mem], auto simp: q' tc'1 \<delta>'_def blank'_def)
    moreover have "rel_R\<^sub>1 ?cs1 w (Suc 0)" 
      by (intro rel_R\<^sub>1.intros, rule 1(2), insert 1 0 assms(2), auto simp: enc) (cases w, auto)
    ultimately show ?thesis unfolding 0 by blast
  next
    case (Suc p)
    from 1(8)[OF Suc] have q': "q' = SYM (w ! p)" by auto
    from Suc assms(2) have "p < length w" by auto
    with assms(3) have "w ! p \<in> \<Sigma>" by auto
    with wj have "(w ! p, w ! j) \<in> \<Sigma> \<times> \<Sigma>" by auto
    hence mem: "(R\<^sub>1 (SYM (w ! p)), INP (w ! j), R\<^sub>1 (SYM (w ! j)), encSym (w ! p), dir.R) \<in> \<delta>'" unfolding \<delta>'_def by auto
    have enc: "enc (init_config w) j = encSym (w ! p)" unfolding Suc using \<open>p < length w\<close>
      by (auto simp: init_config_def encSym_def)
    from 1(6)[of j] assms 1 have tc': "tc' (Suc j) = INP (w ! j)" by auto
    let ?cs1 = "Config\<^sub>S (R\<^sub>1 (SYM (w ! j))) (tc'(Suc j := encSym (w ! p))) (Suc (Suc j))" 
    have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0
      by (rule st.dstepI[OF mem], insert q' tc', auto simp: \<delta>'_def blank'_def)
    moreover have "rel_R\<^sub>1 ?cs1 w (Suc j)" 
      by (intro rel_R\<^sub>1.intros, insert 1 assms enc, auto)
    ultimately show ?thesis by blast
  qed
qed

inductive rel_R\<^sub>2 :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. enc (init_config w) i = tc' (Suc i)) \<Longrightarrow>
  p \<le> length w \<Longrightarrow>
  rel_R\<^sub>2 (Config\<^sub>S R\<^sub>2 tc' p) w p" 


lemma rel_R\<^sub>1_R\<^sub>2: assumes "rel_R\<^sub>1 cs0 w (length w)"
  and "set w \<subseteq> \<Sigma>" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_R\<^sub>2 cs1 w (length w)" 
  using assms
proof (cases rule: rel_R\<^sub>1.cases)
  case (1 n tc' q')
  note cs0 = 1(1)
  have enc: "enc (init_config w) i = tc' (Suc i)" if "i \<noteq> length w" for i
  proof (cases "i < length w")
    case True
    thus ?thesis using 1(5)[of i] by auto
  next
    case False
    with that have i: "i > length w" by auto
    with 1(6)[of i] 1 have "tc' (Suc i) = blank'" by auto
    also have "\<dots> = enc (init_config w) i" using i unfolding init_config_def by (auto simp: blank'_def)
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (cases "length w")
    case 0
    with 1 have q': "q' = \<bullet>" by auto
    from 1(6)[of 0] 0 1 have tc'1: "tc' (Suc 0) = blank'" by auto
    have mem: "(R\<^sub>1 \<bullet>, blank', R\<^sub>2, hatLE', dir.L) \<in> \<delta>'" unfolding \<delta>'_def
      by auto
    let ?tc = "tc'(Suc 0 := hatLE')" 
    let ?cs1 = "Config\<^sub>S R\<^sub>2 ?tc 0" 
    have enc0: "enc (init_config w) 0 = hatLE'" unfolding init_config_def hatLE'_def by auto
    have enc: "enc (init_config w) i = ?tc (Suc i)" for i using enc[of i] enc0 using 0
      by (cases i, auto)
    have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0 0
      by (intro st.dstepI[OF mem], auto simp: q' tc'1 \<delta>'_def blank'_def)
    moreover have "rel_R\<^sub>2 ?cs1 w (length w)" unfolding 0
      by (intro rel_R\<^sub>2.intros enc, insert 1 0, auto)
    ultimately show ?thesis unfolding 0 by blast
  next
    case (Suc p)
    from 1(8)[OF Suc] have q': "q' = SYM (w ! p)" by auto
    from Suc have "p < length w" by auto
    with assms(2) have "w ! p \<in> \<Sigma>" by auto
    hence mem: "(R\<^sub>1 (SYM (w ! p)), blank', R\<^sub>2, encSym (w ! p), dir.L) \<in> \<delta>'" unfolding \<delta>'_def by auto
    let ?tc = "tc'(Suc (length w) := encSym (w ! p))" 
    have encW: "enc (init_config w) (length w) = encSym (w ! p)" unfolding Suc using \<open>p < length w\<close>
      by (auto simp: init_config_def encSym_def)
    from 1(6)[of "length w"] assms 1 have tc': "tc' (Suc (length w)) = blank'" by auto
    let ?cs1 = "Config\<^sub>S R\<^sub>2 ?tc (length w)" 
    have enc: "enc (init_config w) i = ?tc (Suc i)" for i using enc[of i] encW by auto
    have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0 q'
      by (intro st.dstepI[OF mem] tc', auto simp: \<delta>'_def blank'_def)
    moreover have "rel_R\<^sub>2 ?cs1 w (length w)" 
      by (intro rel_R\<^sub>2.intros, insert 1 assms enc, auto)
    ultimately show ?thesis by blast
  qed
qed


lemma rel_R\<^sub>2_R\<^sub>2: assumes "rel_R\<^sub>2 cs0 w (Suc j)"
  and "set w \<subseteq> \<Sigma>" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_R\<^sub>2 cs1 w j" 
  using assms
proof (cases rule: rel_R\<^sub>2.cases)
  case (1 tc')
  note cs0 = 1(1)
  from 1 have j: "j < length w" by auto
  have tc: "tc' (Suc j) \<in> \<Gamma>' - { \<turnstile> }" unfolding 1(3)[symmetric] using j assms(2)[unfolded set_conv_nth] unfolding init_config_def
    by (force simp: \<Gamma>'_def gamma_set_def intro!: imageI LE blank set_mp[OF \<Sigma>_sub_\<Gamma>, of "w ! (j - Suc 0)"])
  hence mem: "(R\<^sub>2, tc' (Suc j), R\<^sub>2, tc' (Suc j), dir.L) \<in> \<delta>'" unfolding \<delta>'_def by auto
  let ?cs1 = "Config\<^sub>S R\<^sub>2 tc' j" 
  have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0 using tc
    by (intro st.dstepI[OF mem], auto simp: \<delta>'_def blank'_def)
  moreover have "rel_R\<^sub>2 ?cs1 w j"
    by (intro rel_R\<^sub>2.intros, insert 1, auto)
  ultimately show ?thesis by blast
qed

inductive rel_S\<^sub>0 :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. tc' (Suc i) = enc (Config\<^sub>M q tc p) i) \<Longrightarrow>
  valid_config (Config\<^sub>M q tc p) \<Longrightarrow>
  rel_S\<^sub>0 (Config\<^sub>S (S\<^sub>0 q) tc' 0) (Config\<^sub>M q tc p)" 

lemma rel_R\<^sub>2_S\<^sub>0: assumes "rel_R\<^sub>2 cs0 w 0"
  and "set w \<subseteq> \<Sigma>" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_S\<^sub>0 cs1 (init_config w)" 
  using assms
proof (cases rule: rel_R\<^sub>2.cases)
  case (1 tc')
  note cs0 = 1(1)
  hence mem: "(R\<^sub>2, \<turnstile>, S\<^sub>0 s, \<turnstile>, dir.N) \<in> \<delta>'" unfolding \<delta>'_def by auto
  let ?cs1 = "Config\<^sub>S (S\<^sub>0 s) tc' 0" 
  have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0
    by (intro st.dstepI[OF mem], insert 1, auto simp: \<delta>'_def blank'_def)
  moreover have "rel_S\<^sub>0 ?cs1 (init_config w)" using valid_init_config[OF assms(2)] unfolding init_config_def
    by (intro rel_S\<^sub>0.intros, insert 1(1,2,4-), auto simp: 1(3)[symmetric] init_config_def)
  ultimately show ?thesis by blast
qed

text \<open>If we start with a proper word \<open>w\<close> as input on the singletape TM, 
  then via the R-phase one can switch to the beginning of 
  the S-phase (@{const rel_S\<^sub>0}) for the initial configuration.\<close>

lemma R_phase: assumes "set w \<subseteq> \<Sigma>"
  shows "\<exists> cs. (st.init_config (map INP w), cs) \<in> st.dstep^^(3 + 2 * length w) \<and> rel_S\<^sub>0 cs (init_config w)" 
proof -
  from rel_R\<^sub>1_init[of w] obtain cs1 n where
    step1: "(st.init_config (map INP w), cs1) \<in> st.dstep" and 
    relR1: "rel_R\<^sub>1 cs1 w n" and 
    n0: "n = 0" 
    by auto
  from relR1
  have "n + k \<le> length w \<Longrightarrow> \<exists> cs2. (cs1, cs2) \<in> st.dstep^^k \<and> rel_R\<^sub>1 cs2 w (n + k)" for k
  proof (induction k arbitrary: cs1 n)
    case (Suc k cs1 n)  
    hence "n < length w" by auto
    from rel_R\<^sub>1_R\<^sub>1[OF Suc(3) this assms] obtain cs3 where
      step: "(cs1, cs3) \<in> st.dstep" and rel: "rel_R\<^sub>1 cs3 w (Suc n)" by auto
    from Suc.IH[OF _ rel] Suc(2) obtain cs2 where
      steps: "(cs3, cs2) \<in> st.dstep ^^ k"  and rel: "rel_R\<^sub>1 cs2 w (Suc n + k)" 
      by auto
    from relpow_Suc_I2[OF step steps] rel
    show ?case by auto
  qed auto
  from this[of "length w", unfolded n0]
  obtain cs2 where steps2: "(cs1, cs2) \<in> st.dstep ^^ length w" and rel: "rel_R\<^sub>1 cs2 w (length w)" by auto
  from rel_R\<^sub>1_R\<^sub>2[OF rel assms] obtain cs3 n where step3: "(cs2, cs3) \<in> st.dstep" 
    and rel: "rel_R\<^sub>2 cs3 w n" and n: "n = length w" 
    by auto
  from rel have "\<exists> cs. (cs3, cs) \<in> st.dstep^^n \<and> rel_R\<^sub>2 cs w 0" 
  proof (induction n arbitrary: cs3 rule: nat_induct)
    case (Suc n cs3)
    from rel_R\<^sub>2_R\<^sub>2[OF Suc(2) assms] obtain cs1 where
      step: "(cs3, cs1) \<in> st.dstep" and rel: "rel_R\<^sub>2 cs1 w n" by auto
    from Suc.IH[OF rel] obtain cs where steps: "(cs1, cs) \<in> st.dstep ^^ n" and rel: "rel_R\<^sub>2 cs w 0" by auto
    from relpow_Suc_I2[OF step steps] rel show ?case by auto
  qed auto
  then obtain cs4 where steps4: "(cs3, cs4) \<in> st.dstep^^(length w)"  and rel: "rel_R\<^sub>2 cs4 w 0" by (auto simp: n)
  from rel_R\<^sub>2_S\<^sub>0[OF rel assms] obtain cs where step5: "(cs4, cs) \<in> st.dstep" and 
    rel: "rel_S\<^sub>0 cs (init_config w)" by auto
  from relpow_Suc_I2[OF step1 relpow_transI[OF steps2 relpow_Suc_I2[OF step3 relpow_Suc_I[OF steps4 step5]]]]
  have "(st.init_config (map INP w), cs) \<in> st.dstep ^^ Suc (length w + Suc (Suc (length w)))" .
  also have "Suc (length w + Suc (Suc (length w))) = 3 + 2 * length w" by simp
  finally show ?thesis using rel by auto
qed  

subsubsection \<open>S-Phase\<close>

inductive rel_S :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> nat \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. tc' (Suc i) = enc (Config\<^sub>M q tc p) i) \<Longrightarrow>
  valid_config (Config\<^sub>M q tc p) \<Longrightarrow>
  (\<And> i. inp i = (if p i < p' then SYM (tc i (p i)) else \<bullet>)) \<Longrightarrow>
  rel_S (Config\<^sub>S (S q inp) tc' (Suc p')) (Config\<^sub>M q tc p) p'" 

lemma rel_S\<^sub>0_S: assumes "rel_S\<^sub>0 cs0 cm"
  and "mt_state cm \<notin> {t,r}" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_S cs1 cm 0" 
  using assms(1)
proof (cases rule: rel_S\<^sub>0.cases)
  case (1 tc' q tc p)
  note cs0 = 1(1)
  note cm = 1(2)
  from assms(2) cm 1(5) have qtr: "q \<in> Q - {t,r}" by auto
  hence mem: "(S\<^sub>0 q, \<turnstile>, S q (\<lambda>_. \<bullet>), \<turnstile>, dir.R) \<in> \<delta>'" unfolding \<delta>'_def by auto
  let ?cs1 = "Config\<^sub>S (S q (\<lambda>_. \<bullet>)) tc' (Suc 0)" 
  have "(cs0, ?cs1) \<in> st.dstep" unfolding cs0
    by (rule st.dstepI[OF mem], insert 1, auto simp: \<delta>'_def blank'_def)
  moreover have "rel_S ?cs1 cm 0" unfolding cm
    by (intro rel_S.intros 1, auto)
  ultimately show ?thesis by blast
qed

lemma rel_S_mem: assumes "rel_S (Config\<^sub>S (S q inp) tc' p') cm j" 
  shows "inp \<in> func_set \<and> q \<in> Q \<and> (\<exists> t. tc' (Suc i) = TUPLE t \<and> t \<in> gamma_set)" 
  using assms(1)
proof (cases rule: rel_S.cases)
  case (1 tc p)
  from 1 have q: "q \<in> Q" by auto
  have inp: "inp \<in> func_set" unfolding func_set_def 1(6) using 1(5)
    by force
  have "\<exists> t. tc' (Suc i) = TUPLE t \<and> t \<in> gamma_set" using 1(5)
    unfolding 1(4) by (force simp: gamma_set_def) 
  with q inp show ?thesis by auto
qed

lemma rel_S_S: assumes "rel_S cs0 cm p'" 
  "p' \<le> Max (range (mt_pos cm))" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_S cs1 cm (Suc p')"
  using assms(1)
proof (cases rule: rel_S.cases)
  case (1 tc' q tc p inp)
  note cs0 = 1(1)
  note cm = 1(2)
  let ?Set = "Q \<times> (func_set - (UNIV \<rightarrow> SYM ` \<Gamma>)) \<times> gamma_set" 
  let ?f = "\<lambda>(q, inp, t). (S q inp, TUPLE t, S q (add_inp t inp), TUPLE t, dir.R)" 
  obtain i where "mt_pos cm i = Max (range (mt_pos cm))" using range_mt_pos(1)[of cm] by auto
  with assms 1 have "p' \<le> p i" by auto
  with 1(6)[of i] have "inp i = \<bullet>" by auto
  hence inp: "inp \<notin> (UNIV \<rightarrow> SYM ` \<Gamma>)"
    by (metis PiE UNIV_I image_iff sym_or_bullet.distinct(1))
  with rel_S_mem[OF assms(1)[unfolded cs0], of p'] obtain t where
    "(q,inp,t) \<in> ?Set" and tc': "tc' (Suc p') = TUPLE t" by auto
  hence "?f (q,inp,t) \<in> \<delta>'" unfolding \<delta>'_def by blast
  hence mem: "(S q inp, TUPLE t, S q (add_inp t inp), TUPLE t, dir.R) \<in> \<delta>'" by simp 
  let ?cs1 = "Config\<^sub>S (S q (add_inp t inp)) tc' (Suc (Suc p'))" 
  have "(cs0,?cs1) \<in> st.dstep" unfolding cs0 using inp
    by (intro st.dstepI[OF mem], auto simp: tc' \<delta>'_def blank'_def)
  moreover have "rel_S ?cs1 cm (Suc p')" unfolding cm
  proof (intro rel_S.intros 1)
    from 1(4)[of p', unfolded tc']
    have t: "t = (\<lambda>k. if p k = p' then HAT (tc k p') else NO_HAT (tc k p'))" by auto
    show "\<And> k. add_inp t inp k = (if p k < Suc p' then SYM (tc k (p k)) else \<bullet>)" 
      unfolding add_inp_def 1 t by auto
  qed
  ultimately show ?thesis by blast
qed

inductive rel_S\<^sub>1 :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. tc' (Suc i) = enc (Config\<^sub>M q tc p) i) \<Longrightarrow>
  valid_config (Config\<^sub>M q tc p) \<Longrightarrow>
  (\<And> i. inp i = tc i (p i)) \<Longrightarrow>
  (\<And> i. p i < p') \<Longrightarrow>
  p' = Suc (Max (range p)) \<Longrightarrow>
  rel_S\<^sub>1 (Config\<^sub>S (S\<^sub>1 q inp) tc' p') (Config\<^sub>M q tc p)" 

lemma rel_S_S\<^sub>1: assumes "rel_S cs0 cm p'" 
  "p' = Suc (Max (range (mt_pos cm)))" 
shows "\<exists> cs1. (cs0, cs1) \<in> st.dstep \<and> rel_S\<^sub>1 cs1 cm"
  using assms(1)
proof (cases rule: rel_S.cases)
  case (1 tc' q tc p inp)
  from assms have p'Max: "p' > Max (range (mt_pos cm))" by auto
  note cs0 = 1(1)
  note cm = 1(2)
  from p'Max range_mt_pos(2-)[of cm] have pip: "p i < p'" for i unfolding cm by auto
  let ?SET = "Q \<times> func_set \<times> gamma_set" 
  let ?Set = "Q \<times> (UNIV \<rightarrow> SYM ` \<Gamma>) \<times> (\<Gamma>' - { \<turnstile> })" 
  from rel_S_mem[OF assms(1)[unfolded cs0], of p'] obtain t where
    mem: "(q,inp,t) \<in> ?SET" and tc': "tc' (Suc p') = TUPLE t" by auto
  hence "inp \<in> func_set" by auto
  with pip have inp: "inp \<in> UNIV \<rightarrow> SYM ` \<Gamma>" unfolding func_set_def using 1(6) by auto
  with mem have "(q,inp,TUPLE t) \<in> ?Set" by auto
  hence "(\<lambda> (q,inp,a). (S q inp, a, S\<^sub>1 q (project_inp inp), a, dir.L)) (q,inp,TUPLE t) \<in> \<delta>'" unfolding \<delta>'_def by blast
  hence mem: "(S q inp, TUPLE t, S\<^sub>1 q (project_inp inp), TUPLE t, dir.L) \<in> \<delta>'" by simp 
  let ?cs1 = "Config\<^sub>S (S\<^sub>1 q (project_inp inp)) tc' p'" 
  have "(cs0,?cs1) \<in> st.dstep" unfolding cs0 using inp
    by (intro st.dstepI[OF mem], auto simp: tc' \<delta>'_def blank'_def)
  moreover have "rel_S\<^sub>1 ?cs1 cm" unfolding cm
  proof (intro rel_S\<^sub>1.intros 1 pip)
    fix i
    from inp have "inp i \<in> SYM ` \<Gamma>" by auto
    then obtain g where "inp i = SYM g" and "g \<in> \<Gamma>" by auto
    thus "project_inp inp i = tc i (p i)" using 1(6)[of i] by (auto simp: project_inp_def split: if_splits)
    show "p' = Suc (Max (range p))" unfolding assms(2) unfolding cm by simp
  qed
  ultimately show ?thesis by auto
qed

text \<open>If we start the S-phase (in @{const rel_S\<^sub>0}), and the multitape-TM is not in a final state, 
  then we can move to the end of the S-phase (in @{const rel_S\<^sub>1}).\<close>

lemma S_phase: assumes "rel_S\<^sub>0 cs cm"
  and "mt_state cm \<notin> {t, r}" 
shows "\<exists> cs'. (cs, cs') \<in> st.dstep^^(3 + Max (range (mt_pos cm))) \<and> rel_S\<^sub>1 cs' cm" 
proof -
  let ?N = "Max (range (mt_pos cm))" 
  from rel_S\<^sub>0_S[OF assms] obtain cs1 n where
    step1: "(cs, cs1) \<in> st.dstep" and rel: "rel_S cs1 cm n" and n: "n = 0"   
    by auto
  from rel have "n + k \<le> Suc ?N \<Longrightarrow> \<exists> cs2. (cs1, cs2) \<in> st.dstep ^^ k \<and> rel_S cs2 cm (n + k)" for k
  proof (induction k arbitrary: cs1 n)
    case (Suc k cs n)
    hence "n \<le> ?N" by auto
    from rel_S_S[OF Suc(3) this] obtain cs1 where step: "(cs, cs1) \<in> st.dstep" and rel: "rel_S cs1 cm (Suc n)" by auto
    from Suc have "Suc n + k \<le> Suc ?N" by auto
    from Suc.IH[OF this rel] obtain cs2 where steps: "(cs1, cs2) \<in> st.dstep ^^ k" and rel: "rel_S cs2 cm (n + Suc k)" by auto
    from relpow_Suc_I2[OF step steps] rel
    show ?case by auto
  qed auto
  from this[of "Suc ?N", unfolded n] obtain cs2 where 
    steps2: "(cs1, cs2) \<in> st.dstep ^^ (Suc ?N)" and rel: "rel_S cs2 cm (Suc ?N)" by auto
  from rel_S_S\<^sub>1[OF rel] obtain cs3 where step3: "(cs2,cs3) \<in> st.dstep" and rel: "rel_S\<^sub>1 cs3 cm" by auto
  from relpow_Suc_I2[OF step1 relpow_Suc_I[OF steps2 step3]]
  have "(cs, cs3) \<in> st.dstep ^^ Suc (Suc (Suc ?N))" by simp
  also have "Suc (Suc (Suc ?N)) = 3 + ?N" by simp
  finally show ?thesis using rel by blast
qed

subsubsection \<open>E-Phase\<close>

context
  fixes rule :: "('a,'q,'k)mt_rule"
begin
inductive_set \<delta>step :: "('a, 'q, 'k) mt_config rel" where
  \<delta>step: "rule = (q, a, q1, b, dir) \<Longrightarrow>
   rule \<in> \<delta> \<Longrightarrow>
   (\<And> k. ts k (n k) = a k) \<Longrightarrow>
   (\<And> k. ts' k = (ts k)(n k := b k)) \<Longrightarrow>
   (\<And> k. n' k = go_dir (dir k) (n k)) \<Longrightarrow> 
   (Config\<^sub>M q ts n, Config\<^sub>M q1 ts' n') \<in> \<delta>step"
end

lemma step_to_\<delta>step: "(c1,c2) \<in> step \<Longrightarrow> \<exists> rule. (c1,c2) \<in> \<delta>step rule" 
proof (induct rule: step.induct)
  case (step q ts n q' a dir)
  show ?case
    by (rule exI, rule \<delta>step.intros[OF refl step], auto)
qed

lemma \<delta>step_to_step: "(c1,c2) \<in> \<delta>step rule \<Longrightarrow> (c1,c2) \<in> step" 
proof (induct rule: \<delta>step.induct)
  case *: (\<delta>step q a q' b dir ts n ts' n')
  from * have a: "a = (\<lambda> k. ts k (n k))" by auto
  from * have ts': "ts' = (\<lambda> k. (ts k)(n k := b k))" by auto
  from * have n': "n' = (\<lambda> k. go_dir (dir k) (n k))" by auto
  from * show ?case using step.intros[of q ts n q' b dir] unfolding a ts' n' by auto
qed

inductive rel_E\<^sub>0 :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config 
  \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> ('a,'q,'k)mt_rule \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. tc' (Suc i) = enc (Config\<^sub>M q tc p) i) \<Longrightarrow>
  valid_config (Config\<^sub>M q tc p) \<Longrightarrow>
  rule = (q,a,q1,b,d) \<Longrightarrow>
  (Config\<^sub>M q tc p, Config\<^sub>M q1 tc1 p1) \<in> \<delta>step rule \<Longrightarrow>
  (\<And> i. p i < p') \<Longrightarrow>
  p' = Suc (Max (range p)) \<Longrightarrow>
  rel_E\<^sub>0 (Config\<^sub>S (E\<^sub>0 q1 b d) tc' p') (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) rule" 

text \<open>For the transition between S and E phase we do not have deterministic steps.
  Therefore we add two lemmas: the former one is for showing that multitape can be simulated
  by singletape, and the latter one is for the inverse direction.\<close>
lemma rel_S\<^sub>1_E\<^sub>0_step: assumes "rel_S\<^sub>1 cs cm" 
  and "(cm,cm1) \<in> step" 
shows "\<exists> rule cs1. (cs, cs1) \<in> st.step \<and> rel_E\<^sub>0 cs1 cm cm1 rule"
proof -
  from step_to_\<delta>step[OF assms(2)] obtain rule where rstep: "(cm, cm1) \<in> \<delta>step rule" by auto 
  show ?thesis using assms(1)
  proof (cases rule: rel_S\<^sub>1.cases)
    case (1 tc' q tc p inp p')
    note cs = 1(1)
    note cm = 1(2)
    have tc': "tc' p' \<in> \<Gamma>'" unfolding 1(8,4) enc.simps \<Gamma>'_def gamma_set_def using 1(5)
      by (force intro!: imageI)
    show ?thesis using rstep[unfolded cm]
    proof (cases rule: \<delta>step.cases)
      case 2: (\<delta>step a q1 b dir ts' n')
      note rule = 2(2)
      note cm1 = 2(1)
      have "(\<lambda>((q, a, q', b, d), t). (S\<^sub>1 q a, t, E\<^sub>0 q' b d, t, dir.N)) (rule,tc' p') \<in> \<delta>'"
        unfolding \<delta>'_def using tc' 2(3) by blast
      hence mem: "(S\<^sub>1 q a, tc' p', E\<^sub>0 q1 b dir, tc' p', dir.N) \<in> \<delta>'" by (auto simp: rule)
      have inp_a: "inp = a" using 2(4)[folded 1(6)] by auto
      let ?cs1 = "Config\<^sub>S (E\<^sub>0 q1 b dir) tc' p'" 
      have step: "(cs, ?cs1) \<in> st.step" unfolding cs
        by (intro st.stepI[OF mem], insert inp_a, auto)
      moreover have "rel_E\<^sub>0 ?cs1 cm cm1 rule" unfolding cm cm1 
        by (intro rel_E\<^sub>0.intros[OF _ _ _ rule], insert 1 2 assms rstep, auto)
      ultimately show ?thesis by blast
    qed
  qed
qed

lemma rel_S\<^sub>1_E\<^sub>0_st_step: assumes "rel_S\<^sub>1 cs cm" 
  and "(cs,cs1) \<in> st.step" 
shows "\<exists> cm1 rule. (cm, cm1) \<in> step \<and> rel_E\<^sub>0 cs1 cm cm1 rule"
  using assms(1)
proof (cases rule: rel_S\<^sub>1.cases)
  case (1 tc' q tc p inp p')
  note cs = 1(1)
  note cm = 1(2)
  have tc': "tc' p' \<in> \<Gamma>'" unfolding 1(8,4) enc.simps \<Gamma>'_def gamma_set_def using 1(5)
    by (force intro!: imageI)
  show ?thesis using assms(2)[unfolded cs]
  proof (cases rule: st.step.cases)
    case 2: (step qq bb ddir)
    from 2(2)[unfolded \<delta>'_def]
    have "(S\<^sub>1 q inp, tc' p', qq, bb, ddir) \<in> (\<lambda>((q, a, q', b, d), t). (S\<^sub>1 q a, t, E\<^sub>0 q' b d, t, dir.N)) ` (\<delta> \<times> \<Gamma>')" by auto
    then obtain q' b dir where mem: "(q,inp,q',b,dir) \<in> \<delta>" and qq: "qq = E\<^sub>0 q' b dir" and ddir: "ddir = dir.N"
      and bb: "bb = tc' p'" by auto
    hence cs1: "cs1 = Config\<^sub>S (E\<^sub>0 q' b dir) tc' p'" unfolding 2 qq ddir bb by auto
    let ?rule = "(q,inp,q',b,dir)" 
    let ?cm1 = "Config\<^sub>M q' (\<lambda> k. (tc k)(p k := b k)) (\<lambda> k. go_dir (dir k) (p k))" 
    have \<delta>step: "(cm, ?cm1) \<in> \<delta>step ?rule" unfolding cm
      by (intro \<delta>step.intros[OF refl mem], auto simp: 1(6))
    from \<delta>step_to_step[OF this] 
    have "(cm, ?cm1) \<in> step" .
    moreover have "rel_E\<^sub>0 cs1 cm ?cm1 ?rule" unfolding cm cs1
      by (intro rel_E\<^sub>0.intros \<delta>step[unfolded cm], insert 1 2, auto)
    ultimately show ?thesis by blast
  qed
qed

fun enc2 :: "('a, 'q, 'k) mt_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, 'k) st_tape_symbol"
  where "enc2 (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) p' n = TUPLE (\<lambda> k. if p k < p' 
    then if p k = n then HAT (tc k n) else NO_HAT (tc k n) 
    else if p1 k = n then HAT (tc1 k n) else NO_HAT (tc1 k n))"

inductive rel_E :: "(('a, 'k) st_tape_symbol,('a, 'q, 'k) st_states)st_config 
  \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> ('a, 'q, 'k) mt_config \<Rightarrow> ('a,'q,'k)mt_rule \<Rightarrow> nat \<Rightarrow> bool" where 
  "tc' 0 = \<turnstile> \<Longrightarrow> 
  (\<And> i. tc' (Suc i) = enc2 (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) p' i) \<Longrightarrow>
  valid_config (Config\<^sub>M q tc p) \<Longrightarrow>
  rule = (q,a,q1,b,d) \<Longrightarrow>
  (Config\<^sub>M q tc p, Config\<^sub>M q1 tc1 p1) \<in> \<delta>step rule \<Longrightarrow>
  bo = (\<lambda> k. if p k < p' then SYM (b k) else \<bullet>)  \<Longrightarrow>
  rel_E (Config\<^sub>S (E q1 bo d) tc' p') (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) rule p'" 

lemma rel_E\<^sub>0_E: assumes "rel_E\<^sub>0 cs cm cm1 rule" 
  shows "\<exists> cs1. (cs, cs1) \<in> st.dstep \<and> rel_E cs1 cm cm1 rule (Suc (Max (range (mt_pos cm))))"
  using assms(1)
proof (cases rule: rel_E\<^sub>0.cases)
  case (1 tc' q tc p a q1 b d tc1 p1 p')
  note cs = 1(1)
  note cm = 1(2)
  note cm1 = 1(3)
  note rule = 1(7)
  let ?rule = "(q, a, q1, b, d)" 
  have tc': "tc' p' \<in> \<Gamma>'" unfolding 1(10,5) enc.simps \<Gamma>'_def gamma_set_def using 1(6)
    by (force intro!: imageI)
  have rmem: "?rule \<in> \<delta>" using 1(8,7) by (cases rule: \<delta>step.cases, auto)
  note elem = \<delta>[OF this]
  have "((q1,b,d), tc' p') \<in> (Q \<times> (UNIV \<rightarrow> \<Gamma>) \<times> UNIV) \<times> \<Gamma>'" 
    using elem tc' by auto
  hence "(\<lambda>((q, a, d), t). (E\<^sub>0 q a d, t, E q (SYM \<circ> a) d, t, dir.N)) ((q1,b,d), tc' p') \<in> \<delta>'" 
    unfolding \<delta>'_def by blast
  hence mem: "(E\<^sub>0 q1 b d, tc' p', E q1 (SYM \<circ> b) d, tc' p', dir.N) \<in> \<delta>'" by simp
  have Max: "Suc (Max (range (mt_pos cm))) = p'" unfolding cm using 1 by auto
  let ?cs1 = "Config\<^sub>S (E q1 (SYM \<circ> b) d) tc' p'"
  have "(cs, ?cs1) \<in> st.dstep" unfolding cs
    by (intro st.dstepI[OF mem] refl, auto simp: \<delta>'_def)
  moreover have "rel_E ?cs1 cm cm1 rule (Suc (Max (range (mt_pos cm))))"
    unfolding Max unfolding cm cm1 rule
    by (intro rel_E.intros, insert 1, auto)
  ultimately show ?thesis by blast
qed

lemma rel_E_S\<^sub>0: assumes "rel_E cs cm cm1 rule 0" 
  shows "\<exists> cs1. (cs,cs1) \<in> st.dstep \<and> rel_S\<^sub>0 cs1 cm1" 
  using assms(1)
proof (cases rule: rel_E.cases)
  case (1 tc' q tc p q1 tc1 p1 a b d bo)
  note cs = 1(1)
  note cm = 1(2)
  note cm1 = 1(3)
  from valid_step[OF \<delta>step_to_step[OF 1(8)] 1(6)]
  have valid: "valid_config (Config\<^sub>M q1 tc1 p1)" .
  from valid have q1: "q1 \<in> Q" by auto
  hence mem: "(E q1 (\<lambda> _. \<bullet>) d, \<turnstile>, S\<^sub>0 q1, \<turnstile>, dir.N) \<in> \<delta>'" unfolding \<delta>'_def by auto
  let ?cs1 = "Config\<^sub>S (S\<^sub>0 q1) tc' 0" 
  have "(cs, ?cs1) \<in> st.dstep" unfolding cs
    by (intro st.dstepI[OF mem], insert 1, auto simp: \<delta>'_def)
  moreover have "rel_S\<^sub>0 ?cs1 cm1" unfolding cm1
    by (intro rel_S\<^sub>0.intros valid, insert 1, auto)
  ultimately show ?thesis by blast
qed

lemma dsteps_to_steps: "a \<in> st.dstep ^^ n \<Longrightarrow> a \<in> st.step ^^ n" 
  using relpow_mono[OF st.dstep_step] by auto

lemma \<delta>'_mem: assumes "tup \<in> A" 
  and "f ` A \<subseteq> \<delta>'"
shows "f tup \<in> \<delta>'"
  using assms by auto

lemma rel_E_E: assumes "rel_E cs cm cm1 rule (Suc p')" 
  shows "\<exists> cs1. (cs,cs1) \<in> st.dstep^^4 \<and> rel_E cs1 cm cm1 rule p'" 
  using assms
proof(cases rule: rel_E.cases)
  case (1 tc' q tc p q1 tc1 p1 a b d bo)
  let ?rule = "(q, a, q1, b, d)" 
  have valid_next: "valid_config(Config\<^sub>M q1 tc1 p1)"
    using 1(8,6) \<delta>step_to_step valid_step by blast
  have trans: "(\<lambda>(q, ys, ds, t). (E q ys ds, TUPLE t, Er q (update_ys t ys) ds (compute_idx_set t ys),
                  TUPLE (replace_sym t ys), dir.R)) ` (Q \<times> func_set \<times> UNIV \<times> gamma_set) \<subseteq> \<delta>'"
    "(\<lambda>(q, ys, ds, I, t). (Er q ys ds I, TUPLE t, Em q ys ds I, TUPLE (place_hats_R t ds I), dir.L)) 
                  ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set) \<subseteq> \<delta>'"
    "(\<lambda>(q, ys, ds, I, t). (Em q ys ds I, TUPLE t, El q ys ds I, TUPLE (place_hats_M t ds I), dir.L)) 
                  ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set) \<subseteq> \<delta>'"
    "(\<lambda>(q, ys, ds, I). (El q ys ds I, \<turnstile>, E q ys ds, \<turnstile>, dir.N)) 
                  ` (Q \<times> func_set \<times> UNIV \<times> Pow UNIV) \<subseteq> \<delta>'"
    "(\<lambda> (q,ys,ds,I,t). (El q ys ds I, TUPLE t, E  q ys ds, TUPLE (place_hats_L t ds I), dir.N)) 
                  ` (Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set) \<subseteq> \<delta>'"
    unfolding \<delta>'_def 
    by(blast, blast, blast, blast, blast)
      (*---------------------------- first step start-----------------------------*)
  obtain tup where tup: "tc' (Suc p') = TUPLE tup"
    unfolding 1(5) \<Gamma>'_def gamma_set_def enc2.simps by auto
  have tup_mem: "tup \<in> gamma_set"
    using tup 1(6) valid_next unfolding gamma_set_def 1(5) enc2.simps valid_config.simps
    by (smt (z3) Pi_iff UnI1 UnI2 image_iff range_subsetD st_tape_symbol.simps(1))
  have bo_set: "bo \<in> func_set"
    using 1 \<delta>(4) \<delta>step.simps unfolding func_set_def by fastforce
  have rmem: "?rule \<in> \<delta>" using 1(8,7) by (cases rule: \<delta>step.cases, auto)
  note elem = \<delta>[OF this]
  let ?rep_tup = "TUPLE (replace_sym tup bo)" 
  let ?tc1 = "(tc'(Suc p' := ?rep_tup))"
  let ?I = "compute_idx_set tup bo"
  let ?ys' = "update_ys tup bo"
  let ?er = "Er q1 ?ys' d ?I"
  let ?cs1 = "Config\<^sub>S ?er ?tc1 (Suc(Suc p'))"
  have "(q1,bo,d,tup) \<in> Q \<times> func_set \<times> UNIV \<times> gamma_set" using elem tup_mem bo_set by blast
  hence mem: "(E q1 bo d, tc' (Suc p'), ?er, ?rep_tup, dir.R) \<in> \<delta>'"
    using \<delta>'_mem[OF _ trans(1)] unfolding split tup by fast
  note dstep_help = st.dstep[of "E q1 bo d" "tc'" "(Suc p')" ?er ?rep_tup "dir.R"]
  have to_r: "(Config\<^sub>S (E q1 bo d) tc' (Suc p'), ?cs1) \<in> st.dstep"
    using dstep_help[OF mem] unfolding \<delta>'_def go_dir.simps tup by fast
      (*---------------------------- first step end-----------------------------*)
      (*---------------------------- second step start-----------------------------*)
  obtain tup2 where tup2: "tc' (Suc(Suc p')) = TUPLE tup2"
    unfolding 1(5) \<Gamma>'_def gamma_set_def enc2.simps by auto
  have tup2_mem: "tup2 \<in> gamma_set"
    using tup2 1(6) valid_next
    unfolding gamma_set_def 1(5) enc2.simps valid_config.simps
    by (smt (z3) Pi_iff UnI1 UnI2 imageI range_subsetD st_tape_symbol.inject(1))
  let ?em = "Em q1 ?ys' d ?I"
  let ?tc2 = "(?tc1(Suc(Suc p') := TUPLE (place_hats_R tup2 d ?I)))"
  let ?cs2 = "Config\<^sub>S ?em ?tc2 (Suc p')"
  have "(q1,?ys',d,?I,tup2) \<in> Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set" 
    using update_ys_range[OF tup_mem bo_set] elem tup2_mem by blast
  hence mem2: "(?er, ?tc1 (Suc(Suc p')), Em q1 ?ys' d ?I, TUPLE (place_hats_R tup2 d ?I), dir.L) \<in> \<delta>'"
    using \<delta>'_mem[OF _ trans(2)] tup2 unfolding split by auto
  note dstep_help2 = st.dstep[of ?er ?tc1 "Suc(Suc p')" ?em "TUPLE (place_hats_R tup2 d ?I)" "dir.L"]
  have to_m: "(?cs1, ?cs2) \<in> st.dstep"
    using dstep_help2[OF mem2] tup2 unfolding \<delta>'_def go_dir.simps by fastforce
      (*---------------------------- second step end-----------------------------*)
      (*---------------------------- third step start-----------------------------*)
  have "(q1,?ys',d,?I,replace_sym tup bo) \<in> Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set" 
    using update_ys_range[OF tup_mem bo_set] replace_sym_range[OF tup_mem bo_set] elem(3) by blast
  hence mem3: "(?em, ?tc2 (Suc p'), El q1 ?ys' d ?I, TUPLE (place_hats_M (replace_sym tup bo) d ?I), dir.L) \<in> \<delta>'" 
    using \<delta>'_mem[OF _ trans(3)] by auto
  note dstep_help3 = st.dstep[of ?em ?tc2 "Suc p'" "El q1 ?ys' d ?I" "TUPLE (place_hats_M (replace_sym tup bo) d ?I)" dir.L]
  let ?el = "El q1 (update_ys tup bo) d (compute_idx_set tup bo)"
  let ?tc3 = "tc'(Suc p' := TUPLE (replace_sym tup bo),
         Suc (Suc p') := TUPLE (place_hats_R tup2 d (compute_idx_set tup bo)),
         Suc p' := TUPLE (place_hats_M (replace_sym tup bo) d (compute_idx_set tup bo)))"
  let ?cs3 = "Config\<^sub>S ?el ?tc3 p'"
  have to_l: "(?cs2, ?cs3) \<in> st.dstep"
    using dstep_help3[OF mem3] unfolding \<delta>'_def go_dir.simps by fastforce
      (*---------------------------- third step end-----------------------------*)
  have steps3: "(cs, ?cs3) \<in> st.dstep ^^ 3" unfolding numeral_3_eq_3 using to_l to_m to_r 1(1) by auto
      (*-------case distinction depending on whether end of tape is reached------------------*)
  have tc1_def: "\<And> k. tc1 k = (tc k)(p k := b k)"
    using 1(8) unfolding 1(7) by (simp add: \<delta>step.simps old.prod.inject)
  have p1_def: "\<And> k. p1 k = go_dir (d k) (p k)"
    using 1(8) unfolding 1(7) by (simp add: \<delta>step.simps old.prod.inject)
  have not_I_mem_current_pos: "\<forall> k'. k' \<notin> ?I \<longrightarrow> p k' \<noteq> p'"
    by(intro allI impI, insert tup elem 1(6), fastforce simp: 1 compute_idx_set_def)
  have I_mem_current_pos: "\<forall> k. k \<in> ?I \<longrightarrow> p k = p'"
    using compute_idx_set_def 1(5,9) tup by(simp, fastforce)
  have I_mem_eq_cur_pos: "\<forall> k. k \<in> ?I \<longleftrightarrow> p k = p'"
    using I_mem_current_pos not_I_mem_current_pos by auto
  show ?thesis
  proof(cases p')
    case p_zero: 0
    hence tc3_tup: "?tc3 p' = \<turnstile>" using 1(4) by simp
    have "(q1,?ys',d,?I) \<in> Q \<times> func_set \<times> UNIV \<times> UNIV" 
      using update_ys_range[OF tup_mem bo_set] replace_sym_range[OF tup_mem bo_set] elem(3) by blast
    hence mem4: "(El q1 ?ys' d ?I, ?tc3 p', E q1 ?ys' d, \<turnstile>, dir.N) \<in> \<delta>'" 
      using \<delta>'_mem[OF _ trans(4)] unfolding tc3_tup by auto
    let ?tc4 = "?tc3(p' := \<turnstile>)"
    let ?cs4 = "Config\<^sub>S (E q1 ?ys' d) ?tc4 p'"
    note dstep_help4 = st.dstep[of "El q1 ?ys' d ?I" ?tc3 p' "E q1 ?ys' d" \<turnstile> dir.N]
    have "(?cs3, ?cs4) \<in>  st.dstep ^^ 1"
      using dstep_help4[OF mem4] unfolding \<delta>'_def go_dir.simps relpow_1 tc3_tup by fastforce
    hence steps: "(cs, ?cs4) \<in>  st.dstep ^^ 4"
      using relpow_transI[OF steps3] by fastforce
    note intro_helper = rel_E.intros[of ?tc4 q tc p q1 tc1 p1 p' rule a b d "update_ys tup bo"]
    have valid_subs: "(\<forall> i. (tc'(Suc p' := TUPLE (replace_sym tup bo),
             Suc (Suc p') := TUPLE (place_hats_R tup2 d (compute_idx_set tup bo)),
             Suc p' := TUPLE (place_hats_M (replace_sym tup bo) d (compute_idx_set tup bo)),
             p' := \<turnstile>)) (Suc i) = enc2 (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) p' i)"
    proof 
      fix i
      consider (zer) "i = 0" | (suc) "i = Suc 0" | (ge_one) "i > Suc 0" by linarith
      then show "(tc'(Suc p' := TUPLE (replace_sym tup bo),
             Suc (Suc p') := TUPLE (place_hats_R tup2 d (compute_idx_set tup bo)),
             Suc p' := TUPLE (place_hats_M (replace_sym tup bo) d (compute_idx_set tup bo)),
             p' := \<turnstile>)) (Suc i) = enc2 (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) p' i"
      proof(cases)
        case zer
        have "(case replace_sym tup bo k of
         NO_HAT a \<Rightarrow> if k \<in> compute_idx_set tup bo \<and> d k = dir.N then HAT a else NO_HAT a
         | HAT x \<Rightarrow> HAT x) = (if p1 k = 0 then HAT (tc1 k 0) else NO_HAT (tc1 k 0))" for k
        proof(cases "k \<in> ?I")
          case k_in_I: True
          then obtain x where rep_no_hat: "replace_sym tup bo k = NO_HAT x"
            unfolding replace_sym_def compute_idx_set_def by auto
          have pk_zero: "p k = 0"
            using k_in_I less_Suc0 p_zero unfolding compute_idx_set_def 1(9) by fastforce
          show ?thesis
          proof(cases "d k = dir.N")
            case False
            moreover have "tc k (p k) = LE"
              using 1(6) pk_zero 1(8) by auto
            moreover have  "tc k (p k) = a k"
              using 1(7,8) pk_zero unfolding \<delta>step.simps by blast
            ultimately have "d k = dir.R"
              using \<delta>LE[OF rmem] by auto
            then show ?thesis
              by(insert k_in_I p1_def tc1_def, simp, insert rep_no_hat, auto simp: replace_sym_def 1(9) p_zero pk_zero)
          qed(insert k_in_I rep_no_hat pk_zero 1(9), auto simp:  replace_sym_def tc1_def p1_def)
        next
          case False
          show ?thesis
            using tup False 1(5) p_zero not_I_mem_current_pos p1_def tc1_def
            unfolding p_zero replace_sym_def by fastforce
        qed
        then show ?thesis
          unfolding zer p_zero place_hats_M_def place_hats_to_dir_def by simp
      next
        case suc
        have "(case tup2 k of
         NO_HAT a \<Rightarrow> if k \<in> compute_idx_set tup bo \<and> d k = dir.R then HAT a else NO_HAT a
         | HAT x \<Rightarrow> HAT x) = (if p1 k = Suc 0 then HAT (tc1 k (Suc 0)) else NO_HAT (tc1 k (Suc 0)))" for k
          using tup2 p_zero elem(4) 1(5,6,9) gr_zeroI tm(4) tup
          by (auto simp: compute_idx_set_def tc1_def p1_def, smt (verit, best) diff_0_eq_0 go_dir.elims not_gr0)
        then show ?thesis unfolding suc p_zero place_hats_R_def place_hats_to_dir_def by simp
      next
        case ge_one
        have "(if p k = 0 then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
         else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i)) = (if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i))" for k
          using insert ge_one p1_def tc1_def
          by (smt (verit, ccfv_threshold) diff_0_eq_0 fun_upd_other go_dir.elims less_irrefl_nat less_nat_zero_code)  
        then show ?thesis using ge_one p_zero 1(5)[of i] enc2.simps by simp
      qed
    qed
    have only_hats: "\<And> k. p k = 0 \<longrightarrow> tup k \<in> HAT ` \<Gamma>"
      using tup unfolding p_zero 1(5)[of 0] enc2.simps by (simp, meson imageI tup_hat_content tup_mem)
    have "(if k \<in> compute_idx_set tup bo then \<bullet> else bo k) = \<bullet>" for k
      using only_hats elem(4) 1(9) by (auto simp: compute_idx_set_def p_zero)
    hence replaced_all: "update_ys tup bo = (\<lambda>k. if p k < p' then SYM (b k) else \<bullet>)"
      unfolding update_ys_def p_zero by auto
    have invs: "rel_E ?cs4 cm cm1 rule p'"
      using valid_subs p_zero intro_helper[OF _ _ 1(6) 1(7) 1(8) replaced_all] 1(2,3,7) by auto
    then show ?thesis
      by(insert steps invs, intro exI conjI, auto)
  next
    case (Suc nat)
    obtain tup3 where tc3_p': "?tc3 p' = TUPLE tup3" and
      tup3_def: "tup3 = (\<lambda>k. if p k < Suc (Suc nat) then if p k = nat then HAT (tc k nat) else NO_HAT (tc k nat)
        else if p1 k = nat then HAT (tc1 k nat) else NO_HAT (tc1 k nat))"
      using 1(5)[of nat] unfolding Suc enc2.simps by simp
    have tup3_mem: "tup3 \<in> gamma_set"
      using tup3_def 1(6) valid_next unfolding gamma_set_def 1(5) enc2.simps valid_config.simps
      by (smt (z3) Pi_I UnI1 UnI2 imageI range_subsetD st_tape_symbol.inject(1))
    let ?a4 = "TUPLE (place_hats_L tup3 d (compute_idx_set tup bo))"
    let ?tc4 = "?tc3(p' := ?a4)"
    let ?cs4 = "Config\<^sub>S (E q1 ?ys' d) ?tc4 p'"
    have step_mem:"(q1, ?ys', d, ?I, tup3) \<in> Q \<times> func_set \<times> UNIV \<times> UNIV \<times> gamma_set" 
      using update_ys_range[OF tup_mem bo_set] replace_sym_range[OF tup_mem bo_set] elem(3) tup3_mem by blast
    have mem5: "(El q1 ?ys' d ?I, ?tc3 p', E q1 ?ys' d, TUPLE (place_hats_L tup3 d (compute_idx_set tup bo)), dir.N) \<in> \<delta>'" 
      using \<delta>'_mem[OF step_mem trans(5)] unfolding split tc3_p' .
    note dstep_help5 = st.dstep[of "El q1 ?ys' d ?I" ?tc3 p' "E q1 ?ys' d" ?a4 dir.N]
    note intros_helper2 = rel_E.intros[of ?tc4 q tc p q1 tc1 p1 p' rule a b d "update_ys tup bo"]
    have correct_shift: "(tc'(Suc p' := TUPLE (replace_sym tup bo),
             Suc (Suc p') := TUPLE (place_hats_R tup2 d (compute_idx_set tup bo)),
             Suc p' := TUPLE (place_hats_M (replace_sym tup bo) d (compute_idx_set tup bo)),
             p' := TUPLE (place_hats_L tup3 d (compute_idx_set tup bo))))
         (Suc i) = enc2 (Config\<^sub>M q tc p) (Config\<^sub>M q1 tc1 p1) p' i" for i
    proof -
      consider (one) "Suc i = Suc nat"
        | (two) "Suc i = Suc(Suc nat)" 
        | (three) "Suc i = Suc(Suc(Suc nat))"
        | (else) "Suc i \<notin> {Suc nat ,Suc(Suc nat), Suc(Suc(Suc nat))}" by blast
      then show ?thesis
      proof cases
        case one
        have "(case tup3 k of
          NO_HAT a \<Rightarrow> if k \<in> compute_idx_set tup bo \<and> d k = dir.L then HAT a else NO_HAT a
          | HAT x \<Rightarrow> HAT x) = (if p k < Suc nat then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
          else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i))" for k
          using one I_mem_eq_cur_pos Suc nat_less_le 
          by (cases "d k", auto simp: tc1_def p1_def tup3_def compute_idx_set_def)
        then show ?thesis
          using one unfolding Suc place_hats_L_def place_hats_to_dir_def by auto
      next
        case two
        have "(case replace_sym tup bo k of
                 NO_HAT a \<Rightarrow> if k \<in> compute_idx_set tup bo \<and> d k = dir.N then HAT a else NO_HAT a
                 | HAT x \<Rightarrow> HAT x) = (if p k < Suc nat then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
          else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i))" for k
          using two 1(5,9) Suc tup elem(4) not_I_mem_current_pos
          by (cases "d k", auto simp: replace_sym_def compute_idx_set_def p1_def tc1_def)
        then show ?thesis
          unfolding two Suc enc2.simps place_hats_M_def place_hats_to_dir_def by simp
      next
        case three
        have "(case tup2 k of
                 NO_HAT a \<Rightarrow> if k \<in> compute_idx_set tup bo \<and> d k = dir.R then HAT a else NO_HAT a
                 | HAT x \<Rightarrow> HAT x) = (if p k < Suc nat then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
          else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i))" for k
          using three p1_def tc1_def compute_idx_set_def tup2 Suc 1(9) elem(4) I_mem_eq_cur_pos less_SucE
          unfolding 1(5) enc2.simps by (cases "d k", auto)
        then show ?thesis
          unfolding three Suc enc2.simps place_hats_R_def place_hats_to_dir_def by simp
      next
        case else
        have "(if p k < Suc (Suc nat) then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
         else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i)) =
        (if p k < Suc nat then if p k = i then HAT (tc k i) else NO_HAT (tc k i)
         else if p1 k = i then HAT (tc1 k i) else NO_HAT (tc1 k i))" for k
          unfolding 1(5) enc2.simps Suc
          using else  p1_def tc1_def 
          by (cases "d k") auto
        then show ?thesis
          using else Suc 1(5) enc2.simps by auto
      qed
    qed
    have correct_replace: "update_ys tup bo = (\<lambda>k. if p k < p' then SYM (b k) else \<bullet>)"
      by(insert I_mem_eq_cur_pos 1(9), auto simp: Suc update_ys_def)
    have step: "(?cs3, ?cs4) \<in> st.dstep ^^ 1"
      using mem5 dstep_help5[OF mem5]
      unfolding \<delta>'_def go_dir.simps relpow_1 Suc by fastforce
    hence "(cs, ?cs4) \<in> st.dstep ^^ 4"
      using relpow_transI[OF steps3 step] by simp
    moreover have "rel_E ?cs4 cm cm1 rule p'"
      using Suc 1 intros_helper2[OF _ _ 1(6) 1(7) 1(8) correct_replace] correct_shift by simp
    ultimately show ?thesis by blast
  qed
qed

lemma E_phase: assumes "rel_E\<^sub>0 cs cm cm1 rule" 
  shows "\<exists> cs'. (cs,cs') \<in> st.dstep ^^ (6 + 4 * Max (range (mt_pos cm))) \<and> rel_S\<^sub>0 cs' cm1" 
proof -
  from rel_E\<^sub>0_E[OF assms] obtain n cs1 where step1: "(cs, cs1) \<in> st.dstep" 
    and n: "n = Suc (Max (range (mt_pos cm)))" 
    and rel: "rel_E cs1 cm cm1 rule n" 
    by auto
  from rel have "\<exists> cs2. (cs1,cs2) \<in> st.dstep^^(4 * n) \<and> rel_E cs2 cm cm1 rule 0" 
  proof (induction n arbitrary: cs1 rule: nat_induct)
    case (Suc n)
    from rel_E_E[OF Suc.prems] obtain cs' where 
      step4: "(cs1, cs') \<in> st.dstep ^^ 4" and rel: "rel_E cs' cm cm1 rule n" by auto
    from Suc.IH[OF rel] obtain cs2 where 
      steps: "(cs', cs2) \<in> st.dstep ^^ (4 * n)" and rel: "rel_E cs2 cm cm1 rule 0"
      by auto
    from relpow_transI[OF step4 steps] rel show ?case by auto
  qed auto
  then obtain cs2 where steps2: "(cs1,cs2) \<in> st.dstep^^(4 * n)" and rel: "rel_E cs2 cm cm1 rule 0" by auto
  from rel_E_S\<^sub>0[OF rel] obtain cs' where step3: "(cs2, cs') \<in> st.dstep" and rel: "rel_S\<^sub>0 cs' cm1" by auto
  from relpow_Suc_I2[OF step1 relpow_Suc_I[OF steps2 step3]]
  have "(cs, cs') \<in> st.dstep ^^ Suc (Suc (4 * n))" by simp 
  also have "Suc (Suc (4 * n)) = 6 + 4 * Max (range (mt_pos cm))" unfolding n by simp
  finally show ?thesis using rel by auto
qed


subsubsection \<open>Simulation of multitape TM by singletape TM\<close>

lemma step_simulation: assumes "rel_S\<^sub>0 cs cm" 
  and "(cm, cm') \<in> step" 
shows "\<exists> cs'. (cs,cs') \<in> st.step ^^ (10 + 5 * Max (range (mt_pos cm))) \<and> rel_S\<^sub>0 cs' cm'" 
proof -
  let ?n = "Max (range (mt_pos cm))" 
  from assms(2) have "mt_state cm \<notin> {t, r}" using \<delta>_set
    by (cases, auto)
  from S_phase[OF assms(1) this] obtain cs1 where 
    steps1: "(cs, cs1) \<in> st.dstep ^^ (3 + ?n)" and rel: "rel_S\<^sub>1 cs1 cm" 
    by auto
  from rel_S\<^sub>1_E\<^sub>0_step[OF rel assms(2)] obtain r cs2 where
    step2: "(cs1, cs2) \<in> st.step" and rel: "rel_E\<^sub>0 cs2 cm cm' r" 
    by auto
  from E_phase[OF rel] obtain cs' where 
    steps3: "(cs2, cs') \<in> st.dstep ^^ (6 + 4 * ?n)" and rel: "rel_S\<^sub>0 cs' cm'" 
    by auto
  from relpow_transI[OF dsteps_to_steps[OF steps1] relpow_Suc_I2[OF step2 dsteps_to_steps[OF steps3]]]
  have "(cs, cs') \<in> st.step ^^ ((3 + ?n) + Suc (6 + 4 * ?n))" by simp
  also have "((3 + ?n) + Suc (6 + 4 * ?n)) = 10 + 5 * ?n" by simp
  finally show ?thesis using rel by auto
qed 

lemma steps_simulation_main: assumes "rel_S\<^sub>0 cs cm" 
  and "Max (range (mt_pos cm)) \<le> N" 
  and "(cm, cm') \<in> step^^n" 
shows "\<exists> m cs'. (cs,cs') \<in> st.step^^m \<and> rel_S\<^sub>0 cs' cm' \<and> m \<le> sum (\<lambda> i. 10 + 5 * (N + i)) {..< n} \<and> Max (range (mt_pos cm')) \<le> N + n" 
  using assms(3,1,2)
proof (induct n arbitrary: cm' N)
  case 0
  show ?case
    by (intro exI[of _ 0] exI[of _ cs], insert 0, auto)
next
  case (Suc n cm' N)
  from Suc(2) obtain cm'' where "(cm,cm'') \<in> step^^n" and step: "(cm'', cm') \<in> step" by auto
  from Suc(1)[OF this(1) Suc(3-4)] obtain m cs'' where
    steps: "(cs, cs'') \<in> st.step ^^ m" and m: "m \<le> (\<Sum>i < n. 10 + 5 * (N + i))" and rel: "rel_S\<^sub>0 cs'' cm''" and max: "Max (range (mt_pos cm'')) \<le> N + n" 
    by auto
  from step_simulation[OF rel step] obtain cs' where 
    steps2: "(cs'', cs') \<in> st.step ^^ (10 + 5 * Max (range (mt_pos cm'')))" and rel: "rel_S\<^sub>0 cs' cm'" by auto
  let ?m = "m + (10 + 5 * Max (range (mt_pos cm'')))" 
  from relpow_transI[OF steps steps2] 
  have steps: "(cs, cs') \<in> st.step ^^ ?m" by auto
  show ?case
  proof (intro exI conjI, rule steps, rule rel)
    from max_mt_pos_step[OF step] max 
    show "Max (range (mt_pos cm')) \<le> N + Suc n" by linarith
    have id: "{..<Suc n} = insert n {..< n}" by auto
    have "?m \<le> m + (10 + 5 * (N + n))" using max by presburger
    also have "\<dots> \<le> (\<Sum>i < Suc n. 10 + 5 * (N + i))" using m unfolding id by auto
    finally show "?m \<le> (\<Sum>i < Suc n. 10 + 5 * (N + i))" by auto
  qed
qed

lemma steps_simulation_rel_S\<^sub>0: assumes "rel_S\<^sub>0 cs (init_config w)" 
  and "(init_config w, cm') \<in> step^^n" 
shows "\<exists> m cs'. (cs,cs') \<in> st.step^^m \<and> rel_S\<^sub>0 cs' cm' \<and> m \<le> 3 * n^2 + 7 * n" 
proof -
  from steps_simulation_main[OF assms(1) _ assms(2), unfolded max_mt_pos_init, OF le_refl]
  obtain m cs' where steps: "(cs, cs') \<in> st.step ^^ m" and rel: "rel_S\<^sub>0 cs' cm'" and m: "m \<le> (\<Sum>i<n. 10 + 5 * i)" 
    by auto
  have "m \<le> (\<Sum>i<n. 10 + 5 * i)" by fact
  also have "\<dots> \<le> 3 * n^2 + 7 * n" using aux_sum_formula .
  finally show ?thesis using steps rel by auto
qed 

lemma simulation_with_complexity: assumes w: "set w \<subseteq> \<Sigma>" 
  and steps: "(init_config w, Config\<^sub>M q mtape p) \<in> step^^n" 
shows "\<exists> stape k. (st.init_config (map INP w), Config\<^sub>S (S\<^sub>0 q) stape 0) \<in> st.step^^k \<and> k \<le> 2 * length w + 3 * n^2 + 7 * n + 3" 
proof -
  let ?INP = "INP :: 'a \<Rightarrow> ('a, 'k) st_tape_symbol" 
  let ?initm = "init_config w" 
  define x where "x = map ?INP w" 
  from R_phase[OF w, folded x_def] obtain cs where 
    steps1: "(st.init_config x, cs) \<in> st.dstep ^^ (3 + 2 * length w)" and rel: "rel_S\<^sub>0 cs ?initm"
    by auto
  from steps_simulation_rel_S\<^sub>0[of _ w, OF rel steps] obtain k' cs' where 
    steps2: "(cs, cs') \<in> st.step^^k'" and 
    rel: "rel_S\<^sub>0 cs' (Config\<^sub>M q mtape p)" and 
    k': "k' \<le> 3 * n^2 + 7 * n" by auto
  let ?k = "3 + 2 * length w + k'" 
  from relpow_transI[OF dsteps_to_steps[OF steps1] steps2]
  have steps: "(st.init_config x, cs') \<in> st.step ^^ ?k" .
  from rel obtain stape where cs': "cs' = Config\<^sub>S (S\<^sub>0 q) stape 0" 
    by (cases, auto)
  show ?thesis
    by (intro exI[of _ stape] exI[of _ ?k], insert steps cs' k', auto simp: x_def)
qed


lemma simulation: "map INP ` Lang \<subseteq> st.Lang" 
proof
  fix x :: "('a, 'k) st_tape_symbol list" 
  assume "x \<in> map INP ` Lang" 
  then obtain w where mem: "w \<in> Lang" and x: "x = map INP w" by auto
  define cm where "cm = init_config w" 
  from mem[unfolded Lang_def] obtain w' n where w: "set w \<subseteq> \<Sigma>" and steps: "(cm, Config\<^sub>M t w' n) \<in> step^*" by (auto simp: cm_def)
  from rtrancl_imp_relpow[OF steps] obtain num where steps: "(cm, Config\<^sub>M t w' n) \<in> step^^num" by auto
  from simulation_with_complexity[OF w, folded cm_def, OF steps] obtain stape
    where steps: "(st.init_config (map INP w), Config\<^sub>S (S\<^sub>0 t) stape 0) \<in> st.step^*" 
    using relpow_imp_rtrancl by blast
  show "x \<in> st.Lang" using steps w unfolding x st.Lang_def by auto
qed

subsubsection \<open>Simulation of singletape TM by multitape TM\<close>

lemma rev_simulation: "st.Lang \<subseteq> map INP ` Lang" 
proof
  fix x :: "('a, 'k) st_tape_symbol list" 
  let ?INP = "INP :: 'a \<Rightarrow> ('a, 'k) st_tape_symbol" 
  assume "x \<in> st.Lang" 
  from this[unfolded st.Lang_def] obtain ts p where x: "set x \<subseteq> ?INP ` \<Sigma>" 
    and steps: "(st.init_config x, Config\<^sub>S (S\<^sub>0 t) ts p) \<in> st.step^*" by force
  let ?NF = "Config\<^sub>S (S\<^sub>0 t) ts p" 
  have NF: "\<not> (\<exists> c. (?NF, c) \<in> st.step)" 
  proof
    assume "\<exists> c. (?NF, c) \<in> st.step" 
    then obtain c where "(?NF, c) \<in> st.step" by auto
    thus False
      by (cases rule: st.step.cases, insert st.\<delta>_set, auto)
  qed
  from INP_D[OF x] obtain w where x: "x = map ?INP w" and w: "set w \<subseteq> \<Sigma>" by auto
  define cm where "cm = init_config w" 
  from R_phase[OF w, folded x] obtain cs where 
    dsteps: "(st.init_config x, cs) \<in> st.dstep ^^ (3 + 2 * length w)" and rel: "rel_S\<^sub>0 cs cm" 
    by (auto simp: cm_def)
  from steps obtain k where "(st.init_config x, ?NF) \<in> st.step^^k" using rtrancl_power by blast
  from st.dsteps_inj[OF dsteps this NF] obtain n where ssteps: "(cs, ?NF) \<in> st.step ^^ n" by auto
  from rel ssteps have "\<exists> cm'. (cm,cm') \<in> step^* \<and> rel_S\<^sub>0 ?NF cm'"
  proof (induct n arbitrary: cs cm rule: less_induct)
    case (less n cs cm)
    note rel = less(2)
    note steps = less(3)
    show ?case
    proof (cases "mt_state cm \<in> {t, r}")
      case True
      with rel obtain ts' p' q where cs: "cs = Config\<^sub>S (S\<^sub>0 q) ts' p'" and q: "q \<in> {t,r}" 
        by (cases, auto)
      have NF: False if "(cs, cs') \<in> st.step" for cs' using that unfolding cs using q
        by (cases rule: st.step.cases, insert st.\<delta>_set, auto)
      have "cs = ?NF" 
      proof (cases n)
        case 0
        thus ?thesis using steps by auto
      next
        case (Suc m)
        from NF relpow_Suc_E2[OF steps[unfolded this]] show ?thesis by auto
      qed
      thus ?thesis using rel by auto
    next
      case False
      define N where "N = Max (range (mt_pos cm))" 
      from S_phase[OF rel False] obtain cs1 where dsteps: "(cs, cs1) \<in> st.dstep ^^ (3 + N)" and rel: "rel_S\<^sub>1 cs1 cm" by (auto simp: N_def)
      from st.dsteps_inj[OF dsteps steps NF] obtain k1 where n: "n = 3 + N + k1" and steps: "(cs1, ?NF) \<in> st.step ^^ k1" by auto
      from rel have "cs1 \<noteq> ?NF" by (cases, auto)
      then obtain k where k1: "k1 = Suc k" using steps by (cases k1, auto)
      from relpow_Suc_E2[OF steps[unfolded this]] obtain cs2 where step: "(cs1, cs2) \<in> st.step" and steps: "(cs2,?NF) \<in> st.step ^^ k" by auto
      from rel_S\<^sub>1_E\<^sub>0_st_step[OF rel step] obtain cm1 rule where mstep: "(cm, cm1) \<in> step" and rel: "rel_E\<^sub>0 cs2 cm cm1 rule" by auto
      from E_phase[OF rel] obtain cs3 where dsteps: "(cs2, cs3) \<in> st.dstep ^^ (6 + 4 * N)" and rel: "rel_S\<^sub>0 cs3 cm1" by (auto simp: N_def)
      from st.dsteps_inj[OF dsteps steps NF] obtain m where k: "k = 6 + 4 * N + m" and steps: "(cs3, Config\<^sub>S (S\<^sub>0 t) ts p) \<in> st.step ^^ m" 
        by auto
      have "m < n" unfolding n k1 k by auto
      from less(1)[OF this rel steps] obtain cm' where msteps: "(cm1, cm') \<in> step^*" and rel: "rel_S\<^sub>0 ?NF cm'" by auto
      from mstep msteps have "(cm, cm') \<in> step^*" by auto
      with rel show ?thesis by auto
    qed
  qed
  then obtain cm' where msteps: "(cm, cm') \<in> step^*" and rel: "rel_S\<^sub>0 ?NF cm'" by auto
  from rel obtain tc p where cm': "cm' = Config\<^sub>M t tc p" by (cases, auto)
  from msteps have "w \<in> Lang" unfolding cm_def cm' Lang_def using w by auto
  thus "x \<in> map INP ` Lang" unfolding x by auto
qed

lemma rev_simulation_complexity: assumes w: "set w \<subseteq> \<Sigma>" 
  and steps: "(st.init_config (map INP w), cs) \<in> st.step^^n" 
  and n: "n \<ge> 2 * length w + 3 * k^2 + 7 * k + 3" 
shows "\<exists> cm. (init_config w, cm) \<in> step^^k" 
proof -
  let ?INP = "INP :: 'a \<Rightarrow> ('a, 'k) st_tape_symbol" 
  define cm1 where "cm1 = init_config w"  
  define x where "x = map ?INP w" 
  from R_phase[OF w, folded x_def] obtain cs1 where 
    steps1: "(st.init_config x, cs1) \<in> st.dstep ^^ (3 + 2 * length w)" and rel1: "rel_S\<^sub>0 cs1 cm1"
    by (auto simp: cm1_def)
  from st.dsteps_inj'[OF steps1 steps[folded x_def]] obtain n1 where 
    nn1: "n = 3 + 2 * length w + n1" and
    ssteps1: "(cs1, cs) \<in> st.step ^^ n1" 
    using n by auto  
  define M where "M = (0 :: nat)" 
  have r: "Max (range (mt_pos cm1)) \<le> M" unfolding M_def cm1_def by (simp add: max_mt_pos_init)
  from nn1 n have "n1 \<ge> 3 * k^2 + 7 * k" by auto
  hence n1: "n1 \<ge> sum (\<lambda> i. 10 + 5 * (M + i)) {..< k}" unfolding M_def 
    using aux_sum_formula[of k] by simp
  from ssteps1 rel1 n1 r show ?thesis unfolding cm1_def[symmetric]
  proof (induct k arbitrary: cs1 cm1 M n1)
    case (Suc k cs1 cm1 M n1)
    let ?M = "Max (range (mt_pos cm1))" 
    define n where "n = (\<Sum>i<k. 10 + 5 * (Suc M + i))" 
    from Suc(4) have "n1 \<ge> n + 10 + M * 5" unfolding n_def
      by (simp add: algebra_simps sum.distrib) 
    with Suc(5) have n1: "n1 \<ge> n + 10 + 5 * ?M" by linarith
    show ?case
    proof (cases "mt_state cm1 \<in> {t, r}")
      case False
      from S_phase[OF Suc(3) False]
      obtain cs2 where steps2: "(cs1, cs2) \<in> st.dstep ^^ (3 + ?M)" and rel2: "rel_S\<^sub>1 cs2 cm1" by auto
      from st.dsteps_inj'[OF steps2 Suc(2)] n1 obtain n2 where 
        n12: "n1 = 3 + ?M + n2" and 
        steps2: "(cs2, cs) \<in> st.step ^^ n2" 
        by auto      
      from n12 n1 obtain n3 where n23: "n2 = Suc n3" by (cases n2, auto)
      from steps2 obtain cs3 where step: "(cs2, cs3) \<in> st.step" and steps3: "(cs3,cs) \<in> st.step ^^ n3" unfolding n23 by (metis relpow_Suc_E2)
      from rel_S\<^sub>1_E\<^sub>0_st_step[OF rel2 step] obtain cm2 rule where step: "(cm1, cm2) \<in> step" and rel3: "rel_E\<^sub>0 cs3 cm1 cm2 rule" by auto
      let ?M2 = "Max (range (mt_pos cm2))" 
      from n1 n12 n23 have n3: "6 + 4 * ?M \<le> n3" by auto
      from E_phase[OF rel3] obtain cs4 where dsteps: "(cs3, cs4) \<in> st.dstep ^^ (6 + 4 * ?M)" and rel4: "rel_S\<^sub>0 cs4 cm2" by auto
      from st.dsteps_inj'[OF dsteps steps3 n3] obtain n4 where n34: "n3 = 6 + 4 * ?M + n4"
        and steps: "(cs4, cs) \<in> st.step ^^ n4" by auto
      from max_mt_pos_step[OF step] Suc(5) 
      have M2: "?M2 \<le> Suc M" by linarith
      have n4: "n \<le> n4" using n34 n12 n23 n1 by simp 
      from Suc(1)[OF steps rel4 n4[unfolded n_def] M2] obtain cm where "(cm2, cm) \<in> step ^^ k" ..
      with step have "(cm1, cm) \<in> step ^^ (Suc k)" by (metis relpow_Suc_I2)
      thus ?thesis ..
    next
      case True
      from n1 obtain n2 where "n1 = Suc n2" by (cases n1, auto)
      from relpow_Suc_E2[OF Suc(2)[unfolded this]]
      obtain cs2 where step: "(cs1, cs2) \<in> st.step" by auto      
      from rel_S\<^sub>0.cases[OF Suc(3)] obtain tc' q tc p where 
        cs1: "cs1 = Config\<^sub>S (S\<^sub>0 q) tc' 0" and
        cm1: "cm1 = Config\<^sub>M q tc p" 
        by metis
      with True have q: "q \<in> {t,r}" by auto
      from st.step.cases[OF step] obtain ts q' a dir where rule: "(S\<^sub>0 q, ts, q', a, dir) \<in> \<delta>'" 
        unfolding cs1 by fastforce
      with q have False unfolding \<delta>'_def by auto
      thus ?thesis by simp
    qed
  qed auto
qed

subsubsection \<open>Main Results\<close>

theorem language_equivalence: "st.Lang = map INP ` Lang" 
  using simulation rev_simulation by auto

theorem upper_time_bound_quadratic_increase: assumes "upper_time_bound f" 
  shows "st.upper_time_bound (\<lambda> n. 3 * (f n)^2 + 13 * f n + 2 * n + 12)" 
  unfolding st.upper_time_bound_def
proof (intro allI impI, rule ccontr)
  fix ww c n
  assume "set ww \<subseteq> INP ` \<Sigma>" and steps: "(st.init_config ww, c) \<in> st.step ^^ n" 
    and bnd: "\<not> n \<le> 3 * (f (length ww))\<^sup>2 + 13 * (f (length ww)) + 2 * length ww + 12" 
  from INP_D[OF this(1)] obtain w where w: "set w \<subseteq> \<Sigma>" and ww: "ww = map INP w" by auto
  let ?lw = "length w" 
  from bnd have "n \<ge> 2 * ?lw +  3 * (f ?lw + 1)\<^sup>2 + 7 * (f ?lw + 1) + 3" 
    by (auto simp: ww power2_eq_square)
  from rev_simulation_complexity[OF w steps[unfolded ww] this]
  obtain cm where "(init_config w, cm) \<in> step ^^ (f ?lw + 1)" by auto
  from assms[unfolded upper_time_bound_def, rule_format, OF w this] show False by simp
qed
end

subsection \<open>Main Results with Proper Renamings\<close>

text \<open>By using the renaming capabilities we can get rid of the @{term "map INP"} in the language
  equivalence theorem. We just assume that there will always be enough symbols for the renaming, 
  i.e., an infinite supply of fresh names is available.\<close>

theorem multitape_to_singletape: assumes "valid_mttm (mttm :: ('p,'a,'k :: {finite,zero})mttm)" 
  and "infinite (UNIV :: 'q set)" 
  and "infinite (UNIV :: 'a set)" 
shows "\<exists> tm :: ('q,'a)tm. valid_tm tm \<and> 
  Lang_mttm mttm = Lang_tm tm \<and> 
  (det_mttm mttm \<longrightarrow> det_tm tm) \<and>
  (upperb_time_mttm mttm f \<longrightarrow> upperb_time_tm tm (\<lambda> n. 3 * (f n)^2 + 13 * f n + 2 * n + 12))" 
proof (cases mttm)
  let ?INP = "INP :: 'a \<Rightarrow> ('a, 'k) st_tape_symbol" 
  case (MTTM Q \<Sigma> \<Gamma> bl le \<delta> s t r)
  from assms(1)[unfolded this]
  interpret multitape_tm Q \<Sigma> \<Gamma> bl le \<delta> s t r by simp
  let ?TM1 = "TM Q' (?INP ` \<Sigma>) \<Gamma>' blank' \<turnstile> \<delta>' (R\<^sub>1 \<bullet>) (S\<^sub>0 t) (S\<^sub>0 r)"
  have valid: "valid_tm ?TM1" unfolding valid_tm.simps using valid_st .
  interpret st: singletape_tm Q' "?INP ` \<Sigma>" \<Gamma>' blank' \<turnstile> \<delta>' "R\<^sub>1 \<bullet>" "S\<^sub>0 t" "S\<^sub>0 r" using valid_st .
  from language_equivalence 
  have id: "Lang_tm ?TM1 = map INP ` Lang_mttm mttm" unfolding MTTM by auto
  have "finite Q'" using st.fin_Q .
  with assms(2) have "\<exists> tq :: (('a, 'p, 'k) st_states \<Rightarrow> 'q). inj_on tq Q'" by (metis finite_infinite_inj_on)
  then obtain tq :: "_ \<Rightarrow> 'q" where "inj_on tq Q'" by blast
  hence tq: "inj_on tq (Q_tm ?TM1)" by simp

  from st.fin_\<Gamma> have finG': "finite \<Gamma>'" .
  from fin_\<Sigma> assms(3) have "infinite (UNIV - \<Sigma>)" by auto
  then obtain B :: "'a set" where B: "finite B" "card B = card \<Gamma>'" "B \<subseteq> UNIV - \<Sigma>" 
    by (meson infinite_arbitrarily_large)
  from st.fin\<Sigma> have finS': "finite (?INP ` \<Sigma>)" .
  from finG' B obtain ta' where bij: "bij_betw ta' \<Gamma>' B" 
    by (metis bij_betw_iff_card)
  define ta where "ta x = (if x \<in> ?INP ` \<Sigma> then (case x of INP y \<Rightarrow> y) else ta' x)" for x 
  have ta: "inj_on ta (\<Gamma>_tm ?TM1)" using bij B(3)
    by (auto simp: bij_betw_def inj_on_def ta_def split: st_tape_symbol.splits)
  obtain tm' :: "('q,'a)tm" where valid: "valid_tm tm'" and lang: "Lang_tm tm' = map ta ` map INP ` Lang_mttm mttm" 
    and det: "st.deterministic \<Longrightarrow> det_tm tm'" 
    and upper: "\<And> f. st.upper_time_bound f \<Longrightarrow> upperb_time_tm tm' f"
    using tm_renaming[OF valid ta tq, unfolded id] by auto
  note lang also have "map ta ` map INP ` Lang_mttm mttm = (\<lambda> w. w) ` Lang_mttm mttm" 
    unfolding image_comp o_def map_map
  proof (rule image_cong[OF refl])
    fix w
    assume "w \<in> Lang_mttm mttm" 
    hence w: "set w \<subseteq> \<Sigma>" unfolding Lang_def MTTM Lang_mttm.simps by auto
    show "map (\<lambda>x. ta (INP x)) w = w" 
      by (intro map_idI, insert w, auto simp: ta_def)
  qed
  finally have lang: "Lang_tm tm' = Lang_mttm mttm" by simp
  {
    assume "det_mttm mttm" 
    hence deterministic unfolding MTTM by simp
    from det_preservation[OF this] have st.deterministic by auto
    from det[OF this] have "det_tm tm'" .
  } note det = this
  {
    assume "upperb_time_mttm mttm f" 
    hence "upper_time_bound f" unfolding MTTM by simp
    from upper[OF upper_time_bound_quadratic_increase[OF this]]
    have "upperb_time_tm tm' (\<lambda>n. 3 * (f n)\<^sup>2 + 13 * f n + 2 * n + 12)" .
  } note upper = this
  from valid lang det upper show ?thesis by blast
qed


end
