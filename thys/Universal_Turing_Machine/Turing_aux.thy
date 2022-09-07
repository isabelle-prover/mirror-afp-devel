(* Title: thys/Turing_aux.thy
   Author:  Franz Regensburger (FABR) 04/2022
 *)

subsection \<open>Auxiliary theorems about Turing Machines\<close>

theory Turing_aux
  imports Turing
begin

(* -------------------------------------------- *)
(* START: enhanced/clarified semantics of fetch *)
(* -------------------------------------------- *)

fun fetch' :: "instr list \<Rightarrow> state \<Rightarrow> cell \<Rightarrow> instr"
  where
    "fetch' []                 s              b = (Nop, 0)"

  | "fetch' [iBk]              0              b  = (Nop, 0)" 
  | "fetch' [iBk]              (Suc 0)        Bk = iBk" 
  | "fetch' [iBk]              (Suc 0)        Oc = (Nop, 0)"
  | "fetch' [iBk]              (Suc (Suc s')) b  = (Nop, 0)"

  | "fetch' (iBk # iOc # inss) 0              b  = (Nop, 0)" 
  | "fetch' (iBk # iOc # inss) (Suc 0)        Bk = iBk" 
  | "fetch' (iBk # iOc # inss) (Suc 0)        Oc = iOc"
  | "fetch' (iBk # iOc # inss) (Suc (Suc s')) b  = fetch' inss (Suc s') b"

lemma fetch'_Nil:
  shows "fetch' [] s b = (Nop, 0)"
  by (cases s,force) (cases b;force)

lemma fetch'_eq_fetch_app: "fetch' tm s b = fetch tm s b"
proof (induct rule: fetch'.induct)
  case (1 s b)
  then show ?case by (cases b) (auto simp add: fetch_imp)
next
  case (2 iBk b)
  then show ?case by (cases b) auto
next
  case (3 iBk)
  then show ?case by auto
next
  case (4 iBk)
  then show ?case by auto
next
  case (5 iBk s' b)
  then show ?case by (cases b) auto
next
  case (6 iBk iOc inss b)
  then show ?case by (cases b) auto
next
  case (7 iBk iOc inss)
  then show ?case by  auto
next
  case (8 iBk iOc inss)
  then show ?case by  auto
next
  case (9 iBk iOc inss s' b)
  then show ?case by (cases b) auto
qed

corollary fetch'_eq_fetch: "fetch' = fetch"
  by (blast intro: fetch'_eq_fetch_app)

(* ------------------------------------------- *)
(* END: enhanced/clarified semantics of fetch  *)
(* ------------------------------------------- *)

(* ------------------------------------------- *)
(* step function versus step relation          *)
(* ------------------------------------------- *)

(* Definition for a step relation instead of a step function *)

definition
  tm_step0_rel :: "tprog0 \<Rightarrow> ((config \<times> config) set)"
  where
   "tm_step0_rel tp = {(c1, c2) . step0 c1 tp = c2}"

abbreviation tm_step0_rel_aux :: "[config, tprog0, config] \<Rightarrow> bool"   ("((1_)/ \<Turnstile>\<langle>(_)\<rangle>\<Midarrow>/ (1_))" 50)
  where
            "tm_step0_rel_aux c1 tp c2  \<equiv> (c1,c2) \<in> tm_step0_rel tp" 

theorem tm_step0_rel_iff_step0: "(c1 \<Turnstile>\<langle>tp\<rangle>\<Midarrow> c2) \<longleftrightarrow> step0 c1 tp = c2"
  unfolding tm_step0_rel_def by auto

(* The steps relation is the reflexive and transitive closure of the step relation  *)

definition tm_steps0_rel :: "tprog0 \<Rightarrow> ((config \<times> config) set)"
  where
   "tm_steps0_rel tp = rtrancl (tm_step0_rel tp)"

abbreviation tm_steps0_rel_aux :: "[config, tprog0, config] \<Rightarrow> bool"   ("((1_)/ \<Turnstile>\<langle>(_)\<rangle>\<Midarrow>\<^sup>*/ (1_))" 50)
  where
            "tm_steps0_rel_aux c1 tp c2  \<equiv> (c1,c2) \<in> tm_steps0_rel tp" 

lemma tm_step0_rel_power: "(tm_step0_rel tp ^^ n) = {(c1,c2) . steps0 c1 tp n = c2}"
proof (induct n)
  case 0
  then show ?case
    using prod.exhaust relpowp_0_I split_conv 
       by auto
next
  case (Suc n)
  then have IV: "tm_step0_rel tp ^^ n = {a. case a of (c1, c2) \<Rightarrow> steps0 c1 tp n = c2}"
    by auto
  show "tm_step0_rel tp ^^ Suc n = {a. case a of (c1, c2) \<Rightarrow> steps0 c1 tp (Suc n) = c2}"
  proof 
    show "tm_step0_rel tp ^^ Suc n \<subseteq> {a. case a of (c1, c2) \<Rightarrow> steps0 c1 tp (Suc n) = c2}"
      using IV step_red tm_step0_rel_def by auto
  next
    show "{a. case a of (c1, c2) \<Rightarrow> steps0 c1 tp (Suc n) = c2} \<subseteq> tm_step0_rel tp ^^ Suc n"
    proof
      fix cp
      assume "cp \<in> {a. case a of (c1, c2) \<Rightarrow> steps0 c1 tp (Suc n) = c2}"
      then have "\<exists>c1 c2. cp = (c1,c2) \<and> steps0 c1 tp (Suc n) = c2"        
        using prod.exhaust_sel by blast
      then obtain c1 c2 where "cp = (c1,c2) \<and> steps0 c1 tp (Suc n) = c2" by blast
      then show "cp \<in> tm_step0_rel tp ^^ Suc n"
        using IV step_red  tm_step0_rel_def by auto
    qed
  qed
qed

theorem tm_steps0_rel_iff_steps0: "(c1 \<Turnstile>\<langle>tp\<rangle>\<Midarrow>\<^sup>* c2) \<longleftrightarrow> (\<exists>stp. steps0 c1 tp stp = c2)"
proof -
  have major: "((c1 \<Turnstile>\<langle>tp\<rangle>\<Midarrow>\<^sup>* c2)) \<longleftrightarrow> (\<exists>n. (c1,c2) \<in> (tm_step0_rel tp ^^ n))"
    by (simp add: relpow_code_def rtrancl_power tm_step0_rel_def tm_steps0_rel_def)
  show ?thesis
  proof
    assume "(c1 \<Turnstile>\<langle>tp\<rangle>\<Midarrow>\<^sup>* c2)"
    with major have "(\<exists>n. (c1,c2) \<in> (tm_step0_rel tp ^^ n))" by auto
    then obtain n where w_n: "(c1,c2) \<in> (tm_step0_rel tp ^^ n)" by blast
    then show "\<exists>stp. steps0 c1 tp stp = c2" using tm_step0_rel_power
      by auto
  next
    assume "\<exists>stp. steps0 c1 tp stp = c2"
    then obtain stp where "steps0 c1 tp stp = c2" by blast
    then show "(c1 \<Turnstile>\<langle>tp\<rangle>\<Midarrow>\<^sup>* c2)"
      using tm_step0_rel_power major 
      by auto
  qed
qed

end
