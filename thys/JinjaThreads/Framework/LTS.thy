(*  Title:      JinjaThreads/Framework/LTS.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Labelled transition systems} *}

theory LTS
imports
  "../Basic/Aux"
  "../../Coinductive/TLList"
  "~~/src/HOL/Library/Quotient_Option"
begin

lemma option_rel_mono:
  "\<lbrakk> option_rel R x y; \<And>x y. R x y \<Longrightarrow> R' x y \<rbrakk> \<Longrightarrow> option_rel R' x y"
by(cases x)(case_tac [!] y, auto)

lemma nth_concat_conv:
  "n < length (concat xss) 
   \<Longrightarrow> \<exists>m n'. concat xss ! n = (xss ! m) ! n' \<and> n' < length (xss ! m) \<and> 
             m < length xss \<and> n = (\<Sum>i<m. length (xss ! i)) + n'"
using lnth_lconcat_conv[of n "llist_of (map llist_of xss)"]
  setsum_hom[where f = enat and h = "\<lambda>i. length (xss ! i)"]
by(clarsimp simp add: lconcat_llist_of zero_enat_def[symmetric]) blast


definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
where "flip f = (\<lambda>b a. f a b)"

text {* Create a dynamic list @{text "flip_simps"} of theorems for flip *}
ML {*
structure FlipSimpRules = Named_Thms
(
  val name = @{binding flip_simps}
  val description = "Simplification rules for flip in bisimulations"
)
*}
setup {* FlipSimpRules.setup *}

lemma flip_conv [flip_simps]: "flip f b a = f a b"
by(simp add: flip_def)

lemma flip_flip [flip_simps, simp]: "flip (flip f) = f"
by(simp add: flip_def)

lemma list_all2_flip [flip_simps]: "list_all2 (flip P) xs ys = list_all2 P ys xs"
unfolding flip_def list_all2_conv_all_nth by auto

lemma llist_all2_flip [flip_simps]: "llist_all2 (flip P) xs ys = llist_all2 P ys xs"
unfolding flip_def llist_all2_conv_all_lnth by auto

lemma rtranclp_flipD:
  assumes "(flip r)^** x y"
  shows "r^** y x" 
using assms
by(induct rule: rtranclp_induct)(auto intro: rtranclp.rtrancl_into_rtrancl simp add: flip_conv)

lemma rtranclp_flip [flip_simps]:
  "(flip r)^** = flip r^**"
by(auto intro!: ext iffI simp add: flip_conv flip_flip intro: rtranclp_flipD)

lemma prod_rel_flip [flip_simps]:
  "prod_rel (flip R) (flip S) = flip (prod_rel R S)"
by(auto intro!: ext simp add: flip_def)

lemma option_rel_flip [flip_simps]:
  "option_rel (flip R) = flip (option_rel R)"
by(simp add: fun_eq_iff option_rel_unfold flip_def)

lemma tllist_all2_flip [flip_simps]:
  "tllist_all2 (flip P) (flip Q) xs ys \<longleftrightarrow> tllist_all2 P Q ys xs"
proof
  assume "tllist_all2 (flip P) (flip Q) xs ys"
  thus "tllist_all2 P Q ys xs"
    by coinduct(auto elim: tllist_all2_cases simp add: flip_def)
next
  assume "tllist_all2 P Q ys xs"
  thus "tllist_all2 (flip P) (flip Q) xs ys"
    by coinduct(auto elim: tllist_all2_cases simp add: flip_def)
qed

subsection {* Labelled transition systems *}

type_synonym ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"

locale trsys = 
  fixes trsys :: "('s, 'tl) trsys" ("_/ -_\<rightarrow>/ _" [50, 0, 50] 60)
begin

abbreviation Trsys :: "('s, 'tl list) trsys" ("_/ -_\<rightarrow>*/ _" [50,0,50] 60)
where "\<And>tl. s -tl\<rightarrow>* s' \<equiv> rtrancl3p trsys s tl s'"

coinductive inf_step :: "'s \<Rightarrow> 'tl llist \<Rightarrow> bool" ("_ -_\<rightarrow>* \<infinity>" [50, 0] 80)
where inf_stepI: "\<lbrakk> trsys a b a'; a' -bs\<rightarrow>* \<infinity> \<rbrakk> \<Longrightarrow> a -LCons b bs\<rightarrow>* \<infinity>"

coinductive inf_step_table :: "'s \<Rightarrow> ('s \<times> 'tl \<times> 's) llist \<Rightarrow> bool" ("_ -_\<rightarrow>*t \<infinity>" [50, 0] 80)
where 
  inf_step_tableI:
  "\<And>tl. \<lbrakk> trsys s tl s'; s' -stls\<rightarrow>*t \<infinity> \<rbrakk> 
  \<Longrightarrow> s -LCons (s, tl, s') stls\<rightarrow>*t \<infinity>"

definition inf_step2inf_step_table :: "'s \<Rightarrow> 'tl llist \<Rightarrow> ('s \<times> 'tl \<times> 's) llist"
where
  "inf_step2inf_step_table s tls =
   llist_corec (s, tls) (\<lambda>(s, tls). case tls of LNil \<Rightarrow> None |
                                      LCons tl tls' \<Rightarrow> let s' = SOME s'. trsys s tl s' \<and> s' -tls'\<rightarrow>* \<infinity>
                                                    in Some ((s, tl, s'), (s', tls')))"

coinductive Rtrancl3p :: "'s \<Rightarrow> ('tl, 's) tllist \<Rightarrow> bool"
where 
  Rtrancl3p_refl: "Rtrancl3p a (TNil a)"
| Rtrancl3p_into_Rtrancl3p: "\<lbrakk> trsys a b a'; Rtrancl3p a' tr \<rbrakk> \<Longrightarrow> Rtrancl3p a (TCons b bs)"

coinductive Runs :: "'s \<Rightarrow> 'tl llist \<Rightarrow> bool"
where
  Stuck: "(\<And>tl s'. \<not> s -tl\<rightarrow> s') \<Longrightarrow> Runs s LNil"
| Step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; Runs s' tls \<rbrakk> \<Longrightarrow> Runs s (LCons tl tls)"

coinductive Runs_table :: "'s \<Rightarrow> ('s \<times> 'tl \<times> 's) llist \<Rightarrow> bool"
where
  Stuck: "(\<And>tl s'. \<not> s -tl\<rightarrow> s') \<Longrightarrow> Runs_table s LNil"
| Step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; Runs_table s' stlss \<rbrakk> \<Longrightarrow> Runs_table s (LCons (s, tl, s') stlss)"

inductive_simps Runs_table_simps:
  "Runs_table s LNil"
  "Runs_table s (LCons stls stlss)"

lemma inf_step_not_finite_llist:
  assumes r: "s -bs\<rightarrow>* \<infinity>"
  shows "\<not> lfinite bs"
proof
  assume "lfinite bs" thus False using r
    by(induct arbitrary: s rule: lfinite.induct)(auto elim: inf_step.cases)
qed

lemma inf_step2inf_step_table_LNil [simp]: "inf_step2inf_step_table s LNil = LNil"
by(simp add: inf_step2inf_step_table_def llist_corec)

lemma inf_step2inf_step_table_LCons [simp]:
  fixes tl shows
  "inf_step2inf_step_table s (LCons tl tls) =
   LCons (s, tl, SOME s'. trsys s tl s' \<and> s' -tls\<rightarrow>* \<infinity>) 
         (inf_step2inf_step_table (SOME s'. trsys s tl s' \<and> s' -tls\<rightarrow>* \<infinity>) tls)"
by(simp add: inf_step2inf_step_table_def llist_corec)

lemma lmap_inf_step2inf_step_table: "lmap (fst \<circ> snd) (inf_step2inf_step_table s tls) = tls"
proof -
  have "(lmap (fst \<circ> snd) (inf_step2inf_step_table s tls), tls) \<in> 
        {(lmap (fst \<circ> snd) (inf_step2inf_step_table s l), l) | l s. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain a l where q: "q = (lmap (fst \<circ> snd) (inf_step2inf_step_table a l), l)" by blast
    thus ?case by(cases l) fastforce+
  qed
qed

lemma inf_step_imp_inf_step_table:
  assumes inf: "s -tls\<rightarrow>* \<infinity>"
  shows "\<exists>stls. s -stls\<rightarrow>*t \<infinity> \<and> tls = lmap (fst \<circ> snd) stls"
proof -
  def stls: stls \<equiv> "inf_step2inf_step_table s tls"
  with inf have "\<exists>tls. s -tls\<rightarrow>* \<infinity> \<and> stls = inf_step2inf_step_table s tls" by blast
  hence "s -stls\<rightarrow>*t \<infinity>"
  proof coinduct
    case (inf_step_table s stls)
    then obtain tls where inf: "s -tls\<rightarrow>* \<infinity>"
      and stls: "stls = inf_step2inf_step_table s tls" by blast
    from inf show ?case
    proof cases
      case (inf_stepI tl s' tls')
      hence tls: "tls = LCons tl tls'" and r: "trsys s tl s'"
	and inf': "s' -tls'\<rightarrow>* \<infinity>" by simp_all
      let ?s' = "SOME s'. trsys s tl s' \<and> s' -tls'\<rightarrow>* \<infinity>"
      from tls stls have "stls = LCons (s, tl, ?s') (inf_step2inf_step_table ?s' tls')" by simp
      moreover from r inf' have "trsys s tl s' \<and> s' -tls'\<rightarrow>* \<infinity>" ..
      hence "trsys s tl ?s' \<and> ?s' -tls'\<rightarrow>* \<infinity>" by(rule someI)
      ultimately show ?thesis by blast
    qed
  qed
  moreover have "tls = lmap (fst \<circ> snd) stls" unfolding stls
    by(simp only: lmap_inf_step2inf_step_table)
  ultimately show ?thesis by blast
qed

lemma inf_step_table_imp_inf_step:
  assumes inf: "s-stls\<rightarrow>*t \<infinity>"
  shows "s -lmap (fst \<circ> snd) stls\<rightarrow>* \<infinity>"
proof -
  def tls: tls \<equiv> "lmap (fst \<circ> snd) stls"
  with inf have "\<exists>stls. s-stls\<rightarrow>*t \<infinity> \<and> tls = lmap (fst \<circ> snd) stls" by blast
  hence "s -tls\<rightarrow>* \<infinity>"
  proof(coinduct)
    case (inf_step s tls)
    then obtain stls where inf: "s -stls\<rightarrow>*t \<infinity>"
      and tls: "tls = lmap (fst \<circ> snd) stls" by blast
    from inf show ?case
    proof cases
      case (inf_step_tableI s' stls' tl)
      hence stls: "stls = LCons (s, tl, s') stls'" and r: "trsys s tl s'"
	and inf': "s' -stls'\<rightarrow>*t \<infinity>" by simp_all
      from stls tls have "tls = LCons tl (lmap (fst \<circ> snd) stls')" by simp
      with r inf' show ?thesis by blast
    qed
  qed
  thus ?thesis unfolding tls .
qed

lemma rtrancl3p_into_Rtrancl3p:
  "rtrancl3p trsys a bs a' \<Longrightarrow> Rtrancl3p a (tllist_of_llist a' (llist_of bs))"
by(induct rule: rtrancl3p_converse_induct)(auto intro: Rtrancl3p.intros)

lemma Runs_table_into_Runs:
  assumes "Runs_table s stlss"
  shows "Runs s (lmap (\<lambda>(s, tl, s'). tl) stlss)"
proof -
  def tls \<equiv> "lmap (\<lambda>(s, tl, s'). tl) stlss"
  with assms have "\<exists>stlss. tls = lmap (\<lambda>(s, tl, s'). tl) stlss \<and> Runs_table s stlss" by blast
  thus "Runs s tls"
  proof(coinduct)
    case (Runs s tls)
    then obtain stlss where "Runs_table s stlss" "tls = lmap (\<lambda>(s, tl, s'). tl) stlss" by blast
    thus ?case by (cases)auto
  qed
qed

lemma Runs_into_Runs_table:
  assumes "Runs s tls"
  obtains stlss
  where "tls = lmap (\<lambda>(s, tl, s'). tl) stlss"
  and "Runs_table s stlss"
proof -
  def step \<equiv>
    "\<lambda>(s, tls). case tls of 
        LNil \<Rightarrow> None 
      | LCons tl tls' \<Rightarrow> 
        let s' = SOME s'. s -tl\<rightarrow> s' \<and> Runs s' tls'
        in Some ((s, tl, s'), s', tls')"
  def stlss \<equiv> "\<lambda>s tls. llist_corec (s, tls) step"
  have [simp]: "\<And>s. stlss s LNil = LNil"
    unfolding stlss_def step_def by(simp add: llist_corec)
  have [simp]: "\<And>s tl tls. stlss s (LCons tl tls) = LCons (s, tl, SOME s'. s -tl\<rightarrow> s' \<and> Runs s' tls) (stlss (SOME s'. s -tl\<rightarrow> s' \<and> Runs s' tls) tls)"
    unfolding stlss_def step_def by(subst llist_corec) simp
  from assms
  have "(tls, lmap (\<lambda>(s, tl, s'). tl) (stlss s tls)) \<in> 
        {(tls, lmap (\<lambda>(s, tl, s'). tl) (stlss s tls)) | tls s. Runs s tls}" by blast
  hence "tls = lmap (\<lambda>(s, tl, s'). tl) (stlss s tls)"
  proof(coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain tls s where q: "q = (tls, lmap (\<lambda>(s, tl, s'). tl) (stlss s tls))"
      and Runs: "Runs s tls" by blast
    from Runs show ?case
    proof(cases)
      case (Step s' tls' tl)
      let ?P = "\<lambda>s'. s -tl\<rightarrow> s' \<and> Runs s' tls'"
      from `s -tl\<rightarrow> s'` `Runs s' tls'` have "?P s'" ..
      hence "?P (Eps ?P)" by(rule someI)
      hence "?EqLCons" using Step q by auto
      thus ?thesis ..
    qed(simp add: q)
  qed
  moreover
  def stlss' \<equiv> "stlss s tls"
  with assms have "\<exists>tls. stlss' = stlss s tls \<and> Runs s tls" by blast
  hence "Runs_table s stlss'"
  proof(coinduct)
    case (Runs_table s stlss')
    then obtain tls where "Runs s tls"
      and [simp]: "stlss' = stlss s tls" by blast
    thus ?case
    proof(cases)
      case (Step s' tls' tl)
      let ?P = "\<lambda>s'. s -tl\<rightarrow> s' \<and> Runs s' tls'"
      from `s -tl\<rightarrow> s'` `Runs s' tls'` have "?P s'" ..
      hence "?P (Eps ?P)" by(rule someI)
      with Step have ?Step by auto
      thus ?thesis ..
    qed simp
  qed
  ultimately show ?thesis unfolding stlss'_def by(rule that)
qed

lemma Runs_lappendE:
  assumes "Runs \<sigma> (lappend tls tls')"
  and "lfinite tls"
  obtains \<sigma>' where "\<sigma> -list_of tls\<rightarrow>* \<sigma>'"
  and "Runs \<sigma>' tls'"
proof(atomize_elim)
  from `lfinite tls` `Runs \<sigma> (lappend tls tls')`
  show "\<exists>\<sigma>'. \<sigma> -list_of tls\<rightarrow>* \<sigma>' \<and> Runs \<sigma>' tls'"
  proof(induct arbitrary: \<sigma>)
    case lfinite_LNil thus ?case by(auto)
  next
    case (lfinite_LConsI tls tl)
    from `Runs \<sigma> (lappend (LCons tl tls) tls')`
    show ?case unfolding lappend_LCons
    proof(cases)
      case (Step \<sigma>')
      from `Runs \<sigma>' (lappend tls tls') \<Longrightarrow> \<exists>\<sigma>''. \<sigma>' -list_of tls\<rightarrow>* \<sigma>'' \<and> Runs \<sigma>'' tls'` `Runs \<sigma>' (lappend tls tls')`
      obtain \<sigma>'' where "\<sigma>' -list_of tls\<rightarrow>* \<sigma>''" "Runs \<sigma>'' tls'" by blast
      from `\<sigma> -tl\<rightarrow> \<sigma>'` `\<sigma>' -list_of tls\<rightarrow>* \<sigma>''`
      have "\<sigma> -tl # list_of tls\<rightarrow>* \<sigma>''" by(rule rtrancl3p_step_converse)
      with `lfinite tls` have "\<sigma> -list_of (LCons tl tls)\<rightarrow>* \<sigma>''" by(simp)
      with `Runs \<sigma>'' tls'` show ?thesis by blast
    qed
  qed
qed

lemma Trsys_into_Runs:
  assumes "s -tls\<rightarrow>* s'"
  and "Runs s' tls'"
  shows "Runs s (lappend (llist_of tls) tls')"
using assms
by(induct rule: rtrancl3p_converse_induct)(auto intro: Runs.Step)

end

subsection {* Labelled transition systems with internal actions *}

locale \<tau>trsys = trsys +
  constrains trsys :: "('s, 'tl) trsys"
  fixes \<tau>move :: "('s, 'tl) trsys"
begin

inductive silent_move :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ -\<tau>\<rightarrow> _" [50, 50] 60)
where [intro]: "!!tl. \<lbrakk> trsys s tl s'; \<tau>move s tl s' \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow> s'"

declare silent_move.cases [elim]

lemma silent_move_iff: "silent_move = (\<lambda>s s'. (\<exists>tl. trsys s tl s' \<and> \<tau>move s tl s'))"
by(auto simp add: fun_eq_iff)

abbreviation silent_moves :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ -\<tau>\<rightarrow>* _" [50, 50] 60)
where "silent_moves == silent_move^**"

abbreviation silent_movet :: "'s \<Rightarrow> 's \<Rightarrow> bool" ("_ -\<tau>\<rightarrow>+ _" [50, 50] 60)
where "silent_movet == silent_move^++"

coinductive \<tau>diverge :: "'s \<Rightarrow> bool" ("_ -\<tau>\<rightarrow> \<infinity>" [50] 60)
where
  \<tau>divergeI: "\<lbrakk> s -\<tau>\<rightarrow> s'; s' -\<tau>\<rightarrow> \<infinity> \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow> \<infinity>"

coinductive \<tau>inf_step :: "'s \<Rightarrow> 'tl llist \<Rightarrow> bool" ("_ -\<tau>-_\<rightarrow>* \<infinity>" [50, 0] 60)
where
  \<tau>inf_step_Cons: "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; s'' -\<tau>-tls\<rightarrow>* \<infinity> \<rbrakk> \<Longrightarrow> s -\<tau>-LCons tl tls\<rightarrow>* \<infinity>"
| \<tau>inf_step_Nil: "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> s -\<tau>-LNil\<rightarrow>* \<infinity>"

coinductive \<tau>inf_step_table :: "'s \<Rightarrow> ('s \<times> 's \<times> 'tl \<times> 's) llist \<Rightarrow> bool" ("_ -\<tau>-_\<rightarrow>*t \<infinity>" [50, 0] 80)
where
  \<tau>inf_step_table_Cons:
  "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; s'' -\<tau>-tls\<rightarrow>*t \<infinity> \<rbrakk> \<Longrightarrow> s -\<tau>-LCons (s, s', tl, s'') tls\<rightarrow>*t \<infinity>"

| \<tau>inf_step_table_Nil:
  "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> s -\<tau>-LNil\<rightarrow>*t \<infinity>"

definition \<tau>inf_step2\<tau>inf_step_table :: "'s \<Rightarrow> 'tl llist \<Rightarrow> ('s \<times> 's \<times> 'tl \<times> 's) llist"
where
  "\<tau>inf_step2\<tau>inf_step_table s tls =
   llist_corec (s, tls) (\<lambda>(s, tls). case tls of LNil \<Rightarrow> None |
        LCons tl tls' \<Rightarrow> let (s', s'') = SOME (s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>-tls'\<rightarrow>* \<infinity>
                         in Some ((s, s', tl, s''), (s'', tls')))"

definition silent_move_from :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where "silent_move_from s0 s1 s2 \<longleftrightarrow> silent_moves s0 s1 \<and> silent_move s1 s2"

inductive \<tau>rtrancl3p :: "'s \<Rightarrow> 'tl list \<Rightarrow> 's \<Rightarrow> bool" ("_ -\<tau>-_\<rightarrow>* _" [50, 0, 50] 60)
where
  \<tau>rtrancl3p_refl: "\<tau>rtrancl3p s [] s"
| \<tau>rtrancl3p_step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; \<not> \<tau>move s tl s'; \<tau>rtrancl3p s' tls s'' \<rbrakk> \<Longrightarrow> \<tau>rtrancl3p s (tl # tls) s''"
| \<tau>rtrancl3p_\<tau>step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; \<tau>move s tl s'; \<tau>rtrancl3p s' tls s'' \<rbrakk> \<Longrightarrow> \<tau>rtrancl3p s tls s''"

coinductive \<tau>Runs :: "'s \<Rightarrow> ('tl, 's option) tllist \<Rightarrow> bool" ("_ \<Down> _" [50, 50] 51)
where
  Terminate: "\<lbrakk> s -\<tau>\<rightarrow>* s'; \<And>tl s''. \<not> s' -tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> s \<Down> TNil \<lfloor>s'\<rfloor>" 
| Diverge: "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> s \<Down> TNil None"
| Proceed: "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; s'' \<Down> tls \<rbrakk> \<Longrightarrow> s \<Down> TCons tl tls"

inductive_simps \<tau>Runs_simps:
  "s \<Down> TNil (Some s')"
  "s \<Down> TNil None"
  "s \<Down> TCons tl' tls"

coinductive \<tau>Runs_table :: "'s \<Rightarrow> ('tl \<times> 's, 's option) tllist \<Rightarrow> bool"
where 
  Terminate: "\<lbrakk> s -\<tau>\<rightarrow>* s'; \<And>tl s''. \<not> s' -tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> \<tau>Runs_table s (TNil \<lfloor>s'\<rfloor>)"
| Diverge: "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> \<tau>Runs_table s (TNil None)"
| Proceed:
  "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; \<tau>Runs_table s'' tls \<rbrakk> 
  \<Longrightarrow> \<tau>Runs_table s (TCons (tl, s'') tls)"

definition silent_move2 :: "'s \<Rightarrow> 'tl \<Rightarrow> 's \<Rightarrow> bool"
where "\<And>tl. silent_move2 s tl s' \<longleftrightarrow> s -tl\<rightarrow> s' \<and> \<tau>move s tl s'"

abbreviation silent_moves2 :: "'s \<Rightarrow> 'tl list \<Rightarrow> 's \<Rightarrow> bool"
where "silent_moves2 \<equiv> rtrancl3p silent_move2"

coinductive \<tau>Runs_table2 :: "'s \<Rightarrow> ('tl list \<times> 's \<times> 'tl \<times> 's, ('tl list \<times> 's) + 'tl llist) tllist \<Rightarrow> bool"
where 
  Terminate: "\<lbrakk> silent_moves2 s tls s'; \<And>tl s''. \<not> s' -tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> \<tau>Runs_table2 s (TNil (Inl (tls, s')))"
| Diverge: "trsys.inf_step silent_move2 s tls \<Longrightarrow> \<tau>Runs_table2 s (TNil (Inr tls))"
| Proceed:
  "\<And>tl. \<lbrakk> silent_moves2 s tls s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; \<tau>Runs_table2 s'' tlsstlss \<rbrakk> 
  \<Longrightarrow> \<tau>Runs_table2 s (TCons (tls, s', tl, s'') tlsstlss)"

inductive_simps \<tau>Runs_table2_simps:
  "\<tau>Runs_table2 s (TNil tlss)"
  "\<tau>Runs_table2 s (TCons tlsstls tlsstlss)"

lemma inf_step_table_all_\<tau>_into_\<tau>diverge:
  assumes "s -stls\<rightarrow>*t \<infinity>" "\<forall>(s, tl, s') \<in> lset stls. \<tau>move s tl s'"
  shows "s -\<tau>\<rightarrow> \<infinity>"
proof -
  from assms have "\<exists>stls. s -stls\<rightarrow>*t \<infinity> \<and> (\<forall>(s, tl, s') \<in> lset stls. \<tau>move s tl s')" by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>diverge s)
    then obtain stls where "s -stls\<rightarrow>*t \<infinity>" "\<And>s tl s'. (s, tl, s') \<in> lset stls \<Longrightarrow> \<tau>move s tl s'" by blast
    thus ?case by cases (auto simp add: silent_move_iff, blast)
  qed
qed

lemma inf_step_table_lappend_llist_ofD:
  "s -lappend (llist_of stls) (LCons (x, tl', x') xs)\<rightarrow>*t \<infinity>
  \<Longrightarrow> (s -map (fst \<circ> snd) stls\<rightarrow>* x) \<and> (x -LCons (x, tl', x') xs\<rightarrow>*t \<infinity>)"
proof(induct stls arbitrary: s)
  case Nil thus ?case by(auto elim: inf_step_table.cases intro: inf_step_table.intros rtrancl3p_refl)
next
  case (Cons st stls)
  note IH = `\<And>s. s -lappend (llist_of stls) (LCons (x, tl', x') xs)\<rightarrow>*t \<infinity> \<Longrightarrow>
                 s -map (fst \<circ> snd) stls\<rightarrow>* x \<and> x -LCons (x, tl', x') xs\<rightarrow>*t \<infinity>`
  from `s -lappend (llist_of (st # stls)) (LCons (x, tl', x') xs)\<rightarrow>*t \<infinity>`
  show ?case
  proof cases
    case (inf_step_tableI s' stls' tl)
    hence [simp]: "st = (s, tl, s')" "stls' = lappend (llist_of stls) (LCons (x, tl', x') xs)"
      and "s -tl\<rightarrow> s'" "s' -lappend (llist_of stls) (LCons (x, tl', x') xs)\<rightarrow>*t \<infinity>" by simp_all
    from IH[OF `s' -lappend (llist_of stls) (LCons (x, tl', x') xs)\<rightarrow>*t \<infinity>`]
    have "s' -map (fst \<circ> snd) stls\<rightarrow>* x" "x -LCons (x, tl', x') xs\<rightarrow>*t \<infinity>" by auto
    with `s -tl\<rightarrow> s'` show ?thesis by(auto simp add: o_def intro: rtrancl3p_step_converse)
  qed
qed

lemma inf_step_table_lappend_llist_of_\<tau>_into_\<tau>moves:
  assumes "lfinite stls"
  shows "\<lbrakk> s -lappend stls (LCons (x, tl' x') xs)\<rightarrow>*t \<infinity>; \<forall>(s, tl, s')\<in>lset stls. \<tau>move s tl s' \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow>* x"
using assms
proof(induct arbitrary: s rule: lfinite.induct)
  case lfinite_LNil thus ?case by(auto elim: inf_step_table.cases)
next
  case (lfinite_LConsI stls st)
  note IH = `\<And>s. \<lbrakk>s -lappend stls (LCons (x, tl' x') xs)\<rightarrow>*t \<infinity>; \<forall>(s, tl, s')\<in>lset stls. \<tau>move s tl s' \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow>* x`
  obtain s1 tl1 s1' where [simp]: "st = (s1, tl1, s1')" by(cases st)
  from `s -lappend (LCons st stls) (LCons (x, tl' x') xs)\<rightarrow>*t \<infinity>`
  show ?case
  proof cases
    case (inf_step_tableI X' STLS TL)
    hence [simp]: "s1 = s" "TL = tl1" "X' = s1'" "STLS = lappend stls (LCons (x, tl' x') xs)"
      and "s -tl1\<rightarrow> s1'" and "s1' -lappend stls (LCons (x, tl' x') xs)\<rightarrow>*t \<infinity>" by simp_all
    from `\<forall>(s, tl, s')\<in>lset (LCons st stls). \<tau>move s tl s'` have "\<tau>move s tl1 s1'" by simp
    moreover
    from IH[OF `s1' -lappend stls (LCons (x, tl' x') xs)\<rightarrow>*t \<infinity>`] `\<forall>(s, tl, s')\<in>lset (LCons st stls). \<tau>move s tl s'`
    have "s1' -\<tau>\<rightarrow>* x" by simp
    ultimately show ?thesis using `s -tl1\<rightarrow> s1'` by(auto intro: converse_rtranclp_into_rtranclp)
  qed
qed


lemma inf_step_table_into_\<tau>inf_step:
  assumes "s -stls\<rightarrow>*t \<infinity>"
  shows "s -\<tau>-lmap (fst \<circ> snd) (lfilter (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') stls)\<rightarrow>* \<infinity>"
proof -
  let ?P = "\<lambda>(s, tl, s'). \<not> \<tau>move s tl s'"
  def tls \<equiv> "lmap (fst \<circ> snd) (lfilter ?P stls)"
  with assms have "\<exists>stls. s -stls\<rightarrow>*t \<infinity> \<and> tls = lmap (fst \<circ> snd) (lfilter ?P stls)" by blast
  thus "s -\<tau>-tls\<rightarrow>* \<infinity>"
  proof(coinduct)
    case (\<tau>inf_step s tls)
    then obtain stls where inf_step: "s -stls\<rightarrow>*t \<infinity>"
      and tls_def: "tls = lmap (fst \<circ> snd) (lfilter ?P stls)" by blast
    show ?case
    proof(cases "stls \<in> Domain (findRel ?P)")
      case False
      hence "lfilter ?P stls = LNil" by(rule diverge_lfilter_LNil)
      with inf_step have ?\<tau>inf_step_Nil unfolding tls_def 
	by(auto simp add: lfilter_empty_conv intro: inf_step_table_all_\<tau>_into_\<tau>diverge)
      thus ?thesis ..
    next
      case True
      hence "lfilter ?P stls \<noteq> LNil" by(rule contrapos_pn)(rule lfilter_eq_LNil)
      then obtain x tl x' xs where stls: "lfilter ?P stls = LCons (x, tl, x') xs" by(auto simp add: neq_LNil_conv)
      from lfilter_eq_LConsD[OF this] obtain stls1 stls2
	where stls1: "stls = lappend stls1 (LCons (x, tl, x') stls2)"
	and "lfinite stls1"
	and \<tau>s: "\<forall>(s, tl, s')\<in>lset stls1. \<tau>move s tl s'"
	and n\<tau>: "\<not> \<tau>move x tl x'" and xs: "xs = lfilter ?P stls2" by blast
      from `lfinite stls1` inf_step \<tau>s have "s -\<tau>\<rightarrow>* x" unfolding stls1
	by(rule inf_step_table_lappend_llist_of_\<tau>_into_\<tau>moves)
      moreover from `lfinite stls1` have "llist_of (list_of stls1) = stls1" by(simp add: llist_of_list_of)
      with inf_step stls1 have "s -lappend (llist_of (list_of stls1)) (LCons (x, tl, x') stls2)\<rightarrow>*t \<infinity>" by simp
      from inf_step_table_lappend_llist_ofD[OF this]
      have "x -LCons (x, tl, x') stls2\<rightarrow>*t \<infinity>" ..
      hence "x -tl\<rightarrow> x'" "x' -stls2\<rightarrow>*t \<infinity>" by(auto elim: inf_step_table.cases)
      ultimately have ?\<tau>inf_step_Cons using xs n\<tau> by(auto simp add: tls_def stls o_def)
      thus ?thesis ..
    qed
  qed
qed


lemma inf_step_into_\<tau>inf_step:
  assumes "s -tls\<rightarrow>* \<infinity>"
  shows "\<exists>A. s -\<tau>-lsublist tls A\<rightarrow>* \<infinity>"
proof -
  from inf_step_imp_inf_step_table[OF assms]
  obtain stls where "s -stls\<rightarrow>*t \<infinity>" and tls: "tls = lmap (fst \<circ> snd) stls" by blast
  from `s -stls\<rightarrow>*t \<infinity>` have "s -\<tau>-lmap (fst \<circ> snd) (lfilter (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') stls)\<rightarrow>* \<infinity>"
    by(rule inf_step_table_into_\<tau>inf_step)
  hence "s -\<tau>-lsublist tls {n. enat n < llength stls \<and> (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') (lnth stls n)}\<rightarrow>* \<infinity>"
    unfolding lfilter_conv_lsublist tls by simp
  thus ?thesis by blast
qed

lemma silent_moves_into_\<tau>rtrancl3p:
  "s -\<tau>\<rightarrow>* s' \<Longrightarrow> s -\<tau>-[]\<rightarrow>* s'"
by(induct rule: converse_rtranclp_induct)(blast intro: \<tau>rtrancl3p.intros)+

lemma \<tau>rtrancl3p_into_silent_moves:
  "s -\<tau>-[]\<rightarrow>* s' \<Longrightarrow> s -\<tau>\<rightarrow>* s'"
apply(induct s tls\<equiv>"[] :: 'tl list" s' rule: \<tau>rtrancl3p.induct)
apply(auto intro: converse_rtranclp_into_rtranclp)
done

lemma \<tau>rtrancl3p_Nil_eq_\<tau>moves:
  "s -\<tau>-[]\<rightarrow>* s' \<longleftrightarrow> s -\<tau>\<rightarrow>* s'"
by(blast intro: silent_moves_into_\<tau>rtrancl3p \<tau>rtrancl3p_into_silent_moves)

lemma \<tau>rtrancl3p_trans [trans]:
  "\<lbrakk> s -\<tau>-tls\<rightarrow>* s'; s' -\<tau>-tls'\<rightarrow>* s'' \<rbrakk> \<Longrightarrow> s -\<tau>-tls @ tls'\<rightarrow>* s''"
apply(induct rule: \<tau>rtrancl3p.induct)
apply(auto intro: \<tau>rtrancl3p.intros)
done

lemma \<tau>rtrancl3p_SingletonE:
  fixes tl
  assumes red: "s -\<tau>-[tl]\<rightarrow>* s'''"
  obtains s' s'' where "s -\<tau>\<rightarrow>* s'" "s' -tl\<rightarrow> s''" "\<not> \<tau>move s' tl s''" "s'' -\<tau>\<rightarrow>* s'''"
proof(atomize_elim)
  from red show "\<exists>s' s''. s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>\<rightarrow>* s'''"
  proof(induct s tls\<equiv>"[tl]" s''')
    case (\<tau>rtrancl3p_step s s' s'')
    from `s -tl\<rightarrow> s'` `\<not> \<tau>move s tl s'` `s' -\<tau>-[]\<rightarrow>* s''` show ?case
      by(auto simp add: \<tau>rtrancl3p_Nil_eq_\<tau>moves)
   next
    case (\<tau>rtrancl3p_\<tau>step s s' s'' tl')
    then obtain t' t'' where "s' -\<tau>\<rightarrow>* t'" "t' -tl\<rightarrow> t''" "\<not> \<tau>move t' tl t''" "t'' -\<tau>\<rightarrow>* s''" by auto
    moreover
    from `s -tl'\<rightarrow> s'` `\<tau>move s tl' s'` have "s -\<tau>\<rightarrow>* s'" by blast
    ultimately show ?case by(auto intro: rtranclp_trans)
  qed
qed

lemma \<tau>rtrancl3p_snocI:
  "\<And>tl. \<lbrakk> \<tau>rtrancl3p s tls s''; s'' -\<tau>\<rightarrow>* s'''; s''' -tl\<rightarrow> s'; \<not> \<tau>move s''' tl s' \<rbrakk>
  \<Longrightarrow> \<tau>rtrancl3p s (tls @ [tl]) s'"
apply(erule \<tau>rtrancl3p_trans)
apply(fold \<tau>rtrancl3p_Nil_eq_\<tau>moves)
apply(drule \<tau>rtrancl3p_trans)
 apply(erule (1) \<tau>rtrancl3p_step)
 apply(rule \<tau>rtrancl3p_refl)
apply simp
done

lemma \<tau>diverge_rtranclp_silent_move:
  "\<lbrakk> silent_move^** s s'; s' -\<tau>\<rightarrow> \<infinity> \<rbrakk> \<Longrightarrow> s -\<tau>\<rightarrow> \<infinity>"
by(induct rule: converse_rtranclp_induct)(auto intro: \<tau>divergeI)

lemma \<tau>diverge_trancl_coinduct [consumes 1, case_names \<tau>diverge]:
  assumes X: "X s"
  and step: "\<And>s. X s \<Longrightarrow> \<exists>s'. silent_move^++ s s' \<and> (X s' \<or> s' -\<tau>\<rightarrow> \<infinity>)"
  shows "s -\<tau>\<rightarrow> \<infinity>"
proof -
  from X have "\<exists>s'. silent_move^** s s' \<and> X s'" by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>diverge s)
    then obtain s' where "silent_move\<^sup>*\<^sup>* s s'" "X s'" by blast
    from step[OF `X s'`] obtain s'''
      where "silent_move^++ s' s'''" "X s''' \<or> s''' -\<tau>\<rightarrow> \<infinity>" by blast
    from `silent_move\<^sup>*\<^sup>* s s'` show ?case
    proof(cases rule: converse_rtranclpE[consumes 1, case_names refl step])
      case refl
      moreover from tranclpD[OF `silent_move^++ s' s'''`] obtain s''
	where "silent_move s' s''" "silent_move^** s'' s'''" by blast
      ultimately show ?thesis using `silent_move^** s'' s'''` `X s''' \<or> s''' -\<tau>\<rightarrow> \<infinity>`
	by(auto intro: \<tau>diverge_rtranclp_silent_move)
    next
      case (step S)
      moreover from `silent_move\<^sup>*\<^sup>* S s'` `silent_move^++ s' s'''`
      have "silent_move^** S s'''" by(rule rtranclp_trans[OF _ tranclp_into_rtranclp])
      ultimately show ?thesis using `X s''' \<or> s''' -\<tau>\<rightarrow> \<infinity>` by(auto intro: \<tau>diverge_rtranclp_silent_move)
    qed
  qed
qed

lemma \<tau>diverge_trancl_measure_coinduct [consumes 2, case_names \<tau>diverge]:
  assumes major: "X s t" "wfP \<mu>"
  and step: "\<And>s t. X s t \<Longrightarrow> \<exists>s' t'. (\<mu> t' t \<and> s' = s \<or> silent_move^++ s s') \<and> (X s' t' \<or> s' -\<tau>\<rightarrow> \<infinity>)"
  shows "s -\<tau>\<rightarrow> \<infinity>"
proof -
  { fix s t
    assume "X s t"
    with `wfP \<mu>` have "\<exists>s' t'. silent_move^++ s s' \<and> (X s' t' \<or> s' -\<tau>\<rightarrow> \<infinity>)"
    proof(induct arbitrary: s rule: wfP_induct[consumes 1])
      case (1 t)
      hence IH: "\<And>s' t'. \<lbrakk> \<mu> t' t; X s' t' \<rbrakk> \<Longrightarrow>
                 \<exists>s'' t''. silent_move^++ s' s'' \<and> (X s'' t'' \<or> s'' -\<tau>\<rightarrow> \<infinity>)" by blast
      from step[OF `X s t`] obtain s' t'
	where "\<mu> t' t \<and> s' = s \<or> silent_move\<^sup>+\<^sup>+ s s'" "X s' t' \<or> s' -\<tau>\<rightarrow> \<infinity>" by blast
      from `\<mu> t' t \<and> s' = s \<or> silent_move\<^sup>+\<^sup>+ s s'` show ?case
      proof
	assume "\<mu> t' t \<and> s' = s"
	hence  "\<mu> t' t" and [simp]: "s' = s" by simp_all
	from `X s' t' \<or> s' -\<tau>\<rightarrow> \<infinity>` show ?thesis
	proof
	  assume "X s' t'"
	  from IH[OF `\<mu> t' t` this] show ?thesis by simp
	next
	  assume "s' -\<tau>\<rightarrow> \<infinity>" thus ?thesis
	    by cases(auto simp add: silent_move_iff)
	qed
      next
	assume "silent_move\<^sup>+\<^sup>+ s s'"
	thus ?thesis using `X s' t' \<or> s' -\<tau>\<rightarrow> \<infinity>` by blast
      qed
    qed }
  note X = this
  from `X s t` have "\<exists>t. X s t" ..
  thus ?thesis
  proof(coinduct rule: \<tau>diverge_trancl_coinduct)
    case (\<tau>diverge s)
    then obtain t where "X s t" ..
    from X[OF this] show ?case by blast
  qed
qed

lemma \<tau>inf_step2\<tau>inf_step_table_LNil [simp]: "\<tau>inf_step2\<tau>inf_step_table s LNil = LNil"
by(simp add: \<tau>inf_step2\<tau>inf_step_table_def llist_corec)

lemma \<tau>inf_step2\<tau>inf_step_table_LCons [simp]:
  fixes s tl ss tls
  defines "ss \<equiv> SOME (s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>-tls\<rightarrow>* \<infinity>"
  shows
  "\<tau>inf_step2\<tau>inf_step_table s (LCons tl tls) =
   LCons (s, fst ss, tl, snd ss) (\<tau>inf_step2\<tau>inf_step_table (snd ss) tls)"
by(simp add: ss_def \<tau>inf_step2\<tau>inf_step_table_def llist_corec split_beta)

lemma lmap_\<tau>inf_step2\<tau>inf_step_table: "lmap (fst \<circ> snd \<circ> snd) (\<tau>inf_step2\<tau>inf_step_table s tls) = tls"
proof -
  have "(lmap (fst \<circ> snd \<circ> snd) (\<tau>inf_step2\<tau>inf_step_table s tls), tls) \<in> 
        {(lmap (fst \<circ> snd \<circ> snd) (\<tau>inf_step2\<tau>inf_step_table s l), l) | l s. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain a l where q: "q = (lmap (fst \<circ> snd \<circ> snd) (\<tau>inf_step2\<tau>inf_step_table a l), l)" by blast
    thus ?case by(cases l) fastforce+
  qed
qed

lemma \<tau>inf_step_into_\<tau>inf_step_table:
  assumes "s -\<tau>-tls\<rightarrow>* \<infinity>"
  shows "s -\<tau>-\<tau>inf_step2\<tau>inf_step_table s tls\<rightarrow>*t \<infinity>"
proof -
  def sstls \<equiv> "\<tau>inf_step2\<tau>inf_step_table s tls"
  with assms have "\<exists>tls. s -\<tau>-tls\<rightarrow>* \<infinity> \<and> sstls = \<tau>inf_step2\<tau>inf_step_table s tls" by blast
  thus "s -\<tau>-sstls\<rightarrow>*t \<infinity>"
  proof(coinduct)
    case (\<tau>inf_step_table s sstls)
    then obtain tls where \<tau>inf: "s -\<tau>-tls\<rightarrow>* \<infinity>"
      and sstls: "sstls = \<tau>inf_step2\<tau>inf_step_table s tls" by blast
    from \<tau>inf show ?case
    proof(cases)
      case (\<tau>inf_step_Cons s' s'' tls' tl)
      let ?ss = "SOME (s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>-tls'\<rightarrow>* \<infinity>"
      from \<tau>inf_step_Cons have tls: "tls = LCons tl tls'" and "s -\<tau>\<rightarrow>* s'" "s' -tl\<rightarrow> s''"
	"\<not> \<tau>move s' tl s''" "s'' -\<tau>-tls'\<rightarrow>* \<infinity>" by simp_all
      hence "(\<lambda>(s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>-tls'\<rightarrow>* \<infinity>) (s', s'')" by simp
      hence "(\<lambda>(s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' -\<tau>-tls'\<rightarrow>* \<infinity>) ?ss" by(rule someI)
      with sstls tls have ?\<tau>inf_step_table_Cons by auto
      thus ?thesis ..
    next
      case \<tau>inf_step_Nil
      with sstls have ?\<tau>inf_step_table_Nil by simp
      thus ?thesis ..
    qed
  qed
qed

lemma \<tau>inf_step_imp_\<tau>inf_step_table:
  assumes "s -\<tau>-tls\<rightarrow>* \<infinity>"
  shows "\<exists>sstls. s -\<tau>-sstls\<rightarrow>*t \<infinity> \<and> tls = lmap (fst \<circ> snd \<circ> snd) sstls"
using \<tau>inf_step_into_\<tau>inf_step_table[OF assms]
by(auto simp only: lmap_\<tau>inf_step2\<tau>inf_step_table)

lemma \<tau>inf_step_table_into_\<tau>inf_step:
  assumes "s -\<tau>-sstls\<rightarrow>*t \<infinity>"
  shows "s -\<tau>-lmap (fst \<circ> snd \<circ> snd) sstls\<rightarrow>* \<infinity>"
proof -
  def tls \<equiv> "lmap (fst \<circ> snd \<circ> snd) sstls"
  with assms have "\<exists>sstls. s -\<tau>-sstls\<rightarrow>*t \<infinity> \<and> tls = lmap (fst \<circ> snd \<circ> snd) sstls" by blast
  thus "s -\<tau>-tls\<rightarrow>* \<infinity>"
  proof(coinduct)
    case (\<tau>inf_step s tls)
    then obtain sstls where "s -\<tau>-sstls\<rightarrow>*t \<infinity>" 
      and tls: "tls = lmap (fst \<circ> snd \<circ> snd) sstls" by blast
    thus ?case by cases(auto simp add: o_def)
  qed
qed


lemma silent_move_fromI [intro]:
  "\<lbrakk> silent_moves s0 s1; silent_move s1 s2 \<rbrakk> \<Longrightarrow> silent_move_from s0 s1 s2"
by(simp add: silent_move_from_def)

lemma silent_move_fromE [elim]:
  assumes "silent_move_from s0 s1 s2"
  obtains "silent_moves s0 s1" "silent_move s1 s2"
using assms by(auto simp add: silent_move_from_def)

lemma rtranclp_silent_move_from_imp_silent_moves:
  assumes s'x: "silent_move\<^sup>*\<^sup>* s' x"
  shows "(silent_move_from s')^** x z \<Longrightarrow> silent_moves s' z"
by(induct rule: rtranclp_induct)(auto intro: s'x)

lemma \<tau>diverge_not_wfP_silent_move_from:
  assumes "s -\<tau>\<rightarrow> \<infinity>"
  shows "\<not> wfP (flip (silent_move_from s))"
proof
  assume "wfP (flip (silent_move_from s))"
  moreover def Q == "{s'. silent_moves s s' \<and> s' -\<tau>\<rightarrow> \<infinity>}"
  hence "s \<in> Q" using `s -\<tau>\<rightarrow> \<infinity>` by(auto)
  ultimately have "\<exists>z\<in>Q. \<forall>y. silent_move_from s z y \<longrightarrow> y \<notin> Q"
    unfolding wfP_eq_minimal flip_simps by blast
  then obtain z where "z \<in> Q"
    and min: "\<And>y. silent_move_from s z y \<Longrightarrow> y \<notin> Q" by blast
  from `z \<in> Q` have "silent_moves s z" "z -\<tau>\<rightarrow> \<infinity>" unfolding Q_def by auto
  from `z -\<tau>\<rightarrow> \<infinity>` obtain y where "silent_move z y" "y -\<tau>\<rightarrow> \<infinity>" by cases auto
  from `silent_moves s z` `silent_move z y` have "silent_move_from s z y" ..
  hence "y \<notin> Q" by(rule min)
  moreover from `silent_moves s z` `silent_move z y` `y -\<tau>\<rightarrow> \<infinity>`
  have "y \<in> Q" unfolding Q_def by auto
  ultimately show False by contradiction
qed

lemma wfP_silent_move_from_unroll:
  assumes wfPs': "\<And>s'. s -\<tau>\<rightarrow> s' \<Longrightarrow> wfP (flip (silent_move_from s'))"
  shows "wfP (flip (silent_move_from s))"
  unfolding wfP_eq_minimal flip_conv
proof(intro allI impI)
  fix Q and x :: 's
  assume "x \<in> Q"
  show "\<exists>z\<in>Q. \<forall>y. silent_move_from s z y \<longrightarrow> y \<notin> Q"
  proof(cases "\<exists>s'. s -\<tau>\<rightarrow> s' \<and> (\<exists>x'. silent_moves s' x' \<and> x' \<in> Q)")
    case False
    hence "\<forall>y. silent_move_from s x y \<longrightarrow> \<not> y \<in> Q"
      by(cases "x=s")(auto, blast elim: converse_rtranclpE intro: rtranclp.rtrancl_into_rtrancl)
    with `x \<in> Q` show ?thesis by blast
  next
    case True
    then obtain s' x' where "s -\<tau>\<rightarrow> s'" and "silent_moves s' x'" and "x' \<in> Q"
      by auto
    from `s -\<tau>\<rightarrow> s'` have "wfP (flip (silent_move_from s'))" by(rule wfPs')
    from this `x' \<in> Q` obtain z where "z \<in> Q" and min: "\<And>y. silent_move_from s' z y \<Longrightarrow> \<not> y \<in> Q"
      and "(silent_move_from s')^** x' z"
      by (rule wfP_minimalE) (unfold flip_simps, blast)
    { fix y
      assume "silent_move_from s z y"
      with `(silent_move_from s')^** x' z` `silent_move^** s' x'`
      have "silent_move_from s' z y"
	by(blast intro: rtranclp_silent_move_from_imp_silent_moves)
      hence "\<not> y \<in> Q" by(rule min) }
    with `z \<in> Q` show ?thesis by(auto simp add: intro!: bexI)
  qed
qed

lemma not_wfP_silent_move_from_\<tau>diverge:
  assumes "\<not> wfP (flip (silent_move_from s))"
  shows "s -\<tau>\<rightarrow> \<infinity>"
using assms
proof(coinduct)
  case (\<tau>diverge s)
  { assume wfPs': "\<And>s'. s -\<tau>\<rightarrow> s' \<Longrightarrow> wfP (flip (silent_move_from s'))"
    hence "wfP (flip (silent_move_from s))" by(rule wfP_silent_move_from_unroll) }
  with \<tau>diverge have "\<exists>s'. s -\<tau>\<rightarrow> s' \<and> \<not> wfP (flip (silent_move_from s'))" by auto
  thus ?case by blast
qed

lemma \<tau>diverge_neq_wfP_silent_move_from:
  "s -\<tau>\<rightarrow> \<infinity> \<noteq> wfP (flip (silent_move_from s))"
by(auto intro: not_wfP_silent_move_from_\<tau>diverge dest: \<tau>diverge_not_wfP_silent_move_from)

lemma not_\<tau>diverge_to_no_\<tau>move:
  assumes "\<not> s -\<tau>\<rightarrow> \<infinity>"
  shows "\<exists>s'. s -\<tau>\<rightarrow>* s' \<and> (\<forall>s''. \<not> s' -\<tau>\<rightarrow> s'')"
proof -
  def S == s
  from `\<not> \<tau>diverge s` have "wfP (flip (silent_move_from S))" unfolding S_def
    using \<tau>diverge_neq_wfP_silent_move_from[of s] by simp
  moreover have "silent_moves S s" unfolding S_def ..
  ultimately show ?thesis
  proof(induct rule: wfP_induct')
    case (wfP s)
    note IH = `\<And>y. \<lbrakk>flip (silent_move_from S) y s; S -\<tau>\<rightarrow>* y \<rbrakk>
             \<Longrightarrow> \<exists>s'. y -\<tau>\<rightarrow>* s' \<and> (\<forall>s''. \<not> s' -\<tau>\<rightarrow> s'')`
    show ?case
    proof(cases "\<exists>s'. silent_move s s'")
      case False thus ?thesis by auto
    next
      case True
      then obtain s' where "s -\<tau>\<rightarrow> s'" ..
      with `S -\<tau>\<rightarrow>* s` have "flip (silent_move_from S) s' s"
	unfolding flip_conv by(rule silent_move_fromI)
      moreover from `S -\<tau>\<rightarrow>* s` `s -\<tau>\<rightarrow> s'` have "S -\<tau>\<rightarrow>* s'" ..
      ultimately have "\<exists>s''. s' -\<tau>\<rightarrow>* s'' \<and> (\<forall>s'''. \<not> s'' -\<tau>\<rightarrow> s''')" by(rule IH)
      then obtain s'' where "s' -\<tau>\<rightarrow>* s''" "\<forall>s'''. \<not> s'' -\<tau>\<rightarrow> s'''" by blast
      from `s -\<tau>\<rightarrow> s'` `s' -\<tau>\<rightarrow>* s''` have "s -\<tau>\<rightarrow>* s''" by(rule converse_rtranclp_into_rtranclp)
      with `\<forall>s'''. \<not> s'' -\<tau>\<rightarrow> s'''` show ?thesis by blast
    qed
  qed
qed

lemma \<tau>diverge_conv_\<tau>Runs:
  "s -\<tau>\<rightarrow> \<infinity> \<longleftrightarrow> s \<Down> TNil None"
by(auto intro: \<tau>Runs.Diverge elim: \<tau>Runs.cases)

lemma \<tau>inf_step_into_\<tau>Runs:
  assumes "s -\<tau>-tls\<rightarrow>* \<infinity>"
  shows "s \<Down> tllist_of_llist None tls"
proof -
  def tls' == "tllist_of_llist (None :: 's option) tls"
  with assms have "\<exists>tls. tls' = tllist_of_llist None tls \<and> s -\<tau>-tls\<rightarrow>* \<infinity>" by blast
  thus "s \<Down> tls'"
  proof(coinduct)
    case (\<tau>Runs s tls')
    then obtain tls where "s -\<tau>-tls\<rightarrow>* \<infinity>"
      and "tls' = tllist_of_llist None tls" by blast
    thus ?case by cases(auto simp add: \<tau>diverge_conv_\<tau>Runs)
  qed
qed

lemma \<tau>_into_\<tau>Runs:
  "\<lbrakk> s -\<tau>\<rightarrow> s'; s' \<Down> tls \<rbrakk> \<Longrightarrow> s \<Down> tls"
by(blast elim: \<tau>Runs.cases intro: \<tau>Runs.intros \<tau>diverge.intros converse_rtranclp_into_rtranclp)

lemma \<tau>rtrancl3p_into_\<tau>Runs:
  assumes "s -\<tau>-tls\<rightarrow>* s'"
  and "s' \<Down> tls'"
  shows "s \<Down> lappendt (llist_of tls) tls'"
using assms
by induct(auto intro: \<tau>Runs.Proceed \<tau>_into_\<tau>Runs)

lemma \<tau>Runs_table_into_\<tau>Runs:
  assumes "\<tau>Runs_table s stlsss"
  shows "s \<Down> tmap fst id stlsss"
proof -
  def tls == "tmap fst id stlsss"
  with assms have "\<exists>stlsss. tls = tmap fst id stlsss \<and> \<tau>Runs_table s stlsss" by blast
  thus "s \<Down> tls"
  proof coinduct
    case (\<tau>Runs s tls)
    then obtain stlsss where "\<tau>Runs_table s stlsss" "tls = tmap fst id stlsss" by blast
    thus ?case by cases(auto simp add: o_def id_def)
  qed
qed

definition \<tau>Runs2\<tau>Runs_table :: "'s \<Rightarrow> ('tl, 's option) tllist \<Rightarrow> ('tl \<times> 's, 's option) tllist"
where
  "\<tau>Runs2\<tau>Runs_table s tls = 
  tllist_corec (s, tls)
       (\<lambda>(s, tls). case tls of 
                     TNil b \<Rightarrow> Inr b
                   | TCons tl tls' \<Rightarrow> 
                     let s'' = SOME s''. \<exists>s'. s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'
                     in Inl ((tl, s''), (s'', tls')))"

lemma \<tau>Runs2\<tau>Runs_table_simps [simp, nitpick_simp]:
  "\<tau>Runs2\<tau>Runs_table s (TNil so) = TNil so"
  "\<And>tl. 
   \<tau>Runs2\<tau>Runs_table s (TCons tl tls) =
   (let s'' = SOME s''. \<exists>s'. s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls
    in TCons (tl, s'') (\<tau>Runs2\<tau>Runs_table s'' tls))"
unfolding \<tau>Runs2\<tau>Runs_table_def Let_def
 apply(simp add: tllist_corec)
apply(subst tllist_corec)
apply(simp add: split_beta)
done

lemma \<tau>Runs2\<tau>Runs_table_inverse:
  "tmap fst id (\<tau>Runs2\<tau>Runs_table s tls) = tls"
proof -
  have "(tmap fst id (\<tau>Runs2\<tau>Runs_table s tls), tls) \<in>
        {(tmap fst id (\<tau>Runs2\<tau>Runs_table s tls), tls)|tls s. True}" by blast
  thus ?thesis
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain tls s where q: "q = (tmap fst id (\<tau>Runs2\<tau>Runs_table s tls), tls)" by blast
    show ?case unfolding q
      by(cases tls)(auto simp add: split_beta)
  qed
qed
 
lemma \<tau>Runs_into_\<tau>Runs_table:
  assumes "s \<Down> tls"
  shows "\<exists>stlsss. tls = tmap fst id stlsss \<and> \<tau>Runs_table s stlsss"
proof(intro exI conjI)
  def stlsss == "\<tau>Runs2\<tau>Runs_table s tls"

  show "tls = tmap fst id stlsss"
    unfolding stlsss_def by(simp add: \<tau>Runs2\<tau>Runs_table_inverse)

  from assms have "\<exists>tls. stlsss = \<tau>Runs2\<tau>Runs_table s tls \<and> s \<Down> tls" unfolding stlsss_def by blast
  thus "\<tau>Runs_table s stlsss"
  proof coinduct
    case (\<tau>Runs_table s stlsss)
    then obtain tls where "s \<Down> tls" 
      and stlsss [simp]: "stlsss = \<tau>Runs2\<tau>Runs_table s tls" by blast
    thus ?case
    proof cases
      case (Terminate s')
      hence ?Terminate by simp
      thus ?thesis ..
    next
      case Diverge
      hence ?Diverge by simp
      thus ?thesis by simp
    next
      case (Proceed s' s'' tls' tl)
      let ?P = "\<lambda>s''. \<exists>s'. s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'"
      from Proceed have "?P s''" by auto
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Proceed using `tls = TCons tl tls'`
        by(auto simp add: split_beta)
      thus ?thesis by simp
    qed
  qed
qed

lemma \<tau>Runs_lappendtE:
  assumes "\<sigma> \<Down> lappendt tls tls'"
  and "lfinite tls"
  obtains \<sigma>' where "\<sigma> -\<tau>-list_of tls\<rightarrow>* \<sigma>'"
  and "\<sigma>' \<Down> tls'"
proof(atomize_elim)
  from `lfinite tls` `\<sigma> \<Down> lappendt tls tls'`
  show "\<exists>\<sigma>'. \<sigma> -\<tau>-list_of tls\<rightarrow>* \<sigma>' \<and> \<sigma>' \<Down> tls'"
  proof(induct arbitrary: \<sigma>)
    case lfinite_LNil thus ?case by(auto intro: \<tau>rtrancl3p_refl)
  next
    case (lfinite_LConsI tls tl)
    from `\<sigma> \<Down> lappendt (LCons tl tls) tls'`
    show ?case unfolding lappendt_LCons
    proof(cases)
      case (Proceed \<sigma>' \<sigma>'')
      from `\<sigma>'' \<Down> lappendt tls tls' \<Longrightarrow> \<exists>\<sigma>'''. \<sigma>'' -\<tau>-list_of tls\<rightarrow>* \<sigma>''' \<and> \<sigma>''' \<Down> tls'` `\<sigma>'' \<Down> lappendt tls tls'`
      obtain \<sigma>''' where "\<sigma>'' -\<tau>-list_of tls\<rightarrow>* \<sigma>'''" "\<sigma>''' \<Down> tls'" by blast
      from `\<sigma>' -tl\<rightarrow> \<sigma>''` `\<not> \<tau>move \<sigma>' tl \<sigma>''` `\<sigma>'' -\<tau>-list_of tls\<rightarrow>* \<sigma>'''`
      have "\<sigma>' -\<tau>-tl # list_of tls\<rightarrow>* \<sigma>'''" by(rule \<tau>rtrancl3p_step)
      with `\<sigma> -\<tau>\<rightarrow>* \<sigma>'` have "\<sigma> -\<tau>-[] @ (tl # list_of tls)\<rightarrow>* \<sigma>'''"
        unfolding \<tau>rtrancl3p_Nil_eq_\<tau>moves[symmetric] by(rule \<tau>rtrancl3p_trans)
      with `lfinite tls` have "\<sigma> -\<tau>-list_of (LCons tl tls)\<rightarrow>* \<sigma>'''" by(simp add: list_of_LCons)
      with `\<sigma>''' \<Down> tls'` show ?thesis by blast
    qed
  qed
qed

lemma \<tau>Runs_total:
  "\<exists>tls. \<sigma> \<Down> tls"
proof
  let ?\<tau>halt = "\<lambda>\<sigma> \<sigma>'. \<sigma> -\<tau>\<rightarrow>* \<sigma>' \<and> (\<forall>tl \<sigma>''. \<not> \<sigma>' -tl\<rightarrow> \<sigma>'')"
  let ?\<tau>diverge = "\<lambda>\<sigma>. \<sigma> -\<tau>\<rightarrow> \<infinity>"
  let ?proceed = "\<lambda>\<sigma> (tl, \<sigma>''). \<exists>\<sigma>'. \<sigma> -\<tau>\<rightarrow>* \<sigma>' \<and> \<sigma>' -tl\<rightarrow> \<sigma>'' \<and> \<not> \<tau>move \<sigma>' tl \<sigma>''"
  def step == 
    "\<lambda>\<sigma>. if (\<exists>\<sigma>'. ?\<tau>halt \<sigma> \<sigma>')
         then Inr (Some (SOME \<sigma>'. ?\<tau>halt \<sigma> \<sigma>'))
         else if ?\<tau>diverge \<sigma> then Inr None
         else Inl (SOME tl\<sigma>'. ?proceed \<sigma> tl\<sigma>')"
  def tls == "tllist_corec \<sigma> step"
  hence "tls = tllist_corec \<sigma> step" by simp
  thus "\<sigma> \<Down> tls"
  proof(coinduct rule: \<tau>Runs.coinduct)
    case (\<tau>Runs \<sigma> tls)[simp]
    show ?case
    proof(cases "\<exists>\<sigma>'. ?\<tau>halt \<sigma> \<sigma>'")
      case True
      hence "?\<tau>halt \<sigma> (SOME \<sigma>'. ?\<tau>halt \<sigma> \<sigma>')" by(rule someI_ex)
      hence ?Terminate using True unfolding \<tau>Runs
        by(subst tllist_corec)(simp add: step_def)
      thus ?thesis by simp
    next
      case False
      note \<tau>halt = this
      show ?thesis
      proof(cases "?\<tau>diverge \<sigma>")
        case True
        hence ?Diverge using True False unfolding \<tau>Runs
          by(subst tllist_corec)(simp add: step_def)
        thus ?thesis by simp
      next
        case False
        from not_\<tau>diverge_to_no_\<tau>move[OF this]
        obtain \<sigma>' where \<sigma>_\<sigma>': "\<sigma> -\<tau>\<rightarrow>* \<sigma>'"
          and no_\<tau>: "\<And>\<sigma>''. \<not> \<sigma>' -\<tau>\<rightarrow> \<sigma>''" by blast
        from \<sigma>_\<sigma>' \<tau>halt obtain tl \<sigma>'' where "\<sigma>' -tl\<rightarrow> \<sigma>''" by auto
        moreover with no_\<tau>[of \<sigma>''] have "\<not> \<tau>move \<sigma>' tl \<sigma>''" by auto
        ultimately have "?proceed \<sigma> (tl, \<sigma>'')" using \<sigma>_\<sigma>' by auto
        hence "?proceed \<sigma> (SOME tl\<sigma>. ?proceed \<sigma> tl\<sigma>)" by(rule someI)
        hence ?Proceed using False \<tau>halt unfolding \<tau>Runs
          by(subst tllist_corec)(fastforce simp add: step_def)
        thus ?thesis by simp
      qed
    qed
  qed
qed

lemma silent_move2_into_silent_move:
  fixes tl
  assumes "silent_move2 s tl s'"
  shows "s -\<tau>\<rightarrow> s'"
using assms by(auto simp add: silent_move2_def)

lemma silent_move_into_silent_move2:
  assumes "s -\<tau>\<rightarrow> s'"
  shows "\<exists>tl. silent_move2 s tl s'"
using assms by(auto simp add: silent_move2_def)

lemma silent_moves2_into_silent_moves:
  assumes "silent_moves2 s tls s'"
  shows "s -\<tau>\<rightarrow>* s'"
using assms
by(induct)(blast intro: silent_move2_into_silent_move rtranclp.rtrancl_into_rtrancl)+

lemma silent_moves_into_silent_moves2:
  assumes "s -\<tau>\<rightarrow>* s'"
  shows "\<exists>tls. silent_moves2 s tls s'"
using assms
by(induct)(blast dest: silent_move_into_silent_move2 intro: rtrancl3p_step)+

lemma inf_step_silent_move2_into_\<tau>diverge:
  assumes "trsys.inf_step silent_move2 s tls"
  shows "s -\<tau>\<rightarrow> \<infinity>"
proof -
  have "\<exists>tls. trsys.inf_step silent_move2 s tls"
    using assms by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>diverge s)
    then obtain tls where "trsys.inf_step silent_move2 s tls" ..
    thus ?case
      by(cases rule: trsys.inf_step.cases[consumes 1])(auto intro: silent_move2_into_silent_move)
  qed
qed

lemma \<tau>diverge_into_inf_step_silent_move2:
  assumes "s -\<tau>\<rightarrow> \<infinity>"
  obtains tls where "trsys.inf_step silent_move2 s tls"
proof -
  def step \<equiv> "\<lambda>s. let (tl, s') = SOME (tl, s'). silent_move2 s tl s' \<and> s' -\<tau>\<rightarrow> \<infinity> in Some (tl, s')"
  def tls \<equiv> "llist_corec s step"
  from assms have "s -\<tau>\<rightarrow> \<infinity> \<and> tls = llist_corec s step" unfolding tls_def by blast
  hence "trsys.inf_step silent_move2 s tls"
  proof(coinduct rule: trsys.inf_step.coinduct[consumes 1, case_names inf_step, case_conclusion inf_step step])
    case (inf_step s tls)
    let ?P = "\<lambda>(tl, s'). silent_move2 s tl s' \<and> s' -\<tau>\<rightarrow> \<infinity>"
    from inf_step obtain "s -\<tau>\<rightarrow> \<infinity>" and tls: "tls = llist_corec s step" ..
    from `s -\<tau>\<rightarrow> \<infinity>` obtain s' where "s -\<tau>\<rightarrow> s'" "s' -\<tau>\<rightarrow> \<infinity>" by cases
    from `s -\<tau>\<rightarrow> s'` obtain tl where "silent_move2 s tl s'" 
      by(blast dest: silent_move_into_silent_move2)
    with `s' -\<tau>\<rightarrow> \<infinity>` have "?P (tl, s')" by simp
    hence "?P (Eps ?P)" by(rule someI)
    thus ?case using tls
      by(subst (asm) llist_corec)(auto simp add: step_def)
  qed
  thus thesis by(rule that)
qed

lemma \<tau>Runs_into_\<tau>rtrancl3p:
  assumes runs: "s \<Down> tlss"
  and fin: "tfinite tlss"
  and terminal: "terminal tlss = \<lfloor>s'\<rfloor>"
  shows "\<tau>rtrancl3p s (list_of (llist_of_tllist tlss)) s'"
using fin runs terminal
proof(induct arbitrary: s rule: tfinite_induct)
  case TNil thus ?case by cases(auto intro: silent_moves_into_\<tau>rtrancl3p)
next
  case (TCons tl tlss)
  from `s \<Down> TCons tl tlss` obtain s'' s'''
    where step: "s -\<tau>\<rightarrow>* s''"
    and step2: "s'' -tl\<rightarrow> s'''" "\<not> \<tau>move s'' tl s'''" 
    and "s''' \<Down> tlss" by cases
  from `terminal (TCons tl tlss) = \<lfloor>s'\<rfloor>` have "terminal tlss = \<lfloor>s'\<rfloor>" by simp
  with `s''' \<Down> tlss` have "s''' -\<tau>-list_of (llist_of_tllist tlss)\<rightarrow>* s'" by(rule TCons)
  with step2 have "s'' -\<tau>-tl # list_of (llist_of_tllist tlss)\<rightarrow>* s'" by(rule \<tau>rtrancl3p_step)
  with step have "s -\<tau>-[] @ tl # list_of (llist_of_tllist tlss)\<rightarrow>* s'"
    by(rule \<tau>rtrancl3p_trans[OF silent_moves_into_\<tau>rtrancl3p])
  thus ?case using `tfinite tlss` by simp
qed

lemma \<tau>Runs_terminal_stuck:
  assumes Runs: "s \<Down> tlss"
  and fin: "tfinite tlss"
  and terminal: "terminal tlss = \<lfloor>s'\<rfloor>"
  and proceed: "s' -tls\<rightarrow> s''"
  shows False
using fin Runs terminal
proof(induct arbitrary: s rule: tfinite_induct)
  case TNil thus ?case using proceed by cases auto
next
  case TCons thus ?case by(fastforce elim: \<tau>Runs.cases)
qed

lemma Runs_table_silent_diverge:
  assumes "Runs_table s stlss"
  and "\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s'"
  and "\<not> lfinite stlss"
  shows "s -\<tau>\<rightarrow> \<infinity>"
proof -
  have "\<exists>stlss. Runs_table s stlss \<and> (\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s') \<and> \<not> lfinite stlss"
    using assms by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>diverge s)
    then obtain stlss where "Runs_table s stlss"
      and "\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s'"
      and "\<not> lfinite stlss" by blast
    thus ?case by cases auto
  qed
qed

lemma Runs_table_silent_rtrancl:
  assumes "lfinite stlss"
  and "Runs_table s stlss"
  and "\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s'"
  shows "s -\<tau>\<rightarrow>* llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss))" (is ?thesis1)
  and "llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss)) -tl'\<rightarrow> s'' \<Longrightarrow> False" (is "PROP ?thesis2")
proof -
  from assms have "?thesis1 \<and> (llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss)) -tl'\<rightarrow> s'' \<longrightarrow> False)"
  proof(induct arbitrary: s)
    case lfinite_LNil thus ?case by(auto elim: Runs_table.cases)
  next
    case (lfinite_LConsI stlss stls)
    from `Runs_table s (LCons stls stlss)`
    obtain tl s' where [simp]: "stls = (s, tl, s')"
      and "s -tl\<rightarrow> s'" and Run': "Runs_table s' stlss" by cases
    from `\<forall>(s, tl, s')\<in>lset (LCons stls stlss). \<tau>move s tl s'`
    have "\<tau>move s tl s'" and silent': "\<forall>(s, tl, s')\<in>lset stlss. \<tau>move s tl s'" by simp_all
    from `s -tl\<rightarrow> s'` `\<tau>move s tl s'` have "s -\<tau>\<rightarrow> s'" by auto
    moreover from Run' silent'
    have "s' -\<tau>\<rightarrow>* llast (LCons s' (lmap (\<lambda>(s, tl, s'). s') stlss)) \<and>
          (llast (LCons s' (lmap (\<lambda>(s, tl, s'). s') stlss)) -tl'\<rightarrow> s'' \<longrightarrow> False)"
      by(rule lfinite_LConsI)
    ultimately show ?case by(auto)
  qed
  thus ?thesis1 "PROP ?thesis2" by blast+
qed

lemma Runs_table_silent_lappendD:
  fixes s stlss
  defines "s' \<equiv> llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss))"
  assumes Runs: "Runs_table s (lappend stlss stlss')"
  and fin: "lfinite stlss"
  and silent: "\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s'"
  shows "s -\<tau>\<rightarrow>* s'" (is ?thesis1)
  and "Runs_table s' stlss'" (is ?thesis2)
  and "stlss' \<noteq> LNil \<Longrightarrow> s' = fst (lhd stlss')" (is "PROP ?thesis3")
proof -
  from fin Runs silent
  have "?thesis1 \<and> ?thesis2 \<and> (stlss' \<noteq> LNil \<longrightarrow> s' = fst (lhd stlss'))"
    unfolding s'_def
  proof(induct arbitrary: s)
    case lfinite_LNil thus ?case
      by(auto simp add: neq_LNil_conv Runs_table_simps)
  next
    case lfinite_LConsI thus ?case
      by(clarsimp simp add: neq_LNil_conv Runs_table_simps)(blast intro: converse_rtranclp_into_rtranclp)
  qed
  thus ?thesis1 ?thesis2 "PROP ?thesis3" by simp_all
qed

lemma Runs_table_into_\<tau>Runs:
  fixes s stlss
  defines "tls \<equiv> tmap (\<lambda>(s, tl, s'). tl) id (tfilter None (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') (tllist_of_llist (Some (llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss)))) stlss))"
  (is "_ \<equiv> ?conv s stlss")
  assumes "Runs_table s stlss"
  shows "\<tau>Runs s tls"
proof -
  from assms have "\<exists>stlss. tls = ?conv s stlss \<and> Runs_table s stlss"
    unfolding tls_def by blast
  thus ?thesis
  proof(coinduct)
    case (\<tau>Runs s tls)
    then obtain stlss where tls: "tls = ?conv s stlss"
      and Run: "Runs_table s stlss" by blast
    show ?case
    proof(cases tls)
      case (TNil so)[simp]
      from tls 
      have silent: "\<forall>(s, tl, s') \<in> lset stlss. \<tau>move s tl s'"
        by(auto simp add: TNil_eq_tmap_conv tfilter_empty_conv)
      show ?thesis
      proof(cases "lfinite stlss")
        case False
        with Run silent have "s -\<tau>\<rightarrow> \<infinity>" by(rule Runs_table_silent_diverge)
        hence ?Diverge using False tls by(simp add: TNil_eq_tmap_conv tfilter_empty_conv)
        thus ?thesis by simp
      next
        case True
        with Runs_table_silent_rtrancl[OF this Run silent]
        have ?Terminate using tls
          by(auto simp add: TNil_eq_tmap_conv tfilter_empty_conv terminal_tllist_of_llist split_def)
        thus ?thesis by simp
      qed
    next
      case (TCons tl tls')[simp]
      from tls obtain s' s'' stlss' 
        where tl': "tfilter None (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') (tllist_of_llist \<lfloor>llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss))\<rfloor> stlss) = TCons (s', tl, s'') stlss'"
        and tls': "tls' = tmap (\<lambda>(s, tl, s'). tl) id stlss'"
        by(simp add: TCons_eq_tmap_conv split_def id_def split_paired_Ex) blast
      from tfilter_eq_TConsD[OF tl']
      obtain stls\<tau> rest
        where stlss_eq: "tllist_of_llist \<lfloor>llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss))\<rfloor> stlss = lappendt stls\<tau> (TCons (s', tl, s'') rest)"
        and fin: "lfinite stls\<tau>"
        and silent: "\<forall>(s, tl, s')\<in>lset stls\<tau>. \<tau>move s tl s'"
        and "\<not> \<tau>move s' tl s''"
        and stlss': "stlss' = tfilter None (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') rest"
        by(auto simp add: split_def)
      from stlss_eq fin obtain rest'
        where stlss: "stlss = lappend stls\<tau> rest'"
        and rest': "tllist_of_llist \<lfloor>llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stlss))\<rfloor> rest' = TCons (s', tl, s'') rest"
        unfolding tllist_of_llist_eq_lappendt_conv by auto
      hence "rest' \<noteq> LNil" by clarsimp
      from Run[unfolded stlss] fin silent
      have "s -\<tau>\<rightarrow>* llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stls\<tau>))"
        and "Runs_table (llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stls\<tau>))) rest'"
        and "llast (LCons s (lmap (\<lambda>(s, tl, s'). s') stls\<tau>)) = fst (lhd rest')"
        by(rule Runs_table_silent_lappendD)+(simp add: `rest' \<noteq> LNil`)
      moreover with rest' `rest' \<noteq> LNil` stlss fin obtain rest''
        where rest': "rest' = LCons (s', tl, s'') rest''"
        and rest: "rest = tllist_of_llist \<lfloor>llast (LCons s'' (lmap (\<lambda>(s, tl, s'). s') rest''))\<rfloor> rest''"
        by(clarsimp simp add: neq_LNil_conv llast_LCons lmap_lappend_distrib)
      ultimately have "s -\<tau>\<rightarrow>* s'" "s' -tl\<rightarrow> s''" "Runs_table s'' rest''"
        by(simp_all add: Runs_table_simps)
      hence ?Proceed using `\<not> \<tau>move s' tl s''` tls' stlss' rest
        by(auto simp add: id_def)
      thus ?thesis by simp
    qed
  qed
qed

lemma \<tau>Runs_table2_into_\<tau>Runs:
  assumes "\<tau>Runs_table2 s tlsstlss"
  shows "s \<Down> tmap (\<lambda>(tls, s', tl, s''). tl) (\<lambda>x. case x of Inl (tls, s') \<Rightarrow> Some s' | Inr _ \<Rightarrow> None) tlsstlss"
  (is "s \<Down> ?conv tlsstlss")
proof -
  def tls \<equiv> "?conv tlsstlss"
  with assms have "\<exists>tlsstlss. \<tau>Runs_table2 s tlsstlss \<and> tls = ?conv tlsstlss" by blast
  thus "s \<Down> tls"
  proof(coinduct)
    case (\<tau>Runs s tls)
    then obtain tlsstlss 
      where "\<tau>Runs_table2 s tlsstlss" "tls = ?conv tlsstlss" by blast
    thus ?case by cases(auto intro: silent_moves2_into_silent_moves inf_step_silent_move2_into_\<tau>diverge)
  qed
qed

lemma \<tau>Runs_into_\<tau>Runs_table2:
  assumes "s \<Down> tls"
  obtains tlsstlss
  where "\<tau>Runs_table2 s tlsstlss"
  and "tls = tmap (\<lambda>(tls, s', tl, s''). tl) (\<lambda>x. case x of Inl (tls, s') \<Rightarrow> Some s' | Inr _ \<Rightarrow> None) tlsstlss"
proof -
  def step \<equiv>
    "\<lambda>(s, tls). 
     case tls of
       TNil so \<Rightarrow>
       case so of
         None \<Rightarrow> Inr (Inr (SOME tls'. trsys.inf_step silent_move2 s tls'))
       | Some s' \<Rightarrow> 
         let tls' = SOME tls'. silent_moves2 s tls' s'
         in Inr (Inl (tls', s'))
     | TCons tl tls' \<Rightarrow>
       let (tls'', s', s'') = SOME (tls'', s', s''). silent_moves2 s tls'' s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'
       in Inl ((tls'', s', tl, s''), s'', tls')"
  def tlsstlss \<equiv> "\<lambda>s tls. tllist_corec (s, tls) step"
  have [simp]: "\<And>s. tlsstlss s (TNil None) = TNil (Inr (SOME tls'. trsys.inf_step silent_move2 s tls'))"
               "\<And>s s'. tlsstlss s (TNil (Some s')) = TNil (Inl (SOME tls'. silent_moves2 s tls' s', s'))"
    unfolding tlsstlss_def by(simp_all add: tllist_corec step_def)

  let ?conv = "tmap (\<lambda>(tls, s', tl, s''). tl) (\<lambda>x. case x of Inl (tls, s') \<Rightarrow> Some s' | Inr _ \<Rightarrow> None)"
  def xs \<equiv> "tlsstlss s tls"
  hence "\<exists>tls. xs = tlsstlss s tls \<and> s \<Down> tls" using assms by blast
  hence "\<tau>Runs_table2 s xs"
  proof(coinduct)
    case (\<tau>Runs_table2 s xs)
    then obtain tls where xs: "xs = tlsstlss s tls"
      and "s \<Down> tls" by blast
    from `s \<Down> tls` show ?case
    proof(cases)
      case (Terminate s')
      let ?P = "\<lambda>tls'. silent_moves2 s tls' s'"
      from `s -\<tau>\<rightarrow>* s'` obtain tls' where "?P tls'" by(blast dest: silent_moves_into_silent_moves2)
      hence "?P (Eps ?P)" by(rule someI)
      with Terminate xs have ?Terminate by auto
      thus ?thesis by simp
    next
      case Diverge
      let ?P = "\<lambda>tls'. trsys.inf_step silent_move2 s tls'"
      from `s -\<tau>\<rightarrow> \<infinity>` obtain tls' where "?P tls'" by(rule \<tau>diverge_into_inf_step_silent_move2)
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Diverge using xs `tls = TNil None` by simp
      thus ?thesis by simp
    next
      case (Proceed s' s'' tls' tl)
      let ?P = "\<lambda>(tls'', s', s''). silent_moves2 s tls'' s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'"
      from `s -\<tau>\<rightarrow>* s'` obtain tls'' where "silent_moves2 s tls'' s'"
        by(blast dest: silent_moves_into_silent_moves2)
      with Proceed have "?P (tls'', s', s'')" by simp
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Proceed using xs Proceed unfolding tlsstlss_def
        by(subst (asm) tllist_corec)(auto simp add: step_def split_def)
      thus ?thesis by simp
    qed
  qed
  moreover
  have "(tls, ?conv (tlsstlss s tls)) \<in> {(tls, ?conv (tlsstlss s tls))|s tls. s \<Down> tls}"
    using assms unfolding tlsstlss_def by blast
  hence "tls = ?conv (tlsstlss s tls)"
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain s tls where q: "q = (tls, ?conv (tlsstlss s tls))"
      and "s \<Down> tls" by blast
    from `s \<Down> tls` show ?case
    proof(cases)
      case Terminate
      hence ?EqTNil using q by simp
      thus ?thesis ..
    next
      case Diverge
      hence ?EqTNil using q by simp
      thus ?thesis ..
    next
      case (Proceed s' s'' tls' tl)
      let ?P = "\<lambda>(tls'', s', s''). silent_moves2 s tls'' s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'"
      from `s -\<tau>\<rightarrow>* s'` obtain tls'' where "silent_moves2 s tls'' s'"
        by(blast dest: silent_moves_into_silent_moves2)
      with Proceed have "?P (tls'', s', s'')" by simp
      hence "?P (Eps ?P)" by(rule someI)
      hence ?EqTCons using q `tls = TCons tl tls'` unfolding tlsstlss_def
        by(subst (asm) tllist_corec)(auto simp add: step_def split_def)
      thus ?thesis ..
    qed
  qed
  ultimately show thesis unfolding xs_def by(rule that)
qed

lemma \<tau>Runs_table2_into_Runs:
  assumes "\<tau>Runs_table2 s tlsstlss"
  shows "Runs s (lconcat (lappend (lmap (\<lambda>(tls, s, tl, s'). llist_of (tls @ [tl])) (llist_of_tllist tlsstlss)) (LCons (case terminal tlsstlss of Inl (tls, s') \<Rightarrow> llist_of tls | Inr tls \<Rightarrow> tls) LNil)))"
  (is "Runs _ (?conv tlsstlss)")
proof -
  def tls \<equiv> "?conv tlsstlss"
  have "\<exists>tlsstlss. \<tau>Runs_table2 s tlsstlss \<and> tls = ?conv tlsstlss"
    using assms unfolding tls_def by blast
  thus "Runs s tls"
  proof(coinduct)
    case (Runs s tls)
    then obtain tlsstlss 
      where \<tau>Runs: "\<tau>Runs_table2 s tlsstlss"
      and tls: "tls = ?conv tlsstlss" by blast
    from \<tau>Runs show ?case
    proof(cases)
      case (Terminate tls' s')
      from `silent_moves2 s tls' s'` show ?thesis
      proof(cases rule: rtrancl3p_converseE)
        case refl 
        hence ?Stuck using Terminate tls by simp
        thus ?thesis ..
      next
        case (step tls'' tl s'')
        from `silent_moves2 s'' tls'' s'` `\<And>tl s''. \<not> s' -tl\<rightarrow> s''`
        have "\<tau>Runs_table2 s'' (TNil (Inl (tls'', s')))" ..
        with `tls' = tl # tls''` `silent_move2 s tl s''` `tlsstlss = TNil (Inl (tls', s'))` tls
        have ?Step by(fastforce simp add: silent_move2_def)
        thus ?thesis ..
      qed
    next
      case (Diverge tls')
      from `trsys.inf_step silent_move2 s tls'`
      obtain tl tls'' s' where "silent_move2 s tl s'" 
        and "tls' = LCons tl tls''" "trsys.inf_step silent_move2 s' tls''"
        by(cases rule: trsys.inf_step.cases[consumes 1]) auto
      from `trsys.inf_step silent_move2 s' tls''`
      have "\<tau>Runs_table2 s' (TNil (Inr tls''))" ..
      hence ?Step using `tlsstlss = TNil (Inr tls')` tls `tls' = LCons tl tls''` `silent_move2 s tl s'`
        by(fastforce simp add: silent_move2_def)
      thus ?thesis ..
    next
      case (Proceed tls' s' s'' tlsstlss' tl)
      from `silent_moves2 s tls' s'` have ?Step
      proof(cases rule: rtrancl3p_converseE)
        case refl with Proceed tls show ?thesis by auto
      next
        case (step tls'' tl' s''')
        from `silent_moves2 s''' tls'' s'` `s' -tl\<rightarrow> s''` `\<not> \<tau>move s' tl s''` `\<tau>Runs_table2 s'' tlsstlss'`
        have "\<tau>Runs_table2 s''' (TCons (tls'', s', tl, s'') tlsstlss')" ..
        with `tls' = tl' # tls''` `silent_move2 s tl' s'''` `tlsstlss = TCons (tls', s', tl, s'') tlsstlss'` tls
        show ?thesis by(fastforce simp add: silent_move2_def)
      qed
      thus ?thesis ..
    qed
  qed
qed

lemma \<tau>Runs_table2_silentsD:
  fixes tl
  assumes Runs: "\<tau>Runs_table2 s tlsstlss"
  and tset: "(tls, s', tl', s'') \<in> tset tlsstlss"
  and set: "tl \<in> set tls"
  shows "\<exists>s''' s''''. silent_move2 s''' tl s''''"
using tset Runs
proof(induct arbitrary: s rule: tset_induct)
  case (find tlsstlss')
  from `\<tau>Runs_table2 s (TCons (tls, s', tl', s'') tlsstlss')`
  have "silent_moves2 s tls s'" by cases
  thus ?case using set by induct auto
next
  case step thus ?case by(auto simp add: \<tau>Runs_table2_simps)
qed

lemma \<tau>Runs_table2_terminal_silentsD:
  assumes Runs: "\<tau>Runs_table2 s tlsstlss"
  and fin: "lfinite (llist_of_tllist tlsstlss)"
  and terminal: "terminal tlsstlss = Inl (tls, s'')"
  shows "\<exists>s'. silent_moves2 s' tls s''"
using fin Runs terminal
proof(induct "llist_of_tllist tlsstlss" arbitrary: tlsstlss s)
  case lfinite_LNil thus ?case 
    by(cases tlsstlss)(auto simp add: \<tau>Runs_table2_simps)
next
  case (lfinite_LConsI xs tlsstls)
  thus ?case by(cases tlsstlss)(auto simp add: \<tau>Runs_table2_simps)
qed

lemma \<tau>Runs_table2_terminal_inf_stepD:
  assumes Runs: "\<tau>Runs_table2 s tlsstlss"
  and fin: "lfinite (llist_of_tllist tlsstlss)"
  and terminal: "terminal tlsstlss = Inr tls"
  shows "\<exists>s'. trsys.inf_step silent_move2 s' tls"
using fin Runs terminal
proof(induct "llist_of_tllist tlsstlss" arbitrary: s tlsstlss)
  case lfinite_LNil thus ?case
    by(cases tlsstlss)(auto simp add: \<tau>Runs_table2_simps)
next
  case (lfinite_LConsI xs tlsstls)
  thus ?case by(cases tlsstlss)(auto simp add: \<tau>Runs_table2_simps)
qed

lemma \<tau>Runs_table2_lappendtD:
  assumes Runs: "\<tau>Runs_table2 s (lappendt tlsstlss tlsstlss')"
  and fin: "lfinite tlsstlss"
  shows "\<exists>s'. \<tau>Runs_table2 s' tlsstlss'"
using fin Runs
by(induct arbitrary: s)(auto simp add: \<tau>Runs_table2_simps)

end

lemma \<tau>moves_False: "\<tau>trsys.silent_move r (\<lambda>s ta s'. False) = (\<lambda>s s'. False)"
by(auto simp add: \<tau>trsys.silent_move_iff)

lemma \<tau>rtrancl3p_False_eq_rtrancl3p: "\<tau>trsys.\<tau>rtrancl3p r (\<lambda>s tl s'. False) = rtrancl3p r"
proof(intro ext iffI)
  fix s tls s'
  assume "\<tau>trsys.\<tau>rtrancl3p r (\<lambda>s tl s'. False) s tls s'"
  thus "rtrancl3p r s tls s'" by(rule \<tau>trsys.\<tau>rtrancl3p.induct)(blast intro: rtrancl3p_refl rtrancl3p_step_converse)+
next
  fix s tls s'
  assume "rtrancl3p r s tls s'"
  thus "\<tau>trsys.\<tau>rtrancl3p r (\<lambda>s tl s'. False) s tls s'"
    by(induct rule: rtrancl3p_converse_induct)(auto intro: \<tau>trsys.\<tau>rtrancl3p.intros)
qed

lemma \<tau>diverge_empty_\<tau>move:
  "\<tau>trsys.\<tau>diverge r (\<lambda>s ta s'. False) = (\<lambda>s. False)"
by(auto intro!: ext elim: \<tau>trsys.\<tau>diverge.cases \<tau>trsys.silent_move.cases)

end