(*  Title:      JinjaThreads/Framework/Bisimulation.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Various notions of bisimulation} *}

theory Bisimulation imports
  "FWState"
  "../../Coinductive/Coinductive_List_Lib"
begin

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
where "flip f = (\<lambda>b a. f a b)"

text {* Create a dynamic list @{text "flip_simps"} of theorems for flip *}
ML {*
  structure FlipSimpRules = Named_Thms
    (val name = "flip_simps"
     val description = "Simplification rules for flip in bisimulations")
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

subsection {* Labelled transition systems *}

types ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
types ('a, 'b) bisim = "'a \<Rightarrow> 'b \<Rightarrow> bool"

context trsys begin

coinductive inf_step :: "'s \<Rightarrow> 'tl llist \<Rightarrow> bool" ("_ -_\<rightarrow>* \<infinity>" [50, 0] 80)
where inf_stepI: "\<lbrakk> trsys a b a'; a' -bs\<rightarrow>* \<infinity> \<rbrakk> \<Longrightarrow> a -LCons b bs\<rightarrow>* \<infinity>"

coinductive inf_step_table :: "'s \<Rightarrow> ('s \<times> 'tl \<times> 's) llist \<Rightarrow> bool" ("_ -_\<rightarrow>*t \<infinity>" [50, 0] 80)
where inf_step_tableI: "\<And>tl. \<lbrakk> trsys s tl s'; s' -stls\<rightarrow>*t \<infinity> \<rbrakk> \<Longrightarrow> s -LCons (s, tl, s') stls\<rightarrow>*t \<infinity>"

definition inf_step2inf_step_table :: "'s \<Rightarrow> 'tl llist \<Rightarrow> ('s \<times> 'tl \<times> 's) llist"
where
  "inf_step2inf_step_table s tls =
   llist_corec (s, tls) (\<lambda>(s, tls). case tls of LNil \<Rightarrow> None |
                                      LCons tl tls' \<Rightarrow> let s' = SOME s'. trsys s tl s' \<and> s' -tls'\<rightarrow>* \<infinity>
                                                    in Some ((s, tl, s'), (s', tls')))"


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
   LCons (s, tl, SOME s'. trsys s tl s' \<and> s' -tls\<rightarrow>* \<infinity>) (inf_step2inf_step_table (SOME s'. trsys s tl s' \<and> s' -tls\<rightarrow>* \<infinity>) tls)"
by(simp add: inf_step2inf_step_table_def llist_corec)

lemma lmap_inf_step2inf_step_table: "lmap (fst \<circ> snd) (inf_step2inf_step_table s tls) = tls"
proof -
  have "(lmap (fst \<circ> snd) (inf_step2inf_step_table s tls), tls) \<in> 
        {(lmap (fst \<circ> snd) (inf_step2inf_step_table s l), l) | l s. True}" by blast
  then show ?thesis
  proof (coinduct rule: llist_equalityI)
    case (Eqllist q)
    then obtain a l where q: "q = (lmap (fst \<circ> snd) (inf_step2inf_step_table a l), l)" by blast
    thus ?case by(cases l) fastsimp+
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
  hence "s -\<tau>-lsublist tls {n. Fin n < llength stls \<and> (\<lambda>(s, tl, s'). \<not> \<tau>move s tl s') (lnth stls n)}\<rightarrow>* \<infinity>"
    unfolding lfilter_conv_lsublist tls by simp
  thus ?thesis by blast
qed

inductive \<tau>rtrancl3p :: "'s \<Rightarrow> 'tl list \<Rightarrow> 's \<Rightarrow> bool" ("_ -\<tau>-_\<rightarrow>* _" [50, 0, 50] 60)
where
  \<tau>rtrancl3p_refl: "\<tau>rtrancl3p s [] s"
| \<tau>rtrancl3p_step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; \<not> \<tau>move s tl s'; \<tau>rtrancl3p s' tls s'' \<rbrakk> \<Longrightarrow> \<tau>rtrancl3p s (tl # tls) s''"
| \<tau>rtrancl3p_\<tau>step: "\<And>tl. \<lbrakk> s -tl\<rightarrow> s'; \<tau>move s tl s'; \<tau>rtrancl3p s' tls s'' \<rbrakk> \<Longrightarrow> \<tau>rtrancl3p s tls s''"

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
    thus ?case by(cases l) fastsimp+
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

definition silent_move_from :: "'s \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where "silent_move_from s0 s1 s2 \<longleftrightarrow> silent_moves s0 s1 \<and> silent_move s1 s2"

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
      by(cases "x=s")(auto simp add: mem_def, blast elim: converse_rtranclpE intro: rtranclp.rtrancl_into_rtrancl)
    with `x \<in> Q` show ?thesis by blast
  next
    case True
    then obtain s' x' where "s -\<tau>\<rightarrow> s'" and "silent_moves s' x'" and "x' \<in> Q"
      by(auto simp add: mem_def)
    from `s -\<tau>\<rightarrow> s'` have "wfP (flip (silent_move_from s'))" by(rule wfPs')
    moreover from `x' \<in> Q` have "Q x'" by(simp add: mem_def)
    ultimately obtain z where "Q z" and min: "\<And>y. silent_move_from s' z y \<Longrightarrow> \<not> Q y"
      and "(silent_move_from s')^** x' z"
      by(rule wfP_minimalE)(unfold flip_simps, blast)
    { fix y
      assume "silent_move_from s z y"
      with `(silent_move_from s')^** x' z` `silent_move^** s' x'`
      have "silent_move_from s' z y"
	by(blast intro: rtranclp_silent_move_from_imp_silent_moves)
      hence "\<not> Q y" by(rule min) }
    with `Q z` show ?thesis by(auto simp add: mem_def intro!: bexI)
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

subsection {* Strong bisimulation *}

locale bisimulation_base = r1!: trsys trsys1 + r2!: trsys trsys2
  for trsys1 :: "('s1, 'tl1) trsys" ("_/ -1-_\<rightarrow>/ _" [50,0,50] 60)
  and trsys2 :: "('s2, 'tl2) trsys" ("_/ -2-_\<rightarrow>/ _" [50,0,50] 60) +
  fixes bisim :: "('s1, 's2) bisim" ("_/ \<approx> _" [50, 50] 60)
  and tlsim :: "('tl1, 'tl2) bisim" ("_/ \<sim> _" [50, 50] 60)
begin

notation
  r1.Trsys ("_/ -1-_\<rightarrow>*/ _" [50,0,50] 60) and
  r2.Trsys ("_/ -2-_\<rightarrow>*/ _" [50,0,50] 60)

notation
  r1.inf_step ("_ -1-_\<rightarrow>* \<infinity>" [50, 0] 80) and
  r2.inf_step ("_ -2-_\<rightarrow>* \<infinity>" [50, 0] 80)

notation
  r1.inf_step_table ("_ -1-_\<rightarrow>*t \<infinity>" [50, 0] 80) and
  r2.inf_step_table ("_ -2-_\<rightarrow>*t \<infinity>" [50, 0] 80)

abbreviation Tlsim :: "('tl1 list, 'tl2 list) bisim" ("_/ [\<sim>] _" [50, 50] 60)
where "Tlsim tl1 tl2 \<equiv> list_all2 tlsim tl1 tl2"

abbreviation Tlsiml :: "('tl1 llist, 'tl2 llist) bisim" ("_/ [[\<sim>]] _" [50, 50] 60)
where "Tlsiml tl1 tl2 \<equiv> llist_all2 tlsim tl1 tl2"

end

locale bisimulation = bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  assumes simulation1: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2' tl2. s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
  and simulation2: "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1' tl1. s1 -1-tl1\<rightarrow> s1' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma bisimulation_flip:
  "bisimulation trsys2 trsys1 (flip bisim) (flip tlsim)"
by(unfold_locales)(unfold flip_simps,(blast intro: simulation1 simulation2)+)

end

lemma bisimulation_flip_simps [flip_simps]:
  "bisimulation trsys2 trsys1 (flip bisim) (flip tlsim) = bisimulation trsys1 trsys2 bisim tlsim"
by(auto dest: bisimulation.bisimulation_flip simp only: flip_flip)

context bisimulation begin

lemma simulation1_rtrancl:
  "\<lbrakk>s1 -1-tls1\<rightarrow>* s1'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by(auto intro: rtrancl3p.rtrancl3p_refl)
next
  case (rtrancl3p_step s1 tls1 s1' tl1 s1'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2` `s1 \<approx> s2`
  obtain s2' tls2 where "s2 -2-tls2\<rightarrow>* s2'" "s1' \<approx> s2'" "tls1 [\<sim>] tls2" by blast
  moreover from `s1' -1-tl1\<rightarrow> s1''` `s1' \<approx> s2'`
  obtain s2'' tl2 where "s2' -2-tl2\<rightarrow> s2''" "s1'' \<approx> s2''" "tl1 \<sim> tl2" by(auto dest: simulation1)
  ultimately have "s2 -2-tls2 @ [tl2]\<rightarrow>* s2''" "tls1 @ [tl1] [\<sim>] tls2 @ [tl2]"
    by(auto intro: rtrancl3p.rtrancl3p_step list_all2_appendI)
  with `s1'' \<approx> s2''` show ?case by(blast)
qed

lemma simulation2_rtrancl:
  "\<lbrakk>s2 -2-tls2\<rightarrow>* s2'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
using bisimulation.simulation1_rtrancl[OF bisimulation_flip]
unfolding flip_simps .

lemma simulation1_inf_step:
  assumes red1: "s1 -1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from r1.inf_step_imp_inf_step_table[OF red1]
  obtain stls1 where red1': "s1 -1-stls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd) stls1" by blast
  def tl1_to_tl2_def: tl1_to_tl2 \<equiv> "\<lambda>(s2 :: 's2) (stls1 :: ('s1 \<times> 'tl1 \<times> 's1) llist).
      llist_corec (s2, stls1) (\<lambda>(s2, stls1). case stls1 of LNil \<Rightarrow> None
                               |    LCons (s1, tl1, s1') stls1' \<Rightarrow> 
             let (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
             in Some ((s2, tl2, s2'), (s2', stls1')))"
  hence [simp]: "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 tl1 s1' stls1'. tl1_to_tl2 s2 (LCons (s1, tl1, s1') stls1') =
        LCons (s2, SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2)) stls1')"
    by(simp_all add: llist_corec split_beta)

  have "(llength (tl1_to_tl2 s2 stls1), llength stls1) \<in>
       {(llength (tl1_to_tl2 s2 stls1), llength stls1)|s2 stls1. True}" by blast
  hence [simp]: "llength (tl1_to_tl2 s2 stls1) = llength stls1"
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain s2 stls1 where m: "m = llength (tl1_to_tl2 s2 stls1)"
      and n: "n = llength stls1" by blast
    thus ?case by(cases "stls1") fastsimp+
  qed

  def stls2: stls2 \<equiv> "tl1_to_tl2 s2 stls1"
  with red1' bisim have "\<exists>s1 stls1. s1 -1-stls1\<rightarrow>*t \<infinity> \<and> stls2 = tl1_to_tl2 s2 stls1 \<and> s1 \<approx> s2" by blast
  hence "s2 -2-stls2\<rightarrow>*t \<infinity>"
  proof(coinduct)
    case (inf_step_table s2 stls2)
    then obtain s1 stls1 where red1': "s1 -1-stls1\<rightarrow>*t \<infinity>"
      and stls2: "stls2 = tl1_to_tl2 s2 stls1" and bisim: "s1 \<approx> s2" by blast
    from red1' show ?case
    proof(cases)
      case (inf_step_tableI s1' stls1' tl1)
      hence stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
	and r: "s1 -1-tl1\<rightarrow> s1'" and reds1: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?tl2s2' = "SOME (tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
      let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
      from stls2 stls1 have "stls2 = LCons (s2, ?tl2s2') (tl1_to_tl2 ?s2' stls1')" by simp
      moreover from simulation1[OF bisim r] obtain s2' tl2
	where "s2 -2-tl2\<rightarrow> s2'" "s1' \<approx> s2'" "tl1 \<sim> tl2" by blast
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
      hence "s2 -2-?tl2\<rightarrow> ?s2'" "s1' \<approx> ?s2'" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
      ultimately show ?thesis using reds1 by(fastsimp intro: prod_eqI)
    qed
  qed
  hence "s2 -2-tl1_to_tl2 s2 stls1\<rightarrow>*t \<infinity>" unfolding stls2 .
  hence "s2 -2-lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)\<rightarrow>* \<infinity>"
    by(rule r2.inf_step_table_imp_inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1))"
      using tls1 by simp
  next
    fix n
    assume "Fin n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) n"
      using red1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 stls1 rule: nat_less_induct)
      case (1 n)
      hence IH: "\<And>m s1 s2 stls1. \<lbrakk> m < n; Fin m < llength (lmap (fst \<circ> snd) stls1);
                                   s1 -1-stls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
	         \<Longrightarrow> lnth (lmap (fst \<circ> snd) stls1) m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) m"
	by blast
      from `s1 -1-stls1\<rightarrow>*t \<infinity>` show ?case
      proof cases
	case (inf_step_tableI s1' stls1' tl1)
	hence  stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
	  and r: "s1 -1-tl1\<rightarrow> s1'" and reds: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
	let ?tl2s2' = "SOME (tl2, s2').  s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
	let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
	from simulation1[OF `s1 \<approx> s2` r] obtain s2' tl2
	  where "s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2" by blast
	hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
	hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
	hence bisim': "s1' \<approx> ?s2'" and tlsim: "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
	show ?thesis
	proof(cases n)
	  case 0
	  with stls1 tlsim show ?thesis by simp
	next
	  case (Suc m)
	  hence "m < n" by simp
	  moreover have "Fin m < llength (lmap (fst \<circ> snd) stls1')"
	    using stls1 `Fin n < llength (lmap (fst \<circ> snd) stls1)` Suc by(simp add: Suc_ile_eq)
	  ultimately have "lnth (lmap (fst \<circ> snd) stls1') m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 ?s2' stls1')) m"
	    using reds bisim' by(rule IH)
	  with Suc stls1 show ?thesis by(simp del: o_apply)
	qed
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma simulation2_inf_step:
  "\<lbrakk> s2 -2-tls2\<rightarrow>* \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> \<exists>tls1. s1 -1-tls1\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
using bisimulation.simulation1_inf_step[OF bisimulation_flip]
unfolding flip_simps .

end

locale bisimulation_final_base =
  bisimulation_base + 
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  fixes final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"

locale bisimulation_final = bisimulation_final_base + bisimulation +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"
  assumes bisim_final: "s1 \<approx> s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2"

begin

lemma bisimulation_final_flip:
  "bisimulation_final trsys2 trsys1 (flip bisim) (flip tlsim) final2 final1"
apply(intro_locales)
apply(rule bisimulation_flip)
apply(unfold_locales)
by(unfold flip_simps, rule bisim_final[symmetric])

end

lemma bisimulation_final_flip_simps [flip_simps]:
  "bisimulation_final trsys2 trsys1 (flip bisim) (flip tlsim) final2 final1 =
   bisimulation_final trsys1 trsys2 bisim tlsim final1 final2"
by(auto dest: bisimulation_final.bisimulation_final_flip simp only: flip_flip)

context bisimulation_final begin

lemma final_simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tls1\<rightarrow>* s1'; final1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> final2 s2' \<and> tls1 [\<sim>] tls2"
by(auto dest: bisim_final dest!: simulation1_rtrancl)

lemma final_simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tls2\<rightarrow>* s2'; final2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> final1 s1' \<and> tls1 [\<sim>] tls2"
by(auto dest: bisim_final dest!: simulation2_rtrancl)

end

subsection {* Delay bisimulation *}

locale delay_bisimulation_base =
  bisimulation_base +
  trsys1: \<tau>trsys trsys1 \<tau>move1 +
  trsys2: \<tau>trsys trsys2 \<tau>move2 
  for \<tau>move1 \<tau>move2 +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
begin

notation
  trsys1.silent_move ("_/ -\<tau>1\<rightarrow> _" [50, 50] 60) and
  trsys2.silent_move ("_/ -\<tau>2\<rightarrow> _" [50, 50] 60)

notation
  trsys1.silent_moves ("_/ -\<tau>1\<rightarrow>* _" [50, 50] 60) and
  trsys2.silent_moves ("_/ -\<tau>2\<rightarrow>* _" [50, 50] 60)

notation
  trsys1.silent_movet ("_/ -\<tau>1\<rightarrow>+ _" [50, 50] 60) and
  trsys2.silent_movet ("_/ -\<tau>2\<rightarrow>+ _" [50, 50] 60)

notation
  trsys1.\<tau>rtrancl3p ("_ -\<tau>1-_\<rightarrow>* _" [50, 0, 50] 60) and
  trsys2.\<tau>rtrancl3p ("_ -\<tau>2-_\<rightarrow>* _" [50, 0, 50] 60)

notation
  trsys1.\<tau>inf_step ("_ -\<tau>1-_\<rightarrow>* \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step ("_ -\<tau>2-_\<rightarrow>* \<infinity>" [50, 0] 80)

notation
  trsys1.\<tau>diverge ("_ -\<tau>1\<rightarrow> \<infinity>" [50] 80) and
  trsys2.\<tau>diverge ("_ -\<tau>2\<rightarrow> \<infinity>" [50] 80)

notation
  trsys1.\<tau>inf_step_table ("_ -\<tau>1-_\<rightarrow>*t \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step_table ("_ -\<tau>2-_\<rightarrow>*t \<infinity>" [50, 0] 80)

lemma simulation_silent1I':
  assumes "\<exists>s2'. (if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2' \<and> s1' \<approx> s2'"
  shows "s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
proof -
  from assms obtain s2' where red: "(if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2'" 
    and bisim: "s1' \<approx> s2'" by blast
  show ?thesis
  proof(cases "\<mu>1 s1' s1")
    case True
    with red have "s2 -\<tau>2\<rightarrow>* s2'" by simp
    thus ?thesis using bisim True by cases(blast intro: rtranclp_into_tranclp1)+
  next
    case False
    with red bisim show ?thesis by auto
  qed
qed

lemma simulation_silent2I':
  assumes "\<exists>s1'. (if \<mu>2 s2' s2 then trsys1.silent_moves else trsys1.silent_movet) s1 s1' \<and> s1' \<approx> s2'"
  shows "s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using assms
by(rule delay_bisimulation_base.simulation_silent1I')

end

locale delay_bisimulation_obs = delay_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; \<not> \<tau>move1 s1 tl1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
  and simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; \<not> \<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma delay_bisimulation_obs_flip: "delay_bisimulation_obs trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: simulation1 simulation2)+

end

lemma delay_bisimulation_obs_flip_simps [flip_simps]:
  "delay_bisimulation_obs trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   delay_bisimulation_obs trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: delay_bisimulation_obs.delay_bisimulation_obs_flip simp only: flip_flip)

locale delay_bisimulation_diverge = delay_bisimulation_obs _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation_silent1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
  and simulation_silent2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
  and \<tau>diverge_bisim_inv: "s1 \<approx> s2 \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>"
begin

lemma delay_bisimulation_diverge_flip: "delay_bisimulation_diverge trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
apply(rule delay_bisimulation_diverge.intro)
 apply(rule delay_bisimulation_obs_flip)
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: simulation_silent1 simulation_silent2 \<tau>diverge_bisim_inv[symmetric] del: iffI)+

end


lemma delay_bisimulation_diverge_flip_simps [flip_simps]:
  "delay_bisimulation_diverge trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: delay_bisimulation_diverge.delay_bisimulation_diverge_flip simp only: flip_flip)

context delay_bisimulation_diverge begin

lemma simulation_silents1:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>* s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
using moves bisim
proof induct
  case base thus ?case by(blast)
next
  case (step s1' s1'')
  from `s1 \<approx> s2 \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'` `s1 \<approx> s2`
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
  from simulation_silent1[OF `s1' \<approx> s2'` `s1' -\<tau>1\<rightarrow> s1''`]
  obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" "s1'' \<approx> s2''" by blast
  from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
  with `s1'' \<approx> s2''` show ?case by blast
qed

lemma simulation_silents2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow>* s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
using delay_bisimulation_diverge.simulation_silents1[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma simulation1_\<tau>rtrancl3p:
  "\<lbrakk> s1 -\<tau>1-tls1\<rightarrow>* s1'; s1 \<approx> s2 \<rbrakk>
  \<Longrightarrow> \<exists>tls2 s2'. s2 -\<tau>2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct arbitrary: s2 rule: trsys1.\<tau>rtrancl3p.induct)
  case (\<tau>rtrancl3p_refl s)
  thus ?case by(auto intro: \<tau>trsys.\<tau>rtrancl3p.intros)
next
  case (\<tau>rtrancl3p_step s1 s1' tls1 s1'' tl1)
  from simulation1[OF `s1 \<approx> s2` `s1 -1-tl1\<rightarrow> s1'` `\<not> \<tau>move1 s1 tl1 s1'`]
  obtain s2' s2'' tl2 where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'"
    and red: "s2' -2-tl2\<rightarrow> s2''" and n\<tau>: "\<not> \<tau>move2 s2' tl2 s2''"
    and bisim': "s1' \<approx> s2''" and tlsim: "tl1 \<sim> tl2" by blast
  from bisim' `s1' \<approx> s2'' \<Longrightarrow> \<exists>tls2 s2'. s2'' -\<tau>2-tls2\<rightarrow>* s2' \<and> s1'' \<approx> s2' \<and> tls1 [\<sim>] tls2`
  obtain tls2 s2''' where IH: "s2'' -\<tau>2-tls2\<rightarrow>* s2'''" "s1'' \<approx> s2'''" "tls1 [\<sim>] tls2" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from red n\<tau> IH(1) have "s2' -\<tau>2-tl2 # tls2\<rightarrow>* s2'''" by(rule \<tau>rtrancl3p.\<tau>rtrancl3p_step)
  finally show ?case using IH tlsim by fastsimp
next
  case (\<tau>rtrancl3p_\<tau>step s1 s1' tls1 s1'' tl1)
  from `s1 -1-tl1\<rightarrow> s1'` `\<tau>move1 s1 tl1 s1'` have "s1 -\<tau>1\<rightarrow> s1'" .. 
  from simulation_silent1[OF `s1 \<approx> s2` this]
  obtain s2' where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'" and bisim': "s1' \<approx> s2'" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from bisim' `s1' \<approx> s2' \<Longrightarrow> \<exists>tls2 s2''. s2' -\<tau>2-tls2\<rightarrow>* s2'' \<and> s1'' \<approx> s2'' \<and> tls1 [\<sim>] tls2`
  obtain tls2 s2'' where IH: "s2' -\<tau>2-tls2\<rightarrow>* s2''" "s1'' \<approx> s2''" "tls1 [\<sim>] tls2" by blast
  note `s2' -\<tau>2-tls2\<rightarrow>* s2''`
  finally show ?case using IH by auto
qed

lemma simulation2_\<tau>rtrancl3p:
  "\<lbrakk> s2 -\<tau>2-tls2\<rightarrow>* s2'; s1 \<approx> s2 \<rbrakk>
  \<Longrightarrow> \<exists>tls1 s1'. s1 -\<tau>1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
using delay_bisimulation_diverge.simulation1_\<tau>rtrancl3p[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma simulation1_\<tau>inf_step:
  assumes \<tau>inf1: "s1 -\<tau>1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -\<tau>2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from trsys1.\<tau>inf_step_imp_\<tau>inf_step_table[OF \<tau>inf1]
  obtain sstls1 where \<tau>inf1': "s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd \<circ> snd) sstls1" by blast
  def tl1_to_tl2 \<equiv> "\<lambda>(s2 :: 's2) (sstls1 :: ('s1 \<times> 's1 \<times> 'tl1 \<times> 's1) llist).
      llist_corec (s2, sstls1) (\<lambda>(s2, sstls1). case sstls1 of LNil \<Rightarrow> None
                               | LCons (s1, s1', tl1, s1'') stls1' \<Rightarrow> 
             let (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                                           \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
             in Some ((s2, s2', tl2, s2''), (s2'', stls1')))"
  hence [simp]: "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 s1' tl1 s1'' stls1'. tl1_to_tl2 s2 (LCons (s1, s1', tl1, s1'') stls1') =
        LCons (s2, SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> 
                                          \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (snd (SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                                            \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2)))
                           stls1')"
    by(simp_all add: llist_corec split_beta)

  have "(llength (tl1_to_tl2 s2 sstls1), llength sstls1) \<in>
       {(llength (tl1_to_tl2 s2 sstls1), llength sstls1)|s2 sstls1. True}" by blast
  hence [simp]: "llength (tl1_to_tl2 s2 sstls1) = llength sstls1"
  proof(coinduct rule: inat_equalityI)
    case (Eqinat m n)
    then obtain s2 sstls1 where m: "m = llength (tl1_to_tl2 s2 sstls1)"
      and n: "n = llength sstls1" by blast
    thus ?case by(cases "sstls1") fastsimp+
  qed

  def sstls2: sstls2 \<equiv> "tl1_to_tl2 s2 sstls1"
  with \<tau>inf1' bisim have "\<exists>s1 sstls1. s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity> \<and> sstls2 = tl1_to_tl2 s2 sstls1 \<and> s1 \<approx> s2" by blast
  hence "s2 -\<tau>2-sstls2\<rightarrow>*t \<infinity>"
  proof(coinduct)
    case (\<tau>inf_step_table s2 sstls2)
    then obtain s1 sstls1 where \<tau>inf': "s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>"
      and sstls2: "sstls2 = tl1_to_tl2 s2 sstls1" and bisim: "s1 \<approx> s2" by blast
    from \<tau>inf' show ?case
    proof(cases)
      case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
      hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
	and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''" and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''"
	and reds1: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
      let ?s2tl2s2' = "Eps ?P"
      let ?s2'' = "snd (snd ?s2tl2s2')"
      from sstls2 sstls1 have "sstls2 = LCons (s2, ?s2tl2s2') (tl1_to_tl2 ?s2'' sstls1')" by simp
      moreover from simulation_silents1[OF `s1 \<approx> s2` \<tau>s]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
      from simulation1[OF `s1' \<approx> s2'` r n\<tau>] obtain s2'' s2''' tl2
	where "s2' -\<tau>2\<rightarrow>* s2''" 
	and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
      from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
      with rest have "?P (s2'', tl2, s2''')" by simp
      hence "?P ?s2tl2s2'" by(rule someI)
      ultimately show ?thesis using reds1 by fastsimp
    next
      case \<tau>inf_step_table_Nil
      hence [simp]: "sstls1 = LNil" and "s1 -\<tau>1\<rightarrow> \<infinity>" by simp_all
      from `s1 -\<tau>1\<rightarrow> \<infinity>` `s1 \<approx> s2` have "s2 -\<tau>2\<rightarrow> \<infinity>" by(simp add: \<tau>diverge_bisim_inv)
      thus ?thesis using sstls2 by simp
    qed
  qed
  hence "s2 -\<tau>2-tl1_to_tl2 s2 sstls1\<rightarrow>*t \<infinity>" unfolding sstls2 .
  hence "s2 -\<tau>2-lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)\<rightarrow>* \<infinity>"
    by(rule trsys2.\<tau>inf_step_table_into_\<tau>inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1))"
      using tls1 by simp
  next
    fix n
    assume "Fin n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) n"
      using \<tau>inf1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 sstls1 rule: less_induct)
      case (less n)
      note IH = `\<And>m s1 s2 sstls1. \<lbrakk> m < n; Fin m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1);
                                   s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
	         \<Longrightarrow> lnth (lmap (fst \<circ> snd \<circ> snd) sstls1) m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) m`
      from `s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>` show ?case
      proof cases
	case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
	hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
	  and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''"
	  and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''" and reds: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
	let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
	let ?s2tl2s2' = "Eps ?P" let ?tl2 = "fst (snd ?s2tl2s2')" let ?s2'' = "snd (snd ?s2tl2s2')"
	from simulation_silents1[OF `s1 \<approx> s2` \<tau>s] obtain s2'
	  where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
	from simulation1[OF `s1' \<approx> s2'` r n\<tau>] obtain s2'' s2''' tl2
	  where "s2' -\<tau>2\<rightarrow>* s2''"
	  and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
	from `s2 -\<tau>2\<rightarrow>* s2'` `s2' -\<tau>2\<rightarrow>* s2''` have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
	with rest have "?P (s2'', tl2, s2''')" by auto
	hence "?P ?s2tl2s2'" by(rule someI)
	hence "s1'' \<approx> ?s2''" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
	show ?thesis
	proof(cases n)
	  case 0
	  with sstls1 `tl1 \<sim> ?tl2` show ?thesis by simp
	next
	  case (Suc m)
	  hence "m < n" by simp
	  moreover have "Fin m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1')"
	    using sstls1 `Fin n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)` Suc by(simp add: Suc_ile_eq)
	  ultimately have "lnth (lmap (fst \<circ> snd \<circ> snd) sstls1') m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 ?s2'' sstls1')) m"
	    using reds `s1'' \<approx> ?s2''` by(rule IH)
	  with Suc sstls1 show ?thesis by(simp del: o_apply)
	qed
      next
	case \<tau>inf_step_table_Nil
	with `Fin n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)` have False by simp
	thus ?thesis ..
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma simulation2_\<tau>inf_step:
  "\<lbrakk> s2 -\<tau>2-tls2\<rightarrow>* \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> \<exists>tls1. s1 -\<tau>1-tls1\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
using delay_bisimulation_diverge.simulation1_\<tau>inf_step[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

end

locale delay_bisimulation_final_base =
  delay_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2 +
  bisimulation_final_base _ _ _ _ final1 final2 
  for \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool" +
  assumes final1_simulation: "\<lbrakk> s1 \<approx> s2; final1 s1 \<rbrakk> \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1 \<approx> s2' \<and> final2 s2'"
  and final2_simulation: "\<lbrakk> s1 \<approx> s2; final2 s2 \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2 \<and> final1 s1'"
begin

lemma delay_bisimulation_final_base_flip:
  "delay_bisimulation_final_base trsys2 trsys1 (flip bisim) \<tau>move2 \<tau>move1 final2 final1"
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: final1_simulation final2_simulation)+

end

lemma delay_bisimulation_final_base_flip_simps [flip_simps]:
  "delay_bisimulation_final_base trsys2 trsys1 (flip bisim) \<tau>move2 \<tau>move1 final2 final1 =
  delay_bisimulation_final_base trsys1 trsys2 bisim \<tau>move1 \<tau>move2 final1 final2"
by(auto dest: delay_bisimulation_final_base.delay_bisimulation_final_base_flip simp only: flip_flip)

locale delay_bisimulation_diverge_final = 
  delay_bisimulation_diverge + 
  delay_bisimulation_final_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"
begin

lemma delay_bisimulation_diverge_final_flip:
  "delay_bisimulation_diverge_final trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 final2 final1"
apply(rule delay_bisimulation_diverge_final.intro)
 apply(rule delay_bisimulation_diverge_flip)
apply(unfold_locales, unfold flip_simps)
apply(blast intro: final1_simulation final2_simulation)+
done

end

lemma delay_bisimulation_diverge_final_flip_simps [flip_simps]:
  "delay_bisimulation_diverge_final trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 final2 final1 =
   delay_bisimulation_diverge_final trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 final1 final2"
by(auto dest: delay_bisimulation_diverge_final.delay_bisimulation_diverge_final_flip simp only: flip_flip)

context delay_bisimulation_diverge_final begin

lemma final_simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1-tls1\<rightarrow>* s1'; final1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -\<tau>2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> final2 s2' \<and> tls1 [\<sim>] tls2"
by(blast dest: simulation1_\<tau>rtrancl3p final1_simulation intro: \<tau>rtrancl3p_trans[OF _ silent_moves_into_\<tau>rtrancl3p, simplified])

lemma final_simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2-tls2\<rightarrow>* s2'; final2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -\<tau>1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> final1 s1' \<and> tls1 [\<sim>] tls2"
by(rule delay_bisimulation_diverge_final.final_simulation1[OF delay_bisimulation_diverge_final_flip, unfolded flip_simps])

end

locale delay_bisimulation_measure_base = 
  delay_bisimulation_base +
  constrains trsys1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and trsys2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and bisim :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  and tlsim :: "'tl1 \<Rightarrow> 'tl2 \<Rightarrow> bool"
  and \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  fixes \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"

locale delay_bisimulation_measure =
  delay_bisimulation_measure_base _ _ _ _ \<tau>move1 \<tau>move2 \<mu>1 \<mu>2 +
  delay_bisimulation_obs trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation_silent1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
  and simulation_silent2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
  and wf_\<mu>1: "wfP \<mu>1"
  and wf_\<mu>2: "wfP \<mu>2"
begin

lemma delay_bisimulation_measure_flip:
  "delay_bisimulation_measure trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1"
apply(rule delay_bisimulation_measure.intro)
 apply(rule delay_bisimulation_obs_flip)
apply(unfold_locales)
apply(unfold flip_simps)
apply(rule simulation_silent1 simulation_silent2 wf_\<mu>1 wf_\<mu>2|assumption)+
done

end

lemma delay_bisimulation_measure_flip_simps [flip_simps]:
  "delay_bisimulation_measure trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1 =
   delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"
by(auto dest: delay_bisimulation_measure.delay_bisimulation_measure_flip simp only: flip_simps)

context delay_bisimulation_measure begin

lemma simulation_silentst1:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>+ s1'"
  shows "s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
using moves bisim
proof induct
  case (base s1') thus ?case by(auto dest: simulation_silent1)
next
  case (step s1' s1'')
  hence "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')" by blast
  thus ?case
  proof
    assume "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1"
    hence "s1' \<approx> s2" "\<mu>1\<^sup>+\<^sup>+ s1' s1" by simp_all
    with simulation_silent1[OF `s1' \<approx> s2` `s1' -\<tau>1\<rightarrow> s1''`]
    show ?thesis by(auto)
  next
    assume "\<exists>s2'. trsys2.silent_move\<^sup>+\<^sup>+ s2 s2' \<and> s1' \<approx> s2'"
    then obtain s2' where "s2 -\<tau>2\<rightarrow>+ s2'" "s1' \<approx> s2'" by blast
    with simulation_silent1[OF `s1' \<approx> s2'` `s1' -\<tau>1\<rightarrow> s1''`]
    show ?thesis by(auto intro: tranclp_trans)
  qed
qed

lemma simulation_silentst2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow>+ s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using delay_bisimulation_measure.simulation_silentst1[OF delay_bisimulation_measure_flip]
unfolding flip_simps .

lemma \<tau>diverge_simulation1:
  assumes diverge1: "s1 -\<tau>1\<rightarrow> \<infinity>"
  and bisim: "s1 \<approx> s2"
  shows "s2 -\<tau>2\<rightarrow> \<infinity>"
proof -
  from assms have "s1 -\<tau>1\<rightarrow> \<infinity> \<and> s1 \<approx> s2" by blast
  thus ?thesis using wfP_trancl[OF wf_\<mu>1]
  proof(coinduct rule: trsys2.\<tau>diverge_trancl_measure_coinduct)
    case (\<tau>diverge s2 s1)
    hence "s1 -\<tau>1\<rightarrow> \<infinity>" "s1 \<approx> s2" by simp_all
    then obtain s1' where "trsys1.silent_move s1 s1'" "s1' -\<tau>1\<rightarrow> \<infinity>"
      by(fastsimp elim: trsys1.\<tau>diverge.cases)
    from simulation_silent1[OF `s1 \<approx> s2` `trsys1.silent_move s1 s1'`] `s1' -\<tau>1\<rightarrow> \<infinity>`
    show ?case by auto
  qed
qed

lemma \<tau>diverge_simulation2:
  "\<lbrakk> s2 -\<tau>2\<rightarrow> \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity>"
using delay_bisimulation_measure.\<tau>diverge_simulation1[OF delay_bisimulation_measure_flip]
unfolding flip_simps .

lemma \<tau>diverge_bisim_inv:
  "s1 \<approx> s2 \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>"
by(blast intro: \<tau>diverge_simulation1 \<tau>diverge_simulation2)

end

sublocale delay_bisimulation_measure < delay_bisimulation_diverge
proof
  fix s1 s2 s1'
  assume "s1 \<approx> s2" "s1 -\<tau>1\<rightarrow> s1'"
  from simulation_silent1[OF this]
  show "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'" by(auto intro: tranclp_into_rtranclp)
next
  fix s1 s2 s2'
  assume "s1 \<approx> s2" "s2 -\<tau>2\<rightarrow> s2'"
  from simulation_silent2[OF this]
  show "\<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'" by(auto intro: tranclp_into_rtranclp)
next
  fix s1 s2
  assume "s1 \<approx> s2"
  thus "s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>" by(rule \<tau>diverge_bisim_inv)
qed

text {*
  Counter example for
  @{prop "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<Longrightarrow> \<exists>\<mu>1 \<mu>2. delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"}

 (only @{text "\<tau>"}moves):
\begin{verbatim}
--|
| v
--a  ~  x
  |     |
  |     |
  v     v
--b  ~  y--
| ^     ^ |
--|     |--
\end{verbatim}
*}

locale delay_bisimulation_measure_final =
  delay_bisimulation_measure + 
  delay_bisimulation_final_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"

sublocale delay_bisimulation_measure_final < delay_bisimulation_diverge_final
by unfold_locales

locale \<tau>inv = delay_bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<tau>moves1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>moves2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes \<tau>inv: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; s2 -2-tl2\<rightarrow> s2'; s1' \<approx> s2'; tl1 \<sim> tl2 \<rbrakk>
                 \<Longrightarrow> \<tau>move1 s1 tl1 s1' \<longleftrightarrow> \<tau>move2 s2 tl2 s2'"
begin

lemma \<tau>inv_flip:
  "\<tau>inv trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
by(unfold_locales)(unfold flip_simps,rule \<tau>inv[symmetric])

end

lemma \<tau>inv_flip_simps [flip_simps]:
  "\<tau>inv trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 = \<tau>inv trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: \<tau>inv.\<tau>inv_flip simp only: flip_simps)

locale bisimulation_into_delay =
  bisimulation + \<tau>inv +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
begin

lemma bisimulation_into_delay_flip:
  "bisimulation_into_delay trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
by(intro_locales)(intro bisimulation_flip \<tau>inv_flip)+

end

lemma bisimulation_into_delay_flip_simps [flip_simps]:
  "bisimulation_into_delay trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   bisimulation_into_delay trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: bisimulation_into_delay.bisimulation_into_delay_flip simp only: flip_simps)

context bisimulation_into_delay begin

lemma simulation_silent1_aux:
  assumes bisim: "s1 \<approx> s2" and "s1 -\<tau>1\<rightarrow> s1'"
  shows "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
proof -
  from assms obtain tl1 where tr1: "s1 -1-tl1\<rightarrow> s1'"
    and \<tau>1: "\<tau>move1 s1 tl1 s1'" by(auto)
  from simulation1[OF bisim tr1]
  obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "\<tau>move2 s2 tl2 s2'" by simp
  from tr2 \<tau>2 have "s2 -\<tau>2\<rightarrow>+ s2'" by(auto)
  with bisim' show ?thesis by blast
qed

lemma simulation_silent2_aux:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2\<^sup>+\<^sup>+ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using bisimulation_into_delay.simulation_silent1_aux[OF bisimulation_into_delay_flip]
unfolding flip_simps .

lemma simulation1_aux:
  assumes bisim: "s1 \<approx> s2" and tr1: "s1 -1-tl1\<rightarrow> s1'" and \<tau>1: "\<not> \<tau>move1 s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
proof -
  from simulation1[OF bisim tr1]
  obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "\<not> \<tau>move2 s2 tl2 s2'" by simp
  with bisim' tr2 tlsim show ?thesis by blast
qed

lemma simulation2_aux:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; \<not> \<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
using bisimulation_into_delay.simulation1_aux[OF bisimulation_into_delay_flip]
unfolding flip_simps .

lemma delay_bisimulation_measure:
  assumes wf_\<mu>1: "wfP \<mu>1"
  and wf_\<mu>2: "wfP \<mu>2"
  shows "delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"
apply(unfold_locales)
apply(rule simulation_silent1_aux simulation_silent2_aux simulation1_aux simulation2_aux wf_\<mu>1 wf_\<mu>2|assumption)+
done

lemma delay_bisimulation:
  "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
proof -
  interpret delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 "\<lambda>s s'. False" "\<lambda>s s'. False"
    by(blast intro: delay_bisimulation_measure wfP_empty)
  show ?thesis ..
qed

end

sublocale bisimulation_into_delay < delay_bisimulation_diverge
by(rule delay_bisimulation)

lemma delay_bisimulation_conv_bisimulation:
  "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim (\<lambda>s tl s'. False) (\<lambda>s tl s'. False) =
   bisimulation trsys1 trsys2 bisim tlsim"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then interpret delay_bisimulation_diverge trsys1 trsys2 bisim tlsim "\<lambda>s tl s'. False" "\<lambda>s tl s'. False" .
  show ?rhs by(unfold_locales)(fastsimp simp add: \<tau>moves_False dest: simulation1 simulation2)+
next
  assume ?rhs
  then interpret bisimulation trsys1 trsys2 bisim tlsim .
  interpret bisimulation_into_delay trsys1 trsys2 bisim tlsim "\<lambda>s tl s'. False" "\<lambda>s tl s'. False"
    by(unfold_locales)(rule refl)
  show ?lhs by unfold_locales
qed

sublocale bisimulation_final < delay_bisimulation_final_base
by(unfold_locales)(auto simp add: bisim_final)

subsection {* Transitivity for bisimulations *}

definition bisim_compose :: "('s1, 's2) bisim \<Rightarrow> ('s2, 's3) bisim \<Rightarrow> ('s1, 's3) bisim" (infixr "\<circ>\<^isub>B" 60)
where "(bisim1 \<circ>\<^isub>B bisim2) s1 s3 \<equiv> \<exists>s2. bisim1 s1 s2 \<and> bisim2 s2 s3"

lemma bisim_composeI [intro]:
  "\<lbrakk> bisim12 s1 s2; bisim23 s2 s3 \<rbrakk> \<Longrightarrow> (bisim12 \<circ>\<^isub>B bisim23) s1 s3"
by(auto simp add: bisim_compose_def)

lemma bisim_composeE [elim!]:
  assumes bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
  obtains s2 where "bisim12 s1 s2" "bisim23 s2 s3"
by(atomize_elim)(rule bisim[unfolded bisim_compose_def])

lemma bisim_compose_assoc [simp]:
  "(bisim12 \<circ>\<^isub>B bisim23) \<circ>\<^isub>B bisim34 = bisim12 \<circ>\<^isub>B bisim23 \<circ>\<^isub>B bisim34"
by(auto simp add: fun_eq_iff intro: bisim_composeI)

lemma bisim_compose_conv_rel_comp:
  "split (bisim_compose bisim12 bisim23) = rel_comp (split bisim12) (split bisim23)"
by(auto simp add: rel_comp_def mem_def intro: bisim_composeI)

lemma list_all2_bisim_composeI:
  "\<lbrakk> list_all2 A xs ys; list_all2 B ys zs \<rbrakk>
  \<Longrightarrow> list_all2 (A \<circ>\<^isub>B B) xs zs"
by(rule list_all2_trans)(auto intro: bisim_composeI)+

lemma delay_bisimulation_diverge_compose:
  assumes wbisim12: "delay_bisimulation_diverge trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2"
  and wbisim23: "delay_bisimulation_diverge trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3"
  shows "delay_bisimulation_diverge trsys1 trsys3 (bisim12 \<circ>\<^isub>B bisim23) (tlsim12 \<circ>\<^isub>B tlsim23) \<tau>move1 \<tau>move3"
proof -
  interpret trsys1!: \<tau>trsys trsys1 \<tau>move1 .
  interpret trsys2!: \<tau>trsys trsys2 \<tau>move2 .
  interpret trsys3!: \<tau>trsys trsys3 \<tau>move3 .
  interpret wb12!: delay_bisimulation_diverge trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 by(auto intro: wbisim12)
  interpret wb23!: delay_bisimulation_diverge trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 by(auto intro: wbisim23)
  show ?thesis
  proof
    fix s1 s3 s1'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" and tr1: "trsys1.silent_move s1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation_silent1[OF bisim1 tr1] obtain s2'
      where tr2: "trsys2.silent_moves s2 s2'" and bisim1': "bisim12 s1' s2'" by blast
    from wb23.simulation_silents1[OF bisim2 tr2] obtain s3'
      where "trsys3.silent_moves s3 s3'" "bisim23 s2' s3'" by blast
    with bisim1' show "\<exists>s3'. trsys3.silent_moves s3 s3' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 s3'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" and tr3: "trsys3.silent_move s3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation_silent2[OF bisim2 tr3] obtain s2'
      where tr2: "trsys2.silent_moves s2 s2'" and bisim2': "bisim23 s2' s3'" by blast
    from wb12.simulation_silents2[OF bisim1 tr2] obtain s1'
      where "trsys1.silent_moves s1 s1'" "bisim12 s1' s2'" by blast
    with bisim2' show "\<exists>s1'. trsys1.silent_moves s1 s1' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 tl1 s1'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr1: "trsys1 s1 tl1 s1'" and \<tau>1: "\<not> \<tau>move1 s1 tl1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation1[OF bisim1 tr1 \<tau>1] obtain s2' s2'' tl2
      where tr21: "trsys2.silent_moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim1': "bisim12 s1' s2''" and tlsim1: "tlsim12 tl1 tl2" by blast
    from wb23.simulation_silents1[OF bisim2 tr21] obtain s3'
      where tr31: "trsys3.silent_moves s3 s3'" and bisim2': "bisim23 s2' s3'" by blast
    from wb23.simulation1[OF bisim2' tr22 \<tau>2] obtain s3'' s3''' tl3
      where "trsys3.silent_moves s3' s3''" "trsys3 s3'' tl3 s3'''"
      "\<not> \<tau>move3 s3'' tl3 s3'''" "bisim23 s2'' s3'''" "tlsim23 tl2 tl3" by blast
    with tr31 bisim1' tlsim1 
    show "\<exists>s3' s3'' tl3. trsys3.silent_moves s3 s3' \<and> trsys3 s3' tl3 s3'' \<and> \<not> \<tau>move3 s3' tl3 s3'' \<and>
                         (bisim12 \<circ>\<^isub>B bisim23) s1' s3'' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      by(blast intro: rtranclp_trans bisim_composeI)
  next
    fix s1 s3 tl3 s3'
    assume bisim: "(bisim12 \<circ>\<^isub>B bisim23) s1 s3"
      and tr3: "trsys3 s3 tl3 s3'" and \<tau>3: "\<not> \<tau>move3 s3 tl3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation2[OF bisim2 tr3 \<tau>3] obtain s2' s2'' tl2
      where tr21: "trsys2.silent_moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim2': "bisim23 s2'' s3'" and tlsim2: "tlsim23 tl2 tl3" by blast
    from wb12.simulation_silents2[OF bisim1 tr21] obtain s1'
      where tr11: "trsys1.silent_moves s1 s1'" and bisim1': "bisim12 s1' s2'" by blast
    from wb12.simulation2[OF bisim1' tr22 \<tau>2] obtain s1'' s1''' tl1
      where "trsys1.silent_moves s1' s1''" "trsys1 s1'' tl1 s1'''"
      "\<not> \<tau>move1 s1'' tl1 s1'''" "bisim12 s1''' s2''" "tlsim12 tl1 tl2" by blast
    with tr11 bisim2' tlsim2
    show "\<exists>s1' s1'' tl1. trsys1.silent_moves s1 s1' \<and> trsys1 s1' tl1 s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and>
                         (bisim12 \<circ>\<^isub>B bisim23) s1'' s3' \<and> (tlsim12 \<circ>\<^isub>B tlsim23) tl1 tl3"
      by(blast intro: rtranclp_trans bisim_composeI)
  next
    fix s1 s2
    assume "(bisim12 \<circ>\<^isub>B bisim23) s1 s2"
    thus "\<tau>trsys.\<tau>diverge trsys1 \<tau>move1 s1 = \<tau>trsys.\<tau>diverge trsys3 \<tau>move3 s2"
      by(auto simp add: wb12.\<tau>diverge_bisim_inv wb23.\<tau>diverge_bisim_inv)
  qed
qed

lemma bisimulation_bisim_compose:
  "\<lbrakk> bisimulation trsys1 trsys2 bisim12 tlsim12; bisimulation trsys2 trsys3 bisim23 tlsim23 \<rbrakk>
  \<Longrightarrow> bisimulation trsys1 trsys3 (bisim_compose bisim12 bisim23) (bisim_compose tlsim12 tlsim23)"
unfolding delay_bisimulation_conv_bisimulation[symmetric]
by(rule delay_bisimulation_diverge_compose)

lemma delay_bisimulation_diverge_final_compose:
  fixes \<tau>move1 \<tau>move2
  assumes wbisim12: "delay_bisimulation_diverge_final trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 final1 final2"
  and wbisim23: "delay_bisimulation_diverge_final trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 final2 final3"
  shows "delay_bisimulation_diverge_final trsys1 trsys3 (bisim12 \<circ>\<^isub>B bisim23) (tlsim12 \<circ>\<^isub>B tlsim23) \<tau>move1 \<tau>move3 final1 final3"
proof -
  interpret trsys1!: \<tau>trsys trsys1 \<tau>move1 .
  interpret trsys2!: \<tau>trsys trsys2 \<tau>move2 .
  interpret trsys3!: \<tau>trsys trsys3 \<tau>move3 .
  interpret wb12!: delay_bisimulation_diverge_final trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 final1 final2
    by(auto intro: wbisim12)
  interpret wb23!: delay_bisimulation_diverge_final trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 final2 final3
    by(auto intro: wbisim23)
  interpret delay_bisimulation_diverge trsys1 trsys3 "bisim12 \<circ>\<^isub>B bisim23" "tlsim12 \<circ>\<^isub>B tlsim23" \<tau>move1 \<tau>move3
    by(rule delay_bisimulation_diverge_compose)(unfold_locales)
  show ?thesis
  proof
    fix s1 s3
    assume "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" "final1 s1"
    from `(bisim12 \<circ>\<^isub>B bisim23) s1 s3` obtain s2 where "bisim12 s1 s2" and "bisim23 s2 s3" ..
    from wb12.final1_simulation[OF `bisim12 s1 s2` `final1 s1`]
    obtain s2' where "trsys2.silent_moves s2 s2'" "bisim12 s1 s2'" "final2 s2'" by blast
    from wb23.simulation_silents1[OF `bisim23 s2 s3` `trsys2.silent_moves s2 s2'`]
    obtain s3' where "trsys3.silent_moves s3 s3'" "bisim23 s2' s3'" by blast
    from wb23.final1_simulation[OF `bisim23 s2' s3'` `final2 s2'`]
    obtain s3'' where "trsys3.silent_moves s3' s3''" "bisim23 s2' s3''" "final3 s3''" by blast
    from `trsys3.silent_moves s3 s3'` `trsys3.silent_moves s3' s3''`
    have "trsys3.silent_moves s3 s3''" by(rule rtranclp_trans)
    moreover from `bisim12 s1 s2'` `bisim23 s2' s3''`
    have "(bisim12 \<circ>\<^isub>B bisim23) s1 s3''" ..
    ultimately show "\<exists>s3'. trsys3.silent_moves s3 s3' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1 s3' \<and> final3 s3'"
      using `final3 s3''` by iprover
  next
    fix s1 s3
    assume "(bisim12 \<circ>\<^isub>B bisim23) s1 s3" "final3 s3"
    from `(bisim12 \<circ>\<^isub>B bisim23) s1 s3` obtain s2 where "bisim12 s1 s2" and "bisim23 s2 s3" ..
    from wb23.final2_simulation[OF `bisim23 s2 s3` `final3 s3`]
    obtain s2' where "trsys2.silent_moves s2 s2'" "bisim23 s2' s3" "final2 s2'" by blast
    from wb12.simulation_silents2[OF `bisim12 s1 s2` `trsys2.silent_moves s2 s2'`]
    obtain s1' where "trsys1.silent_moves s1 s1'" "bisim12 s1' s2'" by blast
    from wb12.final2_simulation[OF `bisim12 s1' s2'` `final2 s2'`]
    obtain s1'' where "trsys1.silent_moves s1' s1''" "bisim12 s1'' s2'" "final1 s1''" by blast
    from `trsys1.silent_moves s1 s1'` `trsys1.silent_moves s1' s1''`
    have "trsys1.silent_moves s1 s1''" by(rule rtranclp_trans)
    moreover from `bisim12 s1'' s2'` `bisim23 s2' s3`
    have "(bisim12 \<circ>\<^isub>B bisim23) s1'' s3" ..
    ultimately show "\<exists>s1'. trsys1.silent_moves s1 s1' \<and> (bisim12 \<circ>\<^isub>B bisim23) s1' s3 \<and> final1 s1'"
      using `final1 s1''` by iprover
  qed
qed

end