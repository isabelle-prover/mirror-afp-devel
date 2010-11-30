(*  Title:      JinjaThreads/Framework/LTS.thy
    Author:     Andreas Lochbihler
*)

header {* \isaheader{Labelled transition systems} *}

theory LTS imports
  "../Common/Aux"
  "../../Coinductive/TLList"
  "Quotient_Option"
begin

lemma option_rel_mono:
  "\<lbrakk> option_rel R x y; \<And>x y. R x y \<Longrightarrow> R' x y \<rbrakk> \<Longrightarrow> option_rel R' x y"
by(cases x)(case_tac [!] y, auto)

lemma nth_concat_conv:
  "n < length (concat xss) 
   \<Longrightarrow> \<exists>m n'. concat xss ! n = (xss ! m) ! n' \<and> n' < length (xss ! m) \<and> 
             m < length xss \<and> n = (\<Sum>i<m. length (xss ! i)) + n'"
using lnth_lconcat_conv[of n "llist_of (map llist_of xss)"]
  setsum_hom[where f = Fin and h = "\<lambda>i. length (xss ! i)"]
by(clarsimp simp add: lconcat_llist_of zero_inat_def[symmetric]) blast


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

types ('a, 'b) trsys = "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"

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

lemma rtrancl3p_into_Rtrancl3p:
  "rtrancl3p trsys a bs a' \<Longrightarrow> Rtrancl3p a (tllist_of_llist a' (llist_of bs))"
by(induct rule: rtrancl3p_converse_induct)(auto intro: Rtrancl3p.intros)

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

coinductive Runs :: "'s \<Rightarrow> ('tl, 's option) tllist \<Rightarrow> bool" ("_ \<Down> _" [50, 50] 51)
where
  Terminate: "\<lbrakk> s -\<tau>\<rightarrow>* s'; \<And>tl s''. \<not> s' -tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> s \<Down> TNil \<lfloor>s'\<rfloor>" 
| Diverge: "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> s \<Down> TNil None"
| Proceed: "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; s'' \<Down> tls \<rbrakk> \<Longrightarrow> s \<Down> TCons tl tls"

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

lemma \<tau>diverge_conv_Runs:
  "s -\<tau>\<rightarrow> \<infinity> \<longleftrightarrow> s \<Down> TNil None"
by(auto intro: Runs.Diverge elim: Runs.cases)

lemma \<tau>inf_step_into_Runs:
  assumes "s -\<tau>-tls\<rightarrow>* \<infinity>"
  shows "s \<Down> tllist_of_llist None tls"
proof -
  def tls' == "tllist_of_llist (None :: 's option) tls"
  with assms have "\<exists>tls. tls' = tllist_of_llist None tls \<and> s -\<tau>-tls\<rightarrow>* \<infinity>" by blast
  thus "s \<Down> tls'"
  proof(coinduct)
    case (Runs s tls')
    then obtain tls where "s -\<tau>-tls\<rightarrow>* \<infinity>"
      and "tls' = tllist_of_llist None tls" by blast
    thus ?case by cases(auto simp add: \<tau>diverge_conv_Runs)
  qed
qed

lemma \<tau>_into_Runs:
  "\<lbrakk> s -\<tau>\<rightarrow> s'; s' \<Down> tls \<rbrakk> \<Longrightarrow> s \<Down> tls"
by(blast elim: Runs.cases intro: Runs.intros \<tau>diverge.intros converse_rtranclp_into_rtranclp)

lemma \<tau>rtrancl3p_into_Runs:
  assumes "s -\<tau>-tls\<rightarrow>* s'"
  and "s' \<Down> tls'"
  shows "s \<Down> lappendt (llist_of tls) tls'"
using assms
by induct(auto intro: Runs.Proceed \<tau>_into_Runs)

coinductive Runs_table :: "'s \<Rightarrow> ('s \<times> 's \<times> 'tl \<times> 's, ('s \<times> 's) option) tllist \<Rightarrow> bool"
where 
  Terminate: "\<lbrakk> s -\<tau>\<rightarrow>* s'; \<And>tl s''. \<not> s' -tl\<rightarrow> s'' \<rbrakk> \<Longrightarrow> Runs_table s (TNil \<lfloor>(s, s')\<rfloor>)"
| Diverge: "s -\<tau>\<rightarrow> \<infinity> \<Longrightarrow> Runs_table s (TNil None)"
| Proceed:
  "\<And>tl. \<lbrakk> s -\<tau>\<rightarrow>* s'; s' -tl\<rightarrow> s''; \<not> \<tau>move s' tl s''; Runs_table s'' tls \<rbrakk> 
  \<Longrightarrow> Runs_table s (TCons (s, s', tl, s'') tls)"

lemma Runs_table_into_Runs:
  assumes "Runs_table s stlsss"
  shows "s \<Down> tmap (fst o snd o snd) (Option.map snd) stlsss"
proof -
  def tls == "tmap (fst o snd o snd) (Option.map snd) stlsss"
  with assms have "\<exists>stlsss. tls = tmap (fst o snd o snd) (Option.map snd) stlsss \<and> Runs_table s stlsss" by blast
  thus "s \<Down> tls"
  proof coinduct
    case (Runs s tls)
    then obtain stlsss where "Runs_table s stlsss" "tls = tmap (fst \<circ> snd \<circ> snd) (Option.map snd) stlsss" by blast
    thus ?case by cases(auto simp add: o_def id_def)
  qed
qed

definition Runs2Runs_table :: "'s \<Rightarrow> ('tl, 's option) tllist \<Rightarrow> ('s \<times> 's \<times> 'tl \<times> 's, ('s \<times> 's) option) tllist"
where
  "Runs2Runs_table s tls = 
  tllist_corec (s, tls)
       (\<lambda>(s, tls). case tls of 
                     TNil b \<Rightarrow> Inr (Option.map (Pair s) b)
                   | TCons tl tls' \<Rightarrow> 
                     let (s', s'') = SOME (s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'
                     in Inl ((s, s', tl, s''), (s'', tls')))"

lemma Runs2Runs_table_simps [simp, nitpick_simp]:
  "Runs2Runs_table s (TNil so) = TNil (Option.map (Pair s) so)"
  "\<And>tl. 
   Runs2Runs_table s (TCons tl tls) =
   (let (s', s'') = SOME (s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls
    in TCons (s, s', tl, s'') (Runs2Runs_table s'' tls))"
unfolding Runs2Runs_table_def Let_def
 apply(simp add: tllist_corec)
apply(subst tllist_corec)
apply(simp add: split_beta)
done

lemma Runs2Runs_table_inverse:
  "tmap (fst \<circ> snd \<circ> snd) (Option.map snd) (Runs2Runs_table s tls) = tls"
proof -
  have "(tmap (fst \<circ> snd \<circ> snd) (Option.map snd) (Runs2Runs_table s tls), tls) \<in>
        {(tmap (fst \<circ> snd \<circ> snd) (Option.map snd) (Runs2Runs_table s tls), tls)|tls s. True}" by blast
  thus ?thesis
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain tls s where q: "q = (tmap (fst \<circ> snd \<circ> snd) (Option.map snd) (Runs2Runs_table s tls), tls)" by blast
    show ?case unfolding q
      by(cases tls)(auto simp add: split_beta option_map_comp snd_o_Pair_conv_id option_map_id)
  qed
qed
 
lemma Runs_into_Runs_table:
  assumes "s \<Down> tls"
  shows "\<exists>stlsss. tls = tmap (fst o snd o snd) (Option.map snd) stlsss \<and> Runs_table s stlsss"
proof(intro exI conjI)
  def stlsss == "Runs2Runs_table s tls"

  show "tls = tmap (fst o snd o snd) (Option.map snd) stlsss"
    unfolding stlsss_def by(simp add: Runs2Runs_table_inverse)

  from assms have "\<exists>tls. stlsss = Runs2Runs_table s tls \<and> s \<Down> tls" unfolding stlsss_def by blast
  thus "Runs_table s stlsss"
  proof coinduct
    case (Runs_table s stlsss)
    then obtain tls where "s \<Down> tls" 
      and stlsss [simp]: "stlsss = Runs2Runs_table s tls" by blast
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
      let ?P = "\<lambda>(s', s''). s -\<tau>\<rightarrow>* s' \<and> s' -tl\<rightarrow> s'' \<and> \<not> \<tau>move s' tl s'' \<and> s'' \<Down> tls'"
      from Proceed have "?P (s', s'')" by simp
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Proceed using `tls = TCons tl tls'`
        by(auto simp add: split_beta)
      thus ?thesis by simp
    qed
  qed
qed

lemma Runs_lappendtE:
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

lemma Runs_total:
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
  proof(coinduct rule: Runs.coinduct)
    case (Runs \<sigma> tls)[simp]
    show ?case
    proof(cases "\<exists>\<sigma>'. ?\<tau>halt \<sigma> \<sigma>'")
      case True
      hence "?\<tau>halt \<sigma> (SOME \<sigma>'. ?\<tau>halt \<sigma> \<sigma>')" by(rule someI_ex)
      hence ?Terminate using True unfolding Runs
        by(subst tllist_corec)(simp add: step_def)
      thus ?thesis by simp
    next
      case False
      note \<tau>halt = this
      show ?thesis
      proof(cases "?\<tau>diverge \<sigma>")
        case True
        hence ?Diverge using True False unfolding Runs
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
        hence ?Proceed using False \<tau>halt unfolding Runs
          by(subst tllist_corec)(fastsimp simp add: step_def)
        thus ?thesis by simp
      qed
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

end