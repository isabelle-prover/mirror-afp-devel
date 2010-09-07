(*  Title:       Preservation and respectfulness theorems for terminated coinductive lists
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

header {* Quotient preservation and respectfulness theorems for terminated coinductive lists *}

theory Quotient_TLList imports
  TLList
begin

declare [[map tllist = (tmap, tllist_all2)]]

lemma tmap_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  and q4: "Quotient R4 Abs4 Rep4"
  shows "((Abs1 ---> Rep2) ---> (Abs3 ---> Rep4) ---> tmap Rep1 Rep3 ---> tmap Abs2 Abs4) tmap = tmap"
  and "((Abs1 ---> id) ---> (Abs2 ---> id) ---> tmap Rep1 Rep2 ---> id) tmap = tmap"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] Quotient_abs_rep[OF q3] Quotient_abs_rep[OF q4]
by(simp_all add: ext_iff tmap_compose[symmetric] o_def del: tmap_compose)

lemma tmap_respect [quot_respect]:
  "((R1 ===> R2) ===> (R3 ===> R4) ===> tllist_all2 R1 R3 ===> tllist_all2 R2 R4) tmap tmap"
proof -
  {
    fix f f' g g' ts ts'
    assume f: "(R1 ===> R2) f f'"
      and g: "(R3 ===> R4) g g'"
      and ts: "tllist_all2 R1 R3 ts ts'"
    def TS == "tmap f g ts" and TS' == "tmap f' g' ts'"
    with ts have "\<exists>ts ts'. TS = tmap f g ts \<and> TS' = tmap f' g' ts' \<and> tllist_all2 R1 R3 ts ts'" by blast
    hence "tllist_all2 R2 R4 TS TS'"
    proof(coinduct)
      case (tllist_all2 TS TS')
      then obtain ts ts' where [simp]: "TS = tmap f g ts" "TS' = tmap f' g' ts'"
        and ts: "tllist_all2 R1 R3 ts ts'" by blast
      from ts show ?case using f g
        by cases auto
    qed      
    }
  thus ?thesis by simp
qed

lemma Quotient_tmap_Abs_Rep:
  "\<lbrakk>Quotient R1 Abs1 Rep1; Quotient R2 Abs2 Rep2\<rbrakk>
  \<Longrightarrow> tmap Abs1 Abs2 (tmap Rep1 Rep2 ts) = ts"
by(drule abs_o_rep)+(simp add: tmap_compose[symmetric] tmap_id_id del: tmap_compose)

lemma Quotient_tllist_all2_tmap_tmapI:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "tllist_all2 R1 R2 (tmap Rep1 Rep2 ts) (tmap Rep1 Rep2 ts)"
proof -
  def ts' == "tmap Rep1 Rep2 ts"
    and ts'' == "tmap Rep1 Rep2 ts"
  hence "\<exists>ts. ts' = ts'' \<and> ts'' = tmap Rep1 Rep2 ts"
    by(auto simp add: ts'_def)
  thus "tllist_all2 R1 R2 ts' ts''"
  proof coinduct
    case (tllist_all2 ts' ts'')
    then obtain ts where [simp]: "ts' = ts''" "ts'' = tmap Rep1 Rep2 ts" by blast
    show ?case using Quotient_rep_reflp[OF q1] Quotient_rep_reflp[OF q2]
      by(cases ts) auto
  qed
qed

lemma reflp_tllist_all2: 
  assumes R: "reflp R" and Q: "reflp Q"
  shows "reflp (tllist_all2 R Q)"
proof -
  { fix ts :: "('a, 'b) tllist"
    def ts' == ts
    hence "ts = ts'" by simp
    hence "tllist_all2 R Q ts ts'"
    proof(coinduct)
      case (tllist_all2 ts ts')
      thus ?case using R Q
        by(cases ts)(auto simp add: reflp_def)
    qed }
  thus ?thesis by(simp add: reflp_def)
qed

lemma tllist_all2_rel:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "tllist_all2 R1 R2 r s \<longleftrightarrow> (tllist_all2 R1 R2 r r \<and> tllist_all2 R1 R2 s s \<and> tmap Abs1 Abs2 r = tmap Abs1 Abs2 s)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume "?lhs"
  def r' == r
  with `?lhs` have "\<exists>s. tllist_all2 R1 R2 r s \<and> r' = r" by blast
  thus "tllist_all2 R1 R2 r r'"
  proof(coinduct)
    case (tllist_all2 r r')
    then obtain s where s: "tllist_all2 R1 R2 r s"
      and [simp]: "r' = r" by blast
    show ?case using s Quotient_rel[OF q1, THEN iffD1] Quotient_rel[OF q2, THEN iffD1]
      by(cases r)(auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)
  qed

  def s' == s
  with `?lhs` have "\<exists>r. tllist_all2 R1 R2 r s \<and> s' = s" by blast
  thus "tllist_all2 R1 R2 s' s"
  proof(coinduct)
    case (tllist_all2 s s')
    then obtain r where r: "tllist_all2 R1 R2 r s"
      and [simp]: "s' = s" by blast
    show ?case using r Quotient_rel[OF q1, THEN iffD1] Quotient_rel[OF q2, THEN iffD1]
      by(cases s)(auto simp add: tllist_all2_TNil2 tllist_all2_TCons2)
  qed

  def ts == "tmap Abs1 Abs2 r"
    and ts' == "tmap Abs1 Abs2 s"
  hence "(ts, ts') \<in> {(tmap Abs1 Abs2 r, tmap Abs1 Abs2 s)|r s. tllist_all2 R1 R2 r s}"
    using `?lhs` by blast
  thus "ts = ts'"
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain r s where "q = (tmap Abs1 Abs2 r, tmap Abs1 Abs2 s)"
      and "tllist_all2 R1 R2 r s" by blast
    thus ?case using Quotient_rel[OF q1, THEN iffD1] Quotient_rel[OF q2, THEN iffD1]
      by(cases r)(fastsimp simp add: tllist_all2_TNil1 tllist_all2_TCons1)+
  qed
next
  assume "?rhs"
  thus "?lhs"
  proof coinduct
    case (tllist_all2 r s) thus ?case
      by(cases r)(case_tac [!] s, auto simp add: tllist_all2_TCons1 tllist_all2_TNil1 intro: Quotient_rel[OF q1, THEN iffD2] Quotient_rel[OF q2, THEN iffD2])
  qed
qed
    
lemma tllist_quotient [quot_thm]:
  "\<lbrakk> Quotient R1 Abs1 Rep1; Quotient R2 Abs2 Rep2 \<rbrakk> 
  \<Longrightarrow> Quotient (tllist_all2 R1 R2) (tmap Abs1 Abs2) (tmap Rep1 Rep2)"
by(blast intro: QuotientI dest: Quotient_tmap_Abs_Rep Quotient_tllist_all2_tmap_tmapI tllist_all2_rel)

lemma TCons_preserve [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "(Rep1 ---> (tmap Rep1 Rep2) ---> (tmap Abs1 Abs2)) TCons = TCons"
using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2] 
by(simp add: ext_iff tmap_compose[symmetric] o_def tmap_id_id[unfolded id_def] del: tmap_compose)

lemma TCons_respect [quot_respect]:
  "(R ===> tllist_all2 R Q ===> tllist_all2 R Q) TCons TCons"
by simp

lemma TNil_preserve [quot_preserve]:
  assumes "Quotient R2 Abs2 Rep2"
  shows "(Rep2 ---> tmap Abs1 Abs2) TNil = TNil"
using Quotient_abs_rep[OF assms]
by(simp add: ext_iff)

lemma LNil_respect [quot_respect]:
  "(R2 ===> tllist_all2 R1 R2) TNil TNil"
by simp

lemma tllist_all2_eq [id_simps]: "tllist_all2 (op =) (op =) = (op =)"
proof(rule ext)+
  fix xs ys
  show "tllist_all2 (op =) (op =) xs ys \<longleftrightarrow> xs = ys"
    by(descending)(auto simp add: llist_all2_eq)
qed

lemma tllist_all2_rsp: 
  assumes R1: "\<forall>x y. R1 x y \<longrightarrow> (\<forall>a b. R1 a b \<longrightarrow> S x a = T y b)"
  and R2: "\<forall>x y. R2 x y \<longrightarrow> (\<forall>a b. R2 a b \<longrightarrow> S' x a = T' y b)"
  and xsys: "tllist_all2 R1 R2 xs ys"
  and xs'ys': "tllist_all2 R1 R2 xs' ys'"
  shows "tllist_all2 S S' xs xs' = tllist_all2 T T' ys ys'"
proof
  assume "tllist_all2 S S' xs xs'"
  with xsys xs'ys'
  have "\<exists>xs xs'. tllist_all2 S S' xs xs' \<and> tllist_all2 R1 R2 xs ys \<and> tllist_all2 R1 R2 xs' ys'" by blast
  thus "tllist_all2 T T' ys ys'"
  proof coinduct
    case (tllist_all2 ys ys')
    then obtain xs xs' where "tllist_all2 S S' xs xs'" "tllist_all2 R1 R2 xs ys" "tllist_all2 R1 R2 xs' ys'"
      by blast
    thus ?case
      by cases(auto simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
next
  assume "tllist_all2 T T' ys ys'"
  with xsys xs'ys'
  have "\<exists>ys ys'. tllist_all2 T T' ys ys' \<and> tllist_all2 R1 R2 xs ys \<and> tllist_all2 R1 R2 xs' ys'" by blast
  thus "tllist_all2 S S' xs xs'"
  proof coinduct
    case (tllist_all2 xs xs')
    then obtain ys ys' where "tllist_all2 T T' ys ys'" "tllist_all2 R1 R2 xs ys" "tllist_all2 R1 R2 xs' ys'"
      by blast
    thus ?case
      by cases(auto simp add: tllist_all2_TCons1 tllist_all2_TCons2 tllist_all2_TNil1 tllist_all2_TNil2 dest: R1[rule_format] R2[rule_format])
  qed
qed

lemma tllist_all2_respect [quot_respect]:
  "((R1 ===> R1 ===> op =) ===> (R2 ===> R2 ===> op =) ===>
    tllist_all2 R1 R2 ===> tllist_all2 R1 R2 ===> op =) tllist_all2 tllist_all2"
by(simp add: tllist_all2_rsp)

lemma tllist_all2_prs:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "tllist_all2 ((Abs1 ---> Abs1 ---> id) P) ((Abs2 ---> Abs2 ---> id) Q)
                     (tmap Rep1 Rep2 ts) (tmap Rep1 Rep2 ts')
         \<longleftrightarrow> tllist_all2 P Q ts ts'"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof coinduct
    case (tllist_all2 ts ts')
    thus ?case using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2]
      by(cases ts)(case_tac [!] ts', auto simp add: tllist_all2_TNil1 tllist_all2_TCons1)
  qed
next
  assume ?rhs
  moreover 
  def TS == "tmap Rep1 Rep2 ts" and TS' == "tmap Rep1 Rep2 ts'"
  ultimately have "\<exists>ts ts'. TS = tmap Rep1 Rep2 ts \<and> TS' = tmap Rep1 Rep2 ts' \<and> tllist_all2 P Q ts ts'" by blast
  thus ?lhs unfolding TS_def[symmetric] TS'_def[symmetric]
  proof coinduct
    case (tllist_all2 TS TS')
    then obtain ts ts' where "tllist_all2 P Q ts ts'" 
      and "TS = tmap Rep1 Rep2 ts" "TS' = tmap Rep1 Rep2 ts'" by blast
    thus ?case using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2]
      by cases auto
  qed
qed

lemma tllist_all2_preserve [quot_preserve]:
  assumes "Quotient R1 Abs1 Rep1"
  and "Quotient R2 Abs2 Rep2"
  shows "((Abs1 ---> Abs1 ---> id) ---> (Abs2 ---> Abs2 ---> id) ---> 
          tmap Rep1 Rep2 ---> tmap Rep1 Rep2 ---> id) tllist_all2 = tllist_all2"
by(simp add: ext_iff tllist_all2_prs[OF assms])

lemma tllist_all2_preserve2 [quot_preserve]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  shows "(tllist_all2 ((Rep1 ---> Rep1 ---> id) R1) ((Rep2 ---> Rep2 ---> id) R2)) = (op =)"
by(simp add: ext_iff fun_map_def_raw Quotient_rel_rep[OF q1] Quotient_rel_rep[OF q2] tllist_all2_eq)

lemma tllist_corec_preserve [quot_preserve]: 
  assumes q1: "Quotient R1 Abs1 Rep1"
  and q2: "Quotient R2 Abs2 Rep2"
  and q3: "Quotient R3 Abs3 Rep3"
  shows "(Rep1 ---> (Abs1 ---> sum_map (prod_fun Rep2 Rep1) Rep3) ---> tmap Abs2 Abs3) tllist_corec = tllist_corec"
proof(intro ext)
  fix a f
  let ?fmap = "Rep1 ---> (Abs1 ---> sum_map (prod_fun Rep2 Rep1) Rep3) ---> tmap Abs2 Abs3"
  have "(?fmap tllist_corec a f, tllist_corec a f) \<in> {(?fmap tllist_corec a f, tllist_corec a f)|a. True}"
    by blast
  thus "?fmap tllist_corec a f = tllist_corec a f"
  proof(coinduct rule: tllist_equalityI)
    case (Eqtllist q)
    then obtain a where q: "q = (?fmap tllist_corec a f, tllist_corec a f)" by blast
    thus ?case
    proof(cases "f a")
      case (Inl l)
      hence ?EqTCons unfolding q fun_map_def_raw 
        using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q2]
        by(cases l)(subst (1 2) tllist_corec, auto)
      thus ?thesis ..
    next
      case (Inr r)
      hence ?EqTNil unfolding q fun_map_def_raw
        using Quotient_abs_rep[OF q1] Quotient_abs_rep[OF q3]
        by(subst (1 2) tllist_corec)(simp)
      thus ?thesis ..
    qed
  qed
qed

end