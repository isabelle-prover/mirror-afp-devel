(*     License:    LGPL  *)

subsection \<open>Optimality of the DCR3 method for proving confluence of relations of the least uncountable cardinality\<close>

theory DCR3_Optimality
  imports 
    "HOL-Cardinals.Cardinals"
    Finite_DCR_Hierarchy
begin

(* ----------------------------------------------------------------------- *)

subsubsection \<open>Auxiliary definitions\<close>

(* ----------------------------------------------------------------------- *)

datatype Lev = \<l>0 | \<l>1 | \<l>2 | \<l>3 | \<l>4 | \<l>5 | \<l>6 | \<l>7 | \<l>8

type_synonym 'U rD = "Lev \<times> 'U set \<times> 'U set \<times> 'U set"

fun rP :: "Lev \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> Lev \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> bool"
where
  "rP \<l>0 A B C n' A' B' C' = (A = {} \<and> B = {} \<and> C = {} \<and> n' = \<l>1 \<and> finite A' \<and> B' = {} \<and> C' = {})"
| "rP \<l>1 A B C n' A' B' C' = (finite A \<and> B = {} \<and> C = {} \<and> n' = \<l>2 \<and> A' = A \<and> B' = {} \<and> C' = {})"
| "rP \<l>2 A B C n' A' B' C' = (finite A \<and> B = {} \<and> C = {} \<and> n' = \<l>3 \<and> A' = A \<and> finite B' \<and> C' = {})"
| "rP \<l>3 A B C n' A' B' C' = (finite A \<and> finite B \<and> C = {} \<and> n' = \<l>4 \<and> A' = A \<and> B' = B \<and> C' = {})"
| "rP \<l>4 A B C n' A' B' C' = (finite A \<and> finite B \<and> C = {} \<and> n' = \<l>5 \<and> A' = A \<and> B' = B \<and> finite C')"
| "rP \<l>5 A B C n' A' B' C' = (finite A \<and> finite B \<and> finite C \<and> n' = \<l>6 \<and> A' = A \<and> B' = B \<and> C' = C)"
| "rP \<l>6 A B C n' A' B' C' = (finite A \<and> finite B \<and> finite C \<and> n' = \<l>7 \<and> A' = A \<union> B \<union> C \<and> B' = A' \<and> C' = A')"
| "rP \<l>7 A B C n' A' B' C' = (finite A \<and> B = A \<and> C = A \<and> n' = \<l>8 \<and> A' = A \<and> B' = A' \<and> C' = A')"
| "rP \<l>8 A B C n' A' B' C' = (finite A \<and> B = A \<and> C = A \<and> n' = \<l>7 \<and> A \<subset> A' \<and> finite A' \<and> B' = A' \<and> C' = A')"

definition rC :: "'U set \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> 'U set \<Rightarrow> bool"
where
  "rC S A B C = (A \<subseteq> S \<and> B \<subseteq> S \<and> C \<subseteq> S)"

definition rE :: "'U set \<Rightarrow> ('U rD) rel"
where
  "rE S = { ((n1, A1, B1, C1), (n2, A2, B2, C2)). rP n1 A1 B1 C1 n2 A2 B2 C2 \<and> rC S A1 B1 C1 \<and> rC S A2 B2 C2 }"

fun lev_next :: "Lev \<Rightarrow> Lev"
where
  "lev_next \<l>0 = \<l>1" 
| "lev_next \<l>1 = \<l>2"
| "lev_next \<l>2 = \<l>3"
| "lev_next \<l>3 = \<l>4"
| "lev_next \<l>4 = \<l>5"
| "lev_next \<l>5 = \<l>6"
| "lev_next \<l>6 = \<l>7"
| "lev_next \<l>7 = \<l>8"
| "lev_next \<l>8 = \<l>7"

fun levrd :: "'U rD \<Rightarrow> Lev"
where
  "levrd (n, A, B, C) = n"

fun wrd :: "'U rD \<Rightarrow> 'U set"
where
  "wrd (n, A, B, C) = A \<union> B \<union> C"

definition Wrd :: "'U rD set \<Rightarrow> 'U set"
where
  "Wrd S = (\<Union> (wrd ` S))"

definition bkset :: "'a rel \<Rightarrow> 'a set \<Rightarrow> 'a set" 
where 
  "bkset r A = ((r^*)^-1)``A"

(* ----------------------------------------------------------------------- *)

subsubsection \<open>Auxiliary lemmas\<close>

(* ----------------------------------------------------------------------- *)

lemma lem_rtr_field: "(x,y) \<in> r^* \<Longrightarrow> (x = y) \<or> (x \<in> Field r \<and> y \<in> Field r)"
  by (metis Field_def Not_Domain_rtrancl Range.RangeI UnCI rtranclE)

lemma lem_fin_fl_rel: "finite (Field r) = finite r"
  using finite_Field finite_subset trancl_subset_Field2 by fastforce

lemma lem_rel_inf_fld_card:
fixes r::"'U rel"
assumes "\<not> finite r"
shows "|Field r| =o |r|"
proof -
  obtain f1::"'U \<times> 'U \<Rightarrow> 'U" where b1: "f1 = (\<lambda> (x,y). x)" by blast
  obtain f2::"'U \<times> 'U \<Rightarrow> 'U" where b2: "f2 = (\<lambda> (x,y). y)" by blast
  then have "f1 ` r = Domain r \<and> f2 ` r = Range r" using b1 b2 by force
  then have b3: "|Domain r| \<le>o |r| \<and> |Range r| \<le>o |r|" 
    using card_of_image[of f1 r] card_of_image[of f2 r] by simp
  have "|Domain r| \<le>o |Range r| \<or> |Range r| \<le>o |Domain r|" by (simp add: ordLeq_total)
  moreover have "|Domain r| \<le>o |Range r| \<longrightarrow> |Field r| \<le>o |r|"
  proof
    assume c1: "|Domain r| \<le>o |Range r|"
    moreover have "finite (Domain r) \<and> finite (Range r) \<longrightarrow> finite (Field r)" unfolding Field_def by blast
    ultimately have "\<not> finite (Range r)" 
      using assms lem_fin_fl_rel card_of_ordLeq_finite by blast
    then have "|Field r| =o |Range r|" using c1 card_of_Un_infinite unfolding Field_def by blast
    then show "|Field r| \<le>o |r|" using b3 ordIso_ordLeq_trans by blast
  qed
  moreover have "|Range r| \<le>o |Domain r| \<longrightarrow> |Field r| \<le>o |r|"
  proof
    assume c1: "|Range r| \<le>o |Domain r|"
    moreover have "finite (Domain r) \<and> finite (Range r) \<longrightarrow> finite (Field r)" unfolding Field_def by blast
    ultimately have "\<not> finite (Domain r)" 
      using assms lem_fin_fl_rel card_of_ordLeq_finite by blast
    then have "|Field r| =o |Domain r|" using c1 card_of_Un_infinite unfolding Field_def by blast
    then show "|Field r| \<le>o |r|" using b3 ordIso_ordLeq_trans by blast
  qed
  ultimately have "|Field r| \<le>o |r|" by blast
  moreover have "|r| \<le>o |Field r|"
  proof -
    have "r \<subseteq> (Field r) \<times> (Field r)" unfolding Field_def by force
    then have c1: "|r| \<le>o |Field r \<times> Field r|" by simp
    have "\<not> finite (Field r)" using assms lem_fin_fl_rel by blast
    then have c2: "|Field r \<times> Field r| =o |Field r|" by simp
    show ?thesis using c1 c2 using ordLeq_ordIso_trans by blast
  qed
  ultimately show ?thesis using ordIso_iff_ordLeq by blast
qed

lemma lem_confl_field: "confl_rel r = (\<forall> a \<in> Field r. \<forall> b \<in> Field r. \<forall> c \<in> Field r. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> 
                  (\<exists> d \<in> Field r. (b,d) \<in> r^* \<and> (c,d) \<in> r^*))"
proof
  assume b1: "confl_rel r"
  show "\<forall> a \<in> Field r. \<forall> b \<in> Field r. \<forall> c \<in> Field r. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> 
                  (\<exists> d \<in> Field r. (b,d) \<in> r^* \<and> (c,d) \<in> r^*)"
  proof (intro ballI impI)
    fix a b c
    assume c1: "a \<in> Field r" and c2: "b \<in> Field r" and c3: "c \<in> Field r" and c4: "(a,b) \<in> r^* \<and> (a,c) \<in> r^*"
    obtain d where "(b,d) \<in> r^* \<and> (c,d) \<in> r^*" using b1 c4 unfolding confl_rel_def by blast
    moreover then have "d \<in> Field r" using c2 using lem_rtr_field by fastforce
    ultimately show "\<exists> d \<in> Field r. (b,d) \<in> r^* \<and> (c,d) \<in> r^*" by blast
  qed
next
  assume b1: "\<forall> a \<in> Field r. \<forall> b \<in> Field r. \<forall> c \<in> Field r. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> 
                  (\<exists> d \<in> Field r. (b,d) \<in> r^* \<and> (c,d) \<in> r^*)"
  have "\<forall>a b c. (a, b) \<in> r^* \<and> (a, c) \<in> r^* \<longrightarrow> (\<exists>d. (b, d) \<in> r^* \<and> (c, d) \<in> r^*)"
  proof (intro allI impI)
    fix a b c
    assume "(a, b) \<in> r^* \<and> (a, c) \<in> r^*"
    moreover then have "a \<notin> Field r \<or> b \<notin> Field r \<or> c \<notin> Field r \<longrightarrow> a = b \<or> a = c" by (meson lem_rtr_field)
    ultimately show "\<exists>d. (b, d) \<in> r^* \<and> (c, d) \<in> r^*" using b1 by blast
  qed
  then show "confl_rel r" unfolding confl_rel_def by blast
qed

lemma lem_d2_to_dc2:
fixes r::"'U rel"
assumes "DCR2 r"
shows "DCR 2 r"
proof -
  obtain r0 r1 where b1: "r = r0 \<union> r1"
       and b2: "\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0 \<longrightarrow> jn00 r0 b c"
       and b3: "\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r1 \<longrightarrow> jn01 r0 r1 b c"
       and b4: "\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r1 \<longrightarrow> jn11 r0 r1 b c" 
     using assms unfolding DCR2_def LD2_def by blast
  obtain g::"nat \<Rightarrow> 'U rel" 
    where b5: "g = (\<lambda> \<alpha>::nat. if \<alpha> = 0 then r0 else (if \<alpha> = 1 then r1 else {}))" by blast
  have b6: "g 0 = r0 \<and> g 1 = r1" using b5 by simp
  have b7: "\<forall> n. (\<not> (n = 0 \<or> n = 1)) \<longrightarrow> g n = {}" using b5 by simp
  have "\<forall>\<alpha> \<beta> a b c. (a, b) \<in> g \<alpha> \<and> (a, c) \<in> g \<beta> \<longrightarrow>
       (\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>)"
  proof (intro allI impI)
    fix \<alpha> \<beta> a b c
    assume c1: "(a, b) \<in> g \<alpha> \<and> (a, c) \<in> g \<beta>"
    then have c2: "(\<alpha> = 0 \<or> \<alpha> = 1) \<and> (\<beta> = 0 \<or> \<beta> = 1)" using b7 by blast
    show "\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>"
    proof -
      have "\<alpha> = 0 \<and> \<beta> = 0 \<longrightarrow> ?thesis"
      proof
        assume e1: "\<alpha> = 0 \<and> \<beta> = 0"
        then have "jn00 r0 b c" using c1 b2 b6 by blast
        then obtain d where "(b, d) \<in> r0^= \<and> (c, d) \<in> r0^=" unfolding jn00_def by blast
        then have "(b, b, d, d) \<in> \<DD> g 0 0 \<and> (c, c, d, d) \<in> \<DD> g 0 0" using b6 unfolding \<DD>_def by blast
        then show "\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>" using e1 by blast
      qed
      moreover have "\<alpha> = 0 \<and> \<beta> = 1 \<longrightarrow> ?thesis"
      proof
        assume e1: "\<alpha> = 0 \<and> \<beta> = 1"
        then have "jn01 r0 r1 b c" using c1 b3 b6 by blast
        then obtain b'' d where "(b,b'') \<in> r1^= \<and> (b'',d) \<in> r0^* \<and> (c,d) \<in> r0^*" unfolding jn01_def by blast
        moreover have "\<LL>v g 0 1 = g 0 \<and> \<LL>v g 1 0 = g 0" using b6 b7 unfolding \<LL>v_def by blast
        ultimately have "(b, b, b'', d) \<in> \<DD> g 0 1 \<and> (c, c, c, d) \<in> \<DD> g 1 0" using b6 unfolding \<DD>_def by simp
        then show "\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>" using e1 by blast
      qed
      moreover have "\<alpha> = 1 \<and> \<beta> = 0 \<longrightarrow> ?thesis"
      proof
        assume e1: "\<alpha> = 1 \<and> \<beta> = 0"
        then have "jn01 r0 r1 c b" using c1 b3 b6 by blast
        then obtain c'' d where "(c,c'') \<in> r1^= \<and> (c'',d) \<in> r0^* \<and> (b,d) \<in> r0^*" unfolding jn01_def by blast
        moreover have "\<LL>v g 0 1 = g 0 \<and> \<LL>v g 1 0 = g 0" using b6 b7 unfolding \<LL>v_def by blast
        ultimately have "(b, b, b, d) \<in> \<DD> g 1 0 \<and> (c, c, c'', d) \<in> \<DD> g 0 1" using b6 unfolding \<DD>_def by simp
        then show "\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>" using e1 by blast
      qed
      moreover have "\<alpha> = 1 \<and> \<beta> = 1 \<longrightarrow> ?thesis"
      proof
        assume e1: "\<alpha> = 1 \<and> \<beta> = 1"
        then have "jn11 r0 r1 b c" using c1 b4 b6 by blast
        then obtain b' b'' c' c'' d where 
              e2: "(b,b') \<in> r0^* \<and> (b',b'') \<in> r1^= \<and> (b'',d) \<in> r0^*"
          and e3: "(c,c') \<in> r0^* \<and> (c',c'') \<in> r1^= \<and> (c'',d) \<in> r0^*" unfolding jn11_def by blast
        moreover have "\<LL>v g 1 1 = g 0 \<and> \<LL>1 g 1 = g 0" using b6 b7 unfolding \<LL>1_def \<LL>v_def by blast
        ultimately have "(b, b', b'', d) \<in> \<DD> g 1 1 \<and> (c, c', c'', d) \<in> \<DD> g 1 1" using b6 unfolding \<DD>_def by simp
        then show "\<exists>b' b'' c' c'' d. (b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>" using e1 by blast
      qed
      ultimately show ?thesis using c2 by blast
    qed
  qed
  then have "DCR_generating g" unfolding DCR_generating_def by blast
  moreover have "r = \<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'}"
  proof
    show "r \<subseteq> \<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'}"
    proof
      fix p
      assume "p \<in> r"
      then have "p \<in> r0 \<or> p \<in> r1" using b1 by blast
      moreover have "(0::nat) < (2::nat) \<and> (1::nat) < (2::nat)" by simp
      ultimately show "p \<in> \<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'}" using b6 by blast
    qed
  next
    show "\<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'} \<subseteq> r"
    proof
      fix p
      assume "p \<in> \<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'}"
      then obtain \<alpha>' where "\<alpha>'<2 \<and> p \<in> g \<alpha>'" by blast
      moreover then have "\<alpha>' = 0 \<or> \<alpha>' = 1" by force
      ultimately show "p \<in> r" using b1 b6 by blast
    qed
  qed
  ultimately show ?thesis unfolding DCR_def by blast
qed

lemma lem_dc2_to_d2:
fixes r::"'U rel"
assumes "DCR 2 r"
shows "DCR2 r"
proof -
  obtain g where b1: "DCR_generating g" and b2: "r = \<Union>{r'. \<exists>\<alpha>'<2. r' = g \<alpha>'}" 
      using assms unfolding DCR_def by blast
  have "\<forall> \<alpha>::nat. \<alpha><2 \<longleftrightarrow> \<alpha> = 0 \<or> \<alpha> = 1" by force
  then have b3: "\<LL>1 g 0 = {} \<and> \<LL>1 g 1 = g 0 \<and> \<LL>1 g 2 = g 0 \<union> g 1
      \<and> \<LL>v g 0 0 = {} \<and> \<LL>v g 1 0 = g 0 \<and> \<LL>v g 0 1 = g 0 \<and> \<LL>v g 1 1 = g 0"
    unfolding \<LL>1_def \<LL>v_def by (simp_all, blast+)
  have "r = (g 0) \<union> (g 1)"
  proof
    show "r \<subseteq> (g 0) \<union> (g 1)"
    proof
      fix p
      assume "p \<in> r"
      then obtain \<alpha> where "p \<in> g \<alpha> \<and> \<alpha> < 2" using b2 by blast
      moreover have "\<forall> \<alpha>::nat. \<alpha><2 \<longleftrightarrow> \<alpha> = 0 \<or> \<alpha> = 1" by force
      ultimately show "p \<in> (g 0) \<union> (g 1)" by force
    qed
  next
    have "(0::nat) < (2::nat) \<and> (1::nat) < (2::nat)" by simp
    then show "(g 0) \<union> (g 1) \<subseteq> r" using b2 by blast
  qed
  moreover have "\<forall> a b c. (a,b) \<in> (g 0) \<and> (a,c) \<in> (g 0) \<longrightarrow> jn00 (g 0) b c"
  proof (intro allI impI)
    fix a b c
    assume "(a,b) \<in> (g 0) \<and> (a,c) \<in> (g 0)"
    then obtain b' b'' c' c'' d where "(b, b', b'', d) \<in> \<DD> g 0 0 \<and> (c, c', c'', d) \<in> \<DD> g 0 0" 
      using b1 unfolding DCR_generating_def by blast
    then show "jn00 (g 0) b c" unfolding jn00_def \<DD>_def \<LL>1_def \<LL>v_def by force
  qed
  moreover have "\<forall> a b c. (a,b) \<in> (g 0) \<and> (a,c) \<in> (g 1) \<longrightarrow> jn01 (g 0) (g 1) b c"
  proof (intro allI impI)
    fix a b c
    assume "(a,b) \<in> (g 0) \<and> (a,c) \<in> (g 1)"
    then obtain b' b'' c' c'' d where 
      "(b, b', b'', d) \<in> \<DD> g 0 1 \<and> (c, c', c'', d) \<in> \<DD> g 1 0" 
        using b1 unfolding DCR_generating_def by blast
    then show "jn01 (g 0) (g 1) b c" unfolding jn01_def \<DD>_def \<LL>1_def \<LL>v_def by force
  qed
  moreover have "\<forall> a b c. (a,b) \<in> (g 1) \<and> (a,c) \<in> (g 1) \<longrightarrow> jn11 (g 0) (g 1) b c"
  proof (intro allI impI)
    fix a b c
    assume "(a,b) \<in> (g 1) \<and> (a,c) \<in> (g 1)"
    then obtain b' b'' c' c'' d where "(b, b', b'', d) \<in> \<DD> g 1 1 \<and> (c, c', c'', d) \<in> \<DD> g 1 1" 
        using b1 unfolding DCR_generating_def by blast
    then show "jn11 (g 0) (g 1) b c" 
        unfolding jn11_def \<DD>_def apply (simp only: b3) 
        by blast
  qed
  ultimately have "LD2 r (g 0) (g 1)" unfolding LD2_def by blast
  then show ?thesis unfolding DCR2_def by blast
qed

lemma lem_rP_inv: "rP n A B C n' A' B' C' \<Longrightarrow> ( A \<subseteq> A' \<and> B \<subseteq> B' \<and> C \<subseteq> C' 
        \<and> finite A \<and> finite B \<and> finite C \<and> finite A' \<and> finite B' \<and> finite C' )"
  by (cases n, cases n', force+)

lemma lem_infset_finext:
fixes S::"'U set" and A::"'U set"
assumes "\<not> finite S" and "finite A" and "A \<subseteq> S"
shows "\<exists> B. B \<subseteq> S \<and> A \<subset> B \<and> finite B"
proof -
  have b1: "finite A" using assms lem_rP_inv by blast
  then have "A \<noteq> S" using assms by blast
  then obtain A2 x where "x \<in> S \<and> A2 = A \<union> {x} \<and> x \<notin> A \<and> A2 \<subseteq> S" using assms by force
  moreover then have "finite A2" using b1 by blast
  ultimately show ?thesis by blast
qed

lemma lem_rE_df:
fixes S::"'U set"
shows  "(u,v) \<in> rE S \<Longrightarrow> (u,w) \<in> rE S \<Longrightarrow> (v,t) \<in> (rE S)^= \<Longrightarrow> (w,t) \<in> (rE S)^= \<Longrightarrow> v = w"
proof -
  assume "(u,v) \<in> rE S" and "(u,w) \<in> rE S" and "(v,t) \<in> (rE S)^=" and "(w,t) \<in> (rE S)^="
  moreover have "\<And> u v w t. (u,v) \<in> rE S \<Longrightarrow> (u, w) \<in> rE S \<Longrightarrow> (v, t) \<in> rE S \<or> v = t \<Longrightarrow> (w, t) \<in> rE S \<Longrightarrow> v = w"
  proof -
    fix u v w t
    assume "(u,v) \<in> (rE S)" and "(u, w) \<in> (rE S)" and "(v, t) \<in> (rE S) \<or> v = t" and "(w, t) \<in> (rE S)"
    moreover obtain n::Lev and a b c where "u = (n,a,b,c)" using prod_cases4 by blast
    moreover obtain n'::Lev and a' b' c' where "v = (n',a',b',c')" using prod_cases4 by blast
    moreover obtain n''::Lev and a'' b'' c'' where "w = (n'',a'',b'',c'')" using prod_cases4 by blast
    moreover obtain n'''::Lev and a''' b''' c''' where "t = (n''',a''',b''',c''')" using prod_cases4 by blast
    ultimately show "v = w" 
      apply (simp add: rE_def) 
      apply (cases n)
      apply (cases n')
      apply (cases n'')
      apply (cases n''')
      by simp+
  qed
  ultimately show ?thesis by blast
qed

lemma lem_rE_succ_lev:
fixes S::"'U set"
assumes "(u,v) \<in> rE S" 
shows "levrd v = (lev_next (levrd u))"
proof -
  obtain n A B C where b1: "u = (n,A,B,C)" using prod_cases4 by blast
  moreover obtain n' A' B' C' where b2: "v = (n',A',B',C')" using prod_cases4 by blast
  ultimately have "rP n A B C n' A' B' C'" using assms unfolding rE_def by blast
  then have "n' = (lev_next n)" by (cases n, auto+)
  then show ?thesis using b1 b2 by simp
qed

lemma lem_rE_levset_inv:
fixes S::"'U set" and L u v
assumes a1: "(u,v) \<in> (rE S)^*" and a2: "levrd u \<in> L" and a3: "lev_next ` L \<subseteq> L"
shows "levrd v \<in> L"
proof -
  have "\<And> k. \<forall> u v::'U rD. (u,v) \<in> (rE S)^^k \<and> levrd u \<in> L \<longrightarrow> levrd v \<in> L"
  proof -
    fix k
    show "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^k \<and> levrd u \<in> L \<longrightarrow> levrd v \<in> L"
    proof (induct k)
      show "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^0 \<and> levrd u \<in> L \<longrightarrow> levrd v \<in> L" by simp
    next
      fix k
      assume d1: "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^k \<and> levrd u \<in> L \<longrightarrow> levrd v \<in> L"
      show "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^(Suc k) \<and> levrd u \<in> L \<longrightarrow> levrd v \<in> L"
      proof (intro allI impI)
        fix u v::"'U rD"
        assume "(u,v) \<in> (rE S)^^(Suc k) \<and> levrd u \<in> L"
        moreover then obtain v' where e1: "(u,v') \<in> (rE S)^^k \<and> (v',v) \<in> (rE S)" by force
        ultimately have "levrd v' \<in> L" using d1 by blast
        then have "levrd v \<in> lev_next ` L" using e1 lem_rE_succ_lev[of v' v] by force
        then show "levrd v \<in> L" using a3 by force
      qed
    qed
  qed
  then show ?thesis using a1 a2 rtrancl_imp_relpow by blast
qed

lemma lem_rE_levun: 
fixes S::"'U set"
shows "u \<in> Domain (rE S) \<Longrightarrow> levrd u \<in> {\<l>1, \<l>3, \<l>5} \<Longrightarrow> \<exists> v. (rE S)``{u} \<subseteq> {v}"
proof -
  assume a1: "u \<in> Domain (rE S)" and a2: "levrd u \<in> {\<l>1, \<l>3, \<l>5}"
  then obtain v where b1: "(u,v) \<in> (rE S)" by blast
  obtain n a b c where b2: "u = (n,a,b,c)" using prod_cases4 by blast
  obtain n' a' b' c' where b3: "v = (n',a',b',c')" using prod_cases4 by blast
  have b4: "rP n a b c n' a' b' c'" using b1 b2 b3 unfolding rE_def by blast
  have "n = \<l>1 \<or> n = \<l>3 \<or> n = \<l>5" using b2 a2 by simp
  moreover have "n = \<l>1 \<longrightarrow> (rE S) `` {u} \<subseteq> {v}" using b2 b3 b4 unfolding rE_def by force
  moreover have "n = \<l>3 \<longrightarrow> (rE S) `` {u} \<subseteq> {v}" using b2 b3 b4 unfolding rE_def by force
  moreover have "n = \<l>5 \<longrightarrow> (rE S) `` {u} \<subseteq> {v}" using b2 b3 b4 unfolding rE_def by force
  ultimately show "\<exists> v. (rE S)``{u} \<subseteq> {v}" by blast
qed

lemma lem_rE_domfield:
fixes S::"'U set"
assumes "\<not> finite S"
shows "Domain (rE S) = Field (rE S)"
proof -
  have "\<And> u2 u1::'U rD. (u2,u1) \<in> rE S \<Longrightarrow> \<exists> u3. (u1,u3) \<in> rE S"
  proof -
    fix u2 u1::"'U rD"
    assume c1: "(u2,u1) \<in> rE S"
    obtain n1 A1 B1 C1 where c2: "u1 = (n1,A1,B1,C1)" using prod_cases4 by blast
    obtain n2 A2 B2 C2 where c3: "u2 = (n2,A2,B2,C2)" using prod_cases4 by blast
    have c4: "rP n2 A2 B2 C2 n1 A1 B1 C1 \<and> rC S A2 B2 C2 \<and> rC S A1 B1 C1" using c1 c2 c3 unfolding rE_def by blast
    then have "finite (A1 \<union> A2)" using lem_rP_inv by blast
    moreover have "A1 \<union> A2 \<subseteq> S" using c4 unfolding rC_def by blast
    ultimately obtain A3 where c5: "A3 \<subseteq> S \<and> A1 \<subset> A3 \<and> A2 \<subset> A3 \<and> finite A3" 
      using assms lem_infset_finext[of S "A1 \<union> A2"] by blast
    have "\<exists> n3 A3 B3 C3. (rP n1 A1 B1 C1 n3 A3 B3 C3 \<and> rC S A3 B3 C3)" 
    using c4 unfolding rC_def
      apply (cases n1)
      apply (cases n2, simp+)
      apply (cases n2, simp+)
      apply (cases n2, simp+)
      apply (force, simp+)
      apply (cases n2, simp+)
      apply (cases n2, simp+)
      apply (force, simp+)
      apply (cases n2, simp+)
      apply (cases n2, simp+)
      apply (cases n2, simp+)
      using c5 apply (cases n2)
      apply simp+
      apply blast
      apply simp
      done
    then obtain n3 A3 B3 C3 where "rP n1 A1 B1 C1 n3 A3 B3 C3 \<and> rC S A3 B3 C3" by blast
    moreover obtain u3 where "u3 = (n3, A3, B3, C3)" by blast
    moreover have "rC S A1 B1 C1" using c1 c2 unfolding rE_def by blast
    ultimately have "(u1,u3) \<in> rE S" using c2 unfolding rE_def by blast
    then show "\<exists> u3. (u1,u3) \<in> rE S" by blast
  qed
  then show ?thesis unfolding Field_def by blast
qed

lemma lem_wrd_fin_field_rE: 
fixes S::"'U set"
assumes "\<not> finite S"
shows "u \<in> Field (rE S) \<Longrightarrow> finite (wrd u)"
proof -
  assume "u \<in> Field (rE S)"
  then have "u \<in> Domain (rE S)" using assms lem_rE_domfield by blast
  then show "finite (wrd u)" using lem_rP_inv unfolding rE_def by force
qed

lemma lem_rE_rtr_wrd_mon:
fixes S::"'U set" and u v::"'U rD"
shows "(u,v) \<in> (rE S)^* \<Longrightarrow> wrd u \<subseteq> wrd v"
proof -
  assume a1: "(u,v) \<in> (rE S)^*"
  have b1: "\<And> u v::'U rD. (u,v) \<in> (rE S) \<Longrightarrow> wrd u \<subseteq> wrd v"
  proof -
    fix u v::"'U rD"
    assume a1: "(u,v) \<in> (rE S)"
    obtain n A B C where b1: "u = (n,A,B,C)" using prod_cases4 by blast
    obtain n' A' B' C' where b2: "v = (n',A',B',C')" using prod_cases4 by blast
    have "wrd u = A \<union> B \<union> C \<and> wrd v = A'\<union> B'\<union> C'" using a1 b1 b2 by simp
    then show "wrd u \<subseteq> wrd v" using a1 b1 b2 lem_rP_inv unfolding rE_def by fast
  qed
  have "\<And> n. \<forall> u v::'U rD. (u,v) \<in> (rE S)^^n \<longrightarrow> wrd u \<subseteq> wrd v"
  proof -
    fix n 
    show "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^n \<longrightarrow> wrd u \<subseteq> wrd v"
    proof (induct n)
      show "\<forall> u v. (u,v) \<in> (rE S)^^0 \<longrightarrow> wrd u \<subseteq> wrd v" by simp
    next
      fix m
      assume d1: "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^m \<longrightarrow> wrd u \<subseteq> wrd v"
      show "\<forall> u v::'U rD. (u,v) \<in> (rE S)^^(Suc m) \<longrightarrow> wrd u \<subseteq> wrd v"
      proof (intro allI impI)
        fix u v::"'U rD"
        assume "(u,v) \<in> (rE S)^^(Suc m)"
        then obtain v' where "(u,v') \<in> (rE S)^^m \<and> (v',v) \<in> (rE S)" by force
        then show "wrd u \<subseteq> wrd v" using d1 b1 by blast
      qed
    qed
  qed
  then show "wrd u \<subseteq> wrd v" using a1 rtrancl_imp_relpow by blast
qed

lemma lem_Wrd_bkset_rE: "Wrd (bkset (rE S) U) = Wrd U"
proof
  show "Wrd (bkset (rE S) U) \<subseteq> Wrd U"
  proof
    fix y
    assume "y \<in> Wrd (bkset (rE S) U)"
    then obtain u v where "u \<in> U \<and> (v,u) \<in> (rE S)^* \<and> y \<in> wrd v" unfolding Wrd_def bkset_def by force
    moreover then have "wrd v \<subseteq> wrd u" using lem_rE_rtr_wrd_mon by blast
    ultimately show "y \<in> Wrd U" unfolding Wrd_def by blast
  qed
next
  show "Wrd U \<subseteq> Wrd (bkset (rE S) U)" unfolding Wrd_def bkset_def by blast
qed

lemma lem_Wrd_rE_field_subs_cnt: 
fixes S::"'U set" and U::"('U rD) set"
assumes "\<not> finite S"
shows "U \<subseteq> Field (rE S) \<Longrightarrow> |U| \<le>o |UNIV::nat set| \<Longrightarrow> |Wrd U| \<le>o |UNIV::nat set|"
proof -
  assume b1: "U \<subseteq> Field (rE S)" and a2: "|U| \<le>o |UNIV::nat set|"
  moreover have "\<forall>u\<in>U. |wrd u| \<le>o |UNIV::nat set|"
  proof
    fix u::"'U rD"
    assume "u \<in> U"
    then have "finite (wrd u)" using b1 assms lem_wrd_fin_field_rE by blast
    then show "|wrd u| \<le>o |UNIV::nat set|" using ordLess_imp_ordLeq by force
  qed
  ultimately have "|\<Union>u\<in>U. wrd u| \<le>o |UNIV::nat set|" 
    using card_of_UNION_ordLeq_infinite infinite_UNIV_nat by blast
  then show "|Wrd U| \<le>o |UNIV::nat set|" unfolding Wrd_def by simp
qed

lemma lem_rE_dn_cnt: 
fixes S::"'U set" and U::"('U rD) set"
assumes "\<not> finite S"
shows "U \<subseteq> Field (rE S) \<Longrightarrow> |U| \<le>o |UNIV::nat set| \<Longrightarrow> V \<subseteq> bkset (rE S) U \<Longrightarrow> |Wrd V| \<le>o |UNIV::nat set|"
proof -
  assume a1: "U \<subseteq> Field (rE S)" and a2: "|U| \<le>o |UNIV::nat set|" and a3: "V \<subseteq> bkset (rE S) U"
  have "Wrd V \<subseteq> Wrd (bkset (rE S) U)" using a3 unfolding Wrd_def by blast
  then have "|Wrd V| \<le>o |Wrd (bkset (rE S) U)|" by simp
  moreover have "|Wrd (bkset (rE S) U)| \<le>o |UNIV::nat set|" 
    using a1 a2 assms lem_Wrd_bkset_rE[of S U] lem_Wrd_rE_field_subs_cnt[of S U] by force
  ultimately show "|Wrd V| \<le>o |UNIV::nat set|" using ordLeq_transitive by blast
qed

lemma lem_rE_succ_Wrd_univ: "(u,w) \<in> (rE S) \<Longrightarrow> levrd u \<in> {\<l>0, \<l>2, \<l>4} \<Longrightarrow> S - wrd w \<subseteq> Wrd (((rE S)``{u}) - {w})"
proof -
  assume a1: "(u,w) \<in> (rE S)" and a2: "levrd u \<in> {\<l>0, \<l>2, \<l>4}"
  moreover obtain n a b c where b2: "u = (n,a,b,c)" using prod_cases4 by blast
  moreover obtain n' a' b' c' where b3: "w = (n',a',b',c')" using prod_cases4 by blast
  ultimately have b4: "rP n a b c n' a' b' c' \<and> rC S a b c \<and> rC S a' b' c'" unfolding rE_def by blast
  have "\<forall> y \<in> S. y \<notin> wrd w \<longrightarrow> (\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v)"
  proof (intro ballI impI)
    fix y
    assume c0: "y \<in> S" and c1: "y \<notin> wrd w"
    have "n = \<l>0 \<longrightarrow> (\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v)"
    proof
      assume "n = \<l>0"
      then have "(u, (\<l>1, {y}, {}, {})) \<in> (rE S)" using c0 b2 b4 unfolding rE_def rC_def by force
      then show "\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v" using c1 by force
    qed
    moreover have "n = \<l>2 \<longrightarrow> (\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v)"
    proof
      assume "n = \<l>2"
      then have "(u, (\<l>3, a, {y}, {})) \<in> (rE S)" using c0 b2 b4 unfolding rE_def rC_def by force
      then show "\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v" using c1 by force
    qed
    moreover have "n = \<l>4 \<longrightarrow> (\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v)"
    proof
      assume "n = \<l>4"
      then have "(u, (\<l>5, a, b, {y})) \<in> (rE S)" using c0 b2 b4 unfolding rE_def rC_def by force
      then show "\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v" using c1 by force
    qed
    ultimately show "\<exists> v \<in> (rE S)``{u} - {w}. y \<in> wrd v" using a2 b2 by force
  qed
  then show "S - wrd w \<subseteq> Wrd (((rE S)``{u}) - {w})" unfolding Wrd_def by blast
qed

lemma lem_rE_succ_nocntbnd:
fixes S::"'U set" and u0::"'U rD" and v0::"'U rD" and U::"('U rD) set"
assumes a0: "\<not> |S| \<le>o |UNIV::nat set|" and a1: "(u0, v0) \<in> (rE S)" and a2: "levrd u0 \<in> {\<l>0, \<l>2, \<l>4}"
    and a3: "U \<subseteq> Field (rE S)" and a4: "((rE S) `` {u0}) - {v0} \<subseteq> bkset (rE S) U"
shows "\<not> |U| \<le>o |UNIV::nat set|"
proof
  assume "|U| \<le>o |UNIV::nat set|"
  moreover have c0: "\<not> finite S" using a0 by (meson card_of_Well_order infinite_iff_card_of_nat ordLeq_total)
  ultimately have c1: "|Wrd (((rE S)``{u0}) - {v0})| \<le>o |UNIV::nat set|" using a3 a4 lem_rE_dn_cnt by blast
  have "v0 \<in> Field (rE S)" using a1 unfolding Field_def by blast
  then have "finite (wrd v0)" using c0 a0 lem_wrd_fin_field_rE by blast
  then have "\<not> |S - wrd v0| \<le>o |UNIV::nat set|" using a0 
    by (metis card_of_infinite_diff_finite finite_iff_cardOf_nat ordIso_symmetric ordLeq_iff_ordLess_or_ordIso ordLeq_transitive)
  moreover have "S - wrd v0 \<subseteq> Wrd (((rE S)``{u0}) - {v0})" using lem_rE_succ_Wrd_univ a1 a2 by blast
  ultimately have "\<not> |Wrd (((rE S)``{u0}) - {v0})| \<le>o |UNIV::nat set|" by (metis card_of_mono1 ordLeq_transitive)
  then show "False" using c1 by blast
qed

lemma lem_rE_succ_nocntbnd2:
fixes S::"'U set" and u0::"'U rD" and v0::"'U rD"
assumes a0: "\<not> |S| \<le>o |UNIV::nat set|"
    and a1: "(u0, v0) \<in> (rE S)" and a2: "levrd u0 \<in> {\<l>0, \<l>2, \<l>4}"
    and a3: "r \<subseteq> (rE S)" and a4: "\<forall> u. |r``{u}| \<le>o |UNIV::nat set|"
    and a5: "((rE S) `` {u0}) - {v0} \<subseteq> bkset (rE S) ((r^*)``{u0})"
shows "False"
proof -
  have b1: "\<And> n::nat. \<And> u::('U rD). u \<in> Field (rE S) \<longrightarrow> (r^^n)``{u} \<subseteq> Field (rE S) \<and> |(r^^n)``{u}| \<le>o |UNIV::nat set|"
  proof (intro impI)
    fix n::nat and u::"'U rD"
    assume c1: "u \<in> Field (rE S)"
    show "(r^^n)``{u} \<subseteq> Field (rE S) \<and> |(r^^n) `` {u}| \<le>o |UNIV::nat set|"
    proof (induct n)
      show "(r^^0)``{u} \<subseteq> Field (rE S) \<and> |(r ^^ 0) `` {u}| \<le>o |UNIV::nat set|" using c1 by simp
    next
      fix m
      assume d1: "(r^^m)``{u} \<subseteq> Field (rE S) \<and> |(r^^m)``{u}| \<le>o |UNIV::nat set|"
      moreover have "\<forall> v \<in> (r^^m)``{u}. |r``{v}| \<le>o |UNIV::nat set|" using a4 by blast
      moreover have  "(r ^^ Suc m) `` {u} = (\<Union>v\<in>((r^^m)``{u}). r ``{v})" by force
      ultimately have "|(r ^^ Suc m) `` {u}| \<le>o |UNIV::nat set|" 
        using card_of_UNION_ordLeq_infinite[of "UNIV::nat set" "(r^^m)``{u}"] infinite_UNIV_nat by simp
      moreover have "(r ^^ Suc m)``{u} \<subseteq> Field (rE S)" using d1 a3 unfolding Field_def by fastforce
      ultimately show "(r ^^ Suc m)``{u} \<subseteq> Field (rE S) \<and> |(r ^^ Suc m) `` {u}| \<le>o |UNIV::nat set|" by blast
    qed
  qed
  have b2: "\<And> u::'U rD. u \<in> Field (rE S) \<longrightarrow> |(r^*) `` {u}| \<le>o |UNIV::nat set|"
  proof (intro impI)
    fix u::"'U rD"
    assume c1: "u \<in> Field (rE S)"
    have "|UNIV::nat set| \<le> |UNIV::nat set|" by simp
    moreover have "\<forall>n. |(r^^n) `` {u}| \<le>o |UNIV::nat set|" using c1 b1 by blast
    ultimately have c1: "|\<Union>n. (r^^n) `` {u}| \<le>o |UNIV::nat set|"
      using card_of_UNION_ordLeq_infinite[of "UNIV::nat set" "UNIV::nat set"] infinite_UNIV_nat by simp
    have "(r^*) `` {u} \<subseteq> (\<Union>n. (r^^n) `` {u})" by (simp add: rtrancl_is_UN_relpow subset_eq)
    then have "|(r^*) `` {u}| \<le>o |\<Union>n. (r^^n) `` {u}|" by simp
    then show "|(r^*) `` {u}| \<le>o |UNIV::nat set|" using c1 ordLeq_transitive by blast
  qed
  obtain U where b3: "U = ((r^*) `` {u0})" by blast
  have "U \<subseteq> (\<Union>n. (r^^n) `` {u0})" using b3 by (simp add: rtrancl_is_UN_relpow subset_eq)
  moreover have "u0 \<in> Field (rE S)" using a1 unfolding Field_def by blast
  ultimately have "U \<subseteq> Field (rE S) \<and> |U| \<le>o |UNIV::nat set|" using b1 b2 b3 by blast
  moreover have "((rE S) `` {u0}) - {v0} \<subseteq> bkset (rE S) U" using b3 a5 by blast
  ultimately show "False" using a0 a1 a2 lem_rE_succ_nocntbnd[of S u0 v0 U] by blast
qed

lemma lem_rE_diamsubr_un:
fixes S::"'U set"
assumes a1: "r0 \<subseteq> (rE S)" and a2: "\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0 \<longrightarrow> (\<exists> d. (b,d) \<in> r0^= \<and> (c,d) \<in> r0^=)"
shows "\<forall> u. \<exists> v. r0``{u} \<subseteq> {v}"
proof
  fix u
  have "\<forall> v w. (u,v) \<in> r0 \<and> (u,w) \<in> r0 \<longrightarrow> v = w"
  proof (intro allI impI)
    fix v w
    assume "(u,v) \<in> r0 \<and> (u,w) \<in> r0"
    moreover then obtain t where "(v,t) \<in> r0^= \<and> (w,t) \<in> r0^=" using a2 by blast
    ultimately have "(u,v) \<in> (rE S) \<and> (u,w) \<in> (rE S) \<and> (v,t) \<in> (rE S)^= \<and> (w,t) \<in> (rE S)^=" using a1 by blast
    then show "v = w" using lem_rE_df by blast
  qed
  then show "\<exists> v. r0``{u} \<subseteq> {v}" by blast
qed

lemma lem_rE_succ_nocntbnd3:
fixes S::"'U set" and u0::"'U rD" and v0::"'U rD"
assumes a0: "\<not> |S| \<le>o |UNIV::nat set|"
    and a1: "LD2 (rE S) r0 r1"
    and a2: "(u0, v0) \<in> (rE S)" and a3: "levrd u0 \<in> {\<l>0, \<l>2, \<l>4}"
    and a4: "r = {(u,v) \<in> rE S. u = v0} \<union> r0"
    and a5: "((rE S) `` {u0}) - {v0} \<subseteq> bkset (rE S) ((r^*)``{u0})"
shows "False"
proof -
  have b1: "r0 \<subseteq> (rE S)" using a1 unfolding LD2_def by blast
  then have "r \<subseteq> (rE S)" using a4 by blast
  moreover have "\<forall> u. |r``{u}| \<le>o |UNIV::nat set|"
  proof
    fix u
    have "\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0 \<longrightarrow> (\<exists> d. (b,d) \<in> r0^= \<and> (c,d) \<in> r0^=)"
      using a1 unfolding LD2_def jn00_def by blast
    then obtain v where "r0``{u} \<subseteq> {v}" using b1 lem_rE_diamsubr_un[of r0] by blast
    moreover have "r``{u} \<subseteq> r0``{u} \<union> (rE S)``{v0}" using a4 by blast
    ultimately have "r``{u} \<subseteq> {v} \<union> (rE S)``{v0}" by blast
    moreover have "|{v} \<union> (rE S)``{v0}| \<le>o |UNIV::nat set|"
    proof -
      have "levrd v0 \<in> {\<l>1, \<l>3, \<l>5}" using a2 a3 unfolding rE_def by force
      moreover have "\<not> finite S" using a0 by (meson card_of_Well_order infinite_iff_card_of_nat ordLeq_total)
      moreover then have "v0 \<in> Domain (rE S)" using a2 a0 lem_rE_domfield unfolding Field_def by blast
      ultimately obtain v0' where "(rE S)``{v0} \<subseteq> {v0'}" using lem_rE_levun by blast
      then have "{v} \<union> (rE S)``{v0} \<subseteq> {v,v0'}" by blast
      then have "finite ({v} \<union> (rE S)``{v0})" by (meson finite.emptyI finite.insertI rev_finite_subset)
      then show ?thesis by (simp add: ordLess_imp_ordLeq)
    qed
    ultimately show "|r``{u}| \<le>o |UNIV::nat set|" using card_of_mono1 ordLeq_transitive by blast
  qed
  ultimately show ?thesis using a0 a2 a3 a5 lem_rE_succ_nocntbnd2[of S u0 v0 r] by blast
qed

lemma lem_rE_one:
fixes S::"'U set" and u0::"'U rD" and v0::"'U rD"
assumes a0: "\<not> |S| \<le>o |UNIV::nat set|" and a1: "LD2 (rE S) r0 r1" 
    and a2: "(u0, v0) \<in> r0" and a3: "levrd u0 \<in> {\<l>0, \<l>2, \<l>4}"
shows "False"
proof -
  obtain r where b1: "r = {(u,v) \<in> rE S. u = v0} \<union> r0" by blast
  moreover have "(u0, v0) \<in> (rE S)" using a1 a2 unfolding LD2_def by blast
  moreover have "((rE S) `` {u0}) - {v0} \<subseteq> bkset (rE S) ((r^*)``{u0})"
  proof
    fix v
    assume c1: "v \<in> ((rE S) `` {u0}) - {v0}"
    have "\<exists> v. r0``{u0} \<subseteq> {v}" using a1 lem_rE_diamsubr_un[of r0 S] unfolding LD2_def jn00_def by blast
    then have "r0 `` {u0} \<subseteq> {v0}" using a2 by blast
    moreover have c2: "(rE S) = r0 \<union> r1" using a1 unfolding LD2_def by blast
    ultimately have "(u0, v) \<in> r1" using c1 by blast
    then have "jn01 r0 r1 v0 v" using a1 a2 unfolding LD2_def by blast
    then obtain v0' d where c3: "(v0, v0') \<in> r1^= \<and> (v0', d) \<in> r0^* \<and> (v, d) \<in> r0^*" unfolding jn01_def by blast
    obtain U where c4: "U = (r^*)``{u0}" by blast
    have "(u0, d) \<in> r^*"
    proof -
      have "v0 = v0' \<or> (v0,v0') \<in> (rE S)" using c2 c3 by blast
      then have "(v0, v0') \<in> r^=" using b1 by blast
      moreover have "(u0, v0) \<in> r" using b1 a2 by blast
      ultimately have "(u0, v0') \<in> r^*" by force
      moreover have "(v0',d) \<in> r^*" using c3 b1 rtrancl_mono[of r0 r] by blast
      ultimately show ?thesis by force
    qed
    then have "d \<in> U" using c4 by blast
    then have c3: "v \<in> bkset r0 U" using c3 unfolding bkset_def by blast
    have "r0 \<subseteq> (rE S)" using a1 unfolding LD2_def by blast
    then have "bkset r0 U \<subseteq> bkset (rE S) U" unfolding bkset_def by (simp add: Image_mono rtrancl_mono)
    then show "v \<in> bkset (rE S) ((r^*)``{u0})" using c3 c4 by blast
  qed
  ultimately show "False" using a0 a1 a3 lem_rE_succ_nocntbnd3[of S r0 r1 u0 v0 r] by blast
qed

lemma lem_rE_jn0:
fixes S::"'U set" and u1::"'U rD" and u2::"'U rD" and v::"'U rD"
assumes a1: "(u1,v) \<in> (rE S)" and a2: "(u2,v) \<in> (rE S)" and a3: "u1 \<noteq> u2"
shows "levrd v \<in> {\<l>7, \<l>8}"
proof -
  obtain n1 a1 b1 c1 where b1: "u1 = (n1,a1,b1,c1)" using prod_cases4 by blast
  obtain n2 a2 b2 c2 where b2: "u2 = (n2,a2,b2,c2)" using prod_cases4 by blast
  obtain n a b c where b3: "v = (n,a,b,c)" using prod_cases4 by blast
  have "rP n1 a1 b1 c1 n a b c" using b1 b3 a1 unfolding rE_def by blast
  moreover have "rP n2 a2 b2 c2 n a b c" using b2 b3 a2 unfolding rE_def by blast
  moreover have "(n1,a1,b1,c1) \<noteq> (n2,a2,b2,c2)" using a3 b1 b2 by blast
  ultimately have "n \<in> { \<l>7, \<l>8}"
    apply (cases n1, cases n2)
    apply (simp+, cases n2)
    apply (simp+, cases n2)
    apply (simp+, cases n2)
    apply (simp+, cases n2)
    apply (simp+, cases n2)
    apply simp+
    done
  then show ?thesis using b3 by simp
qed

lemma lem_rE_jn1:
fixes S::"'U set" and u1::"'U rD" and u2::"'U rD" and v::"'U rD"
assumes a1: "(u1,v) \<in> (rE S)" and a2: "(u2,v) \<in> (rE S)^*" and a3: "(u1,u2) \<notin> (rE S) \<and> (u2,u1) \<notin> (rE S)^*"
shows "levrd v \<in> {\<l>7, \<l>8}"
proof -
  have "\<And> k2. \<forall> u1 u2 v::'U rD. \<forall> i. i \<le> k2 \<and> (u1,u2) \<notin> (rE S) \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1,v) \<in> (rE S) \<longrightarrow> (u2,v) \<in> (rE S)^^i \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
  proof -
    fix k2
    show "\<forall> u1 u2 v::'U rD. \<forall> i. i \<le> k2 \<and> (u1,u2) \<notin> (rE S) \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1,v) \<in> (rE S) \<longrightarrow> (u2,v) \<in> (rE S)^^i \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
    proof (induct k2)
      show "\<forall>u1 u2 v::'U rD. \<forall> i. i \<le> 0 \<and> (u1,u2) \<notin> (rE S) \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1, v) \<in> (rE S) \<longrightarrow> (u2, v) \<in> (rE S)^^i \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}" by force
    next
      fix k2
      assume d1: "\<forall>u1 u2 v::'U rD. \<forall> i.  i \<le> k2 \<and> (u1,u2) \<notin> (rE S) \<and> (u2, u1) \<notin> (rE S)^* \<longrightarrow>
                 (u1, v) \<in> (rE S) \<longrightarrow> (u2, v) \<in> (rE S)^^i \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
      show "\<forall>u1 u2 v::'U rD. \<forall> i. i \<le> Suc k2 \<and> (u1,u2) \<notin> (rE S) \<and> (u2, u1) \<notin> (rE S)^* \<longrightarrow>
          (u1, v) \<in> (rE S) \<longrightarrow> (u2, v) \<in> (rE S)^^i \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
      proof (intro allI impI)
        fix u1 u2 v::"'U rD" and i
        assume e1: "i \<le> Suc k2 \<and> (u1, u2) \<notin> (rE S) \<and> (u2, u1) \<notin> (rE S)^*" 
           and e2: "(u1, v) \<in> (rE S)" and e3: "(u2, v) \<in> (rE S)^^i"
        show "levrd v \<in> {\<l>7, \<l>8}"
        proof (cases "i = Suc k2")
          assume f1: "i = Suc k2"
          then obtain v' where f2: "(u2, v') \<in> (rE S)" and f3: "(v', v) \<in> (rE S)^^k2" using e3 by (meson relpow_Suc_E2)
          moreover have "k2 \<le> k2" using e1 by force
          ultimately have "(v',u1) \<notin> (rE S)^* \<and> (u1,v') \<notin> (rE S) \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}" using e2 d1 by blast
          moreover have "(v',u1) \<in> (rE S)^* \<longrightarrow> False"
          proof
            assume "(v',u1) \<in> (rE S)^*"
            then have "(u2,u1) \<in> (rE S)^*" using f2 by force
            then show "False" using e1 by blast
          qed
          moreover have "(u1,v') \<in> (rE S) \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
          proof
            assume "(u1,v') \<in> (rE S)"
            moreover have "u1 \<noteq> u2" using e1 by force
            ultimately have "levrd v' \<in> {\<l>7, \<l>8}" using f2 lem_rE_jn0[of u1 v' S u2] by blast
            moreover have "(v', v) \<in> (rE S)^*" using f3 rtrancl_power by blast
            moreover have "lev_next ` {\<l>7, \<l>8} \<subseteq> {\<l>7, \<l>8}" by simp
            ultimately show "levrd v \<in> {\<l>7, \<l>8}" using lem_rE_levset_inv[of v' v S "{\<l>7, \<l>8}"] by blast
          qed
          ultimately show ?thesis by blast
        next
          assume "i \<noteq> Suc k2"
          then have "i \<le> k2" using e1 by force
          then show ?thesis using d1 e1 e2 e3 by blast
        qed
      qed
    qed
  qed
  moreover obtain k2 where "(u2,v) \<in> (rE S)^^k2" using a2 rtrancl_imp_relpow by blast  
  moreover have "k2 \<le> k2" by force
  ultimately show ?thesis using a1 a3 by blast
qed

lemma lem_rE_jn2:
fixes S::"'U set" and u1::"'U rD" and u2::"'U rD" and v::"'U rD"
assumes a1: "(u1,v) \<in> (rE S)^*" and a2: "(u2,v) \<in> (rE S)^*" and a3: "(u1,u2) \<notin> (rE S)^* \<and> (u2,u1) \<notin> (rE S)^*"
shows "levrd v \<in> {\<l>7, \<l>8}"
proof -
  have "\<And> k1. \<forall> u1 u2 v::'U rD. \<forall> i. i \<le> k1 \<and> (u1,u2) \<notin> (rE S)^* \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1,v) \<in> (rE S)^^i \<longrightarrow> (u2,v) \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
  proof -
    fix k1
    show "\<forall> u1 u2 v::'U rD. \<forall> i. i \<le> k1 \<and> (u1,u2) \<notin> (rE S)^* \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1,v) \<in> (rE S)^^i \<longrightarrow> (u2,v) \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
    proof (induct k1)
      show "\<forall>u1 u2 v::'U rD. \<forall> i. i \<le> 0 \<and> (u1,u2) \<notin> (rE S)^* \<and> (u2,u1) \<notin> (rE S)^* \<longrightarrow> (u1, v) \<in> (rE S)^^i \<longrightarrow> (u2, v) \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
      proof (intro allI impI)
        fix u1 u2 v::"'U rD" and i
        assume "i \<le> 0 \<and> (u1,u2) \<notin> (rE S)^* \<and> (u2,u1) \<notin> (rE S)^*" and "(u1, v) \<in> (rE S)^^i" and "(u2, v) \<in> (rE S)^*"
        moreover then have "(u2,u1) \<in> (rE S)^*" using rtrancl_power by fastforce
        ultimately have "False" by blast
        then show "levrd v \<in> {\<l>7, \<l>8}" by blast
      qed
    next
      fix k1
      assume d1: "\<forall>u1 u2 v::'U rD. \<forall> i.  i \<le> k1 \<and> (u1, u2) \<notin> (rE S)^* \<and> (u2, u1) \<notin> (rE S)^* \<longrightarrow>
                 (u1, v) \<in> (rE S) ^^ i \<longrightarrow> (u2, v) \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
      show "\<forall>u1 u2 v::'U rD. \<forall> i. i \<le> Suc k1 \<and> (u1, u2) \<notin> (rE S)^* \<and> (u2, u1) \<notin> (rE S)^* \<longrightarrow>
          (u1, v) \<in> (rE S) ^^ i \<longrightarrow> (u2, v) \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
      proof (intro allI impI)
        fix u1 u2 v::"'U rD" and i
        assume e1: "i \<le> Suc k1 \<and> (u1, u2) \<notin> (rE S)^* \<and> (u2, u1) \<notin> (rE S)^*" 
           and e2: "(u1, v) \<in> (rE S)^^i" and e3: "(u2, v) \<in> (rE S)^*"
        show "levrd v \<in> {\<l>7, \<l>8}"
        proof (cases "i = Suc k1")
          assume f1: "i = Suc k1"
          then obtain v' where f2: "(u1, v') \<in> (rE S)" and f3: "(v', v) \<in> (rE S)^^k1" using e2 by (meson relpow_Suc_E2)
          moreover have "k1 \<le> k1" using e1 by force
          ultimately have "(v',u2) \<notin> (rE S)^* \<and> (u2,v') \<notin> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}" using e3 d1 by blast
          moreover have "(v',u2) \<in> (rE S)^* \<longrightarrow> False"
          proof
            assume "(v',u2) \<in> (rE S)^*"
            then have "(u1,u2) \<in> (rE S)^*" using f2 by force
            then show "False" using e1 by blast
          qed
          moreover have "(u2,v') \<in> (rE S)^* \<longrightarrow> levrd v \<in> {\<l>7, \<l>8}"
          proof
            assume "(u2,v') \<in> (rE S)^*"
            then have "levrd v' \<in> {\<l>7, \<l>8}" using e1 f2 lem_rE_jn1[of u1 v' S u2] by blast
            moreover have "(v', v) \<in> (rE S)^*" using f3 rtrancl_power by blast
            moreover have "lev_next ` {\<l>7, \<l>8} \<subseteq> {\<l>7, \<l>8}" by simp
            ultimately show "levrd v \<in> {\<l>7, \<l>8}" using lem_rE_levset_inv[of v' v S "{\<l>7, \<l>8}"] by blast
          qed
          ultimately show ?thesis by blast
        next
          assume "i \<noteq> Suc k1"
          then have "i \<le> k1" using e1 by force
          then show ?thesis using d1 e1 e2 e3 by blast
        qed
      qed
    qed
  qed
  moreover obtain k1 where "(u1,v) \<in> (rE S)^^k1" using a1 rtrancl_imp_relpow by blast  
  moreover have "k1 \<le> k1" by force
  ultimately show ?thesis using a2 a3 by blast
qed

lemma lem_rel_pow2fw: "(u,u1) \<in> r \<and> (u1,v) \<in> r\<longrightarrow> (u,v) \<in> r^^2" 
  by (metis Suc_1 relpow_1 relpow_Suc_I)

lemma lem_rel_pow3fw: "(u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,v) \<in> r \<longrightarrow> (u,v) \<in> r^^3" 
  by (metis One_nat_def numeral_3_eq_3 relpow_1 relpow_Suc_I)

lemma lem_rel_pow3: "(u,v) \<in> r^^3 \<Longrightarrow> \<exists> u1 u2. (u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,v) \<in> r"
  by (metis One_nat_def numeral_3_eq_3 relpow_1 relpow_Suc_E)

lemma lem_rel_pow4: "(u,v) \<in> r^^4 \<Longrightarrow> \<exists> u1 u2 u3. (u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r \<and> (u3,v) \<in> r"
proof -
  assume "(u,v) \<in> r^^4"
  then obtain u3 where "(u,u3) \<in> r^^3 \<and> (u3,v) \<in> r" using relpow_E by force
  moreover then obtain u1 u2 where "(u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r"
    by (metis One_nat_def numeral_3_eq_3 relpow_1 relpow_Suc_E)
  ultimately show "\<exists> u1 u2 u3. (u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r \<and> (u3,v) \<in> r" by blast
qed

lemma lem_rel_pow5: "(u,v) \<in> r^^5 \<Longrightarrow> \<exists> u1 u2 u3 u4. (u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r \<and> (u3,u4) \<in> r \<and> (u4,v) \<in> r"
proof -
  assume "(u,v) \<in> r^^5"
  then obtain u4 where "(u,u4) \<in> r^^4 \<and> (u4,v) \<in> r" using relpow_E by force
  moreover then obtain u1 u2 u3 where "(u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r \<and> (u3, u4) \<in> r"
    using lem_rel_pow4[of u u4 r] by blast
  ultimately show "\<exists> u1 u2 u3 u4. (u,u1) \<in> r \<and> (u1,u2) \<in> r \<and> (u2,u3) \<in> r \<and> (u3,u4) \<in> r \<and> (u4,v) \<in> r" by blast
qed

lemma lem_rE_l1_l78_dist:
fixes S::"'U set"
assumes a1: "levrd u = \<l>1" and a2: "levrd v \<in> {\<l>7, \<l>8}" and a3: "n \<le> 5"
shows "(u,v) \<notin> (rE S)^^n"
proof -
  have b0: "(u,v) \<notin> (rE S)^^0" using a1 a2 by force
  have b1: "(u,v) \<notin> (rE S)^^1" using a1 a2 lem_rE_succ_lev[of u v] by force
  have "\<And> u1. (u,u1) \<in> (rE S) \<and> (u1,v) \<in> (rE S) \<Longrightarrow> False" 
    using a1 a2 lem_rE_succ_lev
    by (metis Lev.distinct(49) Lev.distinct(51) insertE lev_next.simps(2) lev_next.simps(3) singletonD) 
  then have b2: "(u,v) \<notin> (rE S)^^2" by (metis Suc_1 relpow_1 relpow_Suc_D2)
  have "\<And> u1 u2. (u,u1) \<in> (rE S) \<and> (u1,u2) \<in> (rE S) \<and> (u2,v) \<in> (rE S) \<Longrightarrow> False"
    using a1 a2 lem_rE_succ_lev
    by (metis Lev.distinct(57) Lev.distinct(59) insertE lev_next.simps(2) lev_next.simps(3) lev_next.simps(4) singletonD)
  then have b3: "(u,v) \<notin> (rE S)^^3" using lem_rel_pow3[of u v "rE S"] by blast
  have "\<And> u1 u2 u3. (u,u1) \<in> (rE S) \<and> (u1,u2) \<in> (rE S) \<and> (u2,u3) \<in> (rE S) \<and> (u3,v) \<in> (rE S) \<Longrightarrow> False"
    using a1 a2 lem_rE_succ_lev
    by (metis Lev.distinct(63) Lev.distinct(65) insertE lev_next.simps(2) lev_next.simps(3) lev_next.simps(4) lev_next.simps(5) singletonD)
  then have b4: "(u,v) \<notin> (rE S)^^4" using lem_rel_pow4[of u v "rE S"] by blast
  have "\<And> u1 u2 u3 u4. (u,u1) \<in> (rE S) \<and> (u1,u2) \<in> (rE S) \<and> (u2,u3) \<in> (rE S) \<and> (u3,u4) \<in> (rE S) \<and> (u4,v) \<in> (rE S) \<Longrightarrow> False"
    using a1 a2 lem_rE_succ_lev
    by (metis Lev.distinct(67) Lev.distinct(69) insertE lev_next.simps(2) lev_next.simps(3) lev_next.simps(4) lev_next.simps(5) lev_next.simps(6) singletonD)
  then have b5: "(u,v) \<notin> (rE S)^^5" using lem_rel_pow5[of u v "rE S"] by blast
  have "n = 0 \<or> n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4 \<or> n = 5" using a3 by force
  then show ?thesis using b0 b1 b2 b3 b4 b5 by blast
qed

lemma lem_rE_notLD2:
fixes S::"'U set" and r0 r1::"('U rD) rel"
assumes a0: "\<not> |S| \<le>o |UNIV::nat set|" and a1: "LD2 (rE S) r0 r1"
shows "False"
proof -
  obtain x0::'U where b0: "x0 \<in> S" using a0
    by (metis all_not_in_conv card_of_mono1 card_of_singl_ordLeq empty_subsetI 
        finite.emptyI infinite_UNIV_char_0 ordLeq_transitive)
  obtain u::"'U rD" where b1: "u = (\<l>0, {}, {}, {})" by blast
  obtain v1::"'U rD" where b2: "v1 = (\<l>1, {}, {}, {})" by blast
  obtain v2::"'U rD" where b3: "v2 = (\<l>1, {x0}, {}, {})" by blast
  have "levrd u = \<l>0" using b1 by simp
  then have "(u,v1) \<notin> r0 \<and> (u,v2) \<notin> r0" using a0 a1 lem_rE_one[of S r0 r1 u ] by blast
  moreover have "(u,v1) \<in> (rE S) \<and> (u,v2) \<in> (rE S)" using b0 b1 b2 b3 unfolding rE_def rC_def by simp
  ultimately have "(u,v1) \<in> r1 \<and> (u,v2) \<in> r1" using a1 unfolding LD2_def by blast
  then have "jn11 r0 r1 v1 v2" using a1 unfolding LD2_def by blast
  then obtain b' b'' c' c'' d where 
       b4: "(v1, b') \<in> r0^* \<and> (b', b'') \<in> r1^= \<and> (b'', d) \<in> r0^*"
   and b5: "(v2, c') \<in> r0^* \<and> (c', c'') \<in> r1^= \<and> (c'', d) \<in> r0^*" unfolding jn11_def by blast
  have b6: "\<And> v v'::'U rD. levrd v \<in> {\<l>1, \<l>3} \<and> (v, v') \<in> r0^* \<Longrightarrow> (v,v') \<in> r0^="
  proof -
    fix v v'::"'U rD"
    assume c1: "levrd v \<in> {\<l>1, \<l>3} \<and> (v, v') \<in> r0^*"
    then obtain k1 where c2: "(v, v') \<in> r0^^k1" using rtrancl_imp_relpow by blast
    have "k1 \<ge> 2 \<longrightarrow> False"
    proof
      assume "k1 \<ge> 2"
      then obtain k where "k1 = 2 + k" using le_Suc_ex by blast
      then obtain w' where "(v, w') \<in> r0^^2" using c2 relpow_add[of 2 k r0] by fastforce
      then obtain w w' where "(v, w) \<in> r0 \<and> (w, w') \<in> r0" by (metis One_nat_def numeral_2_eq_2 relpow_1 relpow_Suc_E)
      moreover then have "(v, w) \<in> (rE S)" using a1 unfolding LD2_def by blast
      moreover then have "levrd w \<in> {\<l>2, \<l>4}" using c1 unfolding rE_def by force
      ultimately show "False" using a0 a1 lem_rE_one by blast
    qed
    then have "k1 = 0 \<or> k1 = 1" by (simp add: less_2_cases)
    then show "(v, v') \<in> r0^=" using c2 by force
  qed
  then have b7: "(v1, b') \<in> r0^= \<and> (v2, c') \<in> r0^=" using b2 b3 b4 b5 by simp
  have b8: "levrd d \<in> {\<l>7, \<l>8}"
  proof -
    have "r0 \<subseteq> (rE S) \<and> r1 \<subseteq> (rE S)" using a1 unfolding LD2_def by blast
    then have "r0^* \<subseteq> (rE S)^* \<and> r1^= \<subseteq> (rE S)^*" using rtrancl_mono by blast
    then have "(v1, b') \<in> (rE S)^* \<and> (b', b'') \<in> (rE S)^* \<and> (b'', d) \<in> (rE S)^*" 
          and "(v2, c') \<in> (rE S)^* \<and> (c', c'') \<in> (rE S)^* \<and> (c'', d) \<in> (rE S)^*" using b4 b5 by blast+
    then have e1: "(v1,d) \<in> (rE S)^* \<and> (v2,d) \<in> (rE S)^*" by force
    have "\<And> v v'::'U rD. levrd v = \<l>1 \<longrightarrow> (v,v') \<in> (rE S)^* \<longrightarrow> v \<noteq> v' \<longrightarrow> levrd v' \<noteq> \<l>1"
    proof (intro impI)
      fix v v'::"'U rD"
      assume d1: "levrd v = \<l>1" and d2: "(v,v') \<in> (rE S)^*" and d3: "v \<noteq> v'"
      moreover then obtain k where "(v,v') \<in> (rE S)^^k" using rtrancl_imp_relpow by blast
      ultimately obtain k' where "(v,v') \<in> (rE S)^^(Suc k')" by (cases k, force+)
      then obtain v'' where "(v,v'') \<in> (rE S) \<and> (v'',v') \<in> (rE S)^^k'" by (meson relpow_Suc_D2)
      then have "levrd v'' = \<l>2 \<and> (v'',v') \<in> (rE S)^*" using d1 lem_rE_succ_lev[of v v''] relpow_imp_rtrancl by force
      moreover have "lev_next ` {\<l>2, \<l>3, \<l>4, \<l>5, \<l>6, \<l>7, \<l>8} \<subseteq> {\<l>2, \<l>3, \<l>4, \<l>5, \<l>6, \<l>7, \<l>8}" by simp
      ultimately have "levrd v' \<in> {\<l>2, \<l>3, \<l>4, \<l>5, \<l>6, \<l>7, \<l>8}" using lem_rE_levset_inv[of v'' v' S "{\<l>2, \<l>3, \<l>4, \<l>5, \<l>6, \<l>7, \<l>8}"] by simp
      then show "levrd v' \<noteq> \<l>1" by force
    qed
    then have "(v1,v2) \<notin> (rE S)^*" and "(v2,v1) \<notin> (rE S)^*" using b2 b3 by fastforce+
    then show "levrd d \<in> {\<l>7, \<l>8}" using e1 lem_rE_jn2 by blast
  qed
  then have b9: "\<forall> n \<le> 5. (v1,d) \<notin> (rE S)^^n \<and> (v2,d) \<notin> (rE S)^^n" using b2 b3 lem_rE_l1_l78_dist[of _ d] by simp
  have b10: "levrd b'' = \<l>2"
  proof -
    have c1: "v1 = b' \<or> (v1,b') \<in> (rE S)" using b7 a1 unfolding LD2_def by blast
    then have "levrd b' \<in> {\<l>1, \<l>2}" using b2 lem_rE_succ_lev[of v1 b'] by force
    moreover have c2: "b' = b'' \<or> (b',b'') \<in> (rE S)" using b4 a1 unfolding LD2_def by blast
    ultimately have "levrd b'' \<in> {\<l>1, \<l>2, \<l>3}" using lem_rE_succ_lev[of b' b''] by force
    moreover have "levrd b'' \<in> {\<l>1, \<l>3} \<longrightarrow> False"
    proof
      assume "levrd b'' \<in> {\<l>1, \<l>3}"
      then have "(b'',d) \<in> r0^=" using b4 b6 by blast
      then have d1: "b'' = d \<or> (b'', d) \<in> (rE S)" using a1 unfolding LD2_def by blast
      have "(v1,d) \<in> (rE S)^^0 \<or> (v1,d) \<in> (rE S)^^1 \<or> (v1,d) \<in> (rE S)^^2 \<or> (v1,d) \<in> (rE S)^^3"
        using c1 c2 d1 lem_rel_pow2fw[of _ _ "rE S"] lem_rel_pow3fw[of _ _ "rE S"] by (metis relpow_0_I relpow_1)
      then show "False" using b9
        by (meson le0 numeral_le_iff one_le_numeral semiring_norm(68) semiring_norm(72) semiring_norm(73))
    qed
    ultimately show "levrd b'' = \<l>2" by blast
  qed
  then have "b'' \<noteq> d" using b8 by force
  then obtain t where b11: "(b'',t) \<in> r0 \<and> (t, d) \<in> r0^*" using b4 by (meson converse_rtranclE)
  then have b12: "(b'',t) \<in> (rE S)" using a1 unfolding LD2_def by blast
  then have "levrd t = \<l>3" using b10 a1 lem_rE_succ_lev[of b'' t S] unfolding LD2_def by simp
  then have "(t,d) \<in> r0^=" using b11 b6 by blast
  then have b13: "t = d \<or> (t,d) \<in> (rE S)" using a1 unfolding LD2_def by blast
  have b14: "v1 = b' \<or> (v1,b') \<in> (rE S)" using b7 a1 unfolding LD2_def by blast
  moreover have b15: "b' = b'' \<or> (b',b'') \<in> (rE S)" using b4 a1 unfolding LD2_def by blast
  ultimately have "(v1,b'') \<in> (rE S)^^0 \<or> (v1,b'') \<in> (rE S)^^1 \<or> (v1,b'') \<in> (rE S)^^2"
    using lem_rel_pow2fw[of _ _ "rE S"] by (metis relpow_0_I relpow_1)
  then have "(v1,t) \<in> (rE S)^^1 \<or> (v1,t) \<in> (rE S)^^2 \<or> (v1,t) \<in> (rE S)^^3" using b12 b14 b15
   lem_rel_pow2fw[of _ _ "rE S"] lem_rel_pow3fw[of _ _ "rE S"] by (metis relpow_1)
  moreover have "(v1,t) \<in> (rE S)^^1 \<longrightarrow> (v1,d) \<in> (rE S)^^1 \<or> (v1,d) \<in> (rE S)^^2" using b13 lem_rel_pow2fw by fastforce
  moreover have "(v1,t) \<in> (rE S)^^2 \<longrightarrow> (v1,d) \<in> (rE S)^^2 \<or> (v1,d) \<in> (rE S)^^3" using b13 relpow_Suc_I by fastforce
  moreover have "(v1,t) \<in> (rE S)^^3 \<longrightarrow> (v1,d) \<in> (rE S)^^3 \<or> (v1,d) \<in> (rE S)^^4" using b13 relpow_Suc_I by fastforce
  ultimately have "\<exists> n \<in> {1,2,3,4}. (v1,d) \<in> (rE S)^^n" by blast
  moreover have "\<forall> n \<in> {1,2,3,4}::nat set. n \<le> 5" by simp
  ultimately show "False" using b9 by blast
qed

lemma lem_rE_dominv:
fixes S::"'U set"
assumes "\<not> finite S"
shows "u \<in> Domain (rE S) \<Longrightarrow> (u,v) \<in> (rE S)^* \<Longrightarrow> v \<in> Domain (rE S)"
  using assms lem_rE_domfield unfolding Field_def by (metis Range.RangeI UnCI rtranclE)

lemma lem_rE_next:
fixes S::"'U set"
assumes "\<not> finite S" and "u \<in> Domain (rE S)" 
shows "\<exists> v. (u,v) \<in> (rE S) \<and> v \<in> Domain (rE S) \<and> levrd v = (lev_next (levrd u))"
proof -
  obtain u' where b1: "(u,u') \<in> (rE S)" using assms by blast
  obtain n A B C where b2: "u = (n,A,B,C)" using prod_cases4 by blast
  obtain n' A' B' C' where b3: "u' = (n',A',B',C')" using prod_cases4 by blast
  have b4: "rP n A B C n' A' B' C' \<and> rC S A B C \<and> rC S A' B' C'" using b1 b2 b3 unfolding rE_def by blast
  moreover then have "A \<subseteq> S" unfolding rC_def by blast
  moreover then have b4': "\<exists>A2\<subseteq>S. A \<subset> A2 \<and> finite A2" 
    using b4 assms lem_rP_inv lem_infset_finext[of S A] by metis
  ultimately have "(\<exists> A1 B1 C1 n2 A2 B2 C2. rP n A B C (lev_next n) A1 B1 C1 \<and> rC S A1 B1 C1
                               \<and> rP (lev_next n) A1 B1 C1 n2 A2 B2 C2 \<and> rC S A2 B2 C2)" 
    apply (cases n) 
    unfolding rC_def by auto+
  then obtain A1 B1 C1 n2 A2 B2 C2 where 
    "rP n A B C (lev_next n) A1 B1 C1 \<and> rC S A1 B1 C1 \<and> rP (lev_next n) A1 B1 C1 n2 A2 B2 C2 \<and> rC S A2 B2 C2" by blast
  moreover obtain v where "v = ((lev_next n), A1, B1, C1)" by blast
  ultimately have "(u,v) \<in> (rE S) \<and> v \<in> Domain (rE S) \<and> levrd v = (lev_next (levrd u))"
    using b2 b4 unfolding rE_def by force
  then show ?thesis by blast
qed

lemma lem_rE_reachl8:
fixes S::"'U set"
assumes "\<not> finite S" and "u \<in> Domain (rE S)"
shows "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8"
proof -
  have "levrd u = \<l>8 \<longrightarrow> ?thesis" using assms by blast
  moreover have b0: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>7 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>7"
    moreover then have "(lev_next (levrd u)) = \<l>8" by force
    ultimately obtain v where "(u,v) \<in> (rE S) \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using assms lem_rE_next by metis
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b1: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>6 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>6"
    moreover then have "(lev_next (levrd u)) = \<l>7" by force
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>7" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b0 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force    
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b2: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>5 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>5"
    moreover then have "(lev_next (levrd u)) = \<l>6" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>6" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b1 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b3: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>4 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>4"
    moreover then have "(lev_next (levrd u)) = \<l>5" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>5" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b2 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b4: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>3 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>3"
    moreover then have "(lev_next (levrd u)) = \<l>4" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>4" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b3 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b5: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>2 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>2"
    moreover then have "(lev_next (levrd u)) = \<l>3" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>3" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b4 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b6: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>1 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>1"
    moreover then have "(lev_next (levrd u)) = \<l>2" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>2" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b5 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  moreover have b7: "\<And> u::'U rD. u \<in> Domain (rE S) \<Longrightarrow> levrd u = \<l>0 \<Longrightarrow> (\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8)"
  proof -
    fix u::"'U rD"
    assume "u \<in> Domain (rE S)" and "levrd u = \<l>0"
    moreover then have "(lev_next (levrd u)) = \<l>1" by simp
    ultimately obtain v' where "(u,v') \<in> (rE S) \<and> v' \<in> Domain (rE S) \<and> levrd v' = \<l>1" using assms lem_rE_next by metis
    moreover then obtain v where "(v',v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" using b6 by blast
    ultimately have "(u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by force
    then show "\<exists> v. (u,v) \<in> (rE S)^* \<and> v \<in> Domain (rE S) \<and> levrd v = \<l>8" by blast
  qed
  ultimately show ?thesis using assms by (meson lev_next.cases)
qed

lemma lem_rE_jn:
fixes S::"'U set"
assumes a0: "\<not> finite S" and a1: "u1 \<in> Domain (rE S)" and a2: "u2 \<in> Domain (rE S)"
shows "\<exists> t. (u1,t) \<in> (rE S)^* \<and> (u2,t) \<in> (rE S)^*"
proof -
  obtain v1 where b1: "(u1,v1) \<in> (rE S)^*" and b2: "v1 \<in> Domain (rE S) \<and> levrd v1 = \<l>8" using a0 a1 lem_rE_reachl8 by blast
  obtain v2 where b3: "(u2,v2) \<in> (rE S)^*" and b4: "v2 \<in> Domain (rE S) \<and> levrd v2 = \<l>8" using a0 a2 lem_rE_reachl8 by blast
  obtain n1 A1 B1 C1 where b5: "v1 = (n1,A1,B1,C1)" using prod_cases4 by blast
  obtain n2 A2 B2 C2 where b6: "v2 = (n2,A2,B2,C2)" using prod_cases4 by blast
  have b7: "n1 = \<l>8 \<and> A1 = B1 \<and> A1 = C1 \<and> finite A1 \<and> A1 \<subseteq> S" using b5 b2 unfolding rE_def rC_def by force
  have b8: "n2 = \<l>8 \<and> A2 = B2 \<and> A2 = C2 \<and> finite A2 \<and> A2 \<subseteq> S" using b6 b4 unfolding rE_def rC_def by force 
  have "finite (A1 \<union> A2) \<and> A1 \<union> A2 \<subseteq> S" using b7 b8 by blast
  then obtain A3 where "A3 \<subseteq> S \<and> A1 \<union> A2 \<subset> A3 \<and> finite A3" using a0 lem_infset_finext[of S "A1 \<union> A2"] by blast
  moreover obtain t where "t = (\<l>7, A3, A3, A3)" by blast
  ultimately have "(v1, t) \<in> (rE S) \<and> (v2, t) \<in> (rE S)" using b5 b6 b7 b8 unfolding rE_def rC_def by force
  then have "(u1,t) \<in> (rE S)^* \<and> (u2,t) \<in> (rE S)^*" using b1 b3 by force
  then show ?thesis by blast
qed

lemma lem_rE_confl:
fixes S::"'U set"
assumes "\<not> finite S"
shows "confl_rel (rE S)"
proof -
  have "\<forall> a b c::'U rD. (a,b) \<in> (rE S)^* \<longrightarrow> (a,c) \<in> (rE S)^* \<longrightarrow> (\<exists> d. (b,d) \<in> (rE S)^* \<and> (c,d) \<in> (rE S)^*)"
  proof (intro allI impI)
    fix a b c::"'U rD"
    assume c1: "(a,b) \<in> (rE S)^*" and c2: "(a,c) \<in> (rE S)^*"
    show "\<exists> d. (b,d) \<in> (rE S)^* \<and> (c,d) \<in> (rE S)^*"
    proof (cases "a \<in> Domain (rE S)")
      assume "a \<in> Domain (rE S)"
      then have "b \<in> Domain (rE S) \<and> c \<in> Domain (rE S)" using c1 c2 assms lem_rE_dominv by blast
      then obtain d where "(b,d) \<in> (rE S)^* \<and> (c,d) \<in> (rE S)^*" using assms lem_rE_jn by blast
      then show ?thesis by blast
    next
      assume "a \<notin> Domain (rE S)"
      then have "a = b \<and> a = c" using c1 c2 by (meson Not_Domain_rtrancl)
      then show ?thesis by blast
    qed
  qed
  then show ?thesis unfolding confl_rel_def by blast
qed

lemma lem_rE_dc3dc2:
fixes S::"'U set"
assumes "\<not> |S| \<le>o |UNIV::nat set|"
shows "confl_rel (rE S) \<and> (\<not> DCR2 (rE S))"
proof (intro conjI)
  have "\<not> finite S" using assms by (meson card_of_Well_order infinite_iff_card_of_nat ordLeq_total)
  then show "confl_rel (rE S)" using lem_rE_confl by blast
next
  show "\<not> DCR2 (rE S)" using assms lem_rE_notLD2 unfolding DCR2_def by blast
qed

lemma lem_rE_cardbnd:
fixes S::"'U set"
assumes "\<not> finite S"
shows "|rE S| \<le>o |S|"
proof -
  obtain L where b1: "L = (UNIV::Lev set)" by blast
  obtain F where b2: "F = { A. A \<subseteq> S \<and> finite A }" by blast
  obtain D where b3: "D = (L \<times> (F \<times> (F \<times> F)))" by blast
  have "\<forall> u v. (u,v) \<in> rE S \<longrightarrow> u \<in> D \<and> v \<in> D"
  proof (intro allI impI)
    fix u v
    assume "(u,v) \<in> rE S"
    then obtain n A B C n' A' B' C' 
      where "u = (n,A,B,C) \<and> v = (n',A',B',C') \<and> rC S A B C \<and> rC S A' B' C'
        \<and> rP n A B C n' A' B' C'" unfolding rE_def by blast
    moreover then have "n \<in> L \<and> A \<in> F \<and> B \<in> F \<and> C \<in> F \<and> n' \<in> L \<and> A' \<in> F \<and> B' \<in> F \<and> C' \<in> F" 
      using b1 b2 lem_rP_inv unfolding rC_def by fast
    ultimately show "u \<in> D \<and> v \<in> D" using b3 by blast
  qed
  then have "rE S \<subseteq> D \<times> D" by force
  then have "|rE S| \<le>o |D \<times> D|" by simp
  moreover have "|D \<times> D| \<le>o |S|"
  proof -
    have "F = Fpow S" using b2 unfolding Fpow_def by simp
    then have c1: "|F| =o |S|" using assms by simp
    then have "|F \<times> F| =o |F| \<and> \<not> finite F" using assms by simp
    then have "|F| \<le>o |F| \<and> |F \<times> F| \<le>o |F| \<and> \<not> finite F" using ordIso_iff_ordLeq by force
    then have c2: "|F \<times> (F \<times> F)| \<le>o |S|" using c1 card_of_Times_ordLeq_infinite ordLeq_ordIso_trans by blast
    have "L \<subseteq> {\<l>0,\<l>1,\<l>2,\<l>3,\<l>4,\<l>5,\<l>6,\<l>7,\<l>8}"
    proof
      fix l
      assume "l \<in> L"
      show "l \<in> {\<l>0,\<l>1,\<l>2,\<l>3,\<l>4,\<l>5,\<l>6,\<l>7,\<l>8}" by (cases l, simp+)
    qed
    moreover have "finite {\<l>0,\<l>1,\<l>2,\<l>3,\<l>4,\<l>5,\<l>6,\<l>7,\<l>8}" by simp
    ultimately have "finite L" using finite_subset by blast
    then have "|L| \<le>o |S|" using assms ordLess_imp_ordLeq by force
    then have "|D| \<le>o |S|" using b3 c2 assms card_of_Times_ordLeq_infinite by blast
    then show ?thesis using assms card_of_Times_ordLeq_infinite by blast
  qed
  ultimately show "|rE S| \<le>o |S|" using ordLeq_transitive by blast
qed

lemma lem_fmap_rel:
fixes f r s a0 b0
assumes a1: "(a0, b0) \<in> r^*" and a2: "\<forall> a b. (a,b) \<in> r \<longrightarrow> (f a, f b) \<in> s"
shows "(f a0, f b0) \<in> s^*"
proof -
  have "\<And> n. \<forall> a b. (a,b) \<in> r^^n \<longrightarrow> (f a, f b) \<in> s^*"
  proof -
    fix n0
    show "\<forall> a b. (a,b) \<in> r^^n0 \<longrightarrow> (f a, f b) \<in> s^*"
    proof (induct n0)
      show "\<forall> a b. (a,b) \<in> r^^0 \<longrightarrow> (f a, f b) \<in> s^*" by simp
    next
      fix n
      assume "\<forall> a b. (a,b) \<in> r^^n \<longrightarrow> (f a, f b) \<in> s^*"
      then show "\<forall> a b. (a,b) \<in> r^^(Suc n) \<longrightarrow> (f a, f b) \<in> s^*" using a2 by force
    qed
  qed
  then show ?thesis using a1 rtrancl_power by blast
qed

lemma lem_fmap_confl:
fixes r::"'a rel" and f::"'a \<Rightarrow> 'b"
assumes a1: "inj_on f (Field r)" and a2: "confl_rel r"
shows "confl_rel {(u,v). \<exists> a b. u = f a \<and> v = f b \<and> (a,b) \<in> r}"
proof -
  obtain rA where q1: "rA = {(u,v). \<exists> a b. u = f a \<and> v = f b \<and> (a,b) \<in> r}" by blast
  then have q2: "\<forall>a b. (a, b) \<in> r \<longrightarrow> (f a, f b) \<in> rA" by blast
  have q3: "Field rA \<subseteq> f`(Field r)" using q1 unfolding Field_def by blast
  obtain g where q4: "g = inv_into (Field r) f" by blast
  then have q5: "\<forall> x \<in> Field r. g (f x) = x" using a1 by simp
  have q6: "\<forall> u v. (u,v) \<in> rA \<longrightarrow> (g u, g v) \<in> r"
  proof (intro allI impI)
    fix u v
    assume "(u,v) \<in> rA"
    then obtain a b where "u = f a \<and> v = f b \<and> (a,b) \<in> r" using q1 by blast
    moreover then have "a \<in> Field r \<and> b \<in> Field r" unfolding Field_def by blast
    ultimately show "(g u, g v) \<in> r" using q5 by force
  qed
  have "\<forall>u \<in> Field rA. \<forall> v \<in> Field rA. \<forall> w \<in> Field rA. 
    (u,v) \<in> rA^* \<and> (u,w) \<in> rA^* \<longrightarrow> (\<exists> t \<in> Field rA. (v,t) \<in> rA^* \<and> (w,t) \<in> rA^*)"
  proof (intro ballI impI)
    fix u v w
    assume c1: "u \<in> Field rA" and c2: "v \<in> Field rA" and c3: "w \<in> Field rA" 
       and c4: "(u,v) \<in> rA^* \<and> (u,w) \<in> rA^*"
    then have "(g u, g v) \<in> r^* \<and> (g u, g w) \<in> r^*" using q6 lem_fmap_rel[of u _ rA g r] by blast
    then obtain d where c5: "(g v, d) \<in> r^* \<and> (g w, d) \<in> r^*" using a2 unfolding confl_rel_def by blast
    moreover have c6: "g v \<in> Field r \<and> g w \<in> Field r" using c2 c3 q3 q5 by force
    ultimately have "d \<in> Field r" using lem_rtr_field by fastforce
    have "v = f (g v) \<and> w = f (g w)" using c2 c3 q3 q4 a1 by force
    moreover have "(f (g v), f d) \<in> rA^* \<and> (f (g w), f d) \<in> rA^*" 
      using c5 q2 lem_fmap_rel[of _ d r f rA] by blast
    ultimately have "(v, f d) \<in> rA^* \<and> (w, f d) \<in> rA^*" by simp
    moreover then have "f d \<in> Field rA" using c2 lem_rtr_field by fastforce
    ultimately show "\<exists> t \<in> Field rA. (v,t) \<in> rA^* \<and> (w,t) \<in> rA^*" by blast
  qed
  then show ?thesis using q1 lem_confl_field by blast
qed

lemma lem_fmap_dcn:
fixes r::"'a rel" and f::"'a \<Rightarrow> 'b"
assumes a1: "inj_on f (Field r)" and a2: "DCR n r"
shows "DCR n {(u,v). \<exists> a b. u = f a \<and> v = f b \<and> (a,b) \<in> r}"
proof -
  obtain rA where q1: "rA = {(u,v). \<exists> a b. u = f a \<and> v = f b \<and> (a,b) \<in> r}" by blast
  have q2: "\<forall> a \<in> Field r. \<forall> b \<in> Field r. (a,b) \<in> r \<longleftrightarrow> (f a, f b) \<in> rA" 
    using a1 q1 unfolding Field_def inj_on_def by blast
  have q3: "Field rA \<subseteq> f`(Field r)" using q1 unfolding Field_def by blast  
  obtain g::"nat \<Rightarrow> 'a rel" where b1: "DCR_generating g" 
         and b2: "r = \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = g \<alpha>' }" using a2 unfolding DCR_def by blast
  obtain gA::"nat \<Rightarrow> 'b rel" 
    where b3: "gA = (\<lambda> \<alpha>. if \<alpha> < n then {(x,y). \<exists> a b. x = f a \<and> y = f b \<and> (a,b) \<in> g \<alpha> } else {})" by blast
  have "\<forall>\<alpha> \<beta> u v w. (u, v) \<in> gA \<alpha> \<and> (u, w) \<in> gA \<beta> \<longrightarrow>
       (\<exists>v' v'' w' w'' e. (v, v', v'', e) \<in> \<DD> gA \<alpha> \<beta> \<and> (w, w', w'', e) \<in> \<DD> gA \<beta> \<alpha>)"
  proof (intro allI impI)
    fix \<alpha> \<beta> u v w
    assume c1: "(u, v) \<in> gA \<alpha> \<and> (u, w) \<in> gA \<beta>"
    obtain a b where c2: "\<alpha> < n \<and> u = f a \<and> v = f b \<and> (a,b) \<in> g \<alpha>" using c1 b3 by (cases "\<alpha> < n", force+)
    obtain a' c where c3: "\<beta> < n \<and> u = f a' \<and> w = f c \<and> (a',c) \<in> g \<beta>" using c1 b3 by (cases "\<beta> < n", force+)
    have "(a,b) \<in> r \<and> (a',c) \<in> r" using c2 c3 b2 by blast
    then have "a' = a" using c2 c3 a1 unfolding inj_on_def Field_def by blast
    then have "(a,b) \<in> g \<alpha> \<and> (a,c) \<in> g \<beta>" using c2 c3 by blast
    then obtain b' b'' c' c'' d where c4: "(b, b', b'', d) \<in> \<DD> g \<alpha> \<beta> \<and> (c, c', c'', d) \<in> \<DD> g \<beta> \<alpha>" 
      using b1 unfolding DCR_generating_def by blast
    have c5: "\<And> \<alpha>'. \<alpha>' < n \<Longrightarrow> \<forall> a0 b0. (a0,b0) \<in> \<LL>1 g \<alpha>' \<longrightarrow> (f a0, f b0) \<in> \<LL>1 gA \<alpha>'"
    proof (intro allI impI)
      fix \<alpha>' a0 b0
      assume d1: "\<alpha>' < n" and "(a0,b0) \<in> \<LL>1 g \<alpha>'"
      then obtain \<alpha>'' where "(a0,b0) \<in> g \<alpha>'' \<and> \<alpha>'' < \<alpha>'" unfolding \<LL>1_def by blast
      moreover then have "(f a0, f b0) \<in> gA \<alpha>''" using d1 c2 b3 by force
      ultimately show "(f a0, f b0) \<in> \<LL>1 gA \<alpha>'" using c2 b3 unfolding \<LL>1_def by blast
    qed
    have c6: "\<And> \<alpha>' a0 b0. \<alpha>' < n \<Longrightarrow> (a0,b0) \<in> (g \<alpha>')^= \<longrightarrow> (f a0, f b0) \<in> (gA \<alpha>')^=" using b3 by force
    have c7: "\<And> \<alpha>' \<beta>'. \<alpha>' < n \<Longrightarrow> \<beta>' < n \<Longrightarrow> \<forall> a0 b0. (a0,b0) \<in> \<LL>v g \<alpha>' \<beta>' \<longrightarrow> (f a0, f b0) \<in> \<LL>v gA \<alpha>' \<beta>'"
    proof (intro allI impI)
      fix \<alpha>' \<beta>' a0 b0
      assume d1: "\<alpha>' < n" and d2: "\<beta>' < n" and "(a0,b0) \<in> \<LL>v g \<alpha>' \<beta>'"
      then obtain \<alpha>'' where "(a0,b0) \<in> g \<alpha>'' \<and> (\<alpha>'' < \<alpha>' \<or> \<alpha>'' < \<beta>')" unfolding \<LL>v_def by blast
      moreover then have "(f a0, f b0) \<in> gA \<alpha>''" using d1 d2 c2 b3 by force
      ultimately show "(f a0, f b0) \<in> \<LL>v gA \<alpha>' \<beta>'" using c2 b3 unfolding \<LL>v_def by blast
    qed
    have "(v, f b') \<in> (\<LL>1 gA \<alpha>)^*" using c2 c4 c5[of \<alpha>] lem_fmap_rel[of b b'] unfolding \<DD>_def by blast
    moreover have "(f b', f b'') \<in> (gA \<beta>)^=" using c3 c4 c6 unfolding \<DD>_def by blast
    moreover have "(f b'', f d) \<in> (\<LL>v gA \<alpha> \<beta>)^*" using c2 c3 c4 c7[of \<alpha> \<beta>] lem_fmap_rel[of b'' d] unfolding \<DD>_def by blast
    moreover have "(w, f c') \<in> (\<LL>1 gA \<beta>)^*" using c3 c4 c5[of \<beta>] lem_fmap_rel[of c c'] unfolding \<DD>_def by blast
    moreover have "(f c', f c'') \<in> (gA \<alpha>)^=" using c2 c4 c6 unfolding \<DD>_def by blast
    moreover have "(f c'', f d) \<in> (\<LL>v gA \<beta> \<alpha>)^*" using c2 c3 c4 c7[of \<beta> \<alpha>] lem_fmap_rel[of c'' d] unfolding \<DD>_def by blast
    ultimately show "\<exists>v' v'' w' w'' e. (v, v', v'', e) \<in> \<DD> gA \<alpha> \<beta> \<and> (w, w', w'', e) \<in> \<DD> gA \<beta> \<alpha>"
      unfolding \<DD>_def by blast
  qed
  then have "DCR_generating gA" unfolding DCR_generating_def by blast
  moreover have "rA = \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = gA \<alpha>'}"
  proof
    show "rA \<subseteq> \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = gA \<alpha>'}"
    proof
      fix p
      assume "p \<in> rA"
      then obtain x y where d1: "p = (x,y) \<and> p \<in> rA" by force
      moreover then obtain a b where d2: "x = f a \<and> y = f b \<and> a \<in> Field r \<and> b \<in> Field r" 
        using q3 unfolding Field_def by blast
      ultimately have "(a,b) \<in> r" using q2 by blast
      then obtain \<alpha>' where "\<alpha>' < n \<and> (a,b) \<in> g \<alpha>'" using b2 by blast
      then have "\<alpha>' < n \<and> (x,y) \<in> gA \<alpha>'" using d2 b3 by force
      then show "p \<in> \<Union>{r'. \<exists>\<alpha>'<n. r' = gA \<alpha>'}" using d1 by blast
    qed
  next
    show "\<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = gA \<alpha>'} \<subseteq> rA"
    proof
      fix p
      assume "p \<in> \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = gA \<alpha>'}"
      then obtain \<alpha>' where d1: "\<alpha>' < n \<and> p \<in> gA \<alpha>'" by blast
      then obtain x y where d2: "p = (x,y) \<and> p \<in> gA \<alpha>'" by force
      then obtain a b where "x = f a \<and> y = f b \<and> (a,b) \<in> g \<alpha>'" using d1 b3 by force
      moreover then have "(a,b) \<in> r" using d1 b2 by blast
      ultimately show "p \<in> rA" using d2 q2 unfolding Field_def by blast
    qed
  qed
  ultimately have "DCR n rA" unfolding DCR_def by blast
  then show ?thesis using q1 by blast
qed

lemma lem_not_dcr2: 
assumes "cardSuc |UNIV::nat set| \<le>o |UNIV::'U set|"
shows "\<exists> r::'U rel. confl_rel r \<and> |r| \<le>o cardSuc |UNIV::nat set| \<and> (\<not> DCR2 r)"
proof -
  obtain A where b1: "A = (UNIV::'U set)" by blast
  obtain S where b2: "S \<subseteq> A \<and> |S| =o cardSuc |UNIV::nat set|"
    using b1 assms
      by (smt Card_order_ordIso2 Field_card_of cardSuc_Card_order card_of_Field_ordIso 
          card_of_card_order_on internalize_ordLeq ordIso_symmetric ordIso_transitive)
  then have "\<not> ( |S| \<le>o |UNIV::nat set| )" by (simp add: cardSuc_ordLess_ordLeq ordIso_iff_ordLeq)
  moreover then have "\<not> finite S" by (meson card_of_Well_order infinite_iff_card_of_nat ordLeq_total)
  moreover obtain s where b3: "s = (rE S)" by blast
  ultimately have b4: "confl_rel s \<and> \<not> DCR2 s \<and> |s| \<le>o |S|" using lem_rE_dc3dc2 lem_rE_cardbnd by blast
  obtain B where b5: "B = Field s" by blast
  obtain C::"'U set" where b6: "C = UNIV" by blast
  then have "cardSuc |UNIV::nat set| \<le>o |C|" using assms by blast
  moreover have b6': "|s| \<le>o cardSuc |UNIV::nat set|" using b2 b4 ordLeq_ordIso_trans by blast
  ultimately have "|s| \<le>o |C|" using ordLeq_transitive by blast
  moreover have b6'': "\<not> finite (Field s) \<longrightarrow> |Field s| =o |s|" using lem_fin_fl_rel lem_rel_inf_fld_card by blast
  ultimately have "\<not> finite (Field s) \<longrightarrow> |Field s| \<le>o |C|" using ordIso_ordLeq_trans by blast
  moreover have "\<not> finite C" using b6 assms ordLeq_finite_Field by fastforce
  moreover then have "finite (Field s) \<longrightarrow> |Field s| \<le>o |C|" using ordLess_imp_ordLeq by force
  ultimately have "|B| \<le>o |C|" using b5 by blast
  then obtain f where b7: "f`B \<subseteq> C \<and> inj_on f B" by (meson card_of_ordLeq) 
  moreover obtain g where b8: "g = inv_into B f" by blast
  ultimately have b9: "\<forall> x \<in> B. g (f x) = x" by simp
  obtain r where b10: "r = {(a,b). \<exists> x y. a = f x \<and> b = f y \<and> (x,y) \<in> s}" by blast
  have "s \<subseteq> {(x,y). \<exists> a b. x = g a \<and> y = g b \<and> (a,b) \<in> r}"
  proof
    fix p
    assume "p \<in> s"
    then obtain x y where "p = (x,y) \<and> (x,y) \<in> s" by (cases p, blast)
    moreover then have "(f x, f y) \<in> r \<and> x \<in> B \<and> y \<in> B" using b5 b10 unfolding Field_def by blast
    moreover then have "x = g (f x) \<and> y = g (f y)" using b9 by simp
    ultimately show "p \<in> {(x,y). \<exists> a b. x = g a \<and> y = g b \<and> (a,b) \<in> r}" using b9 by blast
  qed
  moreover have "{(x,y). \<exists> a b. x = g a \<and> y = g b \<and> (a,b) \<in> r} \<subseteq> s"
  proof
    fix p
    assume "p \<in> {(x,y). \<exists> a b. x = g a \<and> y = g b \<and> (a,b) \<in> r}"
    then obtain a b where "p = (g a, g b) \<and> (a,b) \<in> r" by blast
    moreover then obtain x y where "a = f x \<and> b = f y \<and> (x,y) \<in> s" using b10 by blast
    moreover then have "x \<in> B \<and> y \<in> B" using b5 unfolding Field_def by blast
    ultimately show "p \<in> s" using b9 by force
  qed
  ultimately have b11: "s = {(x,y). \<exists> a b. x = g a \<and> y = g b \<and> (a,b) \<in> r}" by blast
  have "inj_on g (f`B)" using b8 inj_on_inv_into[of "f`B" f B] by blast
  moreover have b12: "Field r \<subseteq> f`B" 
  proof
    fix c
    assume "c \<in> Field r"
    then obtain a b where "(a,b) \<in> r \<and> (c = a \<or> c = b)" unfolding Field_def by blast
    moreover then obtain x y where "a = f x \<and> b = f y \<and> (x,y) \<in> s" using b10 by blast
    moreover then have "x \<in> B \<and> y \<in> B" using b5 unfolding Field_def by blast
    ultimately show "c \<in> f ` B" by blast
  qed
  ultimately have "inj_on g (Field r)" using Fun.subset_inj_on by blast
  moreover have "\<not> DCR 2 s" using b4 lem_dc2_to_d2 by blast
  ultimately have "\<not> DCR 2 r" using b11 lem_fmap_dcn[of g r 2] by blast
  then have "\<not> DCR2 r" using lem_d2_to_dc2 by blast
  moreover have "confl_rel r" using b4 b5 b7 b10 lem_fmap_confl[of f s] by blast
  moreover have "|r| \<le>o cardSuc |UNIV::nat set|"
  proof -
    have "finite (Field s) \<longrightarrow> |B| \<le>o cardSuc |UNIV::nat set|" using b2 b5 
      by (metis Field_card_of cardSuc_greater card_of_card_order_on finite_ordLess_infinite2 
          infinite_UNIV_nat ordLeq_transitive ordLess_imp_ordLeq) 
    moreover have "\<not> finite (Field s) \<longrightarrow> |B| \<le>o cardSuc |UNIV::nat set|" 
      using b5 b6' b6'' ordIso_ordLeq_trans by blast
    ultimately have "|B| \<le>o cardSuc |UNIV::nat set|" by blast
    moreover have "|f`B| \<le>o |B|" by simp
    moreover have "|Field r| \<le>o |f`B|" using b12 by simp
    ultimately have "|Field r| \<le>o cardSuc |UNIV::nat set|" using ordLeq_transitive by metis
    then have "\<not> finite r \<longrightarrow> |r| \<le>o cardSuc |UNIV::nat set|" 
      using lem_rel_inf_fld_card[of r] ordIso_ordLeq_trans ordIso_symmetric by blast
    moreover have "finite r \<longrightarrow> |r| \<le>o cardSuc |UNIV::nat set|" by (simp add: ordLess_imp_ordLeq)
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

(* ----------------------------------------------------------------------- *)

subsubsection \<open>Result\<close>

(* ----------------------------------------------------------------------- *)

text \<open>The next theorem has the following meaning:
  if the set of elements of type \<open>'U\<close> is uncountable,
  then there exists a confluent binary relation $r$ on \<open>'U\<close>
  such that the cardinality of $r$ does not exceed the first uncountable cardinal
  and confluence of $r$ cannot be proved using the decreasing diagrams method with 2 labels.\<close>

theorem thm_example_not_dcr2: 
assumes "cardSuc |{n::nat. True}| \<le>o |{x::'U. True}|"
shows "\<exists> r::'U rel. ( 
            ( \<forall>a b c. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> (\<exists> d. (b,d) \<in> r^* \<and> (c,d) \<in> r^*) ) 
          \<and> |r| \<le>o cardSuc |{n::nat. True}| 
          \<and> (\<not> ( \<exists>r0 r1. (  
                ( r = (r0 \<union> r1) )
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0  
                   \<longrightarrow> (\<exists> d. 
                          (b,d) \<in> r0^= 
                        \<and> (c,d) \<in> r0^=) )
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r1  
                   \<longrightarrow> (\<exists>b' d. 
                          (b,b') \<in> r1^= \<and> (b',d) \<in> r0^* 
                        \<and> (c,d) \<in> r0^*) )
              \<and> (\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r1  
                   \<longrightarrow> (\<exists>b' b'' c' c'' d.  
                          (b,b') \<in> r0^* \<and> (b',b'') \<in> r1^= \<and> (b'',d) \<in> r0^* 
                        \<and> (c,c') \<in> r0^* \<and> (c',c'') \<in> r1^= \<and> (c'',d) \<in> r0^*) ) ) )
            ) )"
proof -
  have "cardSuc |UNIV::nat set| \<le>o |UNIV::'U set|" using assms by (simp only: UNIV_def)
  then have "\<exists> r::'U rel. confl_rel r \<and> |r| \<le>o cardSuc |UNIV::nat set| \<and> (\<not> DCR2 r)" 
    using assms lem_not_dcr2 by blast
  then show ?thesis unfolding confl_rel_def DCR2_def LD2_def jn00_def jn01_def jn11_def
    by (simp only: UNIV_def) 
qed

corollary cor_example_not_dcr2:
shows "\<exists> r::(nat set) rel. ( 
            ( \<forall>a b c. (a,b) \<in> r^* \<and> (a,c) \<in> r^* \<longrightarrow> (\<exists> d. (b,d) \<in> r^* \<and> (c,d) \<in> r^*) ) 
          \<and> |r| \<le>o cardSuc |{n::nat. True}| 
          \<and> (\<not> ( \<exists>r0 r1. (  
                ( r = (r0 \<union> r1) )
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r0  
                   \<longrightarrow> (\<exists> d. 
                          (b,d) \<in> r0^= 
                        \<and> (c,d) \<in> r0^=) )
              \<and> (\<forall> a b c. (a,b) \<in> r0 \<and> (a,c) \<in> r1  
                   \<longrightarrow> (\<exists>b' d. 
                          (b,b') \<in> r1^= \<and> (b',d) \<in> r0^* 
                        \<and> (c,d) \<in> r0^*) )
              \<and> (\<forall> a b c. (a,b) \<in> r1 \<and> (a,c) \<in> r1  
                   \<longrightarrow> (\<exists>b' b'' c' c'' d.  
                          (b,b') \<in> r0^* \<and> (b',b'') \<in> r1^= \<and> (b'',d) \<in> r0^* 
                        \<and> (c,c') \<in> r0^* \<and> (c',c'') \<in> r1^= \<and> (c'',d) \<in> r0^*) ) ) )
            ) )"
proof -
  have "cardSuc |{x::nat. True}| \<le>o |{x::nat set. True}|" by force
  then show ?thesis using thm_example_not_dcr2 by blast
qed

end
