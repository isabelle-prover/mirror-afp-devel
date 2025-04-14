(*     License:    LGPL  *)

subsection \<open>DCR implies LD Property\<close>

theory Main_Result_DCR_N1
  imports 
    DCR3_Method
    "Decreasing-Diagrams.Decreasing_Diagrams"
begin

(* ----------------------------------------------------------------------- *)

subsubsection \<open>Auxiliary definitions\<close>

(* ----------------------------------------------------------------------- *)

definition map_seq_labels :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a,'b) seq \<Rightarrow> ('a,'c) seq"
where
  "map_seq_labels f \<sigma> = (fst \<sigma>, map (\<lambda>(\<alpha>,a). (f \<alpha>, a)) (snd \<sigma>))"

fun map_diag_labels :: "('b \<Rightarrow> 'c) \<Rightarrow> 
   ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<Rightarrow> 
   ('a,'c) seq \<times> ('a,'c) seq \<times> ('a,'c) seq \<times> ('a,'c) seq"
where
  "map_diag_labels f (\<tau>,\<sigma>,\<sigma>',\<tau>') = ((map_seq_labels f \<tau>), (map_seq_labels f \<sigma>), (map_seq_labels f \<sigma>'), (map_seq_labels f \<tau>'))"
  
fun f_to_ls :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "f_to_ls f 0 = []"
| "f_to_ls f (Suc n) = (f_to_ls f n) @ [(f n)]"

(* ---------------------------------------------------------------------------------------------------- *)

subsubsection \<open>Auxiliary lemmas\<close>

lemma lem_ftofs_len: "length (f_to_ls f n) = n" by (induct n, simp+)

lemma lem_irr_inj_im_irr:
fixes r::"'a rel" and r'::"'b rel" and f::"'a \<Rightarrow> 'b"
assumes "irrefl r" and "inj_on f (Field r)"
    and "r' = {(a',b'). \<exists> a b. a' = f a \<and> b' = f b \<and> (a,b) \<in> r}"
shows "irrefl r'"
  using assms unfolding inj_on_def Field_def irrefl_def by blast

lemma lem_tr_inj_im_tr:
fixes r::"'a rel" and r'::"'b rel" and f::"'a \<Rightarrow> 'b"
assumes "trans r" and "inj_on f (Field r)"
    and "r' = {(a',b'). \<exists> a b. a' = f a \<and> b' = f b \<and> (a,b) \<in> r}"
shows "trans r'"
  using assms unfolding inj_on_def Field_def trans_def by blast

lemma lem_lpeak_expr: "local_peak lrs (\<tau>, \<sigma>) = (\<exists> a b c \<alpha> \<beta>. (a,\<alpha>,b) \<in> lrs \<and> (a,\<beta>,c) \<in> lrs \<and> \<tau> = (a,[(\<alpha>,b)]) \<and> \<sigma> = (a,[(\<beta>,c)]))"
proof
  assume "local_peak lrs (\<tau>, \<sigma>)"
  then show "\<exists> a b c \<alpha> \<beta>. (a,\<alpha>,b) \<in> lrs \<and> (a,\<beta>,c) \<in> lrs \<and> \<tau> = (a,[(\<alpha>,b)]) \<and> \<sigma> = (a,[(\<beta>,c)])"
    unfolding Decreasing_Diagrams.local_peak_def Decreasing_Diagrams.peak_def
    apply(cases \<tau>, cases \<sigma>, simp) 
    using Decreasing_Diagrams.seq_tail1(2)
    by (metis (no_types, lifting) Suc_length_conv length_0_conv prod.collapse)
next
  assume "\<exists> a b c \<alpha> \<beta>. (a,\<alpha>,b) \<in> lrs \<and> (a,\<beta>,c) \<in> lrs \<and> \<tau> = (a,[(\<alpha>,b)]) \<and> \<sigma> = (a,[(\<beta>,c)])"
  then obtain a b c \<alpha> \<beta> where "(a,\<alpha>,b) \<in> lrs \<and> (a,\<beta>,c) \<in> lrs \<and> \<tau> = (a,[(\<alpha>,b)]) \<and> \<sigma> = (a,[(\<beta>,c)])" by blast
  then show "local_peak lrs (\<tau>, \<sigma>)"
    unfolding Decreasing_Diagrams.local_peak_def Decreasing_Diagrams.peak_def
    by (simp add: Decreasing_Diagrams.seq.intros)
qed

lemma lem_map_seq:
fixes lrs::"('a,'b) lars" and f::"'b \<Rightarrow> 'c" and lrs'::"('a,'c) lars" and \<sigma>::"('a,'b) seq"
assumes a1: "lrs' = {(a,l',b). \<exists>l. l' = f l \<and> (a,l,b) \<in> lrs }" 
    and a2: "\<sigma> \<in> Decreasing_Diagrams.seq lrs"
shows "(map_seq_labels f \<sigma>) \<in> Decreasing_Diagrams.seq lrs'"
proof -
  have "\<forall> s a. (a,s) \<in> Decreasing_Diagrams.seq lrs \<longrightarrow> (map_seq_labels f (a,s)) \<in> Decreasing_Diagrams.seq lrs'"
  proof
    fix s
    show "\<forall> a. (a,s) \<in> Decreasing_Diagrams.seq lrs \<longrightarrow> (map_seq_labels f (a,s)) \<in> Decreasing_Diagrams.seq lrs'"
    proof (induct s)
      show "\<forall>a. (a, []) \<in> Decreasing_Diagrams.seq lrs \<longrightarrow> map_seq_labels f (a, []) \<in> Decreasing_Diagrams.seq lrs'"
        unfolding map_seq_labels_def by (simp add: seq.intros(1))
    next
      fix p s1
      assume d1: "\<forall>b. (b, s1) \<in> Decreasing_Diagrams.seq lrs \<longrightarrow> map_seq_labels f (b, s1) \<in> Decreasing_Diagrams.seq lrs'"
      show "\<forall>b. (b, p # s1) \<in> Decreasing_Diagrams.seq lrs \<longrightarrow> map_seq_labels f (b, p # s1) \<in> Decreasing_Diagrams.seq lrs'"
      proof (intro allI impI)
        fix b
        assume e1: "(b, p # s1) \<in> Decreasing_Diagrams.seq lrs"
        moreover obtain l b' where e2: "p = (l, b')" by force
        ultimately have e3: "(b,l,b') \<in> lrs \<and> (b',s1) \<in> Decreasing_Diagrams.seq lrs"
          by (metis Decreasing_Diagrams.seq_tail1(1) Decreasing_Diagrams.seq_tail1(2) prod.collapse snd_conv)
        then have "(b,f l,b') \<in> lrs'" using a1 by blast
        moreover have "map_seq_labels f (b', s1) \<in> Decreasing_Diagrams.seq lrs'" using d1 e3 by blast
        ultimately show "map_seq_labels f (b, p # s1) \<in> Decreasing_Diagrams.seq lrs'"
          using e2 unfolding map_seq_labels_def by (simp add: seq.intros(2))
      qed
    qed
  qed
  moreover obtain a s where "\<sigma> = (a,s)" by force
  ultimately show "(map_seq_labels f \<sigma>) \<in> Decreasing_Diagrams.seq lrs'" using a2 by blast
qed

lemma lem_map_diag:
fixes lrs::"('a,'b) lars" and f::"'b \<Rightarrow> 'c" and lrs'::"('a,'c) lars" 
    and d::"('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq \<times> ('a,'b) seq"
assumes a1: "lrs' = {(a,l',b). \<exists>l. l' = f l \<and> (a,l,b) \<in> lrs }" 
    and a2: "diagram lrs d"
shows "diagram lrs' (map_diag_labels f d)"
proof -
  obtain \<tau> \<sigma> \<sigma>' \<tau>' where b1: "d = (\<tau>, \<sigma>, \<sigma>', \<tau>')" using prod_cases4 by blast
  moreover obtain \<tau>1 \<sigma>1 \<sigma>1' \<tau>1' where b2: "\<tau>1 = (map_seq_labels f \<tau>) \<and> \<sigma>1 = (map_seq_labels f \<sigma>) 
                          \<and> (\<sigma>1' = map_seq_labels f \<sigma>') \<and> (\<tau>1' = map_seq_labels f \<tau>')" by blast
  ultimately have b3: "(map_diag_labels f d) = (\<tau>1, \<sigma>1, \<sigma>1', \<tau>1')" by simp
  have b4: "fst \<sigma> = fst \<tau> \<and> lst \<sigma> = fst \<tau>' \<and> lst \<tau> = fst \<sigma>' \<and> lst \<sigma>' = lst \<tau>'" 
    using b1 a2 unfolding Decreasing_Diagrams.diagram_def by simp
  have b5: "\<sigma>1 \<in> Decreasing_Diagrams.seq lrs' \<and> \<tau>1 \<in> Decreasing_Diagrams.seq lrs' 
         \<and> \<sigma>1' \<in> Decreasing_Diagrams.seq lrs' \<and> \<tau>1' \<in> Decreasing_Diagrams.seq lrs'" 
      using a1 a2 b1 b2 lem_map_seq[of lrs' f] by (simp add: Decreasing_Diagrams.diagram_def)
  moreover have "fst \<sigma>1 = fst \<tau>1" using b2 b4 unfolding map_seq_labels_def by simp
  moreover have "lst \<sigma>1 = fst \<tau>1' \<and> lst \<tau>1 = fst \<sigma>1'" using b4 
    by (simp add: b2 map_seq_labels_def lst_def, metis (no_types, lifting) case_prod_beta last_map snd_conv)
  moreover have "lst \<sigma>1' = lst \<tau>1'" using b4 
    by (simp add: b2 map_seq_labels_def lst_def, metis (no_types, lifting) case_prod_beta last_map snd_conv)
  ultimately show "diagram lrs' (map_diag_labels f d)" using b3 b5 unfolding Decreasing_Diagrams.diagram_def by simp
qed

lemma lem_map_D_loc:
fixes cmp cmp' s1 s2 s3 s4 f
assumes a1: "Decreasing_Diagrams.D cmp s1 s2 s3 s4" 
    and a2: "trans cmp" and a3: "irrefl cmp" and a4: "inj_on f (Field cmp)"
    and a5: "cmp' = {(a',b'). \<exists> a b. a' = f a \<and> b' = f b \<and> (a,b) \<in> cmp}"
    and a6: "length s1 = 1" and a7: "length s2 = 1"
shows "Decreasing_Diagrams.D cmp' (map f s1) (map f s2) (map f s3) (map f s4)"
proof -
  obtain \<alpha> where b1: "s2 = [\<alpha>]" using a7 by (metis One_nat_def Suc_length_conv length_0_conv)
  moreover obtain \<beta> where b2: "s1 = [\<beta>]" using a6 by (metis One_nat_def Suc_length_conv length_0_conv)
  ultimately have b3: "Decreasing_Diagrams.D cmp [\<beta>] [\<alpha>] s3 s4" using a1 by blast
  then obtain \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3 where b4: "s3 = \<sigma>1@\<sigma>2@\<sigma>3" and b5: "s4 = \<tau>1@\<tau>2@\<tau>3" and b6: "LD' cmp \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3"
    using Decreasing_Diagrams.proposition3_4_inv[of cmp \<beta> \<alpha> s3 s4] a2 a3 by blast
  obtain \<sigma>1' \<sigma>2' \<sigma>3' where b7: "\<sigma>1' = map f \<sigma>1 \<and> \<sigma>2' = map f \<sigma>2 \<and> \<sigma>3' = map f \<sigma>3" by blast
  obtain \<tau>1' \<tau>2' \<tau>3' where b8: "\<tau>1' = map f \<tau>1 \<and> \<tau>2' = map f \<tau>2 \<and> \<tau>3' = map f \<tau>3" by blast
  obtain s3' s4' where b9: "s3' = map f s3" and b10: "s4' = map f s4" by blast
  have "trans cmp'" using a2 a4 a5 lem_tr_inj_im_tr by blast
  moreover have "irrefl cmp'" using a3 a4 a5 lem_irr_inj_im_irr by blast
  moreover have "s3' = \<sigma>1'@\<sigma>2'@\<sigma>3'" using b4 b7 b9 by simp
  moreover have "s4' = \<tau>1'@\<tau>2'@\<tau>3'" using b5 b8 b10 by simp
  moreover have "LD' cmp' (f \<beta>) (f \<alpha>) \<sigma>1' \<sigma>2' \<sigma>3' \<tau>1' \<tau>2' \<tau>3'"
  proof -
     have c1: "LD_1' cmp \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3" and c2: "LD_1' cmp \<alpha> \<beta> \<tau>1 \<tau>2 \<tau>3" 
      using b6 unfolding Decreasing_Diagrams.LD'_def by blast+
     have "LD_1' cmp' (f \<beta>) (f \<alpha>) \<sigma>1' \<sigma>2' \<sigma>3'"
      using c1 unfolding Decreasing_Diagrams.LD_1'_def Decreasing_Diagrams.ds_def by (simp add: a5 b7, blast)
     moreover have "LD_1' cmp' (f \<alpha>) (f \<beta>) \<tau>1' \<tau>2' \<tau>3'"
      using c2 unfolding Decreasing_Diagrams.LD_1'_def Decreasing_Diagrams.ds_def by (simp add: a5 b8, blast)
     ultimately show "LD' cmp' (f \<beta>) (f \<alpha>) \<sigma>1' \<sigma>2' \<sigma>3' \<tau>1' \<tau>2' \<tau>3'" unfolding Decreasing_Diagrams.LD'_def by blast
  qed
  ultimately have "Decreasing_Diagrams.D cmp' [f \<beta>] [f \<alpha>] s3' s4'" using Decreasing_Diagrams.proposition3_4[of cmp'] by blast
  moreover have "(map f s1) = [f \<beta>] \<and> (map f s2) = [f \<alpha>]" using b1 b2 by simp
  ultimately show "Decreasing_Diagrams.D cmp' (map f s1) (map f s2) (map f s3) (map f s4)" using b9 b10 by simp
qed

lemma lem_map_DD_loc:
fixes lrs::"('a,'b) lars" and cmp::"'b rel" and lrs'::"('a,'c) lars" and cmp'::"'c rel" and f::"'b \<Rightarrow> 'c"
assumes a1: "trans cmp" and a2: "irrefl cmp" and a3: "inj_on f (Field cmp)"
    and a4: "cmp' = {(a',b'). \<exists> a b. a' = f a \<and> b' = f b \<and> (a,b) \<in> cmp}"
    and a5: "lrs' = {(a,l',b). \<exists>l. l' = f l \<and> (a,l,b) \<in> lrs }"
    and a6: "length (snd (fst d)) = 1" and a7: "length (snd (fst (snd d))) = 1"
    and a8: "DD lrs cmp d"
shows "DD lrs' cmp' (map_diag_labels f d)"
proof -
  have "diagram lrs' (map_diag_labels f d)" using a4 a5 a8 lem_map_diag unfolding Decreasing_Diagrams.DD_def by blast
  moreover have "D2 cmp' (map_diag_labels f d)"
  proof -
    obtain \<tau> \<sigma> \<sigma>' \<tau>' where c1: "d = (\<tau>,\<sigma>,\<sigma>',\<tau>')" by (metis prod_cases3)
    obtain s1 s2 s3 s4 where c2: "s1 = labels \<tau> \<and> s2 = labels \<sigma> \<and> s3 = labels \<sigma>' \<and> s4 = labels \<tau>'" by blast
    have "Decreasing_Diagrams.D cmp s1 s2 s3 s4" 
      using a8 c1 c2 unfolding Decreasing_Diagrams.DD_def Decreasing_Diagrams.D2_def by simp
    moreover have "length s1 = 1 \<and> length s2 = 1" using a6 a7 c1 c2 unfolding labels_def by simp
    ultimately have "Decreasing_Diagrams.D cmp' (map f s1) (map f s2) (map f s3) (map f s4)"
      using a1 a2 a3 a4 lem_map_D_loc by blast
    moreover have "labels (map_seq_labels f \<tau>) = (map f s1)" 
              and "labels (map_seq_labels f \<sigma>) = (map f s2)"
              and "labels (map_seq_labels f \<sigma>') = (map f s3)"
              and "labels (map_seq_labels f \<tau>') = (map f s4)"
      using c2 unfolding map_seq_labels_def Decreasing_Diagrams.labels_def by force+
    ultimately have "D2 cmp' ((map_seq_labels f \<tau>), (map_seq_labels f \<sigma>), (map_seq_labels f \<sigma>'), (map_seq_labels f \<tau>'))"
      unfolding Decreasing_Diagrams.D2_def by simp
    then show "D2 cmp' (map_diag_labels f d)" using c1 unfolding Decreasing_Diagrams.D2_def by simp
  qed
  ultimately show "DD lrs' cmp' (map_diag_labels f d)" unfolding Decreasing_Diagrams.DD_def by blast
qed

lemma lem_ddseq_mon: "lrs1 \<subseteq> lrs2 \<Longrightarrow> Decreasing_Diagrams.seq lrs1 \<subseteq> Decreasing_Diagrams.seq lrs2"
proof -
  assume a1: "lrs1 \<subseteq> lrs2"
  show "Decreasing_Diagrams.seq lrs1 \<subseteq> Decreasing_Diagrams.seq lrs2"
  proof
    fix a s
    assume b1: "(a,s) \<in> Decreasing_Diagrams.seq lrs1"
    show "(a,s) \<in> Decreasing_Diagrams.seq lrs2"
      by (rule Decreasing_Diagrams.seq.induct[of _ _ lrs1], 
          simp only: b1, simp only: seq.intros(1), meson a1 contra_subsetD seq.intros(2))
  qed
qed

lemma lem_dd_D_mon:
fixes cmp1 cmp2 \<alpha> \<beta> s1 s2
assumes a1: "trans cmp1 \<and> irrefl cmp1" and a2: "trans cmp2 \<and> irrefl cmp2" and a3: "cmp1 \<subseteq> cmp2"
    and a4: "Decreasing_Diagrams.D cmp1 [\<alpha>] [\<beta>] s1 s2"
shows "Decreasing_Diagrams.D cmp2 [\<alpha>] [\<beta>] s1 s2"
proof -
  obtain \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3 
    where b1: "s1 = \<sigma>1@\<sigma>2@\<sigma>3 \<and> s2 = \<tau>1@\<tau>2@\<tau>3" and b2: "LD' cmp1 \<alpha> \<beta> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3" 
    using a1 a4 Decreasing_Diagrams.proposition3_4_inv[of "cmp1" \<alpha> \<beta> s1 s2] by blast
  then have b3: "LD_1' cmp1 \<alpha> \<beta> \<sigma>1 \<sigma>2 \<sigma>3" and b4: "LD_1' cmp1 \<beta> \<alpha> \<tau>1 \<tau>2 \<tau>3" 
    unfolding Decreasing_Diagrams.LD'_def by blast+
  have "LD_1' cmp2 \<alpha> \<beta> \<sigma>1 \<sigma>2 \<sigma>3" 
    using a3 b3 unfolding Decreasing_Diagrams.LD_1'_def Decreasing_Diagrams.ds_def by blast
  moreover have "LD_1' cmp2 \<beta> \<alpha> \<tau>1 \<tau>2 \<tau>3"
    using a3 b4 unfolding Decreasing_Diagrams.LD_1'_def Decreasing_Diagrams.ds_def by blast
  ultimately show "Decreasing_Diagrams.D cmp2 [\<alpha>] [\<beta>] s1 s2"
    using Decreasing_Diagrams.proposition3_4[of cmp2 \<alpha> \<beta>] by (simp add: a2 b1 LD'_def)
qed

(* ----------------------------------------------------------------------- *)

subsubsection \<open>Result\<close>

(* ----------------------------------------------------------------------- *)

text \<open>The next lemma has the following meaning: every ARS in the finite DCR hierarchy has the LD property.\<close>

lemma lem_dcr_to_ld:
fixes n::nat and r::"'U rel"
assumes "DCR n r"
shows "LD (UNIV::nat set) r"
proof -
  obtain g::"nat \<Rightarrow> 'U rel" where
    b1: "DCR_generating g" and b3: "r = \<Union> { r'. \<exists> \<alpha>'. \<alpha>' < n \<and> r' = g \<alpha>' }"
    using assms unfolding DCR_def by blast
  obtain lrs::"('U, nat) lars" where b4: "lrs = {(a,\<alpha>',b). \<alpha>' < n \<and> (a,b) \<in> g \<alpha>'}" by blast
  obtain cmp::"nat rel" where b5: "cmp = {(\<alpha>, \<beta>). \<alpha> < \<beta> }" by blast
  have "r = unlabel lrs" using b3 b4 unfolding unlabel_def by blast
  moreover have b6: "trans cmp" using b5 unfolding trans_def by force
  moreover have b7: "wf cmp"
  proof -
    have "cmp = ({(x::nat, y::nat). x < y})"
      unfolding b5 lex_prod_def by fastforce
    moreover have "wf {(x::nat, y::nat). x < y}" using wf_less by blast
    ultimately show ?thesis using wf_lex_prod by blast
  qed
  moreover have "\<forall>P. local_peak lrs P \<longrightarrow> (\<exists> \<sigma>' \<tau>'. DD lrs cmp (fst P,snd P,\<sigma>',\<tau>'))"
  proof (intro allI impI)
    fix P
    assume c1: "local_peak lrs P"
    moreover obtain \<tau> \<sigma> where c2: "P = (\<tau>, \<sigma>)" using surjective_pairing by blast
    ultimately obtain a b c \<alpha> \<beta> 
        where c3: "(a,\<alpha>,b) \<in> lrs \<and> (a,\<beta>,c) \<in> lrs" 
          and c4: "\<sigma> = (a,[(\<alpha>,b)]) \<and> \<tau> = (a,[(\<beta>,c)])" using lem_lpeak_expr[of lrs] by blast
    then have c5: "\<alpha> < n \<and> \<beta> < n" and c6: "(a,b) \<in> (g \<alpha>) \<and> (a,c) \<in> (g \<beta>)" using b4 by blast+
    obtain b' b'' c' c'' d where 
                 c7: "(b,b') \<in> (\<LL>1 g \<alpha>)^* \<and> (b',b'') \<in> (g \<beta>)^= \<and> (b'',d) \<in> (\<LL>v g \<alpha> \<beta>)^*"
             and c8: "(c,c') \<in> (\<LL>1 g \<beta>)^* \<and> (c',c'') \<in> (g \<alpha>)^= \<and> (c'',d) \<in> (\<LL>v g \<beta> \<alpha>)^*" 
             using b1 c6 unfolding DCR_generating_def \<DD>_def by (metis (no_types, lifting) mem_Collect_eq old.prod.case)
    obtain pn1 where "(b,b') \<in> (\<LL>1 g \<alpha>)^^pn1" using c7 by fastforce
    then obtain ph1 where pc9: "ph1 0 = b \<and> ph1 pn1 = b'" and "\<forall> i::nat. i < pn1 \<longrightarrow> (ph1 i, ph1 (Suc i)) \<in> (\<LL>1 g \<alpha>)"
      using relpow_fun_conv by metis
    then have "\<forall> i::nat. i<pn1 \<longrightarrow> (\<exists> \<alpha>'. \<alpha>' < \<alpha> \<and> (ph1 i, ph1 (Suc i)) \<in> g \<alpha>')" unfolding \<LL>1_def by blast
    then obtain p\<alpha>i1::"nat \<Rightarrow> nat" 
      where pc10: "\<forall> i::nat. i<pn1 \<longrightarrow> (p\<alpha>i1 i) < \<alpha> \<and> (ph1 i, ph1 (Suc i)) \<in> g (p\<alpha>i1 i)" by metis
    let ?pf1 = "\<lambda>i. ( p\<alpha>i1 i, ph1 (Suc i) )"
    obtain pls1 where pc11: "pls1 = (f_to_ls ?pf1 pn1)" by blast
    obtain n1 where "(b'',d) \<in> (\<LL>v g \<alpha> \<beta>)^^n1" using c7 by fastforce
    then obtain h1 where c9: "h1 0 = b'' \<and> h1 n1 = d" and "\<forall> i::nat. i < n1 \<longrightarrow> (h1 i, h1 (Suc i)) \<in> (\<LL>v g \<alpha> \<beta>)"
      using relpow_fun_conv by metis
    then have "\<forall> i::nat. i < n1 \<longrightarrow> (\<exists> \<alpha>'. (\<alpha>' < \<alpha> \<or> \<alpha>' < \<beta>) \<and> (h1 i, h1 (Suc i)) \<in> g \<alpha>')" unfolding \<LL>v_def by blast
    then obtain \<alpha>i1::"nat \<Rightarrow> nat" 
      where c10: "\<forall> i::nat. i<n1 \<longrightarrow> ((\<alpha>i1 i) < \<alpha> \<or> (\<alpha>i1 i) < \<beta>) \<and> (h1 i, h1 (Suc i)) \<in> g (\<alpha>i1 i)" by metis
    let ?f1 = "\<lambda>i. ( \<alpha>i1 i, h1 (Suc i) )"
    obtain ls1 where c11: "ls1 = (f_to_ls ?f1 n1)" by blast
    obtain \<tau>'' where qc12: "\<tau>'' = (if b' = b'' then (b'', ls1) else (b', (\<beta>, b'') # ls1))" by blast
    obtain \<tau>' where c12: "\<tau>' = (b, pls1 @ (snd \<tau>''))" by blast
    obtain pn2 where "(c,c') \<in> (\<LL>1 g \<beta>)^^pn2" using c8 by fastforce
    then obtain ph2 where pc13: "ph2 0 = c \<and> ph2 pn2 = c'" and "\<forall> i::nat. i < pn2 \<longrightarrow> (ph2 i, ph2 (Suc i)) \<in> (\<LL>1 g \<beta>)"
      using relpow_fun_conv by metis
    then have "\<forall> i::nat. i<pn2 \<longrightarrow> (\<exists> \<alpha>'. \<alpha>' < \<beta> \<and> (ph2 i, ph2 (Suc i)) \<in> g \<alpha>')" unfolding \<LL>1_def by blast
    then obtain p\<alpha>i2::"nat \<Rightarrow> nat" 
      where pc14: "\<forall> i::nat. i<pn2 \<longrightarrow> (p\<alpha>i2 i) < \<beta> \<and> (ph2 i, ph2 (Suc i)) \<in> g (p\<alpha>i2 i)" by metis
    let ?pf2 = "\<lambda>i. ( p\<alpha>i2 i, ph2 (Suc i) )"
    obtain pls2 where pc15: "pls2 = (f_to_ls ?pf2 pn2)" by blast
    have "\<LL>v g \<beta> \<alpha> = \<LL>v g \<alpha> \<beta>" unfolding \<LL>v_def by blast
    then have "(c'',d) \<in> (\<LL>v g \<alpha> \<beta>)^*" using c8 by simp
    then obtain n2 where "(c'',d) \<in> (\<LL>v g \<alpha> \<beta>)^^n2" using c8 by fastforce
    then obtain h2 where c13: "h2 0 = c'' \<and> h2 n2 = d" and "\<forall> i::nat. i < n2 \<longrightarrow> (h2 i, h2 (Suc i)) \<in> (\<LL>v g \<alpha> \<beta>)"
      using relpow_fun_conv by metis
    then have "\<forall> i::nat. i<n2 \<longrightarrow> (\<exists> \<alpha>'. (\<alpha>' < \<alpha> \<or> \<alpha>' < \<beta>) \<and> (h2 i, h2 (Suc i)) \<in> g \<alpha>')" unfolding \<LL>v_def by blast
    then obtain \<alpha>i2::"nat \<Rightarrow> nat" 
      where c14: "\<forall> i::nat. i<n2 \<longrightarrow> ((\<alpha>i2 i) < \<alpha> \<or> (\<alpha>i2 i) < \<beta>) \<and> (h2 i, h2 (Suc i)) \<in> g (\<alpha>i2 i)" by metis
    let ?f2 = "\<lambda>i. ( \<alpha>i2 i, h2 (Suc i) )"
    obtain ls2 where c15: "ls2 = (f_to_ls ?f2 n2)" by blast
    obtain \<sigma>'' where qc16: "\<sigma>'' = (if c' = c'' then (c'', ls2) else (c', (\<alpha>, c'') # ls2))" by blast
    obtain \<sigma>' where c16: "\<sigma>' = (c, pls2 @ (snd \<sigma>''))" by blast
    have "DD lrs cmp (\<tau>, \<sigma>, \<sigma>', \<tau>')"
    proof -
      have d1': "\<forall> k. k < pn1 \<longrightarrow> (ph1 k, p\<alpha>i1 k, ph1 (Suc k)) \<in> lrs"
      proof (intro allI impI)
        fix k
        assume "k < pn1"
        moreover then have "(ph1 k, ph1 (Suc k)) \<in> g (p\<alpha>i1 k) \<and> (p\<alpha>i1 k <  n)" 
          using c5 pc10 by force
        ultimately show "(ph1 k, p\<alpha>i1 k, ph1 (Suc k)) \<in> lrs" using b4 by blast
      qed
      have d1: "\<forall> k. k < n1 \<longrightarrow> (h1 k, \<alpha>i1 k, h1 (Suc k)) \<in> lrs"
      proof (intro allI impI)
        fix k
        assume "k < n1"
        moreover then have "(h1 k, h1 (Suc k)) \<in> g (\<alpha>i1 k) \<and> \<alpha>i1 k < n" 
          using c5 c10 by force
        ultimately show "(h1 k, \<alpha>i1 k, h1 (Suc k)) \<in> lrs" using b4 by blast
      qed
      have d2': "\<forall> k. k < pn2 \<longrightarrow> (ph2 k, p\<alpha>i2 k, ph2 (Suc k)) \<in> lrs"
      proof (intro allI impI)
        fix k
        assume "k < pn2"
        moreover then have "(ph2 k, ph2 (Suc k)) \<in> g (p\<alpha>i2 k) \<and> p\<alpha>i2 k < n" 
          using c5 pc14 by force
        ultimately show "(ph2 k, p\<alpha>i2 k, ph2 (Suc k)) \<in> lrs" using b4 by blast
      qed
      have d2: "\<forall> k. k < n2 \<longrightarrow> (h2 k, \<alpha>i2 k, h2 (Suc k)) \<in> lrs"
      proof (intro allI impI)
        fix k
        assume "k < n2"
        moreover then have "(h2 k, h2 (Suc k)) \<in> g (\<alpha>i2 k) \<and> \<alpha>i2 k < n" 
          using c5 c14 by force
        ultimately show "(h2 k, \<alpha>i2 k, h2 (Suc k)) \<in> lrs" using b4 by blast
      qed
      have d3: "\<tau>'' \<in> Decreasing_Diagrams.seq lrs"
      proof -
        have "\<forall> k. k \<le> n1 \<longrightarrow> (b'', (f_to_ls ?f1 k)) \<in> Decreasing_Diagrams.seq lrs"
        proof
          fix k0
          show "k0 \<le> n1 \<longrightarrow> (b'', (f_to_ls ?f1 k0)) \<in> Decreasing_Diagrams.seq lrs"
          proof (induct k0)
            show "0 \<le> n1 \<longrightarrow> (b'', f_to_ls ?f1 0) \<in> Decreasing_Diagrams.seq lrs"
              using Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
          next
            fix k
            assume g1: "k \<le> n1 \<longrightarrow> (b'', f_to_ls ?f1 k) \<in> Decreasing_Diagrams.seq lrs"
            show "Suc k \<le> n1 \<longrightarrow> (b'', f_to_ls ?f1 (Suc k)) \<in> Decreasing_Diagrams.seq lrs"
            proof
              assume h1: "Suc k \<le> n1"
              then have h2: "(b'', f_to_ls ?f1 k) \<in> Decreasing_Diagrams.seq lrs" using g1 by simp
              obtain s where h3: "s = (h1 k, [(\<alpha>i1 k, h1 (Suc k))])" by blast
              then have "s \<in> Decreasing_Diagrams.seq lrs"
                using h1 d1 Decreasing_Diagrams.seq.intros(2)[of "h1 k" "\<alpha>i1 k"] Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
              moreover have "lst (b'', f_to_ls ?f1 k) = fst s" 
                using c9 h3 unfolding lst_def by (cases k, simp+)
              ultimately show "(b'', f_to_ls ?f1 (Suc k)) \<in> Decreasing_Diagrams.seq lrs" 
                using h2 h3 Decreasing_Diagrams.seq_concat_helper[of b'' "f_to_ls ?f1 k" lrs s] by simp
            qed
          qed
        qed
        then have "(b'', ls1) \<in> Decreasing_Diagrams.seq lrs" using c11 by blast
        moreover then have "b' \<noteq> b'' \<longrightarrow> (b', (\<beta>, b'') # ls1) \<in> Decreasing_Diagrams.seq lrs"
          using b4 c5 c7 Decreasing_Diagrams.seq.intros(2)[of b' \<beta> b''] by fastforce
        ultimately show "\<tau>'' \<in> Decreasing_Diagrams.seq lrs" using qc12 by simp
      qed
      have d4: "\<sigma>'' \<in> Decreasing_Diagrams.seq lrs"
      proof -
        have "\<forall> k. k \<le> n2 \<longrightarrow> (c'', (f_to_ls ?f2 k)) \<in> Decreasing_Diagrams.seq lrs"
        proof
          fix k0
          show "k0 \<le> n2 \<longrightarrow> (c'', (f_to_ls ?f2 k0)) \<in> Decreasing_Diagrams.seq lrs"
          proof (induct k0)
            show "0 \<le> n2 \<longrightarrow> (c'', f_to_ls ?f2 0) \<in> Decreasing_Diagrams.seq lrs"
              using Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
          next
            fix k
            assume g1: "k \<le> n2 \<longrightarrow> (c'', f_to_ls ?f2 k) \<in> Decreasing_Diagrams.seq lrs"
            show "Suc k \<le> n2 \<longrightarrow> (c'', f_to_ls ?f2 (Suc k)) \<in> Decreasing_Diagrams.seq lrs"
            proof
              assume h1: "Suc k \<le> n2"
              then have h2: "(c'', f_to_ls ?f2 k) \<in> Decreasing_Diagrams.seq lrs" using g1 by simp
              obtain s where h3: "s = (h2 k, [(\<alpha>i2 k, h2 (Suc k))])" by blast
              then have "s \<in> Decreasing_Diagrams.seq lrs"
                using h1 d2 Decreasing_Diagrams.seq.intros(2)[of "h2 k" "\<alpha>i2 k"] Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
              moreover have "lst (c'', f_to_ls ?f2 k) = fst s" 
                using c13 h3 unfolding lst_def  by (cases k, simp+)
              ultimately show "(c'', f_to_ls ?f2 (Suc k)) \<in> Decreasing_Diagrams.seq lrs" 
                using h2 h3 Decreasing_Diagrams.seq_concat_helper[of c'' "f_to_ls ?f2 k" lrs s] by simp
            qed
          qed
        qed
        then have "(c'', ls2) \<in> Decreasing_Diagrams.seq lrs" using c15 by blast
        moreover then have "c' \<noteq> c'' \<longrightarrow> (c', (\<alpha>, c'') # ls2) \<in> Decreasing_Diagrams.seq lrs"
          using b4 c5 c8 Decreasing_Diagrams.seq.intros(2)[of c' \<alpha> c''] by fastforce
        ultimately show "\<sigma>'' \<in> Decreasing_Diagrams.seq lrs" using qc16 by simp
      qed
      have "\<sigma> \<in> Decreasing_Diagrams.seq lrs" by (simp add: c3 c4 seq.intros(1) seq.intros(2))
      moreover have "\<tau> \<in> Decreasing_Diagrams.seq lrs" by (simp add: c3 c4 seq.intros(1) seq.intros(2))
      moreover have d5: "\<sigma>' \<in> Decreasing_Diagrams.seq lrs \<and> lst \<sigma>' = lst \<sigma>''"
      proof -
        have "(c, pls2) \<in> Decreasing_Diagrams.seq lrs"
        proof -
          have "\<forall> k. k \<le> pn2 \<longrightarrow> (c, (f_to_ls ?pf2 k)) \<in> Decreasing_Diagrams.seq lrs"
          proof
            fix k0
            show "k0 \<le> pn2 \<longrightarrow> (c, (f_to_ls ?pf2 k0)) \<in> Decreasing_Diagrams.seq lrs"
            proof (induct k0)
              show "0 \<le> pn2 \<longrightarrow> (c, f_to_ls ?pf2 0) \<in> Decreasing_Diagrams.seq lrs"
                using Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
            next
              fix k
              assume g1: "k \<le> pn2 \<longrightarrow> (c, f_to_ls ?pf2 k) \<in> Decreasing_Diagrams.seq lrs"
              show "Suc k \<le> pn2 \<longrightarrow> (c, f_to_ls ?pf2 (Suc k)) \<in> Decreasing_Diagrams.seq lrs"
              proof
                assume h1: "Suc k \<le> pn2"
                then have h2: "(c, f_to_ls ?pf2 k) \<in> Decreasing_Diagrams.seq lrs" using g1 by simp
                obtain s where h3: "s = (ph2 k, [(p\<alpha>i2 k, ph2 (Suc k))])" by blast
                then have "s \<in> Decreasing_Diagrams.seq lrs"
                  using h1 d2' Decreasing_Diagrams.seq.intros(2)[of "ph2 k" "p\<alpha>i2 k"] Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
                moreover have "lst (c, f_to_ls ?pf2 k) = fst s" 
                  using pc13 h3 unfolding lst_def by (cases k, simp+)
                ultimately show "(c, f_to_ls ?pf2 (Suc k)) \<in> Decreasing_Diagrams.seq lrs" 
                  using h2 h3 Decreasing_Diagrams.seq_concat_helper[of c "f_to_ls ?pf2 k" lrs s] by simp
              qed
            qed
          qed
          then show ?thesis using pc15 by blast
        qed
        moreover have "lst (c, pls2) = fst \<sigma>''"
        proof -
          have "lst (c, pls2) = c'" using pc13 pc15 unfolding lst_def by (cases pn2, simp+)
          then show ?thesis unfolding qc16 by simp
        qed
        ultimately show ?thesis using d4
          unfolding c16 using Decreasing_Diagrams.seq_concat_helper[of c pls2 lrs \<sigma>'' ] by blast
      qed
      moreover have d6: "\<tau>' \<in> Decreasing_Diagrams.seq lrs \<and> lst \<tau>' = lst \<tau>''"
      proof -
        have "(b, pls1) \<in> Decreasing_Diagrams.seq lrs"
        proof -
          have "\<forall> k. k \<le> pn1 \<longrightarrow> (b, (f_to_ls ?pf1 k)) \<in> Decreasing_Diagrams.seq lrs"
          proof
            fix k0
            show "k0 \<le> pn1 \<longrightarrow> (b, (f_to_ls ?pf1 k0)) \<in> Decreasing_Diagrams.seq lrs"
            proof (induct k0)
              show "0 \<le> pn1 \<longrightarrow> (b, f_to_ls ?pf1 0) \<in> Decreasing_Diagrams.seq lrs"
                using Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
            next
              fix k
              assume g1: "k \<le> pn1 \<longrightarrow> (b, f_to_ls ?pf1 k) \<in> Decreasing_Diagrams.seq lrs"
              show "Suc k \<le> pn1 \<longrightarrow> (b, f_to_ls ?pf1 (Suc k)) \<in> Decreasing_Diagrams.seq lrs"
              proof
                assume h1: "Suc k \<le> pn1"
                then have h2: "(b, f_to_ls ?pf1 k) \<in> Decreasing_Diagrams.seq lrs" using g1 by simp
                obtain s where h3: "s = (ph1 k, [(p\<alpha>i1 k, ph1 (Suc k))])" by blast
                then have "s \<in> Decreasing_Diagrams.seq lrs"
                  using h1 d1' Decreasing_Diagrams.seq.intros(2)[of "ph1 k" "p\<alpha>i1 k"] Decreasing_Diagrams.seq.intros(1)[of _ lrs] by simp
                moreover have "lst (b, f_to_ls ?pf1 k) = fst s" 
                  using pc9 h3 unfolding lst_def by (cases k, simp+)
                ultimately show "(b, f_to_ls ?pf1 (Suc k)) \<in> Decreasing_Diagrams.seq lrs" 
                  using h2 h3 Decreasing_Diagrams.seq_concat_helper[of b "f_to_ls ?pf1 k" lrs s] by simp
              qed
            qed
          qed
          then show ?thesis using pc11 by blast
        qed
        moreover have "lst (b, pls1) = fst \<tau>''"
        proof -
          have "lst (b, pls1) = b'" using pc9 pc11 unfolding lst_def by (cases pn1, simp+)
          then show ?thesis unfolding qc12 by simp
        qed
        ultimately show ?thesis using d3
          unfolding c12 using Decreasing_Diagrams.seq_concat_helper[of b pls1 lrs \<tau>'' ] by blast
      qed
      moreover have "fst \<sigma> = fst \<tau>" using c4 by simp
      moreover have "lst \<sigma> = fst \<tau>'" using c4 c12 unfolding lst_def by simp
      moreover have "lst \<tau> = fst \<sigma>'" using c4 c16 unfolding lst_def by simp
      moreover have "lst \<sigma>' = lst \<tau>'"
      proof -
        have "lst \<tau>'' = d"
        proof (cases "n1 = 0")
          assume "n1 = 0"
          then show "lst \<tau>'' = d" using c9 c11 qc12 unfolding lst_def by force
        next
          assume "n1 \<noteq> 0"
          moreover then have "last ls1 = ( \<alpha>i1 (n1-1), h1 n1 )" using c11 by (cases n1, simp+)
          ultimately show "lst \<tau>'' = d" using c9 c11 qc12 lem_ftofs_len unfolding lst_def
            by (smt last_ConsR list.distinct(1) list.size(3) snd_conv)
        qed
        moreover have "lst \<sigma>'' = d"
        proof (cases "n2 = 0")
          assume "n2 = 0"
          then show "lst \<sigma>'' = d" using c13 c15 qc16 unfolding lst_def by force
        next
          assume "n2 \<noteq> 0"
          moreover then have "last ls2 = ( \<alpha>i2 (n2-1), h2 n2 )" using c15 by (cases n2, simp+)
          ultimately show "lst \<sigma>'' = d" using c13 c15 qc16 lem_ftofs_len unfolding lst_def
            by (smt last_ConsR list.distinct(1) list.size(3) snd_conv)
        qed
        moreover have "lst \<tau>' = lst \<tau>'' \<and> lst \<sigma>' = lst \<sigma>''" using d5 d6 by blast
        ultimately show ?thesis by metis
      qed
      moreover have "Decreasing_Diagrams.D cmp (labels \<tau>) (labels \<sigma>) (labels \<sigma>') (labels \<tau>')"
      proof -
        obtain \<sigma>1 where e01: "\<sigma>1 = (f_to_ls p\<alpha>i2 pn2)" by blast
        obtain \<sigma>2 where e1: "\<sigma>2 = (if c' = c'' then [] else [\<alpha>])" by blast
        obtain \<sigma>3 where e2: "\<sigma>3 = (f_to_ls \<alpha>i2 n2)" by blast
        obtain \<tau>1 where e02: "\<tau>1 = (f_to_ls p\<alpha>i1 pn1)" by blast
        obtain \<tau>2 where e3: "\<tau>2 = (if b' = b'' then [] else [\<beta>])" by blast
        obtain \<tau>3 where e4: "\<tau>3 = (f_to_ls \<alpha>i1 n1)" by blast
        have "labels \<tau> = [\<beta>] \<and> labels \<sigma> = [\<alpha>]" using c4 unfolding labels_def by simp
        moreover have "labels \<sigma>' = \<sigma>1 @ \<sigma>2 @ \<sigma>3"
        proof -
          have "labels \<sigma>'' = \<sigma>2 @ \<sigma>3"
          proof -
            have "\<forall> k. k \<le> n2 \<longrightarrow> map fst (f_to_ls ?f2 k) = f_to_ls \<alpha>i2 k"
            proof
              fix k
              show "k \<le> n2 \<longrightarrow> map fst (f_to_ls ?f2 k) = f_to_ls \<alpha>i2 k" by (induct k, simp+)
            qed
            then show ?thesis using c15 qc16 e1 e2 unfolding labels_def by simp
          qed
          moreover have "labels \<sigma>' = \<sigma>1 @ labels \<sigma>''"
          proof -
            have "\<forall> k. k \<le> pn2 \<longrightarrow> map fst (f_to_ls ?pf2 k) = f_to_ls p\<alpha>i2 k"
            proof
              fix k
              show "k \<le> pn2 \<longrightarrow> map fst (f_to_ls ?pf2 k) = f_to_ls p\<alpha>i2 k" by (induct k, simp+)
            qed
            then have "map fst pls2 = \<sigma>1" unfolding pc15 e01 by blast
            then show ?thesis unfolding c16 labels_def by simp
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "labels \<tau>' = \<tau>1 @ \<tau>2 @ \<tau>3"
        proof -
          have "labels \<tau>'' = \<tau>2 @ \<tau>3"
          proof -
            have "\<forall> k. k \<le> n1 \<longrightarrow> map fst (f_to_ls ?f1 k) = f_to_ls \<alpha>i1 k"
            proof
              fix k
              show "k \<le> n1 \<longrightarrow> map fst (f_to_ls ?f1 k) = f_to_ls \<alpha>i1 k" by (induct k, simp+)
            qed
            then show ?thesis using c11 qc12 e3 e4 unfolding labels_def by simp
          qed
          moreover have "labels \<tau>' = \<tau>1 @ labels \<tau>''"
          proof -
            have "\<forall> k. k \<le> pn1 \<longrightarrow> map fst (f_to_ls ?pf1 k) = f_to_ls p\<alpha>i1 k"
            proof
              fix k
              show "k \<le> pn1 \<longrightarrow> map fst (f_to_ls ?pf1 k) = f_to_ls p\<alpha>i1 k" by (induct k, simp+)
            qed
            then have "map fst pls1 = \<tau>1" unfolding pc11 e02 by blast
            then show ?thesis unfolding c12 labels_def by simp
          qed
          ultimately show ?thesis by simp
        qed
        moreover have "LD' cmp \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3"
        proof -
          let ?dn = "{\<alpha>' . (\<alpha>',\<alpha>) \<in> cmp \<or> (\<alpha>',\<beta>) \<in> cmp}"
          have pf1: "set \<sigma>1 \<subseteq> {y. (y, \<beta>) \<in> cmp}"
          proof -
            have "\<forall> k. k \<le> pn2 \<longrightarrow> set (f_to_ls p\<alpha>i2 k) \<subseteq> {y. (y, \<beta>) \<in> cmp}"
            proof
              fix k
              show "k \<le> pn2 \<longrightarrow> set (f_to_ls p\<alpha>i2 k) \<subseteq> {y. (y, \<beta>) \<in> cmp}" using b5 pc14 by (induct k, simp+)
            qed
            then show ?thesis using e01 by blast
          qed
          have pf2: "set \<tau>1 \<subseteq> {y. (y, \<alpha>) \<in> cmp}"
          proof -
            have "\<forall> k. k \<le> pn1 \<longrightarrow> set (f_to_ls p\<alpha>i1 k) \<subseteq> {y. (y, \<alpha>) \<in> cmp}"
            proof
              fix k
              show "k \<le> pn1 \<longrightarrow> set (f_to_ls p\<alpha>i1 k) \<subseteq> {y. (y, \<alpha>) \<in> cmp}" using b5 pc10 by (induct k, simp+)
            qed
            then show ?thesis using e02 by blast
          qed
          have f1: "set \<sigma>3 \<subseteq> ?dn"
          proof -
            have "\<forall> k. k \<le> n2 \<longrightarrow> set (f_to_ls \<alpha>i2 k) \<subseteq> ?dn"
            proof
              fix k
              show "k \<le> n2 \<longrightarrow> set (f_to_ls \<alpha>i2 k) \<subseteq> ?dn" using b5 c14 by (induct k, simp+)
            qed
            then show ?thesis using e2 by blast
          qed
          have f2: "set \<tau>3 \<subseteq> ?dn"
          proof -
            have "\<forall> k. k \<le> n1 \<longrightarrow> set (f_to_ls \<alpha>i1 k) \<subseteq> ?dn"
            proof
              fix k
              show "k \<le> n1 \<longrightarrow> set (f_to_ls \<alpha>i1 k) \<subseteq> ?dn" using b5 c10 by (induct k, simp+)
            qed
            then show ?thesis using e4 by blast
          qed
          have "LD_1' cmp \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3" using pf1 f1 e1 e2 unfolding LD_1'_def Decreasing_Diagrams.ds_def by simp
          moreover have "LD_1' cmp \<alpha> \<beta> \<tau>1 \<tau>2 \<tau>3" using pf2 f2 e3 e4 unfolding LD_1'_def Decreasing_Diagrams.ds_def by force
          ultimately show ?thesis unfolding LD'_def by blast
        qed
        moreover have "trans cmp \<and> wf cmp" using b6 b7 by blast
        moreover then have "irrefl cmp" using irrefl_def by fastforce
        ultimately show ?thesis using proposition3_4[of cmp \<beta> \<alpha> \<sigma>1 \<sigma>2 \<sigma>3 \<tau>1 \<tau>2 \<tau>3] by simp
      qed
      ultimately show ?thesis unfolding DD_def diagram_def D2_def by simp
    qed
    then show "\<exists> \<sigma>' \<tau>'. DD lrs cmp (fst P,snd P,\<sigma>',\<tau>')" using c2 by fastforce
  qed
  ultimately show ?thesis unfolding LD_def by blast
qed


(* ----------------------------------------------------------------------- *)

section \<open>Main theorem\<close>

(* ----------------------------------------------------------------------- *)

text \<open>The next theorem has the following meaning:
  if the cardinality of a binary relation $r$ does not exceed the first uncountable cardinal (\<open>cardSuc |UNIV::nat set|\<close>), then the following two conditions are equivalent:\<close>
text \<open>1. $r$ is confluent (\<open>Abstract_Rewriting.CR r\<close>)\<close>
text \<open>2. $r$ can be proven confluent using the decreasing diagrams method with natural numbers as labels (\<open>Decreasing_Diagrams.LD (UNIV::nat set) r\<close>).\<close>

theorem N1_completeness:
fixes r::"'a rel"
assumes "|r| \<le>o cardSuc |UNIV::nat set|"
shows "Abstract_Rewriting.CR r = Decreasing_Diagrams.LD (UNIV::nat set) r"
proof
  assume b0: "CR r"
  have b1: "|r| \<le>o cardSuc |UNIV::nat set|" using assms by simp
  obtain \<kappa> where b2: "\<kappa> = cardSuc |UNIV::nat set|" by blast
  have "|Field r| \<le>o cardSuc |UNIV::nat set|"
  proof (cases "finite r")
    assume "finite r"
    then show ?thesis using b2 lem_fin_fl_rel by (metis Field_card_of Field_natLeq cardSuc_ordLeq_ordLess 
      card_of_card_order_on card_of_mono2 finite_iff_ordLess_natLeq ordLess_imp_ordLeq)
  next
    assume "\<not> finite r"
    then show ?thesis using b1 b2 lem_rel_inf_fld_card using ordIso_ordLeq_trans by blast
  qed
  moreover have "confl_rel r" using b0 unfolding confl_rel_def Abstract_Rewriting.CR_on_def by blast
  ultimately show "LD (UNIV::nat set) r" using lem_dc3_confl_lewsuc[of r] lem_dcr_to_ld by blast
next
  assume "LD (UNIV::nat set) r"
  then show "CR r" using Decreasing_Diagrams.sound by blast
qed

end
