header {* Well-order relations  *}

(* author: Andrei Popescu *)

theory Wellorder_Relation imports Wellfounded2
begin


text{* In this section, we develop basic concepts and results pertaining 
to well-order relations.  Note that we consider well-order relations 
as {\em non-strict relations},  
i.e., as containing the diagonals of their fields. *}


locale wo_rel = rel + assumes WELL: "Well_order r"

text{* The following context encompasses all this section. In other words, 
for the whole section, we consider a fixed well-order relation @{text "r"}. *} 

context wo_rel  
begin 


subsection{* Auxiliaries *}


lemma REFL: "Refl r" 
using WELL order_on_defs[of _ r] by auto


lemma TRANS: "trans r" 
using WELL order_on_defs[of _ r] by auto


lemma ANTISYM: "antisym r" 
using WELL order_on_defs[of _ r] by auto


lemma PREORD: "Preorder r" 
using WELL order_on_defs[of _ r] by auto


lemma PARORD: "Partial_order r" 
using WELL order_on_defs[of _ r] by auto


lemma TOTAL: "Total r" 
using WELL order_on_defs[of _ r] by auto


lemma TOTALS: "\<forall>a \<in> Field r. \<forall>b \<in> Field r. (a,b) \<in> r \<or> (b,a) \<in> r" 
using REFL TOTAL refl_on_def[of _ r] total_on_def[of _ r] by force


lemma LIN: "Linear_order r" 
using WELL well_order_on_def[of _ r] by auto


lemma WF: "wf (r - Id)" 
using WELL well_order_on_def[of _ r] by auto


lemma cases_Total: 
"\<And> phi a b. \<lbrakk>{a,b} <= Field r; ((a,b) \<in> r \<Longrightarrow> phi a b); ((b,a) \<in> r \<Longrightarrow> phi a b)\<rbrakk> 
             \<Longrightarrow> phi a b"
using TOTALS by auto


lemma cases_Total2: 
"\<And> phi a b. \<lbrakk>{a,b} \<le> Field r; ((a,b) \<in> r - Id \<Longrightarrow> phi a b); 
              ((b,a) \<in> r - Id \<Longrightarrow> phi a b); (a = b \<Longrightarrow> phi a b)\<rbrakk> 
             \<Longrightarrow> phi a b"
using TOTALS by auto


lemma cases_Total3: 
"\<And> phi a b. \<lbrakk>{a,b} \<le> Field r; ((a,b) \<in> r - Id \<or> (b,a) \<in> r - Id \<Longrightarrow> phi a b); 
              (a = b \<Longrightarrow> phi a b)\<rbrakk>  \<Longrightarrow> phi a b"
using TOTALS by auto


 
subsection {* Well-founded induction and recursion adapted to non-strict well-order relations  *}


text{* Here we provide induction and recursion principles specific to {\em non-strict} 
well-order relations. 
Although minor variations of those for well-founded relations, they will be useful 
for doing away with the tediousness of 
having to take out the diagonal each time in order to switch to a well-founded relation. *}


lemma well_order_induct:
assumes IND: "\<And>x. \<forall>y. y \<noteq> x \<and> (y, x) \<in> r \<longrightarrow> P y \<Longrightarrow> P x"
shows "P a"
proof- 
  have "\<And>x. \<forall>y. (y, x) \<in> r - Id \<longrightarrow> P y \<Longrightarrow> P x" 
  using IND by blast
  thus "P a" using WF wf_induct[of "r - Id" P a] by blast
qed


definition 
worec :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
where 
"worec F \<equiv> wfrec (r - Id) F"


definition 
adm_wo :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool"
where
"adm_wo H \<equiv> \<forall>f g x. (\<forall>y \<in> underS x. f y = g y) \<longrightarrow> H f x = H g x"


lemma worec_fixpoint:
assumes ADM: "adm_wo H"
shows "worec H = H (worec H)"
proof-
  let ?rS = "r - Id"
  have "adm_wf (r - Id) H"
  unfolding adm_wf_def
  using ADM adm_wo_def[of H] underS_def by auto
  hence "wfrec ?rS H = H (wfrec ?rS H)" 
  using WF wfrec_fixpoint[of ?rS H] by simp
  thus ?thesis unfolding worec_def .
qed


lemma worec_unique_fixpoint:
assumes ADM: "adm_wo H" and fp: "f = H f"
shows "f = worec H"
proof- 
  have "adm_wf (r - Id) H"
  unfolding adm_wf_def
  using ADM adm_wo_def[of H] underS_def by auto
  hence "f = wfrec (r - Id) H" 
  using fp WF wfrec_unique_fixpoint[of "r - Id" H] by simp
  thus ?thesis unfolding worec_def .
qed 


subsection {* The notions of maximum, minimum, supremum, successor and order filter  *}


text{* 
We define the successor {\em of a set}, and not of an element (the latter is of course 
a particular case).  Also, we define the maximum {\em of two elements}, @{text "max2"}, 
and the minimum {\em of a set}, @{text "minim"} -- we chose these variants since we 
consider them the most useful for well-orders.  The minimum is defined in terms of the 
auxiliary relational operator @{text "isMinim"}.  Then, supremum and successor are 
defined in terms of minimum as expected. 
The minimum is only meaningful for non-empty sets, and the successor is only 
meaningful for sets for which strict upper bounds exist.  
Order filters for well-orders are also known as ``initial segments". *}


definition max2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
where "max2 a b \<equiv> if (a,b) \<in> r then b else a"


definition isMinim :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
where "isMinim A b \<equiv> b \<in> A \<and> (\<forall>a \<in> A. (b,a) \<in> r)"

definition minim :: "'a set \<Rightarrow> 'a"
where "minim A \<equiv> THE b. isMinim A b"


definition supr :: "'a set \<Rightarrow> 'a" 
where "supr A \<equiv> minim (Above A)"

definition suc :: "'a set \<Rightarrow> 'a"
where "suc A \<equiv> minim (AboveS A)"

definition ofilter :: "'a set \<Rightarrow> bool"
where 
"ofilter A \<equiv> (A \<le> Field r) \<and> (\<forall>a \<in> A. under a \<le> A)"


subsubsection {* Properties of max2 *}


lemma max2_greater_among:
assumes "a \<in> Field r" and "b \<in> Field r" 
shows "(a, max2 a b) \<in> r \<and> (b, max2 a b) \<in> r \<and> max2 a b \<in> {a,b}"
proof-
  {assume "(a,b) \<in> r"  
   hence ?thesis using max2_def assms REFL refl_on_def 
   by (auto simp add: refl_on_def)
  }
  moreover
  {assume "a = b"
   hence "(a,b) \<in> r" using REFL  assms
   by (auto simp add: refl_on_def)
  }
  moreover
  {assume *: "a \<noteq> b \<and> (b,a) \<in> r" 
   hence "(a,b) \<notin> r" using ANTISYM 
   by (auto simp add: antisym_def)
   hence ?thesis using * max2_def assms REFL refl_on_def 
   by (auto simp add: refl_on_def)
  }
  ultimately show ?thesis using assms TOTAL
  total_on_def[of "Field r" r] by blast
qed


lemma max2_greater:
assumes "a \<in> Field r" and "b \<in> Field r" 
shows "(a, max2 a b) \<in> r \<and> (b, max2 a b) \<in> r"
using assms by (auto simp add: max2_greater_among)
 

lemma max2_among: 
assumes "a \<in> Field r" and "b \<in> Field r"
shows "max2 a b \<in> {a, b}"
using assms max2_greater_among[of a b] by simp


lemma max2_equals1:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(max2 a b = a) = ((b,a) \<in> r)"
using assms ANTISYM unfolding antisym_def using TOTALS 
by(auto simp add: max2_def max2_among) 


lemma max2_equals2:
assumes "a \<in> Field r" and "b \<in> Field r"
shows "(max2 a b = b) = ((a,b) \<in> r)"
using assms ANTISYM unfolding antisym_def using TOTALS 
by(auto simp add: max2_def max2_among)


lemma max2_iff: 
assumes "a \<in> Field r" and "b \<in> Field r"
shows "((max2 a b, c) \<in> r) = ((a,c) \<in> r \<and> (b,c) \<in> r)"
proof
  assume "(max2 a b, c) \<in> r"
  thus "(a,c) \<in> r \<and> (b,c) \<in> r" 
  using assms max2_greater[of a b] TRANS trans_def[of r] by blast
next
  assume "(a,c) \<in> r \<and> (b,c) \<in> r"
  thus "(max2 a b, c) \<in> r"
  using assms max2_among[of a b] by auto
qed 


subsubsection {* Existence and uniqueness for isMinim and well-definedness of minim *}


lemma isMinim_unique:
assumes MINIM: "isMinim B a" and MINIM': "isMinim B a'"
shows "a = a'"
proof-
  {have "a \<in> B" 
   using MINIM isMinim_def by simp
   hence "(a',a) \<in> r" 
   using MINIM' isMinim_def by simp
  }
  moreover
  {have "a' \<in> B" 
   using MINIM' isMinim_def by simp
   hence "(a,a') \<in> r" 
   using MINIM isMinim_def by simp
  }
  ultimately 
  show ?thesis using ANTISYM antisym_def[of r] by blast
qed


lemma Well_order_isMinim_exists:
assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}" 
shows "\<exists>b. isMinim B b"
proof-
  from WF wf_eq_minimal[of "r - Id"] NE Id_def obtain b where 
  *: "b \<in> B \<and> (\<forall>b'. b' \<noteq> b \<and> (b',b) \<in> r \<longrightarrow> b' \<notin> B)" by force
  show ?thesis
  proof(simp add: isMinim_def, rule exI[of _ b], auto)
    show "b \<in> B" using * by simp
  next
    fix b' assume As: "b' \<in> B"
    hence **: "b \<in> Field r \<and> b' \<in> Field r" using As SUB * by auto 
    (*  *) 
    from As  * have "b' = b \<or> (b',b) \<notin> r" by auto
    moreover 
    {assume "b' = b"
     hence "(b,b') \<in> r"  
     using ** REFL by (auto simp add: refl_on_def)
    }
    moreover
    {assume "b' \<noteq> b \<and> (b',b) \<notin> r"
     hence "(b,b') \<in> r"  
     using ** TOTAL by (auto simp add: total_on_def)
    }
    ultimately show "(b,b') \<in> r" by blast
  qed    
qed


lemma minim_isMinim: 
assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}" 
shows "isMinim B (minim B)"
proof-
  let ?phi = "(\<lambda> b. isMinim B b)"
  from assms Well_order_isMinim_exists 
  obtain b where *: "?phi b" by blast
  moreover
  have "\<And> b'. ?phi b' \<Longrightarrow> b' = b"
  using isMinim_unique * by auto
  ultimately show ?thesis
  unfolding minim_def using theI[of ?phi b] by blast
qed



subsubsection{* Properties of minim *}


lemma minim_in: 
assumes "B \<le> Field r" and "B \<noteq> {}"
shows "minim B \<in> B"
proof-
  from minim_isMinim[of B] assms 
  have "isMinim B (minim B)" by simp
  thus ?thesis by (simp add: isMinim_def) 
qed


lemma minim_inField: 
assumes "B \<le> Field r" and "B \<noteq> {}"
shows "minim B \<in> Field r"
proof- 
  have "minim B \<in> B" using assms by (simp add: minim_in)
  thus ?thesis using assms by blast 
qed


lemma minim_least: 
assumes  SUB: "B \<le> Field r" and IN: "b \<in> B"
shows "(minim B, b) \<in> r"
proof-
  from minim_isMinim[of B] assms 
  have "isMinim B (minim B)" by auto
  thus ?thesis by (auto simp add: isMinim_def IN) 
qed 


lemma minim_Under:
"\<lbrakk>B \<le> Field r; B \<noteq> {}\<rbrakk> \<Longrightarrow> minim B \<in> Under B"
by(auto simp add: Under_def minim_least minim_inField)


lemma equals_minim:
assumes SUB: "B \<le> Field r" and IN: "a \<in> B" and 
        LEAST: "\<And> b. b \<in> B \<Longrightarrow> (a,b) \<in> r" 
shows "a = minim B"
proof-
  from minim_isMinim[of B] assms 
  have "isMinim B (minim B)" by auto
  moreover have "isMinim B a" using IN LEAST isMinim_def by auto
  ultimately show ?thesis 
  using isMinim_unique by auto
qed


lemma equals_minim_Under:
"\<lbrakk>B \<le> Field r; a \<in> B; a \<in> Under B\<rbrakk> 
 \<Longrightarrow> a = minim B"
by(auto simp add: Under_def equals_minim minim_inField)


lemma minim_iff_In_Under:
assumes SUB: "B \<le> Field r" and NE: "B \<noteq> {}"
shows "(a = minim B) = (a \<in> B \<and> a \<in> Under B)"
proof
  assume "a = minim B"
  thus "a \<in> B \<and> a \<in> Under B" 
  using assms minim_in minim_Under by simp
next
  assume "a \<in> B \<and> a \<in> Under B"
  thus "a = minim B" 
  using assms equals_minim_Under by simp
qed


lemma minim_Under_under:
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "Under A = under (minim A)"
proof-
  (* Preliminary facts *)
  have 1: "minim A \<in> A"  
  using assms minim_in by auto
  have 2: "\<forall>x \<in> A. (minim A, x) \<in> r" 
  using assms minim_least by auto
  (* Main proof *)
  have "Under A \<le> under (minim A)"
  proof
    fix x assume "x \<in> Under A"
    with 1 Under_def have "(x,minim A) \<in> r" by auto
    thus "x \<in> under(minim A)" unfolding under_def by simp
  qed
  (*  *)
  moreover 
  (*  *)
  have "under (minim A) \<le> Under A"
  proof
    fix x assume "x \<in> under(minim A)"
    hence 11: "(x,minim A) \<in> r" unfolding under_def by simp
    hence "x \<in> Field r" unfolding Field_def by auto  
    moreover 
    {fix a assume "a \<in> A" 
     with 2 have "(minim A, a) \<in> r" by simp 
     with 11 have "(x,a) \<in> r" 
     using TRANS trans_def[of r] by blast
    }
    ultimately show "x \<in> Under A" by (unfold Under_def, auto)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed


lemma minim_UnderS_underS:
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "UnderS A = underS (minim A)"
proof-
  (* Preliminary facts *)
  have 1: "minim A \<in> A"  
  using assms minim_in by auto
  have 2: "\<forall>x \<in> A. (minim A, x) \<in> r" 
  using assms minim_least by auto
  (* Main proof *)
  have "UnderS A \<le> underS (minim A)"
  proof
    fix x assume "x \<in> UnderS A"
    with 1 UnderS_def have "x \<noteq> minim A \<and> (x,minim A) \<in> r" by auto
    thus "x \<in> underS(minim A)" unfolding underS_def by simp
  qed
  (*  *)
  moreover 
  (*  *)
  have "underS (minim A) \<le> UnderS A"
  proof
    fix x assume "x \<in> underS(minim A)"
    hence 11: "x \<noteq> minim A \<and> (x,minim A) \<in> r" unfolding underS_def by simp
    hence "x \<in> Field r" unfolding Field_def by auto  
    moreover 
    {fix a assume "a \<in> A" 
     with 2 have 3: "(minim A, a) \<in> r" by simp 
     with 11 have "(x,a) \<in> r" 
     using TRANS trans_def[of r] by blast
     moreover 
     have "x \<noteq> a"
     proof
       assume "x = a" 
       with 11 3 ANTISYM antisym_def[of r] 
       show False by auto
     qed 
     ultimately 
     have "x \<noteq> a \<and> (x,a) \<in> r" by simp
    }
    ultimately show "x \<in> UnderS A" by (unfold UnderS_def, auto)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed 



subsubsection{* Properties of supr *}


lemma supr_Above: 
assumes SUB: "B \<le> Field r" and ABOVE: "Above B \<noteq> {}" 
shows "supr B \<in> Above B"
proof(unfold supr_def) 
  have "Above B \<le> Field r" 
  using Above_Field by auto
  thus "minim (Above B) \<in> Above B"
  using assms by (auto simp add: minim_in)
qed
  


lemma supr_greater:
assumes SUB: "B \<le> Field r" and ABOVE: "Above B \<noteq> {}" and 
        IN: "b \<in> B" 
shows "(b, supr B) \<in> r"
proof- 
  from assms supr_Above
  have "supr B \<in> Above B" by simp 
  with IN Above_def show ?thesis by simp
qed


lemma supr_least_Above: 
assumes SUB: "B \<le> Field r" and  
        ABOVE: "a \<in> Above B" 
shows "(supr B, a) \<in> r"
proof(unfold supr_def) 
  have "Above B \<le> Field r" 
  using Above_Field by auto
  thus "(minim (Above B), a) \<in> r"
  using assms minim_least
  by simp
qed


lemma supr_least: 
"\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> (b,a) \<in> r)\<rbrakk> 
 \<Longrightarrow> (supr B, a) \<in> r"
by(auto simp add: supr_least_Above Above_def)


lemma equals_supr_Above:
assumes SUB: "B \<le> Field r" and ABV: "a \<in> Above B" and 
        MINIM: "\<And> a'. a' \<in> Above B \<Longrightarrow> (a,a') \<in> r" 
shows "a = supr B"
proof(unfold supr_def)
  have "Above B \<le> Field r" 
  using Above_Field by auto
  thus "a = minim (Above B)"
  using assms equals_minim by simp
qed


lemma equals_supr:
assumes SUB: "B \<le> Field r" and IN: "a \<in> Field r" and 
        ABV: "\<And> b. b \<in> B \<Longrightarrow> (b,a) \<in> r" and
        MINIM: "\<And> a'. \<lbrakk> a' \<in> Field r; \<And> b. b \<in> B \<Longrightarrow> (b,a') \<in> r\<rbrakk> \<Longrightarrow> (a,a') \<in> r" 
shows "a = supr B"
proof-
  have "a \<in> Above B" 
  unfolding Above_def using ABV IN by simp
  moreover    
  have "\<And> a'. a' \<in> Above B \<Longrightarrow> (a,a') \<in> r"
  unfolding Above_def using MINIM by simp
  ultimately show ?thesis 
  using equals_supr_Above SUB by auto
qed


lemma supr_inField:
assumes "B \<le> Field r" and  "Above B \<noteq> {}"
shows "supr B \<in> Field r"
proof-
  have "supr B \<in> Above B" using supr_Above assms by simp
  thus ?thesis using assms Above_Field by auto
qed


lemma supr_above_Above:
assumes SUB: "B \<le> Field r" and  ABOVE: "Above B \<noteq> {}"
shows "Above B = above (supr B)"
proof(unfold Above_def above_def, auto)
  fix a assume "a \<in> Field r" "\<forall>b \<in> B. (b,a) \<in> r"
  with supr_least assms 
  show "(supr B, a) \<in> r" by auto
next 
  fix b assume "(supr B, b) \<in> r" 
  thus "b \<in> Field r"
  using REFL refl_on_def[of _ r] by auto
next
  fix a b 
  assume 1: "(supr B, b) \<in> r" and 2: "a \<in> B" 
  with assms supr_greater  
  have "(a,supr B) \<in> r" by auto
  thus "(a,b) \<in> r"
  using 1 TRANS trans_def[of r] by blast
qed


lemma supr_under: 
assumes IN: "a \<in> Field r"
shows "a = supr (under a)"
proof-
  have "under a \<le> Field r" 
  using under_Field by auto 
  moreover 
  have "under a \<noteq> {}"
  using IN Refl_under_in REFL by auto
  moreover 
  have "a \<in> Above (under a)" 
  using in_Above_under IN by auto
  moreover 
  have "\<forall>a' \<in> Above (under a). (a,a') \<in> r"
  proof(unfold Above_def under_def, auto) 
    fix a'
    assume "\<forall>aa. (aa, a) \<in> r \<longrightarrow> (aa, a') \<in> r"
    hence "(a,a) \<in> r \<longrightarrow> (a,a') \<in> r" by blast
    moreover have "(a,a) \<in> r" 
    using REFL IN by (auto simp add: refl_on_def)
    ultimately 
    show  "(a, a') \<in> r" by (rule mp)
  qed
  ultimately show ?thesis 
  using equals_supr_Above by auto
qed


subsubsection{* Properties of successor *}


lemma suc_AboveS:
assumes SUB: "B \<le> Field r" and ABOVES: "AboveS B \<noteq> {}" 
shows "suc B \<in> AboveS B"
proof(unfold suc_def) 
  have "AboveS B \<le> Field r" 
  using AboveS_Field by auto
  thus "minim (AboveS B) \<in> AboveS B"
  using assms by (auto simp add: minim_in)
qed


lemma suc_greater: 
assumes SUB: "B \<le> Field r" and ABOVES: "AboveS B \<noteq> {}" and 
        IN: "b \<in> B"  
shows "suc B \<noteq> b \<and> (b,suc B) \<in> r"
proof- 
  from assms suc_AboveS
  have "suc B \<in> AboveS B" by simp 
  with IN AboveS_def show ?thesis by simp
qed


lemma suc_least_AboveS: 
assumes ABOVES: "a \<in> AboveS B" 
shows "(suc B,a) \<in> r"
proof(unfold suc_def) 
  have "AboveS B \<le> Field r" 
  using AboveS_Field by auto
  thus "(minim (AboveS B),a) \<in> r"
  using assms minim_least by simp
qed


lemma suc_least: 
"\<lbrakk>B \<le> Field r; a \<in> Field r; (\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r)\<rbrakk> 
 \<Longrightarrow> (suc B, a) \<in> r"
by(auto simp add: suc_least_AboveS AboveS_def)


lemma suc_inField:
assumes "B \<le> Field r" and "AboveS B \<noteq> {}"
shows "suc B \<in> Field r"
proof-
  have "suc B \<in> AboveS B" using suc_AboveS assms by simp
  thus ?thesis 
  using assms AboveS_Field by auto
qed


lemma equals_suc_AboveS:
assumes SUB: "B \<le> Field r" and ABV: "a \<in> AboveS B" and 
        MINIM: "\<And> a'. a' \<in> AboveS B \<Longrightarrow> (a,a') \<in> r" 
shows "a = suc B"
proof(unfold suc_def)
  have "AboveS B \<le> Field r" 
  using AboveS_Field[of B] by auto
  thus "a = minim (AboveS B)"
  using assms equals_minim 
  by simp
qed


lemma equals_suc:
assumes SUB: "B \<le> Field r" and IN: "a \<in> Field r" and 
 ABVS: "\<And> b. b \<in> B \<Longrightarrow> a \<noteq> b \<and> (b,a) \<in> r" and
 MINIM: "\<And> a'. \<lbrakk>a' \<in> Field r; \<And> b. b \<in> B \<Longrightarrow> a' \<noteq> b \<and> (b,a') \<in> r\<rbrakk> \<Longrightarrow> (a,a') \<in> r" 
shows "a = suc B"
proof-
  have "a \<in> AboveS B" 
  unfolding AboveS_def using ABVS IN by simp
  moreover    
  have "\<And> a'. a' \<in> AboveS B \<Longrightarrow> (a,a') \<in> r"
  unfolding AboveS_def using MINIM by simp
  ultimately show ?thesis 
  using equals_suc_AboveS SUB by auto
qed


lemma suc_above_AboveS:
assumes SUB: "B \<le> Field r" and 
        ABOVE: "AboveS B \<noteq> {}"
shows "AboveS B = above (suc B)"
proof(unfold AboveS_def above_def, auto)
  fix a assume "a \<in> Field r" "\<forall>b \<in> B. a \<noteq> b \<and> (b,a) \<in> r"
  with suc_least assms  
  show "(suc B,a) \<in> r" by auto
next
  fix b assume "(suc B, b) \<in> r" 
  thus "b \<in> Field r"
  using REFL refl_on_def[of _ r] by auto
next
  fix a b 
  assume 1: "(suc B, b) \<in> r" and 2: "a \<in> B" 
  with assms suc_greater[of B a] 
  have "(a,suc B) \<in> r" by auto
  thus "(a,b) \<in> r"
  using 1 TRANS trans_def[of r] by blast
next
  fix a 
  assume 1: "(suc B, a) \<in> r" and 2: "a \<in> B"
  with assms suc_greater[of B a] 
  have "(a,suc B) \<in> r" by auto
  moreover have "suc B \<in> Field r" 
  using assms suc_inField by simp
  ultimately have "a = suc B" 
  using 1 2 SUB ANTISYM antisym_def[of r] by auto
  thus False 
  using assms suc_greater[of B a] 2 by auto
qed


lemma suc_underS: 
assumes IN: "a \<in> Field r" 
shows "a = suc (underS a)"
proof-
  have "underS a \<le> Field r" 
  using underS_Field by auto
  moreover 
  have "a \<in> AboveS (underS a)" 
  using in_AboveS_underS IN by auto
  moreover 
  have "\<forall>a' \<in> AboveS (underS a). (a,a') \<in> r"
  proof(clarify)
    fix a'
    assume *: "a' \<in> AboveS (underS a)"
    hence **: "a' \<in> Field r" 
    using AboveS_Field by auto
    {assume "(a,a') \<notin> r"
     hence "a' = a \<or> (a',a) \<in> r" 
     using TOTAL IN ** by (auto simp add: total_on_def)
     moreover 
     {assume "a' = a"
      hence "(a,a') \<in> r" 
      using REFL IN ** by (auto simp add: refl_on_def)
     }
     moreover 
     {assume "a' \<noteq> a \<and> (a',a) \<in> r"
      hence "a' \<in> underS a" 
      unfolding underS_def by simp
      hence "a' \<notin> AboveS (underS a)" 
      using AboveS_disjoint by blast
      with * have False by simp 
     }
     ultimately have "(a,a') \<in> r" by blast
    } 
    thus  "(a, a') \<in> r" by blast
  qed
  ultimately show ?thesis 
  using equals_suc_AboveS by auto
qed


lemma suc_singl_pred: 
assumes IN: "a \<in> Field r" and ABOVE_NE: "aboveS a \<noteq> {}" and 
        REL: "(a',suc {a}) \<in> r" and DIFF: "a' \<noteq> suc {a}"
shows "a' = a \<or> (a',a) \<in> r"
proof-
  have *: "suc {a} \<in> Field r \<and> a' \<in> Field r" 
  using WELL REL well_order_on_domain by auto
  {assume **: "a' \<noteq> a"
   hence "(a,a') \<in> r \<or> (a',a) \<in> r"
   using TOTAL IN * by (auto simp add: total_on_def)
   moreover 
   {assume "(a,a') \<in> r"
    with ** * assms WELL suc_least[of "{a}" a'] 
    have "(suc {a},a') \<in> r" by auto
    with REL DIFF * ANTISYM antisym_def[of r] 
    have False by simp
   }
   ultimately have "(a',a) \<in> r"
   by blast
  }
  thus ?thesis by blast
qed


lemma under_underS_suc:
assumes IN: "a \<in> Field r" and ABV: "aboveS a \<noteq> {}"
shows "underS (suc {a}) = under a"
proof-
  have 1: "AboveS {a} \<noteq> {}" 
  using ABV aboveS_AboveS_singl by auto
  have 2: "a \<noteq> suc {a} \<and> (a,suc {a}) \<in> r" 
  using suc_greater[of "{a}" a] IN 1 by auto
  (*   *)
  have "underS (suc {a}) \<le> under a"
  proof(unfold underS_def under_def, auto)
    fix x assume *: "x \<noteq> suc {a}" and **: "(x,suc {a}) \<in> r" 
    with suc_singl_pred[of a x] IN ABV 
    have "x = a \<or> (x,a) \<in> r" by auto
    with REFL refl_on_def[of _ r] IN
    show "(x,a) \<in> r" by auto
  qed
  (*  *)
  moreover
  (*   *)
  have "under a \<le> underS (suc {a})"
  proof(unfold underS_def under_def, auto)
    assume "(suc {a}, a) \<in> r" 
    with 2 ANTISYM antisym_def[of r] 
    show False by auto
  next
    fix x assume *: "(x,a) \<in> r" 
    with 2 TRANS trans_def[of r]
    show "(x,suc {a}) \<in> r" by blast  
  (*  blast is often better than auto/auto for transitivity-like properties *)
  qed
  (*  *)
  ultimately show ?thesis by blast
qed



subsubsection {* Properties of order filters  *}


lemma under_ofilter:
"ofilter (under a)"
proof(unfold ofilter_def under_def, auto simp add: Field_def) 
  fix aa x 
  assume "(aa,a) \<in> r" "(x,aa) \<in> r"
  thus "(x,a) \<in> r"
  using TRANS trans_def[of r] by blast
qed


lemma underS_ofilter:
"ofilter (underS a)"
proof(unfold ofilter_def underS_def under_def, auto simp add: Field_def) 
  fix aa assume "(a, aa) \<in> r" "(aa, a) \<in> r" and DIFF: "aa \<noteq> a"
  thus False 
  using ANTISYM antisym_def[of r] by blast
next
  fix aa x 
  assume "(aa,a) \<in> r" "aa \<noteq> a" "(x,aa) \<in> r"
  thus "(x,a) \<in> r"
  using TRANS trans_def[of r] by blast
qed


lemma Field_ofilter:
"ofilter (Field r)"
by(unfold ofilter_def under_def, auto simp add: Field_def)


lemma ofilter_underS_Field:
"ofilter A = ((\<exists>a \<in> Field r. A = underS a) \<or> (A = Field r))"
proof
  assume "(\<exists>a\<in>Field r. A = underS a) \<or> A = Field r" 
  thus "ofilter A" 
  by (auto simp add: underS_ofilter Field_ofilter)
next
  assume *: "ofilter A"
  let ?One = "(\<exists>a\<in>Field r. A = underS a)" 
  let ?Two = "(A = Field r)"
  show "?One \<or> ?Two"
  proof(cases ?Two, simp)
    let ?B = "(Field r) - A"
    let ?a = "minim ?B"
    assume "A \<noteq> Field r" 
    moreover have "A \<le> Field r" using * ofilter_def by simp
    ultimately have 1: "?B \<noteq> {}" by blast
    hence 2: "?a \<in> Field r" using minim_inField[of ?B] by auto
    have 3: "?a \<in> ?B" using minim_in[of ?B] 1 by auto 
    hence 4: "?a \<notin> A" by blast
    have 5: "A \<le> Field r" using * ofilter_def[of A] by auto
    (*  *)
    moreover 
    have "A = underS ?a" 
    proof
      show "A \<le> underS ?a"
      proof(unfold underS_def, auto simp add: 4)
        fix x assume **: "x \<in> A" 
        hence 11: "x \<in> Field r" using 5 by auto
        have 12: "x \<noteq> ?a" using 4 ** by auto  
        have 13: "under x \<le> A" using * ofilter_def ** by auto
        {assume "(x,?a) \<notin> r" 
         hence "(?a,x) \<in> r" 
         using TOTAL total_on_def[of "Field r" r] 
               2 4 11 12 by auto
         hence "?a \<in> under x" using under_def by auto
         hence "?a \<in> A" using ** 13 by blast
         with 4 have False by simp
        } 
        thus "(x,?a) \<in> r" by blast
      qed
    next
      show "underS ?a \<le> A"
      proof(unfold underS_def, auto)
        fix x 
        assume **: "x \<noteq> ?a" and ***: "(x,?a) \<in> r"
        hence 11: "x \<in> Field r" using Field_def by fastsimp
         {assume "x \<notin> A" 
          hence "x \<in> ?B" using 11 by auto
          hence "(?a,x) \<in> r" using 3 minim_least[of ?B x] by auto
          hence False 
          using ANTISYM antisym_def[of r] ** *** by auto
         }
        thus "x \<in> A" by blast
      qed
    qed 
    ultimately have ?One using 2 by blast 
    thus ?thesis by simp
  qed
qed 

 
lemma ofilter_Under: 
assumes "A \<le> Field r"
shows "ofilter(Under A)"
proof(unfold ofilter_def, auto)
  fix x assume "x \<in> Under A" 
  thus "x \<in> Field r" 
  using Under_Field assms by auto
next
  fix a x 
  assume "a \<in> Under A" and "x \<in> under a" 
  thus "x \<in> Under A" 
  using TRANS under_Under_trans by auto
qed


lemma ofilter_UnderS: 
assumes "A \<le> Field r"
shows "ofilter(UnderS A)"
proof(unfold ofilter_def, auto)
  fix x assume "x \<in> UnderS A" 
  thus "x \<in> Field r" 
  using UnderS_Field assms by auto
next
  fix a x 
  assume "a \<in> UnderS A" and "x \<in> under a" 
  thus "x \<in> UnderS A" 
  using TRANS ANTISYM under_UnderS_trans by auto
qed


lemma ofilter_Int: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A Int B)"
unfolding ofilter_def by blast


lemma ofilter_INTER:
"\<lbrakk>I \<noteq> {}; \<And> i. i \<in> I \<Longrightarrow> ofilter(A i)\<rbrakk> \<Longrightarrow> ofilter (\<Inter> i \<in> I. A i)"
unfolding ofilter_def by blast


lemma ofilter_Inter:
"\<lbrakk>S \<noteq> {}; \<And> A. A \<in> S \<Longrightarrow> ofilter A\<rbrakk> \<Longrightarrow> ofilter (Inter S)"
unfolding ofilter_def by blast


lemma ofilter_Un: "\<lbrakk>ofilter A; ofilter B\<rbrakk> \<Longrightarrow> ofilter(A \<union> B)"
unfolding ofilter_def by blast


lemma ofilter_UNION:
"(\<And> i. i \<in> I \<Longrightarrow> ofilter(A i)) \<Longrightarrow> ofilter (\<Union> i \<in> I. A i)"
unfolding ofilter_def by blast


lemma ofilter_Union:
"(\<And> A. A \<in> S \<Longrightarrow> ofilter A) \<Longrightarrow> ofilter (Union S)"
unfolding ofilter_def by blast


lemma ofilter_under_UNION:
assumes "ofilter A"
shows "A = (\<Union> a \<in> A. under a)"
proof
  have "\<forall>a \<in> A. under a \<le> A" 
  using assms ofilter_def by auto
  thus "(\<Union> a \<in> A. under a) \<le> A" by blast
next
  have "\<forall>a \<in> A. a \<in> under a" 
  using REFL Refl_under_in assms ofilter_def by blast
  thus "A \<le> (\<Union> a \<in> A. under a)" by blast
qed


lemma ofilter_under_Union:
"ofilter A \<Longrightarrow> A = Union {under a| a. a \<in> A}"
using ofilter_under_UNION[of A]
by(unfold Union_def, auto)



subsubsection{* Other properties  *}


lemma Trans_Under_regressive: 
assumes NE: "A \<noteq> {}" and SUB: "A \<le> Field r"
shows "Under(Under A) \<le> Under A"
proof
  let ?a = "minim A"
  (*  Preliminary facts *)
  have 1: "minim A \<in> Under A"  
  using assms minim_Under by auto
  have 2: "\<forall>y \<in> A. (minim A, y) \<in> r" 
  using assms minim_least by auto
  (* Main proof *)
  fix x assume "x \<in> Under(Under A)"
  with 1 have 1: "(x,minim A) \<in> r" 
  using Under_def by auto
  with Field_def have "x \<in> Field r" by fastsimp
  moreover
  {fix y assume *: "y \<in> A"
   hence "(x,y) \<in> r"
   using 1 2 TRANS trans_def[of r] by blast
   with Field_def have "(x,y) \<in> r" by auto
  }
  ultimately 
  show "x \<in> Under A" unfolding Under_def by auto
qed


lemma ofilter_linord:
assumes OF1: "ofilter A" and OF2: "ofilter B"
shows "A \<le> B \<or> B \<le> A"
proof(cases "A = Field r")
  assume Case1: "A = Field r" 
  hence "B \<le> A" using OF2 ofilter_def by auto
  thus ?thesis by simp
next
  assume Case2: "A \<noteq> Field r" 
  with ofilter_underS_Field OF1 obtain a where 
  1: "a \<in> Field r \<and> A = underS a" by auto
  show ?thesis
  proof(cases "B = Field r")
    assume Case21: "B = Field r" 
    hence "A \<le> B" using OF1 ofilter_def by auto
    thus ?thesis by simp
  next 
    assume Case22: "B \<noteq> Field r" 
    with ofilter_underS_Field OF2 obtain b where 
    2: "b \<in> Field r \<and> B = underS b" by auto
    have "a = b \<or> (a,b) \<in> r \<or> (b,a) \<in> r" 
    using 1 2 TOTAL total_on_def[of _ r] by auto
    moreover
    {assume "a = b" with 1 2 have ?thesis by auto
    }
    moreover
    {assume "(a,b) \<in> r"
     with underS_incr TRANS ANTISYM 1 2
     have "A \<le> B" by auto
     hence ?thesis by auto
    }
    moreover
     {assume "(b,a) \<in> r"
     with underS_incr TRANS ANTISYM 1 2
     have "B \<le> A" by auto
     hence ?thesis by auto
    }
    ultimately show ?thesis by blast
  qed
qed


lemma ofilter_AboveS_Field: 
assumes "ofilter A"
shows "A \<union> (AboveS A) = Field r"
proof
  show "A \<union> (AboveS A) \<le> Field r" 
  using assms ofilter_def AboveS_Field by auto
next
  {fix x assume *: "x \<in> Field r" and **: "x \<notin> A"
   {fix y assume ***: "y \<in> A"
    with ** have 1: "y \<noteq> x" by auto
    {assume "(y,x) \<notin> r"
     moreover 
     have "y \<in> Field r" using assms ofilter_def *** by auto
     ultimately have "(x,y) \<in> r"  
     using 1 * TOTAL total_on_def[of _ r] by auto
     with *** assms ofilter_def under_def have "x \<in> A" by auto
     with ** have False by contradiction
    }
    hence "(y,x) \<in> r" by blast 
    with 1 have "y \<noteq> x \<and> (y,x) \<in> r" by auto
   }
   with * have "x \<in> AboveS A" unfolding AboveS_def by auto
  }
  thus "Field r \<le> A \<union> (AboveS A)" by blast
qed


lemma ofilter_suc_Field:  
assumes OF: "ofilter A" and NE: "A \<noteq> Field r"
shows "ofilter (A \<union> {suc A})"
proof-
  (* Preliminary facts *)
  have 1: "A \<le> Field r" using OF ofilter_def by auto
  hence 2: "AboveS A \<noteq> {}" 
  using ofilter_AboveS_Field NE OF by blast
  from 1 2 suc_inField 
  have 3: "suc A \<in> Field r" by auto
  (* Main proof *)
  show ?thesis
  proof(unfold ofilter_def, auto simp add: 1 3)
    fix a x 
    assume "a \<in> A" "x \<in> under a" "x \<notin> A"
    with OF ofilter_def have False by auto
    thus "x = suc A" by simp
  next
    fix x assume *: "x \<in> under (suc A)" and **: "x \<notin> A"
    hence "x \<in> Field r" using under_def Field_def by fastsimp
    with ** have "x \<in> AboveS A" 
    using ofilter_AboveS_Field[of A] OF by auto
    hence "(suc A,x) \<in> r" 
    using suc_least_AboveS by auto
    moreover 
    have "(x,suc A) \<in> r" using * under_def by auto
    ultimately show "x = suc A"  
    using ANTISYM antisym_def[of r] by auto
  qed
qed


lemma suc_ofilter_in: 
assumes OF: "ofilter A" and ABOVE_NE: "AboveS A \<noteq> {}" and 
        REL: "(b,suc A) \<in> r" and DIFF: "b \<noteq> suc A"         
shows "b \<in> A"
proof-
  have *: "suc A \<in> Field r \<and> b \<in> Field r" 
  using WELL REL well_order_on_domain by auto
  {assume **: "b \<notin> A"
   hence "b \<in> AboveS A" 
   using OF * ofilter_AboveS_Field by auto
   hence "(suc A, b) \<in> r" 
   using suc_least_AboveS by auto
   hence False using REL DIFF ANTISYM *
   by (auto simp add: antisym_def) 
  }
  thus ?thesis by blast
qed



end (* context wo_rell  *)



abbreviation "worec \<equiv> wo_rel.worec"
abbreviation "adm_wo \<equiv> wo_rel.adm_wo"
abbreviation "isMinim \<equiv> wo_rel.isMinim"
abbreviation "minim \<equiv> wo_rel.minim"
abbreviation "max2 \<equiv> wo_rel.max2"
abbreviation "supr \<equiv> wo_rel.supr"
abbreviation "suc \<equiv> wo_rel.suc"
abbreviation "ofilter \<equiv> wo_rel.ofilter"



end





