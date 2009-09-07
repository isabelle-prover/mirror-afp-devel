header {* Basics on order-like relations *}


theory Order_Relation2 imports Order_Relation
begin


text{* In this section, we develop basic concepts and results pertaining 
to order-like relations, i.e., to reflexive and/or transitive and/or symmetric and/or 
total relations.  The development is placed on top of the definitions 
from the theory @{text "Order_Relation"}.  We also further define upper and lower bounds operators. *}


types 'a rel = "('a * 'a) set"

locale rel = fixes r :: "'a rel"

text{* The following context encompasses all this section, except 
for its last subsection. In other words, for the rest of this section except its last 
subsection, we consider a fixed relation @{text "r"}. *}

context rel 
begin


subsection {* Auxiliaries *}


lemma refl_on_domain:
"\<lbrakk>refl_on A r; (a,b) : r\<rbrakk> \<Longrightarrow> a \<in> A \<and> b \<in> A"
by(auto simp add: refl_on_def)


corollary well_order_on_domain:
"\<lbrakk>well_order_on A r; (a,b) \<in> r\<rbrakk> \<Longrightarrow> a \<in> A \<and> b \<in> A"
by(auto simp add: refl_on_domain order_on_defs)


lemma well_order_on_Field:
"well_order_on A r \<Longrightarrow> A = Field r"  
by(auto simp add: refl_on_def Field_def order_on_defs)


lemma well_order_on_Well_order:
"well_order_on A r \<Longrightarrow> A = Field r \<and> Well_order r"
using well_order_on_Field by auto


lemma Total_Id_Field:
assumes TOT: "Total r" and NID: "\<not> (r <= Id)" 
shows "Field r = Field(r - Id)"
using mono_Field[of "r - Id" r] Diff_subset[of r Id]
proof(auto)
  have "r \<noteq> {}" using NID by auto
  then obtain b and c where "b \<noteq> c \<and> (b,c) \<in> r" using NID by auto
  hence 1: "b \<noteq> c \<and> {b,c} \<le> Field r" unfolding Field_def by auto
  (*  *)
  fix a assume *: "a \<in> Field r"
  obtain d where 2: "d \<in> Field r" and 3: "d \<noteq> a" 
  using * 1 by blast
  hence "(a,d) \<in> r \<or> (d,a) \<in> r" using * TOT 
  by (auto simp add: total_on_def)
  thus "a \<in> Field(r - Id)" using 3 unfolding Field_def by blast
qed


lemma Total_subset_Id: 
assumes TOT: "Total r" and SUB: "r \<le> Id"
shows "r = {} \<or> (\<exists>a. r = {(a,a)})"
proof-
  {assume "r \<noteq> {}"
   then obtain a b where 1: "(a,b) \<in> r" by auto
   hence "a = b" using SUB by blast
   hence 2: "(a,a) \<in> r" using 1 by auto
   {fix c d assume "(c,d) \<in> r" 
    hence "{a,c,d} \<le> Field r" using 1 unfolding Field_def by auto
    hence "((a,c) \<in> r \<or> (c,a) \<in> r \<or> a = c) \<and> 
           ((a,d) \<in> r \<or> (d,a) \<in> r \<or> a = d)" 
    using TOT unfolding total_on_def by auto
    hence "a = c \<and> a = d" using SUB by blast
   }
   hence "r \<le> {(a,a)}" by auto
   with 2 have "\<exists>a. r = {(a,a)}" by blast
  }
  thus ?thesis by auto
qed


lemma Linear_order_in_diff_Id:
assumes LI: "Linear_order r" and 
        IN1: "a \<in> Field r" and IN2: "b \<in> Field r"
shows "((a,b) \<in> r) = ((b,a) \<notin> r - Id)"
using assms unfolding order_on_defs total_on_def antisym_def Id_def refl_on_def by force
 (* Here "fastsimp" works too, but is slower than "force". *)


subsection {* The upper and lower bounds operators  *} 


text{* Here we define upper (``above") and lower (``below") bounds operators. 
We think of @{text "r"} as a {\em non-strict} relation.  The suffix ``S" 
at the names of some operators indicates that the bounds are strict -- e.g., 
@{text "underS a"} is the set of all strict lower bounds of @{text "a"} (w.r.t. @{text "r"}). 
Capitalization of the first letter in the name reminds that the operator acts on sets, rather 
than on individual elements. *}

definition under::"'a \<Rightarrow> 'a set"
where "under a \<equiv> {b. (b,a) \<in> r}"

definition underS::"'a \<Rightarrow> 'a set"
where "underS a \<equiv> {b. b \<noteq> a \<and> (b,a) \<in> r}"

definition Under::"'a set \<Rightarrow> 'a set"
where "Under A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (b,a) \<in> r}"

definition UnderS::"'a set \<Rightarrow> 'a set"
where "UnderS A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (b,a) \<in> r}"

definition above::"'a \<Rightarrow> 'a set"
where "above a \<equiv> {b. (a,b) \<in> r}"

definition aboveS::"'a \<Rightarrow> 'a set"
where "aboveS a \<equiv> {b. b \<noteq> a \<and> (a,b) \<in> r}"

definition Above::"'a set \<Rightarrow> 'a set"
where "Above A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (a,b) \<in> r}"

definition AboveS::"'a set \<Rightarrow> 'a set"
where "AboveS A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (a,b) \<in> r}"
(*  *)

text{* Note:  In the definitions of @{text "Above[S]"} and @{text "Under[S]"}, 
  we bounded comprehension by @{text "Field r"} in order to properly cover 
  the case of @{text "A"} being empty. *}


lemma underS_subset_under: "underS a \<le> under a"
by(auto simp add: underS_def under_def)


lemma UnderS_subset_Under: "UnderS A \<le> Under A"
by(auto simp add: UnderS_def Under_def)


lemma aboveS_subset_above: "aboveS a \<le> above a"
by(auto simp add: aboveS_def above_def)


lemma AboveS_subset_Above: "AboveS A \<le> Above A"
by(auto simp add: AboveS_def Above_def)


lemma underS_notIn: "a \<notin> underS a"
by(auto simp add: underS_def)


lemma Refl_under_in: "\<lbrakk>Refl r; a \<in> Field r\<rbrakk> \<Longrightarrow> a \<in> under a"
by(auto simp add: refl_on_def under_def)


lemma UnderS_disjoint: "A Int (UnderS A) = {}"
by(auto simp add: UnderS_def)


lemma aboveS_notIn: "a \<notin> aboveS a"
by(auto simp add: aboveS_def)


lemma AboveS_disjoint: "A Int (AboveS A) = {}"
by(auto simp add: AboveS_def)


lemma Refl_above_in: "\<lbrakk>Refl r; a \<in> Field r\<rbrakk> \<Longrightarrow> a \<in> above a"
by(auto simp add: refl_on_def above_def)


lemma in_Above_under: "a \<in> Field r \<Longrightarrow> a \<in> Above (under a)"
by(auto simp add: Above_def under_def)


lemma in_Under_above: "a \<in> Field r \<Longrightarrow> a \<in> Under (above a)"
by(auto simp add: Under_def above_def)


lemma in_AboveS_underS: "a \<in> Field r \<Longrightarrow> a \<in> AboveS (underS a)"
by(auto simp add: AboveS_def underS_def)


lemma in_UnderS_aboveS: "a \<in> Field r \<Longrightarrow> a \<in> UnderS (aboveS a)"
by(auto simp add: UnderS_def aboveS_def)


lemma subset_Above_Under: "B \<le> Field r \<Longrightarrow> B \<le> Above (Under B)"
by(auto simp add: Above_def Under_def)


lemma subset_Under_Above: "B \<le> Field r \<Longrightarrow> B \<le> Under (Above B)"
by(auto simp add: Under_def Above_def)


lemma subset_AboveS_UnderS: "B \<le> Field r \<Longrightarrow> B \<le> AboveS (UnderS B)"
by(auto simp add: AboveS_def UnderS_def)


lemma subset_UnderS_AboveS: "B \<le> Field r \<Longrightarrow> B \<le> UnderS (AboveS B)"
by(auto simp add: UnderS_def AboveS_def)


lemma Under_Above_Galois: 
"\<lbrakk>B \<le> Field r; C \<le> Field r\<rbrakk> \<Longrightarrow> (B \<le> Above C) = (C \<le> Under B)"
by(unfold Above_def Under_def, blast)


lemma UnderS_AboveS_Galois: 
"\<lbrakk>B \<le> Field r; C \<le> Field r\<rbrakk> \<Longrightarrow> (B \<le> AboveS C) = (C \<le> UnderS B)"
by(unfold AboveS_def UnderS_def, blast)


lemma Refl_under_underS:
assumes REFL: "Refl r" and IN: "a \<in> Field r"
shows "under a = underS a \<union> {a}"
proof(unfold under_def underS_def, auto)
  show "(a,a) \<in> r" using REFL IN refl_on_def[of _ r] by blast
qed


lemma Refl_above_aboveS:
assumes REFL: "Refl r" and IN: "a \<in> Field r"
shows "above a = aboveS a \<union> {a}"
proof(unfold above_def aboveS_def, auto)
  show "(a,a) \<in> r" using REFL IN refl_on_def[of _ r] by blast
qed


lemma Linear_order_under_aboveS_Field:
assumes LIN: "Linear_order r" and IN: "a \<in> Field r"
shows "Field r = under a \<union> aboveS a"
proof(unfold under_def aboveS_def, auto)
  assume "a \<in> Field r" "(a, a) \<notin> r" 
  with LIN IN order_on_defs[of _ r] refl_on_def[of _ r]
  show False by auto
next
  fix b assume "b \<in> Field r" "(b, a) \<notin> r" 
  with LIN IN order_on_defs[of "Field r" r] total_on_def[of "Field r" r]
  have "(a,b) \<in> r \<or> a = b" by blast
  thus "(a,b) \<in> r" 
  using LIN IN order_on_defs[of _ r] refl_on_def[of _ r] by auto
next
  fix b assume "(b, a) \<in> r" 
  thus "b \<in> Field r" 
  using LIN order_on_defs[of _ r] refl_on_def[of _ r] by blast
next
  fix b assume "b \<noteq> a" "(a, b) \<in> r" 
  thus "b \<in> Field r" 
  using LIN order_on_defs[of "Field r" r] refl_on_def[of "Field r" r] by blast
qed


lemma Linear_order_underS_above_Field:
assumes LIN: "Linear_order r" and IN: "a \<in> Field r"
shows "Field r = underS a \<union> above a"
proof(unfold underS_def above_def, auto)
  assume "a \<in> Field r" "(a, a) \<notin> r" 
  with LIN IN order_on_defs[of _ r] refl_on_def[of _ r]
  show False by auto
next
  fix b assume "b \<in> Field r" "(a, b) \<notin> r" 
  with LIN IN order_on_defs[of "Field r" r] total_on_def[of "Field r" r]
  have "(b,a) \<in> r \<or> b = a" by blast
  thus "(b,a) \<in> r" 
  using LIN IN order_on_defs[of _ r] refl_on_def[of _ r] by auto
next
  fix b assume "b \<noteq> a" "(b, a) \<in> r" 
  thus "b \<in> Field r" 
  using LIN order_on_defs[of _ r] refl_on_def[of _ r] by blast
next
  fix b assume "(a, b) \<in> r" 
  thus "b \<in> Field r" 
  using LIN order_on_defs[of "Field r" r] refl_on_def[of "Field r" r] by blast
qed


lemma under_empty: "a \<notin> Field r \<Longrightarrow> under a = {}"
unfolding Field_def under_def by auto


lemma underS_empty: "a \<notin> Field r \<Longrightarrow> underS a = {}"
unfolding Field_def underS_def by auto


lemma under_Field: "under a \<le> Field r"
by(unfold under_def Field_def, auto)


lemma underS_Field: "underS a \<le> Field r"
by(unfold underS_def Field_def, auto)


lemma underS_Field2: 
"a \<in> Field r \<Longrightarrow> underS a < Field r"
using assms underS_notIn underS_Field by blast


lemma underS_Field3: 
"Field r \<noteq> {} \<Longrightarrow> underS a < Field r"
by(cases "a \<in> Field r", simp add: underS_Field2, 
                        auto simp add: underS_empty)


lemma Under_Field: "Under A \<le> Field r"
by(unfold Under_def Field_def, auto)


lemma UnderS_Field: "UnderS A \<le> Field r"
by(unfold UnderS_def Field_def, auto)


lemma above_Field: "above a \<le> Field r"
by(unfold above_def Field_def, auto)


lemma aboveS_Field: "aboveS a \<le> Field r"
by(unfold aboveS_def Field_def, auto)


lemma Above_Field: "Above A \<le> Field r"
by(unfold Above_def Field_def, auto)


lemma AboveS_Field: "AboveS A \<le> Field r"
by(unfold AboveS_def Field_def, auto)


lemma Refl_under_Under: 
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "Under A = (\<Inter> a \<in> A. under a)"
proof
  show "Under A \<subseteq> (\<Inter> a \<in> A. under a)" 
  by(unfold Under_def under_def, auto)
next
  show "(\<Inter> a \<in> A. under a) \<subseteq> Under A"
  proof(auto)
    fix x 
    assume *: "\<forall>xa \<in> A. x \<in> under xa"
    hence "\<forall>xa \<in> A. (x,xa) \<in> r" 
    by (simp add: under_def)
    moreover 
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> under a" by simp
     hence "x \<in> Field r" 
     using under_Field[of a] by auto
    }
    ultimately show "x \<in> Under A" 
    unfolding Under_def by auto
  qed
qed


lemma Refl_underS_UnderS: 
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "UnderS A = (\<Inter> a \<in> A. underS a)"
proof
  show "UnderS A \<subseteq> (\<Inter> a \<in> A. underS a)" 
  by(unfold UnderS_def underS_def, auto)
next
  show "(\<Inter> a \<in> A. underS a) \<subseteq> UnderS A"
  proof(auto)
    fix x 
    assume *: "\<forall>xa \<in> A. x \<in> underS xa"
    hence "\<forall>xa \<in> A. x \<noteq> xa \<and> (x,xa) \<in> r" 
    by (auto simp add: underS_def)
    moreover 
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> underS a" by simp
     hence "x \<in> Field r" 
     using underS_Field[of a] by auto
    }
    ultimately show "x \<in> UnderS A" 
    unfolding UnderS_def by auto
  qed
qed


lemma Refl_above_Above: 
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "Above A = (\<Inter> a \<in> A. above a)"
proof
  show "Above A \<subseteq> (\<Inter> a \<in> A. above a)" 
  by(unfold Above_def above_def, auto)
next
  show "(\<Inter> a \<in> A. above a) \<subseteq> Above A"
  proof(auto)
    fix x 
    assume *: "\<forall>xa \<in> A. x \<in> above xa"
    hence "\<forall>xa \<in> A. (xa,x) \<in> r" 
    by (simp add: above_def)
    moreover 
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> above a" by simp
     hence "x \<in> Field r" 
     using above_Field[of a] by auto
    }
    ultimately show "x \<in> Above A" 
    unfolding Above_def by auto
  qed
qed


lemma Refl_aboveS_AboveS: 
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "AboveS A = (\<Inter> a \<in> A. aboveS a)"
proof
  show "AboveS A \<subseteq> (\<Inter> a \<in> A. aboveS a)" 
  by(unfold AboveS_def aboveS_def, auto)
next
  show "(\<Inter> a \<in> A. aboveS a) \<subseteq> AboveS A"
  proof(auto)
    fix x 
    assume *: "\<forall>xa \<in> A. x \<in> aboveS xa"
    hence "\<forall>xa \<in> A. xa \<noteq> x \<and> (xa,x) \<in> r" 
    by (auto simp add: aboveS_def)
    moreover 
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> aboveS a" by simp
     hence "x \<in> Field r" 
     using aboveS_Field[of a] by auto
    }
    ultimately show "x \<in> AboveS A" 
    unfolding AboveS_def by auto
  qed
qed


lemma under_Under_singl: "under a = Under {a}"
by(unfold Under_def under_def, auto simp add: Field_def)


lemma underS_UnderS_singl: "underS a = UnderS {a}"
by(unfold UnderS_def underS_def, auto simp add: Field_def)


lemma above_Above_singl: "above a = Above {a}"
by(unfold Above_def above_def, auto simp add: Field_def)


lemma aboveS_AboveS_singl: "aboveS a = AboveS {a}"
by(unfold AboveS_def aboveS_def, auto simp add: Field_def)


lemma Under_decr: "A \<le> B \<Longrightarrow> Under B \<le> Under A"
by(unfold Under_def, auto)


lemma UnderS_decr: "A \<le> B \<Longrightarrow> UnderS B \<le> UnderS A"
by(unfold UnderS_def, auto)


lemma Above_decr: "A \<le> B \<Longrightarrow> Above B \<le> Above A"
by(unfold Above_def, auto)


lemma AboveS_decr: "A \<le> B \<Longrightarrow> AboveS B \<le> AboveS A"
by(unfold AboveS_def, auto)


lemma under_incr: 
assumes TRANS: "trans r" and REL: "(a,b) \<in> r" 
shows "under a \<le> under b"
proof(unfold under_def, auto)
  fix x assume "(x,a) \<in> r" 
  with REL TRANS trans_def[of r] 
  show "(x,b) \<in> r" by blast
qed


lemma under_incl_iff: 
assumes TRANS: "trans r" and REFL: "Refl r" and IN: "a \<in> Field r"
shows "(under a \<le> under b) = ((a,b) \<in> r)"
proof
  assume "(a,b) \<in> r"
  thus "under a \<le> under b" using TRANS
  by (auto simp add: under_incr)
next
  assume "under a \<le> under b" 
  moreover 
  have "a \<in> under a" using REFL IN   
  by (auto simp add: Refl_under_in)
  ultimately show "(a,b) \<in> r" 
  by (auto simp add: under_def)
qed


lemma underS_incr: 
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        REL: "(a,b) \<in> r" 
shows "underS a \<le> underS b"
proof(unfold underS_def, auto)
  assume *: "b \<noteq> a" and **: "(b,a) \<in> r"
  with ANTISYM antisym_def[of r] REL 
  show False by auto
next
  fix x assume "x \<noteq> a" "(x,a) \<in> r" 
  with REL TRANS trans_def[of r] 
  show "(x,b) \<in> r" by blast
qed


lemma underS_incl_iff: 
assumes LO: "Linear_order r" and 
        INa: "a \<in> Field r" and INb: "b \<in> Field r"
shows "(underS a \<le> underS b) = ((a,b) \<in> r)"
proof
  assume "(a,b) \<in> r"
  thus "underS a \<le> underS b" using LO
  by (auto simp add: order_on_defs underS_incr)
next
  assume *: "underS a \<le> underS b" 
  {assume "a = b"
   hence "(a,b) \<in> r" using assms
   by (auto simp add: order_on_defs refl_on_def)
  }
  moreover
  {assume "a \<noteq> b \<and> (b,a) \<in> r"
   hence "b \<in> underS a" unfolding underS_def by auto
   hence "b \<in> underS b" using * by auto
   hence False by (auto simp add: underS_notIn)
  }
  ultimately 
  show "(a,b) \<in> r" using assms
  order_on_defs[of "Field r" r] total_on_def[of "Field r" r] by blast
qed


lemma above_decr: 
assumes TRANS: "trans r" and REL: "(a,b) \<in> r" 
shows "above b \<le> above a"
proof(unfold above_def, auto)
  fix x assume "(b,x) \<in> r" 
  with REL TRANS trans_def[of r] 
  show "(a,x) \<in> r" by blast
qed


lemma aboveS_decr: 
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        REL: "(a,b) \<in> r" 
shows "aboveS b \<le> aboveS a"
proof(unfold aboveS_def, auto)
  assume *: "a \<noteq> b" and **: "(b,a) \<in> r"
  with ANTISYM antisym_def[of r] REL 
  show False by auto
next
  fix x assume "x \<noteq> b" "(b,x) \<in> r" 
  with REL TRANS trans_def[of r] 
  show "(a,x) \<in> r" by blast
qed


lemma under_trans:
assumes TRANS: "trans r" and 
        IN1: "a \<in> under b" and IN2: "b \<in> under c" 
shows "a \<in> under c"
proof- 
  have "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def by auto
  hence "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  thus ?thesis unfolding under_def by simp
qed


lemma under_underS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "a \<in> under b" and IN2: "b \<in> underS c" 
shows "a \<in> underS c"
proof- 
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def underS_def by auto
  hence 1: "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  have 2: "b \<noteq> c" using IN2 underS_def by auto
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r] 
    show False by auto
  qed 
  from 1 3 show ?thesis unfolding underS_def by simp
qed


lemma underS_under_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "a \<in> underS b" and IN2: "b \<in> under c" 
shows "a \<in> underS c"
proof- 
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def underS_def by auto
  hence 1: "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  have 2: "a \<noteq> b" using IN1 underS_def by auto
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r] 
    show False by auto
  qed 
  from 1 3 show ?thesis unfolding underS_def by simp
qed


lemma underS_underS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "a \<in> underS b" and IN2: "b \<in> underS c" 
shows "a \<in> underS c"
proof-
  have "a \<in> under b" 
  using IN1 underS_subset_under by auto
  with assms under_underS_trans show ?thesis by auto
qed



lemma above_trans:
assumes TRANS: "trans r" and 
        IN1: "b \<in> above a" and IN2: "c \<in> above b" 
shows "c \<in> above a"
proof- 
  have "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def by auto
  hence "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  thus ?thesis unfolding above_def by simp
qed


lemma above_aboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "b \<in> above a" and IN2: "c \<in> aboveS b" 
shows "c \<in> aboveS a"
proof- 
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def aboveS_def by auto
  hence 1: "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  have 2: "b \<noteq> c" using IN2 aboveS_def by auto
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r] 
    show False by auto
  qed 
  from 1 3 show ?thesis unfolding aboveS_def by simp
qed


lemma aboveS_above_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "b \<in> aboveS a" and IN2: "c \<in> above b" 
shows "c \<in> aboveS a"
proof- 
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def aboveS_def by auto
  hence 1: "(a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  have 2: "a \<noteq> b" using IN1 aboveS_def by auto
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r] 
    show False by auto
  qed 
  from 1 3 show ?thesis unfolding aboveS_def by simp
qed


lemma aboveS_aboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
        IN1: "b \<in> aboveS a" and IN2: "c \<in> aboveS b" 
shows "c \<in> aboveS a"
proof-
  have "b \<in> above a" 
  using IN1 aboveS_subset_above by auto
  with assms above_aboveS_trans show ?thesis by auto
qed


lemma under_Under_trans:
assumes TRANS: "trans r" and 
       IN1: "a \<in> under b" and IN2: "b \<in> Under C"
shows "a \<in> Under C" 
proof- 
  have "(a,b) \<in> r \<and> (\<forall>c \<in> C. (b,c) \<in> r)"
  using IN1 IN2 under_def Under_def by auto
  hence "\<forall>c \<in> C. (a,c) \<in> r" 
  using TRANS trans_def[of r] by blast
  moreover 
  have "a \<in> Field r" using IN1 Field_def under_def by force
  ultimately 
  show ?thesis unfolding Under_def by auto
qed


lemma underS_Under_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> underS b" and IN2: "b \<in> Under C"
shows "a \<in> UnderS C"
proof- 
  from IN1 have "a \<in> under b" 
  using underS_subset_under[of b] by blast
  with assms under_Under_trans 
  have "a \<in> Under C" by auto
  (*  *)
  moreover 
  have "a \<notin> C"
  proof
    assume *: "a \<in> C" 
    have 1: "b \<noteq> a \<and> (a,b) \<in> r" 
    using IN1 underS_def[of b] by auto
    have "\<forall>c \<in> C. (b,c) \<in> r" 
    using IN2 Under_def[of C] by auto
    with * have "(b,a) \<in> r" by simp 
    with 1 ANTISYM antisym_def[of r] 
    show False by blast
  qed 
  (*  *)
  ultimately 
  show ?thesis unfolding UnderS_def 
  using Under_def by auto
qed


lemma under_UnderS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> under b" and IN2: "b \<in> UnderS C"
shows "a \<in> UnderS C"
proof- 
  from IN2 have "b \<in> Under C" 
  using UnderS_subset_Under[of C] by blast
  with assms under_Under_trans 
  have "a \<in> Under C" by auto
  (*  *)
  moreover 
  have "a \<notin> C"
  proof
    assume *: "a \<in> C" 
    have 1: "(a,b) \<in> r" 
    using IN1 under_def[of b] by auto
    have "\<forall>c \<in> C. b \<noteq> c \<and> (b,c) \<in> r" 
    using IN2 UnderS_def[of C] by auto
    with * have "b \<noteq> a \<and> (b,a) \<in> r" by simp 
    with 1 ANTISYM antisym_def[of r] 
    show False by blast
  qed 
  (*  *)
  ultimately 
  show ?thesis unfolding UnderS_def 
  using Under_def by auto
qed


lemma underS_UnderS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> underS b" and IN2: "b \<in> UnderS C"
shows "a \<in> UnderS C"
proof-
  from IN2 have "b \<in> Under C" 
  using UnderS_subset_Under[of C] by blast
  with underS_Under_trans assms  
  show ?thesis by auto
qed


lemma above_Above_trans:
assumes TRANS: "trans r" and 
       IN1: "a \<in> above b" and IN2: "b \<in> Above C"
shows "a \<in> Above C" 
proof- 
  have "(b,a) \<in> r \<and> (\<forall>c \<in> C. (c,b) \<in> r)"
  using IN1 IN2 above_def Above_def by auto
  hence "\<forall>c \<in> C. (c,a) \<in> r" 
  using TRANS trans_def[of r] by blast
  moreover 
  have "a \<in> Field r" using IN1 Field_def above_def by force
  ultimately 
  show ?thesis unfolding Above_def by auto
qed


lemma aboveS_Above_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> aboveS b" and IN2: "b \<in> Above C"
shows "a \<in> AboveS C"
proof- 
  from IN1 have "a \<in> above b" 
  using aboveS_subset_above[of b] by blast
  with assms above_Above_trans 
  have "a \<in> Above C" by auto
  (*  *)
  moreover 
  have "a \<notin> C"
  proof
    assume *: "a \<in> C" 
    have 1: "b \<noteq> a \<and> (b,a) \<in> r" 
    using IN1 aboveS_def[of b] by auto
    have "\<forall>c \<in> C. (c,b) \<in> r" 
    using IN2 Above_def[of C] by auto
    with * have "(a,b) \<in> r" by simp 
    with 1 ANTISYM antisym_def[of r] 
    show False by blast
  qed 
  (*  *)
  ultimately 
  show ?thesis unfolding AboveS_def 
  using Above_def by auto
qed


lemma above_AboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> above b" and IN2: "b \<in> AboveS C"
shows "a \<in> AboveS C"
proof- 
  from IN2 have "b \<in> Above C" 
  using AboveS_subset_Above[of C] by blast
  with assms above_Above_trans 
  have "a \<in> Above C" by auto
  (*  *)
  moreover 
  have "a \<notin> C"
  proof
    assume *: "a \<in> C" 
    have 1: "(b,a) \<in> r" 
    using IN1 above_def[of b] by auto
    have "\<forall>c \<in> C. b \<noteq> c \<and> (c,b) \<in> r" 
    using IN2 AboveS_def[of C] by auto
    with * have "b \<noteq> a \<and> (a,b) \<in> r" by simp 
    with 1 ANTISYM antisym_def[of r] 
    show False by blast
  qed 
  (*  *)
  ultimately 
  show ?thesis unfolding AboveS_def 
  using Above_def by auto
qed


lemma aboveS_AboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and 
       IN1: "a \<in> aboveS b" and IN2: "b \<in> AboveS C"
shows "a \<in> AboveS C"
proof-
  from IN2 have "b \<in> Above C" 
  using AboveS_subset_Above[of C] by blast
  with aboveS_Above_trans assms  
  show ?thesis by auto
qed


end  (* context rel *)



subsection {* Properties depending on more than one relation  *}


abbreviation "under \<equiv> rel.under"
abbreviation "underS \<equiv> rel.underS"
abbreviation "Under \<equiv> rel.Under"
abbreviation "UnderS \<equiv> rel.UnderS"
abbreviation "above \<equiv> rel.above"
abbreviation "aboveS \<equiv> rel.aboveS"
abbreviation "Above \<equiv> rel.Above"
abbreviation "AboveS \<equiv> rel.AboveS"


lemma under_incr2:
"r \<le> r' \<Longrightarrow> under r a \<le> under r' a"
unfolding rel.under_def by blast


lemma underS_incr2:
"r \<le> r' \<Longrightarrow> underS r a \<le> underS r' a"
unfolding rel.underS_def by blast


lemma Under_incr:
"r \<le> r' \<Longrightarrow> Under r A \<le> Under r A"
unfolding rel.Under_def by blast


lemma UnderS_incr:
"r \<le> r' \<Longrightarrow> UnderS r A \<le> UnderS r A"
unfolding rel.UnderS_def by blast


lemma Under_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> Under r A \<le> Under r A'"
unfolding rel.Under_def by blast


lemma UnderS_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> UnderS r A \<le> UnderS r A'"
unfolding rel.UnderS_def by blast


lemma above_incr2:
"r \<le> r' \<Longrightarrow> above r a \<le> above r' a"
unfolding rel.above_def by blast


lemma aboveS_incr2:
"r \<le> r' \<Longrightarrow> aboveS r a \<le> aboveS r' a"
unfolding rel.aboveS_def by blast


lemma Above_incr:
"r \<le> r' \<Longrightarrow> Above r A \<le> Above r A"
unfolding rel.Above_def by blast


lemma AboveS_incr:
"r \<le> r' \<Longrightarrow> AboveS r A \<le> AboveS r A"
unfolding rel.AboveS_def by blast


lemma Above_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> Above r A \<le> Above r A'"
unfolding rel.Above_def by blast


lemma AboveS_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> AboveS r A \<le> AboveS r A'"
unfolding rel.AboveS_def by blast


end
