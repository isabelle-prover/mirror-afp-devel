(*<*)
theory Incidence imports Main begin
(*>*)

section\<open>Incidence\<close>
text\<open>
D.Hilbert made a rigorous reconstruction of Euclidean geometry in Chapter 1 of \<^cite>\<open>"Hilbert"\<close>.
There, five types of axioms are listed and 32 theorems are proved.
In Hilbert's axiom system, basic concepts such as points and lines are treated as undefined terms, and only their relationships are defined by axioms.
In addition, the continuity axiom stipulates that the Euclidean plane is essentially equivalent to the real plane R2, ensuring that the axiom system is categorical.

Implement each axiom and definition and prove the theorem (Coupling axioms related to space geometry axiom 4 to 8 are excluded).
\<close>

datatype Point = "char"
datatype Segment = Se "Point" "Point"
datatype Line = Li "Point" "Point"
datatype Angle = An "Point" "Point" "Point"
datatype Triangle = Tr "Point" "Point" "Point"
datatype Geo_object = 
  Poi "Point" 
  | Seg "Segment" 
  | Lin "Line" 
  | Ang "Angle" 
  | Tri "Triangle"
datatype sign = add | sub
datatype Geo_objects = Emp | Geos "Geo_object" "sign" "Geo_objects"

locale Eq_relation =
  fixes Eq :: "Geo_objects \<Rightarrow> Geo_objects \<Rightarrow> bool" 
    and Inv :: "bool \<Rightarrow> bool"
 assumes Eq_refl [simp,intro] : "Eq obs obs"
    and Eq_rev : "\<lbrakk>Eq obs1 obs2\<rbrakk> \<Longrightarrow> Eq obs2 obs1"
    and Eq_trans : "\<lbrakk>Eq obs1 obs3; Eq obs2 obs3\<rbrakk> \<Longrightarrow> Eq obs1 obs2"
    and Inv_def : "Inv b1 \<longleftrightarrow> \<not> b1"
    
locale Definition_1 = Eq_relation +
  fixes Line_on :: "Line \<Rightarrow> Point \<Rightarrow> bool"
        
locale Axiom_1 = Definition_1 +
  assumes Line_exist : "\<lbrakk>\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)\<rbrakk> 
        \<Longrightarrow> \<exists>l. Line_on l p1 \<and> Line_on l p2"
    and Line_unique : "\<lbrakk>Line_on l1 p1; Line_on l1 p2; Line_on l2 p1; Line_on l2 p2;
        \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)\<rbrakk> \<Longrightarrow> Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
    and Line_on_exist : "\<exists>p q. Line_on l1 p \<and> Line_on l1 q
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp)"
    and Line_not_on_exist : "\<exists>p q r. \<not> Line_on l1 p \<and> \<not> Line_on l1 q \<and> \<not> Line_on l1 r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp)
        \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)"

locale Incidence_Rule = Axiom_1 +
  assumes Point_Eq : "\<lbrakk>P1(p1); Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)\<rbrakk> \<Longrightarrow> P1(p2)"
    and Line_on_trans : "\<lbrakk>Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp); Line_on l1 p1\<rbrakk>
        \<Longrightarrow> Line_on l2 p1"
    and Line_on_rule : "Line_on (Li p1 p2) p1 \<and> Line_on (Li p1 p2) p2"

lemma(in Incidence_Rule) Eq_not_trans : 
  assumes N :
    "\<not> Eq obs1 obs2"
    "Eq obs2 obs3"
  shows "\<not> Eq obs1 obs3"
proof 
  assume W : "Eq obs1 obs3"
  from assms have P1 : "Eq obs3 obs2" by (simp add:Eq_rev)
  from W P1 have P2 : "Eq obs1 obs2" by (blast intro:Eq_trans)
  from N P2 show False by simp
qed

lemma(in Incidence_Rule) Line_rev : 
  assumes "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
  shows "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p2 p1)) add Emp)" 
proof -
  from assms have P1 : "Line_on (Li p1 p2) p1 \<and> Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p2 p1) p1 \<and> Line_on (Li p2 p1) p2" by (simp add:Line_on_rule)
  from assms P1 P2 show "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p2 p1)) add Emp)" by (blast intro:Line_unique)
qed

lemma(in Incidence_Rule) Line_not_on_Point : 
  assumes N : 
    "\<not> Line_on (Li p1 p2) p3"
  shows "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" 
proof 
  assume W : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)"
  have P1 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  from W P1 have P2 : "Line_on (Li p1 p2) p3" by (simp add:Point_Eq)
  from N P2 show False by simp
qed

lemma(in Incidence_Rule) Line_not_on_trans : 
  assumes
    "Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
    "\<not> Line_on l1 p1"
  shows "\<not> Line_on l2 p1" 
proof -
  from assms have P1 : "Eq (Geos (Lin l2) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Eq_rev)
  from P1 have P2 : "Line_on l2 p1 \<Longrightarrow> Line_on l1 p1" by (simp add:Line_on_trans)
  from assms P2 show "\<not> Line_on l2 p1" by blast
qed

lemma(in Incidence_Rule) Line_on_rev : 
  assumes 
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" 
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" 
    "Line_on (Li p1 p2) p3"
  shows "Line_on (Li p1 p3) p2" 
proof -
  have P1 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  from assms P1 P2 P3 have P4 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (simp add:Line_unique)
  have P5 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from P4 P5 show "Line_on (Li p1 p3) p2" by (simp add:Line_on_trans)
qed

lemma(in Incidence_Rule) Line_not_Eq : 
  assumes
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    "\<not> Line_on (Li p1 p2) p3"
  shows "\<not> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" 
proof -
  have P1 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  have P2 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Eq_rev)
  from P1 P2 have P3 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp) \<Longrightarrow>
    Line_on (Li p1 p2) p3" by (simp add:Line_on_trans)
  from assms P3 show "\<not> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by blast
qed

lemma(in Incidence_Rule) Line_not_Eq_on : 
  assumes N :
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)"
    "\<not> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)"
  shows "\<not> Line_on (Li p1 p2) p3" 
proof 
  assume W : "Line_on (Li p1 p2) p3" 
  have P1 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  from N W P1 P2 P3 have P4 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (simp add:Line_unique)
  from N P4 show False by simp
qed

lemma(in Incidence_Rule) Line_unique_Point : 
  assumes
    "\<not> Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
    "Line_on l1 p1" "Line_on l1 p2"
    "Line_on l2 p1" "Line_on l2 p2"
  shows "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" 
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)" by (simp add:Line_unique)
  from assms P1 show "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by blast
qed

lemma(in Incidence_Rule) Line_not_on_Eq : 
  assumes N :
    "\<not> Line_on l1 p1"
    "Line_on l2 p1"
  shows "\<not> Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
proof 
  assume W : "Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)" 
  from N W have P1 : "Line_on l1 p1" by (blast intro:Line_on_trans Eq_rev)
  from N P1 show False by simp
qed

lemma(in Incidence_Rule) Line_cross_not_on : 
  assumes
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp)"
    "\<not> Line_on (Li p1 p2) p3"
    "Line_on (Li p2 p3) p4"
  shows "\<not> Line_on (Li p1 p2) p4"
proof -
  have P1 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p2 p3) p2" by (simp add:Line_on_rule)
  from assms P1 P2 have P3 : "Line_on (Li p1 p2) p4 \<Longrightarrow> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p2 p3)) add Emp)" by (simp add:Line_unique)
  have P4 : "Line_on (Li p2 p3) p3" by (simp add:Line_on_rule)
  from P3 P4 have P5 : "Line_on (Li p1 p2) p4 \<Longrightarrow> Line_on (Li p1 p2) p3" by (blast intro:Line_on_trans Eq_rev)
  from assms P5 show "\<not> Line_on (Li p1 p2) p4" by blast
qed

end
  