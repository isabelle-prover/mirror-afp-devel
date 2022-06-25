(*<*)
theory Congruence imports Order begin
(*>*)

section\<open>Congruence\<close>
text\<open>
Of the equivalence relations for angles, only the transitive law is not included in the axiom, but is mentioned by the theorem.
However, in the proofs before that, there are some scenes where it is regarded as congruence by the congruence relation with the same angle.
Therefore, we add a weak transitive law that ``when two angles are congruent, the same angle as one is congruent with the other".
Also, the uniqueness of the large and small relationship between the two angles and the transitive relation of three or more those have not been proved.
Therefore, each proof regarding these is added to this section.
Furthermore, regarding Theorem 23, the proof is omitted because the ``large and small relationship of line segments", which is treated as a premise, is undefined.
As a result, the proof process of Theorem 24 is different from the existing one.
\<close>

locale Definition_3 = Order_Rule +
  fixes Def :: "Geo_object \<Rightarrow> bool"
    and Cong :: "Geo_objects \<Rightarrow> Geo_objects \<Rightarrow> bool"
    and Gr :: "Geo_objects \<Rightarrow> Geo_objects \<Rightarrow> bool"
    and Ang_inside :: "Angle \<Rightarrow> Point \<Rightarrow> bool"
    and Right_angle :: "Angle \<Rightarrow> bool"
  assumes Tri_def : "Def (Tri (Tr p1 p2 p3)) \<longleftrightarrow> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)
        \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp) \<and> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)
        \<and> \<not> Bet_Point (Se p1 p2) p3 \<and> \<not> Bet_Point (Se p2 p3) p1 \<and> \<not> Bet_Point (Se p3 p1) p2
        \<and> \<not> Seg_on_Seg (Se p1 p2) (Se p2 p3) \<and> \<not> Seg_on_Seg (Se p2 p3) (Se p3 p1) \<and> \<not> Seg_on_Seg (Se p3 p1) (Se p1 p2)"
    and Cong_refl [simp,intro] : "Cong obs obs"
    and Ang_def : "Def (Ang (An p1 p2 p3)) \<longleftrightarrow> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)
        \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp) \<and> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)
        \<and> \<not> Eq (Geos (Lin (Li p2 p1)) add Emp) (Geos (Lin (Li p2 p3)) add Emp)"
    and Ang_rev : "\<lbrakk>Cong (Geos (ang1) add Emp) (Geos (ang2) add Emp)\<rbrakk> \<Longrightarrow>
        Cong (Geos (ang2) add Emp) (Geos (ang1) add Emp)"
    and Ang_roll : "Cong (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p3 p2 p1)) add Emp)
        \<and> Eq (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p3 p2 p1)) add Emp)"
    and Ang_inside_def : "Ang_inside (An p1 p2 p3) p \<longleftrightarrow> Def (Ang (An p1 p2 p3)) \<and> Plane_sameside (Li p2 p1) p3 p \<and> Plane_sameside (Li p2 p3) p1 p"
    and Ang_Point_swap : "\<lbrakk>Def (Ang (An p1 p2 p3)); Line_on (Li p2 p1) p4; \<not> Bet_Point (Se p1 p4) p2;
        Line_on (Li p2 p3) p5; \<not> Bet_Point (Se p3 p5) p2; \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp);
        \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p5) add Emp)\<rbrakk> \<Longrightarrow> 
        Eq (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p5)) add Emp) \<and> Def (Ang (An p4 p2 p5))"
    and Ang_Right_angle_def : "Right_angle (An p1 p2 p3) \<longleftrightarrow>
        (\<exists>p. Cong (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p1 p2 p)) add Emp)
        \<and> Bet_Point (Se p3 p) p2 \<and> Def (Ang (An p1 p2 p3)) \<and> Def (Ang (An p1 p2 p)))"
    and Tri_Cong_def : "Cong (Geos (Tri (Tr p11 p12 p13)) add Emp) (Geos (Tri (Tr p21 p22 p23)) add Emp) 
        \<longleftrightarrow> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)
        \<and> Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p23)) add Emp)
        \<and> Eq (Geos (Seg (Se p13 p11)) add Emp) (Geos (Seg (Se p23 p21)) add Emp)
        \<and> Cong (Geos (Ang (An p12 p11 p13)) add Emp) (Geos (Ang (An p22 p21 p23)) add Emp)
        \<and> Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p23 p22 p21)) add Emp)
        \<and> Cong (Geos (Ang (An p11 p13 p12)) add Emp) (Geos (Ang (An p21 p23 p22)) add Emp)"
    and Ang_greater_def : "\<lbrakk>Cong (Geos (Ang an1) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp);
        Plane_sameside (Li p2 p3) p4 p1\<rbrakk> \<Longrightarrow>
        Ang_inside (An p1 p2 p3) p4 \<longleftrightarrow> Gr (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang an1) add Emp)"
    and Ang_less_def : "\<lbrakk>Cong (Geos (Ang an1) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp);
        Plane_sameside (Li p2 p3) p4 p1; \<not> Ang_inside (An p1 p2 p3) p4;
        \<not> Eq (Geos (Lin (Li p2 p1)) add Emp) (Geos (Lin (Li p2 p4)) add Emp)\<rbrakk> \<Longrightarrow> 
        Gr (Geos (Ang an1) add Emp) (Geos (Ang (An p1 p2 p3)) add Emp)"
        
locale Axiom_3 = Definition_3 +
  assumes Seg_add : "\<lbrakk>Line_on l1 p11; Line_on l1 p12; Line_on l1 p13; \<not> Seg_on_Seg (Se p11 p12) (Se p12 p13);
        Line_on l2 p21; Line_on l2 p22; Line_on l2 p23; \<not> Seg_on_Seg (Se p21 p22) (Se p22 p23);
        Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp);
        Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p23)) add Emp)\<rbrakk> \<Longrightarrow>
        Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)"
    and Seg_sub : "\<lbrakk>Line_on l1 p11; Line_on l1 p12; Line_on l1 p13; \<not> Seg_on_Seg (Se p11 p12) (Se p12 p13);
        Line_on l2 p21; Line_on l2 p22; Line_on l2 p23; \<not> Seg_on_Seg (Se p21 p22) (Se p22 p23);
        Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)\<rbrakk> \<Longrightarrow>
        Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)
        \<and> Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p23)) add Emp)"
    and Ang_move_sameside : "\<lbrakk>\<not> Line_on (Li p1 p2) p3; Def (Ang a1)\<rbrakk> \<Longrightarrow> \<exists>p. Cong (Geos (Ang a1) add Emp) (Geos (Ang (An p p1 p2)) add Emp) \<and> Plane_sameside (Li p1 p2) p p3"
    and Ang_move_diffside : "\<lbrakk>\<not> Line_on (Li p1 p2) p3; Def (Ang a1)\<rbrakk> \<Longrightarrow> \<exists>p. Cong (Geos (Ang a1) add Emp) (Geos (Ang (An p p1 p2)) add Emp) \<and> Plane_diffside (Li p1 p2) p p3"
    and Ang_move_unique : "\<lbrakk>Cong (Geos (Ang an1) add Emp) (Geos (Ang (An p1 p2 p3)) add Emp);
        Cong (Geos (Ang an1) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp);
        Plane_sameside (Li p2 p3) p1 p4\<rbrakk> \<Longrightarrow>
        Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p4 p2)) add Emp) \<and> \<not> Bet_Point (Se p1 p4) p2"
    and Tri_week_SAS : "\<lbrakk>Def (Tri (Tr p11 p12 p13)); Def (Tri (Tr p21 p22 p23));
        Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp);
        Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp);
        Cong (Geos (Ang (An p12 p11 p13)) add Emp) (Geos (Ang (An p22 p21 p23)) add Emp)\<rbrakk>
        \<Longrightarrow> Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p23 p22 p21)) add Emp)"

locale Congruence_Rule = Axiom_3 +
  assumes Ang_weektrans : "\<lbrakk>Eq (Geos (Ang an1) add Emp) (Geos (Ang an2) add Emp);
        Cong (Geos (Ang an2) add Emp) (Geos (Ang an3) add Emp)\<rbrakk> \<Longrightarrow> Cong (Geos (Ang an1) add Emp) (Geos (Ang an3) add Emp)"

lemma (in Congruence_Rule) Seg_Bet_add : 
  assumes 
    "Bet_Point (Se p11 p13) p12"
    "Bet_Point (Se p21 p23) p22"
    "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)"
    "Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p23)) add Emp)"
  shows "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)"
proof -
  from assms have "\<exists>l. Line_on l p11 \<and> Line_on l p13 \<and> Line_on l p12" by (simp add:Line_Bet_exist)
  then obtain l1 :: Line where P1 : "Line_on l1 p11 \<and> Line_on l1 p13 \<and> Line_on l1 p12" by blast
  from assms have "\<exists>l. Line_on l p21 \<and> Line_on l p23 \<and> Line_on l p22" by (simp add:Line_Bet_exist)
  then obtain l2 :: Line where P2 : "Line_on l2 p21 \<and> Line_on l2 p23 \<and> Line_on l2 p22" by blast
  from assms have P3 : "\<not> Seg_on_Seg (Se p11 p12) (Se p12 p13)" by (simp add:Seg_Bet_not_on)
  from assms have P4 : "\<not> Seg_on_Seg (Se p21 p22) (Se p22 p23)" by (simp add:Seg_Bet_not_on)
  from assms P1 P2 P3 P4 show "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)" by (blast intro:Seg_add)
qed

lemma (in Congruence_Rule) Tri_sinple_def :
  assumes 
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)"
    "\<not> Line_on (Li A B) C"
  shows "Def (Tri (Tr A B C))"
proof -
  have P1 : "Bet_Point (Se A B) C \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_Bet_on)
  from assms P1 have P2 : "\<not> Bet_Point (Se A B) C" by blast 
  from assms have P3 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P3 have P4 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_rev)
  have P5 : "Bet_Point (Se B C) A \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_Bet_on)
  from assms P5 have P6 : "\<not> Bet_Point (Se B C) A" by blast 
  have P7 : "Bet_Point (Se C A) B \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_Bet_on)
  from assms P7 have P8 : "\<not> Bet_Point (Se C A) B" by blast 
  have "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> \<exists>p. Bet_Point (Se A B) p \<and> Bet_Point (Se B C) p" by (simp add:Seg_on_Seg_rule)
  then obtain D :: Point where P9 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Bet_Point (Se A B) D \<and> Bet_Point (Se B C) D" by blast
  have P10 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from P9 have P11 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Line_on (Li A B) D" by (simp add:Line_Bet_on)
  have P12 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  from P9 have P13 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_Bet_on)
  from P9 have "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Bet_Point (Se A B) D" by simp
  then have P14 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P10 P11 P12 P13 P14 have P15 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  have P16 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P15 P16 have P17 : "Seg_on_Seg (Se A B) (Se B C) \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from assms P17 have P18 : "\<not> Seg_on_Seg (Se A B) (Se B C)" by blast 
  have "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> \<exists>p. Bet_Point (Se B C) p \<and> Bet_Point (Se C A) p" by (simp add:Seg_on_Seg_rule)
  then obtain E :: Point where P19 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Bet_Point (Se B C) E \<and> Bet_Point (Se C A) E" by blast
  then have P20 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Line_on (Li B C) E" by (simp add:Line_Bet_on)
  have P21 : "Line_on (Li C A) C" by (simp add:Line_on_rule)
  from P19 have P22 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Line_on (Li C A) E" by (simp add:Line_Bet_on)
  from P19 have "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Bet_Point (Se B C) E" by simp
  then have P23 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def)
  from P16 P20 P21 P22 P23 have P24 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Eq (Geos (Lin (Li C A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  have P25 : "Line_on (Li C A) A" by (simp add:Line_on_rule)
  from P24 P25 have P26 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from assms P3 P26 have P27 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Line_on (Li B A) C" by (blast intro:Line_on_rev)
  from P4 P27 have P28 : "Seg_on_Seg (Se B C) (Se C A) \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from assms P28 have P29 : "\<not> Seg_on_Seg (Se B C) (Se C A)" by blast 
  have "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> \<exists>p. Bet_Point (Se C A) p \<and> Bet_Point (Se A B) p" by (simp add:Seg_on_Seg_rule)
  then obtain F :: Point where P30 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Bet_Point (Se C A) F \<and> Bet_Point (Se A B) F" by blast
  then have P31 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Line_on (Li C A) F" by (simp add:Line_Bet_on)
  have P32 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  from P30 have P33 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Line_on (Li A B) F" by (simp add:Line_Bet_on)
  from P30 have "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Bet_Point (Se C A) F" by simp
  then have P34 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi F) add Emp)" by (simp add:Bet_Point_def)
  from P25 P31 P32 P33 P34 have P35 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Eq (Geos (Lin (Li C A)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  from P21 P35 have P36 : "Seg_on_Seg (Se C A) (Se A B) \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from assms P36 have P37 : "\<not> Seg_on_Seg (Se C A) (Se A B)" by blast
  from assms P2 P6 P8 P18 P29 P37 show "Def (Tri (Tr A B C))" by (simp add:Tri_def)
qed

lemma (in Congruence_Rule) Tri_def_Line :
  assumes 
    "Def (Tri (Tr A B C))"
  shows "\<not> Line_on (Li A B) C \<and> \<not> Line_on (Li B C) A \<and> \<not> Line_on (Li C A) B"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
        \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
        \<and> \<not> Bet_Point (Se A B) C \<and> \<not> Bet_Point (Se B C) A \<and> \<not> Bet_Point (Se C A) B" by (simp add:Tri_def)
  have P2 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  from P1 P2 P3 have P4 : "Line_on (Li A B) C \<Longrightarrow> Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C" by (simp add:Bet_case)
  from P1 have P5 : "\<not> Bet_Point (Se A C) B" by (blast intro:Bet_rev)
  from P1 have P6 : "\<not> Bet_Point (Se C B) A" by (blast intro:Bet_rev)
  from P1 have P7 : "\<not> Bet_Point (Se B A) C" by (blast intro:Bet_rev)
  from P4 P5 P6 P7 have P8 : "\<not> Line_on (Li A B) C" by blast 
  have P9 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P10 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P1 P9 P10 have P11 : "Line_on (Li B C) A \<Longrightarrow> Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C" by (simp add:Bet_case)
  from P5 P6 P7 P11 have P12 : "\<not> Line_on (Li B C) A" by blast 
  have P13 : "Line_on (Li C A) C" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li C A) A" by (simp add:Line_on_rule)
  from P1 P13 P14 have P15 : "Line_on (Li C A) B \<Longrightarrow> Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C" by (simp add:Bet_case)
  from P5 P6 P7 P15 have P16 : "\<not> Line_on (Li C A) B" by blast 
  from P8 P12 P16 show "\<not> Line_on (Li A B) C \<and> \<not> Line_on (Li B C) A \<and> \<not> Line_on (Li C A) B" by simp
qed

lemma (in Congruence_Rule) Tri_def_trans :
  assumes 
    "Def (Tri (Tr A B C))"
  shows "Def (Tri (Tr B C A))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
        \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
        \<and> \<not> Bet_Point (Se A B) C \<and> \<not> Bet_Point (Se B C) A \<and> \<not> Bet_Point (Se C A) B" by (simp add:Tri_def)
  from assms have P2 : "\<not> Line_on (Li B C) A" by (simp add:Tri_def_Line)
  from P1 P2 show "Def (Tri (Tr B C A))" by (simp add:Tri_sinple_def)
qed

lemma (in Congruence_Rule) Tri_def_rev :
  assumes 
    "Def (Tri (Tr A B C))"
  shows "Def (Tri (Tr C B A))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
        \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
        \<and> \<not> Bet_Point (Se A B) C \<and> \<not> Bet_Point (Se B C) A \<and> \<not> Bet_Point (Se C A) B" by (simp add:Tri_def)
  from assms have P2 : "\<not> Line_on (Li B C) A" by (simp add:Tri_def_Line)
  from P1 have P3 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li C B)) add Emp)" by (simp add:Line_rev)
  from P2 P3 have P4 : "\<not> Line_on (Li C B) A" by (simp add:Line_not_on_trans)
  from P1 have P5 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P1 have P6 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P1 have P7 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P4 P5 P6 P7 show "Def (Tri (Tr C B A))" by (simp add:Tri_sinple_def)
qed

lemma (in Congruence_Rule) Tri_def_extension :
  assumes 
    "Def (Tri (Tr A B C))"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)"
    "Line_on (Li B C) D"
  shows "Def (Tri (Tr A B D))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from assms have P2 : "\<not> Line_on (Li B C) A" by (simp add:Tri_def_Line)
  from assms have P3 : "Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Point_Eq)
  from P2 P3 have P4 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by blast
  from assms have P5 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Tri_def)
  from assms P5 have P6 : "Line_on (Li B D) C" by (simp add:Line_on_rev)
  have P7 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  have P8 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P5 P6 P7 P8 P9 have "Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  then have P10 : "Line_on (Li B D) A \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from P2 P10 have P11 : "\<not> Line_on (Li B D) A" by blast
  from assms P1 P4 P11 have "Def (Tri (Tr B D A))" by (simp add:Tri_sinple_def)
  thus "Def (Tri (Tr A B D))" by (simp add:Tri_def_trans)
qed

lemma (in Congruence_Rule) Ang_to_Tri : 
  assumes 
    "Def (Ang (An A B C))"
  shows "Def (Tri (Tr A B C))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
    \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
    \<and> \<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Ang_def)
  have P2 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P1 have P5 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by simp
  from P1 have "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_rev)
  then have P6 : "Line_on (Li A B) C \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P2 P3 P4 P5 P6 have P7 : "Line_on (Li A B) C \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P1 P7 have P8 : "\<not> Line_on (Li A B) C" by blast
  from P1 P8 show "Def (Tri (Tr A B C))" by (simp add:Tri_sinple_def)
qed

lemma (in Congruence_Rule) Ang_sinple_def : 
  assumes 
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Line_on (Li A B) C"
  shows "Def (Ang (An A B C))"
proof -
  from assms have P1 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_rev)
  from assms P1 have P2 : "\<not> Line_on (Li B A) C" by (simp add:Line_not_on_trans)
  have "Line_on (Li B A) B" by (simp add:Line_on_rule)
  then have P3 : "Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li B A) C" by (simp add:Point_Eq)
  from P2 P3 have P4 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
  have "Line_on (Li B A) A" by (simp add:Line_on_rule)
  then have P5 : "Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li B A) C" by (simp add:Point_Eq)
  from P2 P5 have P6 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  have "Line_on (Li B C) C" by (simp add:Line_on_rule)
  then have P7 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B A)) add Emp) \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P2 P7 have P8 : "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (blast intro:Eq_rev)
  from assms P4 P6 P8 show "Def (Ang (An A B C))" by (simp add:Ang_def)
qed

lemma (in Congruence_Rule) Tri_to_Ang : 
  assumes
    "Def (Tri (Tr A B C))"
  shows "Def (Ang (An A B C))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
    \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  from assms have P2 : "\<not> Line_on (Li A B) C" by (simp add:Tri_def_Line)
  from P1 P2 show "Def (Ang (An A B C))" by (simp add:Ang_sinple_def)
qed

lemma (in Congruence_Rule) Ang_def_rev : 
  assumes 
    "Def (Ang (An A B C))"
  shows "Def (Ang (An C B A))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
    \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
    \<and> \<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Ang_def)
  have P2 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  from P1 have P5 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by simp
  from P2 P3 P4 P5 have P6 : "Line_on (Li B C) A \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P1 P6 have P7 : "\<not> Line_on (Li B C) A" by blast
  from P1 have P8 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li C B)) add Emp)" by (simp add:Line_rev)
  from P7 P8 have P9 : "\<not> Line_on (Li C B) A" by (simp add:Line_not_on_trans)
  from P1 have P10 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P9 P10 show "Def (Ang (An C B A))" by (simp add:Ang_sinple_def)
qed

lemma (in Congruence_Rule) Ang_def_inv : 
  assumes 
    "Def (Ang (An A B C))"
  shows "Def (Ang (An A C B))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)
    \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<and> \<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)
    \<and> \<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Ang_def)
  have P2 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  from P1 have P5 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by simp
  from P2 P3 P4 P5 have P6 : "Line_on (Li B C) A \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P1 P6 have P7 : "\<not> Line_on (Li B C) A" by blast
  have P8 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P1 P4 P8 P9 have P10 : "Line_on (Li A C) B \<Longrightarrow> Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  have P11 : "Line_on (Li A C) A" by (simp add:Line_on_rule)  
  from P10 P11 have P12 : "Line_on (Li A C) B \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from P7 P12 have P13 : "\<not> Line_on (Li A C) B" by blast
  from P1 have P14 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P13 P14 show "Def (Ang (An A C B))" by (simp add:Ang_sinple_def)
qed

lemma (in Congruence_Rule) Ang_def_extension : 
  assumes 
    "Def (Ang (An A B C))"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)"
    "Line_on (Li B C) D"
  shows "Def (Ang (An A B D))"
proof -
  from assms have P1 : "Def (Tri (Tr A B C))" by (simp add:Ang_to_Tri)
  from assms P1 have "Def (Tri (Tr A B D))" by (simp add:Tri_def_extension)
  thus "Def (Ang (An A B D))" by (simp add:Tri_to_Ang)
qed

lemma (in Congruence_Rule) Bet_end_Point :
  shows "\<not> Bet_Point (Se p1 p1) p2"
proof 
  assume W : "Bet_Point (Se p1 p1) p2"
  then have P1 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def del:Eq_refl)
  have P2 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p1) add Emp)" by simp
  from P1 P2 show False by blast
qed

lemma (in Congruence_Rule) Seg_Plane_sameside :
  assumes 
    "Line_on l1 A"
    "Line_on l1 B"
    "Line_on l1 C"
    "\<not> Line_on l1 D"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Bet_Point (Se B C) A"
  shows "Plane_sameside (Li D A) B C \<or> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
proof -
  have "Line_on (Li D A) D" by (simp add:Line_on_rule)
  then have P1 : "Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 D" by (simp add:Line_on_trans)
  from assms P1 have P2 : "\<not> Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp)" by blast
  have "Plane_diffside (Li D A) B C \<Longrightarrow> \<exists>p. Bet_Point (Se B C) p \<and> Line_on (Li D A) p \<and> \<not> Line_on (Li D A) B \<and> \<not> Line_on (Li D A) C" by (simp add:Plane_diffside_def)
  then obtain E :: Point where P3 : "Plane_diffside (Li D A) B C \<Longrightarrow> Bet_Point (Se B C) E \<and> Line_on (Li D A) E" by blast
  then have P4 : "Plane_diffside (Li D A) B C \<Longrightarrow> Line_on (Li B C) E" by (simp add:Line_Bet_on)
  have P5 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P6 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from assms P5 P6 have P7 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from P4 P7 have P8 : "Plane_diffside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> 
    Line_on l1 E" by (simp add:Line_on_trans)
  have P9 : "Line_on (Li D A) A" by (simp add:Line_on_rule)
  from assms P2 P3 P8 P9 have P10 : "Plane_diffside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> 
    Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp)" by (simp add:Line_unique_Point)
  from P3 have P11 : "Plane_diffside (Li D A) B C \<Longrightarrow> Bet_Point (Se B C) E" by simp
  from P10 P11 have P12 : "Plane_diffside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow>
    Bet_Point (Se B C) A" by (simp add:Point_Eq)
  from assms P12 have "\<not> Plane_diffside (Li D A) B C \<or> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
  then have P13 : "\<not> Plane_diffside (Li D A) B C \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) 
    \<or> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
  from assms P9 have P14 : "Line_on (Li D A) B \<Longrightarrow> Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from P2 P14 have P15 : "\<not> Line_on (Li D A) B" by blast
  from assms P9 have P16 : "Line_on (Li D A) C \<Longrightarrow> Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from P2 P16 have P17 : "\<not> Line_on (Li D A) C" by blast
  from P15 P17 have P18 : "\<not> Plane_diffside (Li D A) B C \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow>
    Plane_sameside (Li D A) B C" by (simp add:Plane_not_diffside_sameside)
  from P13 P18 show "Plane_sameside (Li D A) B C \<or> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
qed

lemma (in Congruence_Rule) Seg_move_unique :
  assumes 
    "Line_on l1 A"
    "Line_on l1 B"
    "Line_on l1 C"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
    "\<not> Bet_Point (Se B C) A"
  shows "Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
proof -
  have "\<exists>p q r. \<not> Line_on l1 p \<and> \<not> Line_on l1 q \<and> \<not> Line_on l1 r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain D :: Point where P1 : "\<not> Line_on l1 D" by blast
  have P2 : "Line_on (Li A D) D" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from assms P3 P4 have P5 : "Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  from assms P5 have P6 : "Line_on (Li A B) C" by (simp add:Line_on_trans)
  from P1 P5 have P7 : "\<not> Line_on (Li A B) D" by (simp add:Line_not_on_trans)
  from assms P7 have "Def (Ang (An A B D))" by (simp add:Ang_sinple_def)
  then have P8 : "Def (Ang (An D A B))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (simp add:Ang_def)
  then have P9 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  have P10 : "\<not> Bet_Point (Se D D) A" by (simp add:Bet_end_Point)
  from assms P2 P6 P8 P9 P10 have "Eq (Geos (Ang (An D A B)) add Emp) (Geos (Ang (An D A C)) add Emp)" by (simp add:Ang_Point_swap)
  then have P11 : "Cong (Geos (Ang (An D A B)) add Emp) (Geos (Ang (An D A C)) add Emp)" by (simp add:Ang_weektrans)
  from assms P7 have "Def (Tri (Tr A B D))" by (blast intro:Ang_sinple_def Ang_to_Tri)
  then have "Def (Tri (Tr D B A))" by (simp add:Tri_def_rev)
  then have P12 : "Def (Tri (Tr A D B))" by (simp add:Tri_def_trans)
  have P13 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  from assms P13 P14 have P15 : "Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P1 P15 have P16 : "\<not> Line_on (Li A C) D" by (simp add:Line_not_on_trans)
  from assms P16 have "Def (Tri (Tr A C D))" by (blast intro:Ang_sinple_def Ang_to_Tri)
  then have "Def (Tri (Tr D C A))" by (simp add:Tri_def_rev)
  then have P17 : "Def (Tri (Tr A D C))" by (simp add:Tri_def_trans)
  from assms P11 P12 P17 have P18 : "Cong (Geos (Ang (An B D A)) add Emp) (Geos (Ang (An C D A)) add Emp)" by (simp add:Tri_week_SAS)
  have P19 : "Cong (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An B D A)) add Emp)" by (simp add:Ang_roll)
  have P20 : "Eq (Geos (Ang (An B D A)) add Emp) (Geos (Ang (An A D B)) add Emp)" by (simp add:Ang_roll)
  from P18 P20 have P21 : "Cong (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An C D A)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from assms P1 have P22 : "Plane_sameside (Li D A) B C \<or> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Seg_Plane_sameside)
  from P19 P21 have P23 : "Plane_sameside (Li D A) B C \<Longrightarrow> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li C D)) add Emp)" by (simp add:Ang_move_unique)
  have P24 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  from P23 P24 have P25 : "Plane_sameside (Li D A) B C \<Longrightarrow> Line_on (Li C D) B" by (simp add:Line_on_trans)
  have P26 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P27 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  have P28 : "Line_on (Li C D) C" by (simp add:Line_on_rule)
  from P25 P26 P27 P28 have P29 : "Plane_sameside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li C D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  have P30 : "Line_on (Li C D) D" by (simp add:Line_on_rule)
  from P29 P30 have P31 : "Plane_sameside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow>
    Line_on (Li B C) D" by (simp add:Line_on_trans)
  from assms P26 P27 have P32 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from P31 P32 have P33 : "Plane_sameside (Li D A) B C \<Longrightarrow> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow>
    Line_on l1 D" by (simp add:Line_on_trans)
  from P1 P33 have P34 : "Plane_sameside (Li D A) B C \<Longrightarrow> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
  from P22 P34 show "Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
qed

lemma (in Congruence_Rule) Seg_not_Eq_Point :
  assumes 
    "\<not> Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
  shows "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
proof -
  have P1 : "Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> 
    Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)" by (simp add:Seg_Point_Eq)
  from assms P1 show "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_replace : 
  assumes 
    "Def (Ang (An A B C))"
    "Def (Ang (An A1 B1 C1))"
    "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 C1)) add Emp)"
  shows "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 A1) p \<and> \<not> Bet_Point (Se p A1) B1 \<and> Def (Ang (An p B1 C1))"
    and "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 p)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A1 B1 p)) add Emp)
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 C1) p \<and> \<not> Bet_Point (Se p C1) B1 \<and> Def (Ang (An A1 B1 p))"
    and "\<exists>p q. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An p B1 q)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B1 q)) add Emp) 
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 A1) p \<and> \<not> Bet_Point (Se p A1) B1
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 q)) add Emp) \<and> Line_on (Li B1 C1) q \<and> \<not> Bet_Point (Se q C1) B1 \<and> Def (Ang (An p B1 q))"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi B1) add Emp)" by (simp add:Ang_def)
  then have P2 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A1) add Emp)" by (blast intro:Eq_rev)
  have P3 : "Line_on (Li B1 A1) A1" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B1 A1) B1" by (simp add:Line_on_rule)
  from assms have "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Ang_def)
  then have P5 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P2 P3 P4 P5 have "\<exists>p. Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> \<not> Bet_Point (Se p A1) B1 \<and> Line_on (Li B1 A1) p \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain A2 :: Point where P6 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 A2)) add Emp) \<and> \<not> Bet_Point (Se A2 A1) B1 \<and> Line_on (Li B1 A1) A2 \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A2) add Emp)" by blast
  from assms have P7 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C1) add Emp)" by (simp add:Ang_def)
  have P8 : "Line_on (Li B1 C1) B1" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li B1 C1) C1" by (simp add:Line_on_rule)
  from assms have P10 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Ang_def)
  from P7 P8 P9 P10 have "\<exists>p. Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> \<not> Bet_Point (Se p C1) B1 \<and> Line_on (Li B1 C1) p \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain C2 :: Point where P11 : "Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 C2)) add Emp) \<and> \<not> Bet_Point (Se C2 C1) B1 \<and> Line_on (Li B1 C1) C2 \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C2) add Emp)" by blast
  have P12 : "\<not> Bet_Point (Se C1 C1) B1" by (simp add:Bet_end_Point)
  from P6 have P13 : "\<not> Bet_Point (Se A1 A2) B1" by (blast intro:Bet_rev)
  from assms P3 P6 P7 P9 P12 P13 have P14 : "Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B1 C1)) add Emp)" by (simp add:Ang_Point_swap)
  from assms P14 have P15 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A2 B1 C1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms have P16 : "\<not> Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Ang_def)
  from P6 have P17 : "Line_on (Li B1 A1) A2" by simp
  from P6 have P18 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A2) add Emp)" by simp
  from P4 P8 P17 P18 have P19 : "Line_on (Li B1 C1) A2 \<Longrightarrow> Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Line_unique)
  from P16 P19 have P20 : "\<not> Line_on (Li B1 C1) A2" by blast
  from P7 P20 have "Def (Ang (An B1 C1 A2))" by (simp add:Ang_sinple_def)
  then have P21 : "Def (Ang (An A2 B1 C1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P6 P14 P15 P21 show "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 A1) p \<and> \<not> Bet_Point (Se p A1) B1 \<and> Def (Ang (An p B1 C1))" by blast
  have P22 : "\<not> Bet_Point (Se A1 A1) B1" by (simp add:Bet_end_Point)
  from P11 have P23 : "\<not> Bet_Point (Se C1 C2) B1" by (blast intro:Bet_rev)
  from assms P2 P3 P7 P11 P22 P23 have P24 : "Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A1 B1 C2)) add Emp)" by (simp add:Ang_Point_swap)
  from assms P24 have P25 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P11 have P26 : "Line_on (Li B1 C1) C2" by simp
  from P11 have P27 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C2) add Emp)" by simp
  from P4 P8 P26 P27 have P28 : "Line_on (Li B1 A1) C2 \<Longrightarrow> Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Line_unique)
  from P16 P28 have P29: "\<not> Line_on (Li B1 A1) C2" by blast
  from P2 P29 have "Def (Ang (An B1 A1 C2))" by (simp add:Ang_sinple_def)
  then have P30 : "Def (Ang (An A1 B1 C2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P11 P24 P25 P30 show "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 p)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A1 B1 p)) add Emp) 
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 C1) p \<and> \<not> Bet_Point (Se p C1) B1 \<and> Def (Ang (An A1 B1 p))" by blast
  from assms P6 P11 P13 P17 P23 P26 have P31 : "Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B1 C2)) add Emp)" by (simp add:Ang_Point_swap)
  from assms P31 have P32 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A2 B1 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P33 : "Line_on (Li B1 C2) B1" by (simp add:Line_on_rule)
  have P34 : "Line_on (Li B1 C2) C2" by (simp add:Line_on_rule)
  from P8 P26 P27 P33 P34 have "Eq (Geos (Lin (Li B1 C2)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Line_unique)
  then have P35 : "Line_on (Li B1 C2) A2 \<Longrightarrow> Line_on (Li B1 C1) A2" by (simp add:Line_on_trans)
  from P20 P35 have P36 : "\<not> Line_on (Li B1 C2) A2" by blast
  from P11 P36 have "Def (Ang (An B1 C2 A2))" by (simp add:Ang_sinple_def)
  then have P37 : "Def (Ang (An A2 B1 C2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P6 P11 P21 P30 P31 P32 P37 show "\<exists>p q. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An p B1 q)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B1 q)) add Emp)
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp) \<and> Line_on (Li B1 A1) p \<and> \<not> Bet_Point (Se p A1) B1
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 q)) add Emp) \<and> Line_on (Li B1 C1) q \<and> \<not> Bet_Point (Se q C1) B1 \<and> Def (Ang (An p B1 q))"
  by blast
qed

text\<open>Theorem11\<close>

theorem (in Congruence_Rule) Tri_isosceles: 
  assumes 
    "Def (Tri (Tr A B C))"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
  shows "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)"
proof -
  from assms have P1 : "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se A B)) add Emp)" by (simp add:Eq_rev)
  have P2 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An C A B)) add Emp)" by (simp add:Ang_roll)
  from assms have "Def (Tri (Tr C B A))" by (simp add:Tri_def_rev)
  then have P3 : "Def (Tri (Tr A C B))" by (simp add:Tri_def_trans)
  from assms P1 P2 P3 have P4 : "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (simp add:Tri_week_SAS)
  have P5 : "Eq (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_roll)
  from P4 P5 have P6 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  have P7 : "Eq (Geos (Ang (An B C A)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (simp add:Ang_roll)
  from P6 P7 show "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (blast intro:Ang_weektrans Eq_rev Ang_rev)
qed

lemma (in Congruence_Rule) Tri_week_ASA :
  assumes N :
    "Def (Tri (Tr A B C))"
    "Def (Tri (Tr A1 B1 C1))"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A1 B1)) add Emp)"
    "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C1 A1 B1)) add Emp)"
    "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An C1 B1 A1)) add Emp)"
  shows "\<not>\<not> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 C1)) add Emp)"
proof 
  assume W : "\<not> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 C1)) add Emp)"
  have P1 : "Line_on (Li B1 C1) B1" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li B1 C1) C1" by (simp add:Line_on_rule)
  from assms have P3 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C1) add Emp)" by (simp add:Tri_def)
  from assms have P4 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Tri_def)
  from P1 P2 P3 P4 have "\<exists>p. Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p C1) B1 \<and> Line_on (Li B1 C1) p \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain D1 :: Point where P5 : "Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 D1)) add Emp) 
    \<and> \<not> Bet_Point (Se D1 C1) B1 \<and> Line_on (Li B1 C1) D1 \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi D1) add Emp)" by blast
  from W have P6 : "\<not> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B C)) add Emp)" by (blast intro:Eq_rev)
  from P5 P6 have "\<not> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B1 D1)) add Emp)" by (simp add:Eq_not_trans)
  then have P7 : "\<not> Eq (Geos (Poi C1) add Emp) (Geos (Poi D1) add Emp)" by (simp add:Seg_not_Eq_Point)
  from assms have P8 : "\<not> Line_on (Li B1 C1) A1" by (simp add:Tri_def_Line)
  from P5 have P9 : "Line_on (Li B1 C1) D1" by simp
  then have P10 : "Eq (Geos (Poi D1) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> Line_on (Li B1 C1) A1" by (simp add:Point_Eq)
  from P8 P10 have P11 : "\<not> Eq (Geos (Poi D1) add Emp) (Geos (Poi A1) add Emp)" by blast
  from assms have P12 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi B1) add Emp)" by (simp add:Tri_def)
  have P13 : "Line_on (Li A1 B1) B1" by (simp add:Line_on_rule)
  from P5 have P14 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi D1) add Emp)" by simp
  from assms P7 P9 P14 have "Def (Tri (Tr A1 B1 D1))" by (blast intro:Tri_def_extension)
  then have "Def (Tri (Tr D1 B1 A1))" by (simp add:Tri_def_rev)
  then have P15 : "Def (Tri (Tr B1 A1 D1))" by (simp add:Tri_def_trans)
  from assms have P16 : "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P17 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 A1)) add Emp)" by (blast intro:Seg_rev Eq_trans)
  from P5 have P18 : "Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 D1)) add Emp)" by simp
  have P19 : "Line_on (Li B1 A1) A1" by (simp add:Line_on_rule)
  from assms have "Def (Tri (Tr C1 B1 A1))" by (simp add:Tri_def_rev)
  then have P20 : "Def (Ang (An C1 B1 A1))" by (simp add:Tri_to_Ang)
  have P21 : "Line_on (Li B1 A1) A1" by (simp add:Line_on_rule)
  have P22 : "\<not> Bet_Point (Se A1 A1) B1" by (simp add:Bet_end_Point)
  from P5 have P23 : "\<not> Bet_Point (Se C1 D1) B1" by (blast intro:Bet_rev)
  from P12 have P24 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A1) add Emp)" by (blast intro:Eq_rev)
  from P9 P14 P19 P20 P21 P22 P23 P24 have P25 : "Eq (Geos (Ang (An C1 B1 A1)) add Emp) (Geos (Ang (An D1 B1 A1)) add Emp)" by (simp add:Ang_Point_swap)
  from assms P25 have P26 : "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An D1 B1 A1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P27 : "Eq (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_roll)
  from P26 P27 have P28 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D1 B1 A1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  have P29 : "Eq (Geos (Ang (An D1 B1 A1)) add Emp) (Geos (Ang (An A1 B1 D1)) add Emp)" by (simp add:Ang_roll)  
  from P28 P29 have P30 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 D1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev Ang_rev)
  from P15 P16 P17 P18 P30 have P31 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An D1 A1 B1)) add Emp)" by (simp add:Tri_week_SAS)
  from P1 P2 P3 P5 P8 P23 have P32 : "Plane_sameside (Li A1 B1) C1 D1 \<or> Eq (Geos (Poi C1) add Emp) (Geos (Poi D1) add Emp)" by (simp add:Seg_Plane_sameside)
  from assms P31 have P33 : "Plane_sameside (Li A1 B1) C1 D1 \<Longrightarrow> Eq (Geos (Lin (Li C1 A1)) add Emp) (Geos (Lin (Li D1 A1)) add Emp)" by (simp add:Ang_move_unique)
  from assms have "\<not> Eq (Geos (Poi C1) add Emp) (Geos (Poi A1) add Emp)" by (simp add:Tri_def)
  then have P34 : "Eq (Geos (Lin (Li C1 A1)) add Emp) (Geos (Lin (Li A1 C1)) add Emp)" by (simp add:Line_rev)
  from P11 have P35 : "Eq (Geos (Lin (Li D1 A1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (simp add:Line_rev)
  from P33 P34 P35 have P36 : "Plane_sameside (Li A1 B1) C1 D1 \<Longrightarrow> Eq (Geos (Lin (Li A1 C1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  have P37 : "Line_on (Li A1 C1) C1" by (simp add:Line_on_rule)
  have P38 : "Line_on (Li A1 C1) A1" by (simp add:Line_on_rule)
  have P39 : "Line_on (Li A1 D1) D1" by (simp add:Line_on_rule)
  have P40 : "Line_on (Li A1 D1) A1" by (simp add:Line_on_rule)
  from P37 have P41 : "Eq (Geos (Poi C1) add Emp) (Geos (Poi D1) add Emp) \<Longrightarrow> Line_on (Li A1 C1) D1" by (simp add:Point_Eq)
  from P11 P38 P39 P40 P41 have P42 : "Eq (Geos (Poi C1) add Emp) (Geos (Poi D1) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li A1 C1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (simp add:Line_unique)
  from P32 P36 P42 have P43 : "Eq (Geos (Lin (Li A1 C1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by blast
  from P2 P7 P9 P37 have P44 : "Line_on (Li A1 C1) D1 \<Longrightarrow> Eq (Geos (Lin (Li B1 C1)) add Emp) (Geos (Lin (Li A1 C1)) add Emp)" by (simp add:Line_unique)
  from P1 P44 have P45 : "Line_on (Li A1 C1) D1 \<Longrightarrow> Line_on (Li A1 C1) B1" by (simp add:Line_on_trans)
  from assms have "Def (Tri (Tr C1 B1 A1))" by (simp add:Tri_def_rev)
  then have P46 : "\<not> Line_on (Li A1 C1) B1" by (simp add:Tri_def_Line)
  from P45 P46 have P47 : "\<not> Line_on (Li A1 C1) D1" by blast
  have P48 : "Line_on (Li A1 D1) D1" by (simp add:Line_on_rule)
  from P47 P48 have P49 : "\<not> Eq (Geos (Lin (Li A1 C1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (simp add:Line_not_on_Eq)
  from P43 P49 show False by blast
qed

text\<open>Theorem12\<close>

theorem (in Congruence_Rule) Tri_SAS: 
  assumes 
    "Def (Tri (Tr A B C))"
    "Def (Tri (Tr A1 B1 C1))"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A1 B1)) add Emp)"
    "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se A1 C1)) add Emp)"
    "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)"
  shows "Cong (Geos (Tri (Tr A B C)) add Emp) (Geos (Tri (Tr A1 B1 C1)) add Emp)"
proof -
  from assms have P1 : "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An C1 B1 A1)) add Emp)" by (simp add:Tri_week_SAS)
  have P2 : "Eq (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An C A B)) add Emp)" by (simp add:Ang_roll)
  have P3 : "Eq (Geos (Ang (An C1 A1 B1)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)" by (simp add:Ang_roll)
  from assms P2 have P4 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from P3 P4 have P5 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C1 A1 B1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms P1 P5 have P6 : "\<not>\<not> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 C1)) add Emp)" by (simp add:Tri_week_ASA)
  from assms have P7 : "Eq (Geos (Seg (Se C A)) add Emp) (Geos (Seg (Se C1 A1)) add Emp)" by (blast intro:Seg_rev Eq_rev Eq_trans)
  from assms have P8 : "Def (Tri (Tr A C B))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P9 : "Def (Tri (Tr A1 C1 B1))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms P5 P8 P9 have P10 : "Cong (Geos (Ang (An B C A)) add Emp) (Geos (Ang (An B1 C1 A1)) add Emp)" by (simp add:Tri_week_SAS)
  have P11 : "Eq (Geos (Ang (An B C A)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (simp add:Ang_roll)
  have P12 : "Eq (Geos (Ang (An B1 C1 A1)) add Emp) (Geos (Ang (An A1 C1 B1)) add Emp)" by (simp add:Ang_roll)
  from P10 P11 have P13 : "Cong (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An B1 C1 A1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from P10 P12 P13 have P14 : "Cong (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An A1 C1 B1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms P1 P6 P7 P14 show "Cong (Geos (Tri (Tr A B C)) add Emp) (Geos (Tri (Tr A1 B1 C1)) add Emp)" by (simp add:Tri_Cong_def)
qed

text\<open>Theorem13\<close>

theorem (in Congruence_Rule) Tri_ASA: 
  assumes
    "Def (Tri (Tr A B C))"
    "Def (Tri (Tr A1 B1 C1))"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A1 B1)) add Emp)"
    "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An C1 B1 A1)) add Emp)"
    "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C1 A1 B1)) add Emp)"
  shows "Cong (Geos (Tri (Tr A B C)) add Emp) (Geos (Tri (Tr A1 B1 C1)) add Emp)"
proof -
  from assms have P1 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 A1)) add Emp)" by (blast intro:Seg_rev Eq_rev Eq_trans)
  from assms have P2 : "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P3 : "Def (Tri (Tr B1 A1 C1))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms P1 P2 P3 have P4 : "\<not>\<not> Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se A1 C1)) add Emp)" by (simp add:Tri_week_ASA)
  have P5 : "Eq (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Ang_roll)
  have P6 : "Eq (Geos (Ang (An C1 A1 B1)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)" by (simp add:Ang_roll)
  from assms P5 have P7 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An C1 A1 B1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from P6 P7 have P8 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev Ang_rev)
  from assms P1 P4 P8 show "Cong (Geos (Tri (Tr A B C)) add Emp) (Geos (Tri (Tr A1 B1 C1)) add Emp)" by (simp add:Tri_SAS)
qed

text\<open>Theorem14\<close>

theorem (in Congruence_Rule) Ang_complementary :
  assumes
    "Def (Ang (An A B C))"
    "Def (Ang (An A1 B1 C1))"
    "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A1 B1 C1)) add Emp)"
    "Bet_Point (Se A D) B"
    "Bet_Point (Se A1 D1) B1"
  shows
    "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An C1 B1 D1)) add Emp)"
proof -
  from assms have "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B1 C1)) add Emp)
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 p)) add Emp)
    \<and> Line_on (Li B1 A1) p \<and> \<not> Bet_Point (Se p A1) B1 \<and> Def (Ang (An p B1 C1))" by (simp add:Ang_replace)
  then obtain A2 :: Point where P1 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A2 B1 C1)) add Emp) 
    \<and> Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B1 A2)) add Emp) \<and> Line_on (Li B1 A1) A2
    \<and> \<not> Bet_Point (Se A2 A1) B1 \<and> Def (Ang (An A2 B1 C1))" by blast
  from assms P1 have "\<exists>p. Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A2 B1 p)) add Emp)
    \<and> Eq (Geos (Ang (An A2 B1 C1)) add Emp) (Geos (Ang (An A2 B1 p)) add Emp) 
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 p)) add Emp) 
    \<and> Line_on (Li B1 C1) p \<and> \<not> Bet_Point (Se p C1) B1 \<and> Def (Ang (An A2 B1 p))" by (simp add:Ang_replace)
  then obtain C2 :: Point where P2 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A2 B1 C2)) add Emp) 
    \<and> Eq (Geos (Seg (Se B C)) add Emp) (Geos (Seg (Se B1 C2)) add Emp) \<and> Line_on (Li B1 C1) C2
    \<and> \<not> Bet_Point (Se C2 C1) B1 \<and> Def (Ang (An A2 B1 C2))" by blast
  from assms have "Def (Tri (Tr A B C))" by (simp add:Ang_to_Tri)
  then have P3 : "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P2 have "Def (Tri (Tr A2 B1 C2))" by (simp add:Ang_to_Tri)
  then have P4 : "Def (Tri (Tr B1 A2 C2))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P1 P2 P3 P4 have P5 : "Cong (Geos (Tri (Tr B A C)) add Emp) (Geos (Tri (Tr B1 A2 C2)) add Emp)" by (simp add:Tri_SAS)
  then have P6 : "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by (simp add:Tri_Cong_def)
  from P5 have P7 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C2 A2 B1)) add Emp)" by (simp add:Tri_Cong_def)
  have P8 : "Line_on (Li B1 D1) B1" by (simp add:Line_on_rule)
  from assms have P9 : "Line_on (Li A1 D1) B1" by (simp add:Line_Bet_on)
  from assms have p10 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A1) add Emp)" by (simp add:Bet_Point_def)
  from assms have P11 : "Line_on (Li B1 A1) D1" by (simp add:Line_Bet_on)
  have P12 : "Line_on (Li B1 D1) D1" by (simp add:Line_on_rule)
  have P13 : "Line_on (Li B1 A1) B1" by (simp add:Line_on_rule)
  from assms have P14 : "\<not> Eq (Geos (Poi D1) add Emp) (Geos (Poi B1) add Emp)" by (simp add:Bet_Point_def)
  from P8 P11 P12 P13 P14 have P15 : "Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li B1 D1)) add Emp)" by (simp add:Line_unique)
  from P1 P15 have P16 : "Line_on (Li B1 D1) A2" by (simp add:Line_on_trans)
  from P4 have P17 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Tri_def)
  from assms have P18 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  then have P19 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P8 P16 P17 P19 have "\<exists>p. Eq (Geos (Seg (Se B D)) add Emp) (Geos (Seg (Se B1 p)) add Emp)
    \<and> Bet_Point (Se p A2) B1 \<and> Line_on (Li B1 D1) p \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_diffside)
  then obtain D2 :: Point where P20 : "Eq (Geos (Seg (Se B D)) add Emp) (Geos (Seg (Se B1 D2)) add Emp)
    \<and> Bet_Point (Se D2 A2) B1 \<and> Line_on (Li B1 D1) D2 \<and> \<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi D2) add Emp)" by blast
  from P1 have P21 : "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A2 B1)) add Emp)" by (blast intro:Seg_rev Eq_trans)
  from P20 have P22 : "Bet_Point (Se A2 D2) B1" by (blast intro:Bet_rev)
  from assms P20 P21 P22 have P23 : "Eq (Geos (Seg (Se A D)) add Emp) (Geos (Seg (Se A2 D2)) add Emp)" by (blast intro:Seg_Bet_add)
  from P3 have P24 : "Def (Tri (Tr C A B))" by (blast intro:Tri_def_rev)
  from assms have P25 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from assms have P26 : "Line_on (Li A B) D" by (simp add:Line_Bet_on)
  from P24 P25 P26 have P27 : "Def (Tri (Tr C A D))" by (simp add:Tri_def_extension)
  from P4 have P28 : "Def (Tri (Tr C2 A2 B1))" by (blast intro:Tri_def_rev)
  from P22 have P29 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi D2) add Emp)" by (simp add:Bet_Point_def)
  from P22 have P30 : "Line_on (Li A2 B1) D2" by (simp add:Line_Bet_on)
  from P28 P29 P30 have P31 : "Def (Tri (Tr C2 A2 D2))" by (simp add:Tri_def_extension)
  from P24 have P32 : "Def (Ang (An C A B))" by (simp add:Tri_to_Ang)
  from P27 have P33 : "Def (Ang (An C A D))" by (simp add:Tri_to_Ang)
  have P34 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  have P35 : "\<not> Bet_Point (Se C C) A" by (simp add:Bet_end_Point)
  from assms have "Inv (Bet_Point (Se D B) A)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se D B) A" by (simp add:Inv_def)
  then have P36 : "\<not> Bet_Point (Se B D) A" by (blast intro:Bet_rev)
  from P33 have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Ang_def)
  then have P37 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P25 P26 P32 P33 P34 P35 P36 P37 have P38 : "Eq (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (simp add:Ang_Point_swap)
  from P28 have P39 : "Def (Ang (An C2 A2 B1))" by (simp add:Tri_to_Ang)
  from P31 have P40 : "Def (Ang (An C2 A2 D2))" by (simp add:Tri_to_Ang)
  have P41 : "Line_on (Li A2 C2) C2" by (simp add:Line_on_rule)
  have P42 : "\<not> Bet_Point (Se C2 C2) A2" by (simp add:Bet_end_Point)
  from P20 have "Inv (Bet_Point (Se B1 D2) A2)" by (simp add:Bet_iff)
  then have P43 : "\<not> Bet_Point (Se B1 D2) A2" by (simp add:Inv_def)
  from P40 have "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Ang_def)
  then have P44 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi C2) add Emp)" by (blast intro:Eq_rev)
  from P29 P30 P39 P40 P41 P42 P43 P44 have P45 : "Eq (Geos (Ang (An C2 A2 B1)) add Emp) (Geos (Ang (An C2 A2 D2)) add Emp)" by (simp add:Ang_Point_swap)
  from P7 P38 have P46 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An C2 A2 B1)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from P45 P46 have P47 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An C2 A2 D2)) add Emp)" by (blast intro:Ang_weektrans Eq_rev Ang_rev)
  from P27 have P48 : "Def (Tri (Tr A C D))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P31 have P49 : "Def (Tri (Tr A2 C2 D2))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P6 P23 P47 P48 P49 have P50 : "Cong (Geos (Tri (Tr A C D)) add Emp) (Geos (Tri (Tr A2 C2 D2)) add Emp)" by (simp add:Tri_SAS)
  then have P51 : "Cong (Geos (Ang (An A D C)) add Emp) (Geos (Ang (An A2 D2 C2)) add Emp)" by (simp add:Tri_Cong_def)
  from P50 have "Eq (Geos (Seg (Se C D)) add Emp) (Geos (Seg (Se C2 D2)) add Emp)" by (simp add:Tri_Cong_def)
  then have P52 : "Eq (Geos (Seg (Se D C)) add Emp) (Geos (Seg (Se D2 C2)) add Emp)" by (blast intro:Seg_rev Eq_trans)
  from assms have P53 : "Line_on (Li D A) B" by (simp add:Bet_rev Line_Bet_on)
  from assms have "Inv (Bet_Point (Se B A) D)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se B A) D" by (simp add:Inv_def)
  then have P54 : "\<not> Bet_Point (Se A B) D" by (blast intro:Bet_rev)
  have P55 : "Line_on (Li D C) C" by (simp add:Line_on_rule)
  have P56 : "\<not> Bet_Point (Se C C) D" by (simp add:Bet_end_Point)
  from P48 have P57 : "Def (Ang (An A D C))" by (simp add:Tri_to_Ang Ang_def_inv)
  from P57 have P58 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi C) add Emp)" by (simp add:Ang_def)
  from P18 P53 P54 P55 P56 P57 P58 have P59 : "Eq (Geos (Ang (An A D C)) add Emp) (Geos (Ang (An B D C)) add Emp) \<and> Def (Ang (An B D C))" by (simp add:Ang_Point_swap)
  from P22 have P60 : "Line_on (Li D2 A2) B1" by (simp add:Line_Bet_on)
  from P20 have "Inv (Bet_Point (Se A2 B1) D2)" by (simp add:Bet_iff)
  then have P61 : "\<not> Bet_Point (Se A2 B1) D2" by (simp add:Inv_def)
  have P62 : "Line_on (Li D2 C2) C2" by (simp add:Line_on_rule)
  have P63 : "\<not> Bet_Point (Se C2 C2) D2" by (simp add:Bet_end_Point)
  from P49 have P64 : "Def (Ang (An A2 D2 C2))" by (simp add:Tri_to_Ang Ang_def_inv)
  from P20 have P65 : "\<not> Eq (Geos (Poi D2) add Emp) (Geos (Poi B1) add Emp)" by (blast intro:Eq_rev)
  from P64 have P66 : "\<not> Eq (Geos (Poi D2) add Emp) (Geos (Poi C2) add Emp)" by (simp add:Ang_def)
  from P60 P61 P62 P63 P64 P65 P66 have P67 : "Eq (Geos (Ang (An A2 D2 C2)) add Emp) (Geos (Ang (An B1 D2 C2)) add Emp) \<and> Def (Ang (An B1 D2 C2))" by (simp add:Ang_Point_swap)
  from P51 P59 have P68 : "Cong (Geos (Ang (An B D C)) add Emp) (Geos (Ang (An A2 D2 C2)) add Emp)" by (blast intro:Ang_weektrans Eq_rev)
  from P67 P68 have P69 : "Cong (Geos (Ang (An B D C)) add Emp) (Geos (Ang (An B1 D2 C2)) add Emp)" by (blast intro:Ang_weektrans Eq_rev Ang_rev)
  from P59 have "Def (Tri (Tr B D C))" by (simp add:Ang_to_Tri)
  then have P70 : "Def (Tri (Tr D B C))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P67 have "Def (Tri (Tr B1 D2 C2))" by (simp add:Ang_to_Tri)
  then have P71 : "Def (Tri (Tr D2 B1 C2))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P20 have "Eq (Geos (Seg (Se B D)) add Emp) (Geos (Seg (Se B1 D2)) add Emp)" by simp
  then have P72 : "Eq (Geos (Seg (Se D B)) add Emp) (Geos (Seg (Se D2 B1)) add Emp)" by (blast intro:Seg_rev Eq_trans)
  from P52 P69 P70 P71 P72 have "Cong (Geos (Tri (Tr D B C)) add Emp) (Geos (Tri (Tr D2 B1 C2)) add Emp)" by (simp add:Tri_SAS)
  then have P73 : "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An C2 B1 D2)) add Emp)" by (simp add:Tri_Cong_def)
  from P71 have "Def (Tri (Tr C2 B1 D2))" by (blast intro:Tri_def_rev)
  then have P74 : "Def (Ang (An C2 B1 D2))" by (simp add:Tri_to_Ang)
  from assms have P75 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C1) add Emp)" by (simp add:Ang_def)
  from P71 have P76 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C2) add Emp)" by (simp add:Tri_def)
  from P2 P75 P76 have P77 : "Line_on (Li B1 C2) C1" by (simp add:Line_on_rev)
  from P14 have P78 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi D1) add Emp)" by (blast intro:Eq_rev)
  from P74 have P79 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi D2) add Emp)" by (simp add:Ang_def)
  from P20 P78 P79 have P80 : "Line_on (Li B1 D2) D1" by (simp add:Line_on_rev)
  from assms have "\<not> Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Ang_def)
  then have P81 : "\<not> Eq (Geos (Lin (Li B1 C1)) add Emp) (Geos (Lin (Li B1 A1)) add Emp)" by (blast intro:Eq_rev)
  have P82 : "Line_on (Li A1 D1) D1" by (simp add:Line_on_rule)
  from P9 P11 P13 P14 P82 have P83 : "Eq (Geos (Lin (Li B1 A1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (simp add:Line_unique)
  from P81 P83 have P84 : "\<not> Eq (Geos (Lin (Li B1 C1)) add Emp) (Geos (Lin (Li A1 D1)) add Emp)" by (simp add:Eq_not_trans)
  then have P85 : "\<not> Eq (Geos (Lin (Li A1 D1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (blast intro:Eq_rev)
  have P86 : "Line_on (Li B1 C1) B1" by (simp add:Line_on_rule)
  from assms P85 P86 have P87 : "Plane_diffside (Li B1 C1) A1 D1" by (simp add:Plane_Bet_diffside)
  then have P88 : "Plane_diffside (Li B1 C1) D1 A1" by (simp add:Plane_diffside_rev)
  have P89 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Line_on (Li D2 D1) B1" by (simp add:Line_Bet_on)
  have P90 : "Line_on (Li D2 D1) D1" by (simp add:Line_on_rule)
  from P9 P14 P82 P89 P90 have P91 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Eq (Geos (Lin (Li A1 D1)) add Emp) (Geos (Lin (Li D2 D1)) add Emp)" by (simp add:Line_unique)
  from P84 P91 have "Bet_Point (Se D2 D1) B1 \<Longrightarrow> \<not> Eq (Geos (Lin (Li B1 C1)) add Emp) (Geos (Lin (Li D2 D1)) add Emp)" by (simp add:Eq_not_trans)
  then have P92 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> \<not> Eq (Geos (Lin (Li D2 D1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (blast intro:Eq_rev)
  from P86 P92 have "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Plane_diffside (Li B1 C1) D2 D1" by (simp add:Plane_Bet_diffside)
  then have P93 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Plane_diffside (Li B1 C1) D1 D2" by (simp add:Plane_diffside_rev)
  from P20 have "Eq (Geos (Poi D2) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> Bet_Point (Se A1 A2) B1" by (blast intro:Bet_Point_Eq)
  then have P94 : "Eq (Geos (Poi D2) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> Bet_Point (Se A2 A1) B1" by (simp add:Bet_rev)
  from P1 P94 have P95 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi D2) add Emp)" by (blast intro:Eq_rev)
  from P88 P93 P95 have "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Plane_sameside (Li B1 C1) A1 D2" by (blast intro:Plane_trans_inv)
  then have P96 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> Plane_sameside (Li B1 C1) D2 A1" by (simp add:Plane_sameside_rev)
  from P1 have "Def (Tri (Tr A2 B1 C1))" by (simp add:Ang_to_Tri)
  then have P97 : "\<not> Line_on (Li B1 C1) A2" by (simp add:Tri_def_Line)
  have "Line_on (Li D2 A2) A2" by (simp add:Line_on_rule)
  then have P98 : "Eq (Geos (Lin (Li D2 A2)) add Emp) (Geos (Lin (Li B1 C1)) add Emp) \<Longrightarrow> Line_on (Li B1 C1) A2" by (simp add:Line_on_trans)
  from P97 P98 have P99 : "\<not> Eq (Geos (Lin (Li D2 A2)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by blast
  from P20 have P100 : "Bet_Point (Se D2 A2) B1" by simp
  from P86 P99 P100 have P101 : "Plane_diffside (Li B1 C1) D2 A2" by (simp add:Plane_Bet_diffside)
  from P96 P101 have "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se D2 D1) B1 \<Longrightarrow>
    Plane_diffside (Li B1 C1) A1 A2" by (simp add:Plane_trans)
  then have P102 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se D2 D1) B1 \<Longrightarrow>
    \<not> Plane_sameside (Li B1 C1) A1 A2" by (simp add:Plane_diffside_not_sameside)
  have P103 : "Line_on (Li B1 A1) A1" by (simp add:Line_on_rule)
  from assms have "Def (Tri (Tr C1 B1 A1))" by (simp add:Ang_to_Tri Tri_def_rev)
  then have P104 : "\<not> Line_on (Li B1 A1) C1" by (simp add:Tri_def_Line)
  from P4 have P105 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Tri_def)
  from P1 p10 P13 P103 P104 P105 have P106 : "Plane_sameside (Li C1 B1) A2 A1 \<or> Eq (Geos (Poi A2) add Emp) (Geos (Poi A1) add Emp)" by (simp add:Seg_Plane_sameside)
  from assms have "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi C1) add Emp)" by (simp add:Ang_def)
  then have P107 : "Eq (Geos (Lin (Li C1 B1)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (simp add:Line_rev Eq_rev)
  from P106 P107 have P108 : "Plane_sameside (Li B1 C1) A1 A2 \<or> Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp)" by (blast intro:Plane_sameside_rev Plane_Line_trans Eq_rev)
  from P102 P108 have P109 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> \<not> Bet_Point (Se D2 D1) B1" by blast
  from P22 have P110 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se A1 D2) B1" by (blast intro:Bet_Point_Eq Eq_rev)
  then have P111 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Line_on (Li A1 D2) B1" by (simp add:Line_Bet_on)
  have P112 : "Line_on (Li A1 D2) A1" by (simp add:Line_on_rule)
  have P113 : "Line_on (Li A1 D1) A1" by (simp add:Line_on_rule)
  from p10 have P114 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi B1) add Emp)" by (blast intro:Eq_rev)
  from P9 P111 P112 P113 P114 have P115 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Eq (Geos (Lin (Li A1 D1)) add Emp) (Geos (Lin (Li A1 D2)) add Emp)" by (simp add:Line_unique)
  from P84 P115 have "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> \<not> Eq (Geos (Lin (Li B1 C1)) add Emp) (Geos (Lin (Li A1 D2)) add Emp)" by (simp add:Eq_not_trans)
  then have P116 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> \<not> Eq (Geos (Lin (Li A1 D2)) add Emp) (Geos (Lin (Li B1 C1)) add Emp)" by (blast intro:Eq_rev)
  from P86 P110 P116 have P117 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Plane_diffside (Li B1 C1) A1 D2" by (simp add:Plane_Bet_diffside)
  have "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se D2 D1) B1 \<Longrightarrow> \<not> Eq (Geos (Poi D2) add Emp) (Geos (Poi D1) add Emp)" by (simp add:Bet_Point_def)
  then have P118 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se D2 D1) B1 \<Longrightarrow>
    \<not> Eq (Geos (Poi D1) add Emp) (Geos (Poi D2) add Emp)" by (blast intro:Eq_rev)
  from P87 P117 P118 have P119 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> Bet_Point (Se D2 D1) B1 \<Longrightarrow>
    Plane_sameside (Li B1 C1) D1 D2" by (blast intro:Plane_trans_inv)
  from P93 have P120 : "Bet_Point (Se D2 D1) B1 \<Longrightarrow> \<not> Plane_sameside (Li B1 C1) D1 D2" by (simp add:Plane_diffside_not_sameside)
  from P119 P120 have P121 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi A2) add Emp) \<Longrightarrow> \<not> Bet_Point (Se D2 D1) B1" by blast
  from P109 P121 have P122 : "\<not> Bet_Point (Se D2 D1) B1" by blast
  from P2 P74 P75 P77 P78 P80 P122 have P123 : "Eq (Geos (Ang (An C2 B1 D2)) add Emp) (Geos (Ang (An C1 B1 D1)) add Emp)" by (simp add:Ang_Point_swap)
  from P73 P123 show "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An C1 B1 D1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
qed

theorem (in Congruence_Rule) Ang_vertical :
  assumes
    "Def (Ang (An A B C))"
    "Bet_Point (Se A D) B"
    "Bet_Point (Se C E) B"
  shows "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D B E)) add Emp)"
    and "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An A B E)) add Emp)"
proof -
  have P1 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An C B A)) add Emp)" by (simp add:Ang_roll)
  from assms have P2 : "Def (Ang (An C B A))" by (simp add:Ang_def_rev)
  from assms P1 P2 show "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An A B E)) add Emp)" by (simp add:Ang_complementary)
  from assms have P3 : "Line_on (Li B A) D" by (simp add:Line_Bet_on)
  from assms have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  then have P4 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P2 P3 P4 have P5 : "Def (Ang (An C B D))" by (simp add:Ang_def_extension)
  then have P6 : "Def (Ang (An D B C))" by (simp add:Ang_def_rev)
  have P7 : "Cong (Geos (Ang (An C B D)) add Emp) (Geos (Ang (An D B C)) add Emp)" by (simp add:Ang_roll)
  from assms have P8 : "Bet_Point (Se D A) B" by (simp add:Bet_rev)
  from assms P5 P6 P7 P8 have P9 : "Cong (Geos (Ang (An D B E)) add Emp) (Geos (Ang (An C B A)) add Emp)" by (simp add:Ang_complementary)
  from P1 have P10 : "Eq (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_roll)
  from P9 P10 show "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D B E)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
qed

lemma (in Congruence_Rule) Ang_inside_Planeside : 
  assumes "Ang_inside (An A B C) D"
  shows "Plane_diffside (Li B D) A C"
proof -
  from assms have P1 : "Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D" by (simp add:Ang_inside_def)
  then have P2 : "\<not> Line_on (Li B A) C" by (simp add:Plane_sameside_def)
  have P3 :  "Line_on (Li B A) B" by (simp add:Line_on_rule)
  then have P4 : "Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li B A) C" by (simp add:Point_Eq)
  from P2 P4 have P5 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  have P6 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P7 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P5 P6 P7 have "\<exists>p. Bet_Point (Se C p) B \<and> Line_on (Li B C) p" by (simp add:Bet_extension)
  then obtain E :: Point where P8 : "Bet_Point (Se C E) B \<and> Line_on (Li B C) E" by blast
  then have P9 : "Line_on (Li C E) B" by (simp add:Line_Bet_on)
  have P10 : "Line_on (Li C E) C" by (simp add:Line_on_rule)
  from P5 P6 P7 P9 P10 have P11 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li C E)) add Emp)" by (simp add:Line_unique)
  from P1 have P12 : "\<not> Line_on (Li B C) A" by (simp add:Plane_sameside_def) 
  from P11 P12 have P13 : "\<not> Line_on (Li C E) A" by (simp add:Line_not_on_trans)
  have P14 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  from P1 have P15 : "\<not> Line_on (Li B A) D" by (simp add:Plane_sameside_def)
  from P3 have P16 : "Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li B A) D" by (simp add:Point_Eq)
  from P15 P16 have P17 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by blast
  from P6 have P18 : "Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Point_Eq)
  from P12 P18 have P19 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by blast
  from P17 P19 have P20 : "Line_on (Li B D) A \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_rev)
  from P15 P20 have P21 : "\<not> Line_on (Li B D) A" by blast
  from P1 have P22 : "\<not> Line_on (Li B C) D" by (simp add:Plane_sameside_def)
  from P5 have P23 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P17 P23 have P24 : "Line_on (Li B D) C \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_on_rev)
  from P22 P24 have P25 : "\<not> Line_on (Li B D) C" by blast
  from P8 have P26 : "Bet_Point (Se C E) B" by simp
  then have P27 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  from P8 have P28 : "Line_on (Li B C) E" by simp 
  from P6 P14 P27 P28 have P29 : "Line_on (Li B D) E \<Longrightarrow> Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from P7 P29 have P30 : "Line_on (Li B D) E \<Longrightarrow> Line_on (Li B D) C" by (simp add:Line_on_trans)
  from P25 P30 have P31 : "\<not> Line_on (Li B D) E" by blast
  from P13 P14 P21 P25 P26 P31 have P32 : "Line_on_Seg (Li B D) (Se C A) \<and> \<not> Line_on_Seg (Li B D) (Se E A)
        \<or> Line_on_Seg (Li B D) (Se E A) \<and> \<not> Line_on_Seg (Li B D) (Se C A)" by (simp add:Pachets_axiom)
  have "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<exists>p. Line_on (Li B D) p \<and> Bet_Point (Se E A) p" by (simp add:Line_on_Seg_rule)
  then obtain F :: Point where P33 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Line_on (Li B D) F \<and> Bet_Point (Se E A) F" by blast
  then have P34 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se A E) F" by (simp add:Bet_rev)
  from P3 have P35 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li A E)) add Emp) \<Longrightarrow> Line_on (Li A E) B" by (simp add:Line_on_trans)
  have P36 : "Line_on (Li A E) E" by (simp add:Line_on_rule)
  from P6 P27 P28 P35 P36 have "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li A E)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  then have P37 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li A E)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (blast intro:Eq_trans)
  have P38 : "Line_on (Li B A) A" by (simp add:Line_on_rule)  
  from P37 P38 have P39 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from P12 P39 have P40 : "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by blast
  from P37 P40 have P41 : "\<not> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_rev)
  from P34 P38 P41 have P42 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_sameside (Li B A) E F" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  from P11 have P43 : "Eq (Geos (Lin (Li C E)) add Emp) (Geos (Lin (Li B A)) add Emp) \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (blast intro:Eq_trans)
  from P40 P43 have P44 : "\<not> Eq (Geos (Lin (Li C E)) add Emp) (Geos (Lin (Li B A)) add Emp)" by blast
  from P3 P26 P44 have P45 : "Plane_diffside (Li B A) E C" by (simp add:Plane_Bet_diffside Plane_diffside_rev)
  from P34 have P46 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Line_on (Li A E) F" by (simp add:Line_Bet_on)
  have P47 : "Line_on (Li C E) E" by (simp add:Line_on_rule)
  have P48 : "Line_on (Li A E) A" by (simp add:Line_on_rule)
  from P42 P45 have P49 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_diffside (Li B A) F C" by (simp add:Plane_trans)
  from P1 have P50 : "Plane_sameside (Li B A) C D" by (simp add:Point_Eq)
  then have "Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Plane_sameside (Li B A) C F" by (simp add:Point_Eq)
  then have "Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> \<not> Plane_diffside (Li B A) C F" by (simp add:Plane_sameside_not_diffside)
  then have P51 : "Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> \<not> Plane_diffside (Li B A) F C" by (blast intro:Plane_diffside_rev)
  from P49 P51 have P52 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp)" by blast
  from P49 P50 have P53 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_diffside (Li B A) D F" by (simp add:Plane_trans Plane_diffside_rev)
  from P46 have P54 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow>
    Line_on (Li A E) B" by (simp add:Point_Eq)
  from P26 have P55 : "Line_on (Li C E) B" by (simp add:Line_Bet_on)
  from P27 P36 P47 P54 P55 have P56 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li C E)) add Emp)" by (simp add:Line_unique)
  from P48 P56 have P57 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow>
    Line_on (Li C E) A" by (simp add:Line_on_trans)
  from P13 P57 have P58 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp)" by blast
  have P59 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  from P14 P17 P33 P52 P58 P59 have P60 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se B F) D \<or> Bet_Point (Se F D) B \<or> Bet_Point (Se D B) F" by (simp add:Bet_case)
  have P61 : "Line_on (Li B F) B" by (simp add:Line_on_rule)
  have P62 : "Line_on (Li B F) F" by (simp add:Line_on_rule)
  from P33 have P63 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Line_on (Li B D) F" by simp
  from P14 P58 P61 P62 P63 have "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Eq (Geos (Lin (Li B F)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  then have P64 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Eq (Geos (Lin (Li B F)) add Emp) (Geos (Lin (Li B A)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_trans)
  from P38 have P65 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B D)) add Emp) \<Longrightarrow> Line_on (Li B D) A" by (simp add:Line_on_trans)
  from P21 P65 have P66 : "\<not> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_rev)
  from P64 P66 have P67 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Eq (Geos (Lin (Li B F)) add Emp) (Geos (Lin (Li B A)) add Emp)" by blast
  from P3 P67 have "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se B F) D \<Longrightarrow> Plane_sameside (Li B A) D F" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  then have P68 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se B F) D \<Longrightarrow> \<not> Plane_diffside (Li B A) D F" by (simp add:Plane_sameside_not_diffside)
  from P53 P68 have P69 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Bet_Point (Se B F) D" by blast
  have P70 : "Bet_Point (Se D B) F \<Longrightarrow> Bet_Point (Se B D) F" by (simp add:Bet_rev)
  from P3 P66 P70 have "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se D B) F \<Longrightarrow> Plane_sameside (Li B A) D F" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  then have P71 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se D B) F \<Longrightarrow> \<not> Plane_diffside (Li B A) D F" by (simp add:Plane_sameside_not_diffside)
  from P53 P71 have P72 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Bet_Point (Se D B) F" by blast
  from P60 P69 P72 have P73 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se F D) B" by blast
  have "Line_on (Li F D) D" by (simp add:Line_on_rule)
  then have P74 : "Eq (Geos (Lin (Li F D)) add Emp) (Geos (Lin (Li B C)) add Emp) \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_on_trans)
  from P22 P74 have P75 : "\<not> Eq (Geos (Lin (Li F D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by blast
  from P6 P73 P75 have P76 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_diffside (Li B C) F D" by (simp add:Plane_Bet_diffside)
  from P33 have P77 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Bet_Point (Se E A) F" by simp
  have "Line_on (Li E A) A" by (simp add:Line_on_rule)
  then have P78 : "Eq (Geos (Lin (Li E A)) add Emp) (Geos (Lin (Li C E)) add Emp) \<Longrightarrow> Line_on (Li C E) A" by (simp add:Line_on_trans)
  from P13 P78 have P79 : "\<not> Eq (Geos (Lin (Li E A)) add Emp) (Geos (Lin (Li C E)) add Emp)" by blast
  from P47 P77 P79 have P80 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_sameside (Li C E) F A" by (simp add:Plane_Bet_sameside)
  from P11 P80 have P81 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_sameside (Li B C) F A" by (blast intro:Eq_rev Plane_Line_trans)
  from P76 P81 have "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_diffside (Li B C) A D" by (simp add:Plane_trans)
  then have P82 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<not> Plane_sameside (Li B C) A D" by (simp add:Plane_diffside_not_sameside)
  from P1 P82 have P83 : "\<not> Line_on_Seg (Li B D) (Se E A)" by blast
  from P32 P83 have "Line_on_Seg (Li B D) (Se C A)" by blast
  then have P84 : "\<exists>p. Line_on (Li B D) p \<and> Bet_Point (Se C A) p" by (simp add:Line_on_Seg_rule)
  from P21 P25 P84 have "\<exists>p. Bet_Point (Se C A) p \<and> Line_on (Li B D) p \<and> \<not> Line_on (Li B D) C \<and> \<not> Line_on (Li B D) A" by blast
  then have "Plane_diffside (Li B D) C A" by (simp add:Plane_diffside_def)
  thus "Plane_diffside (Li B D) A C" by (simp add:Plane_diffside_rev)
qed

lemma (in Congruence_Rule) Ang_inside_Bet_Point : 
  assumes 
    "Bet_Point (Se p1 p3) p2"
    "\<not> Eq (Geos (Lin (Li p4 p1)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)"          
    "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p1) add Emp)"
    "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p3) add Emp)"
  shows "Ang_inside (An p1 p4 p3) p2"
proof -
  have P1 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p4 p1) p4" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li p4 p1) p1" by (simp add:Line_on_rule)
  have P5 : "Line_on (Li p4 p3) p4" by (simp add:Line_on_rule)
  have P6 : "Line_on (Li p4 p3) p3" by (simp add:Line_on_rule)
  from assms have P7 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P2 have P8 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p1)) add Emp) \<Longrightarrow> Line_on (Li p4 p1) p3" by (simp add:Line_on_trans)
  from assms P3 P5 P6 P8 have P9 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li p4 p1)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)" by (simp add:Line_unique)
  from assms P9 have P10 : "\<not> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p1)) add Emp)" by blast
  from P1 have P11 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p3)) add Emp) \<Longrightarrow> Line_on (Li p4 p3) p1" by (simp add:Line_on_trans)
  from assms P3 P4 P5 P11 have P12 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p3)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li p4 p1)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)" by (simp add:Line_unique)
  from assms P12 have P13 : "\<not> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)" by blast
  from assms P4 P10 have "Plane_sameside (Li p4 p1) p2 p3" by (simp add:Plane_Bet_sameside)
  then have P14 : "Plane_sameside (Li p4 p1) p3 p2" by (simp add:Plane_sameside_rev)
  from assms have P15 : "Bet_Point (Se p3 p1) p2" by (simp add:Bet_rev)
  from P7 have P16 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p3 p1)) add Emp)" by (simp add:Line_rev)
  from P13 P16 have P17 : "\<not> Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from assms P6 P15 P17 have "Plane_sameside (Li p4 p3) p2 p1" by (simp add:Plane_Bet_sameside)
  then have P18 : "Plane_sameside (Li p4 p3) p1 p2" by (simp add:Plane_sameside_rev)
  from assms have P19 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)" by (blast intro:Eq_rev)
  from P7 have P20 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from assms P19 P20 have P21 : "Def (Ang (An p1 p4 p3))" by (simp add:Ang_def)
  from P14 P18 P21 show "Ang_inside (An p1 p4 p3) p2" by (simp add:Ang_inside_def)
qed

lemma (in Congruence_Rule) Ang_inside_HalfLine : 
  assumes 
    "Ang_inside (An A B C) D"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi E) add Emp)"
    "Line_on (Li B D) E"
    "\<not> Bet_Point (Se E D) B"
  shows 
    "Ang_inside (An A B C) E"
proof -
  from assms have P1 : "Def (Ang (An A B C)) \<and> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D" by (simp add:Ang_inside_def)
  have "Plane_diffside (Li B A) C E \<Longrightarrow> \<exists>p. Bet_Point (Se C E) p \<and> Line_on (Li B A) p
    \<and> \<not> Line_on (Li B A) C \<and> \<not> Line_on (Li B A) E" by (simp add:Plane_diffside_def)
  then obtain p1 :: Point where "Plane_diffside (Li B A) C E \<Longrightarrow> Bet_Point (Se C E) p1" by blast
  from assms P1 have "Plane_diffside (Li B A) C E \<Longrightarrow> Plane_diffside (Li B A) D E" by (blast intro:Plane_trans)
  then have "Plane_diffside (Li B A) C E \<Longrightarrow> \<exists>p. Bet_Point (Se D E) p \<and> Line_on (Li B A) p 
    \<and> \<not> Line_on (Li B A) D \<and> \<not> Line_on (Li B A) E" by (simp add:Plane_diffside_def)
  then obtain F :: Point where P2 : "Plane_diffside (Li B A) C E \<Longrightarrow> Bet_Point (Se D E) F \<and> Line_on (Li B A) F" by blast
  then have "Plane_diffside (Li B A) C E \<Longrightarrow> Bet_Point (Se E D) F" by (simp add:Bet_rev)
  then have P3 : "Plane_diffside (Li B A) C E \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp)
    \<Longrightarrow> Bet_Point (Se E D) B" by (simp add:Point_Eq)
  from assms P3 have P4 : "Plane_diffside (Li B A) C E \<Longrightarrow> \<not> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp)" by blast
  have P5 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  have P6 : "Line_on (Li E D) E" by (simp add:Line_on_rule)
  have P7 : "Line_on (Li E D) D" by (simp add:Line_on_rule)
  from assms P5 P6 P7 have P8 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li E D)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from P2 have P9 : "Plane_diffside (Li B A) C E \<Longrightarrow> Line_on (Li E D) F" by (simp add:Line_Bet_on)
  from P8 P9 have P10 : "Plane_diffside (Li B A) C E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B D) F" by (simp add:Line_on_trans)
  have P11 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P12 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  from P2 P4 P10 P11 P12 have P13 : "Plane_diffside (Li B A) C E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Line_unique)
  from P5 P13 have P14 : "Plane_diffside (Li B A) C E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P1 have P15 : "\<not> Line_on (Li B A) D" by (simp add:Plane_sameside_def)
  from P14 P15 have P16 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> \<not> Plane_diffside (Li B A) C E" by blast
  from assms P1 have "Plane_diffside (Li B C) A E \<Longrightarrow> Plane_diffside (Li B C) D E" by (blast intro:Plane_trans)
  then have "Plane_diffside (Li B C) A E \<Longrightarrow> \<exists>p. Bet_Point (Se D E) p \<and> Line_on (Li B C) p 
    \<and> \<not> Line_on (Li B C) D \<and> \<not> Line_on (Li B C) E" by (simp add:Plane_diffside_def)
  then obtain G :: Point where P17 : "Plane_diffside (Li B C) A E \<Longrightarrow> Bet_Point (Se D E) G \<and> Line_on (Li B C) G" by blast
  then have "Plane_diffside (Li B C) A E \<Longrightarrow> Bet_Point (Se E D) G" by (simp add:Bet_rev)
  then have P18 : "Plane_diffside (Li B C) A E \<Longrightarrow> Eq (Geos (Poi G) add Emp) (Geos (Poi B) add Emp)
    \<Longrightarrow> Bet_Point (Se E D) B" by (simp add:Point_Eq)
  from assms P18 have P19 : "Plane_diffside (Li B C) A E \<Longrightarrow> \<not> Eq (Geos (Poi G) add Emp) (Geos (Poi B) add Emp)" by blast
  from P17 have P20 : "Plane_diffside (Li B C) A E \<Longrightarrow> Line_on (Li E D) G" by (simp add:Line_Bet_on)
  from P8 P20 have P21 : "Plane_diffside (Li B C) A E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B D) G" by (simp add:Line_on_trans)
  have P22 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  from P12 P17 P19 P21 P22 have P23 : "Plane_diffside (Li B C) A E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) 
    \<Longrightarrow> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (blast intro:Line_unique)
  from P5 P23 have P24 : "Plane_diffside (Li B C) A E \<Longrightarrow> 
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_on_trans)
  from P1 have P25 : "\<not> Line_on (Li B C) D" by (simp add:Plane_sameside_def)
  from P24 P25 have P26 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> \<not> Plane_diffside (Li B C) A E" by blast
  from P1 have P27 : "\<not> Line_on (Li B A) C" by (simp add:Plane_sameside_def)
  from P8 P12 have P28 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li E D) B" by (blast intro:Line_on_trans Eq_rev)
  from assms P6 P11 P28 have P29 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B A) E \<Longrightarrow> 
    Eq (Geos (Lin (Li E D)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  from P7 P29 have P30 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Line_on (Li B A) E \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P15 P30 have P31 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    \<not> Line_on (Li B A) E" by blast
  from P1 have P32 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Ang_def)
  have P33 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P12 P22 P32 P33 have P34 : "Line_on (Li B D) C \<Longrightarrow>
    Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P5 P34 have P35 : "Line_on (Li B D) C \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_on_trans)
  from P25 P35 have P36 : "\<not> Line_on (Li B D) C" by blast
  from assms have P37 : "Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li B D) C" by (simp add:Point_Eq)
  from P36 P37 have P38 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  from P16 P27 P31 P38 have P39 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Plane_sameside (Li B A) C E" by (simp add:Plane_not_diffside_sameside)
  from P1 have P40 : "\<not> Line_on (Li B C) A" by (simp add:Plane_sameside_def)
  from assms P6 P22 P28 have P41 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B C) E \<Longrightarrow> 
    Eq (Geos (Lin (Li E D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P7 P41 have P42 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Line_on (Li B C) E \<Longrightarrow> Line_on (Li B C) D" by (simp add:Line_on_trans)
  from P25 P42 have P43 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> \<not> Line_on (Li B C) E" by blast
  from P39 have P44 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> \<not> Line_on (Li B A) E" by (simp add:Plane_sameside_def)
  have "Line_on (Li B A) A" by (simp add:Line_on_rule)
  then have P45 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B A) E" by (simp add:Point_Eq)
  from P44 P45 have P46 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by blast
  from P26 P40 P43 P46 have P47 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Plane_sameside (Li B C) A E" by (simp add:Plane_not_diffside_sameside)
  from P1 P39 P47 have P48 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Ang_inside (An A B C) E" by (simp add:Ang_inside_def)
  from assms have P49 : "Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Ang_inside (An A B C) E" by (simp add:Point_Eq)
  from P48 P49 show "Ang_inside (An A B C) E" by blast
qed

lemma (in Congruence_Rule) Ang_outside_Planeside : 
  assumes
    "Def (Ang (An A B C))"
    "\<not> Ang_inside (An A B C) D"
  shows "\<not> (Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D)"
  and "\<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D
      \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D
      \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D"
proof -
  from assms have P1 : "Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<Longrightarrow> Ang_inside (An A B C) D" by (simp add:Ang_inside_def)
  from assms P1 show "\<not> (Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D)" by blast
  thus "\<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D
      \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D
      \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D" by blast
qed

lemma (in Congruence_Rule) Ang_outside_exclusive : 
  assumes 
    "Plane_sameside (Li B C) A D"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B D)) add Emp)"
  shows 
    "\<not> (\<not> Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A)"
proof -
  from assms have P1 : "\<not> Line_on (Li B C) A" by (simp add:Plane_sameside_def)
  from assms P1 have "Def (Ang (An B C A))" by (simp add:Ang_sinple_def)
  then have P2 : "Def (Ang (An A B C))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P3 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> \<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D
      \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D
      \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D" by (simp add:Ang_outside_Planeside)
  from assms have P4 : "\<not> Line_on (Li B C) D" by (simp add:Plane_sameside_def)
  from assms P4 have "Def (Ang (An B C D))" by (simp add:Ang_sinple_def)
  then have P5 : "Def (Ang (An D B C))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P6 : "\<not> Ang_inside (An D B C) A \<Longrightarrow> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
      \<or> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
      \<or> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A" by (simp add:Ang_outside_Planeside)
  from P3 P6 have P7 : "\<not> Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A \<Longrightarrow> 
    \<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
    \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A" by blast
  from assms have P8 : "Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
    \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> \<not> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A \<Longrightarrow> False" by blast
  from assms have "Plane_sameside (Li B C) D A" by (simp add:Plane_sameside_rev)
  then have P9 : "\<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<and> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A
    \<or> \<not> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> \<not> Plane_sameside (Li B C) D A \<Longrightarrow> False" by blast
  have P10 : "Line_on (Li C B) C" by (simp add:Line_on_rule)
  have P11 : "Line_on (Li C B) B" by (simp add:Line_on_rule)
  from assms P10 P11 have "\<exists>p. Bet_Point (Se C p) B \<and> Line_on (Li C B) p" by (blast intro:Bet_extension Eq_rev)
  then obtain E :: Point where P12 : "Bet_Point (Se C E) B \<and> Line_on (Li C B) E" by blast
  then have P13 : "Line_on (Li E C) B" by (simp add:Line_Bet_on)
  have P14 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P15 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  have P16 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P17 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P16 have P18 : "Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Point_Eq)
  from P1 P18 have P19 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by blast
  from P13 P14 P15 P19 have P20 : "Line_on (Li E C) A \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li E C)) add Emp)" by (simp add:Line_unique)
  have P21 : "Line_on (Li E C) C" by (simp add:Line_on_rule)
  from assms P13 P16 P17 P21 have P22 : "Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P20 P22 have P23 : "Line_on (Li E C) A \<Longrightarrow> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (blast intro:Eq_trans)
  from P15 P23 have P24 : "Line_on (Li E C) A \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from P1 P24 have P25 : "\<not> Line_on (Li E C) A" by blast
  have P26 : "Line_on (Li E C) E" by (simp add:Line_on_rule)
  from P21 have P27 : "Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li E C) A" by (simp add:Point_Eq)
  from P25 P27 have P28 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by blast
  from P12 have P29 : "Bet_Point (Se C E) B" by simp
  then have P30 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def Eq_rev)
  have "Plane_diffside (Li B D) C A \<Longrightarrow> \<exists>p. Bet_Point (Se C A) p \<and> Line_on (Li B D) p \<and> \<not> Line_on (Li B D) C \<and> \<not> Line_on (Li B D) A" by (simp add:Plane_diffside_def)
  then have P31 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Line_on (Li B D) C \<and> \<not> Line_on (Li B D) A" by blast
  have P32 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  from P29 have P33 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  from P13 P26 P32 P33 have P34 : "Line_on (Li B D) E \<Longrightarrow> Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from P21 P34 have P35 : "Line_on (Li B D) E \<Longrightarrow> Line_on (Li B D) C" by (simp add:Line_on_trans)
  from P31 P35 have P36 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Line_on (Li B D) E" by blast
  from P29 have P37 : "Bet_Point (Se E C) B" by (simp add:Bet_rev)
  from P25 P31 P32 P36 P37 have P38 : "Plane_diffside (Li B D) C A \<Longrightarrow>
    Line_on_Seg (Li B D) (Se E A) \<and> \<not> Line_on_Seg (Li B D) (Se C A) 
    \<or> Line_on_Seg (Li B D) (Se C A) \<and> \<not> Line_on_Seg (Li B D) (Se E A)" by (simp add:Pachets_axiom)
  have P39 : "Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> \<exists>p. Line_on (Li B D) p \<and> Bet_Point (Se E A) p" by (simp add:Line_on_Seg_rule)
  from P31 P36 P39 have "Plane_diffside (Li B D) C A \<and> Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> 
    \<exists>p. Bet_Point (Se E A) p \<and> Line_on (Li B D) p \<and> \<not> Line_on (Li B D) E \<and> \<not> Line_on (Li B D) A" by blast
  then have P40 : "Plane_diffside (Li B D) C A \<and> Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_diffside (Li B D) E A" by (simp add:Plane_diffside_def)
  from P26 have P41 : "Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B D)) add Emp) \<Longrightarrow> Line_on (Li B D) E" by (simp add:Line_on_trans)
  from P36 P41 have P42 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B D)) add Emp)" by blast
  from P32 P37 P42 have P43 : "Plane_diffside (Li B D) C A \<Longrightarrow> Plane_diffside (Li B D) E C" by (simp add:Plane_Bet_diffside)
  from P28 have P44 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P30 P40 P43 P44 have "Plane_diffside (Li B D) C A \<and> Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_sameside (Li B D) A C" by (blast intro:Plane_trans_inv)
  then have P45 : "Plane_diffside (Li B D) C A \<and> Line_on_Seg (Li B D) (Se E A) \<Longrightarrow> Plane_sameside (Li B D) C A" by (blast intro:Plane_sameside_rev)
  have P46 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Plane_sameside (Li B D) C A" by (simp add:Plane_diffside_not_sameside)
  from P45 P46 have P47 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Line_on_Seg (Li B D) (Se E A)" by blast
  from P38 P47 have "Plane_diffside (Li B D) C A \<Longrightarrow> Line_on_Seg (Li B D) (Se C A)" by blast
  then have "Plane_diffside (Li B D) C A \<Longrightarrow> \<exists>p. Line_on (Li B D) p \<and> Bet_Point (Se C A) p" by (simp add:Line_on_Seg_rule)
  then obtain F :: Point where P48 : "Plane_diffside (Li B D) C A \<Longrightarrow> Line_on (Li B D) F \<and> Bet_Point (Se C A) F" by blast
  from P15 have P49 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from P1 P49 have P50 : "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by blast
  from P48 have P51 : "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se A C) F" by (simp add:Bet_rev)
  from assms P19 P50 P51 have P52 : "Plane_diffside (Li B D) C A \<Longrightarrow> Ang_inside (An A B C) F" by (simp add:Ang_inside_Bet_Point)
  then have "Plane_diffside (Li B D) C A \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Ang_inside (An A B C) D" by (simp add:Point_Eq)
  then have P53 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp)" by (blast intro:Eq_rev)
  from P48 have "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se C A) F" by simp
  then have "Plane_diffside (Li B D) C A \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> Bet_Point (Se C A) B" by (simp add:Point_Eq)
  then have P54 : "Plane_diffside (Li B D) C A \<Longrightarrow> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_Bet_on)
  from P1 P54 have P55 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp)" by blast
  have P56 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  from P16 have P57 : "Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li B C) D" by (simp add:Point_Eq)
  from P4 P57 have P58 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by blast
  from P32 P48 P53 P55 P56 P58 have "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow>
    Bet_Point (Se B F) D \<or> Bet_Point (Se F D) B \<or> Bet_Point (Se D B) F" by (simp add:Bet_case)
  then have P59 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow>
    Bet_Point (Se B F) D \<and> \<not> Bet_Point (Se F D) B \<and> \<not> Bet_Point (Se D B) F
    \<or> \<not> Bet_Point (Se B F) D \<and> Bet_Point (Se F D) B \<and> \<not> Bet_Point (Se D B) F
    \<or> \<not> Bet_Point (Se B F) D \<and> \<not> Bet_Point (Se F D) B \<and> Bet_Point (Se D B) F" by (simp add:Bet_case_fact)
  from P26 have P60 : "Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B D)) add Emp) \<Longrightarrow> Line_on (Li B D) E" by (simp add:Line_on_trans)
  from P36 P60 have P61 : "Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li E C)) add Emp)" by (blast intro:Eq_rev)
  have P62 : "Bet_Point (Se F D) B \<Longrightarrow> Line_on (Li F D) B" by (simp add:Line_Bet_on)
  have P63 : "Line_on (Li F D) D" by (simp add:Line_on_rule)
  from P32 P56 P58 P62 P63 have P64 : "Bet_Point (Se F D) B \<Longrightarrow> Eq (Geos (Lin (Li F D)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from P61 P64 have P65 : "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se F D) B \<Longrightarrow> 
    \<not> Eq (Geos (Lin (Li F D)) add Emp) (Geos (Lin (Li E C)) add Emp)" by (blast intro:Eq_trans)
  from P13 P65 have P66 : "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se F D) B \<Longrightarrow> Plane_diffside (Li E C) F D" by (simp add:Plane_Bet_diffside)
  have "Line_on (Li C A) A" by (simp add:Line_on_rule)
  then have P67 : "Eq (Geos (Lin (Li C A)) add Emp) (Geos (Lin (Li E C)) add Emp) \<Longrightarrow> Line_on (Li E C) A" by (simp add:Line_on_trans)
  from P25 P67 have P68 : "\<not> Eq (Geos (Lin (Li C A)) add Emp) (Geos (Lin (Li E C)) add Emp)" by blast
  from P48 have P69 : "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se C A) F" by simp
  from P21 P68 P69 have P71 : "Plane_diffside (Li B D) C A \<Longrightarrow> Plane_sameside (Li E C) F A" by (simp add:Plane_Bet_sameside)
  from P66 P71 have P72 : "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se F D) B \<Longrightarrow> 
    Plane_diffside (Li E C) A D" by (simp add:Plane_trans)
  from P22 P72 have "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se F D) B \<Longrightarrow> 
    Plane_diffside (Li B C) A D" by (simp add:Plane_Line_diff_trans)
  then have "Plane_diffside (Li B D) C A \<Longrightarrow> Bet_Point (Se F D) B \<Longrightarrow> 
    \<not> Plane_sameside (Li B C) A D" by (simp add:Plane_diffside_not_sameside)
  then have P73 : "Plane_sameside (Li B C) A D \<and> Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Bet_Point (Se F D) B" by blast
  have P74 : "Bet_Point (Se B F) D \<Longrightarrow> Line_on (Li B F) D" by (simp add:Line_Bet_on)
  from P59 have P75 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> 
    Bet_Point (Se B F) D \<Longrightarrow> \<not> Bet_Point (Se D F) B" by (blast intro:Bet_rev)
  from P52 P58 P74 P75 have "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> 
    Bet_Point (Se B F) D \<Longrightarrow> Ang_inside (An A B C) D" by (simp add:Ang_inside_HalfLine)
  then have P76 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Bet_Point (Se B F) D" by blast
  have P77 : "Bet_Point (Se D B) F \<Longrightarrow> Line_on (Li B F) D" by (simp add:Line_Bet_on)
  from P59 have P78 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> 
    Bet_Point (Se D B) F \<Longrightarrow> \<not> Bet_Point (Se D F) B" by (blast intro:Bet_rev)
  from P52 P58 P77 P78 have "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> 
    Bet_Point (Se D B) F \<Longrightarrow> Ang_inside (An A B C) D" by (simp add:Ang_inside_HalfLine)
  then have P79 : "\<not> Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) C A \<Longrightarrow> \<not> Bet_Point (Se D B) F" by blast
  from P59 P73 P76 P79 have "\<not> Ang_inside (An A B C) D \<and> Plane_sameside (Li B C) A D \<and> Plane_diffside (Li B D) C A \<Longrightarrow> False" by blast
  then have P80 : "\<not> Ang_inside (An A B C) D \<and> \<not> Plane_sameside (Li B A) C D 
    \<and> Plane_sameside (Li B C) A D \<and> Plane_diffside (Li B D) C A \<and> Plane_sameside (Li B C) D A \<Longrightarrow> False" by simp
  from P5 have "Def (Tri (Tr B D C))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P81 : "\<not> Line_on (Li B D) C" by (simp add:Tri_def_Line)
  from P14 P15 P19 P32 have P82 : "Line_on (Li B D) A \<Longrightarrow> 
    Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from assms P82 have P83 : "\<not> Line_on (Li B D) A" by blast
  from P28 P81 P83 have P84 : "\<not> Plane_sameside (Li B D) C A \<Longrightarrow> Plane_diffside (Li B D) C A" by (simp add:Plane_not_sameside_diffside)
  from P80 P84 have P85 : "\<not> Ang_inside (An A B C) D \<and> \<not> Plane_sameside (Li B A) C D 
    \<and> Plane_sameside (Li B C) A D \<and> \<not> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A \<Longrightarrow> False" by simp
  from P7 P8 P9 P85 show "\<not> (\<not> Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A)" by blast
qed

lemma (in Congruence_Rule) Ang_inside_case : 
  assumes 
    "Def (Ang (An A B C))"
    "Def (Ang (An D B C))"
    "Plane_sameside (Li B C) A D"
    "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B D)) add Emp)"
  shows 
    "Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A
    \<or> \<not> Ang_inside (An A B C) D \<and> Ang_inside (An D B C) A"
proof -
  have P1 : "Ang_inside (An A B C) D \<Longrightarrow> Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D" by (simp add:Ang_inside_def)
  have P2 : "Ang_inside (An D B C) A \<Longrightarrow> Plane_sameside (Li B D) C A \<and> Plane_sameside (Li B C) D A" by (simp add:Ang_inside_def)
  have P3 : "Ang_inside (An A B C) D \<Longrightarrow> Plane_diffside (Li B D) A C" by (simp add:Ang_inside_Planeside)
  have "Plane_diffside (Li B D) A C \<Longrightarrow> Plane_diffside (Li B D) C A" by (simp add:Plane_diffside_rev)
  then have P4 : "Plane_diffside (Li B D) A C \<Longrightarrow> \<not> Plane_sameside (Li B D) C A" by (simp add:Plane_diffside_not_sameside)
  from P3 P4 have P5 : "Ang_inside (An A B C) D \<Longrightarrow> \<not> Plane_sameside (Li B D) C A" by (simp add:Plane_diffside_rev)
  from P2 P5 have P6 : "Ang_inside (An A B C) D \<and> Ang_inside (An D B C) A \<Longrightarrow> False" by simp
  from assms have P7 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Ang_def)
  from assms P7 have P8 : "\<not> Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A \<Longrightarrow> False" by (simp add:Ang_outside_exclusive)
  from P6 P8 show "Ang_inside (An A B C) D \<and> \<not> Ang_inside (An D B C) A
    \<or> \<not> Ang_inside (An A B C) D \<and> Ang_inside (An D B C) A" by blast
qed

lemma (in Congruence_Rule) Plane_sameside_HalfLine : 
  assumes 
    "Plane_sameside l1 p1 p2"
    "Line_on l1 p3"
    "Line_on (Li p3 p1) p4"
    "\<not> Bet_Point (Se p4 p1) p3"
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)"
    "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p4) add Emp)"
  shows "Plane_sameside l1 p1 p4"
proof -
  from assms have P1 : "\<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2 
    \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Plane_sameside_def)
  have "Plane_diffside l1 p1 p4 \<Longrightarrow> 
    \<exists>p. Bet_Point (Se p1 p4) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p4" by (simp add:Plane_diffside_def)
  then obtain p5 :: Point where P2 : "Plane_diffside l1 p1 p4 \<Longrightarrow> 
    Bet_Point (Se p1 p4) p5 \<and> Line_on l1 p5 \<and> \<not> Line_on l1 p4" by blast
  from assms have P3 : "Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp) \<Longrightarrow> Line_on l1 p1" by (simp add:Point_Eq)
  from P1 P3 have P4 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)" by blast
  then have P5 : "Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (simp add:Line_rev)
  from assms P5 have P6 : "Line_on (Li p1 p3) p4" by (simp add:Line_rev Line_on_trans)
  from P4 have P7 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from assms P6 P7 have P8 : "Line_on (Li p1 p4) p3" by (simp add:Line_on_rev)
  from P2 have P9 : "Plane_diffside l1 p1 p4 \<Longrightarrow> Line_on (Li p1 p4) p5" by (simp add:Line_Bet_on)
  from assms P2 P8 P9 have P10 : "Plane_diffside l1 p1 p4 \<Longrightarrow> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  have P11 : "Line_on (Li p1 p4) p1" by (simp add:Line_on_rule)
  from P10 P11 have P12 : "Plane_diffside l1 p1 p4 \<Longrightarrow> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow>
    Line_on l1 p1" by (simp add:Line_on_trans)
  from P1 P12 have P13 : "Plane_diffside l1 p1 p4 \<Longrightarrow> Eq (Geos (Poi p5) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from P2 have P14 : "Plane_diffside l1 p1 p4 \<Longrightarrow> Bet_Point (Se p1 p4) p5" by simp
  from P13 P14 have "Plane_diffside l1 p1 p4 \<Longrightarrow> Bet_Point (Se p1 p4) p3" by (simp add:Point_Eq)
  then have P15 : "Plane_diffside l1 p1 p4 \<Longrightarrow> Bet_Point (Se p4 p1) p3" by (simp add:Bet_rev)
  from assms P15 have P16 : "\<not> Plane_diffside l1 p1 p4" by blast
  have P17 : "Line_on (Li p3 p1) p3" by (simp add:Line_on_rule)
  from assms P17 have P18 : "Line_on l1 p4 \<Longrightarrow> 
    Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  have P19 : "Line_on (Li p3 p1) p1" by (simp add:Line_on_rule)
  from P18 P19 have P20 : "Line_on l1 p4 \<Longrightarrow> Line_on l1 p1" by (simp add:Line_on_trans)
  from P1 P20 have P21 : "\<not> Line_on l1 p4" by blast
  from assms P1 P16 P21 show "Plane_sameside l1 p1 p4" by (simp add:Plane_not_diffside_sameside)
qed

lemma (in Congruence_Rule) Plane_Bet_sameside_rev : 
  assumes 
    "Plane_sameside l1 p1 p3"
    "Line_on l1 p2"
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)"
    "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)"
    "Line_on l2 p1" "Line_on l2 p2" "Line_on l2 p3"
    "\<not> Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
  shows "Bet_Point (Se p3 p2) p1 \<or> Bet_Point (Se p2 p1) p3"
proof -
  from assms have P1 : "Bet_Point (Se p1 p3) p2 \<or> Bet_Point (Se p3 p2) p1 \<or> Bet_Point (Se p2 p1) p3" by (simp add:Bet_case)
  have P2 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  from assms P2 P3 have P4 : " Eq (Geos (Lin l2) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (simp add:Line_unique)
  from assms P4 have "\<not> Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (blast intro:Eq_trans)
  then have P6 : "\<not> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)" by (blast intro:Eq_rev)
  from assms P6 have "Bet_Point (Se p1 p3) p2 \<Longrightarrow> Plane_diffside l1 p1 p3" by (simp add:Plane_Bet_diffside)
  then have P7 : "Bet_Point (Se p1 p3) p2 \<Longrightarrow> \<not> Plane_sameside l1 p1 p3" by (simp add:Plane_diffside_not_sameside)
  from assms P7 have P8 : "\<not> Bet_Point (Se p1 p3) p2" by blast
  from P1 P8 show "Bet_Point (Se p3 p2) p1 \<or> Bet_Point (Se p2 p1) p3" by blast
qed

lemma (in Congruence_Rule) Seg_Bet_relation : 
  assumes N : 
    "Bet_Point (Se p1 p2) p3"
  shows "\<not> Eq (Geos (Seg (Se p1 p2)) add Emp) (Geos (Seg (Se p1 p3)) add Emp)"
proof
  assume W : "Eq (Geos (Seg (Se p1 p2)) add Emp) (Geos (Seg (Se p1 p3)) add Emp)"
  from N have "Inv (Bet_Point (Se p2 p3) p1) \<and> Inv (Bet_Point (Se p3 p1) p2)" by (simp add:Bet_iff)
  then have P1 : "\<not> Bet_Point (Se p2 p3) p1" by (simp add:Inv_def)
  have P2 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from N have P4 : "Line_on (Li p1 p2) p3" by (simp add:Line_Bet_on)
  from N have P5 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  from N have "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  then have P6 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from W P1 P2 P3 P4 P5 P6 have P7 : "Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Seg_move_unique)
  from N have P8 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P7 P8 show False by blast
qed

lemma (in Congruence_Rule) Seg_Bet_move_lemma1 : 
  assumes
    "Bet_Point (Se p11 p13) p12"
    "Line_on l1 p21" "Line_on l1 p22" "Line_on l1 p23"
    "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p22) add Emp)"
    "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p23) add Emp)"
    "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)"
    "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)"
    "\<not> Bet_Point (Se p22 p23) p21"
  shows "Bet_Point (Se p21 p23) p22"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p21) add Emp)" by (blast intro:Eq_rev)
  from assms have "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p11) add Emp)" by (simp add:Bet_Point_def)
  then have P2 : "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p12) add Emp)" by (blast intro:Eq_rev)
  from assms P1 P2 have "\<exists>p. Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p22 p)) add Emp)
    \<and> \<not> Bet_Point (Se p p21) p22 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain p211 :: Point where P3 : "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p22 p211)) add Emp) 
    \<and> \<not> Bet_Point (Se p211 p21) p22 \<and> Line_on l1 p211 \<and> \<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p211) add Emp)" by blast
  from assms have "\<not> Eq (Geos (Poi p13) add Emp) (Geos (Poi p12) add Emp)" by (simp add:Bet_Point_def)
  then have P4 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (blast intro:Eq_rev)
  from assms P3 P4 have "\<exists>p. Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p)) add Emp) 
    \<and> Bet_Point (Se p p211) p22 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_diffside)
  then obtain p231 :: Point where P5 : "Eq (Geos (Seg (Se p12 p13)) add Emp) (Geos (Seg (Se p22 p231)) add Emp) 
    \<and> Bet_Point (Se p231 p211) p22 \<and> Line_on l1 p231 \<and> \<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p231) add Emp)" by blast
  have P6 : "Eq (Geos (Seg (Se p21 p22)) add Emp) (Geos (Seg (Se p22 p21)) add Emp)" by (simp add:Seg_rev)
  from assms have P7 : "Eq (Geos (Seg (Se p21 p22)) add Emp) (Geos (Seg (Se p11 p12)) add Emp)" by (simp add:Eq_rev)
  from P3 P7 have P8 : "Eq (Geos (Seg (Se p22 p211)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P6 P8 have P9 : "Eq (Geos (Seg (Se p22 p211)) add Emp) (Geos (Seg (Se p22 p21)) add Emp)" by (blast intro:Eq_trans)
  from assms P1 P3 P9 have P10 : "Eq (Geos (Poi p211) add Emp) (Geos (Poi p21) add Emp)" by (blast intro:Seg_move_unique)
  from P5 have P11 : "Bet_Point (Se p211 p231) p22" by (simp add:Bet_rev)
  from P10 P11 have P12 : "Bet_Point (Se p21 p231) p22" by (simp add:Bet_Point_Eq)
  have P13 : "Line_on (Li p11 p12) p11" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li p11 p12) p12" by (simp add:Line_on_rule)
  from assms have P15 : "Line_on (Li p11 p12) p13" by (simp add:Line_Bet_on)
  from assms have P16 : "\<not> Seg_on_Seg (Se p11 p12) (Se p12 p13)" by (simp add:Seg_Bet_not_on)
  from P12 have P17 : "\<not> Seg_on_Seg (Se p21 p22) (Se p22 p231)" by (simp add:Seg_Bet_not_on) 
  from assms P5 P13 P14 P15 P16 P17 have P18 : "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p231)) add Emp)" by (simp add:Seg_add)
  from assms P18 have P19 : "Eq (Geos (Seg (Se p21 p231)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P12 have P20 : "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p231) add Emp)" by (simp add:Bet_Point_def)
  from P12 have P21 : "Bet_Point (Se p231 p21) p22" by (simp add:Bet_rev)
  from P21 have P22 : "Bet_Point (Se p231 p23) p21 \<Longrightarrow> Bet_Point (Se p22 p23) p21" by (blast intro:Bet_swap_134_234)
  from assms P22 have P23 : "\<not> Bet_Point (Se p231 p23) p21" by blast
  from assms P5 P19 P20 P23 have P24 : "Eq (Geos (Poi p231) add Emp) (Geos (Poi p23) add Emp)" by (blast intro:Seg_move_unique)
  from P21 P24 have "Bet_Point (Se p23 p21) p22" by (simp add:Bet_Point_Eq)
  thus "Bet_Point (Se p21 p23) p22" by (simp add:Bet_rev)
qed

lemma (in Congruence_Rule) Seg_Bet_move_sameside : 
  assumes
    "Bet_Point (Se p11 p13) p12"
    "Line_on l1 p21" "Line_on l1 p4"
    "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p4) add Emp)"
  shows "\<exists>p q. Bet_Point (Se p21 q) p \<and> Line_on l1 p \<and> Line_on l1 q
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 q)) add Emp)
    \<and> \<not> Bet_Point (Se p p4) p21 \<and> \<not> Bet_Point (Se q p4) p21"
proof -
  from assms have "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p11) add Emp)" by (simp add:Bet_Point_def)
  then have P1 : "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p12) add Emp)" by (blast intro:Eq_rev)
  from assms P1 have "\<exists>p. Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p p4) p21 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain p22 :: Point where P2 : "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp) 
    \<and> \<not> Bet_Point (Se p22 p4) p21 \<and> Line_on l1 p22 \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p22) add Emp)" by blast
  from assms have P3 : "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Bet_Point_def)
  from assms P2 P3 have "\<exists>p. Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p p22) p21 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain p23 :: Point where P4 : "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)
    \<and> \<not> Bet_Point (Se p23 p22) p21 \<and> Line_on l1 p23 \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p23) add Emp)" by blast
  from P4 have "\<not> Bet_Point (Se p23 p22) p21" by simp
  then have P5 : "\<not> Bet_Point (Se p22 p23) p21" by (blast intro:Bet_rev)
  from assms P2 P4 P5 have P6 : "Bet_Point (Se p21 p23) p22" by (blast intro:Seg_Bet_move_lemma1)
  then have P7 : "Bet_Point (Se p23 p21) p22" by (simp add:Bet_rev)
  from P7 have P8 : "Bet_Point (Se p23 p4) p21 \<Longrightarrow> Bet_Point (Se p22 p4) p21" by (blast intro:Bet_swap_134_234)
  from P2 P8 have P9 : "\<not> Bet_Point (Se p23 p4) p21" by blast
  from P2 P4 P6 P9 show "\<exists>p q. Bet_Point (Se p21 q) p \<and> Line_on l1 p \<and> Line_on l1 q
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 q)) add Emp)
    \<and> \<not> Bet_Point (Se p p4) p21 \<and> \<not> Bet_Point (Se q p4) p21" by blast
qed

lemma (in Congruence_Rule) Seg_Bet_move_diffside : 
  assumes
    "Bet_Point (Se p11 p13) p12"
    "Line_on l1 p21" "Line_on l1 p4"
    "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p4) add Emp)"
  shows "\<exists>p q. Bet_Point (Se p21 q) p \<and> Line_on l1 p \<and> Line_on l1 q
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 q)) add Emp)
    \<and> Bet_Point (Se p p4) p21 \<and> Bet_Point (Se q p4) p21"
proof -
  from assms have "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p11) add Emp)" by (simp add:Bet_Point_def)
  then have P1 : "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p12) add Emp)" by (blast intro:Eq_rev)
  from assms P1 have "\<exists>p. Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp) 
    \<and> Bet_Point (Se p p4) p21 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_diffside)
  then obtain p22 :: Point where P2 : "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp) 
    \<and> Bet_Point (Se p22 p4) p21 \<and> Line_on l1 p22 \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p22) add Emp)" by blast
  from assms have P3 : "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Bet_Point_def)
  from assms P2 P3 have "\<exists>p. Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> \<not> Bet_Point (Se p p22) p21 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain p23 :: Point where P4 : "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp) 
    \<and> \<not> Bet_Point (Se p23 p22) p21 \<and> Line_on l1 p23 \<and> \<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p23) add Emp)" by blast
  from P4 have "\<not> Bet_Point (Se p23 p22) p21" by simp
  then have P5 : "\<not> Bet_Point (Se p22 p23) p21" by (blast intro:Bet_rev)
  from assms P2 P4 P5 have P6 : "Bet_Point (Se p21 p23) p22" by (blast intro:Seg_Bet_move_lemma1)
  then have P7 : "Bet_Point (Se p23 p21) p22" by (simp add:Bet_rev)
  from P2 P7 have P8 : "Bet_Point (Se p23 p4) p21" by (blast intro:Bet_swap_234_134)
  from P2 P4 P6 P8 show "\<exists>p q. Bet_Point (Se p21 q) p \<and> Line_on l1 p \<and> Line_on l1 q
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 q)) add Emp)
    \<and> Bet_Point (Se p p4) p21 \<and> Bet_Point (Se q p4) p21" by blast
qed

lemma (in Congruence_Rule) Seg_Bet_wrong_relation : 
  assumes
    "Bet_Point (Se p11 p13) p12"
    "Bet_Point (Se p21 p22) p23"
    "Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)"
    "Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)"
  shows False
proof -
  have P1 : "Line_on (Li p21 p22) p21" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p21 p22) p22" by (simp add:Line_on_rule)
  from assms have P3 : "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p22) add Emp)" by (simp add:Bet_Point_def)
  from assms P1 P2 P3 have "\<exists>p q. Bet_Point (Se p21 q) p \<and> Line_on (Li p21 p22) p \<and> Line_on (Li p21 p22) q
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 p)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 q)) add Emp)
    \<and> \<not> Bet_Point (Se p p22) p21 \<and> \<not> Bet_Point (Se q p22) p21" by (simp add:Seg_Bet_move_sameside)
  then obtain pn2 pn3 :: Point where P4 : "Bet_Point (Se p21 pn3) pn2 \<and> Line_on (Li p21 p22) pn2 \<and> Line_on (Li p21 p22) pn3
    \<and> Eq (Geos (Seg (Se p11 p12)) add Emp) (Geos (Seg (Se p21 pn2)) add Emp)
    \<and> Eq (Geos (Seg (Se p11 p13)) add Emp) (Geos (Seg (Se p21 pn3)) add Emp)
    \<and> \<not> Bet_Point (Se pn2 p22) p21 \<and> \<not> Bet_Point (Se pn3 p22) p21" by blast
  then have P5 : "Bet_Point (Se p21 pn3) pn2" by simp
  then have "\<not> Eq (Geos (Poi pn2) add Emp) (Geos (Poi p21) add Emp)" by (simp add:Bet_Point_def)
  then have P6 : "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi pn2) add Emp)" by (blast intro:Eq_rev)
  from assms P4 have P7 : "Eq (Geos (Seg (Se p21 pn2)) add Emp) (Geos (Seg (Se p21 p22)) add Emp)" by (blast intro:Eq_trans)
  from P1 P2 P3 P4 P6 P7 have P8 : "Eq (Geos (Poi pn2) add Emp) (Geos (Poi p22) add Emp)" by (blast intro:Seg_move_unique)
  from P5 P8 have "Bet_Point (Se p21 pn3) p22" by (simp add:Point_Eq)
  then have P9 : "Bet_Point (Se pn3 p21) p22" by (simp add:Bet_rev)
  from assms have P10 : "Line_on (Li p21 p22) p23" by (simp add:Line_Bet_on)
  from assms have "\<not> Eq (Geos (Poi p23) add Emp) (Geos (Poi p21) add Emp)" by (simp add:Bet_Point_def)  
  then have P11 : "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi p23) add Emp)" by (blast intro:Eq_rev)
  from P5 have P12 : "\<not> Eq (Geos (Poi p21) add Emp) (Geos (Poi pn3) add Emp)" by (simp add:Bet_Point_def)
  from assms P4 have P13 : "Eq (Geos (Seg (Se p21 pn3)) add Emp) (Geos (Seg (Se p21 p23)) add Emp)" by (blast intro:Eq_trans)
  from assms have P14 : "Bet_Point (Se p22 p21) p23" by (simp add:Bet_rev)
  have P15 : "Bet_Point (Se pn3 p23) p21 \<Longrightarrow> Bet_Point (Se p23 pn3) p21" by (simp add:Bet_rev)
  from P14 P15 have "Bet_Point (Se pn3 p23) p21 \<Longrightarrow> Bet_Point (Se p22 pn3) p21" by (blast intro:Bet_swap_234_134)
  then have P16 : "Bet_Point (Se pn3 p23) p21 \<Longrightarrow> Bet_Point (Se pn3 p22) p21" by (simp add:Bet_rev)
  from P4 P16 have P17 : "\<not> Bet_Point (Se pn3 p23) p21" by blast
  from P1 P4 P10 P11 P12 P13 P17 have P18 : "Eq (Geos (Poi pn3) add Emp) (Geos (Poi p23) add Emp)" by (blast intro:Seg_move_unique)
  from P9 P18 have P19 : "Bet_Point (Se p23 p21) p22" by (simp add:Bet_Point_Eq)
  from assms have "Inv (Bet_Point (Se p22 p23) p21) \<and> Inv (Bet_Point (Se p23 p21) p22)" by (simp add:Bet_iff)
  then have P20 : "\<not> Bet_Point (Se p23 p21) p22" by (simp add:Inv_def)
  from P19 P20 show False by blast 
qed

lemma (in Congruence_Rule) Ang_inside_trans : 
  assumes 
    "Ang_inside (An A B C) D" "Def (Ang (An A B C))"
    "Line_on (Li B A1) A" "\<not> Bet_Point (Se A A1) B"
    "Line_on (Li B C1) C" "\<not> Bet_Point (Se C C1) B"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A1) add Emp)"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C1) add Emp)"
  shows "Ang_inside (An A1 B C1) D"
proof - 
  from assms have P1 : "Plane_sameside (Li B A) C D \<and> Plane_sameside (Li B C) A D" by (simp add:Ang_inside_def)
  have P2 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li B A1) B" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  from assms have P5 : "Def (Tri (Tr A B C))" by (simp add:Ang_to_Tri)
  from P5 have P6 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from assms P2 P3 P4 P6 have P7 : "Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B A1)) add Emp)" by (simp add:Line_unique)
  have P8 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li B C1) B" by (simp add:Line_on_rule)
  have P10 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P5 have P11 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Tri_def)
  from assms P8 P9 P10 P11 have P12 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B C1)) add Emp)" by (simp add:Line_unique)
  have P13 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> Plane_diffside (Li B A) D C1" by (simp add:Plane_diffside_rev)
  from P1 have P14 : "Plane_sameside (Li B A) D C" by (simp add:Plane_sameside_rev)
  from P13 P14 have P15 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> Plane_diffside (Li B A) C C1" by (simp add:Plane_trans)
  then have "Plane_diffside (Li B A) C1 D \<Longrightarrow> \<exists>p. Bet_Point (Se C C1) p 
    \<and> Line_on (Li B A) p \<and> \<not> Line_on (Li B A) C \<and> \<not> Line_on (Li B A) C1" by (simp add:Plane_diffside_def)
  then obtain B1 :: Point where P16 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> Bet_Point (Se C C1) B1 
    \<and> Line_on (Li B A) B1 \<and> \<not> Line_on (Li B A) C \<and> \<not> Line_on (Li B A) C1" by blast
  from P16 have P17 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> Bet_Point (Se C C1) B1" by simp
  then have P18 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> Line_on (Li C C1) B1" by (simp add:Line_Bet_on)
  have P19 : "Line_on (Li B C1) C1" by (simp add:Line_on_rule)
  have P20 : "Line_on (Li C C1) C" by (simp add:Line_on_rule)
  have P21 : "Line_on (Li C C1) C1" by (simp add:Line_on_rule)
  from assms P19 P20 P21 have P22 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B A) C1 D \<Longrightarrow> Eq (Geos (Lin (Li B C1)) add Emp) (Geos (Lin (Li C C1)) add Emp)" by (simp add:Line_unique)
  from P9 P22 have P23 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B A) C1 D \<Longrightarrow> Line_on (Li C C1) B" by (simp add:Line_on_trans)
  from P21 have P24 : "Eq (Geos (Lin (Li C C1)) add Emp) (Geos (Lin (Li B A)) add Emp) \<Longrightarrow> Line_on (Li B A) C1" by (simp add:Line_on_trans)
  from P16 P24 have P25 : "Plane_diffside (Li B A) C1 D \<Longrightarrow> 
    \<not> Eq (Geos (Lin (Li C C1)) add Emp) (Geos (Lin (Li B A)) add Emp)" by blast
  from P2 P16 P18 P23 P25 have P26 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B A) C1 D \<Longrightarrow> Eq (Geos (Poi B1) add Emp) (Geos (Poi B) add Emp)" by (simp add:Line_unique_Point)
  from P17 P26 have P27 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B A) C1 D \<Longrightarrow> Bet_Point (Se C C1) B" by (simp add:Point_Eq)
  from assms P27 have P28 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    \<not> Plane_diffside (Li B A) C1 D" by blast
  from assms P2 P9 P19 have P29 : "Line_on (Li B A) C1 \<Longrightarrow>
    Eq (Geos (Lin (Li B C1)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  from P12 P29 have P30 : "Line_on (Li B A) C1 \<Longrightarrow>
    Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_trans)
  from P10 P30 have P31 : "Line_on (Li B A) C1 \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P1 have P32 : "\<not> Line_on (Li B A) C" by (simp add:Plane_sameside_def)
  from P31 P32 have P33 : "\<not> Line_on (Li B A) C1" by blast
  from P1 have P34 : "\<not> Line_on (Li B A) D" by (simp add:Plane_sameside_def)
  from P12 P19 have "Line_on (Li B C) C1" by (blast intro:Line_on_trans Eq_rev)
  then have P35 : "Eq (Geos (Poi C1) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li B C) D" by (simp add:Point_Eq)
  from P1 have P36 : "\<not> Line_on (Li B C) D" by (simp add:Plane_sameside_def)
  from P35 P36 have P37 : "\<not> Eq (Geos (Poi C1) add Emp) (Geos (Poi D) add Emp)" by blast
  from P28 P33 P34 P37 have P38 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> 
    Plane_sameside (Li B A) C1 D" by (simp add:Plane_not_diffside_sameside)
  from P14 have "Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> Plane_sameside (Li B A) D C1" by (simp add:Point_Eq)
  then have P39 : "Eq (Geos (Poi C) add Emp) (Geos (Poi C1) add Emp) \<Longrightarrow> Plane_sameside (Li B A) C1 D" by (simp add:Plane_sameside_rev)
  from P38 P39 have P40 : "Plane_sameside (Li B A) C1 D" by blast
  from P7 P40 have P41 : "Plane_sameside (Li B A1) C1 D" by (simp add:Plane_Line_trans)
  have P42 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> Plane_diffside (Li B C) D A1" by (simp add:Plane_diffside_rev)
  from P1 have P43 : "Plane_sameside (Li B C) D A" by (simp add:Plane_sameside_rev)
  from P42 P43 have P44 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> Plane_diffside (Li B C) A A1" by (simp add:Plane_trans)
  then have "Plane_diffside (Li B C) A1 D \<Longrightarrow> \<exists>p. Bet_Point (Se A A1) p 
    \<and> Line_on (Li B C) p \<and> \<not> Line_on (Li B C) A \<and> \<not> Line_on (Li B C) A1" by (simp add:Plane_diffside_def)
  then obtain B2 :: Point where P45 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> Bet_Point (Se A A1) B2 
    \<and> Line_on (Li B C) B2 \<and> \<not> Line_on (Li B C) A \<and> \<not> Line_on (Li B C) A1" by blast
  from P45 have P46 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> Bet_Point (Se A A1) B2" by simp
  then have P47 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> Line_on (Li A A1) B2" by (simp add:Line_Bet_on)
  have P48 : "Line_on (Li B A1) A1" by (simp add:Line_on_rule)
  have P49 : "Line_on (Li A A1) A" by (simp add:Line_on_rule)
  have P50 : "Line_on (Li A A1) A1" by (simp add:Line_on_rule)
  from assms P48 P49 P50 have P51 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B C) A1 D \<Longrightarrow> Eq (Geos (Lin (Li B A1)) add Emp) (Geos (Lin (Li A A1)) add Emp)" by (simp add:Line_unique)
  from P3 P51 have P52 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B C) A1 D \<Longrightarrow> Line_on (Li A A1) B" by (simp add:Line_on_trans)
  from P50 have P53 : "Eq (Geos (Lin (Li A A1)) add Emp) (Geos (Lin (Li B C)) add Emp) \<Longrightarrow> Line_on (Li B C) A1" by (simp add:Line_on_trans)
  from P45 P53 have P54 : "Plane_diffside (Li B C) A1 D \<Longrightarrow> 
    \<not> Eq (Geos (Lin (Li A A1)) add Emp) (Geos (Lin (Li B C)) add Emp)" by blast
  from P8 P45 P47 P52 P54 have P55 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B C) A1 D \<Longrightarrow> Eq (Geos (Poi B2) add Emp) (Geos (Poi B) add Emp)" by (simp add:Line_unique_Point)
  from P46 P55 have P56 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    Plane_diffside (Li B C) A1 D \<Longrightarrow> Bet_Point (Se A A1) B" by (simp add:Point_Eq)
  from assms P56 have P57 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    \<not> Plane_diffside (Li B C) A1 D" by blast
  from assms P3 P8 P48 have P58 : "Line_on (Li B C) A1 \<Longrightarrow>
    Eq (Geos (Lin (Li B A1)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P7 P58 have P59 : "Line_on (Li B C) A1 \<Longrightarrow>
    Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_trans)
  from P10 P59 have P60 : "Line_on (Li B C) A1 \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P32 P60 have P61 : "\<not> Line_on (Li B C) A1" by blast
  from P7 P48 have "Line_on (Li B A) A1" by (blast intro:Line_on_trans Eq_rev)
  then have P62 : "Eq (Geos (Poi A1) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li B A) D" by (simp add:Point_Eq)
  from P34 P62 have P63 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi D) add Emp)" by blast
  from P36 P57 P61 P63 have P64 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> 
    Plane_sameside (Li B C) A1 D" by (simp add:Plane_not_diffside_sameside)
  from P43 have "Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> Plane_sameside (Li B C) D A1" by (simp add:Point_Eq)
  then have P65 : "Eq (Geos (Poi A) add Emp) (Geos (Poi A1) add Emp) \<Longrightarrow> Plane_sameside (Li B C) A1 D" by (simp add:Plane_sameside_rev)
  from P64 P65 have P66 : "Plane_sameside (Li B C) A1 D" by blast
  from P12 P66 have P67 : "Plane_sameside (Li B C1) A1 D" by (simp add:Plane_Line_trans)
  from P12 have P68 : "Line_on (Li B C1) A1 \<Longrightarrow> Line_on (Li B C) A1" by (blast intro:Line_on_trans Eq_rev)
  from P61 P68 have P69 : "\<not> Line_on (Li B C1) A1" by blast
  from assms P69 have "Def (Ang (An B C1 A1))" by (simp add:Ang_sinple_def)
  then have P70 : "Def (Ang (An A1 B C1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P41 P67 P70 show "Ang_inside (An A1 B C1) D" by (simp add:Ang_inside_def)
qed

lemma (in Congruence_Rule) Ang_sub_lemma1 : 
  assumes 
    "Plane_sameside (Li o1 l1) h1 k1"
    "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi l1) add Emp)"
    "Plane_sameside (Li o2 l2) h2 k2"
    "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)"
    "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)"
    "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l2)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)"
    "Ang_inside (An k1 o1 l1) h1"
  shows 
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Ang_inside (An k2 o2 l2) h2"
proof -
  from assms have P1 : "\<not> Line_on (Li o1 l1) h1" by (simp add:Plane_sameside_def)
  from assms P1 have "Def (Ang (An o1 l1 h1))" by (simp add:Ang_sinple_def)
  then have P2 : "Def (Ang (An h1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P3 : "\<not> Line_on (Li o1 l1) k1" by (simp add:Plane_sameside_def)
  from assms P3 have "Def (Ang (An o1 l1 k1))" by (simp add:Ang_sinple_def)
  then have P4 : "Def (Ang (An k1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P5 : "\<not> Line_on (Li o2 l2) h2" by (simp add:Plane_sameside_def)
  from assms P5 have "Def (Ang (An o2 l2 h2))" by (simp add:Ang_sinple_def)
  then have P6 : "Def (Ang (An h2 o2 l2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P7 : "\<not> Line_on (Li o2 l2) k2" by (simp add:Plane_sameside_def)
  from assms P7 have "Def (Ang (An o2 l2 k2))" by (simp add:Ang_sinple_def)
  then have P8 : "Def (Ang (An k2 o2 l2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P4 P8 have "\<exists>p q. Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An p o2 q)) add Emp)
    \<and> Eq (Geos (Ang (An k2 o2 l2)) add Emp) (Geos (Ang (An p o2 q)) add Emp)
    \<and> Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o2 p)) add Emp) \<and> Line_on (Li o2 k2) p \<and> \<not> Bet_Point (Se p k2) o2
    \<and> Eq (Geos (Seg (Se o1 l1)) add Emp) (Geos (Seg (Se o2 q)) add Emp) \<and> Line_on (Li o2 l2) q \<and> \<not> Bet_Point (Se q l2) o2 \<and> Def (Ang (An p o2 q))" by (simp add:Ang_replace)
  then obtain k21 l21 :: Point where P9 : "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k21 o2 l21)) add Emp)
    \<and> Eq (Geos (Ang (An k2 o2 l2)) add Emp) (Geos (Ang (An k21 o2 l21)) add Emp)
    \<and> Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o2 k21)) add Emp) \<and> Line_on (Li o2 k2) k21 \<and> \<not> Bet_Point (Se k21 k2) o2
    \<and> Eq (Geos (Seg (Se o1 l1)) add Emp) (Geos (Seg (Se o2 l21)) add Emp) \<and> Line_on (Li o2 l2) l21 \<and> \<not> Bet_Point (Se l21 l2) o2 \<and> Def (Ang (An k21 o2 l21))" by blast
  from assms have "Plane_diffside (Li o1 h1) k1 l1" by (simp add:Ang_inside_Planeside)
  then have "\<exists>p. Bet_Point (Se k1 l1) p \<and> Line_on (Li o1 h1) p \<and> \<not> Line_on (Li o1 h1) k1 \<and> \<not> Line_on (Li o1 h1) l1" by (simp add:Plane_diffside_def)
  then obtain h11 :: Point where P10 : "Bet_Point (Se k1 l1) h11 \<and> Line_on (Li o1 h1) h11 \<and> \<not> Line_on (Li o1 h1) k1 \<and> \<not> Line_on (Li o1 h1) l1" by blast
  then have "Eq (Geos (Poi h11) add Emp) (Geos (Poi o1) add Emp) \<Longrightarrow>
    Bet_Point (Se k1 l1) o1" by (blast intro:Point_Eq)
  then have P11 : "Eq (Geos (Poi h11) add Emp) (Geos (Poi o1) add Emp) \<Longrightarrow>
    Line_on (Li o1 l1) k1" by (simp add:Line_Bet_on)
  from P3 P11 have P12 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h11) add Emp)" by (blast intro:Eq_rev)
  have P13 : "Line_on (Li o2 h2) o2" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li o2 h2) h2" by (simp add:Line_on_rule)
  from P6 have "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi o2) add Emp)" by (simp add:Ang_def)
  then have P15 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi h2) add Emp)" by (blast intro:Eq_rev)
  from P12 P13 P14 P15 have "\<exists>p. Eq (Geos (Seg (Se o1 h11)) add Emp) (Geos (Seg (Se o2 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p h2) o2 \<and> Line_on (Li o2 h2) p \<and> \<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain h21 :: Point where P16 : "Eq (Geos (Seg (Se o1 h11)) add Emp) (Geos (Seg (Se o2 h21)) add Emp) 
    \<and> \<not> Bet_Point (Se h21 h2) o2 \<and> Line_on (Li o2 h2) h21 \<and> \<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi h21) add Emp)" by blast
  have P17 : "Line_on (Li o1 l1) o1" by (simp add:Line_on_rule)
  have "Line_on (Li h1 h11) h1" by (simp add:Line_on_rule)
  then have P18 : "Eq (Geos (Lin (Li h1 h11)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> Line_on (Li o1 l1) h1" by (simp add:Line_on_trans)
  from P1 P18 have P19 : "\<not> Eq (Geos (Lin (Li h1 h11)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
  from P17 P19 have "Bet_Point (Se h1 h11) o1 \<Longrightarrow> Plane_diffside (Li o1 l1) h1 h11" by (simp add:Plane_Bet_diffside)
  then have P20 : "Bet_Point (Se h1 h11) o1 \<Longrightarrow> Plane_diffside (Li o1 l1) h11 h1" by (simp add:Plane_diffside_rev)
  from P10 have P21 : "Bet_Point (Se l1 k1) h11" by (simp add:Bet_rev)
  have P22 : "Line_on (Li o1 l1) l1" by (simp add:Line_on_rule)
  have "Line_on (Li l1 k1) k1" by (simp add:Line_on_rule)
  then have P23 : "Eq (Geos (Lin (Li l1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> Line_on (Li o1 l1) k1" by (simp add:Line_on_trans)
  from P3 P23 have P24 : "\<not> Eq (Geos (Lin (Li l1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
  from P21 P22 P24 have P25 : "Plane_sameside (Li o1 l1) h11 k1" by (simp add:Plane_Bet_sameside)
  from P20 P25 have "Bet_Point (Se h1 h11) o1 \<Longrightarrow> Plane_diffside (Li o1 l1) h1 k1" by (simp add:Plane_trans Plane_diffside_rev)
  then have P26 : "Bet_Point (Se h1 h11) o1 \<Longrightarrow> \<not> Plane_sameside (Li o1 l1) h1 k1" by (simp add:Plane_diffside_not_sameside)
  from assms P26 have P27 : "\<not> Bet_Point (Se h1 h11) o1" by blast
  have P28 : "\<not> Bet_Point (Se l1 l1) o1" by (simp add:Bet_end_Point)
  from assms P2 P10 P22 P27 P28 P12 have P29 : "Eq (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h11 o1 l1)) add Emp) \<and> Def (Ang (An h11 o1 l1))" by (simp add:Ang_Point_swap)
  from P9 have P30 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l21) add Emp)" by (simp add:Ang_def)
  from P16 have P31 : "\<not> Bet_Point (Se h2 h21) o2" by (blast intro:Bet_rev)
  from P9 have P32 : "\<not> Bet_Point (Se l2 l21) o2" by (blast intro:Bet_rev)
  from P6 P9 P16 P30 P31 P32 have P33 : "Eq (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An h21 o2 l21)) add Emp) \<and> Def (Ang (An h21 o2 l21))" by (simp add:Ang_Point_swap)
  from assms P29 have P34 : "Cong (Geos (Ang (An h11 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P33 P34 have P35 : "Cong (Geos (Ang (An h11 o1 l1)) add Emp) (Geos (Ang (An h21 o2 l21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P29 have "Def (Tri (Tr h11 o1 l1))" by (simp add:Ang_to_Tri)
  then have P36 : "Def (Tri (Tr o1 h11 l1))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P33 have "Def (Tri (Tr h21 o2 l21))" by (simp add:Ang_to_Tri)
  then have P37 : "Def (Tri (Tr o2 h21 l21))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P9 P16 P35 P36 P37 have P38 : "Cong (Geos (Tri (Tr o1 h11 l1)) add Emp) (Geos (Tri (Tr o2 h21 l21)) add Emp)" by (simp add:Tri_SAS)
  then have P39 : "Cong (Geos (Ang (An o1 l1 h11)) add Emp) (Geos (Ang (An o2 l21 h21)) add Emp)" by (simp add:Tri_Cong_def)
  from P4 have P40 : "Def (Tri (Tr o1 k1 l1))" by (simp add:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P9 have P41 : "Def (Tri (Tr o2 k21 l21))" by (simp add:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P9 P40 P41 have P42 : "Cong (Geos (Tri (Tr o1 k1 l1)) add Emp) (Geos (Tri (Tr o2 k21 l21)) add Emp)" by (simp add:Tri_SAS)
  then have P43 : "Cong (Geos (Ang (An o1 l1 k1)) add Emp) (Geos (Ang (An o2 l21 k21)) add Emp)" by (simp add:Tri_Cong_def)
  from P4 have P44 : "Def (Ang (An o1 l1 k1))" by (blast intro:Ang_def_rev Ang_def_inv)
  have P45 : "Line_on (Li l1 o1) o1" by (simp add:Line_on_rule)
  have P46 : "\<not> Bet_Point (Se o1 o1) l1" by (simp add:Bet_end_Point)
  from P10 have P47 : "Line_on (Li l1 k1) h11" by (simp add:Line_Bet_on)
  from P10 have "Inv(Bet_Point (Se h11 k1) l1)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se h11 k1) l1" by (simp add:Inv_def)
  then have P48 : "\<not> Bet_Point (Se k1 h11) l1" by (blast intro:Bet_rev)
  from assms have P49 : "\<not> Eq (Geos (Poi l1) add Emp) (Geos (Poi o1) add Emp)" by (blast intro:Eq_rev)
  from P10 have "Bet_Point (Se k1 l1) h11" by simp
  then have P50 : "\<not> Eq (Geos (Poi l1) add Emp) (Geos (Poi h11) add Emp)" by (simp add:Bet_Point_def)
  from P44 P45 P46 P47 P48 P49 P50 have P51 : "Eq (Geos (Ang (An o1 l1 k1)) add Emp) (Geos (Ang (An o1 l1 h11)) add Emp) \<and> Def (Ang (An o1 l1 h11))" by (simp add:Ang_Point_swap)
  have P52 : "Eq (Geos (Ang (An o2 l21 k21)) add Emp) (Geos (Ang (An k21 l21 o2)) add Emp)" by (simp add:Ang_roll)
  from P43 P52 have P53 : "Cong (Geos (Ang (An o1 l1 k1)) add Emp) (Geos (Ang (An k21 l21 o2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P51 P53 have P54 : "Cong (Geos (Ang (An o1 l1 h11)) add Emp) (Geos (Ang (An k21 l21 o2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P55 : "Eq (Geos (Ang (An o2 l21 h21)) add Emp) (Geos (Ang (An h21 l21 o2)) add Emp)" by (simp add:Ang_roll)
  from P39 P55 have P56 : "Cong (Geos (Ang (An o1 l1 h11)) add Emp) (Geos (Ang (An h21 l21 o2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P57 : "Line_on (Li o2 l2) o2" by (simp add:Line_on_rule)
  have P58 : "Line_on (Li l21 o2) o2" by (simp add:Line_on_rule)
  have P59 : "Line_on (Li l21 o2) l21" by (simp add:Line_on_rule)
  from P9 have P60 : "Line_on (Li o2 l2) l21" by simp
  from P30 P57 P58 P59 P60 have P61 : "Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li l21 o2)) add Emp)" by (simp add:Line_unique)
  from assms P16 P57 have P62 : "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) h21 h2" by (blast intro:Plane_sameside_HalfLine Plane_sameside_rev)
  from assms have P63 : "Plane_sameside (Li o2 l2) k2 h2" by (simp add:Plane_sameside_rev)
  from P41 have P64 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k21) add Emp)" by (simp add:Tri_def)
  from P9 P57 P63 P64 have P65 : "\<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) k2 k21" by (simp add:Plane_sameside_HalfLine)
  then have P66 : "\<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) k21 k2" by (simp add:Plane_sameside_rev)
  from assms P62 have P67 : "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) h21 k2" by (blast intro:Plane_sameside_trans)
  have P68 : "Line_on (Li o2 k2) o2" by (simp add:Line_on_rule)
  from P9 have P69 : "Eq (Geos (Poi k21) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> Line_on (Li o2 k2) h21" by (blast intro:Point_Eq)
  from P9 P13 P16 P68 P69 have P70 : "Eq (Geos (Poi k21) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)" by (blast intro:Line_unique)
  from assms P70 have P71 : "\<not> Eq (Geos (Poi k21) add Emp) (Geos (Poi h21) add Emp)" by blast
  from P65 P67 P71 have P72 : "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) k21 h21" by (blast intro:Plane_sameside_trans Plane_sameside_rev)
  from P66 have P73 : "\<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    Eq (Geos (Poi k2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) k21 h21" by (simp add:Point_Eq)
  from P71 P72 P73 have P74 : "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) k21 h21" by blast 
  from P63 have P75 : "Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow> 
    Plane_sameside (Li o2 l2) k2 h21" by (simp add:Point_Eq)
  from P66 P71 P75 have P76 : "Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) k21 h21" by (blast intro:Plane_sameside_trans Eq_rev) 
  from assms have P77 : "Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) h2 k21" by (simp add:Point_Eq)
  from P62 P71 P77 have P78 : "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) k21 h21" by (blast intro:Plane_sameside_trans Plane_sameside_rev) 
  from P77 have P79 : "Eq (Geos (Poi h2) add Emp) (Geos (Poi h21) add Emp) \<Longrightarrow> 
    Eq (Geos (Poi k2) add Emp) (Geos (Poi k21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 l2) k21 h21" by (blast intro:Point_Eq Plane_sameside_rev) 
  from P71 P74 P76 P78 P79 have P80 : "Plane_sameside (Li o2 l2) k21 h21" by blast
  from P61 P74 P80 have P81 : "Plane_sameside (Li l21 o2) k21 h21" by (simp add:Plane_Line_trans)
  from P54 P56 P74 P81 have P82 : "Eq (Geos (Lin (Li k21 l21)) add Emp) (Geos (Lin (Li h21 l21)) add Emp) \<and> \<not> Bet_Point (Se k21 h21) l21" by (simp add:Ang_move_unique)
  have P83 : "Line_on (Li h21 l21) h21" by (simp add:Line_on_rule)
  from P74 P82 P83 have P84 : "Line_on (Li k21 l21) h21" by (blast intro:Line_on_trans Eq_rev)
  have P85 : "Line_on (Li k21 l21) k21" by (simp add:Line_on_rule)
  have P86 : "Line_on (Li k21 l21) l21" by (simp add:Line_on_rule)
  from P9 have "\<not> Eq (Geos (Poi l21) add Emp) (Geos (Poi k21) add Emp)" by (simp add:Ang_def)
  then have P87 : "\<not> Eq (Geos (Poi k21) add Emp) (Geos (Poi l21) add Emp)" by (blast intro:Eq_rev)
  from P33 have P88 : "\<not> Eq (Geos (Poi l21) add Emp) (Geos (Poi h21) add Emp)" by (simp add:Ang_def)
  from P71 have P89 : "\<not> Eq (Geos (Poi h21) add Emp) (Geos (Poi k21) add Emp)" by (blast intro:Eq_rev)
  from P81 have P90 : "\<not> Line_on (Li l21 o2) k21" by (simp add:Plane_sameside_def)
  from P85 have P91 : "Eq (Geos (Lin (Li k21 l21)) add Emp) (Geos (Lin (Li l21 o2)) add Emp) \<Longrightarrow>
    Line_on (Li l21 o2) k21" by (simp add:Line_on_trans)
  from P90 P91 have P92 : "\<not> Eq (Geos (Lin (Li l21 o2)) add Emp) (Geos (Lin (Li k21 l21)) add Emp)" by (blast intro:Eq_rev)
  from assms P59 P81 P84 P85 P86 P87 P88 P89 P92 have P93 : "Bet_Point (Se h21 l21) k21 \<or> Bet_Point (Se l21 k21) h21" by (simp add:Plane_Bet_sameside_rev)
  from P10 have P94 : "Bet_Point (Se k1 l1) h11" by simp
  then have P95 : "Bet_Point (Se l1 k1) h11" by (simp add:Bet_rev)
  from P42 have P96 : "Eq (Geos (Seg (Se k1 l1)) add Emp) (Geos (Seg (Se k21 l21)) add Emp)" by (simp add:Tri_Cong_def)
  then have P97 : "Eq (Geos (Seg (Se l1 k1)) add Emp) (Geos (Seg (Se l21 k21)) add Emp)" by (blast intro:Eq_rev Eq_trans Seg_rev)
  from P38 have "Eq (Geos (Seg (Se h11 l1)) add Emp) (Geos (Seg (Se h21 l21)) add Emp)" by (simp add:Tri_Cong_def)
  then have P98 : "Eq (Geos (Seg (Se l1 h11)) add Emp) (Geos (Seg (Se l21 h21)) add Emp)" by (blast intro:Eq_rev Eq_trans Seg_rev)
  from P95 P97 P98 have P99 : "\<not> Bet_Point (Se l21 h21) k21" by (blast intro:Seg_Bet_wrong_relation)
  then have P100 : "\<not> Bet_Point (Se h21 l21) k21" by (blast intro:Bet_rev)
  from P93 P100 have "Bet_Point (Se l21 k21) h21" by blast
  then have P101 : "\<not> Seg_on_Seg (Se k21 h21) (Se h21 l21)" by (simp add:Bet_rev Seg_Bet_not_on)
  have P102 : "Line_on (Li k1 l1) k1" by (simp add:Line_on_rule)
  have P103 : "Line_on (Li k1 l1) l1" by (simp add:Line_on_rule)
  from P94 have P104 : "Line_on (Li k1 l1) h11" by (simp add:Line_Bet_on)
  from P94 have P105 : "\<not> Seg_on_Seg (Se k1 h11) (Se h11 l1)" by (simp add:Seg_Bet_not_on)
  from assms P84 P85 P86 P96 P101 P102 P103 P104 P105 have P106 : "Eq (Geos (Seg (Se k1 h11)) add Emp) (Geos (Seg (Se k21 h21)) add Emp)" by (simp add:Seg_sub)
  from P42 have P107 : "Cong (Geos (Ang (An l1 k1 o1)) add Emp) (Geos (Ang (An l21 k21 o2)) add Emp)" by (simp add:Tri_Cong_def)
  from P4 have P108 : "Def (Ang (An l1 k1 o1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P94 have "Inv (Bet_Point (Se l1 h11) k1)" by (simp add:Bet_iff)
  then have P109 : "\<not> Bet_Point (Se l1 h11) k1" by (simp add:Inv_def)
  have P110 : "Line_on (Li k1 o1) o1" by (simp add:Line_on_rule)
  have P111 : "\<not> Bet_Point (Se o1 o1) k1" by (simp add:Bet_end_Point)
  from P94 have "\<not> Eq (Geos (Poi h11) add Emp) (Geos (Poi k1) add Emp)" by (simp add:Bet_Point_def)
  then have P112 : "\<not> Eq (Geos (Poi k1) add Emp) (Geos (Poi h11) add Emp)" by (blast intro:Eq_rev)
  from P108 have P113 : "\<not> Eq (Geos (Poi k1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Ang_def)
  from P104 P108 P109 P110 P111 P112 P113 have P114 : "Eq (Geos (Ang (An l1 k1 o1)) add Emp) (Geos (Ang (An h11 k1 o1)) add Emp) \<and> Def (Ang (An h11 k1 o1))" by (simp add:Ang_Point_swap)
  from P9 have P115 : "Def (Ang (An l21 k21 o2))" by (blast intro:Ang_def_rev Ang_def_inv)
  have P116 : "Line_on (Li k21 o2) o2" by (simp add:Line_on_rule)
  have P117 : "\<not> Bet_Point (Se o2 o2) k21" by (simp add:Bet_end_Point)
  from P64 have P119 : "\<not> Eq (Geos (Poi k21) add Emp) (Geos (Poi o2) add Emp)" by (blast intro:Eq_rev)
  from assms P71 P84 P99 P115 P116 P117 P119 have P120 : "Eq (Geos (Ang (An l21 k21 o2)) add Emp) (Geos (Ang (An h21 k21 o2)) add Emp) \<and> Def (Ang (An h21 k21 o2))" by (simp add:Ang_Point_swap)
  from P107 P114 have P121 : "Cong (Geos (Ang (An h11 k1 o1)) add Emp) (Geos (Ang (An l21 k21 o2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P120 P121 have P122 : " Cong (Geos (Ang (An h11 k1 o1)) add Emp) (Geos (Ang (An h21 k21 o2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P114 have P123 : "Def (Tri (Tr k1 h11 o1))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P120 have P124 : "Def (Tri (Tr k21 h21 o2))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)  
  from P9 have P125 : "Eq (Geos (Seg (Se k1 o1)) add Emp) (Geos (Seg (Se k21 o2)) add Emp)" by (blast intro:Seg_rev Eq_trans Eq_rev)
  from P106 P122 P123 P124 P125 have "Cong (Geos (Tri (Tr k1 h11 o1)) add Emp) (Geos (Tri (Tr k21 h21 o2)) add Emp)" by (simp add:Tri_SAS)
  then have P126 : "Cong (Geos (Ang (An k1 o1 h11)) add Emp) (Geos (Ang (An k21 o2 h21)) add Emp)" by (simp add:Tri_Cong_def)
  have P127 : "Eq (Geos (Ang (An k1 o1 h11)) add Emp) (Geos (Ang (An h11 o1 k1)) add Emp)" by (simp add:Ang_roll)
  have P128 : "Eq (Geos (Ang (An k21 o2 h21)) add Emp) (Geos (Ang (An h21 o2 k21)) add Emp)" by (simp add:Ang_roll)
  from P126 P127 have P129 : "Cong (Geos (Ang (An h11 o1 k1)) add Emp) (Geos (Ang (An k21 o2 h21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P128 P129 have P130 : "Cong (Geos (Ang (An h11 o1 k1)) add Emp) (Geos (Ang (An h21 o2 k21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P114 have P131 : "Def (Ang (An h11 o1 k1))" by (simp add:Ang_def_inv)
  from P2 have "\<not> Eq (Geos (Poi h1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Ang_def)
  then have P132 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp)" by (blast intro:Eq_rev)
  from P10 P12 P132 have P133 : "Line_on (Li o1 h11) h1" by (blast intro:Line_on_rev)
  from P27 have P134 : "\<not> Bet_Point (Se h11 h1) o1" by (blast intro:Bet_rev)
  have P135 : "Line_on (Li o1 k1) k1" by (simp add:Line_on_rule)
  have P136 : "\<not> Bet_Point (Se k1 k1) o1" by (simp add:Bet_end_Point)
  from P4 have "\<not> Eq (Geos (Poi k1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Ang_def)
  then have P137 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp)" by (blast intro:Eq_rev)
  from P131 P132 P133 P134 P135 P136 P137 have P138 : "Eq (Geos (Ang (An h11 o1 k1)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp) \<and> Def (Ang (An h1 o1 k1))" by (simp add:Ang_Point_swap)
  from P120 have P139 : "Def (Ang (An h21 o2 k21))" by (simp add:Ang_def_inv)
  from P15 P16 have P140 : "Line_on (Li o2 h21) h2" by (simp add:Line_on_rev)
  from P16 have P141 : "\<not> Bet_Point (Se h21 h2) o2" by (blast intro:Bet_rev)
  from P8 have "\<not> Eq (Geos (Poi k2) add Emp) (Geos (Poi o2) add Emp)" by (simp add:Ang_def)
  then have P142 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp)" by (blast intro:Eq_rev)
  from P9 P64 P142 have P143 : "Line_on (Li o2 k21) k2" by (simp add:Line_on_rev)
  from P9 P15 P139 P140 P141 P142 P143 have P143 : "Eq (Geos (Ang (An h21 o2 k21)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp) \<and> Def (Ang (An h2 o2 k2))" by (simp add:Ang_Point_swap)
  from P130 P138 have P145 : "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h21 o2 k21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P143 P145 show "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P93 P100 have P146 : "Bet_Point (Se k21 l21) h21" by (blast intro:Bet_rev)
  from P9 have P147 : "\<not> Eq (Geos (Lin (Li o2 k21)) add Emp) (Geos (Lin (Li o2 l21)) add Emp)" by (simp add:Ang_def)
  from P30 P64 P146 P147 have P148 : "Ang_inside (An k21 o2 l21) h21" by (simp add:Ang_inside_Bet_Point)
  from P8 have P149 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Ang_def)
  from P9 P142 P148 P149 have P150 : "Ang_inside (An k2 o2 l2) h21" by (simp add:Ang_inside_trans)
  from P15 P16 have P151 : "Line_on (Li o2 h21) h2" by (simp add:Line_on_rev)
  from P16 have P152 : "\<not> Bet_Point (Se h2 h21) o2" by (blast intro:Bet_rev)
  from P15 P150 P151 P152 show "Ang_inside (An k2 o2 l2) h2" by (simp add:Ang_inside_HalfLine)
qed

text\<open>Theorem15\<close>

theorem (in Congruence_Rule) Ang_sub : 
  assumes 
    "Plane_sameside (Li o1 l1) h1 k1"
    "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi l1) add Emp)"
    "Plane_sameside (Li o2 l2) h2 k2"
    "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)"
    "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)"
    "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l2)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)"
  shows 
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
proof -
  from assms have P1 : "\<not> Line_on (Li o1 l1) h1" by (simp add:Plane_sameside_def)
  from assms P1 have "Def (Ang (An o1 l1 h1))" by (simp add:Ang_sinple_def)
  then have P2 : "Def (Ang (An h1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P3 : "\<not> Line_on (Li o1 l1) k1" by (simp add:Plane_sameside_def)
  from assms P3 have "Def (Ang (An o1 l1 k1))" by (simp add:Ang_sinple_def)
  then have P4 : "Def (Ang (An k1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P2 P4 have P5 : "Ang_inside (An h1 o1 l1) k1 \<and> \<not> Ang_inside (An k1 o1 l1) h1
    \<or> \<not> Ang_inside (An h1 o1 l1) k1 \<and> Ang_inside (An k1 o1 l1) h1" by (simp add:Ang_inside_case)
  from assms have P6 : "Ang_inside (An k1 o1 l1) h1 \<Longrightarrow> 
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by (simp add:Ang_sub_lemma1)
  from assms have P7 : "Plane_sameside (Li o1 l1) k1 h1" by (simp add:Plane_sameside_rev)
  from assms have P8 : "Plane_sameside (Li o2 l2) k2 h2" by (simp add:Plane_sameside_rev)
  from assms have P9 : "\<not> Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)" by (blast intro:Eq_rev)
  from assms have P10 : "\<not> Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp)" by (blast intro:Eq_rev)
  from assms P7 P8 P9 P10 have P11 : "Ang_inside (An h1 o1 l1) k1 \<Longrightarrow>
    Cong (Geos (Ang (An k1 o1 h1)) add Emp) (Geos (Ang (An k2 o2 h2)) add Emp)" by (simp add:Ang_sub_lemma1)
  have P12 : "Eq (Geos (Ang (An k1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (simp add:Ang_roll)
  have P13 : "Eq (Geos (Ang (An k2 o2 h2)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by (simp add:Ang_roll)
  from P11 P12 have P14 : "Ang_inside (An h1 o1 l1) k1 \<Longrightarrow>
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An k2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P13 P14 have P15 : "Ang_inside (An h1 o1 l1) k1 \<Longrightarrow>
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P5 P6 P15 show "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by blast
qed

theorem (in Congruence_Rule) Ang_add : 
  assumes 
    "Plane_diffside (Li o1 l1) h1 k1"
    "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi l1) add Emp)"
    "Plane_diffside (Li o2 l2) h2 k2"
    "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)"
    "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)"
    "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l2)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)"
    "\<not> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)"
  shows 
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
proof -
  from assms have "\<exists>p. Bet_Point (Se h1 k1) p \<and> Line_on (Li o1 l1) p
    \<and> \<not> Line_on (Li o1 l1) h1 \<and> \<not> Line_on (Li o1 l1) k1" by (simp add:Plane_diffside_def)
  then obtain l11 :: Point where P1 : "Bet_Point (Se h1 k1) l11 \<and> Line_on (Li o1 l1) l11
    \<and> \<not> Line_on (Li o1 l1) h1 \<and> \<not> Line_on (Li o1 l1) k1" by blast
  have P2 : "Line_on (Li o1 l1) o1" by (simp add:Line_on_rule)
  then have P3 : "Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp) \<Longrightarrow> Line_on (Li o1 l1) k1" by (simp add:Point_Eq)
  from P1 P3 have P4 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp)" by blast
  have P5 : "Line_on (Li o1 k1) o1" by (simp add:Line_on_rule)
  have P6 : "Line_on (Li o1 k1) k1" by (simp add:Line_on_rule)
  from P4 P5 P6 have "\<exists>p. Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o1 p)) add Emp) 
    \<and> Bet_Point (Se p k1) o1 \<and> Line_on (Li o1 k1) p \<and> \<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_diffside)
  then obtain k11 :: Point where P7 : "Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o1 k11)) add Emp) 
    \<and> Bet_Point (Se k11 k1) o1 \<and> Line_on (Li o1 k1) k11 \<and> \<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k11) add Emp)" by blast
  from P7 have P8 : "Bet_Point (Se k11 k1) o1" by blast
  have "Line_on (Li k11 k1) k1" by (simp add:Line_on_rule)
  then have P9 : "Eq (Geos (Lin (Li k11 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> Line_on (Li o1 l1) k1" by (simp add:Line_on_trans)
  from P1 P9 have P10 : "\<not> Eq (Geos (Lin (Li k11 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
  from P2 P8 P10 have "Plane_diffside (Li o1 l1) k11 k1" by (simp add:Plane_Bet_diffside)
  then have P11 : "Plane_diffside (Li o1 l1) k1 k11" by (simp add:Plane_diffside_rev)
  from assms have P12 : "Plane_diffside (Li o1 l1) k1 h1" by (simp add:Plane_diffside_rev)
  from P2 have P13 : "Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp) \<Longrightarrow> Line_on (Li o1 l1) h1" by (simp add:Point_Eq)
  from P1 P13 have P14 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp)" by blast
  have P15 : "Line_on (Li o1 h1) o1" by (simp add:Line_on_rule)
  have P16 : "Line_on (Li o1 h1) h1" by (simp add:Line_on_rule)
  from P5 P14 P15 P16 have P17 : "Line_on (Li o1 k1) h1 
    \<Longrightarrow> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)" by (simp add:Line_unique)
  from assms P17 have P18 : "\<not> Line_on (Li o1 k1) h1" by blast
  from P7 have P19 : "Eq (Geos (Poi k11) add Emp) (Geos (Poi h1) add Emp) \<Longrightarrow> Line_on (Li o1 k1) h1" by (blast intro:Point_Eq)
  from P18 P19 have P20 : "\<not> Eq (Geos (Poi k11) add Emp) (Geos (Poi h1) add Emp)" by blast
  from P11 P12 P20 have "Plane_sameside (Li o1 l1) k11 h1" by (blast intro:Plane_trans_inv)
  then have P21 : "Plane_sameside (Li o1 l1) h1 k11" by (simp add:Plane_sameside_rev)
  from assms have "\<exists>p. Bet_Point (Se h2 k2) p \<and> Line_on (Li o2 l2) p
    \<and> \<not> Line_on (Li o2 l2) h2 \<and> \<not> Line_on (Li o2 l2) k2" by (simp add:Plane_diffside_def)
  then obtain l21 :: Point where P22 : "Bet_Point (Se h2 k2) l21 \<and> Line_on (Li o2 l2) l21
    \<and> \<not> Line_on (Li o2 l2) h2 \<and> \<not> Line_on (Li o2 l2) k2" by blast
  have P23 : "Line_on (Li o2 l2) o2" by (simp add:Line_on_rule)
  then have P24 : "Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp) \<Longrightarrow> Line_on (Li o2 l2) k2" by (simp add:Point_Eq)
  from P22 P24 have P25 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp)" by blast
  have P26 : "Line_on (Li o2 k2) o2" by (simp add:Line_on_rule)
  have P27 : "Line_on (Li o2 k2) k2" by (simp add:Line_on_rule)
  from P4 P25 P26 P27 have "\<exists>p. Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o2 p)) add Emp) 
    \<and> Bet_Point (Se p k2) o2 \<and> Line_on (Li o2 k2) p \<and> \<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_diffside)
  then obtain k21 :: Point where P28 : "Eq (Geos (Seg (Se o1 k1)) add Emp) (Geos (Seg (Se o2 k21)) add Emp) 
    \<and> Bet_Point (Se k21 k2) o2 \<and> Line_on (Li o2 k2) k21 \<and> \<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k21) add Emp)" by blast
  from P28 have P29 : "Bet_Point (Se k21 k2) o2" by blast
  have "Line_on (Li k21 k2) k2" by (simp add:Line_on_rule)
  then have P30 : "Eq (Geos (Lin (Li k21 k2)) add Emp) (Geos (Lin (Li o2 l2)) add Emp) \<Longrightarrow> Line_on (Li o2 l2) k2" by (simp add:Line_on_trans)
  from assms have "\<exists>p. Bet_Point (Se h2 k2) p \<and> Line_on (Li o2 l2) p
    \<and> \<not> Line_on (Li o2 l2) h2 \<and> \<not> Line_on (Li o2 l2) k2" by (simp add:Plane_diffside_def)
  from P22 P30 have P31 : "\<not> Eq (Geos (Lin (Li k21 k2)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)" by blast
  from P23 P29 P31 have "Plane_diffside (Li o2 l2) k21 k2" by (simp add:Plane_Bet_diffside)
  then have P32 : "Plane_diffside (Li o2 l2) k2 k21" by (simp add:Plane_diffside_rev)
  from assms have P33 : "Plane_diffside (Li o2 l2) k2 h2" by (simp add:Plane_diffside_rev)
  from P23 have P34 : "Eq (Geos (Poi o2) add Emp) (Geos (Poi h2) add Emp) \<Longrightarrow> Line_on (Li o2 l2) h2" by (simp add:Point_Eq)
  from P22 P34 have P35 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi h2) add Emp)" by blast
  have P36 : "Line_on (Li o2 h2) o2" by (simp add:Line_on_rule)
  have P37 : "Line_on (Li o2 h2) h2" by (simp add:Line_on_rule)
  from P26 P35 P36 P37 have P38 : "Line_on (Li o2 k2) h2 
    \<Longrightarrow> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)" by (simp add:Line_unique)
  from assms P38 have P39 : "\<not> Line_on (Li o2 k2) h2" by blast
  from P28 have P40 : "Eq (Geos (Poi k21) add Emp) (Geos (Poi h2) add Emp) \<Longrightarrow> Line_on (Li o2 k2) h2" by (blast intro:Point_Eq)
  from P39 P40 have P41 : "\<not> Eq (Geos (Poi k21) add Emp) (Geos (Poi h2) add Emp)" by blast
  from P32 P33 P41 have "Plane_sameside (Li o2 l2) k21 h2" by (blast intro:Plane_trans_inv)
  then have P42 : "Plane_sameside (Li o2 l2) h2 k21" by (simp add:Plane_sameside_rev)
  from assms P1 have "Def (Ang (An o1 l1 k1))" by (simp add:Ang_sinple_def)
  then have P43 : "Def (Ang (An k1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P22 have "Def (Ang (An o2 l2 k2))" by (simp add:Ang_sinple_def)
  then have P44 : "Def (Ang (An k2 o2 l2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P8 have P45 : "Bet_Point (Se k1 k11) o1" by (simp add:Bet_rev)
  from P28 have P46 : "Bet_Point (Se k2 k21) o2" by (simp add:Bet_rev)
  from assms P43 P44 P45 P46 have P47 : "Cong (Geos (Ang (An l1 o1 k11)) add Emp) (Geos (Ang (An l2 o2 k21)) add Emp)" by (simp add:Ang_complementary)
  have P48 : "Eq (Geos (Ang (An l1 o1 k11)) add Emp) (Geos (Ang (An k11 o1 l1)) add Emp)" by (simp add:Ang_roll)
  have P49 : "Eq (Geos (Ang (An l2 o2 k21)) add Emp) (Geos (Ang (An k21 o2 l2)) add Emp)" by (simp add:Ang_roll)  
  from P47 P48 have P50 : "Cong (Geos (Ang (An k11 o1 l1)) add Emp) (Geos (Ang (An l2 o2 k21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P49 P50 have P51 : "Cong (Geos (Ang (An k11 o1 l1)) add Emp) (Geos (Ang (An k21 o2 l2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P52 : "Line_on (Li o1 k11) k11" by (simp add:Line_on_rule)
  have P53 : "Line_on (Li o1 k11) o1" by (simp add:Line_on_rule)
  from P5 P7 P52 P53 have P54 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 k11)) add Emp)" by (blast intro:Line_unique)
  from P54 have P55 : "Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k11)) add Emp)
    \<Longrightarrow> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P55 have P56 : "\<not> Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k11)) add Emp)" by blast
  have P57 : "Line_on (Li o2 k21) k21" by (simp add:Line_on_rule)
  have P58 : "Line_on (Li o2 k21) o2" by (simp add:Line_on_rule)
  from P26 P28 P57 P58 have P59 : "Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li o2 k21)) add Emp)" by (blast intro:Line_unique)
  from P59 have P60 : "Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k21)) add Emp)
    \<Longrightarrow> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P60 have P61 : "\<not> Eq (Geos (Lin (Li o2 h2)) add Emp) (Geos (Lin (Li o2 k21)) add Emp)" by blast
  from assms P21 P42 P51 P56 P61 have P62 : "Cong (Geos (Ang (An h1 o1 k11)) add Emp) (Geos (Ang (An h2 o2 k21)) add Emp)" by (simp add:Ang_sub)
  have P63 : "Eq (Geos (Ang (An h1 o1 k11)) add Emp) (Geos (Ang (An k11 o1 h1)) add Emp)" by (simp add:Ang_roll)
  have P64 : "Eq (Geos (Ang (An h2 o2 k21)) add Emp) (Geos (Ang (An k21 o2 h2)) add Emp)" by (simp add:Ang_roll)  
  from P62 P63 have P65 : "Cong (Geos (Ang (An k11 o1 h1)) add Emp) (Geos (Ang (An h2 o2 k21)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P64 P65 have P66 : "Cong (Geos (Ang (An k11 o1 h1)) add Emp) (Geos (Ang (An k21 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P54 have P67 : "Line_on (Li o1 k11) h1 \<Longrightarrow> Line_on (Li o1 k1) h1" by (blast intro:Line_on_trans Eq_rev)
  from P18 P67 have P68 : "\<not> Line_on (Li o1 k11) h1" by blast
  from P7 P68 have "Def (Ang (An o1 k11 h1))" by (simp add:Ang_sinple_def)
  then have P69 : "Def (Ang (An k11 o1 h1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P59 have P70 : "Line_on (Li o2 k21) h2 \<Longrightarrow> Line_on (Li o2 k2) h2" by (blast intro:Line_on_trans Eq_rev)
  from P39 P70 have P71 : "\<not> Line_on (Li o2 k21) h2" by blast
  from P28 P71 have "Def (Ang (An o2 k21 h2))" by (simp add:Ang_sinple_def)
  then have P72 : "Def (Ang (An k21 o2 h2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P8 P29 P66 P69 P72 show "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)" by (simp add:Ang_complementary)
qed

lemma (in Congruence_Rule) Ang_split_lemma1 : 
  assumes N : 
    "Def (Ang (An h1 o1 k1))" "Def (Ang (An h2 o2 k2))"
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Cong (Geos (Ang (An l1 o1 k1)) add Emp) (Geos (Ang (An l2 o2 k2)) add Emp)"
    "Plane_sameside (Li o1 k1) h1 l1"
    "Plane_sameside (Li o2 k2) h2 l2"
    "\<not> Eq (Geos (Lin (Li o1 l1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)"
  shows 
    "\<not> Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp)"
proof 
  assume W : "Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp)"
  have P1 : "Line_on (Li o2 k2) o2" by (simp add:Line_on_rule)
  from N have P2 : "\<not> Line_on (Li o2 k2) h2 \<and> \<not> Line_on (Li o2 k2) l2
    \<and> \<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Plane_sameside_def)
  from P1 P2 have "Bet_Point (Se h2 l2) o2 \<Longrightarrow> (\<exists>p. Bet_Point (Se h2 l2) p 
    \<and> Line_on (Li o2 k2) p \<and> \<not> Line_on (Li o2 k2) h2 \<and> \<not> Line_on (Li o2 k2) l2)" by blast
  then have "Bet_Point (Se h2 l2) o2 \<Longrightarrow> Plane_diffside (Li o2 k2) h2 l2" by (simp add:Plane_diffside_def)
  then have P3 : "Bet_Point (Se h2 l2) o2 \<Longrightarrow> \<not> Plane_sameside (Li o2 k2) h2 l2" by (simp add:Plane_diffside_not_sameside)
  from N P3 have P4 : "\<not> Bet_Point (Se h2 l2) o2" by blast
  have P5 : "Line_on (Li o2 l2) l2" by (simp add:Line_on_rule)
  from W P5 have P6 : "Line_on (Li o2 h2) l2" by (simp add:Line_on_trans)
  have P7 : "Line_on (Li o2 k2) k2" by (simp add:Line_on_rule)
  have P8 : "\<not> Bet_Point (Se k2 k2) o2" by (simp add:Bet_end_Point)
  from P1 have P9 : "Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp) \<Longrightarrow> Line_on (Li o2 k2) l2" by (simp add:Point_Eq)
  from P2 P9 have P10 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)" by blast
  from N have "Def (Tri (Tr h2 o2 k2))" by (simp add:Ang_to_Tri)
  then have P11 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp)" by (simp add:Tri_def)
  from N P4 P6 P7 P8 P10 P11 have P12 : 
    "Eq (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An l2 o2 k2)) add Emp) \<and> Def (Ang (An l2 o2 k2))" by (simp add:Ang_Point_swap)
  from N P12 have P13 : "Cong (Geos (Ang (An l2 o2 k2)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from N have P14 : "Cong (Geos (Ang (An l2 o2 k2)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)" by (blast intro:Ang_rev)
  from N P13 P14 have P15 : "Eq (Geos (Lin (Li h1 o1)) add Emp) (Geos (Lin (Li l1 o1)) add Emp) \<and> \<not> Bet_Point (Se h1 l1) o1" by (simp add:Ang_move_unique)
  from N have "Def (Tri (Tr h1 o1 k1))" by (simp add:Ang_to_Tri)
  then have "\<not> Eq (Geos (Poi h1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Tri_def)
  then have P16 : "Eq (Geos (Lin (Li h1 o1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)" by (simp add:Line_rev)
  from N have P17 : "\<not> Line_on (Li o1 k1) h1 \<and> \<not> Line_on (Li o1 k1) l1
    \<and> \<not> Eq (Geos (Poi h1) add Emp) (Geos (Poi l1) add Emp)" by (simp add:Plane_sameside_def)
  have P18 : "Line_on (Li o1 k1) o1" by (simp add:Line_on_rule)
  then have P19 : "Eq (Geos (Poi o1) add Emp) (Geos (Poi l1) add Emp) \<Longrightarrow> Line_on (Li o1 k1) l1" by (simp add:Point_Eq)
  from P17 P19 have "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi l1) add Emp)" by blast
  then have P20 : "Eq (Geos (Lin (Li o1 l1)) add Emp) (Geos (Lin (Li l1 o1)) add Emp)" by (simp add:Line_rev)
  from P15 P16 have P21 : "Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li l1 o1)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P20 P21 have P22 : "Eq (Geos (Lin (Li o1 l1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from N P22 show False by blast
qed

text\<open>Theorem16\<close>

theorem (in Congruence_Rule) Ang_split : 
  assumes
    "Def (Ang (An h1 o1 k1))" "Def (Ang (An h2 o2 k2))"
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Ang_inside (An h1 o1 k1) l1"
  shows 
    "\<exists>p. Ang_inside (An h2 o2 k2) p
    \<and> Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 p)) add Emp)
    \<and> Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 p)) add Emp)"
proof -
  from assms have P1 : "Plane_sameside (Li o1 h1) k1 l1 \<and> Plane_sameside (Li o1 k1) h1 l1" by (simp add:Ang_inside_def)
  from assms have P2 : "\<not> Line_on (Li o2 k2) h2" by (simp add:Ang_to_Tri Tri_def_Line)
  from P1 have P3 : "\<not> Line_on (Li o1 k1) l1" by (simp add:Plane_sameside_def)
  from assms have P4 : "Def (Tri (Tr h1 o1 k1))" by (simp add:Ang_to_Tri)
  then have P5 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp)" by (simp add:Tri_def)
  from P3 P5 have "Def (Ang (An o1 k1 l1))" by (simp add:Ang_sinple_def)
  then have P6 : "Def (Ang (An k1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P2 P6 have "\<exists>p. Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An p o2 k2)) add Emp)
    \<and> Plane_sameside (Li o2 k2) p h2" by (simp add:Ang_move_sameside)
  then obtain l2 :: Point where P7 : "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An l2 o2 k2)) add Emp)
    \<and> Plane_sameside (Li o2 k2) l2 h2" by blast
  from assms have "Def (Tri (Tr h2 o2 k2))" by (simp add:Ang_to_Tri)
  then have P8 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp)" by (simp add:Tri_def)
  have P9 : "Eq (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)" by (simp add:Ang_roll)
  from P7 P9 have P10 : "Cong (Geos (Ang (An l1 o1 k1)) add Emp) (Geos (Ang (An l2 o2 k2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P1 have P11 : "\<not> Line_on_Seg (Li o1 h1) (Se k1 l1) \<and> \<not> Line_on (Li o1 h1) k1 
    \<and> \<not> Line_on (Li o1 h1) l1 \<and> \<not> Eq (Geos (Poi k1) add Emp) (Geos (Poi l1) add Emp)" by (simp add:Plane_sameside_def)
  have "Line_on (Li o1 l1) l1" by (simp add:Line_on_rule)
  then have P12 : "Eq (Geos (Lin (Li o1 l1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp) \<Longrightarrow> Line_on (Li o1 h1) l1" by (simp add:Line_on_trans)
  from P11 P12 have P13 : "\<not> Eq (Geos (Lin (Li o1 l1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)" by blast
  from P7 have P14 : "Plane_sameside (Li o2 k2) h2 l2" by (simp add:Plane_sameside_rev)
  from assms P1 P10 P13 P14 have P15 : "\<not> Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp)" by (simp add:Ang_split_lemma1)
  from P1 have P16 :  "Plane_sameside (Li o1 k1) l1 h1" by (simp add:Plane_sameside_rev)
  from P7 have P17 : "Plane_sameside (Li o2 k2) l2 h2" by simp
  from assms P5 P8 P10 P13 P15 P16 P17 have P18 :
    "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)
    \<and> Ang_inside (An h2 o2 k2) l2" by (simp add:Ang_sub_lemma1)
  have P19 : "Eq (Geos (Ang (An l2 o2 k2)) add Emp) (Geos (Ang (An k2 o2 l2)) add Emp)" by (simp add:Ang_roll)
  from P7 P19 have P20 : "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P21 : "Eq (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)" by (simp add:Ang_roll)
  have P22 : "Eq (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (simp add:Ang_roll)
  from P18 P21 have P23 : "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P22 P23 have P24 : "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P18 P20 P24 show "\<exists>p. Ang_inside (An h2 o2 k2) p
    \<and> Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 p)) add Emp)
    \<and> Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 p)) add Emp)" by blast
qed

theorem (in Congruence_Rule) Ang_split_unique : 
  assumes
    "Def (Ang (An h1 o1 k1))" "Def (Ang (An h2 o2 k2))"
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Ang_inside (An h1 o1 k1) l1"
    "Ang_inside (An h2 o2 k2) l21"
    "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l21)) add Emp)"
    "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l21)) add Emp)"
    "Ang_inside (An h2 o2 k2) l22"
    "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l22)) add Emp)"
    "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l22)) add Emp)"
  shows 
    "Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l22)) add Emp)"
proof -
  from assms have "Plane_sameside (Li o2 h2) k2 l21 \<and> Plane_sameside (Li o2 k2) h2 l21" by (simp add:Ang_inside_def)
  then have P1 : "Plane_sameside (Li o2 k2) l21 h2" by (simp add:Plane_sameside_rev)
  from assms have P2 : "Plane_sameside (Li o2 h2) k2 l22 \<and> Plane_sameside (Li o2 k2) h2 l22" by (simp add:Ang_inside_def)
  from P1 P2 have P3 : "\<not> Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow>
    Plane_sameside (Li o2 k2) l21 l22" by (simp add:Plane_sameside_trans)
  have P4 : "Eq (Geos (Ang (An k2 o2 l21)) add Emp) (Geos (Ang (An l21 o2 k2)) add Emp)" by (simp add:Ang_roll)
  from assms P4 have P5 : "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An l21 o2 k2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P6 : "Eq (Geos (Ang (An k2 o2 l22)) add Emp) (Geos (Ang (An l22 o2 k2)) add Emp)" by (simp add:Ang_roll)
  from assms P6 have P7 : "Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An l22 o2 k2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P3 P5 P7 have P8 : "\<not> Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li l21 o2)) add Emp) (Geos (Lin (Li l22 o2)) add Emp)" by (simp add:Ang_move_unique)
  have P9 : "Line_on (Li o2 k2) o2" by (simp add:Line_on_rule)
  from P1 have P10 : "\<not> Line_on (Li o2 k2) l21" by (simp add:Plane_sameside_def)
  from P9 have P11 : "Eq (Geos (Poi o2) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow> Line_on (Li o2 k2) l21" by (simp add:Point_Eq)
  from P10 P11 have P12 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l21) add Emp)" by blast
  then have P13 : "Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li l21 o2)) add Emp)" by (simp add:Line_rev)
  from P2 have P14 : "\<not> Line_on (Li o2 k2) l22" by (simp add:Plane_sameside_def)
  from P9 have P15 : "Eq (Geos (Poi o2) add Emp) (Geos (Poi l22) add Emp) \<Longrightarrow> Line_on (Li o2 k2) l22" by (simp add:Point_Eq)
  from P14 P15 have "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l22) add Emp)" by blast
  then have P16 : "Eq (Geos (Lin (Li o2 l22)) add Emp) (Geos (Lin (Li l22 o2)) add Emp)" by (simp add:Line_rev)
  from P8 P13 have P17 : "\<not> Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li l22 o2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P16 P17 have P18 : "\<not> Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l22)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  have P19 : "Line_on (Li o2 l21) o2" by (simp add:Line_on_rule)
  have P20 : "Line_on (Li o2 l21) l21" by (simp add:Line_on_rule)
  have P21 : "Line_on (Li o2 l22) o2" by (simp add:Line_on_rule)
  have "Line_on (Li o2 l22) l22" by (simp add:Line_on_rule)
  then have P22 : "Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow> Line_on (Li o2 l22) l21" by (simp add:Point_Eq)
  from P12 P19 P20 P21 P22 have P23 : "Eq (Geos (Poi l22) add Emp) (Geos (Poi l21) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l22)) add Emp)" by (simp add:Line_unique)
  from P18 P23 show "Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l22)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Tri_week_SSS_lemma1 :
  assumes
    "Plane_diffside (Li x y) z1 z2"
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi y) add Emp)"
    "Eq (Geos (Seg (Se x z1)) add Emp) (Geos (Seg (Se x z2)) add Emp)"
    "Eq (Geos (Seg (Se y z1)) add Emp) (Geos (Seg (Se y z2)) add Emp)"
    "\<exists>p. Bet_Point (Se z1 z2) p \<and> Line_on (Li x y) p \<and> Eq (Geos (Poi x) add Emp) (Geos (Poi p) add Emp)"
  shows "Cong (Geos (Ang (An x z1 y)) add Emp) (Geos (Ang (An x z2 y)) add Emp)"
proof -
  from assms have P1 : "\<exists>p. Bet_Point (Se z1 z2) p \<and> Line_on (Li x y) p 
    \<and> \<not> Line_on (Li x y) z1 \<and> \<not> Line_on (Li x y) z2" by (simp add:Plane_diffside_def)
  from assms obtain pn :: Point where P2 : "Bet_Point (Se z1 z2) pn \<and> Line_on (Li x y) pn \<and> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp)" by blast
  from P2 have P3 : "Bet_Point (Se z1 z2) pn" by simp
  then have P4 : "Line_on (Li z1 z2) pn" by (simp add:Line_Bet_on)
  from P2 P4 have P5 : "Line_on (Li z1 z2) x" by (blast intro:Eq_rev Point_Eq)
  from assms P3 have P6 : "Bet_Point (Se z1 z2) x" by (blast intro:Eq_rev Point_Eq)
  have P7 : "Line_on (Li x y) x" by (simp add:Line_on_rule)
  have P8 : "Line_on (Li x y) y" by (simp add:Line_on_rule)
  from assms P5 P7 P8 have P9 : "Line_on (Li z1 z2) y \<Longrightarrow> Eq (Geos (Lin (Li z1 z2)) add Emp) (Geos (Lin (Li x y)) add Emp)" by (simp add:Line_unique)
  have P10 : "Line_on (Li z1 z2) z1" by (simp add:Line_on_rule)
  from P9 P10 have P11 : "Line_on (Li z1 z2) y \<Longrightarrow> Line_on (Li x y) z1" by (simp add:Line_on_trans)
  from P1 P11 have P12 : "\<not> Line_on (Li z1 z2) y" by blast
  from P3 have P13 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi z2) add Emp)" by (simp add:Bet_Point_def)
  from P8 have P14 : "Eq (Geos (Poi z2) add Emp) (Geos (Poi y) add Emp) \<Longrightarrow> Line_on (Li x y) z2" by (blast intro:Eq_rev Point_Eq)
  from P1 P14 have P15 : "\<not> Eq (Geos (Poi z2) add Emp) (Geos (Poi y) add Emp)" by blast
  from P8 have P16 : "Eq (Geos (Poi y) add Emp) (Geos (Poi z1) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (blast intro:Eq_rev Point_Eq)
  from P1 P16 have P17 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi z1) add Emp)" by blast
  from P12 P13 have P18 : "Def (Tri (Tr z1 z2 y))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P19 : "Def (Tri (Tr y z1 z2))" by (blast intro:Tri_def_trans)
  from assms P19 have P20 : "Cong (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An y z2 z1)) add Emp)" by (simp add:Tri_isosceles)
  from P18 have P21 : "Def (Ang (An z1 z2 y))" by (simp add:Tri_to_Ang)
  from P6 have P22 : "Line_on (Li z2 z1) x" by (simp add:Line_Bet_on)
  from P6 have P23 : "Inv (Bet_Point (Se z2 x) z1) \<and> Inv (Bet_Point (Se x z1) z2)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se x z1) z2" by (simp add:Inv_def)
  then have P24 : "\<not> Bet_Point (Se z1 x) z2" by (blast intro:Bet_rev)
  have P25 : "Line_on (Li z2 y) y" by (simp add:Line_on_rule)
  have P26 : "\<not> Bet_Point (Se y y) z2" by (simp add:Bet_end_Point)
  from P6 have P27 : "\<not> Eq (Geos (Poi z2) add Emp) (Geos (Poi x) add Emp)" by (simp add:Bet_Point_def)
  from P15 P21 P22 P24 P25 P26 P27 have P28 : 
    "Eq (Geos (Ang (An z1 z2 y)) add Emp) (Geos (Ang (An x z2 y)) add Emp) \<and> Def (Ang (An x z2 y))" by (simp add:Ang_Point_swap)
  have P29 : "Eq (Geos (Ang (An y z2 z1)) add Emp) (Geos (Ang (An z1 z2 y)) add Emp)" by (simp add:Ang_roll)
  from P20 P29 have P30 : "Cong (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An z1 z2 y)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P28 P30 have P31 : "Cong (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An x z2 y)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P19 have P32 : "Def (Ang (An z2 z1 y))" by (blast intro:Tri_to_Ang Tri_def_rev)
  from P6 have P33 : "Line_on (Li z1 z2) x" by (simp add:Line_Bet_on)
  from P23 have P34 : "\<not> Bet_Point (Se z2 x) z1" by (simp add:Inv_def)
  have P35 : "Line_on (Li z1 y) y" by (simp add:Line_on_rule)
  have P36 : "\<not> Bet_Point (Se y y) z1" by (simp add:Bet_end_Point)
  from P6 have "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi z1) add Emp)" by (simp add:Bet_Point_def)
  then have P37 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi x) add Emp)" by (blast intro:Eq_rev)
  from P17 have P38 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi y) add Emp)" by (blast intro:Eq_rev)
  from P32 P33 P34 P35 P36 P37 P38 have P39 : 
    "Eq (Geos (Ang (An z2 z1 y)) add Emp) (Geos (Ang (An x z1 y)) add Emp) \<and> Def (Ang (An x z1 y))" by (simp add:Ang_Point_swap)
  have P40 : "Eq (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An z2 z1 y)) add Emp)" by (simp add:Ang_roll)
  from P31 P40 have P41 : "Cong (Geos (Ang (An z2 z1 y)) add Emp) (Geos (Ang (An x z2 y)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P39 P41 show "Cong (Geos (Ang (An x z1 y)) add Emp) (Geos (Ang (An x z2 y)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
qed

text\<open>Theorem17\<close>

theorem (in Congruence_Rule) Tri_week_SSS :
  assumes
    "Plane_diffside (Li x y) z1 z2"
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi y) add Emp)"
    "Eq (Geos (Seg (Se x z1)) add Emp) (Geos (Seg (Se x z2)) add Emp)"
    "Eq (Geos (Seg (Se y z1)) add Emp) (Geos (Seg (Se y z2)) add Emp)"
  shows "Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An x y z2)) add Emp)"
proof -
  from assms have "\<exists>p. Bet_Point (Se z1 z2) p \<and> Line_on (Li x y) p 
    \<and> \<not> Line_on (Li x y) z1 \<and> \<not> Line_on (Li x y) z2" by (simp add:Plane_diffside_def)
  then obtain pn :: Point where P1 : "Bet_Point (Se z1 z2) pn \<and> Line_on (Li x y) pn
    \<and> \<not> Line_on (Li x y) z1 \<and> \<not> Line_on (Li x y) z2" by blast
  have P2 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Eq (Geos (Poi x) add Emp) (Geos (Poi y) add Emp)" by (blast intro:Eq_trans)
  from assms P2 have "\<not> (Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp))" by blast
  then have P3 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp)
    \<or> \<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp)
    \<or> \<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp)" by blast
  from P1 have P4 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    \<exists>p. Bet_Point (Se z1 z2) p \<and> Line_on (Li x y) p \<and> Eq (Geos (Poi x) add Emp) (Geos (Poi p) add Emp)" by blast
  from assms P4 have P5 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An x z1 y)) add Emp) (Geos (Ang (An x z2 y)) add Emp)" by (simp add:Tri_week_SSS_lemma1)
  have P6 : "Line_on (Li x y) x" by (simp add:Line_on_rule)
  then have P7 : "Eq (Geos (Poi x) add Emp) (Geos (Poi z1) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (simp add:Point_Eq)
  from P1 P7 have P8 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi x) add Emp)" by (blast intro:Eq_rev)
  have P9 : "Line_on (Li x y) y" by (simp add:Line_on_rule)
  then have P10 : "Eq (Geos (Poi y) add Emp) (Geos (Poi z1) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (simp add:Point_Eq)
  from P1 P10 have P11 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi z1) add Emp)" by blast
  from assms P1 have "Def (Tri (Tr x y z1))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P12 : "Def (Tri (Tr z1 x y))" by (simp add:Tri_def_trans)
  from P6 have P13 : "Eq (Geos (Poi x) add Emp) (Geos (Poi z2) add Emp) \<Longrightarrow> Line_on (Li x y) z2" by (simp add:Point_Eq)
  from P1 P13 have P14 : "\<not> Eq (Geos (Poi z2) add Emp) (Geos (Poi x) add Emp)" by (blast intro:Eq_rev)
  from P9 have P15 : "Eq (Geos (Poi y) add Emp) (Geos (Poi z2) add Emp) \<Longrightarrow> Line_on (Li x y) z2" by (simp add:Point_Eq)
  from P1 P15 have P16 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi z2) add Emp)" by (blast intro:Eq_rev)
  from assms P1 have "Def (Tri (Tr x y z2))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P17 : "Def (Tri (Tr z2 x y))" by (simp add:Tri_def_trans)
  have P18 : "Eq (Geos (Seg (Se x z1)) add Emp) (Geos (Seg (Se z1 x)) add Emp)" by (blast intro:Seg_rev)
  have P19 : "Eq (Geos (Seg (Se x z2)) add Emp) (Geos (Seg (Se z2 x)) add Emp)" by (blast intro:Seg_rev)
  from assms P18 have P20 : "Eq (Geos (Seg (Se z1 x)) add Emp) (Geos (Seg (Se x z2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P19 P20 have P21 : "Eq (Geos (Seg (Se z1 x)) add Emp) (Geos (Seg (Se z2 x)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  have P22 : "Eq (Geos (Seg (Se y z1)) add Emp) (Geos (Seg (Se z1 y)) add Emp)" by (blast intro:Seg_rev)
  have P23 : "Eq (Geos (Seg (Se y z2)) add Emp) (Geos (Seg (Se z2 y)) add Emp)" by (blast intro:Seg_rev)
  from assms P22 have P24 : "Eq (Geos (Seg (Se z1 y)) add Emp) (Geos (Seg (Se y z2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P23 P24 have P25 : "Eq (Geos (Seg (Se z1 y)) add Emp) (Geos (Seg (Se z2 y)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P5 P12 P17 P21 P25 have "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Tri (Tr z1 x y)) add Emp) (Geos (Tri (Tr z2 x y)) add Emp)" by (simp add:Tri_SAS)
  then have P26 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An z1 y x)) add Emp) (Geos (Ang (An z2 y x)) add Emp)" by (simp add:Tri_Cong_def)
  have P27 : "Eq (Geos (Ang (An z1 y x)) add Emp) (Geos (Ang (An x y z1)) add Emp)" by (simp add:Ang_roll)
  have P28 : "Eq (Geos (Ang (An z2 y x)) add Emp) (Geos (Ang (An x y z2)) add Emp)" by (simp add:Ang_roll)
  from P26 P27 have P29 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An z2 y x)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P28 P29 have P30 : "Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An x y z2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms have P31 : "Eq (Geos (Lin (Li x y)) add Emp) (Geos (Lin (Li y x)) add Emp)" by (simp add:Line_rev)
  from assms P31 have P32 : "Plane_diffside (Li y x) z1 z2" by (simp add:Plane_Line_diff_trans)
  from assms have P33 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi x) add Emp)" by (blast intro:Eq_rev)
  from P1 P31 have P34 : "Line_on (Li y x) pn" by (blast intro:Line_on_trans)
  from P1 P34 have P35 : "Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    \<exists>p. Bet_Point (Se z1 z2) p \<and> Line_on (Li y x) p \<and> Eq (Geos (Poi y) add Emp) (Geos (Poi p) add Emp)" by blast
  from assms P32 P33 P35 have P36 : "Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An y z1 x)) add Emp) (Geos (Ang (An y z2 x)) add Emp)" by (simp add:Tri_week_SSS_lemma1)
  from P12 have P37 : "Def (Tri (Tr z1 y x))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P17 have P38 : "Def (Tri (Tr z2 y x))" by (blast intro:Tri_def_trans Tri_def_rev)
  from P21 P25 P36 P37 P38 have "Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Tri (Tr z1 y x)) add Emp) (Geos (Tri (Tr z2 y x)) add Emp)" by (simp add:Tri_SAS)
  then have P39 : "Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An x y z2)) add Emp)" by (simp add:Tri_Cong_def)
  from P1 have P40 : "Bet_Point (Se z1 z2) pn" by simp
  then have P41 : "Line_on (Li z1 z2) pn" by (simp add:Line_Bet_on)
  have "Line_on (Li z1 z2) z1" by (simp add:Line_on_rule)
  then have P42 : "Eq (Geos (Lin (Li z1 z2)) add Emp) (Geos (Lin (Li x y)) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (simp add:Line_on_trans)
  from P1 P42 have P43 : "\<not> Eq (Geos (Lin (Li z1 z2)) add Emp) (Geos (Lin (Li x y)) add Emp)" by blast
  from P1 P6 P41 have P44 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> Line_on (Li z1 z2) x \<Longrightarrow>
    Eq (Geos (Lin (Li z1 z2)) add Emp) (Geos (Lin (Li x y)) add Emp)" by (simp add:Line_unique)
  from P43 P44 have P45 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    \<not> Line_on (Li z1 z2) x" by blast
  from P40 have P46 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi z2) add Emp)" by (simp add:Bet_Point_def)
  from P45 P46 have "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Tri (Tr z1 z2 x))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P47 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Tri (Tr x z1 z2))" by (simp add:Tri_def_trans)
  from assms P47 have P48 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An x z1 z2)) add Emp) (Geos (Ang (An x z2 z1)) add Emp)" by (simp add:Tri_isosceles)
  have P49 : "Line_on (Li z1 x) x" by (simp add:Line_on_rule)
  have P50 : "\<not> Bet_Point (Se x x) z1" by (simp add:Bet_end_Point)
  from P40 have P51 : "Inv (Bet_Point (Se z2 pn) z1) \<and> Inv (Bet_Point (Se pn z1) z2)" by (simp add:Bet_iff)
  then have P52 : "\<not> Bet_Point (Se z2 pn) z1" by (simp add:Inv_def)
  from P40 have "\<not> Eq (Geos (Poi pn) add Emp) (Geos (Poi z1) add Emp)" by (simp add:Bet_Point_def)
  then have P53 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi pn) add Emp)" by (blast intro:Eq_rev)
  from P47 have P54 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Ang (An x z1 z2))" by (simp add:Tri_to_Ang)
  from P8 P41 P49 P50 P52 P53 P54 have P55 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Eq (Geos (Ang (An x z1 z2)) add Emp) (Geos (Ang (An x z1 pn)) add Emp) \<and> Def (Ang (An x z1 pn))" by (simp add:Ang_Point_swap)
  from P48 P55 have P56 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An x z1 pn)) add Emp) (Geos (Ang (An x z2 z1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P47 have P57 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Ang (An x z2 z1))" by (blast intro:Tri_def_rev Tri_def_trans Tri_to_Ang)
  have P58 : "Line_on (Li z2 x) x" by (simp add:Line_on_rule)
  have P59 : "\<not> Bet_Point (Se x x) z2" by (simp add:Bet_end_Point)
  from P40 have P60 : "Line_on (Li z2 z1) pn" by (simp add:Line_Bet_on)
  from P51 have "\<not> Bet_Point (Se pn z1) z2" by (simp add:Inv_def)
  then have P61 : "\<not> Bet_Point (Se z1 pn) z2" by (blast intro:Bet_rev)
  from P40 have P62 : "\<not> Eq (Geos (Poi z2) add Emp) (Geos (Poi pn) add Emp)" by (simp add:Bet_Point_def)
  from P14 P57 P58 P59 P60 P61 P62 have P63 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Eq (Geos (Ang (An x z2 z1)) add Emp) (Geos (Ang (An x z2 pn)) add Emp) \<and> Def (Ang (An x z2 pn))" by (simp add:Ang_Point_swap)
  from P56 P63 have P64 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An x z1 pn)) add Emp) (Geos (Ang (An x z2 pn)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P1 P9 P41 have P65 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> Line_on (Li z1 z2) y \<Longrightarrow>
    Eq (Geos (Lin (Li z1 z2)) add Emp) (Geos (Lin (Li x y)) add Emp)" by (simp add:Line_unique)
  from P43 P65 have P66 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    \<not> Line_on (Li z1 z2) y" by blast
  from P46 P66 have "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Tri (Tr z1 z2 y))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P67 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Tri (Tr y z1 z2))" by (simp add:Tri_def_trans)
  from assms P67 have P68 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An y z2 z1)) add Emp)" by (simp add:Tri_isosceles)
  from P67 have P69 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Ang (An y z1 z2))" by (simp add:Tri_to_Ang)
  have P70 : "Line_on (Li z1 y) y" by (simp add:Line_on_rule)
  have P71 : "\<not> Bet_Point (Se y y) z1" by (simp add:Bet_end_Point)
  from P11 have P72 : "\<not> Eq (Geos (Poi z1) add Emp) (Geos (Poi y) add Emp)" by (blast intro:Eq_rev)
  from P41 P52 P53 P69 P70 P71 P72 have P73 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Eq (Geos (Ang (An y z1 z2)) add Emp) (Geos (Ang (An y z1 pn)) add Emp) \<and> Def (Ang (An y z1 pn))" by (simp add:Ang_Point_swap)
  from P68 P73 have P74 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An y z1 pn)) add Emp) (Geos (Ang (An y z2 z1)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P69 have P75 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Def (Ang (An y z2 z1))" by (simp add:Ang_def_inv)
  have P76 : "Line_on (Li z2 y) y" by (simp add:Line_on_rule)
  have P77 : "\<not> Bet_Point (Se y y) z2" by (simp add:Bet_end_Point)
  from P16 have P78 : "\<not> Eq (Geos (Poi z2) add Emp) (Geos (Poi y) add Emp)" by (blast intro:Eq_rev)
  from P60 P61 P62 P75 P76 P77 P78 have P79 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Eq (Geos (Ang (An y z2 z1)) add Emp) (Geos (Ang (An y z2 pn)) add Emp) \<and> Def (Ang (An y z2 pn))" by (simp add:Ang_Point_swap)
  from P74 P79 have P80 : "\<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An y z1 pn)) add Emp) (Geos (Ang (An y z2 pn)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P81 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Poi pn) add Emp) (Geos (Poi x) add Emp)" by (blast intro:Eq_rev)
  from assms P1 P6 P9 P81 have
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Bet_Point (Se x pn) y \<or> Bet_Point (Se pn y) x \<or> Bet_Point (Se y x) pn" by (simp add:Bet_case)
  then have P82 :
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow>
    Bet_Point (Se x pn) y \<and> \<not> Bet_Point (Se pn y) x \<and> \<not> Bet_Point (Se y x) pn
    \<or> \<not> Bet_Point (Se x pn) y \<and> Bet_Point (Se pn y) x \<and> \<not> Bet_Point (Se y x) pn
    \<or> \<not> Bet_Point (Se x pn) y \<and> \<not> Bet_Point (Se pn y) x \<and> Bet_Point (Se y x) pn" by (simp add:Bet_case_fact)
  have P83 : "Bet_Point (Se x pn) y \<Longrightarrow> Bet_Point (Se pn x) y" by (simp add:Bet_rev)
  have P84 : "Line_on (Li z1 pn) pn" by (simp add:Line_on_rule)
  have P85 : "Line_on (Li pn x) x" by (simp add:Line_on_rule)
  from P83 have P86 : "Bet_Point (Se x pn) y \<Longrightarrow> Line_on (Li pn x) y" by (simp add:Line_Bet_on)
  from assms P6 P9 P85 P86 have P87 : "Bet_Point (Se x pn) y \<Longrightarrow>
    Eq (Geos (Lin (Li pn x)) add Emp) (Geos (Lin (Li x y)) add Emp)" by (simp add:Line_unique)
  have P88 : "Line_on (Li z1 pn) z1" by (simp add:Line_on_rule)
  from P87 P88 have P89 : "Bet_Point (Se x pn) y \<Longrightarrow>
    Eq (Geos (Lin (Li pn x)) add Emp) (Geos (Lin (Li z1 pn)) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (blast intro:Line_on_trans Eq_rev)
  from P1 P89 have P90 : "Bet_Point (Se x pn) y \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li pn x)) add Emp) (Geos (Lin (Li z1 pn)) add Emp)" by blast
  from P83 P84 P90 have P91 : "Bet_Point (Se x pn) y \<Longrightarrow> Plane_sameside (Li z1 pn) y x" by (simp add:Plane_Bet_sameside)
  have P92 : "Line_on (Li z2 pn) pn" by (simp add:Line_on_rule)
  have P93 : "Line_on (Li z2 pn) z2" by (simp add:Line_on_rule)
  from P87 P93 have P94 : "Bet_Point (Se x pn) y \<Longrightarrow>
    Eq (Geos (Lin (Li pn x)) add Emp) (Geos (Lin (Li z2 pn)) add Emp) \<Longrightarrow> Line_on (Li x y) z2" by (blast intro:Line_on_trans Eq_rev)
  from P1 P94 have P95 : "Bet_Point (Se x pn) y \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li pn x)) add Emp) (Geos (Lin (Li z2 pn)) add Emp)" by blast
  from P83 P92 P95 have P96 : "Bet_Point (Se x pn) y \<Longrightarrow> Plane_sameside (Li z2 pn) y x" by (simp add:Plane_Bet_sameside)
  from P37 have "Def (Ang (An y z1 x))" by (blast intro:Tri_to_Ang Ang_def_rev Ang_def_inv)
  then have P97 : "\<not> Eq (Geos (Lin (Li z1 y)) add Emp) (Geos (Lin (Li z1 x)) add Emp)" by (simp add:Ang_def)
  from P38 have "Def (Ang (An y z2 x))" by (blast intro:Tri_to_Ang Ang_def_rev Ang_def_inv)
  then have P98 : "\<not> Eq (Geos (Lin (Li z2 y)) add Emp) (Geos (Lin (Li z2 x)) add Emp)" by (simp add:Ang_def)
  from P53 P62 P64 P80 P91 P96 P97 P98 have P99 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) 
    \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> Bet_Point (Se x pn) y \<Longrightarrow> 
    Cong (Geos (Ang (An y z1 x)) add Emp) (Geos (Ang (An y z2 x)) add Emp)" by (simp add:Ang_sub)
  have P100 : "Line_on (Li pn y) y" by (simp add:Line_on_rule)
  from P85 have P101 : "Bet_Point (Se pn y) x \<Longrightarrow> Line_on (Li pn y) x" by (simp add:Line_Bet_on)
  from assms P6 P9 P100 P101 have P102 : "Bet_Point (Se pn y) x \<Longrightarrow>
    Eq (Geos (Lin (Li pn y)) add Emp) (Geos (Lin (Li x y)) add Emp)" by (simp add:Line_unique)
  from P88 P102 have P103 : "Bet_Point (Se pn y) x \<Longrightarrow>
    Eq (Geos (Lin (Li pn y)) add Emp) (Geos (Lin (Li z1 pn)) add Emp) \<Longrightarrow> Line_on (Li x y) z1" by (blast intro:Line_on_trans Eq_rev)
  from P1 P103 have P104 : "Bet_Point (Se pn y) x \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li pn y)) add Emp) (Geos (Lin (Li z1 pn)) add Emp)" by blast
  from P84 P104 have "Bet_Point (Se pn y) x \<Longrightarrow> Plane_sameside (Li z1 pn) x y" by (simp add:Plane_Bet_sameside)
  then have P105 : "Bet_Point (Se pn y) x \<Longrightarrow> Plane_sameside (Li z1 pn) y x" by (simp add:Plane_sameside_rev)
  from P93 P102 have P106 : "Bet_Point (Se pn y) x \<Longrightarrow>
    Eq (Geos (Lin (Li pn y)) add Emp) (Geos (Lin (Li z2 pn)) add Emp) \<Longrightarrow> Line_on (Li x y) z2" by (blast intro:Line_on_trans Eq_rev)
  from P1 P106 have P107 : "Bet_Point (Se pn y) x \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li pn y)) add Emp) (Geos (Lin (Li z2 pn)) add Emp)" by blast
  from P92 P107 have "Bet_Point (Se pn y) x \<Longrightarrow> Plane_sameside (Li z2 pn) x y" by (simp add:Plane_Bet_sameside)
  then have P108 : "Bet_Point (Se pn y) x \<Longrightarrow> Plane_sameside (Li z2 pn) y x" by (simp add:Plane_sameside_rev)
  from P53 P62 P64 P80 P97 P98 P105 P108 have P109 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) 
    \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> Bet_Point (Se pn y) x \<Longrightarrow>
    Cong (Geos (Ang (An y z1 x)) add Emp) (Geos (Ang (An y z2 x)) add Emp)" by (simp add:Ang_sub)
  have P110 : "Bet_Point (Se y x) pn \<Longrightarrow> Bet_Point (Se x y) pn" by (simp add:Bet_rev)
  from P88 have P111 : "Eq (Geos (Lin (Li x y)) add Emp) (Geos (Lin (Li z1 pn)) add Emp)
    \<Longrightarrow> Line_on (Li x y) z1" by (blast intro:Line_on_trans Eq_rev)
  from P1 P111 have P112 : "\<not> Eq (Geos (Lin (Li x y)) add Emp) (Geos (Lin (Li z1 pn)) add Emp)" by blast
  from P84 P110 P112 have "Bet_Point (Se y x) pn \<Longrightarrow> Plane_diffside (Li z1 pn) x y" by (simp add:Plane_Bet_diffside)
  then have P113 : "Bet_Point (Se y x) pn \<Longrightarrow> Plane_diffside (Li z1 pn) y x" by (simp add:Plane_diffside_rev)
  from P93 have P114 : "Eq (Geos (Lin (Li x y)) add Emp) (Geos (Lin (Li z2 pn)) add Emp)
    \<Longrightarrow> Line_on (Li x y) z2" by (blast intro:Line_on_trans Eq_rev)
  from P1 P114 have P115 : "\<not> Eq (Geos (Lin (Li x y)) add Emp) (Geos (Lin (Li z2 pn)) add Emp)" by blast
  from P92 P110 P115 have "Bet_Point (Se y x) pn \<Longrightarrow> Plane_diffside (Li z2 pn) x y" by (simp add:Plane_Bet_diffside)
  then have P116 : "Bet_Point (Se y x) pn \<Longrightarrow> Plane_diffside (Li z2 pn) y x" by (simp add:Plane_diffside_rev)
  from P53 P62 P64 P80 P97 P98 P113 P116 have P117 : "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) 
    \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> Bet_Point (Se y x) pn \<Longrightarrow>
    Cong (Geos (Ang (An y z1 x)) add Emp) (Geos (Ang (An y z2 x)) add Emp)" by (simp add:Ang_add)
  from P82 P99 P109 P117 have P118 : 
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An y z1 x)) add Emp) (Geos (Ang (An y z2 x)) add Emp)" by blast
  from P21 P25 P37 P38 P118 have
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Tri (Tr z1 y x)) add Emp) (Geos (Tri (Tr z2 y x)) add Emp)" by (simp add:Tri_SAS)
  then have P119 : 
    "\<not> Eq (Geos (Poi x) add Emp) (Geos (Poi pn) add Emp) \<and> \<not> Eq (Geos (Poi y) add Emp) (Geos (Poi pn) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An x y z2)) add Emp)" by (simp add:Tri_Cong_def)
  from P3 P30 P39 P119 show "Cong (Geos (Ang (An x y z1)) add Emp) (Geos (Ang (An x y z2)) add Emp)" by blast
qed

text\<open>Theorem18\<close>

theorem (in Congruence_Rule) Tri_SSS :
  assumes
    "Def (Tri (Tr A1 B1 C1))" "Def (Tri (Tr A2 B2 C2))"
    "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)"
    "Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B2 C2)) add Emp)"
    "Eq (Geos (Seg (Se C1 A1)) add Emp) (Geos (Seg (Se C2 A2)) add Emp)"
  shows "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)"
proof -
  from assms have "Def (Tri (Tr C2 B2 A2))" by (simp add:Tri_def_rev)
  then have P1 : "\<not> Line_on (Li A2 C2) B2" by (simp add:Tri_def_Line)
  from assms have P2 : "Def (Ang (An B1 A1 C1))" by (blast intro:Tri_def_rev Tri_def_trans Tri_to_Ang)
  from P1 P2 have "\<exists>p. Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An p A2 C2)) add Emp) \<and> Plane_sameside (Li A2 C2) p B2" by (simp add:Ang_move_sameside)
  then obtain B21 :: Point where P3 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B21 A2 C2)) add Emp) 
    \<and> Plane_sameside (Li A2 C2) B21 B2" by blast
  then have P4 : "\<not> Line_on (Li A2 C2) B21" by (simp add:Plane_sameside_def)
  from P2 P4 have "\<exists>p. Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An p A2 C2)) add Emp) \<and> Plane_diffside (Li A2 C2) p B21" by (simp add:Ang_move_diffside)
  then obtain B22 :: Point where P5 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B22 A2 C2)) add Emp) 
    \<and> Plane_diffside (Li A2 C2) B22 B21" by blast
  have P6 : "Line_on (Li A2 B21) A2" by (simp add:Line_on_rule)
  have P7 : "Line_on (Li A2 B21) B21" by (simp add:Line_on_rule)
  have P8 : "Line_on (Li A2 C2) A2" by (simp add:Line_on_rule)
  then have P9 : "Eq (Geos (Poi A2) add Emp) (Geos (Poi B21) add Emp) \<Longrightarrow> Line_on (Li A2 C2) B21" by (simp add:Point_Eq)
  from P4 P9 have P10 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B21) add Emp)" by blast
  from assms have P11 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi B1) add Emp)" by (simp add:Tri_def)
  from P6 P7 P10 P11 have "\<exists>p. Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p B21) A2 \<and> Line_on (Li A2 B21) p \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain B211 :: Point where P12 : "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B211)) add Emp)
    \<and> \<not> Bet_Point (Se B211 B21) A2 \<and> Line_on (Li A2 B21) B211 \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B211) add Emp)" by blast
  have P13 : "Line_on (Li A2 B22) A2" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li A2 B22) B22" by (simp add:Line_on_rule)
  from P8 have P15 : "Eq (Geos (Poi A2) add Emp) (Geos (Poi B22) add Emp) \<Longrightarrow> Line_on (Li A2 C2) B22" by (simp add:Point_Eq)
  from P5 have P16 : "\<exists>p. Bet_Point (Se B22 B21) p \<and> Line_on (Li A2 C2) p 
    \<and> \<not> Line_on (Li A2 C2) B22 \<and> \<not> Line_on (Li A2 C2) B21" by (simp add:Plane_diffside_def)
  from P15 P16 have P17 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B22) add Emp)" by blast
  from P11 P13 P14 P17 have "\<exists>p. Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p B22) A2 \<and> Line_on (Li A2 B22) p \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain B221 :: Point where P18 : "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B221)) add Emp)
    \<and> \<not> Bet_Point (Se B221 B22) A2 \<and> Line_on (Li A2 B22) B221 \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B221) add Emp)" by blast
  from assms have P19 : "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Tri_def)
  then have P20 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi C2) add Emp)" by (blast intro:Eq_rev)
  from P4 P20 have P21 : "Def (Ang (An B21 A2 C2))" by (blast intro:Ang_sinple_def Ang_def_rev Ang_def_inv)
  from P12 have "\<not> Bet_Point (Se B211 B21) A2" by blast
  then have P22 : "\<not> Bet_Point (Se B21 B211) A2" by (blast intro:Bet_rev)
  have P23 : "Line_on (Li A2 C2) C2" by (simp add:Line_on_rule)
  have P24 : "\<not> Bet_Point (Se C2 C2) A2" by (simp add:Bet_end_Point)
  from P12 P20 P21 P22 P23 P24 have P25 : 
    "Eq (Geos (Ang (An B21 A2 C2)) add Emp) (Geos (Ang (An B211 A2 C2)) add Emp) \<and> Def (Ang (An B211 A2 C2))" by (simp add:Ang_Point_swap)
  from P3 P25 have P26 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B211 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms have P27 : "Def (Tri (Tr A1 B1 C1))" by (simp add:Ang_to_Tri)
  from P25 have P28 : "Def (Tri (Tr A2 B211 C2))" by (blast intro:Ang_to_Tri Tri_def_trans Tri_def_rev)
  from assms have P29 : "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by (blast intro:Seg_rev Eq_rev Eq_trans)
  from P12 P26 P27 P28 P29 have "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B211 C2)) add Emp)" by (simp add:Tri_SAS)
  then have P30 : "Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B211 C2)) add Emp)" by (simp add:Tri_Cong_def)
  from P16 P20 have P31 : "Def (Ang (An B22 A2 C2))" by (blast intro:Ang_sinple_def Ang_def_rev Ang_def_inv)
  from P18 have "\<not> Bet_Point (Se B221 B22) A2" by blast
  then have P32 : "\<not> Bet_Point (Se B22 B221) A2" by (blast intro:Bet_rev)
  from P18 P20 P23 P24 P31 P32 have P33 : 
    "Eq (Geos (Ang (An B22 A2 C2)) add Emp) (Geos (Ang (An B221 A2 C2)) add Emp) \<and> Def (Ang (An B221 A2 C2))" by (simp add:Ang_Point_swap)
  from P5 P33 have P34 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B221 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P33 have P35 : "Def (Tri (Tr A2 B221 C2))" by (blast intro:Ang_to_Tri Tri_def_trans Tri_def_rev)
  from P18 P27 P29 P34 P35 have "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B221 C2)) add Emp)" by (simp add:Tri_SAS)
  then have P36 : "Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B221 C2)) add Emp)" by (simp add:Tri_Cong_def)
  from P12 have P37 : "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B211)) add Emp)" by simp
  from P18 have P38 : "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B221)) add Emp)" by simp
  from P37 P38 have P39 : "Eq (Geos (Seg (Se A2 B221)) add Emp) (Geos (Seg (Se A2 B211)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P38 have P40 : "Eq (Geos (Seg (Se A2 B221)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P30 P36 have P41 : "Eq (Geos (Seg (Se B221 C2)) add Emp) (Geos (Seg (Se B211 C2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P36 have P42 : "Eq (Geos (Seg (Se B221 C2)) add Emp) (Geos (Seg (Se B2 C2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P5 have P43 : "Plane_diffside (Li A2 C2) B22 B21" by simp
  then have P44 : "Eq (Geos (Poi B21) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow>
    Plane_diffside (Li A2 C2) B22 B211" by (blast intro:Point_Eq Eq_rev)
  from P6 P8 P20 P23 have P45 : "Line_on (Li A2 B21) C2 \<Longrightarrow> 
    Eq (Geos (Lin (Li A2 B21)) add Emp) (Geos (Lin (Li A2 C2)) add Emp)" by (simp add:Line_unique)
  from P7 P45 have P46 : "Line_on (Li A2 B21) C2 \<Longrightarrow> Line_on (Li A2 C2) B21" by (simp add:Line_on_trans)
  from P4 P46 have P47 : "\<not> Line_on (Li A2 B21) C2" by blast
  from P6 P7 P10 P12 P22 P47 have P48 : "Plane_sameside (Li C2 A2) B21 B211 \<or> Eq (Geos (Poi B21) add Emp) (Geos (Poi B211) add Emp)" by (simp add:Seg_Plane_sameside)
  from P20 have P49 : "Plane_sameside (Li C2 A2) B21 B211 \<Longrightarrow>
    Plane_sameside (Li A2 C2) B21 B211" by (blast intro:Line_rev Plane_Line_trans Eq_rev)
  from P43 have P50 : "Plane_diffside (Li A2 C2) B21 B22" by (simp add:Plane_diffside_rev)
  from P49 P50 have P51 : "Plane_sameside (Li C2 A2) B21 B211 \<Longrightarrow> 
    Plane_diffside (Li A2 C2) B22 B211" by (simp add:Plane_trans Plane_diffside_rev)
  from P44 P48 P51 have P52 : "Plane_diffside (Li A2 C2) B22 B211" by blast
  then have "Plane_diffside (Li A2 C2) B211 B22" by (blast intro:Plane_diffside_rev)
  then have P53 : "Eq (Geos (Poi B22) add Emp) (Geos (Poi B221) add Emp) \<Longrightarrow>
    Plane_diffside (Li A2 C2) B211 B221" by (blast intro:Point_Eq Eq_rev)
  from P8 P13 P20 P23 have P54 : "Line_on (Li A2 B22) C2 \<Longrightarrow> 
    Eq (Geos (Lin (Li A2 B22)) add Emp) (Geos (Lin (Li A2 C2)) add Emp)" by (simp add:Line_unique)
  from P14 P54 have P55 : "Line_on (Li A2 B22) C2 \<Longrightarrow> Line_on (Li A2 C2) B22" by (simp add:Line_on_trans)
  from P16 P55 have P56 : "\<not> Line_on (Li A2 B22) C2" by blast
  from P31 have "\<not> Eq (Geos (Poi B22) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Ang_def)
  then have P57 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B22) add Emp)" by (blast intro:Eq_rev)
  from P13 P14 P18 P32 P56 P57 have P58 : "Plane_sameside (Li C2 A2) B22 B221 \<or> Eq (Geos (Poi B22) add Emp) (Geos (Poi B221) add Emp)" by (simp add:Seg_Plane_sameside)
  from P20 have P59 : "Plane_sameside (Li C2 A2) B22 B221 \<Longrightarrow> Plane_sameside (Li A2 C2) B22 B221" by (blast intro:Line_rev Plane_Line_trans Eq_rev)
  from P52 P59 have P60 : "Plane_sameside (Li C2 A2) B22 B221 \<Longrightarrow>
    Plane_diffside (Li A2 C2) B211 B221" by (simp add:Plane_trans Plane_diffside_rev)
  from P53 P58 P60 have "Plane_diffside (Li A2 C2) B211 B221" by blast
  then have P61 : "Plane_diffside (Li A2 C2) B221 B211" by (simp add:Plane_diffside_rev)
  from P20 P61 have P62 : "Plane_diffside (Li C2 A2) B221 B211" by (blast intro:Line_rev Plane_Line_diff_trans)
  have P63 : "Eq (Geos (Seg (Se B221 C2)) add Emp) (Geos (Seg (Se C2 B221)) add Emp)" by (simp add:Seg_rev)
  have P64 : "Eq (Geos (Seg (Se B211 C2)) add Emp) (Geos (Seg (Se C2 B211)) add Emp)" by (simp add:Seg_rev)
  from P41 P63 P64 have P65 : "Eq (Geos (Seg (Se C2 B221)) add Emp) (Geos (Seg (Se C2 B211)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P19 P39 P62 P65 have P66 : "Cong (Geos (Ang (An C2 A2 B221)) add Emp) (Geos (Ang (An C2 A2 B211)) add Emp)" by (simp add:Tri_week_SSS)
  have P67 : "Eq (Geos (Ang (An C2 A2 B211)) add Emp) (Geos (Ang (An B211 A2 C2)) add Emp)" by (simp add:Ang_roll)
  from P66 P67 have P68 : "Cong (Geos (Ang (An C2 A2 B221)) add Emp) (Geos (Ang (An B211 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P3 have P69 : "Plane_sameside (Li A2 C2) B21 B2" by simp
  from P50 P69 have P70 : "Plane_diffside (Li A2 C2) B2 B22" by (simp add:Plane_trans)
  then have P71 : "Plane_diffside (Li A2 C2) B22 B2" by (simp add:Plane_diffside_rev)
  from P70 have P72 : "Eq (Geos (Poi B22) add Emp) (Geos (Poi B221) add Emp) \<Longrightarrow>
    Plane_diffside (Li A2 C2) B221 B2" by (blast intro:Point_Eq Plane_diffside_rev)
  from P59 P71 have P73 : "Plane_sameside (Li C2 A2) B22 B221 \<Longrightarrow> 
    Plane_diffside (Li A2 C2) B221 B2" by (simp add:Plane_trans)
  from P58 P72 P73 have P74 : "Plane_diffside (Li A2 C2) B221 B2" by blast
  from P20 P74 have P75 : "Plane_diffside (Li C2 A2) B221 B2" by (blast intro:Line_rev Plane_Line_diff_trans)
  have P76 : "Eq (Geos (Seg (Se B221 C2)) add Emp) (Geos (Seg (Se C2 B221)) add Emp)" by (simp add:Seg_rev)
  have P77 : "Eq (Geos (Seg (Se B2 C2)) add Emp) (Geos (Seg (Se C2 B2)) add Emp)" by (simp add:Seg_rev)
  from P42 P76 P77 have P78 : "Eq (Geos (Seg (Se C2 B221)) add Emp) (Geos (Seg (Se C2 B2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P19 P40 P75 P78 have P79 : "Cong (Geos (Ang (An C2 A2 B221)) add Emp) (Geos (Ang (An C2 A2 B2)) add Emp)" by (simp add:Tri_week_SSS)
  have P80 : "Eq (Geos (Ang (An C2 A2 B2)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (simp add:Ang_roll)
  from P79 P80 have P81 : "Cong (Geos (Ang (An C2 A2 B221)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P52 P71 have P82 : "\<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow>
    Plane_sameside (Li A2 C2) B2 B211" by (blast intro:Plane_trans_inv)
  from P68 P81 P82 have P83 : "\<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li B2 A2)) add Emp) (Geos (Lin (Li B211 A2)) add Emp) \<and> \<not> Bet_Point (Se B2 B211) A2" by (simp add:Ang_move_unique)
  from assms have P84 : "Def (Ang (An B2 A2 C2))" by (blast intro:Tri_to_Ang Ang_def_rev Ang_def_inv)
  then have "\<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Ang_def)
  then have P85 : "Eq (Geos (Lin (Li B2 A2)) add Emp) (Geos (Lin (Li A2 B2)) add Emp)" by (simp add:Line_rev)
  have P86 : "Line_on (Li B211 A2) B211" by (simp add:Line_on_rule)
  from P83 P85 P86 have P87 : "\<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow>
    Line_on (Li A2 B2) B211" by (blast intro:Eq_rev Line_on_trans)
  have "Line_on (Li A2 B2) B2" by (simp add:Line_on_rule)
  then have P88 : "Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow> Line_on (Li A2 B2) B211" by (simp add:Point_Eq)
  from P87 P88 have P89 : "Line_on (Li A2 B2) B211" by blast
  have P90 : "\<not> Bet_Point (Se B2 B2) A2" by (simp add:Bet_end_Point)
  have P91 : "Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow>
    Bet_Point (Se B211 B2) A2 \<Longrightarrow> Bet_Point (Se B2 B2) A2" by (blast intro:Eq_rev Bet_Point_Eq)
  from P90 P91 have P92 : "Eq (Geos (Poi B2) add Emp) (Geos (Poi B211) add Emp) \<Longrightarrow> \<not> Bet_Point (Se B2 B211) A2" by (blast intro:Bet_rev)
  from P83 P92 have P93 : "\<not> Bet_Point (Se B2 B211) A2" by blast
  from P12 P20 P23 P24 P84 P89 P93 have P94 : 
    "Eq (Geos (Ang (An B2 A2 C2)) add Emp) (Geos (Ang (An B211 A2 C2)) add Emp) \<and> Def (Ang (An B211 A2 C2))" by (simp add:Ang_Point_swap)
  from P25 P94 have P95 : "Eq (Geos (Ang (An B21 A2 C2)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P3 P95 have P96 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P97 : "Eq (Geos (Seg (Se C1 A1)) add Emp) (Geos (Seg (Se A1 C1)) add Emp)" by (simp add:Seg_rev)
  have P98 : "Eq (Geos (Seg (Se C2 A2)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by (simp add:Seg_rev)
  from assms P97 P98 have P99 : "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from assms have P100 : "Def (Tri (Tr A1 B1 C1))" by (simp add:Ang_to_Tri)
  from assms have P101 : "Def (Tri (Tr A2 B2 C2))" by (simp add:Ang_to_Tri)
  from assms P96 P99 P100 P101 show "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)" by (simp add:Tri_SAS)
qed

text\<open>Theorem19\<close>

theorem (in Congruence_Rule) Ang_trans : 
  assumes
    "Def (Ang (An A1 B1 C1))" "Def (Ang (An A2 B2 C2))" "Def (Ang (An A3 B3 C3))"
    "Cong (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An A1 B1 C1)) add Emp)"
    "Cong (Geos (Ang (An A3 B3 C3)) add Emp) (Geos (Ang (An A1 B1 C1)) add Emp)"
  shows "Cong (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An A3 B3 C3)) add Emp)"
proof -
  from assms have P1 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp)" by (simp add:Ang_rev)
  from assms P1 have "\<exists>p q. Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B2 q)) add Emp)
    \<and> Eq (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An p B2 q)) add Emp) 
    \<and> Eq (Geos (Seg (Se B1 A1)) add Emp) (Geos (Seg (Se B2 p)) add Emp)
    \<and> Line_on (Li B2 A2) p \<and> \<not> Bet_Point (Se p A2) B2
    \<and> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B2 q)) add Emp)
    \<and> Line_on (Li B2 C2) q \<and> \<not> Bet_Point (Se q C2) B2 \<and> Def (Ang (An p B2 q))" by (simp add:Ang_replace)
  then obtain A21 C21 :: Point where P2 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A21 B2 C21)) add Emp)
    \<and> Eq (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An A21 B2 C21)) add Emp) 
    \<and> Eq (Geos (Seg (Se B1 A1)) add Emp) (Geos (Seg (Se B2 A21)) add Emp)
    \<and> Line_on (Li B2 A2) A21 \<and> \<not> Bet_Point (Se A21 A2) B2
    \<and> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B2 C21)) add Emp)
    \<and> Line_on (Li B2 C2) C21 \<and> \<not> Bet_Point (Se C21 C2) B2 \<and> Def (Ang (An A21 B2 C21))" by blast
  from assms have P3 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A3 B3 C3)) add Emp)" by (simp add:Ang_rev)
  from assms P3 have "\<exists>p q. Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An p B3 q)) add Emp)
    \<and> Eq (Geos (Ang (An A3 B3 C3)) add Emp) (Geos (Ang (An p B3 q)) add Emp) 
    \<and> Eq (Geos (Seg (Se B1 A1)) add Emp) (Geos (Seg (Se B3 p)) add Emp)
    \<and> Line_on (Li B3 A3) p \<and> \<not> Bet_Point (Se p A3) B3
    \<and> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B3 q)) add Emp)
    \<and> Line_on (Li B3 C3) q \<and> \<not> Bet_Point (Se q C3) B3 \<and> Def (Ang (An p B3 q))" by (simp add:Ang_replace)
  then obtain A31 C31 :: Point where P4 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A31 B3 C31)) add Emp)
    \<and> Eq (Geos (Ang (An A3 B3 C3)) add Emp) (Geos (Ang (An A31 B3 C31)) add Emp)
    \<and> Eq (Geos (Seg (Se B1 A1)) add Emp) (Geos (Seg (Se B3 A31)) add Emp)
    \<and> Line_on (Li B3 A3) A31 \<and> \<not> Bet_Point (Se A31 A3) B3
    \<and> Eq (Geos (Seg (Se B1 C1)) add Emp) (Geos (Seg (Se B3 C31)) add Emp)
    \<and> Line_on (Li B3 C3) C31 \<and> \<not> Bet_Point (Se C31 C3) B3 \<and> Def (Ang (An A31 B3 C31))" by blast
  from assms have P5 : "Def (Tri (Tr B1 A1 C1))" by (blast intro:Tri_def_rev Tri_def_trans Ang_to_Tri)
  from P2 have P6 : "Def (Tri (Tr B2 A21 C21))" by (blast intro:Tri_def_rev Tri_def_trans Ang_to_Tri)
  from P2 P5 P6 have "Cong (Geos (Tri (Tr B1 A1 C1)) add Emp) (Geos (Tri (Tr B2 A21 C21)) add Emp)" by (simp add:Tri_SAS)
  then have P7 : "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A21 C21)) add Emp)" by (simp add:Tri_Cong_def)
  from P4 have P8 : "Def (Tri (Tr B3 A31 C31))" by (blast intro:Tri_def_rev Tri_def_trans Ang_to_Tri)
  from P4 P5 P8 have "Cong (Geos (Tri (Tr B1 A1 C1)) add Emp) (Geos (Tri (Tr B3 A31 C31)) add Emp)" by (simp add:Tri_SAS)
  then have P9 : "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A31 C31)) add Emp)" by (simp add:Tri_Cong_def)
  from P6 have P10 : "Def (Tri (Tr A21 C21 B2))" by (blast intro:Tri_def_trans)
  from P8 have P11 : "Def (Tri (Tr A31 C31 B3))" by (blast intro:Tri_def_trans)
  from P7 P9 have P12 : "Eq (Geos (Seg (Se A21 C21)) add Emp) (Geos (Seg (Se A31 C31)) add Emp)" by (blast intro:Eq_trans)
  from P2 P4 have P13 : "Eq (Geos (Seg (Se B2 A21)) add Emp) (Geos (Seg (Se B3 A31)) add Emp)" by (blast intro:Eq_trans)
  from P2 P4 have P14 : "Eq (Geos (Seg (Se B2 C21)) add Emp) (Geos (Seg (Se B3 C31)) add Emp)" by (blast intro:Eq_trans)
  have P15 : "Eq (Geos (Seg (Se B2 C21)) add Emp) (Geos (Seg (Se C21 B2)) add Emp)" by (simp add:Seg_rev)
  have P16 : "Eq (Geos (Seg (Se B3 C31)) add Emp) (Geos (Seg (Se C31 B3)) add Emp)" by (simp add:Seg_rev)
  from P14 P15 P16 have P17 : "Eq (Geos (Seg (Se C21 B2)) add Emp) (Geos (Seg (Se C31 B3)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P10 P11 P12 P13 P17 have "Cong (Geos (Tri (Tr A21 C21 B2)) add Emp) (Geos (Tri (Tr A31 C31 B3)) add Emp)" by (simp add:Tri_SSS)
  then have P18 : "Cong (Geos (Ang (An A21 B2 C21)) add Emp) (Geos (Ang (An A31 B3 C31)) add Emp)" by (simp add:Tri_Cong_def)
  from P2 P18 have P19 : "Cong (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An A31 B3 C31)) add Emp)" by (blast intro:Ang_weektrans Ang_rev)
  from P4 P19 show "Cong (Geos (Ang (An A2 B2 C2)) add Emp) (Geos (Ang (An A3 B3 C3)) add Emp)" by (blast intro:Ang_weektrans Ang_rev)
qed

lemma (in Congruence_Rule) Ang_move_unique_inv : 
  assumes
    "Def (Ang (An p1 p2 p3))" "Def (Ang (An p4 p2 p3))"
    "Plane_sameside (Li p2 p3) p1 p4"
    "Eq (Geos (Lin (Li p2 p1)) add Emp) (Geos (Lin (Li p2 p4)) add Emp)"
  shows 
    "Cong (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp)"
proof -
  have P1 : "Line_on (Li p2 p4) p4" by (simp add:Line_on_rule)
  from assms P1 have P2 : "Line_on (Li p2 p1) p4" by (blast intro:Line_on_trans Eq_rev)
  have P3 : "Line_on (Li p2 p3) p2" by (simp add:Line_on_rule)
  from assms have P4 : "\<not> Line_on (Li p2 p3) p1" by (simp add:Plane_sameside_def)
  from assms have P5 : "\<not> Line_on (Li p2 p3) p4" by (simp add:Plane_sameside_def)
  from P3 P4 P5 have "Bet_Point (Se p1 p4) p2 \<Longrightarrow> \<exists>p. Bet_Point (Se p1 p4) p \<and> Line_on (Li p2 p3) p \<and> 
    \<not> Line_on (Li p2 p3) p1 \<and> \<not> Line_on (Li p2 p3) p4" by blast
  then have "Bet_Point (Se p1 p4) p2 \<Longrightarrow> Plane_diffside (Li p2 p3) p1 p4" by (simp add:Plane_diffside_def)
  then have P6 : "Bet_Point (Se p1 p4) p2 \<Longrightarrow> \<not> Plane_sameside (Li p2 p3) p1 p4" by (simp add:Plane_diffside_not_sameside)
  from assms P6 have P7 : "\<not> Bet_Point (Se p1 p4) p2" by blast
  have P8 : "Line_on (Li p2 p3) p3" by (simp add:Line_on_rule)
  have P9 : "\<not> Bet_Point (Se p3 p3) p2" by (simp add:Bet_end_Point)
  from assms have "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Ang_def)
  then have P10 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp)" by (blast intro:Eq_rev)
  from assms have P11 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Ang_def)
  from assms P2 P7 P8 P9 P10 P11 have "Eq (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp)
    \<and> Def (Ang (An p4 p2 p3))" by (simp add:Ang_Point_swap)
  thus "Cong (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp)" by (blast intro:Ang_weektrans)
qed

text\<open>Theorem20\<close>

theorem (in Congruence_Rule) Ang_move_Greater : 
  assumes
    "Def (Ang (An h1 o1 k1))" "Def (Ang (An h2 o2 l2))"
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Plane_sameside (Li o2 h2) k2 l2"
    "Cong (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)"
    "Plane_sameside (Li o1 h1) k1 l1"
    "Ang_inside (An h2 o2 l2) k2"
  shows 
    "\<not> Ang_inside (An h1 o1 k1) l1"
    "\<not> Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)"
proof - 
  from assms have P1 : "\<not> Line_on (Li o2 h2) k2" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi o2) add Emp)" by (simp add:Ang_def)
  then have P2 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi h2) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 have "Def (Ang (An o2 h2 k2))" by (simp add:Ang_sinple_def)
  then have P3 : "Def (Ang (An h2 o2 k2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P3 have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> \<exists>p. Ang_inside (An h2 o2 k2) p
    \<and> Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 p)) add Emp)
    \<and> Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 p)) add Emp)" by (simp add:Ang_split)
  then obtain l21 :: Point where P4 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Ang_inside (An h2 o2 k2) l21
    \<and> Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l21)) add Emp)
    \<and> Cong (Geos (Ang (An k1 o1 l1)) add Emp) (Geos (Ang (An k2 o2 l21)) add Emp)" by blast
  then have P5 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Plane_sameside (Li o2 k2) h2 l21 \<and> Plane_sameside (Li o2 h2) k2 l21" by (simp add:Ang_inside_def)
  from assms have P6 : "Plane_diffside (Li o2 k2) h2 l2" by (simp add:Ang_inside_Planeside)
  from P5 P6 have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow>
    Plane_diffside (Li o2 k2) l21 l2" by (blast intro:Plane_trans)
  then have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> \<exists>p. Bet_Point (Se l21 l2) p \<and> Line_on (Li o2 k2) p 
    \<and> \<not> Line_on (Li o2 k2) l21 \<and> \<not> Line_on (Li o2 k2) l2" by (simp add:Plane_diffside_def)
  then obtain pn :: Point where P7 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Bet_Point (Se l21 l2) pn \<and> Line_on (Li o2 k2) pn
    \<and> \<not> Line_on (Li o2 k2) l21 \<and> \<not> Line_on (Li o2 k2) l2" by blast
  then have P8 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Bet_Point (Se l21 l2) pn" by simp
  then have P9 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    \<not> Eq (Geos (Poi l21) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Bet_Point_def)
  from assms have P10 : "Plane_sameside (Li o2 h2) l2 k2" by (simp add:Plane_sameside_rev)
  from P5 P9 P10 have P11 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Plane_sameside (Li o2 h2) l2 l21" by (blast intro:Plane_sameside_trans)
  from P8 have P12 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Poi pn) add Emp) (Geos (Poi o2) add Emp) \<Longrightarrow> Bet_Point (Se l21 l2) o2" by (simp add:Point_Eq)
  have P13 : "Line_on (Li o2 h2) o2" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li l21 l2) l2" by (simp add:Line_on_rule)
  from P14 have P15 : "Eq (Geos (Lin (Li l21 l2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp) \<Longrightarrow> 
    Line_on (Li o2 h2) l2" by (simp add:Line_on_trans)
  from assms have "Def (Tri (Tr o2 h2 l2))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P16 : "\<not> Line_on (Li o2 h2) l2" by (simp add:Tri_def_Line)
  from P15 P16 have P17 : "\<not> Eq (Geos (Lin (Li l21 l2)) add Emp) (Geos (Lin (Li o2 h2)) add Emp)" by blast
  from P12 P13 P17 have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Poi pn) add Emp) (Geos (Poi o2) add Emp) \<Longrightarrow> 
    Plane_diffside (Li o2 h2) l2 l21" by (simp add:Plane_Bet_diffside Plane_diffside_rev)
  then have P18 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Poi pn) add Emp) (Geos (Poi o2) add Emp) \<Longrightarrow> 
    \<not> Plane_sameside (Li o2 h2) l2 l21" by (simp add:Plane_diffside_not_sameside)
  from P11 P18 have P19 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    \<not> Eq (Geos (Poi pn) add Emp) (Geos (Poi o2) add Emp)" by blast
  have P20 : "Line_on (Li o2 k2) o2" by (simp add:Line_on_rule)
  from P8 have P21 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Line_on (Li l21 l2) pn" by (simp add:Line_Bet_on)
  from P7 P19 P20 P21 have P22 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Line_on (Li l21 l2) o2 \<Longrightarrow>
    Eq (Geos (Lin (Li l21 l2)) add Emp) (Geos (Lin (Li o2 k2)) add Emp)" by (simp add:Line_unique)
  from P14 P22 have P23 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Line_on (Li l21 l2) o2 \<Longrightarrow> Line_on (Li o2 k2) l2" by (simp add:Line_on_trans)
  from P7 P23 have P24 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> \<not> Line_on (Li l21 l2) o2" by blast
  from P9 P24 have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Def (Ang (An l21 l2 o2))" by (simp add:Ang_sinple_def)
  then have P25 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Def (Ang (An l21 o2 l2))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P26 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    \<not> Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)" by (simp add:Ang_def)
  have P27 : "Eq (Geos (Ang (An h2 o2 l21)) add Emp) (Geos (Ang (An l21 o2 h2)) add Emp)" by (simp add:Ang_roll)
  from P4 P27 have P28 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An l21 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P29 : "Eq (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (simp add:Ang_roll)
  from assms P29 have P30 : "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P11 P28 P30 have P31 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Lin (Li l2 o2)) add Emp) (Geos (Lin (Li l21 o2)) add Emp)" by (simp add:Ang_move_unique)
  from P25 have P32 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> Def (Tri (Tr l21 o2 l2))" by (simp add:Ang_to_Tri)
  then have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> \<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Tri_def)
  then have P33 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp)" by (simp add:Line_rev)
  from P32 have "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    \<not> Eq (Geos (Poi l21) add Emp) (Geos (Poi o2) add Emp)" by (simp add:Tri_def)
  then have P34 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Lin (Li l21 o2)) add Emp) (Geos (Lin (Li o2 l21)) add Emp)" by (simp add:Line_rev)
  from P31 P33 have P35 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li l21 o2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P34 P35 have P36 : "Ang_inside (An h1 o1 k1) l1 \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 l21)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P26 P36 show "\<not> Ang_inside (An h1 o1 k1) l1" by blast
  from assms have P37 : "Def (Ang (An k1 o1 h1))" by (blast intro:Ang_def_rev)
  from assms have P38 : "\<not> Line_on (Li o1 h1) l1" by (simp add:Plane_sameside_def)
  from P37 have P39 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp)" by (simp add:Ang_def)
  from P38 P39 have "Def (Ang (An o1 h1 l1))" by (simp add:Ang_sinple_def)
  then have P40 : "Def (Ang (An l1 o1 h1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P37 P40 have P41 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An k1 o1 h1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by (simp add:Ang_move_unique_inv)
  have P42 : "Cong (Geos (Ang (An k1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (simp add:Ang_roll)
  from assms P37 P40 P41 P42 have P43 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  have P44 : "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)" by (simp add:Ang_roll)
  from P40 have P45 : "Def (Ang (An h1 o1 l1))" by (blast intro:Ang_def_rev)
  from assms P40 P43 P44 P45 have P46 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from assms P45 P46 have P47 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from assms P3 P47 have P48 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P29 P48 have P49 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P50 : "Cong (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An k2 o2 h2)) add Emp)" by (simp add:Ang_roll)
  from assms P49 P50 have P51 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li k2 o2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp)
    \<and> \<not> Bet_Point (Se k2 l2) o2" by (simp add:Ang_move_unique)
  from assms have "Def (Ang (An h2 o2 l2)) \<and> Plane_sameside (Li o2 h2) l2 k2
    \<and> Plane_sameside (Li o2 l2) h2 k2" by (simp add:Ang_inside_def)
  then have P52 : "\<not> Line_on (Li o2 l2) k2" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Ang_def)
  then have P53 : "Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp)" by (simp add:Line_rev)
  from P51 P53 have P54 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li k2 o2)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)" by (blast intro:Eq_trans)
  have P55 : "Line_on (Li k2 o2) k2" by (simp add:Line_on_rule)
  from P54 P55 have P56 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Line_on (Li o2 l2) k2" by (simp add:Line_on_trans)
  from P52 P56 show "\<not> Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
qed

theorem (in Congruence_Rule) Ang_move_Smaller : 
  assumes 
    "Def (Ang (An h1 o1 k1))" "Def (Ang (An h2 o2 l2))"
    "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 k2)) add Emp)"
    "Plane_sameside (Li o2 h2) k2 l2"
    "Cong (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)"
    "Plane_sameside (Li o1 h1) k1 l1"
    "\<not> Ang_inside (An h2 o2 l2) k2"
    "\<not> Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)"
  shows "Ang_inside (An h1 o1 k1) l1"
proof -
  have P1 : "Ang_inside (An l2 o2 h2) k2 \<Longrightarrow> Ang_inside (An h2 o2 l2) k2" by (simp add:Ang_inside_def Ang_def_rev)
  from assms P1 have P2 : "\<not> Ang_inside (An l2 o2 h2) k2" by blast
  from assms have P3 : "\<not> Line_on (Li o2 h2) k2" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi h2) add Emp) (Geos (Poi o2) add Emp)" by (simp add:Ang_def)
  then have P4 : "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi h2) add Emp)" by (blast intro:Eq_rev)
  from P3 P4 have "Def (Ang (An o2 h2 k2))" by (simp add:Ang_sinple_def)
  then have P5 : "Def (Ang (An k2 o2 h2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P6 : "Def (Ang (An l2 o2 h2))" by (blast intro:Ang_def_rev)
  from assms P5 P6 have P7 : "Ang_inside (An k2 o2 h2) l2 \<and> \<not> Ang_inside (An l2 o2 h2) k2
    \<or> \<not> Ang_inside (An k2 o2 h2) l2 \<and> Ang_inside (An l2 o2 h2) k2" by (simp add:Ang_inside_case)
  from P2 P7 have "Ang_inside (An k2 o2 h2) l2" by blast
  then have P8 : "Ang_inside (An h2 o2 k2) l2" by (simp add:Ang_inside_def Ang_def_rev)
  from assms have P9 : "\<not> Line_on (Li o1 h1) l1" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi h1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Ang_def)
  then have P10 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp)" by (blast intro:Eq_rev)
  from P9 P10 have "Def (Ang (An o1 h1 l1))" by (simp add:Ang_sinple_def)
  then have P11 : "Def (Ang (An h1 o1 l1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P5 have P12 : "Def (Ang (An h2 o2 k2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P13 : "Cong (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_rev)
  from assms have P14 : "Plane_sameside (Li o2 h2) l2 k2" by (simp add:Plane_sameside_rev)
  from assms have P15 : "Cong (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (blast intro:Ang_rev)
  from assms have P16 : "Plane_sameside (Li o1 h1) l1 k1" by (simp add:Plane_sameside_rev)
  from P8 P11 P12 P13 P14 P15 P16 have P17 : "\<not> Ang_inside (An h1 o1 l1) k1" by (simp add:Ang_move_Greater)
  have P18 : "Ang_inside (An l1 o1 h1) k1 \<Longrightarrow> Ang_inside (An h1 o1 l1) k1" by (simp add:Ang_inside_def Ang_def_rev)
  from P17 P18 have P19 : "\<not> Ang_inside (An l1 o1 h1) k1" by blast
  from assms have P20 : "Def (Ang (An k1 o1 h1))" by (blast intro:Ang_def_rev)
  from P11 have P21 : "Def (Ang (An l1 o1 h1))" by (blast intro:Ang_def_rev)
  have "Line_on (Li o1 k1) k1" by (simp add:Line_on_rule)
  then have P22 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Line_on (Li o1 l1) k1" by (simp add:Line_on_trans)
  have P23 : "Line_on (Li o1 h1) o1" by (simp add:Line_on_rule)
  have "Line_on (Li l1 k1) l1" by (simp add:Line_on_rule)
  then have P24 : "Eq (Geos (Lin (Li l1 k1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp) \<Longrightarrow> Line_on (Li o1 h1) l1" by (simp add:Line_on_trans)
  from P9 P24 have P25 : "\<not> Eq (Geos (Lin (Li l1 k1)) add Emp) (Geos (Lin (Li o1 h1)) add Emp)" by blast
  from P23 P25 have "Bet_Point (Se l1 k1) o1 \<Longrightarrow> Plane_diffside (Li o1 h1) l1 k1" by (simp add:Plane_Bet_diffside)
  then have P26 : "Bet_Point (Se l1 k1) o1 \<Longrightarrow> \<not> Plane_sameside (Li o1 h1) l1 k1" by (simp add:Plane_diffside_not_sameside)
  from P16 P26 have P27 : "\<not> Bet_Point (Se l1 k1) o1" by blast
  have P28 : "Line_on (Li o1 h1) h1" by (simp add:Line_on_rule)
  have P29 : "\<not> Bet_Point (Se h1 h1) o1" by (simp add:Bet_end_Point)
  from assms have P30 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp)" by (simp add:Ang_def)
  from P10 P21 P22 P27 P28 P29 P30 have P31 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An k1 o1 h1)) add Emp) \<and> Def (Ang (An k1 o1 h1))" by (simp add:Ang_Point_swap)
  have P32 : "Eq (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 l1)) add Emp)" by (simp add:Ang_roll)
  from P31 P32 have P33 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An k1 o1 h1)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  have P34 : "Eq (Geos (Ang (An k1 o1 h1)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (simp add:Ang_roll)
  from P33 P34 have P35 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Ang (An h1 o1 l1)) add Emp) (Geos (Ang (An h1 o1 k1)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P35 have P36 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P37 : "Eq (Geos (Ang (An h2 o2 k2)) add Emp) (Geos (Ang (An k2 o2 h2)) add Emp)" by (simp add:Ang_roll)
  from assms P37 have P38 : "Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An k2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P39 : "Eq (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (simp add:Ang_roll)
  from P36 P39 have P40 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Cong (Geos (Ang (An h1 o1 k1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms P38 P40 have P41 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li k2 o2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp) \<and> \<not> Bet_Point (Se k2 l2) o2" by (simp add:Ang_move_unique)
  from P12 have "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi k2) add Emp)" by (simp add:Ang_def)
  then have P42 : "Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li k2 o2)) add Emp)" by (simp add:Line_rev)
  from P41 P42 have P43 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from assms have "\<not> Eq (Geos (Poi o2) add Emp) (Geos (Poi l2) add Emp)" by (simp add:Ang_def)
  then have P44 : "Eq (Geos (Lin (Li o2 l2)) add Emp) (Geos (Lin (Li l2 o2)) add Emp)" by (simp add:Line_rev)
  from P43 P44 have P45 : "Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li o2 k2)) add Emp) (Geos (Lin (Li o2 l2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from assms P45 have P46 : "\<not> Eq (Geos (Lin (Li o1 k1)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
  from assms P20 P21 P46 have P47 : "Ang_inside (An k1 o1 h1) l1 \<and> \<not> Ang_inside (An l1 o1 h1) k1
    \<or> \<not> Ang_inside (An k1 o1 h1) l1 \<and> Ang_inside (An l1 o1 h1) k1" by (simp add:Ang_inside_case)
  from P19 P47 have "Ang_inside (An k1 o1 h1) l1" by blast
  thus "Ang_inside (An h1 o1 k1) l1" by (simp add:Ang_inside_def Ang_def_rev)
qed

lemma (in Congruence_Rule) Ang_not_Gr_Eq_rev : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
    "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
  shows 
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
proof -
  from assms have "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  then have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" using assms by (simp add:Ang_move_sameside)
  then obtain p4 :: Point where P1 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p4 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p4 p11" by blast
  from assms P1 have P2 : "\<not> Ang_inside (An p11 p12 p13) p4 \<and> \<not> Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (blast intro:Ang_less_def)
  from assms P2 have P3 : "Ang_inside (An p11 p12 p13) p4 \<or> Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp)" by blast
  from P1 have P4 : "Plane_sameside (Li p12 p13) p11 p4" by (simp add:Plane_sameside_rev)
  then have P5 : "\<not> Line_on (Li p12 p13) p4" by (simp add:Plane_sameside_def)
  from assms have P6 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P5 P6 have "Def (Ang (An p12 p13 p4))" by (simp add:Ang_sinple_def)
  then have P7 : "Def (Ang (An p4 p12 p13))" by (blast intro:Ang_def_inv Ang_def_rev)
  from assms P4 P7 have P8 : "Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p4 p12 p13)) add Emp)" by (simp add:Ang_move_unique_inv)
  from assms P1 P7 P8 have P9 : "Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (blast intro:Ang_trans Ang_rev) 
  from P1 have P10 : "Ang_inside (An p11 p12 p13) p4 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  from P3 P9 P10 show "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_not_Eq_Gr : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
    "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
  shows 
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
proof -
  from assms have "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  then have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" using assms by (simp add:Ang_move_sameside)
  then obtain p4 :: Point where P1 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p4 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p4 p11" by blast
  from P1 have P2 : "Plane_sameside (Li p12 p13) p11 p4" by (simp add:Plane_sameside_rev)
  then have P3 : "\<not> Line_on (Li p12 p13) p4" by (simp add:Plane_sameside_def)
  from assms have P4 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P3 P4 have "Def (Ang (An p12 p13 p4))" by (simp add:Ang_sinple_def)
  then have P5 : "Def (Ang (An p4 p12 p13))" by (blast intro:Ang_def_inv Ang_def_rev)
  from assms P2 P5 have P6 : "Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p4 p12 p13)) add Emp)" by (simp add:Ang_move_unique_inv)
  from assms P1 P5 P6 have P7 : "Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (blast intro:Ang_trans Ang_rev) 
  from assms P7 have P8 : "\<not> Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p4)) add Emp)" by blast
  from assms P2 P5 P8 have P9 : "Ang_inside (An p11 p12 p13) p4 \<and> \<not> Ang_inside (An p4 p12 p13) p11
    \<or> \<not> Ang_inside (An p11 p12 p13) p4 \<and> Ang_inside (An p4 p12 p13) p11" by (simp add:Ang_inside_case)
  from P1 have P10 : "Ang_inside (An p11 p12 p13) p4 \<longleftrightarrow>
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  from P1 P8 have P11 : "\<not> Ang_inside (An p11 p12 p13) p4 \<Longrightarrow>
    Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (blast intro:Ang_less_def)
  from P9 P10 P11 show "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_relation_case : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
  shows 
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
proof -
  from assms have P1 : "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_not_Eq_Gr)
  then have P2 : "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by blast
  from P1 have P3 : "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
  from assms have "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_not_Gr_Eq_rev)
  then have P4 : "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp) \<Longrightarrow>
    \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
  from P2 P3 P4 show "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_not_Gr_lemma1 : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
  shows 
    "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
proof -
  from assms have "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  then have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" using assms by (simp add:Ang_move_sameside)
  then obtain p14 :: Point where P1 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p14 p11" by blast
  from P1 have P2 : "Plane_sameside (Li p12 p13) p11 p14" by (simp add:Plane_sameside_rev)
  then have P3 : "\<not> Line_on (Li p12 p13) p14" by (simp add:Plane_sameside_def)
  from assms have P4 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P3 P4 have "Def (Ang (An p12 p13 p14))" by (simp add:Ang_sinple_def)
  then have P5 : "Def (Ang (An p14 p12 p13))" by (blast intro:Ang_def_inv Ang_def_rev)
  from assms P1 P5 have P6 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  have P7 : "Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_roll)
  from assms have P8 : "Def (Ang (An p13 p12 p11))" by (simp add:Ang_def_rev)
  from assms P5 P6 P7 P8 have P9 : "Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P2 P7 P9 have P10 : "Eq (Geos (Lin (Li p11 p12)) add Emp) (Geos (Lin (Li p14 p12)) add Emp) \<and> \<not> Bet_Point (Se p11 p14) p12" by (simp add:Ang_move_unique)
  from P1 have "Ang_inside (An p11 p12 p13) p14 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  then have "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Ang_inside (An p11 p12 p13) p14" by blast
  then have "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Plane_sameside (Li p12 p11) p13 p14" by (simp add:Ang_inside_def)
  then have P11 : "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    \<not> Line_on (Li p12 p11) p14" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p12) add Emp)" by (simp add:Ang_def)
  then have P12 : "Eq (Geos (Lin (Li p11 p12)) add Emp) (Geos (Lin (Li p12 p11)) add Emp)" by (simp add:Line_rev)
  from P10 P12 have P13 : "Eq (Geos (Lin (Li p14 p12)) add Emp) (Geos (Lin (Li p12 p11)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  have P14 : "Line_on (Li p14 p12) p14" by (simp add:Line_on_rule)
  from P13 P14 have P15 : "Line_on (Li p12 p11) p14" by (simp add:Line_on_trans)
  from P11 P15 show "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_not_Gr : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
  shows 
    "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
    "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
proof -
  from assms show P1 : "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_not_Gr_lemma1)
  from assms have P2 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_rev)
  from assms P2 show "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_not_Gr_lemma1)
qed

lemma (in Congruence_Rule) Ang_Gr_not_Eq_rev : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
    "Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
  shows 
    "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
    "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
proof -
  from assms have "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  then have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" using assms by (simp add:Ang_move_sameside)
  then obtain p14 :: Point where P1 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p14 p11" by blast
  from P1 have P2 : "Plane_sameside (Li p12 p13) p11 p14" by (simp add:Plane_sameside_rev)
  then have P3 : "\<not> Line_on (Li p12 p13) p14" by (simp add:Plane_sameside_def)
  from assms have P4 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P3 P4 have "Def (Ang (An p12 p13 p14))" by (simp add:Ang_sinple_def)
  then have P5 : "Def (Ang (An p14 p12 p13))" by (blast intro:Ang_def_inv Ang_def_rev)
  from assms have "\<not> Line_on (Li p22 p23) p21" by (simp add:Ang_to_Tri Tri_def_Line)
  then have "\<exists>p. Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p p22 p23)) add Emp)
    \<and> Plane_sameside (Li p22 p23) p p21" using assms by (simp add:Ang_move_sameside)
  then obtain p24 :: Point where P6 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p24 p22 p23)) add Emp)
    \<and> Plane_sameside (Li p22 p23) p24 p21" by blast
  then have P7 : "\<not> Line_on (Li p22 p23) p24" by (simp add:Plane_sameside_def)
  from assms have P8 : "\<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p23) add Emp)" by (simp add:Ang_def)
  from P7 P8 have "Def (Ang (An p22 p23 p24))" by (simp add:Ang_sinple_def)
  then have P9 : "Def (Ang (An p24 p22 p23))" by (blast intro:Ang_def_inv Ang_def_rev)
  from P6 have P10 : "Plane_sameside (Li p22 p23) p21 p24" by (simp add:Plane_sameside_rev)
  from assms have P11 : "Def (Ang (An p13 p12 p11))" by (simp add:Ang_def_rev)
  from assms have P12 : "Def (Ang (An p23 p22 p21))" by (simp add:Ang_def_rev)
  from P5 have P13 : "Def (Ang (An p13 p12 p14))" by (simp add:Ang_def_rev)
  from P9 have P14 : "Def (Ang (An p23 p22 p24))" by (simp add:Ang_def_rev)
  have P15 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p13 p12 p11)) add Emp)" by (simp add:Ang_roll)
  have P16 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p23 p22 p21)) add Emp)" by (simp add:Ang_roll)
  have P17 : "Cong (Geos (Ang (An p14 p12 p13)) add Emp) (Geos (Ang (An p13 p12 p14)) add Emp)" by (simp add:Ang_roll)
  have P18 : "Cong (Geos (Ang (An p24 p22 p23)) add Emp) (Geos (Ang (An p23 p22 p24)) add Emp)" by (simp add:Ang_roll)
  from assms P6 P9 P11 P15 have P19 : 
    "Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p24 p22 p23)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P9 P11 P14 P18 P19 have P20 : 
    "Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p23 p22 p24)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from assms P1 P5 P12 P16 have P21 : 
    "Cong (Geos (Ang (An p23 p22 p21)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P5 P12 P13 P17 P21 have P22 : 
    "Cong (Geos (Ang (An p23 p22 p21)) add Emp) (Geos (Ang (An p13 p12 p14)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P6 have P23 : "Ang_inside (An p21 p22 p23) p24 \<longleftrightarrow> 
    Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_greater_def)
  from assms P23 have P24 : "Ang_inside (An p21 p22 p23) p24" by blast
  from P12 P24 have P25 : "Ang_inside (An p23 p22 p21) p24" by (simp add:Ang_inside_def)
  from P2 P6 P11 P12 P20 P22 P25 have P26 : "\<not> Ang_inside (An p13 p12 p11) p14 
    \<and> \<not> Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p14)) add Emp)" by (simp add:Ang_move_Greater)
  from P1 have "Ang_inside (An p11 p12 p13) p14 \<longleftrightarrow>
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  then have P27 : "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Ang_inside (An p11 p12 p13) p14" by blast
  from P11 P27 have P28 : "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Ang_inside (An p13 p12 p11) p14" by (simp add:Ang_inside_def)
  from P26 P28 show "\<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
  from assms P1 P5 have P29 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  have P30 : "Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_roll)
  from assms P5 P11 P29 P30 have P31 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p13 p12 p11)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P2 P30 P31 have P32 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li p11 p12)) add Emp) (Geos (Lin (Li p14 p12)) add Emp) \<and> \<not> Bet_Point (Se p11 p14) p12" by (simp add:Ang_move_unique)
  from assms have "\<not> Eq (Geos (Poi p11) add Emp) (Geos (Poi p12) add Emp)" by (simp add:Ang_def)
  then have P33 : "Eq (Geos (Lin (Li p11 p12)) add Emp) (Geos (Lin (Li p12 p11)) add Emp)" by (simp add:Line_rev)
  from P32 P33 have P34 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p14 p12)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P5 have "\<not> Eq (Geos (Poi p14) add Emp) (Geos (Poi p12) add Emp)" by (simp add:Ang_def)
  then have P35 : "Eq (Geos (Lin (Li p14 p12)) add Emp) (Geos (Lin (Li p12 p14)) add Emp)" by (simp add:Line_rev)
  from P34 P35 have P36 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li p12 p11)) add Emp) (Geos (Lin (Li p12 p14)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P26 P36 show "\<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_relation_case_fact : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))"
  shows 
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)"
proof -
  from assms have P1 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<or> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_relation_case)
  from assms have P2 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) ==>
    \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_not_Gr)
  from assms have P3 : "Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp) \<Longrightarrow>
    \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_Gr_not_Eq_rev)
  from assms have "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    \<not> Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_Gr_not_Eq_rev)
  then have P4 : "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp) \<Longrightarrow>
    \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (blast intro:Ang_rev)
  from P1 P2 P3 P4 show "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)
    \<and> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_Gr_trans_Eq_Gr : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))" "Def (Ang (An p31 p32 p33))"
    "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
    "Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
  shows 
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
proof -
  from assms have P1 : "\<not> Line_on (Li p22 p23) p21" by (simp add:Ang_to_Tri Tri_def_Line)
  from assms P1 have "\<exists>p. Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p p22 p23)) add Emp)
    \<and> Plane_sameside (Li p22 p23) p p21" by (simp add:Ang_move_sameside)
  then obtain p24 :: Point where P2 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p24 p22 p23)) add Emp)
    \<and> Plane_sameside (Li p22 p23) p24 p21" by blast
  then have P3 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p24 p22 p23)) add Emp)" by simp
  from P2 have P4 : "Plane_sameside (Li p22 p23) p24 p21" by simp
  from assms P3 P4 have "Ang_inside (An p21 p22 p23) p24" by (simp add:Ang_greater_def)
  then have P5 : "Ang_inside (An p23 p22 p21) p24" by (simp add:Ang_inside_def Ang_def_rev)
  from assms have P6 : "\<not> Line_on (Li p32 p33) p31" by (simp add:Ang_to_Tri Tri_def_Line)
  from assms P6 have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p32 p33)) add Emp)
    \<and> Plane_sameside (Li p32 p33) p p31" by (simp add:Ang_move_sameside)
  then obtain p34 :: Point where P7 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p34 p32 p33)) add Emp)
    \<and> Plane_sameside (Li p32 p33) p34 p31" by blast
  then have P8 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p34 p32 p33)) add Emp)" by simp
  from P7 have P9 : "Plane_sameside (Li p32 p33) p34 p31" by simp
  from assms have P10 : "Def (Ang (An p33 p32 p31))" by (blast intro:Ang_def_rev)
  from assms have P11 : "Def (Ang (An p23 p22 p21))" by (blast intro:Ang_def_rev)
  from P4 have P12 : "\<not> Line_on (Li p22 p23) p24" by (simp add:Plane_sameside_def)
  from assms have P13 : "\<not> Eq (Geos (Poi p22) add Emp) (Geos (Poi p23) add Emp)" by (simp add:Ang_def)
  from P12 P13 have "Def (Ang (An p22 p23 p24))" by (simp add:Ang_sinple_def)
  then have P14 : "Def (Ang (An p24 p22 p23))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P15 : "Def (Ang (An p23 p22 p24))" by (blast intro:Ang_def_rev)
  have P16 : "Cong (Geos (Ang (An p24 p22 p23)) add Emp) (Geos (Ang (An p23 p22 p24)) add Emp)" by (simp add:Ang_roll)
  from assms P3 P14 P15 P16 have P17 : 
    "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p23 p22 p24)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  have P18 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p33 p32 p31)) add Emp)" by (simp add:Ang_roll)
  from assms P10 P15 P17 P18 have P19 : 
    "Cong (Geos (Ang (An p33 p32 p31)) add Emp) (Geos (Ang (An p23 p22 p24)) add Emp)"  by (blast intro:Ang_trans Ang_rev)
  from P9 have P20 : "\<not> Line_on (Li p32 p33) p34" by (simp add:Plane_sameside_def)
  from assms have P21 : "\<not> Eq (Geos (Poi p32) add Emp) (Geos (Poi p33) add Emp)" by (simp add:Ang_def)
  from P20 P21 have "Def (Ang (An p32 p33 p34))" by (simp add:Ang_sinple_def)
  then have P22 : "Def (Ang (An p34 p32 p33))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P23 : "Def (Ang (An p33 p32 p34))" by (blast intro:Ang_def_rev)
  have P24 : "Cong (Geos (Ang (An p34 p32 p33)) add Emp) (Geos (Ang (An p33 p32 p34)) add Emp)" by (simp add:Ang_roll)
  from assms P8 P22 P23 P24 have P25 : 
    "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p33 p32 p34)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  have P26 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p23 p22 p21)) add Emp)" by (simp add:Ang_roll)
  from assms P11 P23 P25 P26 have P27 : 
    "Cong (Geos (Ang (An p23 p22 p21)) add Emp) (Geos (Ang (An p33 p32 p34)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P9 have P28 : "Plane_sameside (Li p32 p33) p31 p34" by (simp add:Plane_sameside_rev)
  from P4 P5 P10 P11 P19 P27 P28 have P29 : "\<not> Ang_inside (An p33 p32 p31) p34
    \<and> \<not> Eq (Geos (Lin (Li p32 p31)) add Emp) (Geos (Lin (Li p32 p34)) add Emp)" by (simp add:Ang_move_Greater)
  have P30 : "Ang_inside (An p31 p32 p33) p34 \<Longrightarrow> Ang_inside (An p33 p32 p31) p34" by (simp add:Ang_inside_def Ang_def_rev)
  from P29 P30 have P31 : "\<not> Ang_inside (An p31 p32 p33) p34" by blast
  from assms P8 P22 have P32 : "Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p34 p32 p33)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P9 P29 P31 P32 show "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by (simp add:Ang_less_def)
qed

lemma (in Congruence_Rule) Ang_Gr_trans_Gr_Eq : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))" "Def (Ang (An p31 p32 p33))"
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
    "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
  shows 
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
proof -
  from assms have P1 : "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  from assms P1 have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" by (simp add:Ang_move_sameside)
  then obtain p14 :: Point where P2 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p14 p11" by blast
  then have P3 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by simp
  from P2 have P4 : "Plane_sameside (Li p12 p13) p14 p11" by simp
  from P3 P4 have P5 : "Ang_inside (An p11 p12 p13) p14 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  from assms P5 have P6 : "Ang_inside (An p11 p12 p13) p14" by simp
  from P4 have P7 : "\<not> Line_on (Li p12 p13) p14" by (simp add:Plane_sameside_def)
  from assms have P8 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P7 P8 have "Def (Ang (An p12 p13 p14))" by (simp add:Ang_sinple_def)
  then have P9 : "Def (Ang (An p14 p12 p13))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P3 P9 have P10 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P4 P10 have P11 : "Ang_inside (An p11 p12 p13) p14 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by (simp add:Ang_greater_def)
  from P6 P11 show "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by simp
qed

lemma (in Congruence_Rule) Ang_Eq_Point : 
  assumes 
    "Def (Ang (An p1 p2 p3))"
    "Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)"
  shows 
    "Eq (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp) \<and> Def (Ang (An p4 p2 p3))"
proof -
  have "Line_on (Li p2 p1) p1" by (simp add:Line_on_rule)
  then have P1 : "Line_on (Li p2 p1) p4" using assms by (simp add:Point_Eq)
  from assms have P2 : "Bet_Point (Se p1 p4) p2 \<Longrightarrow> Bet_Point (Se p4 p4) p2" by (simp add:Bet_Point_Eq)
  have P3 : "\<not> Bet_Point (Se p4 p4) p2" by (simp add:Bet_end_Point)
  from P2 P3 have P4 : "\<not> Bet_Point (Se p1 p4) p2" by blast
  have P5 : "Line_on (Li p2 p3) p3" by (simp add:Line_on_rule)
  have P6 : "\<not> Bet_Point (Se p3 p3) p2" by (simp add:Bet_end_Point)
  from assms have P7 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Ang_def)
  from assms have P8 : "Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp) \<Longrightarrow>
    Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P7 P8 have P9 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp)" by blast
  from assms have P10 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Ang_def)
  from assms P1 P4 P5 P6 P9 P10 show
    "Eq (Geos (Ang (An p1 p2 p3)) add Emp) (Geos (Ang (An p4 p2 p3)) add Emp) \<and> Def (Ang (An p4 p2 p3))" by (simp add:Ang_Point_swap)
qed

lemma (in Congruence_Rule) Planeside_wrong_relation : 
  assumes 
    "Plane_diffside (Li p1 p2) p3 p4"
    "Plane_diffside (Li p1 p3) p2 p4"
    "Plane_sameside (Li p1 p5) p3 p2"
    "Plane_sameside (Li p1 p5) p4 p2"
  shows False
proof -
  from assms have "\<exists>p. Bet_Point (Se p3 p4) p \<and> Line_on (Li p1 p2) p 
    \<and> \<not> Line_on (Li p1 p2) p3 \<and> \<not> Line_on (Li p1 p2) p4" by (simp add:Plane_diffside_def)
  then obtain p6 :: Point where P1 : "Bet_Point (Se p3 p4) p6 \<and> Line_on (Li p1 p2) p6
    \<and> \<not> Line_on (Li p1 p2) p3 \<and> \<not> Line_on (Li p1 p2) p4" by blast
  from assms have "\<exists>p. Bet_Point (Se p2 p4) p \<and> Line_on (Li p1 p3) p 
    \<and> \<not> Line_on (Li p1 p3) p2 \<and> \<not> Line_on (Li p1 p3) p4" by (simp add:Plane_diffside_def)
  then obtain p7 :: Point where P2 : "Bet_Point (Se p2 p4) p7 \<and> Line_on (Li p1 p3) p7
    \<and> \<not> Line_on (Li p1 p3) p2 \<and> \<not> Line_on (Li p1 p3) p4" by blast
  then have P3 : "Bet_Point (Se p2 p4) p7" by simp
  then have P4 : "Line_on (Li p2 p4) p7" by (blast intro:Line_Bet_on)
  from P3 have P5 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p7) add Emp)" by (simp add:Bet_Point_def)
  have P6 : "Line_on (Li p2 p4) p4" by (simp add:Line_on_rule)
  have P7 : "Line_on (Li p3 p4) p4" by (simp add:Line_on_rule)
  from P4 P5 P6 P7 have P8 : "Line_on (Li p3 p4) p7 \<Longrightarrow>
    Eq (Geos (Lin (Li p2 p4)) add Emp) (Geos (Lin (Li p3 p4)) add Emp)" by (simp add:Line_unique)
  have P9 : "Line_on (Li p2 p4) p2" by (simp add:Line_on_rule)
  from P8 P9 have P10 : "Line_on (Li p3 p4) p7 \<Longrightarrow> Line_on (Li p3 p4) p2" by (simp add:Line_on_trans)
  from P7 have P11 : "Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p1 p2)) add Emp) \<Longrightarrow>
    Line_on (Li p1 p2) p4" by (simp add:Line_on_trans)
  from P1 P11 have P12 : "\<not> Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by blast
  from P1 have P13 : "Bet_Point (Se p3 p4) p6" by simp
  then have P14 : "Line_on (Li p3 p4) p6" by (blast intro:Line_Bet_on)
  have P15 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from P1 P10 P12 P14 P15 have P16 : "Line_on (Li p3 p4) p7 \<Longrightarrow>
    Eq (Geos (Poi p6) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Line_unique_Point)
  from P13 P16 have P17 : "Line_on (Li p3 p4) p7 \<Longrightarrow> Bet_Point (Se p3 p4) p2" by (simp add:Point_Eq)
  from P7 have P18 : "Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p1 p3)) add Emp) \<Longrightarrow>
    Line_on (Li p1 p3) p4" by (simp add:Line_on_trans)
  from P2 P18 have P19 : "\<not> Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by blast
  have P20 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  from P17 P19 P20 have "Line_on (Li p3 p4) p7 \<Longrightarrow> Plane_sameside (Li p1 p3) p2 p4" by (simp add:Plane_Bet_sameside)
  then have "Line_on (Li p3 p4) p7 \<Longrightarrow> \<not> Plane_diffside (Li p1 p3) p2 p4" by (simp add:Plane_sameside_not_diffside)
  then have P21 : "\<not> Line_on (Li p3 p4) p7" using assms by blast
  from P3 have P22 : "\<not> Eq (Geos (Poi p7) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  from P4 P9 P15 P22 have P23 : "Line_on (Li p1 p2) p7 \<Longrightarrow>
    Eq (Geos (Lin (Li p2 p4)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  from P6 P23 have P24 : "Line_on (Li p1 p2) p7 \<Longrightarrow> Line_on (Li p1 p2) p4" by (simp add:Line_on_trans)
  from P1 P24 have P25 : "\<not> Line_on (Li p1 p2) p7" by blast
  from P1 P13 P21 P25 have P26 : "Line_on_Seg (Li p1 p2) (Se p3 p7) \<and> \<not> Line_on_Seg (Li p1 p2) (Se p4 p7)
        \<or> Line_on_Seg (Li p1 p2) (Se p4 p7) \<and> \<not> Line_on_Seg (Li p1 p2) (Se p3 p7)" by (simp add:Pachets_axiom)
  have "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> \<exists>p. Line_on (Li p1 p2) p \<and> Bet_Point (Se p4 p7) p" by (simp add:Line_on_Seg_rule)
  then obtain p8 :: Point where P27 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> 
    Line_on (Li p1 p2) p8 \<and> Bet_Point (Se p4 p7) p8" by blast
  then have P28 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> Line_on (Li p4 p7) p8" by (blast intro:Line_Bet_on)
  from P3 have P29 : "Line_on (Li p4 p7) p2" by (blast intro:Line_Bet_on)
  from P27 have "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> Bet_Point (Se p4 p7) p8" by simp
  then have P30 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> 
    Eq (Geos (Poi p8) add Emp) (Geos (Poi p2) add Emp) \<Longrightarrow> Bet_Point (Se p4 p7) p2" by (simp add:Point_Eq)
  from P3 have "Inv (Bet_Point (Se p4 p7) p2)" by (simp add:Bet_iff)
  then have P31 : "\<not> Bet_Point (Se p4 p7) p2" by (simp add:Inv_def)
  from P30 P31 have P32 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> 
    \<not> Eq (Geos (Poi p8) add Emp) (Geos (Poi p2) add Emp)" by blast
  from P15 P27 P28 P29 P32 have P33 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow>
    Eq (Geos (Lin (Li p4 p7)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  have P34 : "Line_on (Li p4 p7) p4" by (simp add:Line_on_rule)
  from P33 P34 have P35 : "Line_on_Seg (Li p1 p2) (Se p4 p7) \<Longrightarrow> Line_on (Li p1 p2) p4" by (simp add:Line_on_trans)
  from P1 P35 have P36 : "\<not> Line_on_Seg (Li p1 p2) (Se p4 p7)" by blast
  from P26 P36 have "Line_on_Seg (Li p1 p2) (Se p3 p7)" by blast
  then have "\<exists>p. Line_on (Li p1 p2) p \<and> Bet_Point (Se p3 p7) p" by (simp add:Line_on_Seg_rule)
  then obtain p8 :: Point where P37 : "Line_on (Li p1 p2) p8 \<and> Bet_Point (Se p3 p7) p8" by blast
  have "Line_on (Li p3 p4) p3" by (simp add:Line_on_rule)
  then have P38 : "Eq (Geos (Poi p3) add Emp) (Geos (Poi p7) add Emp) \<Longrightarrow> Line_on (Li p3 p4) p7" by (simp add:Point_Eq)
  from P21 P38 have P39 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p7) add Emp)" by blast
  have P40 : "Line_on (Li p3 p7) p3" by (simp add:Line_on_rule)
  have P41 : "Line_on (Li p3 p7) p7" by (simp add:Line_on_rule)
  from P2 have P42 : "Line_on (Li p1 p3) p7" by simp
  from P20 P39 P40 P41 P42 have P43 : 
    "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p3 p7)) add Emp)" by (simp add:Line_unique)
  have P44 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  from P43 P44 have P45 : "Line_on (Li p3 p7) p1" by (simp add:Line_on_trans)
  from P37 have P46 : "Line_on (Li p3 p7) p8" by (blast intro:Line_Bet_on)
  have P47 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  from P40 have P48 : "Eq (Geos (Lin (Li p3 p7)) add Emp) (Geos (Lin (Li p1 p2)) add Emp) \<Longrightarrow>
    Line_on (Li p1 p2) p3" by (simp add:Line_on_trans)
  from P1 P48 have P49 : "\<not> Eq (Geos (Lin (Li p3 p7)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by blast
  from P37 P45 P46 P48 P47 P49 have P50 : "Eq (Geos (Poi p8) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Line_unique_Point)
  from P37 have P51 : "Bet_Point (Se p3 p7) p8" by simp
  from P50 P51 have P52 : "Bet_Point (Se p3 p7) p1" by (simp add:Point_Eq)
  from P44 have P53 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<Longrightarrow> Line_on (Li p1 p3) p2" by (simp add:Point_Eq)
  from P2 P53 have P54 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by blast
  have P55 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from P45 P47 P54 P55 have P56 : "Line_on (Li p3 p7) p2 \<Longrightarrow>
    Eq (Geos (Lin (Li p3 p7)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  from P49 P56 have P57 : "\<not> Line_on (Li p3 p7) p2" by blast
  from assms have P58 : "\<not> Line_on_Seg (Li p1 p5) (Se p3 p2) \<and> \<not> Line_on (Li p1 p5) p3
    \<and> \<not> Line_on (Li p1 p5) p2 \<and> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Plane_sameside_def)
  from P52 have P59 : "\<not> Eq (Geos (Poi p7) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  have P60 : "Line_on (Li p1 p5) p1" by (simp add:Line_on_rule)
  from P41 P45 P59 P60 have P61 : "Line_on (Li p1 p5) p7 \<Longrightarrow>
    Eq (Geos (Lin (Li p3 p7)) add Emp) (Geos (Lin (Li p1 p5)) add Emp)" by (simp add:Line_unique)
  from P40 P61 have P62 : "Line_on (Li p1 p5) p7 \<Longrightarrow> Line_on (Li p1 p5) p3" by (simp add:Line_on_trans)
  from P58 P62 have P63 : "\<not> Line_on (Li p1 p5) p7" by blast
  from P58 have P64 : "\<not> Line_on (Li p1 p5) p3" by simp
  from P58 have P65 : "\<not> Line_on (Li p1 p5) p2" by simp
  from P52 P57 P60 P63 P64 P65 have P66 : "Line_on_Seg (Li p1 p5) (Se p3 p2) \<and> \<not> Line_on_Seg (Li p1 p5) (Se p7 p2)
        \<or> Line_on_Seg (Li p1 p5) (Se p7 p2) \<and> \<not> Line_on_Seg (Li p1 p5) (Se p3 p2)" by (simp add:Pachets_axiom)
  from P58 P66 have "Line_on_Seg (Li p1 p5) (Se p7 p2)" by blast
  then have "\<exists>p. Line_on (Li p1 p5) p \<and> Bet_Point (Se p7 p2) p" by (simp add:Line_on_Seg_rule)
  then obtain p9 :: Point where P67 : "Line_on (Li p1 p5) p9 \<and> Bet_Point (Se p7 p2) p9" by blast
  then have P68 : "Bet_Point (Se p2 p7) p9" by (simp add:Bet_rev)
  from P3 P68 have "Bet_Point (Se p2 p4) p9" by (blast intro:Bet_swap_134_124)
  then have P69 : "Bet_Point (Se p4 p2) p9" by (simp add:Bet_rev)
  from P67 P69 have "\<exists>p. Line_on (Li p1 p5) p \<and> Bet_Point (Se p4 p2) p" by blast
  then have P70 : "Line_on_Seg (Li p1 p5) (Se p4 p2)" by (simp add:Line_on_Seg_rule)
  from assms have P71 : "\<not> Line_on_Seg (Li p1 p5) (Se p4 p2)" by (simp add:Plane_sameside_def)
  from P70 P71 show False by blast
qed

lemma (in Congruence_Rule) Ang_Gr_trans_Gr_Gr : 
  assumes 
    "Def (Ang (An p11 p12 p13))" "Def (Ang (An p21 p22 p23))" "Def (Ang (An p31 p32 p33))"
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)"
    "Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
  shows 
    "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)"
proof -
  from assms have P1 : "\<not> Line_on (Li p12 p13) p11" by (simp add:Ang_to_Tri Tri_def_Line)
  from assms P1 have "\<exists>p. Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" by (simp add:Ang_move_sameside)
  then obtain p14 :: Point where P2 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p14 p11" by blast
  from assms P1 have "\<exists>p. Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p p11" by (simp add:Ang_move_sameside)
  then obtain p15 :: Point where P3 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp)
    \<and> Plane_sameside (Li p12 p13) p15 p11" by blast
  from P2 have P4 : "Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p14 p12 p13)) add Emp)" by simp
  from P2 have P5 : "Plane_sameside (Li p12 p13) p14 p11" by simp
  from P3 have P6 : "Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp)" by simp
  from P3 have P7 : "Plane_sameside (Li p12 p13) p15 p11" by simp
  from P4 P5 have "Ang_inside (An p11 p12 p13) p14 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_greater_def)
  then have P8 : "Ang_inside (An p11 p12 p13) p14" using assms by blast
  from P5 have P9 : "\<not> Line_on (Li p12 p13) p14" by (simp add:Plane_sameside_def)
  from assms have P10 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from P9 P10 have "Def (Ang (An p12 p13 p14))" by (simp add:Ang_sinple_def)
  then have P11 : "Def (Ang (An p14 p12 p13))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P4 P11 have P12 : "Gr (Geos (Ang (An p14 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  from P11 have P13 : "Eq (Geos (Poi p14) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow> 
    Eq (Geos (Ang (An p14 p12 p13)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp) \<and> Def (Ang (An p15 p12 p13))" by (simp add:Ang_Eq_Point)
  then have P14 : "Eq (Geos (Poi p14) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p14 p12 p13)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp)" by (blast intro:Ang_weektrans)
  from assms P4 P11 P13 P14 have P15 : "Eq (Geos (Poi p14) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from assms P6 P13 P15 have P16 : "Eq (Geos (Poi p14) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from assms have P17 : "\<not> Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p21 p22 p23)) add Emp)" by (simp add:Ang_Gr_not_Eq_rev)
  from P16 P17 have P18 : "\<not> Eq (Geos (Poi p15) add Emp) (Geos (Poi p14) add Emp)" by (blast intro:Eq_rev)
  from P7 have P19 : "Plane_sameside (Li p12 p13) p11 p15" by (simp add:Plane_sameside_rev)
  from P5 P18 P19 have P20 : "Plane_sameside (Li p12 p13) p15 p14" by (blast intro:Plane_sameside_trans Plane_sameside_rev)
  from P6 P20 have P21 : "Ang_inside (An p14 p12 p13) p15 \<longleftrightarrow>
    Gr (Geos (Ang (An p14 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by (simp add:Ang_greater_def)
  from P12 P21 have "Ang_inside (An p14 p12 p13) p15" by simp
  then have P22 : "Plane_sameside (Li p12 p14) p13 p15 \<and> Plane_sameside (Li p12 p13) p14 p15" by (simp add:Ang_inside_def)
  from P8 have P23 : "Plane_sameside (Li p12 p11) p13 p14 \<and> Plane_sameside (Li p12 p13) p11 p14" by (simp add:Ang_inside_def)
  then have P24 : "Plane_diffside (Li p12 p11) p13 p15 \<Longrightarrow> Plane_diffside (Li p12 p11) p14 p15" by (blast intro:Plane_trans) 
  from P8 have P25 : "Plane_diffside (Li p12 p14) p11 p13" by (simp add:Ang_inside_Planeside)
  from P22 P25 have P26 : "Plane_diffside (Li p12 p14) p11 p15" by (blast intro:Plane_trans Plane_diffside_rev)
  from P5 P7 P24 P26 have "Plane_diffside (Li p12 p11) p13 p15 \<Longrightarrow> False" by (blast intro:Planeside_wrong_relation)
  then have P27 : "\<not> Plane_diffside (Li p12 p11) p13 p15" by blast
  from P23 have P28 : "\<not> Line_on (Li p12 p11) p13" by (simp add:Plane_sameside_def)
  have P29 : "Line_on (Li p12 p13) p12" by (simp add:Line_on_rule)
  from P19 have P30 : "\<not> Line_on (Li p12 p13) p11" by (simp add:Plane_sameside_def)
  from P19 have P31 : "\<not> Line_on (Li p12 p13) p15" by (simp add:Plane_sameside_def)
  from P29 P30 P31 have "Bet_Point (Se p11 p15) p12 \<Longrightarrow> \<exists>p. Bet_Point (Se p11 p15) p \<and> 
    Line_on (Li p12 p13) p \<and> \<not> Line_on (Li p12 p13) p11 \<and> \<not> Line_on (Li p12 p13) p15" by blast
  then have "Bet_Point (Se p11 p15) p12 \<Longrightarrow> Plane_diffside (Li p12 p13) p11 p15" by (simp add:Plane_diffside_def)
  then have P32 : "Bet_Point (Se p11 p15) p12 \<Longrightarrow> \<not> Plane_sameside (Li p12 p13) p15 p11" by (simp add:Plane_diffside_rev Plane_diffside_not_sameside)
  from P7 P32 have P33 : "\<not> Bet_Point (Se p11 p15) p12" by blast
  have P34 : "Line_on (Li p12 p13) p13" by (simp add:Line_on_rule)
  have P35 : "\<not> Bet_Point (Se p13 p13) p12" by (simp add:Bet_end_Point)
  from P29 have P36 : "Eq (Geos (Poi p12) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow>
    Line_on (Li p12 p13) p15" by (simp add:Point_Eq)
  from P31 P36 have P37 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p15) add Emp)" by blast
  from assms have P38 : "\<not> Eq (Geos (Poi p12) add Emp) (Geos (Poi p13) add Emp)" by (simp add:Ang_def)
  from assms P33 P34 P35 P37 P38 have P39 : "Line_on (Li p12 p11) p15 \<Longrightarrow>
    Eq (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp) \<and> Def (Ang (An p15 p12 p13))" by (simp add:Ang_Point_swap)
  then have P40 : "Line_on (Li p12 p11) p15 \<Longrightarrow>
    Cong (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p15 p12 p13)) add Emp)" by (blast intro:Ang_weektrans)
  from assms P6 P39 P40 have P41 : "Line_on (Li p12 p11) p15 \<Longrightarrow>
    Cong (Geos (Ang (An p31 p32 p33)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from assms P41 have P42 : "Line_on (Li p12 p11) p15 \<Longrightarrow> 
    Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq)
  from assms have P43 : "\<not> Gr (Geos (Ang (An p21 p22 p23)) add Emp) (Geos (Ang (An p11 p12 p13)) add Emp)" by (simp add:Ang_Gr_not_Eq_rev)
  from P42 P43 have P44: "\<not> Line_on (Li p12 p11) p15" by blast
  from P34 have P45 : "Eq (Geos (Poi p13) add Emp) (Geos (Poi p15) add Emp) \<Longrightarrow>
    Line_on (Li p12 p13) p15" by (simp add:Point_Eq)
  from P31 P45 have P46 : "\<not> Eq (Geos (Poi p13) add Emp) (Geos (Poi p15) add Emp)" by blast
  from P27 P28 P44 P46 have P47 : "Plane_sameside (Li p12 p11) p13 p15" by (simp add:Plane_not_diffside_sameside)
  from assms P19 P47 have P48 : "Ang_inside (An p11 p12 p13) p15" by (simp add:Ang_inside_def)
  from P6 P7 have P49 : "Ang_inside (An p11 p12 p13) p15 \<longleftrightarrow> 
    Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by (simp add:Ang_greater_def)
  from P48 P49 show "Gr (Geos (Ang (An p11 p12 p13)) add Emp) (Geos (Ang (An p31 p32 p33)) add Emp)" by simp
qed

lemma (in Congruence_Rule) Ang_complementary_inside : 
  assumes 
    "Def (Ang (An p1 p2 p3))"
    "Bet_Point (Se p3 p4) p2"
    "Ang_inside (An p5 p2 p3) p1"
  shows 
    "Ang_inside (An p1 p2 p4) p5"
proof -
  from assms have P1 : "Plane_sameside (Li p2 p5) p3 p1 \<and> Plane_sameside (Li p2 p3) p5 p1" by (simp add:Ang_inside_def)
  from assms have P2 : "Line_on (Li p2 p3) p4" by (simp add:Line_Bet_on)
  have P3 : "Line_on (Li p2 p3) p2" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li p2 p4) p2" by (simp add:Line_on_rule)
  have P5 : "Line_on (Li p2 p4) p4" by (simp add:Line_on_rule)
  from assms have P6 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  from P2 P3 P4 P5 P6 have P7 : "Eq (Geos (Lin (Li p2 p3)) add Emp) (Geos (Lin (Li p2 p4)) add Emp)" by (simp add:Line_unique)
  from P1 P7 have P8 : "Plane_sameside (Li p2 p4) p5 p1" by (blast intro:Plane_Line_trans)
  have P9 : "Line_on (Li p2 p1) p2" by (simp add:Line_on_rule)
  have "Line_on (Li p2 p1) p1" by (simp add:Line_on_rule)
  then have P10 : "Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p2 p1)) add Emp) \<Longrightarrow>
    Line_on (Li p3 p4) p1" by (blast intro:Eq_rev Line_on_trans)
  from P1 have P11 : "\<not> Line_on (Li p2 p3) p1" by (simp add:Plane_sameside_def)
  from assms have P12 : "Line_on (Li p3 p4) p2" by (simp add:Line_Bet_on)
  have P13 : "Line_on (Li p3 p4) p3" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li p2 p3) p3" by (simp add:Line_on_rule)
  from assms have P15 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P3 P12 P13 P14 P15 have P16 : "Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p2 p3)) add Emp)" by (simp add:Line_unique)
  from P10 P16 have P17 : "Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p2 p1)) add Emp) \<Longrightarrow>
    Line_on (Li p2 p3) p1" by (simp add:Line_on_trans)
  from P11 P17 have P18 : "\<not> Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p2 p1)) add Emp)" by blast
  from assms P9 P18 have P19 : "Plane_diffside (Li p2 p1) p3 p4" by (simp add:Plane_Bet_diffside)
  from assms have P20 : "Plane_diffside (Li p2 p1) p3 p5" by (simp add:Ang_inside_Planeside Plane_diffside_rev)
  from P5 have P21 : "Eq (Geos (Poi p4) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow> Line_on (Li p2 p4) p5" by (simp add:Point_Eq)
  from P8 have P22 : "\<not> Line_on (Li p2 p4) p5" by (simp add:Plane_sameside_def)
  from P21 P22 have P23 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p5) add Emp)" by blast
  from P19 P20 P23 have P24 : "Plane_sameside (Li p2 p1) p4 p5" by (simp add:Plane_trans_inv)
  then have P25 : "\<not> Line_on (Li p2 p1) p4" by (simp add:Plane_sameside_def)
  from assms have "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Ang_def)
  then have P26 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from P25 P26 have "Def (Ang (An p2 p1 p4))" by (simp add:Ang_sinple_def)
  then have P27 : "Def (Ang (An p1 p2 p4))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P8 have P28 : "Plane_sameside (Li p2 p4) p1 p5" by (simp add:Plane_sameside_rev)
  from P24 P27 P28 show "Ang_inside (An p1 p2 p4) p5" by (simp add:Ang_inside_def)
qed

text\<open>Theorem21\<close>

theorem (in Congruence_Rule) Ang_Right_angle_Cong : 
  assumes 
    "Right_angle (An l1 o1 h1)" "Right_angle (An l2 o2 h2)"
  shows 
    "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)"
proof -
  from assms have "\<exists>p. Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l1 o1 p)) add Emp)
        \<and> Bet_Point (Se h1 p) o1 \<and> Def (Ang (An l1 o1 h1)) \<and> Def (Ang (An l1 o1 p))" by (simp add:Ang_Right_angle_def)
  then obtain k1 :: Point where P1 : "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)
        \<and> Bet_Point (Se h1 k1) o1 \<and> Def (Ang (An l1 o1 h1)) \<and> Def (Ang (An l1 o1 k1))" by blast
  from assms have "\<exists>p. Cong (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An l2 o2 p)) add Emp)
        \<and> Bet_Point (Se h2 p) o2 \<and> Def (Ang (An l2 o2 h2)) \<and> Def (Ang (An l2 o2 p))" by (simp add:Ang_Right_angle_def)
  then obtain k2 :: Point where P2 : "Cong (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An l2 o2 k2)) add Emp)
        \<and> Bet_Point (Se h2 k2) o2 \<and> Def (Ang (An l2 o2 h2)) \<and> Def (Ang (An l2 o2 k2))" by blast
  from P1 have P3 : "\<not> Line_on (Li o1 h1) l1" by (simp add:Ang_to_Tri Tri_def_Line)
  from P1 P2 P3 have "\<exists>p. Cong (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An p o1 h1)) add Emp)
    \<and> Plane_sameside (Li o1 h1) p l1" by (simp add:Ang_move_sameside)
  then obtain l11 :: Point where P4 : "Cong (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)
    \<and> Plane_sameside (Li o1 h1) l11 l1" by blast
  then have P5 : "\<not> Line_on (Li o1 h1) l11" by (simp add:Plane_sameside_def)
  from P1 have P6 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi h1) add Emp)" by (simp add:Ang_def)
  from P5 P6 have "Def (Ang (An o1 h1 l11))" by (simp add:Ang_sinple_def)
  then have P7 : "Def (Ang (An l11 o1 h1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P2 P4 P7 have P8 : "Cong (Geos (Ang (An l2 o2 k2)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P2 have P9 : "Def (Ang (An h2 o2 l2))" by (simp add:Ang_def_rev)
  from P7 have P10 : "Def (Ang (An h1 o1 l11))" by (simp add:Ang_def_rev)
  have P11 : "Cong (Geos (Ang (An l2 o2 h2)) add Emp) (Geos (Ang (An h2 o2 l2)) add Emp)" by (simp add:Ang_roll)
  have P12 : "Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An h1 o1 l11)) add Emp)" by (simp add:Ang_roll)
  from P2 P4 P7 P9 P11 have P13 : "Cong (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P7 P9 P10 P12 P13 have P14 : "Cong (Geos (Ang (An h2 o2 l2)) add Emp) (Geos (Ang (An h1 o1 l11)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P1 P2 P9 P10 P14 have P15 : "Cong (Geos (Ang (An l2 o2 k2)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by (simp add:Ang_complementary)
  from P1 P4 P7 have P16 : "Eq (Geos (Lin (Li o1 l11)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by (simp add:Ang_move_unique_inv)
  from P1 P2 P4 P7 P16 have "Eq (Geos (Lin (Li o1 l11)) add Emp) (Geos (Lin (Li o1 l1)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  then have P17 : "\<not> Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li o1 l11)) add Emp) (Geos (Lin (Li o1 l1)) add Emp)" by blast
  from P1 P4 P7 P17 have P18 : "\<not> Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp) \<Longrightarrow>
    Ang_inside (An l11 o1 h1) l1 \<and> \<not> Ang_inside (An l1 o1 h1) l11
    \<or> \<not> Ang_inside (An l11 o1 h1) l1 \<and> Ang_inside (An l1 o1 h1) l11" by (simp add:Ang_inside_case)
  from P4 have P19 : "Plane_sameside (Li o1 h1) l1 l11" by (simp add:Plane_sameside_rev)
  have P20 : "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by simp
  from P19 P20 have P21 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow>
    Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by (simp add:Ang_greater_def)
  from P1 have P22 : "Line_on (Li o1 h1) k1" by (simp add:Line_Bet_on)
  have P23 : "Line_on (Li o1 h1) o1" by (simp add:Line_on_rule)
  have P24 : "Line_on (Li o1 k1) k1" by (simp add:Line_on_rule)
  have P25 : "Line_on (Li o1 k1) o1" by (simp add:Line_on_rule)
  from P1 have P26 : "Bet_Point (Se h1 k1) o1" by simp
  then have P27 : "\<not> Eq (Geos (Poi k1) add Emp) (Geos (Poi o1) add Emp)" by (simp add:Bet_Point_def)
  from P22 P23 P24 P25 P27 have P28 : "Eq (Geos (Lin (Li o1 h1)) add Emp) (Geos (Lin (Li o1 k1)) add Emp)" by (simp add:Line_unique)
  from P19 P28 have P29 : "Plane_sameside (Li o1 k1) l1 l11" by (simp add:Plane_Line_trans)
  then have P30 : "Plane_sameside (Li o1 k1) l11 l1" by (simp add:Plane_sameside_rev)
  then have P31 : "\<not> Line_on (Li o1 k1) l11" by (simp add:Plane_sameside_def)
  from P1 have P32 : "\<not> Eq (Geos (Poi o1) add Emp) (Geos (Poi k1) add Emp)" by (simp add:Ang_def)
  from P31 P32 have "Def (Ang (An o1 k1 l11))" by (simp add:Ang_sinple_def)
  then have P33 : "Def (Ang (An l11 o1 k1))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P2 P7 P8 P15 P33 have P34 : "Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by (blast intro:Ang_rev Ang_trans)
  from P1 have P35 : "Def (Ang (An l1 o1 h1))" by simp
  from P26 P35 have P36 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow> Ang_inside (An l1 o1 k1) l11" by (simp add:Ang_complementary_inside)
  have P37 : "Cong (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by simp
  from P30 P36 P37 have P38 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow> 
    Gr (Geos (Ang (An l1 o1 k1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by (simp add:Ang_greater_def)
  from P1 P7 P21 have P39 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow>
    Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq)
  from P1 P7 P33 P38 P39 have P40 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow>
    Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr)
  from P7 P33 have P41 : 
    "Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)
    \<and> Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by (simp add:Ang_relation_case_fact)
  from P40 P41 have P42 : "Ang_inside (An l11 o1 h1) l1 \<Longrightarrow>
    \<not> Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by blast
  from P34 P42 have P43 : "\<not> Ang_inside (An l11 o1 h1) l1" by blast
  have P44 : "Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by simp
  from P4 P44 have P45 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow> 
    Gr (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by (simp add:Ang_greater_def)
  from P1 P7 have P46 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow> Ang_inside (An l11 o1 k1) l1" by (simp add:Ang_complementary_inside)
  have P47 : "Cong (Geos (Ang (An l1 o1 k1)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)" by simp
  from P29 P46 P47 have P48 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow> 
    Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l1 o1 k1)) add Emp)" by (simp add:Ang_greater_def)
  from P1 P33 P48 have P49 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow>
    Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l1 o1 h1)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P1 P7 P33 P45 P49 have P50 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow>
    Gr (Geos (Ang (An l11 o1 k1)) add Emp) (Geos (Ang (An l11 o1 h1)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr)
  from P41 P50 have P51 : "Ang_inside (An l1 o1 h1) l11 \<Longrightarrow>
    \<not> Cong (Geos (Ang (An l11 o1 h1)) add Emp) (Geos (Ang (An l11 o1 k1)) add Emp)" by blast
  from P34 P51 have P52 : "\<not> Ang_inside (An l1 o1 h1) l11" by blast
  from P18 P43 P52 show "Cong (Geos (Ang (An l1 o1 h1)) add Emp) (Geos (Ang (An l2 o2 h2)) add Emp)" by blast
qed

lemma (in Congruence_Rule) Ang_external_Gr_lemma1 : 
  assumes N : 
    "Def (Tri (Tr A B C))"
    "Bet_Point (Se B D) A"
  shows "\<not> Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)"
proof
  assume W : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)"
  from N have P1 : "Line_on (Li B D) A" by (simp add:Line_Bet_on)
  have P2 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  from N have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P3 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from N have P4 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Tri_def)
  then have P5 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 P3 P5 have "\<exists>p. Eq (Geos (Seg (Se C B)) add Emp) (Geos (Seg (Se A p)) add Emp) 
    \<and> \<not> Bet_Point (Se p D) A \<and> Line_on (Li B D) p \<and> \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain D1 :: Point where P6 : "Eq (Geos (Seg (Se C B)) add Emp) (Geos (Seg (Se A D1)) add Emp) 
    \<and> \<not> Bet_Point (Se D1 D) A \<and> Line_on (Li B D) D1 \<and> \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D1) add Emp)" by blast
  have P7 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  from N have P8 : "Line_on (Li A D) B" by (simp add:Line_Bet_on)
  have P9 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  have P10 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from N have P11 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from P7 P8 P9 P10 P11 have "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  then have P12 : "Line_on (Li A D) C \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from N have P13 : "\<not> Line_on (Li A B) C" by (simp add:Tri_def_Line)
  from P12 P13 have P14 : "\<not> Line_on (Li A D) C" by blast
  from P3 P14 have "Def (Ang (An A D C))" by (simp add:Ang_sinple_def)
  then have P15 : "Def (Ang (An C A D))" by (blast intro:Ang_def_rev Ang_def_inv)
  have P16 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  have P17 : "\<not> Bet_Point (Se C C) A" by (simp add:Bet_end_Point)  
  have P18 : "Line_on (Li A D) D" by (simp add:Line_on_rule)
  from P1 P2 P3 P7 P18 have P19 : "Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_unique)
  from P6 P19 have P20 : "Line_on (Li A D) D1" by (simp add:Line_on_trans)
  from P6 have P21 : "\<not> Bet_Point (Se D D1) A" by (blast intro:Bet_rev)
  from N have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  then have P22 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P6 P15 P16 P17 P20 P21 P22 have P23 :
    "Eq (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An C A D1)) add Emp)
    \<and> Def (Ang (An C A D1))" by (simp add:Ang_Point_swap)
  have P24 : "Cong (Geos (Ang (An C A D1)) add Emp) (Geos (Ang (An C A D1)) add Emp)" by simp
  from P23 P24 have P25 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An C A D1)) add Emp)" by (blast intro:Ang_weektrans)
  from P23 have P26 : "Def (Tri (Tr A C D1))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from N have P27 : "Def (Tri (Tr C A B))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  have P28 : "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se C A)) add Emp)" by (simp add:Seg_rev)
  from P6 have P29 : "Eq (Geos (Seg (Se A D1)) add Emp) (Geos (Seg (Se C B)) add Emp)" by (simp add:Eq_rev)
  from P29 P26 P27 P28 have 
    "Cong (Geos (Ang (An C A D1)) add Emp) (Geos (Ang (An A C B)) add Emp) \<Longrightarrow>
    Cong (Geos (Tri (Tr A C D1)) add Emp) (Geos (Tri (Tr C A B)) add Emp)" by (simp add:Tri_SAS)
  then have P29 : "Cong (Geos (Ang (An C A D1)) add Emp) (Geos (Ang (An A C B)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An D1 C A)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Tri_Cong_def)
  from N have P30 : "Def (Ang (An A C B))" by (blast intro:Tri_to_Ang Ang_def_inv)
  from W P15 P23 P25 P30 have P31 : "Cong (Geos (Ang (An C A D1)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P29 P31 have P32 : "Cong (Geos (Ang (An D1 C A)) add Emp) (Geos (Ang (An B A C)) add Emp)" by simp
  have P33 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P34 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from P4 P33 P34 have "\<exists>p. Bet_Point (Se B p) C \<and> Line_on (Li B C) p" by (simp add:Bet_extension)
  then obtain E :: Point where P35 : "Bet_Point (Se B E) C \<and> Line_on (Li B C) E" by blast
  have P36 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An D A C)) add Emp)" by (simp add:Ang_roll)
  from P15 have P37 : "Def (Ang (An D A C))" by (simp add:Ang_def_rev)
  have P38 : "Cong (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (simp add:Ang_roll)
  from P30 have P39 : "Def (Ang (An B C A))" by (simp add:Ang_def_rev)
  from W P15 P30 P36 P37 P38 have P40 : "Cong (Geos (Ang (An D A C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P30 P37 P38 P39 P40 have P41 : "Cong (Geos (Ang (An D A C)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from N have P42 : "Bet_Point (Se D B) A" by (simp add:Bet_rev)
  from P35 P37 P39 P41 P42 have P43 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An A C E)) add Emp)" by (simp add:Ang_complementary)
  have P44 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An C A B)) add Emp)" by (simp add:Ang_roll)
  from P39 have P45 : "Def (Ang (An B A C))" by (simp add:Ang_def_inv)
  then have P46 : "Def (Ang (An C A B))" by (simp add:Ang_def_rev)
  from P23 have P47 : "Def (Ang (An D1 C A))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P32 P44 P45 P46 P47 have P48 : "Cong (Geos (Ang (An D1 C A)) add Emp) (Geos (Ang (An C A B)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P35 have P49 : "Bet_Point (Se B E) C" by simp
  then have P50 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P35 have P51 : "Line_on (Li B C) E" by simp
  from P16 P34 P50 P51 have P52 : "Line_on (Li A C) E \<Longrightarrow>
    Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P33 P52 have P53 : "Line_on (Li A C) E \<Longrightarrow> Line_on (Li A C) B" by (simp add:Line_on_trans)
  from N have "Def (Tri (Tr A C B))" by (blast intro:Tri_def_rev Tri_def_trans)
  then have P54 : "\<not> Line_on (Li A C) B" by (simp add:Tri_def_Line)
  from P53 P54 have P55 : "\<not> Line_on (Li A C) E" by blast
  from P22 P55 have P56 : "Def (Ang (An A C E))" by (simp add:Ang_sinple_def)
  from P43 P46 P47 P48 P56 have P57 : "Cong (Geos (Ang (An D1 C A)) add Emp) (Geos (Ang (An A C E)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  then have P58 : "Cong (Geos (Ang (An A C E)) add Emp) (Geos (Ang (An D1 C A)) add Emp)" by (simp add:Ang_rev)
  have P59 : "Cong (Geos (Ang (An A C E)) add Emp) (Geos (Ang (An E C A)) add Emp)" by (simp add:Ang_roll)
  have P60 : "Line_on (Li C A) A" by (simp add:Line_on_rule)
  have "Line_on (Li B D) B" by (simp add:Line_on_rule)
  then have P61 : "Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow> Line_on (Li C A) B" by (simp add:Line_on_trans)
  from N have P62 : "\<not> Line_on (Li C A) B" by (simp add:Tri_def_Line)
  from P61 P62 have P63 : "\<not> Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from N P60 P63 have P64 : "Plane_diffside (Li C A) B D" by (simp add:Plane_Bet_diffside)
  then have P65 : "Eq (Geos (Poi D) add Emp) (Geos (Poi D1) add Emp) \<Longrightarrow>
    Plane_diffside (Li C A) B D1" by (simp add:Point_Eq)
  from P6 have P66 : "Line_on (Li B D) D1" by simp
  from P6 have P67 : "\<not> Eq (Geos (Poi D1) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 P3 P66 P67 have P68 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi D1) add Emp) \<Longrightarrow>
    Bet_Point (Se D A) D1 \<or> Bet_Point (Se A D1) D \<or> Bet_Point (Se D1 D) A" by (simp add:Bet_case)
  from P19 have P69 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li C A)) add Emp)" by (blast intro:Eq_trans)
  from P63 P69 have P70 : "\<not> Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from P60 P70 have P71 : "Bet_Point (Se A D) D1 \<Longrightarrow> Plane_sameside (Li C A) D D1" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  have "Line_on (Li A D1) D1" by (simp add:Line_on_rule)
  then have P72 : "Eq (Geos (Lin (Li A D1)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow>
    Line_on (Li C A) D1" by (simp add:Line_on_trans)
  from P23 have "Def (Tri (Tr C A D1))" by (simp add:Ang_to_Tri)
  then have P73 : "\<not> Line_on (Li C A) D1" by (simp add:Tri_def_Line)
  from P72 P73 have P74 : "\<not> Eq (Geos (Lin (Li A D1)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from P60 P74 have P75 : "Bet_Point (Se A D1) D \<Longrightarrow> Plane_sameside (Li C A) D D1" by (simp add:Plane_Bet_sameside)
  from P6 P64 P68 P71 P75 have P76 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi D1) add Emp) \<Longrightarrow>
    Plane_diffside (Li C A) B D1" by (blast intro:Plane_trans Plane_diffside_rev Bet_rev)
  from P65 P76 have P77 : "Plane_diffside (Li C A) B D1" by blast
  have P78 : "Line_on (Li C A) C" by (simp add:Line_on_rule)
  have "Line_on (Li B E) B" by (simp add:Line_on_rule)
  then have P79 : "Eq (Geos (Lin (Li B E)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow> Line_on (Li C A) B" by (simp add:Line_on_trans)
  from P62 P79 have P80 : "\<not> Eq (Geos (Lin (Li B E)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from P49 P78 P80 have P81 : "Plane_diffside (Li C A) B E" by (simp add:Plane_Bet_diffside)
  from P51 have P82 : "Eq (Geos (Poi D1) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B C) D1" by (blast intro:Eq_rev Point_Eq)
  from P77 have "\<exists>p. Bet_Point (Se B D1) p \<and> Line_on (Li C A) p 
    \<and> \<not> Line_on (Li C A) B \<and> \<not> Line_on (Li C A) D1" by (simp add:Plane_diffside_def)
  then obtain F :: Point where "Bet_Point (Se B D1) F" by blast
  then have P83 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D1) add Emp)" by (simp add:Bet_Point_def)
  from P8 P20 P33 P82 P83 have P84 : "Eq (Geos (Poi D1) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> 
    Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from P7 P84 have P85 : "Eq (Geos (Poi D1) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Line_on_trans)
  from N have P86 : "\<not> Line_on (Li B C) A" by (simp add:Tri_def_Line)
  from P85 P86 have P87 : "\<not> Eq (Geos (Poi D1) add Emp) (Geos (Poi E) add Emp)" by blast
  from P77 P81 P87 have P88 : "Plane_sameside (Li C A) D1 E" by (simp add:Plane_trans_inv)
  from P58 P59 P88 have P89 : "Eq (Geos (Lin (Li D1 C)) add Emp) (Geos (Lin (Li E C)) add Emp) \<and> \<not> Bet_Point (Se D1 E) C" by (simp add:Ang_move_unique)
  from P49 have P90 : "Line_on (Li E C) B" by (simp add:Line_Bet_on)
  from P89 P90 have P91 : "Line_on (Li D1 C) B" by (blast intro:Eq_rev Line_on_trans)
  have P92 : "Line_on (Li D1 C) D1" by (simp add:Line_on_rule)
  from P8 P20 P83 P91 P92 have P93 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li D1 C)) add Emp)" by (simp add:Line_unique)
  from P89 P93 have P94 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li E C)) add Emp)" by (blast intro:Eq_trans)
  from P7 P94 have P95 : "Line_on (Li E C) A" by (simp add:Line_on_trans)
  from P56 have "Def (Tri (Tr E C A))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P96 : "\<not> Line_on (Li E C) A" by (simp add:Tri_def_Line)
  from P95 P96 show False by blast
qed

lemma (in Congruence_Rule) Ang_external_Gr_lemma2 : 
  assumes N : 
    "Def (Tri (Tr A B C))"
    "Bet_Point (Se B D) A"
  shows "\<not> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An C A D)) add Emp)"
proof 
  assume W : "Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An C A D)) add Emp)"
  from N have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  have P2 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  from N have P3 : "Line_on (Li A D) B" by (simp add:Line_Bet_on)
  have P4 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  have P5 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from N have P6 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from P2 P3 P4 P5 P6 have "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  then have P7 : "Line_on (Li A D) C \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from N have P8 : "\<not> Line_on (Li A B) C" by (simp add:Tri_def_Line)
  from P7 P8 have P9 : "\<not> Line_on (Li A D) C" by blast
  from P1 P9 have "Def (Ang (An A D C))" by (simp add:Ang_sinple_def)
  then have P10 : "Def (Ang (An C A D))" by (blast intro:Ang_def_rev Ang_def_inv)
  have P11 : "Cong (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (simp add:Ang_roll)
  from N have P12 : "Def (Ang (An A C B))" by (blast intro:Tri_to_Ang Ang_def_inv)
  then have P13 : "Def (Ang (An B C A))" by (simp add:Ang_def_rev)
  from W P10 P11 P12 P13 have P14 : "Gr (Geos (Ang (An B C A)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  from N have P15 : "\<not> Line_on (Li C A) B" by (simp add:Tri_def_Line)
  from N have P16 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  from P10 P15 have "\<exists>p. Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An p C A)) add Emp) 
    \<and> Plane_sameside (Li C A) p B" by (simp add:Ang_move_sameside)
  then obtain B1 :: Point where P17 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An B1 C A)) add Emp)
    \<and> Plane_sameside (Li C A) B1 B" by blast
  then have P18 : "\<not> Line_on (Li C A) B1" by (simp add:Plane_sameside_def)
  from P16 P18 have "Def (Ang (An C A B1))" by (blast intro:Ang_sinple_def Eq_rev)
  then have P19 : "Def (Ang (An B1 C A))" by (blast intro:Ang_def_rev Ang_def_inv)
  from N have P20 : "Def (Ang (An A C B))" by (blast intro:Tri_def_rev Tri_def_trans Tri_to_Ang)
  from P17 have P21 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An B1 C A)) add Emp)" by simp
  from P17 have P22 : "Plane_sameside (Li C A) B1 B" by simp
  from P10 P14 P19 P20 P21 P22 have "Ang_inside (An B C A) B1" by (simp add:Ang_greater_def)
  then have "Plane_diffside (Li C B1) B A" by (simp add:Ang_inside_Planeside)
  then have "\<exists>p. Bet_Point (Se B A) p \<and> Line_on (Li C B1) p \<and> \<not> Line_on (Li C B1) B \<and> \<not> Line_on (Li C B1) A" by (simp add:Plane_diffside_def)
  then obtain B2 :: Point where P23 : "Bet_Point (Se B A) B2 \<and> Line_on (Li C B1) B2 
    \<and> \<not> Line_on (Li C B1) B \<and> \<not> Line_on (Li C B1) A" by blast
  then have "Line_on (Li B A) B2" by (simp add:Line_Bet_on)
  then have P24 : "Eq (Geos (Poi B2) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li B A) C" by (simp add:Point_Eq)
  from N have "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  then have P25 : "\<not> Line_on (Li B A) C" by (simp add:Tri_def_Line)
  from P24 P25 have P26 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B2) add Emp)" by (blast intro:Eq_rev)
  from P23 have P27 : "Bet_Point (Se A B) B2" by (simp add:Bet_rev)
  have P28 : "Line_on (Li C A) A" by (simp add:Line_on_rule)
  from P5 have P29 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow> 
    Line_on (Li C A) B" by (simp add: Line_on_trans)
  from P15 P29 have P30 : "\<not> Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from P27 P28 P30 have P31 : "Plane_sameside (Li C A) B B2" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  have P32 : "Line_on (Li C A) C" by (simp add:Line_on_rule)
  have "Line_on (Li B1 B2) B1" by (simp add:Line_on_rule)
  then have P33 : "Eq (Geos (Lin (Li B1 B2)) add Emp) (Geos (Lin (Li C A)) add Emp) \<Longrightarrow> 
    Line_on (Li C A) B1" by (simp add: Line_on_trans)
  from P18 P33 have P34 : "\<not> Eq (Geos (Lin (Li B1 B2)) add Emp) (Geos (Lin (Li C A)) add Emp)" by blast
  from P32 P34 have "Bet_Point (Se B1 B2) C \<Longrightarrow> Plane_diffside (Li C A) B1 B2" by (simp add:Plane_Bet_diffside)
  then have P35 : "Bet_Point (Se B1 B2) C \<Longrightarrow> \<not> Plane_sameside (Li C A) B1 B2" by (simp add:Plane_diffside_not_sameside)
  from P22 P31 have P36 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi B2) add Emp) \<Longrightarrow>
    Plane_sameside (Li C A) B1 B2" by (blast intro:Plane_sameside_trans Eq_rev)
  from P35 P36 have P37 : "\<not> Eq (Geos (Poi B1) add Emp) (Geos (Poi B2) add Emp) \<Longrightarrow>
    \<not> Bet_Point (Se B1 B2) C" by blast
  have P38 : "Eq (Geos (Poi B1) add Emp) (Geos (Poi B2) add Emp) \<Longrightarrow>
    Bet_Point (Se B1 B2) C \<Longrightarrow> Bet_Point (Se B2 B2) C" by (simp add:Bet_Point_Eq)
  have P39 : "\<not> Bet_Point (Se B2 B2) C" by (simp add:Bet_end_Point)
  from P38 P39 have P40 : "Eq (Geos (Poi B1) add Emp) (Geos (Poi B2) add Emp) \<Longrightarrow>
    \<not> Bet_Point (Se B1 B2) C" by blast
  from P37 P40 have P41 : "\<not> Bet_Point (Se B1 B2) C" by blast
  have P42 : "\<not> Bet_Point (Se A A) C" by (simp add:Bet_end_Point)
  from P16 P19 P23 P26 P28 P41 P42 have P43 : 
    "Eq (Geos (Ang (An B1 C A)) add Emp) (Geos (Ang (An B2 C A)) add Emp) \<and> Def (Ang (An B2 C A))" by (simp add:Ang_Point_swap)
  from P21 P43 have P44 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An B2 C A)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P43 have P45 : "Def (Tri (Tr A B2 C))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P27 have P46 : "Bet_Point (Se B A) B2" by (simp add:Bet_rev)
  from N P46 have P47 : "Bet_Point (Se B2 D) A" by (blast intro:Bet_swap_134_234)
  from P45 P47 have P48 : "\<not> Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B2)) add Emp)" by (simp add:Ang_external_Gr_lemma1)
  have P49 : "Cong (Geos (Ang (An B2 C A)) add Emp) (Geos (Ang (An A C B2)) add Emp)" by (simp add:Ang_roll)
  from P43 have P50 : "Def (Ang (An A C B2))" by (simp add:Ang_def_rev)
  from P10 P43 P44 P49 P50 have P51 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B2)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P48 P51 show False by blast
qed

text\<open>Theorem22\<close>

theorem (in Congruence_Rule) Ang_external_Gr : 
  assumes
    "Def (Tri (Tr A B C))"
    "Bet_Point (Se B D) A"
  shows
    "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)"
    "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A B C)) add Emp)"
proof -
  from assms have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  have P2 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  from assms have P3 : "Line_on (Li A D) B" by (simp add:Line_Bet_on)
  have P4 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  have P5 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from assms have P6 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from P2 P3 P4 P5 P6 have "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  then have P7 : "Line_on (Li A D) C \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from assms have P8 : "\<not> Line_on (Li A B) C" by (simp add:Tri_def_Line)
  from P7 P8 have P9 : "\<not> Line_on (Li A D) C" by blast
  from P1 P9 have "Def (Ang (An A D C))" by (simp add:Ang_sinple_def)
  then have P10 : "Def (Ang (An C A D))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P11 : "Def (Ang (An A C B))" by (simp add:Tri_to_Ang Ang_def_inv)
  from P10 P11 have P12 : 
    "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<or> Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<or> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (simp add:Ang_relation_case)
  from assms have P13 : "\<not> Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (simp add:Ang_external_Gr_lemma1)
  from assms have P14 : "\<not> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (simp add:Ang_external_Gr_lemma2)
  from P12 P13 P14 show P15 : "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A C B)) add Emp)" by blast
  have P16 : "Line_on (Li C A) C" by (simp add:Line_on_rule)
  have P17 : "Line_on (Li C A) A" by (simp add:Line_on_rule)
  from assms have P18 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  from P16 P17 P18 have "\<exists>p. Bet_Point (Se C p) A \<and> Line_on (Li C A) p" by (simp add:Bet_extension)
  then obtain E :: Point where P19 : "Bet_Point (Se C E) A" by blast
  from assms have P20 : "Bet_Point (Se D B) A" by (simp add:Bet_rev)
  from P10 P19 P20 have P21 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An E A B)) add Emp)" by (simp add:Ang_vertical)
  have P22 : "Eq (Geos (Ang (An E A B)) add Emp) (Geos (Ang (An B A E)) add Emp)" by (simp add:Ang_roll)
  from P21 P22 have P23 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An B A E)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P19 have P24 : "Line_on (Li C E) A" by (simp add:Line_Bet_on)
  have P25 : "Line_on (Li C E) E" by (simp add:Line_on_rule)
  from P19 have P26 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  from P4 P24 P25 P26 have P27 : "Line_on (Li A B) E \<Longrightarrow>
    Eq (Geos (Lin (Li C E)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  have P28 : "Line_on (Li C E) C" by (simp add:Line_on_rule)
  from P27 P28 have P29 : "Line_on (Li A B) E \<Longrightarrow> Line_on (Li A B) C" by (simp add:Line_on_trans)
  from P8 P29 have P30 : "\<not> Line_on (Li A B) E" by blast
  from P6 P30 have "Def (Ang (An A B E))" by (simp add:Ang_sinple_def)
  then have P31 : "Def (Ang (An B A E))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P11 have P32 : "Def (Tri (Tr A C B))" by (simp add:Ang_to_Tri)
  from P19 P32 have P33 : "\<not> Cong (Geos (Ang (An B A E)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_external_Gr_lemma1)
  from P19 P32 have P34 : "\<not> Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An B A E)) add Emp)" by (simp add:Ang_external_Gr_lemma2)
  from assms have P35 : "Def (Ang (An A B C))" by (simp add:Tri_to_Ang)
  from P31 P35 have P36 : 
    "Cong (Geos (Ang (An B A E)) add Emp) (Geos (Ang (An A B C)) add Emp)
    \<or> Gr (Geos (Ang (An B A E)) add Emp) (Geos (Ang (An A B C)) add Emp)
    \<or> Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An B A E)) add Emp)" by (simp add:Ang_relation_case)
  from P33 P34 P36 have P37 : "Gr (Geos (Ang (An B A E)) add Emp) (Geos (Ang (An A B C)) add Emp)" by blast
  from P10 P23 P31 P35 P37 show "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr)
qed

lemma (in Congruence_Rule) Seg_not_Eq_move : 
  assumes
    "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi B1) add Emp)"
    "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B2) add Emp)"
    "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B3) add Emp)"
    "Line_on l1 A2" "Line_on l1 B2" "Line_on l1 B3"
    "\<not> Bet_Point (Se B3 B2) A2"
    "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B3)) add Emp)"
    "\<not> Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)"
  shows
    "Bet_Point (Se B2 A2) B3 \<and> \<not> Bet_Point (Se A2 B3) B2
    \<or> \<not> Bet_Point (Se B2 A2) B3 \<and> Bet_Point (Se A2 B3) B2"
proof -
  from assms have P1 : "Eq (Geos (Seg (Se A2 B2)) add Emp) (Geos (Seg (Se A2 B3)) add Emp) \<Longrightarrow>
    Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from assms P1 have "\<not> Eq (Geos (Seg (Se A2 B2)) add Emp) (Geos (Seg (Se A2 B3)) add Emp)" by blast
  then have P2 : "\<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi B3) add Emp)" by (simp add:Seg_not_Eq_Point)
  from assms have P3 : "\<not> Eq (Geos (Poi B3) add Emp) (Geos (Poi A2) add Emp)" by (blast intro:Eq_rev)
  from assms have P4 : "Line_on l1 A2" by simp
  from assms have P5 : "Line_on l1 B2" by simp
  from assms have P6 : "Line_on l1 B3" by simp
  from assms have P7 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B2) add Emp)" by simp
  from P2 P3 P4 P5 P6 P7 have "Bet_Point (Se A2 B3) B2 \<or> Bet_Point (Se B3 B2) A2 \<or> Bet_Point (Se B2 A2) B3" by (simp add:Bet_case)
  then have P8 : 
    "Bet_Point (Se A2 B3) B2 \<and> \<not> Bet_Point (Se B3 B2) A2 \<and> \<not> Bet_Point (Se B2 A2) B3
    \<or> \<not> Bet_Point (Se A2 B3) B2 \<and> Bet_Point (Se B3 B2) A2 \<and> \<not> Bet_Point (Se B2 A2) B3
    \<or> \<not> Bet_Point (Se A2 B3) B2 \<and> \<not> Bet_Point (Se B3 B2) A2 \<and> Bet_Point (Se B2 A2) B3" by (simp add:Bet_case_fact)
  from assms P8 show "Bet_Point (Se B2 A2) B3 \<and> \<not> Bet_Point (Se A2 B3) B2
    \<or> \<not> Bet_Point (Se B2 A2) B3 \<and> Bet_Point (Se A2 B3) B2" by blast
qed

lemma (in Congruence_Rule) Tri_Seg_diagonal : 
  assumes
    "Def (Tri (Tr A B C))"
    "Bet_Point (Se B C) D"
    "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se C D)) add Emp)"
  shows
    "Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An A B C)) add Emp)"
proof -
  from assms have P1 : "\<not> Line_on (Li A B) C" by (simp add:Tri_def_Line)
  have "Line_on (Li A C) C" by (simp add:Line_on_rule)
  then have P2 : "Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li A B)) add Emp) \<Longrightarrow>
    Line_on (Li A B) C" by (simp add:Line_on_trans)
  from P1 P2 have P3 : "\<not> Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (blast intro:Eq_rev)
  from assms have P4 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from assms have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  then have P5 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from assms P3 P4 P5 have P6 : "Ang_inside (An B A C) D" by (simp add:Ang_inside_Bet_Point)
  then have "Plane_sameside (Li A C) B D" by (simp add:Ang_inside_def)
  then have P7 : "Plane_sameside (Li A C) D B" by (simp add:Plane_sameside_rev)
  have P8 : "Cong (Geos (Ang (An D A C)) add Emp) (Geos (Ang (An D A C)) add Emp)" by simp
  from P6 P7 P8 have P9 : "Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An D A C)) add Emp)" by (simp add:Ang_greater_def)
  from assms have P10 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from assms have P11 : "Line_on (Li C B) D" by (simp add:Line_Bet_on)
  from assms have P12 : "Def (Tri (Tr A C B))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P10 P11 P12 have "Def (Tri (Tr A C D))" by (simp add:Tri_def_extension)
  then have P13 : "Def (Tri (Tr C A D))" by (blast intro:Tri_def_rev Tri_def_trans)
  have P14 : "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se C A)) add Emp)" by (simp add:Seg_rev)
  from assms P14 have P15 : "Eq (Geos (Seg (Se C A)) add Emp) (Geos (Seg (Se C D)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P13 P15 have P16 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An C D A)) add Emp)" by (simp add:Tri_isosceles)
  from assms have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  then have P17 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from assms have P18 : "Line_on (Li B C) D" by (simp add:Line_Bet_on)
  from assms P17 P18 have "Def (Tri (Tr A B D))" by (simp add:Tri_def_extension)
  then have P19 : "Def (Tri (Tr D B A))" by (simp add:Tri_def_rev)
  from assms P19 have P20 : "Gr (Geos (Ang (An A D C)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (simp add:Ang_external_Gr)
  from assms have P21 : "Def (Ang (An A B C))" by (simp add:Tri_to_Ang)
  have P22 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  have P23 : "\<not> Bet_Point (Se A A) B" by (simp add:Bet_end_Point)
  from assms have P24 : "Line_on (Li B C) D" by (simp add:Line_Bet_on)
  from assms have "Inv (Bet_Point (Se C D) B)" by (simp add:Bet_iff)
  then have P25 : "\<not> Bet_Point (Se C D) B" by (simp add:Inv_def)
  from P4 have P26 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P17 P21 P22 P23 P24 P25 P26 have P27 : 
      "Eq (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A B D)) add Emp) \<and> Def (Ang (An A B D))" by (simp add:Ang_Point_swap)
  have P28 : "Cong (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (simp add:Ang_roll)
  from P27 P28 have P29 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (blast intro:Ang_weektrans Ang_rev)
  have P30 : "Eq (Geos (Ang (An C D A)) add Emp) (Geos (Ang (An A D C)) add Emp)" by (simp add:Ang_roll)
  from P16 P30 have P31 : "Cong (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A D C)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P13 have P32 : "Def (Ang (An C A D))" by (simp add:Tri_to_Ang)
  then have P33 : "Def (Ang (An A D C))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P27 have P34 : "Def (Ang (An D B A))" by (blast intro:Ang_def_rev)
  from P20 P31 P32 P33 P34 have P35 : "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr)
  from P21 P29 P32 P34 P35 have P36 : "Gr (Geos (Ang (An C A D)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  have P37 : "Cong (Geos (Ang (An D A C)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (simp add:Ang_roll)
  from P32 have P38 : "Def (Ang (An D A C))" by (simp add:Ang_def_rev)
  from assms have P39 : "Def (Ang (An B A C))" by (blast intro:Tri_to_Ang Ang_def_rev Ang_def_inv)
  from P9 P32 P37 P38 P39 have P40 : "Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An C A D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq)
  from P21 P32 P36 P39 P40 show "Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr)
qed

lemma (in Congruence_Rule) Tri_Bet_Ang_Gr : 
  assumes
    "Def (Tri (Tr A B C))"
    "Bet_Point (Se A C) D"
    "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
  shows
    "Gr (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An A B D)) add Emp)"
proof -
  from assms have P1 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (simp add:Tri_isosceles)
  from assms have P2 : "Def (Tri (Tr B C A))" by (simp add:Tri_def_trans)
  from assms have P3 : "Line_on (Li C A) D" by (simp add:Line_Bet_on)
  from assms have P4 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P2 P3 P4 have "Def (Tri (Tr B C D))" by (simp add:Tri_def_extension)
  then have P5 : "Def (Tri (Tr D C B))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P6 : "Bet_Point (Se C A) D" by (simp add:Bet_rev)
  from P5 P6 have P7 : "Gr (Geos (Ang (An B D A)) add Emp) (Geos (Ang (An D C B)) add Emp)" by (simp add:Ang_external_Gr)
  from P5 have P8 : "Def (Ang (An D C B))" by (simp add:Tri_to_Ang)
  from assms have P9 : "Line_on (Li C D) A" by (simp add:Line_Bet_on)
  from assms have "Inv (Bet_Point (Se D A) C)" by (simp add:Bet_iff)
  then have P10 : "\<not> Bet_Point (Se D A) C" by (simp add:Inv_def)
  have P11 : "Line_on (Li C B) B" by (simp add:Line_on_rule)
  have P12 : "\<not> Bet_Point (Se B B) C" by (simp add:Bet_end_Point)
  from P6 have P13 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  from P5 have P14 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from P8 P9 P10 P11 P12 P13 P14 have P15 : "Eq (Geos (Ang (An D C B)) add Emp) (Geos (Ang (An A C B)) add Emp) 
    \<and> Def (Ang (An A C B))" by (simp add:Ang_Point_swap)
  from P1 P15 have P16 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D C B)) add Emp)" by (blast intro:Ang_weektrans Ang_rev)
  have P17 : "Cong (Geos (Ang (An B D A)) add Emp) (Geos (Ang (An A D B)) add Emp)" by (simp add:Ang_roll)
  from P2 have P18 : "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P19 : "Line_on (Li A C) D" by (simp add:Line_Bet_on)
  from P6 have P20 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P18 P19 P20 have "Def (Tri (Tr B A D))" by (simp add:Tri_def_extension)
  then have P21 : "Def (Ang (An B D A))" by (blast intro:Tri_to_Ang Ang_def_inv)
  then have P22 : "Def (Ang (An A D B))" by (simp add:Ang_def_rev)
  from P7 P8 P17 P21 P22 have P23 : "Gr (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An D C B)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  from assms have P24 : "Def (Ang (An A B C))" by (simp add:Tri_to_Ang)
  from P8 P16 P22 P23 P24 have P25 : "Gr (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P24 have "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Ang_def)
  then have P26 : "\<not> Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (blast intro:Eq_rev)
  from assms have "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  then have P27 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from assms have P28 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Tri_def)
  from P6 P26 P27 P28 have P29 : "Ang_inside (An C B A) D" by (simp add:Ang_inside_Bet_Point)
  then have P30 : "Plane_sameside (Li B A) D C" by (simp add:Ang_inside_def Plane_sameside_rev)
  have P31 : "Cong (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An D B A)) add Emp)" by simp
  from P29 P30 P31 have P32 : "Gr (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (simp add:Ang_greater_def)
  have P33 : "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_roll)
  from P24 have P34 : "Def (Ang (An C B A))" by (simp add:Ang_def_rev)
  from P22 have P35 : "Def (Ang (An D B A))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P24 P32 P33 P34 P35 have P36 : "Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  have P37 : "Cong (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (simp add:Ang_roll)
  from P35 have P38 : "Def (Ang (An A B D))" by (simp add:Ang_def_rev)
  from P24 P35 P36 P37 P38 have P39 : "Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P22 P24 P25 P38 P39 show "Gr (Geos (Ang (An A D B)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr Ang_rev)
qed

text\<open>Theorem24\<close>

theorem (in Congruence_Rule) Tri_isosceles_inv : 
  assumes N : 
    "Def (Tri (Tr A B C))"
    "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)"
  shows
    "\<not>\<not> Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
proof
  assume W : "\<not> Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A C)) add Emp)"
  have P1 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  from N have P3 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Tri_def)
  from N have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Tri_def)
  then have P4 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 P3 P4 have "\<exists>p. Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A p)) add Emp) 
    \<and> \<not> Bet_Point (Se p C) A \<and> Line_on (Li A C) p \<and> \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain D :: Point where P5 : "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se A D)) add Emp) 
    \<and> \<not> Bet_Point (Se D C) A \<and> Line_on (Li A C) D \<and> \<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by blast
  from W P1 P2 P3 P4 P5 have P6 : "Bet_Point (Se C A) D \<and> \<not> Bet_Point (Se A D) C
    \<or> \<not> Bet_Point (Se C A) D \<and> Bet_Point (Se A D) C" by (simp add:Seg_not_Eq_move)
  from N have P7 : "Def (Tri (Tr B C A))" by (blast intro:Tri_def_rev Tri_def_trans)
  have P8 : "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se B A)) add Emp)" by (simp add:Seg_rev)
  from P5 P8 have P9 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se A D)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P7 P9 have P10 : "Bet_Point (Se C A) D \<Longrightarrow>
    Gr (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (simp add:Tri_Seg_diagonal)
  have P11 : "Cong (Geos (Ang (An C B A)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_roll)
  from assms have P12 : "Def (Ang (An A B C))" by (simp add:Tri_to_Ang)
  then have P13 : "Def (Ang (An C B A))" by (simp add:Ang_def_rev)
  then have P14 : "Def (Ang (An B C A))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P10 P11 P12 P13 P14 have P15 : "Bet_Point (Se C A) D \<Longrightarrow>
    Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An B C A)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  from P14 have P16 : "Def (Ang (An A C B))" by (simp add:Ang_def_rev)
  have P17 : "Cong (Geos (Ang (An B C A)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (simp add:Ang_roll)
  from P12 P14 P15 P16 P17 have P18 : "Bet_Point (Se C A) D \<Longrightarrow>
    Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P12 P16 have P19 : "Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An A B C)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An A B C)) add Emp)
    \<or> \<not> Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)
    \<and> Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Ang_relation_case_fact)
  from P18 P19 have P20 : "Bet_Point (Se C A) D \<Longrightarrow>
    \<not> Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by blast
  from assms have P21 : "Def (Tri (Tr B A C))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P5 P21 have "Def (Tri (Tr B A D))" by (simp add:Tri_def_extension)
  then have P22 : "Def (Tri (Tr A B D))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P5 P22 have P23 : "Bet_Point (Se A D) C \<Longrightarrow>
    Gr (Geos (Ang (An A C B)) add Emp) (Geos (Ang (An A B C)) add Emp)" by (simp add:Tri_Bet_Ang_Gr)
  from P19 P23 have P24 : "Bet_Point (Se A D) C \<Longrightarrow>
    \<not> Cong (Geos (Ang (An A B C)) add Emp) (Geos (Ang (An A C B)) add Emp)" by blast
  from assms P6 P20 P24 show False by blast
qed

lemma (in Congruence_Rule) Tri_AAS_lemma1 : 
  assumes 
    "Def (Tri (Tr A1 B1 C1))" "Def (Tri (Tr A2 B2 C2))"
    "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)"
    "Cong (Geos (Ang (An A1 C1 B1)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)"
    "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)"
  shows
    "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)"
proof - 
  have P1 : "Line_on (Li A2 C2) A2" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li A2 C2) C2" by (simp add:Line_on_rule)
  from assms have "\<not> Eq (Geos (Poi C1) add Emp) (Geos (Poi A1) add Emp)" by (simp add:Tri_def)
  then have P3 : "\<not> Eq (Geos (Poi A1) add Emp) (Geos (Poi C1) add Emp)" by (blast intro:Eq_rev)
  from assms have P4 : "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi A2) add Emp)" by (simp add:Tri_def)
  then have P5 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi C2) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 P3 P5 have "\<exists>p. Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 p)) add Emp) 
    \<and> \<not> Bet_Point (Se p C2) A2 \<and> Line_on (Li A2 C2) p \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain C3 :: Point where P6 : "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C3)) add Emp)
    \<and> \<not> Bet_Point (Se C3 C2) A2 \<and> Line_on (Li A2 C2) C3 \<and> \<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi C3) add Emp)" by blast
  from P6 have P7 : "Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from assms P7 have P8 : "Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)" by (simp add:Tri_SAS)
  from P6 have "Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C2)) add Emp) \<Longrightarrow>
    Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  then have P9 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Seg (Se A1 C1)) add Emp) (Geos (Seg (Se A2 C2)) add Emp)" by blast
  from P1 P2 P3 P5 P6 P9 have P10 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<and> \<not> Bet_Point (Se A2 C3) C2
    \<or> \<not> Bet_Point (Se C2 A2) C3 \<and> Bet_Point (Se A2 C3) C2" by (simp add:Seg_not_Eq_move)
  from assms have P11 : "Def (Tri (Tr B2 A2 C2))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P6 P11 have "Def (Tri (Tr B2 A2 C3))" by (simp add:Tri_def_extension)
  then have P12 : "Def (Tri (Tr A2 B2 C3))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P11 have P13 : "Def (Ang (An B2 A2 C2))" by (simp add:Tri_to_Ang)
  have P14 : "Line_on (Li A2 B2) B2" by (simp add:Line_on_rule)
  have P15 : "\<not> Bet_Point (Se B2 B2) A2" by (simp add:Bet_end_Point)
  from P6 have P16 : "\<not> Bet_Point (Se C2 C3) A2" by (blast intro:Bet_rev)
  from assms have P17 : "\<not> Eq (Geos (Poi A2) add Emp) (Geos (Poi B2) add Emp)" by (simp add:Tri_def)
  from P6 P13 P14 P15 P16 P17 have P18 : 
    "Eq (Geos (Ang (An B2 A2 C2)) add Emp) (Geos (Ang (An B2 A2 C3)) add Emp) \<and> Def (Ang (An B2 A2 C3))" by (simp add:Ang_Point_swap)
  from assms P18 have P19 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C3)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from assms P6 P12 P19 have "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C3)) add Emp)" by (simp add:Tri_SAS)
  then have P20 : "Cong (Geos (Ang (An A1 C1 B1)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)" by (simp add:Tri_Cong_def)
  from assms have P21 : "Def (Ang (An A1 C1 B1))" by (blast intro:Tri_to_Ang Ang_def_inv)
  from assms have P22 : "Def (Ang (An A2 C2 B2))" by (blast intro:Tri_to_Ang Ang_def_inv)
  from P18 have P23 : "Def (Ang (An A2 C3 B2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms P20 P21 P22 P23 have P24 : "Cong (Geos (Ang (An A2 C2 B2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)" by (blast intro:Ang_trans Ang_rev)
  from P22 P23 P24 have P25 : "\<not> Gr (Geos (Ang (An A2 C2 B2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A2 C3 B2)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)" by (simp add:Ang_not_Gr)
  from assms have P26 : "Def (Tri (Tr B2 C2 A2))" by (blast intro:Tri_def_trans)
  have P27 : "Bet_Point (Se C2 A2) C3 \<Longrightarrow> \<not> Eq (Geos (Poi C3) add Emp) (Geos (Poi C2) add Emp)" by (simp add:Bet_Point_def)
  have P28 : "Bet_Point (Se A2 C3) C2 \<Longrightarrow> \<not> Eq (Geos (Poi C3) add Emp) (Geos (Poi C2) add Emp)" by (simp add:Bet_Point_def)
  from P10 P27 P28 have P29 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi C3) add Emp)" by (blast intro:Eq_rev)
  from P5 P6 have P30 : "Line_on (Li C2 A2) C3" by (blast intro:Line_rev Line_on_trans)
  from P26 P29 P30 have "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Def (Tri (Tr B2 C2 C3))" by (simp add:Tri_def_extension)
  then have P31 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Def (Tri (Tr C3 C2 B2))" by (blast intro:Tri_def_rev Tri_def_trans)
  then have P32 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> Gr (Geos (Ang (An B2 C3 A2)) add Emp) (Geos (Ang (An C3 C2 B2)) add Emp)" by (simp add:Ang_external_Gr)
  have P33 : "Cong (Geos (Ang (An B2 C3 A2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)" by (simp add:Ang_roll)
  from P31 have P34 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Def (Ang (An C3 C2 B2))" by (simp add:Tri_to_Ang)
  from P23 have P35 : "Def (Ang (An B2 C3 A2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P23 P32 P33 P34 P35 have P36 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> Gr (Geos (Ang (An A2 C3 B2)) add Emp) (Geos (Ang (An C3 C2 B2)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  have P37 : "Bet_Point (Se C2 A2) C3 \<Longrightarrow> Line_on (Li C2 C3) A2" by (simp add:Line_Bet_on)
  from P10 have P38 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> \<not> Bet_Point (Se C3 A2) C2" by (blast intro:Bet_rev)
  have P39 : "Line_on (Li C2 B2) B2" by (simp add:Line_on_rule)
  have P40 : "\<not> Bet_Point (Se B2 B2) C2" by (simp add:Bet_end_Point)
  from P13 have P41 : "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi B2) add Emp)" by (simp add:Ang_def)
  from P4 P34 P37 P38 P39 P40 P41 have "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> Eq (Geos (Ang (An C3 C2 B2)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)
    \<and> Def (Ang (An A2 C2 B2))" by (simp add:Ang_Point_swap)
  then have P42 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> Cong (Geos (Ang (An C3 C2 B2)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)" by (blast intro:Ang_weektrans)
  from P22 P23 P34 P36 P42 have P43 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se C2 A2) C3 \<Longrightarrow> Gr (Geos (Ang (An A2 C3 B2)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P31 have "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Def (Tri (Tr C2 C3 B2))" by (blast intro:Tri_def_rev Tri_def_trans)
  then have P44 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> Gr (Geos (Ang (An B2 C2 A2)) add Emp) (Geos (Ang (An C2 C3 B2)) add Emp)" by (simp add:Ang_external_Gr Bet_rev)
  have P45 : "Cong (Geos (Ang (An B2 C2 A2)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)" by (simp add:Ang_roll)
  from P26 have P46 : "Def (Ang (An B2 C2 A2))" by (simp add:Tri_to_Ang)
  from P34 have P47 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Def (Ang (An C2 C3 B2))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P22 P44 P45 P46 P47 have P48 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> Gr (Geos (Ang (An A2 C2 B2)) add Emp) (Geos (Ang (An C2 C3 B2)) add Emp)" by (blast intro:Ang_Gr_trans_Eq_Gr Ang_rev)
  have P49 : "Bet_Point (Se A2 C3) C2 \<Longrightarrow> Line_on (Li C3 C2) A2" by (simp add:Line_Bet_on)
  from P10 have P50 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> \<not> Bet_Point (Se C2 A2) C3" by (blast intro:Bet_rev)
  have P51 : "Line_on (Li C3 B2) B2" by (simp add:Line_on_rule)
  have P52 : "\<not> Bet_Point (Se B2 B2) C3" by (simp add:Bet_end_Point)
  from P6 have P53 : "\<not> Eq (Geos (Poi C3) add Emp) (Geos (Poi A2) add Emp)" by (blast intro:Eq_rev)
  from P47 have P54 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    \<not> Eq (Geos (Poi C3) add Emp) (Geos (Poi B2) add Emp)" by (simp add:Ang_def)
  from P47 P49 P50 P51 P52 P53 P54 have "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> Eq (Geos (Ang (An C2 C3 B2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)
    \<and> Def (Ang (An A2 C3 B2))" by (simp add:Ang_Point_swap)
  then have P55 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> Cong (Geos (Ang (An C2 C3 B2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)" by (blast intro:Ang_weektrans)
  from P22 P23 P47 P48 P55 have P56 : "\<not> Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp) \<Longrightarrow>
    Bet_Point (Se A2 C3) C2 \<Longrightarrow> Gr (Geos (Ang (An A2 C2 B2)) add Emp) (Geos (Ang (An A2 C3 B2)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P10 P25 P43 P56 have P57 : "Eq (Geos (Seg (Se A2 C2)) add Emp) (Geos (Seg (Se A2 C3)) add Emp)" by blast
  from P8 P57 show "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)" by blast
qed

text\<open>Theorem25\<close>

theorem (in Congruence_Rule) Tri_AAS : 
  assumes 
    "Def (Tri (Tr A1 B1 C1))" "Def (Tri (Tr A2 B2 C2))"
    "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se A2 B2)) add Emp)"
    "Cong (Geos (Ang (An A1 C1 B1)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)"
    "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp)
    \<or> Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)"
  shows
    "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)"
proof - 
  from assms have P1 : "Def (Tri (Tr B1 A1 C1))" by (blast intro:Tri_def_rev Tri_def_trans)
  from assms have P2 : "Def (Tri (Tr B2 A2 C2))" by (blast intro:Tri_def_rev Tri_def_trans)
  have P3 : "Eq (Geos (Seg (Se A1 B1)) add Emp) (Geos (Seg (Se B1 A1)) add Emp)" by (simp add:Seg_rev)
  have P4 : "Eq (Geos (Seg (Se A2 B2)) add Emp) (Geos (Seg (Se B2 A2)) add Emp)" by (simp add:Seg_rev)
  from assms P3 P4 have P5 : "Eq (Geos (Seg (Se B1 A1)) add Emp) (Geos (Seg (Se B2 A2)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  have P6 : "Eq (Geos (Ang (An A1 C1 B1)) add Emp) (Geos (Ang (An B1 C1 A1)) add Emp)" by (simp add:Ang_roll)
  from assms P6 have P7 : "Cong (Geos (Ang (An B1 C1 A1)) add Emp) (Geos (Ang (An A2 C2 B2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P8 : "Eq (Geos (Ang (An A2 C2 B2)) add Emp) (Geos (Ang (An B2 C2 A2)) add Emp)" by (simp add:Ang_roll)
  from P7 P8 have P9 : "Cong (Geos (Ang (An B1 C1 A1)) add Emp) (Geos (Ang (An B2 C2 A2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P1 P2 P5 P9 have "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Tri (Tr B1 A1 C1)) add Emp) (Geos (Tri (Tr B2 A2 C2)) add Emp)" by (simp add:Tri_AAS_lemma1)
  then have P10 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An C1 A1 B1)) add Emp) (Geos (Ang (An C2 A2 B2)) add Emp)" by (simp add:Tri_Cong_def)
  have P11 : "Eq (Geos (Ang (An C1 A1 B1)) add Emp) (Geos (Ang (An B1 A1 C1)) add Emp)" by (simp add:Ang_roll)
  from P10 P11 have P12 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An C2 A2 B2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P13 : "Eq (Geos (Ang (An C2 A2 B2)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (simp add:Ang_roll)
  from P12 P13 have "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  then have P14 : "Cong (Geos (Ang (An A1 B1 C1)) add Emp) (Geos (Ang (An A2 B2 C2)) add Emp)
    \<or> Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp)" by blast
  from assms have P15 : "Cong (Geos (Ang (An B1 A1 C1)) add Emp) (Geos (Ang (An B2 A2 C2)) add Emp) \<Longrightarrow>
    Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)" by (simp add:Tri_AAS_lemma1)
  from assms P14 P15 show "Cong (Geos (Tri (Tr A1 B1 C1)) add Emp) (Geos (Tri (Tr A2 B2 C2)) add Emp)" by blast
qed

text\<open>Theorem26\<close>

theorem (in Congruence_Rule) Seg_bisection : 
  assumes 
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
  shows
    "\<exists>p. Eq (Geos (Seg (Se A p)) add Emp) (Geos (Seg (Se p B)) add Emp) \<and> Bet_Point (Se A B) p"
proof - 
  have "\<exists>p q r. \<not> Line_on (Li A B) p \<and> \<not> Line_on (Li A B) q \<and> \<not> Line_on (Li A B) r
    \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp) 
    \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain C :: Point where P1 : "\<not> Line_on (Li A B) C" by blast
  from assms P1 have P2 : "Def (Ang (An A B C))" by (simp add:Ang_sinple_def)
  then have P2 : "Def (Ang (An C A B))" by (blast intro:Ang_def_rev Ang_def_inv)
  from assms have P3 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_rev)
  from P1 P3 have P4 : "\<not> Line_on (Li B A) C" by (simp add:Line_not_on_trans)
  from P2 P4 have "\<exists>p. Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An p B A)) add Emp) 
    \<and> Plane_diffside (Li B A) p C" by (simp add:Ang_move_diffside)
  then obtain D1 :: Point where P5 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An D1 B A)) add Emp)
    \<and> Plane_diffside (Li B A) D1 C" by blast
  then have "\<exists>p. Bet_Point (Se D1 C) p \<and> Line_on (Li B A) p \<and> \<not> Line_on (Li B A) D1 \<and> \<not> Line_on (Li B A) C" by (simp add:Plane_diffside_def)
  then have P6 : "\<not> Line_on (Li B A) D1" by blast
  from assms have P7 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P6 P7 have "Def (Ang (An B A D1))" by (simp add:Ang_sinple_def)
  then have P8 : "Def (Ang (An D1 B A))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P2 P5 P8 have "\<exists>p. Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An p B A)) add Emp)
    \<and> Eq (Geos (Ang (An D1 B A)) add Emp) (Geos (Ang (An p B A)) add Emp)
    \<and> Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se B p)) add Emp) \<and> Line_on (Li B D1) p
    \<and> \<not> Bet_Point (Se p D1) B \<and> Def (Ang (An p B A))" by (simp add:Ang_replace)
  then obtain D :: Point where P9 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An D B A)) add Emp)
    \<and> Eq (Geos (Ang (An D1 B A)) add Emp) (Geos (Ang (An D B A)) add Emp)
    \<and> Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se B D)) add Emp) \<and> Line_on (Li B D1) D
    \<and> \<not> Bet_Point (Se D D1) B \<and> Def (Ang (An D B A))" by blast
  have "Plane_diffside (Li B A) D D1 \<Longrightarrow> 
    \<exists>p. Bet_Point (Se D D1) p \<and> Line_on (Li B A) p \<and> \<not> Line_on (Li B A) D \<and> \<not> Line_on (Li B A) D1" by (simp add:Plane_diffside_def)
  then obtain B1 :: Point where P10 : "Plane_diffside (Li B A) D D1 \<Longrightarrow>
    Bet_Point (Se D D1) B1 \<and> Line_on (Li B A) B1 \<and> \<not> Line_on (Li B A) D \<and> \<not> Line_on (Li B A) D1" by blast
  then have P11 : "Plane_diffside (Li B A) D D1 \<Longrightarrow> Line_on (Li D D1) B1" by (simp add:Line_Bet_on)
  from P10 have "Plane_diffside (Li B A) D D1 \<Longrightarrow> Bet_Point (Se D D1) B1" by simp
  then have P12 : "Plane_diffside (Li B A) D D1 \<Longrightarrow>
    \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi D1) add Emp)" by (simp add:Bet_Point_def)
  have P13 : "Line_on (Li B D1) D1" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li D D1) D" by (simp add:Line_on_rule)
  have P15 : "Line_on (Li D D1) D1" by (simp add:Line_on_rule)
  from P9 have P16 : "Line_on (Li B D1) D" by simp
  from P12 P13 P14 P15 P16 have P17 : "Plane_diffside (Li B A) D D1 \<Longrightarrow>
    Eq (Geos (Lin (Li B D1)) add Emp) (Geos (Lin (Li D D1)) add Emp)" by (simp add:Line_unique)
  have P18 : "Line_on (Li B D1) B" by (simp add:Line_on_rule)
  from P17 P18 have P19 : "Plane_diffside (Li B A) D D1 \<Longrightarrow> Line_on (Li D D1) B" by (simp add:Line_on_trans)
  from P14 have P20 : "Eq (Geos (Lin (Li D D1)) add Emp) (Geos (Lin (Li B A)) add Emp) \<Longrightarrow>
    Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P10 P20 have P21 : "Plane_diffside (Li B A) D D1 \<Longrightarrow>
    \<not> Eq (Geos (Lin (Li D D1)) add Emp) (Geos (Lin (Li B A)) add Emp)" by blast
  have P22 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  from P10 P11 P19 P21 P22 have P23 : "Plane_diffside (Li B A) D D1 \<Longrightarrow>
    Eq (Geos (Poi B1) add Emp) (Geos (Poi B) add Emp)" by (simp add:Line_unique_Point)
  from P10 P23 have P24 : "Plane_diffside (Li B A) D D1 \<Longrightarrow> Bet_Point (Se D D1) B" by (blast intro:Point_Eq)
  from P9 P24 have P25 : "\<not> Plane_diffside (Li B A) D D1" by blast
  from P5 have P26 : "Plane_sameside (Li B A) C D \<Longrightarrow> Plane_diffside (Li B A) D D1" by (simp add:Plane_diffside_rev Plane_trans)
  from P25 P26 have P27 : "\<not> Plane_sameside (Li B A) C D" by blast
  from P5 have P28 : "Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow>
    Plane_diffside (Li B A) D1 D" by (blast intro:Point_Eq)
  from P25 P28 have P29 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Plane_diffside_rev)
  from P9 have "Def (Tri (Tr B A D))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P30 : "\<not> Line_on (Li B A) D" by (simp add:Tri_def_Line)
  from P4 P27 P29 P30 have "Plane_diffside (Li B A) C D" by (simp add:Plane_not_sameside_diffside)
  then have "\<exists>p. Bet_Point (Se C D) p \<and> Line_on (Li B A) p \<and> \<not> Line_on (Li B A) C \<and> \<not> Line_on (Li B A) D" by (simp add:Plane_diffside_def)
  then obtain E :: Point where P31 : "Bet_Point (Se C D) E \<and> Line_on (Li B A) E
    \<and> \<not> Line_on (Li B A) C \<and> \<not> Line_on (Li B A) D" by blast
  then have P32 : "Bet_Point (Se C D) E" by simp
  then have P33 : "Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Bet_Point (Se D C) A" by (blast intro:Point_Eq Bet_rev)
  from P9 have P34 : "Def (Tri (Tr A D B))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P33 P34 have P35 : "Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (simp add:Ang_external_Gr)
  from P32 have P36 : "Eq (Geos (Poi E) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> Bet_Point (Se C D) B" by (simp add:Point_Eq)
  from P2 have P37 : "Def (Tri (Tr B C A))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P36 P37 have P38 : "Eq (Geos (Poi E) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow>
    Gr (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Ang_external_Gr)
  have P39 : "Eq (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Ang_roll)
  from P9 P39 have P40 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  have P41 : "Eq (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (simp add:Ang_roll)
  from P40 P41 have P42 : "Cong (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P2 have P43 : "Def (Ang (An B A C))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P9 have P44 : "Def (Ang (An A B D))" by (simp add:Ang_def_rev)
  from P42 P43 P44 have P45 : "\<not> Gr (Geos (Ang (An B A C)) add Emp) (Geos (Ang (An A B D)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Ang_not_Gr)
  from P35 P45 have P46 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp)" by blast
  from P38 P45 have P47 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  have P48 : "Line_on (Li B A) B" by (simp add:Line_on_rule)  
  have P49 : "Line_on (Li B A) A" by (simp add:Line_on_rule)  
  from assms P31 P46 P47 P48 P49 have P50 : "Bet_Point (Se A E) B \<or> Bet_Point (Se E B) A 
    \<or> Bet_Point (Se B A) E" by (simp add:Bet_case)
  have P51 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li B E) A" by (simp add:Line_Bet_on)
  have P52 : "Line_on (Li B E) B" by (simp add:Line_on_rule)  
  from assms P48 P49 P51 P52 have "Bet_Point (Se A E) B \<Longrightarrow> 
    Eq (Geos (Lin (Li B E)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  then have P53 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li B E) D \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P30 P53 have P54 : "Bet_Point (Se A E) B \<Longrightarrow> \<not> Line_on (Li B E) D" by blast
  from P47 P54 have P55 : "Bet_Point (Se A E) B \<Longrightarrow> Def (Tri (Tr B E D))" by (simp add:Ang_sinple_def Ang_to_Tri)
  have P56 : "Bet_Point (Se A E) B \<Longrightarrow> Bet_Point (Se E A) B" by (simp add:Bet_rev)
  from P55 P56 have P57 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Gr (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An B E D)) add Emp)" by (simp add:Ang_external_Gr)
  have P58 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li E A) B" by (simp add:Line_Bet_on)
  have P59 : "Line_on (Li E A) A" by (simp add:Line_on_rule)  
  from assms P48 P49 P58 P59 have P60 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Eq (Geos (Lin (Li E A)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  then have P61 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li E A) C \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P31 P61 have P62 : "Bet_Point (Se A E) B \<Longrightarrow> \<not> Line_on (Li E A) C" by blast
  from P46 P62 have "Bet_Point (Se A E) B \<Longrightarrow> Def (Tri (Tr E A C))" by (simp add:Ang_sinple_def Ang_to_Tri)
  then have P63 : "Bet_Point (Se A E) B \<Longrightarrow> Def (Tri (Tr E C A))" by (blast intro:Tri_def_rev Tri_def_trans)
  from P31 P63 have P64 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Gr (Geos (Ang (An A E D)) add Emp) (Geos (Ang (An E A C)) add Emp)" by (simp add:Ang_external_Gr)
  from P63 have P65 : "Bet_Point (Se A E) B \<Longrightarrow> Def (Ang (An E A C))" by (blast intro:Tri_to_Ang Ang_def_inv)
  have P66 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li A E) B" by (simp add:Line_Bet_on)
  have "Bet_Point (Se A E) B \<Longrightarrow> Inv (Bet_Point (Se E B) A)" by (simp add:Bet_iff)
  then have P67 : "Bet_Point (Se A E) B \<Longrightarrow> \<not> Bet_Point (Se E B) A" by (simp add:Inv_def)
  have P68 : "Line_on (Li A C) C" by (simp add:Line_on_rule)  
  have P69 : "\<not> Bet_Point (Se C C) A" by (simp add:Bet_end_Point)  
  from P2 have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (simp add:Ang_def)
  then have P70 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from assms P65 P66 P67 P68 P69 P70 have P71 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Eq (Geos (Ang (An E A C)) add Emp) (Geos (Ang (An B A C)) add Emp) \<and> Def (Ang (An B A C))" by (simp add:Ang_Point_swap)
  then have P72 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Cong (Geos (Ang (An E A C)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (blast intro:Ang_weektrans Ang_rev)
  from P60 have P73 : "Bet_Point (Se A E) B \<Longrightarrow> Line_on (Li E A) D \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P31 P73 have P74 : "Bet_Point (Se A E) B \<Longrightarrow> \<not> Line_on (Li E A) D" by blast
  from P46 P74 have "Bet_Point (Se A E) B \<Longrightarrow> Def (Ang (An E A D))" by (simp add:Ang_sinple_def)
  then have P75 : "Bet_Point (Se A E) B \<Longrightarrow> Def (Ang (An A E D))" by (blast intro:Ang_def_rev Ang_def_inv)
  from P64 P65 P71 P72 P75 have P76 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Gr (Geos (Ang (An A E D)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  have "Bet_Point (Se A E) B \<Longrightarrow> Inv (Bet_Point (Se B A) E)" by (simp add:Bet_iff)
  then have "Bet_Point (Se A E) B \<Longrightarrow> \<not> Bet_Point (Se B A) E" by (simp add:Inv_def)
  then have P77 : "Bet_Point (Se A E) B \<Longrightarrow> \<not> Bet_Point (Se A B) E" by (blast intro:Bet_rev)
  have P78 : "Line_on (Li E D) D" by (simp add:Line_on_rule)  
  have P79 : "\<not> Bet_Point (Se D D) E" by (simp add:Bet_end_Point)  
  from P47 have P80 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P32 have "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def)
  then have P81 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P58 P75 P77 P78 P79 P80 P81 have P82 : "Bet_Point (Se A E) B \<Longrightarrow>
    Eq (Geos (Ang (An A E D)) add Emp) (Geos (Ang (An B E D)) add Emp) \<and> Def (Ang (An B E D))" by (simp add:Ang_Point_swap)
  then have P83 : "Bet_Point (Se A E) B \<Longrightarrow>
    Cong (Geos (Ang (An A E D)) add Emp) (Geos (Ang (An B E D)) add Emp)" by (blast intro:Ang_weektrans)
  from P9 P57 P75 P82 P83 have P84 : "Bet_Point (Se A E) B \<Longrightarrow> 
    Gr (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An A E D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P9 P71 P75 P76 P84 have P85 : "Bet_Point (Se A E) B \<Longrightarrow>
    Gr (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr)
  from P9 P40 P71 have P86 : "Bet_Point (Se A E) B \<Longrightarrow>
    \<not> Gr (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An B A C)) add Emp)" by (simp add:Ang_not_Gr)
  from P85 P86 have P87 : "\<not> Bet_Point (Se A E) B" by blast
  have P88 : "Bet_Point (Se E B) A \<Longrightarrow> Line_on (Li E A) B" by (simp add:Line_Bet_on)
  from assms P48 P49 P59 P88 have P89 : "Bet_Point (Se E B) A \<Longrightarrow> 
    Eq (Geos (Lin (Li E A)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  then have P90 : "Bet_Point (Se E B) A \<Longrightarrow> Line_on (Li E A) C \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P31 P90 have P91 : "Bet_Point (Se E B) A \<Longrightarrow> \<not> Line_on (Li E A) C" by blast
  from P46 P91 have "Bet_Point (Se E B) A \<Longrightarrow> Def (Ang (An E A C))" by (simp add:Ang_sinple_def)
  then have P92 : "Bet_Point (Se E B) A \<Longrightarrow> Def (Tri (Tr A E C))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P93 : "Bet_Point (Se E B) A \<Longrightarrow> Gr (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An A E C)) add Emp)" by (simp add:Ang_external_Gr)
  have P94 : "Bet_Point (Se E B) A \<Longrightarrow> Line_on (Li B E) A" by (simp add:Line_Bet_on)
  from assms P48 P49 P52 P94 have "Bet_Point (Se E B) A \<Longrightarrow> 
    Eq (Geos (Lin (Li B E)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  then have P95 : "Bet_Point (Se E B) A \<Longrightarrow> Line_on (Li B E) D \<Longrightarrow> Line_on (Li B A) D" by (simp add:Line_on_trans)
  from P31 P95 have P96 : "Bet_Point (Se E B) A \<Longrightarrow> \<not> Line_on (Li B E) D" by blast
  from P47 P96 have "Bet_Point (Se E B) A \<Longrightarrow> Def (Ang (An B E D))" by (simp add:Ang_sinple_def)
  then have P97 : "Bet_Point (Se E B) A \<Longrightarrow> Def (Tri (Tr E D B))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P32 have P98 : "Bet_Point (Se D C) E" by (simp add:Bet_rev)
  from P97 P98 have P99 : "Bet_Point (Se E B) A \<Longrightarrow> 
    Gr (Geos (Ang (An B E C)) add Emp) (Geos (Ang (An E B D)) add Emp)" by (simp add:Ang_external_Gr)
  from P92 have P100 : "Bet_Point (Se E B) A \<Longrightarrow> Def (Ang (An A E C))" by (simp add:Tri_to_Ang)
  have "Bet_Point (Se E B) A \<Longrightarrow> Inv (Bet_Point (Se B A) E)" by (simp add:Bet_iff)
  then have "Bet_Point (Se E B) A \<Longrightarrow> \<not> Bet_Point (Se B A) E" by (simp add:Inv_def)
  then have P101 : "Bet_Point (Se E B) A \<Longrightarrow> \<not> Bet_Point (Se A B) E" by (blast intro:Bet_rev)
  have P102 : "Line_on (Li E C) C" by (simp add:Line_on_rule)  
  have P103 : "\<not> Bet_Point (Se C C) E" by (simp add:Bet_end_Point)  
  from P32 have P104 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P80 P88 P100 P101 P102 P103 P104 have P105 : "Bet_Point (Se E B) A \<Longrightarrow>
    Eq (Geos (Ang (An A E C)) add Emp) (Geos (Ang (An B E C)) add Emp) \<and> Def (Ang (An B E C))" by (simp add:Ang_Point_swap)
  then have P106 : "Bet_Point (Se E B) A \<Longrightarrow>
    Cong (Geos (Ang (An A E C)) add Emp) (Geos (Ang (An B E C)) add Emp)" by (blast intro:Ang_weektrans)
  have P107 : "Bet_Point (Se E B) A \<Longrightarrow> Line_on (Li B A) E" by (simp add:Line_Bet_on)
  have "Bet_Point (Se E B) A \<Longrightarrow> Inv (Bet_Point (Se A E) B)" by (simp add:Bet_iff)
  then have P108 : "Bet_Point (Se E B) A \<Longrightarrow> \<not> Bet_Point (Se A E) B" by (simp add:Inv_def)
  have P109 : "Line_on (Li B D) D" by (simp add:Line_on_rule)  
  have P110 : "\<not> Bet_Point (Se D D) B" by (simp add:Bet_end_Point)
  from P44 have P111 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Ang_def)
  from P44 P47 P107 P108 P109 P110 P111 have P112 : "Bet_Point (Se E B) A \<Longrightarrow>
    Eq (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An E B D)) add Emp) \<and> Def (Ang (An E B D))" by (simp add:Ang_Point_swap)
  then have P113 : "Bet_Point (Se E B) A \<Longrightarrow>
    Cong (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An E B D)) add Emp)" by (blast intro:Ang_weektrans)
  from P2 P93 P100 P105 P106 have P114 : "Bet_Point (Se E B) A \<Longrightarrow>
    Gr (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An B E C)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq)
  from P44 P99 P105 P112 P113 have P115 : "Bet_Point (Se E B) A \<Longrightarrow>
    Gr (Geos (Ang (An B E C)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Eq Ang_rev)
  from P2 P44 P105 P114 P115 have P116 : "Bet_Point (Se E B) A \<Longrightarrow>
    Gr (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_Gr_trans_Gr_Gr)
  from P9 P41 have P117 : "Cong (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P2 P44 P117 have P118 : "\<not> Gr (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An A B D)) add Emp)
    \<and> \<not> Gr (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An C A B)) add Emp)" by (simp add:Ang_not_Gr)
  from P116 P118 have P119 : "\<not> Bet_Point (Se E B) A" by blast
  from P50 P87 P119 have P120 : "Bet_Point (Se B A) E" by blast
  then have P121 : "Line_on (Li B E) A" by (simp add:Line_Bet_on)
  from assms P48 P49 P52 P121 have "Eq (Geos (Lin (Li B E)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  then have P122 : "Line_on (Li B E) C \<Longrightarrow> Line_on (Li B A) C" by (simp add:Line_on_trans)
  from P31 P122 have P123 : "\<not> Line_on (Li B E) C" by blast
  from P47 P123 have P124 : "Def (Ang (An B E C))" by (simp add:Ang_sinple_def)
  from P32 P120 P124 have P125 : "Cong (Geos (Ang (An C E A)) add Emp) (Geos (Ang (An B E D)) add Emp)" by (simp add:Ang_vertical)
  have P126 : "Eq (Geos (Seg (Se A C)) add Emp) (Geos (Seg (Se C A)) add Emp)" by (simp add:Seg_rev)
  have P127 : "Eq (Geos (Seg (Se B D)) add Emp) (Geos (Seg (Se D B)) add Emp)" by (simp add:Seg_rev)
  from P9 P126 P127 have P128 : "Eq (Geos (Seg (Se C A)) add Emp) (Geos (Seg (Se D B)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  have P129 : "Eq (Geos (Ang (An B E D)) add Emp) (Geos (Ang (An D E B)) add Emp)" by (simp add:Ang_roll)
  from P125 P129 have P130 : "Cong (Geos (Ang (An C E A)) add Emp) (Geos (Ang (An D E B)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P120 have P131 : "Line_on (Li A B) E" by (simp add:Line_Bet_on)
  from P119 have P132 : "\<not> Bet_Point (Se B E) A" by (blast intro:Bet_rev)
  from P46 have P133 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  from P2 P68 P69 P70 P131 P132 P133 have P134 : 
    "Eq (Geos (Ang (An C A B)) add Emp) (Geos (Ang (An C A E)) add Emp) \<and> Def (Ang (An C A E))" by (simp add:Ang_Point_swap)
  then have P135 : "Def (Tri (Tr C A E))" by (simp add:Ang_to_Tri)
  from P9 P134 have P136 : "Cong (Geos (Ang (An C A E)) add Emp) (Geos (Ang (An D B A)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P9 have P137 : "Def (Ang (An D B A))" by simp
  from P31 P47 P87 P109 P110 P111 P137 have P138 :
    "Eq (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An D B E)) add Emp) \<and> Def (Ang (An D B E))" by (simp add:Ang_Point_swap)
  then have P139 : "Def (Tri (Tr D B E))" by (simp add:Ang_to_Tri)
  from P136 P138 have P140 : "Cong (Geos (Ang (An C A E)) add Emp) (Geos (Ang (An D B E)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P128 P130 P135 P139 P140 have "Cong (Geos (Tri (Tr C A E)) add Emp) (Geos (Tri (Tr D B E)) add Emp)" by (simp add:Tri_AAS)
  then have P141 : "Eq (Geos (Seg (Se A E)) add Emp) (Geos (Seg (Se B E)) add Emp)" by (simp add:Tri_Cong_def)
  have P142 : "Eq (Geos (Seg (Se B E)) add Emp) (Geos (Seg (Se E B)) add Emp)" by (simp add:Seg_rev)
  from P141 P142 have P143 : "Eq (Geos (Seg (Se A E)) add Emp) (Geos (Seg (Se E B)) add Emp)" by (blast intro:Eq_trans)
  from P120 have P144 : "Bet_Point (Se A B) E" by (simp add:Bet_rev)
  from P143 P144 show "\<exists>p. Eq (Geos (Seg (Se A p)) add Emp) (Geos (Seg (Se p B)) add Emp) \<and> Bet_Point (Se A B) p" by blast
qed

theorem (in Congruence_Rule) Ang_bisection : 
  assumes 
    "Def (Ang (An A B C))"
  shows
    "\<exists>p. Cong (Geos (Ang (An A B p)) add Emp) (Geos (Ang (An p B C)) add Emp) 
    \<and> Ang_inside (An A B C) p \<and> Def (Ang (An A B p)) \<and> Def (Ang (An p B C))"
proof - 
  have P1 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from assms have P3 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)" by (simp add:Ang_def)
  from assms have "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Ang_def)
  then have P4 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P1 P2 P3 P4 have "\<exists>p. Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B p)) add Emp) 
    \<and> \<not> Bet_Point (Se p C) B \<and> Line_on (Li B C) p \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi p) add Emp)" by (simp add:Seg_move_sameside)
  then obtain C2 :: Point where P5 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B C2)) add Emp)
    \<and> \<not> Bet_Point (Se C2 C) B \<and> Line_on (Li B C) C2 \<and> \<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C2) add Emp)" by blast
  then have P6 : "Line_on (Li B C) C2" by simp
  then have P7 : "Eq (Geos (Poi C2) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li B C) A" by (simp add:Point_Eq)
  from assms have P8 : "Def (Tri (Tr A B C))" by (simp add:Ang_to_Tri)
  then have P9 : "\<not> Line_on (Li B C) A" by (simp add:Tri_def_Line)
  from P7 P9 have P10 : "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi A) add Emp)" by blast
  then have "\<exists>p. Eq (Geos (Seg (Se C2 p)) add Emp) (Geos (Seg (Se p A)) add Emp) \<and> Bet_Point (Se C2 A) p" by (simp add:Seg_bisection)
  then obtain D :: Point where P11 : "Eq (Geos (Seg (Se C2 D)) add Emp) (Geos (Seg (Se D A)) add Emp)
    \<and> Bet_Point (Se C2 A) D" by blast
  have P12 : "Line_on (Li B A) B" by (simp add:Line_on_rule)
  from P1 P5 P6 P12 have P13 : "Line_on (Li B A) C2 \<Longrightarrow>
    Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Line_unique)
  from assms have P14 : "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C)) add Emp)" by (simp add:Ang_def)
  from P13 P14 have P15 : "\<not> Line_on (Li B A) C2" by blast
  from P11 have P16 : "Bet_Point (Se C2 A) D" by simp
  then have P17 : "Line_on (Li C2 A) D" by (simp add:Line_Bet_on)
  have P18 : "Line_on (Li C2 A) A" by (simp add:Line_on_rule)
  have P19 : "Line_on (Li B A) A" by (simp add:Line_on_rule)
  from P16 have P20 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P17 P18 P19 P20 have P21 : "Line_on (Li B A) D \<Longrightarrow>
    Eq (Geos (Lin (Li C2 A)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_unique)
  have P22 : "Line_on (Li C2 A) C2" by (simp add:Line_on_rule)
  from P21 P22 have P23 : "Line_on (Li B A) D \<Longrightarrow> Line_on (Li B A) C2" by (simp add:Line_on_trans)
  from P15 P23 have P24 : "\<not> Line_on (Li B A) D" by blast
  from P4 P24 have "Def (Ang (An B A D))" by (simp add:Ang_sinple_def)
  then have P25 : "Def (Tri (Tr A B D))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  from P4 P15 have P26 : "Def (Ang (An B A C2))" by (simp add:Ang_sinple_def)
  then have "Def (Tri (Tr C2 B A))" by (blast intro:Ang_to_Tri Tri_def_rev Tri_def_trans)
  then have P27 : "\<not> Line_on (Li C2 B) A" by (simp add:Tri_def_Line)
  have P28 : "Line_on (Li C2 B) C2" by (simp add:Line_on_rule)
  from P16 have P29 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi C2) add Emp)" by (simp add:Bet_Point_def)
  from P17 P22 P28 P29 have P30 : "Line_on (Li C2 B) D \<Longrightarrow>
    Eq (Geos (Lin (Li C2 A)) add Emp) (Geos (Lin (Li C2 B)) add Emp)" by (simp add:Line_unique)
  from P18 P30 have P31 : "Line_on (Li C2 B) D \<Longrightarrow> Line_on (Li C2 B) A" by (simp add:Line_on_trans)
  from P27 P31 have P32 : "\<not> Line_on (Li C2 B) D" by blast
  from P5 have P33 : "\<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P32 P33 have "Def (Ang (An C2 B D))" by (simp add:Ang_sinple_def)
  then have P34 : "Def (Tri (Tr C2 B D))" by (simp add:Ang_to_Tri)
  have P35 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se A B)) add Emp)" by (simp add:Seg_rev)
  have P36 : "Eq (Geos (Seg (Se B C2)) add Emp) (Geos (Seg (Se C2 B)) add Emp)" by (simp add:Seg_rev)
  from P5 have P37 : "Eq (Geos (Seg (Se B A)) add Emp) (Geos (Seg (Se B C2)) add Emp)" by simp
  from P35 P36 P37 have P38 : "Eq (Geos (Seg (Se A B)) add Emp) (Geos (Seg (Se C2 B)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  have P39 : "Eq (Geos (Seg (Se C2 D)) add Emp) (Geos (Seg (Se D C2)) add Emp)" by (simp add:Seg_rev)
  from P11 P39 have P40 : "Eq (Geos (Seg (Se D A)) add Emp) (Geos (Seg (Se D C2)) add Emp)" by (blast intro:Eq_rev Eq_trans)
  from P25 P34 P38 P40 have "Cong (Geos (Tri (Tr A B D)) add Emp) (Geos (Tri (Tr C2 B D)) add Emp)" by (simp add:Tri_SSS)
  then have P41 : "Cong (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An D B C2)) add Emp)" by (simp add:Tri_Cong_def)
  have P42 : "Eq (Geos (Ang (An D B A)) add Emp) (Geos (Ang (An A B D)) add Emp)" by (simp add:Ang_roll)
  from P41 P42 have P43 : "Cong (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An D B C2)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P34 have P44 : "Def (Ang (An D B C2))" by (blast intro:Tri_to_Ang Ang_def_rev Ang_def_inv)
  have P45 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  have P46 : "\<not> Bet_Point (Se D D) B" by (simp add:Bet_end_Point)
  from P33 have P47 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C2) add Emp)" by (blast intro:Eq_rev)
  from P3 P6 P47 have P48 : "Line_on (Li B C2) C" by (simp add:Line_on_rev)
  from P34 have P49 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Tri_def)
  from P3 P5 P44 P45 P46 P48 P49 have P50 : "Eq (Geos (Ang (An D B C2)) add Emp) (Geos (Ang (An D B C)) add Emp)
    \<and> Def (Ang (An D B C))" by (simp add:Ang_Point_swap)
  from P43 P50 have P51 : "Cong (Geos (Ang (An A B D)) add Emp) (Geos (Ang (An D B C)) add Emp)" by (blast intro:Ang_weektrans Ang_rev Eq_rev)
  from P25 have P52 : "Def (Ang (An A B D))" by (simp add:Tri_to_Ang)
  from P26 have P53 : "Def (Ang (An A B C2))" by (blast intro:Ang_def_rev Ang_def_inv)
  then have P54 : "\<not> Eq (Geos (Lin (Li B A)) add Emp) (Geos (Lin (Li B C2)) add Emp)" by (simp add:Ang_def)
  from P16 have P55 : "Bet_Point (Se A C2) D" by (simp add:Bet_rev)
  from P4 P5 P54 P55 have P56 : "Ang_inside (An A B C2) D" by (simp add:Ang_inside_Bet_Point)
  have P57 : "\<not> Bet_Point (Se A A) B" by (simp add:Bet_end_Point)
  from P3 P4 P5 P6 P19 P53 P56 P57 have P58 : "Ang_inside (An A B C) D" by (simp add:Ang_inside_trans)
  from P50 P51 P52 P58 show "\<exists>p. Cong (Geos (Ang (An A B p)) add Emp) (Geos (Ang (An p B C)) add Emp) 
    \<and> Ang_inside (An A B C) p \<and> Def (Ang (An A B p)) \<and> Def (Ang (An p B C))" by blast
qed


end
  