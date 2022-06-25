(*<*)
theory Order imports Incidence begin
(*>*)

section\<open>Order\<close>

locale Definition_2 = Incidence_Rule +
  fixes Line_on_Seg :: "Line \<Rightarrow> Segment \<Rightarrow> bool"
    and Bet_Point :: "Segment \<Rightarrow> Point \<Rightarrow> bool"
    and Seg_on_Seg :: "Segment \<Rightarrow> Segment \<Rightarrow> bool"
    and Line_on_Line :: "Line \<Rightarrow> Line \<Rightarrow> bool"
    and Plane_sameside :: "Line \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"
    and Plane_diffside :: "Line \<Rightarrow> Point \<Rightarrow> Point \<Rightarrow> bool"
  assumes Bet_Point_def : "\<lbrakk>Bet_Point (Se p1 p2) p3\<rbrakk> \<Longrightarrow> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) 
        \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp) \<and> \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)"
    and Bet_rev : "\<lbrakk>Bet_Point (Se p1 p2) p3\<rbrakk> \<Longrightarrow> Bet_Point (Se p2 p1) p3"
    and Line_Bet_exist : "\<lbrakk>Bet_Point (Se p1 p2) p3\<rbrakk> \<Longrightarrow> \<exists>l. Line_on l p1 \<and> Line_on l p2 \<and> Line_on l p3"
    and Seg_rev : "Eq (Geos (Seg (Se p1 p2)) add Emp) (Geos (Seg (Se p2 p1)) add Emp)"
    and Plane_sameside_def : "Plane_sameside l1 p1 p2 \<longleftrightarrow> \<not> Line_on_Seg l1 (Se p1 p2) \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2 \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    and Plane_diffside_def : "Plane_diffside l1 p1 p2 \<longleftrightarrow> (\<exists>p. Bet_Point (Se p1 p2) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2)"
        
locale Axiom_2 = Definition_2 +
  assumes Bet_extension : "\<lbrakk>Line_on l1 p1; Line_on l1 p2; \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)\<rbrakk> \<Longrightarrow> \<exists>p. Bet_Point (Se p1 p) p2 \<and> Line_on l1 p"
    and Bet_iff : "\<lbrakk>Bet_Point (Se p1 p2) p3\<rbrakk> \<Longrightarrow> Inv (Bet_Point (Se p2 p3) p1) \<and> Inv (Bet_Point (Se p3 p1) p2)"
    and Pachets_axiom : "\<lbrakk>\<not> Line_on (Li p1 p2) p3; Bet_Point (Se p1 p2) p4; Line_on l1 p4;
        \<not> Line_on l1 p1; \<not> Line_on l1 p2; \<not> Line_on l1 p3\<rbrakk> \<Longrightarrow> 
        Line_on_Seg l1 (Se p1 p3) \<and> \<not> Line_on_Seg l1 (Se p2 p3)
        \<or> Line_on_Seg l1 (Se p2 p3) \<and> \<not> Line_on_Seg l1 (Se p1 p3)"
    and Seg_move_sameside : "\<lbrakk>Line_on l1 p1; Line_on l1 p2; \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp);
        \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p4) add Emp)\<rbrakk> \<Longrightarrow> 
        \<exists>p. Eq (Geos (Seg (Se p3 p4)) add Emp) (Geos (Seg (Se p1 p)) add Emp) \<and> \<not> Bet_Point (Se p p2) p1 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)"
    and Seg_move_diffside : "\<lbrakk>Line_on l1 p1; Line_on l1 p2; \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp);
        \<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p4) add Emp)\<rbrakk> \<Longrightarrow> 
        \<exists>p. Eq (Geos (Seg (Se p3 p4)) add Emp) (Geos (Seg (Se p1 p)) add Emp) \<and> Bet_Point (Se p p2) p1 \<and> Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)"

locale Order_Rule = Axiom_2 +
  assumes Bet_Point_Eq : "\<lbrakk>Bet_Point (Se p1 p2) p3; Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)\<rbrakk> \<Longrightarrow> Bet_Point (Se p4 p2) p3"
    and Line_on_Seg_rule : "Line_on_Seg l1 (Se p1 p2) \<longleftrightarrow> (\<exists>p. Line_on l1 p \<and> Bet_Point (Se p1 p2) p)"
    and Seg_on_Seg_rule : "Seg_on_Seg (Se p1 p2) (Se p3 p4) \<longleftrightarrow> (\<exists>p. Bet_Point (Se p1 p2) p \<and> Bet_Point (Se p3 p4) p)"
    and Line_on_Line_rule : "Line_on_Line l1 l2 \<longleftrightarrow> (\<exists>p. Line_on l1 p \<and> Line_on l2 p)"
    and Seg_Point_Eq : "\<lbrakk>Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)\<rbrakk> \<Longrightarrow> Eq (Geos (Seg (Se p3 p1)) add Emp) (Geos (Seg (Se p3 p2)) add Emp)"

lemma(in Order_Rule) Line_Bet_on : 
  assumes
    "Bet_Point (Se p1 p2) p3"
  shows "Line_on (Li p1 p2) p3" and "Line_on (Li p2 p1) p3"
    and "Line_on (Li p2 p3) p1" and "Line_on (Li p3 p2) p1"
    and "Line_on (Li p1 p3) p2" and "Line_on (Li p3 p1) p2"
proof -
  from assms have "\<exists>l. Line_on l p1 \<and> Line_on l p2 \<and> Line_on l p3" by (blast intro:Line_Bet_exist)
  then obtain l1 :: Line where P1 : "Line_on l1 p1 \<and> Line_on l1 p2 \<and> Line_on l1 p3" by blast
  from assms have P2 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  have P3 : "Line_on (Li p1 p2) p1 \<and> Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from P1 have P4 : "Line_on l1 p1" by simp
  from P1 have P5 : "Line_on l1 p2" by simp
  from P2 P3 P4 P5 have P6 : "Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  from P1 P6 show P7 : "Line_on (Li p1 p2) p3" by (simp add:Line_on_trans)
  from assms have P8 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  from P2 P7 P8 show "Line_on (Li p1 p3) p2" by (blast intro:Line_on_rev Eq_rev)
  from P2 P7 P8 show "Line_on (Li p3 p1) p2" by (blast intro:Line_on_trans Line_on_rev Eq_rev Line_rev)
  from P2 P7 show "Line_on (Li p2 p1) p3" by (blast intro:Line_on_trans Line_rev)
  from assms have P9 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P2 P7 P9 show "Line_on (Li p2 p3) p1" by (blast intro:Line_on_rev Line_on_trans Line_rev Eq_rev)
  from P9 have P10 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p2) add Emp)" by (blast intro:Eq_rev)
  from assms P2 P7 P8 P10 show "Line_on (Li p3 p2) p1" by (blast intro:Line_on_rev Bet_Point_def Line_on_trans Eq_rev Line_rev)
qed

lemma(in Order_Rule) Line_Bet_not_Eq :
  assumes N :
    "Bet_Point (Se p1 p2) p3"
    "\<not> Line_on (Li p1 p2) p4"
  shows "\<not> Eq (Geos (Lin (Li p4 p3)) add Emp) (Geos (Lin (Li p4 p2)) add Emp)" 
proof 
  assume W : "Eq (Geos (Lin (Li p4 p3)) add Emp) (Geos (Lin (Li p4 p2)) add Emp)" 
  have P1 : "Line_on (Li p4 p3) p3" by (simp add:Line_on_rule)
  from W P1 have P2 : "Line_on (Li p4 p2) p3" by (simp add:Line_on_trans)
  have P3 : "Line_on (Li p4 p2) p2" by (simp add:Line_on_rule)
  from N have P4 : "Line_on (Li p1 p2) p3" by (simp add:Line_Bet_on)
  have P5 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from assms have P6 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P2 P3 P4 P5 P6 have P7 : "Eq (Geos (Lin (Li p4 p2)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  have P8 : "Line_on (Li p4 p2) p4" by (simp add:Line_on_rule)
  from P7 P8 have P9 : "Line_on (Li p1 p2) p4" by (simp add:Line_on_trans)
  from N P9 show False by simp
qed

text\<open>Theorem3\<close>

theorem(in Order_Rule) Seg_density :
  assumes "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)"
  shows "\<exists>p. Bet_Point (Se A C) p" 
proof -
  have "\<exists>p q r. \<not> Line_on (Li A C) p \<and> \<not> Line_on (Li A C) q \<and> \<not> Line_on (Li A C) r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain E :: Point where P1 : "\<not> Line_on (Li A C) E" by blast
  then have P2 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by (simp add:Line_not_on_Point)
  have P3 : "Line_on (Li A E) A \<and> Line_on (Li A E) E" by (simp add:Line_on_rule)
  from P2 P3 have "\<exists>p. Bet_Point (Se A p) E \<and> Line_on (Li A E) p" by (simp add:Bet_extension)
  then obtain F :: Point where P4 : "Bet_Point (Se A F) E \<and> Line_on (Li A E) F" by blast
  then have P5 : "Line_on (Li A F) E" by (simp add:Line_Bet_on)
  from P4 have P6 : "Bet_Point (Se A F) E" by simp
  from P6 have P7 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi F) add Emp)" by (simp add:Bet_Point_def)
  from P2 P4 P6 P7 have P8 : "Line_on (Li A E) F" by (simp add:Line_on_rev)
  from assms P1 have P9 : "\<not> Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li A E)) add Emp)" by (simp add:Line_not_Eq)
  have P10 : "Line_on (Li A F) A" by (simp add:Line_on_rule)
  from P2 P3 P5 P10 have P11 : "Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li A F)) add Emp)" by (blast intro:Line_unique)
  from P9 P11 have P12 : "\<not> Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li A F)) add Emp)" by (simp add:Eq_not_trans)
  from assms P7 P12 have P13 : "\<not> Line_on (Li A C) F" by (simp add:Line_not_Eq_on)
  from assms P7 P13 have P14 : "\<not> Line_on (Li A F) C" by (blast intro:Line_on_rev)
  have "Line_on (Li A F) F" by (simp add:Line_on_rule)
  then have P15 : "Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li A F) C" by (simp add:Point_Eq)
  from P14 P15 have P16 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp)" by blast
  have P17 : "Line_on (Li F C) F \<and> Line_on (Li F C) C" by (simp add:Line_on_rule)
  from P16 P17 have "\<exists>p. Bet_Point (Se F p) C \<and> Line_on (Li F C) p" by (simp add:Bet_extension)
  then obtain G :: Point where P18 : "Bet_Point (Se F G) C \<and> Line_on (Li F C) G" by blast
  from P18 have P19 : "Line_on (Li F G) C" by (simp add:Line_Bet_on)
  from P18 have P20 : "Bet_Point (Se F G) C" by simp
  then have P21 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from P20 have P22 : "Line_on (Li F C) G" by (simp add:Line_Bet_on)
  from P7 P14 P21 P22 have P23 : "\<not> Line_on (Li A F) G" by (simp add:Line_cross_not_on)
  from P6 P23 have P24 : "\<not> Eq (Geos (Lin (Li G E)) add Emp) (Geos (Lin (Li G F)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P5 have P25 : "Eq (Geos (Poi E) add Emp) (Geos (Poi G) add Emp) \<Longrightarrow> Line_on (Li A F) G" by (simp add:Point_Eq)
  from P23 P25 have P26 : "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  from P21 have P27 : "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi F) add Emp)" by (blast intro:Eq_rev)
  from P24 P26 P27 have P28 : "\<not> Line_on (Li G E) F" by (simp add:Line_not_Eq_on)
  from P26 P28 have P29 : "\<not> Line_on (Li E G) F" by (blast intro:Line_rev Line_on_trans Eq_rev)
  have P30 : "Line_on (Li E G) E" by (simp add:Line_on_rule)
  have P31 : "Line_on (Li A E) E" by (simp add:Line_on_rule)
  have P32 : "Line_on (Li A E) A" by (simp add:Line_on_rule)
  from P2 P30 P31 P32 have P33 : "Line_on (Li E G) A \<Longrightarrow> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li E G)) add Emp)" by (simp add:Line_unique)
  from P8 P33 have P34 : "Line_on (Li E G) A \<Longrightarrow> Line_on (Li E G) F" by (simp add:Line_on_trans)
  from P29 P34 have P35 : "\<not> Line_on (Li E G) A" by blast
  have P36 : "Line_on (Li E G) G" by (simp add:Line_on_rule)
  have P37 : "Line_on (Li F G) G" by (simp add:Line_on_rule)
  from P20 have P38 : "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P19 P36 P37 P38 have P39 : "Line_on (Li E G) C \<Longrightarrow> Eq (Geos (Lin (Li F G)) add Emp) (Geos (Lin (Li E G)) add Emp)" by (simp add:Line_unique)
  have P40 : "Line_on (Li F G) F" by (simp add:Line_on_rule)
  from P39 P40 have P41 : "Line_on (Li E G) C \<Longrightarrow> Line_on (Li E G) F" by (simp add:Line_on_trans)
  from P29 P41 have P42 : "\<not> Line_on (Li E G) C" by blast
  from P6 P14 P29 P30 P35 P42 have P43 : "Line_on_Seg (Li E G) (Se A C) \<and> \<not> Line_on_Seg (Li E G) (Se F C) \<or> Line_on_Seg (Li E G) (Se F C) \<and> \<not> Line_on_Seg (Li E G) (Se A C)" by (simp add:Pachets_axiom)
  then have "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> \<exists>p. Line_on (Li E G) p \<and> Bet_Point (Se F C) p" by (simp add:Line_on_Seg_rule)
  then obtain D :: Point where P44 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> Line_on (Li E G) D \<and> Bet_Point (Se F C) D" by blast
  from P44 have P46 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> Bet_Point (Se F C) D" by simp
  from P46 have "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp)" by (simp add:Bet_Point_def)
  from P46 have P47 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> Line_on (Li F D) C" by (simp add:Line_Bet_on)
  have P48 : "Line_on (Li F D) F" by (simp add:Line_on_rule)
  have P49 : "Line_on (Li F G) F" by (simp add:Line_on_rule)
  from P16 P19 P47 P48 P49 have P50 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow>  
    Eq (Geos (Lin (Li F D)) add Emp) (Geos (Lin (Li F G)) add Emp)" by (simp add:Line_unique)
  have P51 : "Line_on (Li F D) D" by (simp add:Line_on_rule)
  from P50 P51 have P52 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> Line_on (Li F G) D" by (simp add:Line_on_trans)
  have P53 : "Line_on (Li F G) G" by (simp add:Line_on_rule)
  have P54 : "Line_on (Li E G) G" by (simp add:Line_on_rule)
  from P46 have P55 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> Eq (Geos (Poi D) add Emp) (Geos (Poi G) add Emp) 
    \<Longrightarrow> Bet_Point (Se F C) G" by (simp add:Point_Eq)
  from P20 have "Inv (Bet_Point (Se G C) F) \<and> Inv (Bet_Point (Se C F) G)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se C F) G" by (simp add:Inv_def)
  then have P56 : "\<not> Bet_Point (Se F C) G" by (blast intro:Bet_rev)
  from P55 P56 have P57 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> \<not> Eq (Geos (Poi D) add Emp) (Geos (Poi G) add Emp)" by blast
  from P44 P52 P53 P54 P57 have P58 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> 
    Eq (Geos (Lin (Li E G)) add Emp) (Geos (Lin (Li F G)) add Emp)" by (blast intro:Line_unique)
  from P26 have P59 : "Eq (Geos (Lin (Li E G)) add Emp) (Geos (Lin (Li G E)) add Emp)" by (simp add:Line_rev Eq_rev)
  from P27 have P60 : "Eq (Geos (Lin (Li F G)) add Emp) (Geos (Lin (Li G F)) add Emp)" by (simp add:Line_rev Eq_rev)
  from P58 P59 P60 have P61 : "Line_on_Seg (Li E G) (Se F C) \<Longrightarrow> 
    Eq (Geos (Lin (Li G E)) add Emp) (Geos (Lin (Li G F)) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P24 P61 have P62 : "\<not> Line_on_Seg (Li E G) (Se F C)" by blast
  from P43 P62 have "Line_on_Seg (Li E G) (Se A C) \<and> \<not> Line_on_Seg (Li E G) (Se F C)" by blast
  then have "\<exists>p. Line_on (Li E G) p \<and> Bet_Point (Se A C) p" by (simp add:Line_on_Seg_rule)
  thus "\<exists>p. Bet_Point (Se A C) p" by blast
qed

lemma(in Order_Rule) Line_Bet_not_on : 
  assumes 
    "Line_on (Li p1 p2) p3"
    "\<not> Line_on (Li p1 p2) p4"
    "Bet_Point (Se p3 p4) p5"
  shows "Inv (Line_on (Li p1 p2) p5)" 
proof -
  from assms have "\<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  then have P1 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p5) add Emp)" by (blast intro:Eq_rev)
  from assms have P2 : "Line_on (Li p3 p5) p4" by (simp add:Line_Bet_on)
  have P3 : "Line_on (Li p3 p5) p3" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li p3 p5) p5" by (simp add:Line_on_rule)
  from assms P1 P3 P4 have P5 : "Line_on (Li p1 p2) p5 \<Longrightarrow> Eq (Geos (Lin (Li p3 p5)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  from P2 P5 have P6 : "Line_on (Li p1 p2) p5 \<Longrightarrow> Line_on (Li p1 p2) p4" by (simp add:Line_on_trans)
  from assms P6 have "\<not> Line_on (Li p1 p2) p5" by blast
  thus "Inv (Line_on (Li p1 p2) p5)" by (simp add:Inv_def)
qed

lemma(in Order_Rule) Line_not_on_ex : 
  assumes N :
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
    "\<not> Line_on (Li p1 p2) p3"
    "Line_on (Li p1 p4) p2"
  shows "\<not> Line_on (Li p1 p4) p3" 
proof 
  assume W : "Line_on (Li p1 p4) p3" 
  have P1 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p1 p4) p1" by (simp add:Line_on_rule)
  from N P1 P2 P3 have P4 : "Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin (Li p1 p2)) add Emp)" by (simp add:Line_unique)
  from W P4 have P5 : "Line_on (Li p1 p2) p3" by (simp add:Line_on_trans)
  from N P5 show False by simp
qed

lemma(in Order_Rule) Line_on_dens : 
  assumes
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)"
    "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp)"
    "Line_on (Li p1 p2) p3"
    "Line_on (Li p1 p4) p3"
  shows "Line_on (Li p2 p4) p3" 
proof -
  have P1 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li p1 p4) p1" by (simp add:Line_on_rule)
  from assms P1 P2 have P3 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p4)) add Emp)" by (simp add:Line_unique)
  have P4 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from P3 P4 have P5 : "Line_on (Li p1 p4) p2" by (simp add:Line_on_trans)
  have P6 : "Line_on (Li p1 p4) p4" by (simp add:Line_on_rule)
  have P7 : "Line_on (Li p2 p4) p2" by (simp add:Line_on_rule)
  have P8 : "Line_on (Li p2 p4) p4" by (simp add:Line_on_rule)
  from assms P5 P6 P7 P8 have P9 : "Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin (Li p2 p4)) add Emp)" by (simp add:Line_unique)
  from assms P9 show "Line_on (Li p2 p4) p3" by (simp add:Line_on_trans)
qed

lemma(in Order_Rule) Bet_case_lemma1 : 
  assumes 
    "Line_on l1 A"
    "Line_on l1 B"
    "Line_on l1 C"
    "\<not> Bet_Point (Se B A) C"
    "\<not> Bet_Point (Se C B) A"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)"
    "\<not> Line_on (Li A C) D"
    "Bet_Point (Se B G) D"
  shows "\<exists>p. Line_on (Li A D) p \<and> Bet_Point (Se G C) p"
proof -
  have P1 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  from assms P1 P2 have P3 : "Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from assms P3 have P4 : "Line_on (Li A C) B" by (simp add:Line_on_trans)
  have P11 : "Line_on (Li B G) B" by (simp add:Line_on_rule)
  from assms P2 P4 P11 have P12 : "Line_on (Li B G) C \<Longrightarrow> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from assms have P13 : "Line_on (Li B G) D" by (simp add:Line_Bet_on)
  from P12 P13 have P14 : "Line_on (Li B G) C \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from assms P14 have P15 : "\<not> Line_on (Li B G) C" by blast
  have P16 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  from assms P1 P4 P16 have P17 : "Line_on (Li A D) B \<Longrightarrow> Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  have P18 : "Line_on (Li A D) D" by (simp add:Line_on_rule)
  from P17 P18 have P19 : "Line_on (Li A D) B \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from assms P19 have P20 : "\<not> Line_on (Li A D) B" by blast
  from assms P1 P2 P16 have P21 : "Line_on (Li A D) C \<Longrightarrow> Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P18 P21 have P22 : "Line_on (Li A D) C \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from assms P22 have P23 : "\<not> Line_on (Li A D) C" by blast
  from assms P1 P4 P11 have P24 : "Line_on (Li B G) A \<Longrightarrow> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P13 P24 have P25 : "Line_on (Li B G) A \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from assms P25 have P26 : "\<not> Line_on (Li B G) A" by blast
  have P27 : "Line_on (Li B G) G" by (simp add:Line_on_rule)
  from assms have P28 : "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P13 P18 P27 P28 have P29 : "Line_on (Li A D) G \<Longrightarrow> Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li B G)) add Emp)" by (simp add:Line_unique)
  from P16 P29 have P30 : "Line_on (Li A D) G \<Longrightarrow> Line_on (Li B G) A" by (simp add:Line_on_trans)
  from P26 P30 have P31 : "\<not> Line_on (Li A D) G" by blast
  from assms P15 P18 P20 P23 P31 have P32 : "Line_on_Seg (Li A D) (Se B C) \<and> \<not> Line_on_Seg (Li A D) (Se G C)
    \<or> Line_on_Seg (Li A D) (Se G C) \<and> \<not> Line_on_Seg (Li A D) (Se B C)" by (simp add:Pachets_axiom)
  have "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> \<exists>p. Line_on (Li A D) p \<and> Bet_Point (Se B C) p" by (simp add:Line_on_Seg_rule)
  then obtain A2 :: Point where P33 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Line_on (Li A D) A2 \<and> Bet_Point (Se B C) A2" by blast
  from assms have P34 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from assms P34 have P35 : "\<not> Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_not_Eq)
  have P36 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  have P37 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  from assms P2 P4 P36 P37 have P38 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P33 have P39 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Bet_Point (Se B C) A2" by simp
  then have P40 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Line_on (Li B C) A2" by (simp add:Line_Bet_on)
  from P38 P40 have P41 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Line_on (Li A C) A2" by (simp add:Line_on_trans)
  from P1 P16 P33 P35 P41 have P42 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Eq (Geos (Poi A2) add Emp) (Geos (Poi A) add Emp)" by (simp add:Line_unique_Point)
  from P39 P42 have P43 : "Line_on_Seg (Li A D) (Se B C) \<Longrightarrow> Bet_Point (Se B C) A" by (simp add:Point_Eq)
  from assms have P44 : "\<not> Bet_Point (Se B C) A" by (blast intro:Bet_rev)
  from P43 P44 have P45 : "\<not> Line_on_Seg (Li A D) (Se B C)" by blast
  from P32 P45 have "Line_on_Seg (Li A D) (Se G C) \<and> \<not> Line_on_Seg (Li A D) (Se B C)" by blast
  thus "\<exists>p. Line_on (Li A D) p \<and> Bet_Point (Se G C) p" by (simp add:Line_on_Seg_rule)
qed

lemma(in Order_Rule) Bet_case_lemma2 : 
  assumes 
    "Line_on l1 A"
    "Line_on l1 B"
    "Line_on l1 C"
    "\<not> Bet_Point (Se B A) C"
    "\<not> Bet_Point (Se C B) A"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)"
  shows "Bet_Point (Se A C) B"
proof -
  have P1 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  have P2 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  from assms P1 P2 have P3 : "Eq (Geos (Lin l1) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from assms P3 have P4 : "Line_on (Li A C) B" by (simp add:Line_on_trans)
  have "\<exists>p q r. \<not> Line_on (Li A C) p \<and> \<not> Line_on (Li A C) q \<and> \<not> Line_on (Li A C) r
    \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
    \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain D :: Point where P5 : "\<not> Line_on (Li A C) D" by blast
  from P4 have P6 : "Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li A C) D" by (simp add:Point_Eq)
  from P5 P6 have P7 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by blast
  have P8 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li B D) D" by (simp add:Line_on_rule)
  from P7 P8 P9 have "\<exists>p. Bet_Point (Se B p) D \<and> Line_on (Li B D) p" by (simp add:Bet_extension)
  then obtain G :: Point where P10 : "Bet_Point (Se B G) D" by blast
  from assms P5 P10 have "\<exists>p. Line_on (Li A D) p \<and> Bet_Point (Se G C) p" by (simp add:Bet_case_lemma1)
  then obtain E :: Point where P11 : "Line_on (Li A D) E \<and> Bet_Point (Se G C) E" by blast
  from assms have P12 : "\<not> Bet_Point (Se B C) A" by (blast intro:Bet_rev)
  from assms have P13 : "\<not> Bet_Point (Se A B) C" by (blast intro:Bet_rev)
  from assms have P14 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from assms have P15 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from assms have P16 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P14 have P17 : "Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li C A)) add Emp)" by (simp add:Line_rev)
  from P5 P17 have P18 : "\<not> Line_on (Li C A) D" by (simp add:Line_not_on_trans)
  from assms P10 P12 P13 P14 P15 P16 P18 have "\<exists>p. Line_on (Li C D) p \<and> Bet_Point (Se G A) p" by (simp add:Bet_case_lemma1)
  then obtain F :: Point where P19 : "Line_on (Li C D) F \<and> Bet_Point (Se G A) F" by blast
  have P20 : "Line_on (Li B G) B" by (simp add:Line_on_rule)
  have P21 : "Line_on (Li B G) G" by (simp add:Line_on_rule)
  from P10 have P22 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from P4 P20 P21 P22 have P23 : "Line_on (Li A C) G \<Longrightarrow> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P10 have P24 : "Line_on (Li B G) D" by (simp add:Line_Bet_on)
  from P23 P24 have P25 : "Line_on (Li A C) G \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from P5 P25 have P26 : "\<not> Line_on (Li A C) G" by blast
  from P11 have P27 : "Bet_Point (Se C G) E" by (blast intro:Bet_rev)
  have P28 : "Line_on (Li C G) C" by (simp add:Line_on_rule)
  from assms P1 P2 P28 have P29 : "Line_on (Li C G) A \<Longrightarrow> Eq (Geos (Lin (Li C G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  have P30 : "Line_on (Li C G) G" by (simp add:Line_on_rule)
  from P29 P30 have P31 : "Line_on (Li C G) A \<Longrightarrow> Line_on (Li A C) G" by (simp add:Line_on_trans)
  from P26 P31 have P32 : "\<not> Line_on (Li C G) A" by blast
  from P27 P32 have "\<not> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li A G)) add Emp)" by (simp add:Line_Bet_not_Eq)
  then have P33 : "\<not> Eq (Geos (Lin (Li A G)) add Emp) (Geos (Lin (Li A E)) add Emp)" by (blast intro:Eq_rev)
  from P19 have P34 : "Bet_Point (Se A G) F" by (blast intro:Bet_rev)
  then have P35 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from P27 have P36 : "Line_on (Li C G) E" by (simp add:Line_Bet_on)
  then have P37 : "Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li C G) A" by (simp add:Point_Eq)
  from P32 P37 have P38 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  from P33 P35 P38 have P39 : "\<not> Line_on (Li A G) E" by (simp add:Line_not_Eq_on)
  from P14 P26 P35 have P40 : "\<not> Line_on (Li A G) C" by (blast intro:Line_on_rev)
  from P34 P40 have P41 : "\<not> Eq (Geos (Lin (Li C F)) add Emp) (Geos (Lin (Li C G)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P34 have P42 : "Line_on (Li A G) F" by (simp add:Line_Bet_on)
  then have P43 : "Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on (Li A G) C" by (simp add:Point_Eq)
  from P40 P43 have P44 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp)" by (blast intro:Eq_rev)
  from P27 have P45 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from P41 P44 P45 have P46 : "\<not> Line_on (Li C F) G" by (simp add:Line_not_Eq_on)
  from P35 have P47 : "Eq (Geos (Lin (Li A G)) add Emp) (Geos (Lin (Li G A)) add Emp)" by (simp add:Line_rev)
  from P40 P47 have P48 : "\<not> Line_on (Li G A) C" by (simp add:Line_not_on_trans)
  from P19 have P49 : "Bet_Point (Se G A) F" by simp
  from P48 P49 have P50 : "\<not> Eq (Geos (Lin (Li C F)) add Emp) (Geos (Lin (Li C A)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms P44 P50 have P51 : "\<not> Line_on (Li C F) A" by (simp add:Line_not_Eq_on)
  have P52 : "Line_on (Li C F) C" by (simp add:Line_on_rule)
  from P27 have P53 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P28 P36 P52 P53 have P54 : "Line_on (Li C F) E \<Longrightarrow> Eq (Geos (Lin (Li C G)) add Emp) (Geos (Lin (Li C F)) add Emp)" by (simp add:Line_unique)
  from P30 P54 have P55 : "Line_on (Li C F) E \<Longrightarrow> Line_on (Li C F) G" by (simp add:Line_on_trans)
  from P46 P55 have P56 : "\<not> Line_on (Li C F) E" by blast
  have P57 : "Line_on (Li C F) F" by (simp add:Line_on_rule)
  from P34 P39 P46 P51 P56 P57 have P58 : "Line_on_Seg (Li C F) (Se A E) \<and> \<not> Line_on_Seg (Li C F) (Se G E)
    \<or> Line_on_Seg (Li C F) (Se G E) \<and> \<not> Line_on_Seg (Li C F) (Se A E)" by (simp add:Pachets_axiom)
  have "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> \<exists>p. Line_on (Li C F) p \<and> Bet_Point (Se G E) p" by (simp add:Line_on_Seg_rule)
  then obtain D2 :: Point where P59 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Line_on (Li C F) D2 \<and> Bet_Point (Se G E) D2" by blast
  then have P60 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Bet_Point (Se G E) D2" by simp
  then have P61 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Line_on (Li G E) D2" by (simp add:Line_Bet_on)
  have P62 : "Line_on (Li G E) G" by (simp add:Line_on_rule)
  have P63 : "Line_on (Li G E) E" by (simp add:Line_on_rule)
  from P27 have P64 : "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def)
  from P27 have P66 : "Line_on (Li G E) C" by (simp add:Line_Bet_on)
  from P59 have P67 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Line_on (Li C F) D2" by simp
  from P60 have P68 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Eq (Geos (Poi D2) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> 
    Bet_Point (Se G E) C" by (simp add:Point_Eq)
  from P27 have "Inv (Bet_Point (Se G E) C) \<and> Inv (Bet_Point (Se E C) G)" by (simp add:Bet_iff)
  then have P69 : "\<not> Bet_Point (Se G E) C \<and> \<not> Bet_Point (Se E C) G" by (simp add:Inv_def)
  from P68 P69 have P70 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> \<not> Eq (Geos (Poi D2) add Emp) (Geos (Poi C) add Emp)" by blast
  from P52 P61 P66 P67 P70 have P71 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Eq (Geos (Lin (Li G E)) add Emp) (Geos (Lin (Li C F)) add Emp)" by (simp add:Line_unique)
  from P63 P71 have P72 : "Line_on_Seg (Li C F) (Se G E) \<Longrightarrow> Line_on (Li C F) E" by (simp add:Line_on_trans)
  from P56 P72 have P73 : "\<not> Line_on_Seg (Li C F) (Se G E)" by blast
  from P58 P73 have "Line_on_Seg (Li C F) (Se A E) \<and> \<not> Line_on_Seg (Li C F) (Se G E)" by blast
  then have "\<exists>p. Line_on (Li C F) p \<and> Bet_Point (Se A E) p" by (simp add:Line_on_Seg_rule)
  then obtain D3 :: Point where P74 : "Line_on (Li C F) D3 \<and> Bet_Point (Se A E) D3" by blast
  then have P75 : "Line_on (Li C F) D3" by simp
  from P74 have P76 : "Bet_Point (Se A E) D3" by simp
  then have P77 : "Line_on (Li A E) D3" by (simp add:Line_Bet_on)
  from P19 have P78 : "Line_on (Li C D) F" by simp
  from P2 have P79 : "Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li A C) D" by (simp add:Point_Eq)
  from P5 P79 have P80 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi D) add Emp)" by blast
  from P44 P78 P80 have P81 : "Line_on (Li C F) D" by (simp add:Line_on_rev)
  from P11 have P82 : "Line_on (Li A D) E" by simp
  from P1 have P83 : "Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Line_on (Li A C) D" by (simp add:Point_Eq)
  from P5 P83 have P84 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by blast
  from P38 P82 P84 have P85 : "Line_on (Li A E) D" by (simp add:Line_on_rev)
  have P86 : "Line_on (Li A E) E" by (simp add:Line_on_rule)
  then have P87 : "Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li C F)) add Emp) \<Longrightarrow> Line_on (Li C F) E" by (simp add:Line_on_trans)
  from P56 P87 have P88 : "\<not> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li C F)) add Emp)" by blast
  from P75 P77 P81 P85 P88 have P89 : "Eq (Geos (Poi D3) add Emp) (Geos (Poi D) add Emp)" by (simp add:Line_unique_Point)
  from P76 P89 have P90 : "Bet_Point (Se A E) D" by (simp add:Point_Eq)
  have P91 : "Line_on (Li A E) A" by (simp add:Line_on_rule)
  from assms P1 P2 P91 have P92 : "Line_on (Li A E) C \<Longrightarrow> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P85 P92 have P93 : "Line_on (Li A E) C \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from P5 P93 have P94 : "\<not> Line_on (Li A E) C" by blast
  from assms P1 P4 P20 have P95 : "Line_on (Li B G) A \<Longrightarrow> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P24 P95 have P96 : "Line_on (Li B G) A \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from P5 P96 have P97 : "\<not> Line_on (Li B G) A" by blast
  from assms P2 P4 P20 have P98 : "Line_on (Li B G) C \<Longrightarrow> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_unique)
  from P24 P98 have P99 : "Line_on (Li B G) C \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from P5 P99 have P100 : "\<not> Line_on (Li B G) C" by blast
  from P21 P62 P63 P64 have P101 : "Line_on (Li B G) E \<Longrightarrow> Eq (Geos (Lin (Li G E)) add Emp) (Geos (Lin (Li B G)) add Emp)" by (simp add:Line_unique)
  from P66 P101 have P102 : "Line_on (Li B G) E \<Longrightarrow> Line_on (Li B G) C" by (simp add:Line_on_trans)
  from P100 P102 have P103 : "\<not> Line_on (Li B G) E" by blast
  from P24 P90 P94 P97 P100 P103 have P104 : "Line_on_Seg (Li B G) (Se A C) \<and> \<not> Line_on_Seg (Li B G) (Se E C)
    \<or> Line_on_Seg (Li B G) (Se E C) \<and> \<not> Line_on_Seg (Li B G) (Se A C)" by (simp add:Pachets_axiom)
  have "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> \<exists>p. Line_on (Li B G) p \<and> Bet_Point (Se E C) p" by (simp add:Line_on_Seg_rule)
  then obtain B2 :: Point where P105 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Line_on (Li B G) B2 \<and> Bet_Point (Se E C) B2" by blast
  then have P106 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Bet_Point (Se E C) B2" by simp
  then have P107 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Line_on (Li E C) B2" by (simp add:Line_Bet_on)
  from P105 have P108 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Line_on (Li B G) B2" by simp
  have P109 : "Line_on (Li E C) E" by (simp add:Line_on_rule)
  have P110 : "Line_on (Li E C) C" by (simp add:Line_on_rule)
  from P28 P36 P53 P109 P110 have P111 : "Eq (Geos (Lin (Li C G)) add Emp) (Geos (Lin (Li E C)) add Emp)" by (simp add:Line_unique)
  from P30 P111 have P112 : "Line_on (Li E C) G" by (simp add:Line_on_trans)
  from P106 have P113 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Eq (Geos (Poi B2) add Emp) (Geos (Poi G) add Emp) \<Longrightarrow>
    Bet_Point (Se E C) G" by (simp add:Point_Eq)
  from P69 P113 have P114 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> \<not> Eq (Geos (Poi B2) add Emp) (Geos (Poi G) add Emp)" by blast
  from P21 P107 P108 P112 P114 have P115 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Eq (Geos (Lin (Li E C)) add Emp) (Geos (Lin (Li B G)) add Emp)" by (simp add:Line_unique)
  from P109 P115 have P116 : "Line_on_Seg (Li B G) (Se E C) \<Longrightarrow> Line_on (Li B G) E" by (simp add:Line_on_trans)
  from P103 P116 have P117 : "\<not> Line_on_Seg (Li B G) (Se E C)" by blast
  from P104 P117 have "Line_on_Seg (Li B G) (Se A C)" by blast
  then have "\<exists>p. Line_on (Li B G) p \<and> Bet_Point (Se A C) p" by (simp add:Line_on_Seg_rule)
  then obtain B3 :: Point where P118 : "Line_on (Li B G) B3 \<and> Bet_Point (Se A C) B3" by blast
  from P24 have P119 : "Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp) \<Longrightarrow> Line_on (Li A C) D" by (simp add:Line_on_trans)
  from P5 P119 have P120 : "\<not> Eq (Geos (Lin (Li B G)) add Emp) (Geos (Lin (Li A C)) add Emp)" by blast
  from P118 have P121 : "Line_on (Li B G) B3" by simp
  from P118 have P122 : "Bet_Point (Se A C) B3" by simp
  then have P123 : "Line_on (Li A C) B3" by (simp add:Line_Bet_on)
  from P4 P20 P120 P121 P123 have P124 : "Eq (Geos (Poi B3) add Emp) (Geos (Poi B) add Emp)" by (simp add:Line_unique_Point)
  from P122 P124 show "Bet_Point (Se A C) B" by (simp add:Point_Eq)
qed

text\<open>Theorem4\<close>

lemma(in Order_Rule) Bet_case : 
  assumes 
    "Line_on l1 A"
    "Line_on l1 B"
    "Line_on l1 C"
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
    "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)"
  shows "Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C"
proof -
  from assms have P1 : "\<not> Bet_Point (Se B A) C \<and> \<not> Bet_Point (Se C B) A \<Longrightarrow> Bet_Point (Se A C) B" by (simp add:Bet_case_lemma2)
  from assms have P2 : "\<not> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se A C) B \<Longrightarrow> Bet_Point (Se B A) C" by (simp add:Bet_case_lemma2)
  from assms have P3 : "\<not> Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se B A) C \<Longrightarrow> Bet_Point (Se C B) A" by (simp add:Bet_case_lemma2)
  from P1 P2 P3 show "Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C" by blast
qed

lemma(in Order_Rule) Bet_case_fact : 
  assumes 
    "Bet_Point (Se A C) B \<or> Bet_Point (Se C B) A \<or> Bet_Point (Se B A) C"
  shows 
    "Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se B A) C
    \<or> \<not> Bet_Point (Se A C) B \<and> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se B A) C
    \<or> \<not> Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se C B) A \<and> Bet_Point (Se B A) C"
proof -
  have "Bet_Point (Se A C) B \<Longrightarrow> Inv (Bet_Point (Se C B) A) \<and> Inv (Bet_Point (Se B A) C)" by (simp add:Bet_iff)
  then have P1 : "Bet_Point (Se A C) B \<Longrightarrow> \<not> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se B A) C" by (simp add:Inv_def)
  have "Bet_Point (Se C B) A \<Longrightarrow> Inv (Bet_Point (Se A C) B) \<and> Inv (Bet_Point (Se B A) C)" by (simp add:Bet_iff)
  then have P2 : "Bet_Point (Se C B) A \<Longrightarrow> \<not> Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se B A) C" by (simp add:Inv_def)
  have "Bet_Point (Se B A) C \<Longrightarrow> Inv (Bet_Point (Se A C) B) \<and> Inv (Bet_Point (Se C B) A)" by (simp add:Bet_iff)
  then have P3 : "Bet_Point (Se B A) C \<Longrightarrow> \<not> Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se C B) A" by (simp add:Inv_def)
  from assms P1 P2 P3 show "Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se B A) C
    \<or> \<not> Bet_Point (Se A C) B \<and> Bet_Point (Se C B) A \<and> \<not> Bet_Point (Se B A) C
    \<or> \<not> Bet_Point (Se A C) B \<and> \<not> Bet_Point (Se C B) A \<and> Bet_Point (Se B A) C" by blast
qed

lemma(in Order_Rule) Bet_swap_lemma_1 : 
  assumes
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)"
    "Bet_Point (Se A C) B"
    "Bet_Point (Se B D) C"
  shows "Line_on (Li A D) B \<and> Line_on (Li A D) C"
proof -
  from assms have P1 : "Line_on (Li A B) C" by (simp add:Line_Bet_on)
  have P2 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li B C) C" by (simp add:Line_on_rule)
  have P4 : "Line_on (Li B C) B" by (simp add:Line_on_rule)
  from assms have P5 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by (simp add:Bet_Point_def)
  from P1 P2 P3 P4 P5 have P6 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  from assms have P7 : "Line_on (Li B C) D" by (simp add:Line_Bet_on)
  from P6 P7 have P8 : "Line_on (Li A B) D" by (simp add:Line_on_trans)
  from assms have "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P9 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from assms P8 P9 have P10 : "Line_on (Li A D) B" by (simp add:Line_on_rev)
  have P11 : "Line_on (Li A D) D" by (simp add:Line_on_rule)
  from assms have P12 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P4 P7 P10 P11 P12 have P13 : "Eq (Geos (Lin (Li B C)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_unique)
  from P3 P13 have P14 : "Line_on (Li A D) C" by (simp add:Line_on_trans)
  from P10 P14 show "Line_on (Li A D) B \<and> Line_on (Li A D) C" by simp
qed

lemma(in Order_Rule) Bet_swap_lemma_2 : 
  assumes
    "Bet_Point (Se p1 p3) p2"
    "\<not> Line_on (Li p1 p3) p4"
    "\<not> Line_on (Li p2 p5) p3"
    "\<not> Line_on (Li p2 p5) p1"
    "\<not> Line_on (Li p2 p5) p4"
    "Bet_Point (Se p3 p5) p4"
  shows "\<exists>p. Line_on (Li p2 p5) p \<and> Bet_Point (Se p1 p4) p" 
proof -
  have P1 : "Line_on (Li p2 p5) p2" by (simp add:Line_on_rule)
  from assms P1 have P2 : "Line_on_Seg (Li p2 p5) (Se p1 p4) \<and> \<not> Line_on_Seg (Li p2 p5) (Se p3 p4) \<or> Line_on_Seg (Li p2 p5) (Se p3 p4) \<and> \<not> Line_on_Seg (Li p2 p5) (Se p1 p4)" by (simp add:Pachets_axiom)
  then have "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> \<exists>p. Line_on (Li p2 p5) p \<and> Bet_Point (Se p3 p4) p" by (simp add:Line_on_Seg_rule)
  then obtain p6 :: Point where P3 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Line_on (Li p2 p5) p6 \<and> Bet_Point (Se p3 p4) p6" by blast
  from assms have "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  then have P4 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p4) add Emp)" by (blast intro:Eq_rev)
  from P3 have P5 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Bet_Point (Se p3 p4) p6" by simp
  from P3 have P6 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Line_on (Li p3 p6) p4" by (simp add:Line_Bet_on)
  from assms have P7 : "Line_on (Li p3 p5) p4" by (simp add:Line_Bet_on)    
  have P8 : "Line_on (Li p3 p6) p3" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li p3 p5) p3" by (simp add:Line_on_rule)
  from P4 P6 P7 P8 P9 have P10 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> 
    Eq (Geos (Lin (Li p3 p5)) add Emp) (Geos (Lin (Li p3 p6)) add Emp)" by (simp add:Line_unique)
  have P11 : "Line_on (Li p3 p5) p5" by (simp add:Line_on_rule)
  from P10 P11 have P12 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Line_on (Li p3 p6) p5" by (simp add:Line_on_trans)
  have P13 : "Line_on (Li p2 p5) p5" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li p3 p6) p6" by (simp add:Line_on_rule)
  from P5 have P15 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Eq (Geos (Poi p6) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow>
    Bet_Point (Se p3 p4) p5" by (simp add:Point_Eq)
  from assms have "Inv (Bet_Point (Se p5 p4) p3) \<and> Inv (Bet_Point (Se p4 p3) p5)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se p4 p3) p5" by (simp add:Inv_def)
  then have P16 : "\<not> Bet_Point (Se p3 p4) p5" by (blast intro:Bet_rev)
  from P15 P16 have P17 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> \<not> Eq (Geos (Poi p6) add Emp) (Geos (Poi p5) add Emp)" by blast
  from P3 P12 P13 P14 P17 have P18 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> 
    Eq (Geos (Lin (Li p3 p6)) add Emp) (Geos (Lin (Li p2 p5)) add Emp)" by (simp add:Line_unique)
  from P8 P18 have P19 : "Line_on_Seg (Li p2 p5) (Se p3 p4) \<Longrightarrow> Line_on (Li p2 p5) p3" by (simp add:Line_on_trans)
  from assms P19 have P20 : "\<not> Line_on_Seg (Li p2 p5) (Se p3 p4)" by blast
  from P2 P3 P20 have "Line_on_Seg (Li p2 p5) (Se p1 p4)" by blast
  thus "\<exists>p. Line_on (Li p2 p5) p \<and> Bet_Point (Se p1 p4) p" by (simp add:Line_on_Seg_rule)
qed

lemma(in Order_Rule) Bet_swap_lemma_3 : 
  assumes
    "Bet_Point (Se p1 p3) p2"
    "Bet_Point (Se p3 p5) p4"
    "\<not> Line_on (Li p1 p3) p5"
  shows "\<exists>p. Bet_Point (Se p1 p4) p \<and> Bet_Point (Se p5 p2) p" 
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  then have P2 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p3 p1)) add Emp)" by (simp add:Line_rev)
  from assms P2 have P3 : "\<not> Line_on (Li p3 p1) p5" by (simp add:Line_not_on_trans)
  from assms have P4 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p5) add Emp)" by (simp add:Bet_Point_def)
  from P1 have P5 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from P3 P4 P5 have P6 : "\<not> Line_on (Li p3 p5) p1" by (blast intro:Line_on_rev)
  from assms have P7 : "Bet_Point (Se p5 p3) p4" by (simp add:Bet_rev)
  from P4 have P8 : "Eq (Geos (Lin (Li p3 p5)) add Emp) (Geos (Lin (Li p5 p3)) add Emp)" by (simp add:Line_rev)
  from P8 P6 have P9 : "\<not> Line_on (Li p5 p3) p1" by (simp add:Line_not_on_trans)
  from P7 P9 have P10 : "\<not> Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin (Li p1 p3)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms have "Line_on (Li p3 p5) p4" by (simp add:Line_Bet_on)
  then have P11 : "Eq (Geos (Poi p4) add Emp) (Geos (Poi p1) add Emp) \<Longrightarrow> Line_on (Li p3 p5) p1" by (simp add:Point_Eq)
  from P6 P11 have "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p1) add Emp)" by blast
  then have P12 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)" by (blast intro:Eq_rev)
  from P1 P10 P12 have P13 : "\<not> Line_on (Li p1 p4) p3" by (simp add:Line_not_Eq_on)
  from P1 P12 P13 have P14 : "\<not> Line_on (Li p1 p3) p4" by (blast intro:Line_on_rev) 
  from assms have P15 : "\<not> Eq (Geos (Lin (Li p5 p2)) add Emp) (Geos (Lin (Li p5 p3)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms have P16 : "Line_on (Li p1 p3) p2" by (simp add:Line_Bet_on)
  then have P17 : "Eq (Geos (Poi p2) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow> Line_on (Li p1 p3) p5" by (simp add:Point_Eq)
  from assms P17 have "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p5) add Emp)" by blast
  then have P18 : "\<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p2) add Emp)" by (blast intro:Eq_rev)
  from P4 have P19 : "\<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from P15 P18 P19 have P20 : "\<not> Line_on (Li p5 p2) p3" by (simp add:Line_not_Eq_on)
  from P18 have P21 : "Eq (Geos (Lin (Li p5 p2)) add Emp) (Geos (Lin (Li p2 p5)) add Emp)" by (simp add:Line_rev)
  from P20 P21 have P22 : "\<not> Line_on (Li p2 p5) p3" by (simp add:Line_not_on_trans) 
  from assms have P23 :"Bet_Point (Se p3 p1) p2" by (blast intro:Bet_rev)
  from P3 P23 have P24 : "\<not> Eq (Geos (Lin (Li p5 p2)) add Emp) (Geos (Lin (Li p5 p1)) add Emp)" by (simp add:Line_Bet_not_Eq)
  have "Line_on (Li p3 p1) p1" by (simp add:Line_on_rule)
  then have P25 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p5) add Emp) \<Longrightarrow> Line_on (Li p3 p1) p5" by (simp add:Point_Eq)
  from P3 P25 have P26 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p5) add Emp)" by blast
  then have P27 : "\<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from P18 P24 P27 have P28 : "\<not> Line_on (Li p5 p2) p1" by (simp add:Line_not_Eq_on)
  from P21 P28 have P29 : "\<not> Line_on (Li p2 p5) p1" by (simp add:Line_not_on_trans) 
  from assms have P31 : "Line_on (Li p3 p4) p5" by (simp add:Line_Bet_on)
  have P32 : "Line_on (Li p3 p4) p4" by (simp add:Line_on_rule)
  have P33 : "Line_on (Li p2 p5) p5" by (simp add:Line_on_rule)
  from assms have P34 : "\<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p4) add Emp)" by (simp add:Bet_Point_def)
  from P31 P32 P33 P34 have P35 : "Line_on (Li p2 p5) p4 \<Longrightarrow> Eq (Geos (Lin (Li p3 p4)) add Emp) (Geos (Lin (Li p2 p5)) add Emp)" by (simp add:Line_unique)
  have P36 : "Line_on (Li p3 p4) p3" by (simp add:Line_on_rule)
  from P35 P36 have P37 : "Line_on (Li p2 p5) p4 \<Longrightarrow> Line_on (Li p2 p5) p3" by (simp add:Line_on_trans)
  from P22 P37 have P38 : "\<not> Line_on (Li p2 p5) p4" by blast
  from assms P14 P22 P29 P38 have "\<exists>p. Line_on (Li p2 p5) p \<and> Bet_Point (Se p1 p4) p" by (simp add:Bet_swap_lemma_2)
  then obtain p6 :: Point where P39 : "Line_on (Li p2 p5) p6 \<and> Bet_Point (Se p1 p4) p6" by blast
  from P12 have P40 : "Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin (Li p4 p1)) add Emp)" by (simp add:Line_rev)
  from P13 P40 have P41 : "\<not> Line_on (Li p4 p1) p3" by (simp add:Line_not_on_trans) 
  from assms P6 have P42 : "\<not> Eq (Geos (Lin (Li p1 p4)) add Emp) (Geos (Lin (Li p1 p5)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P12 P26 P42 have P43 : "\<not> Line_on (Li p1 p4) p5" by (simp add:Line_not_Eq_on)
  from P40 P43 have P44 : "\<not> Line_on (Li p4 p1) p5" by (simp add:Line_not_on_trans)
  from assms have "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  then have P45 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (blast intro:Eq_rev)
  from P1 P16 P45 have P47 : "Line_on (Li p1 p2) p3" by (simp add:Line_on_rev)
  from P47 have P48 : "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p4)) add Emp) \<Longrightarrow> Line_on (Li p1 p4) p3" by (simp add:Line_on_trans)
  from P13 P48 have P49 : "\<not> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p1 p4)) add Emp)" by blast
  from P12 P45 P49 have P50 : "\<not> Line_on (Li p1 p2) p4" by (simp add:Line_not_Eq_on)
  from P12 P45 P50 have P51 : "\<not> Line_on (Li p1 p4) p2" by (blast intro:Line_on_rev)
  from P40 P51 have P52 : "\<not> Line_on (Li p4 p1) p2" by (simp add:Line_not_on_trans) 
  from P18 P19 P20 have P53 : "\<not> Line_on (Li p5 p3) p2" by (blast intro:Line_on_rev)
  from P7 P23 P41 P44 P52 P53 have "\<exists>p. Line_on (Li p4 p1) p \<and> Bet_Point (Se p5 p2) p" by (simp add:Bet_swap_lemma_2)
  then obtain p7 :: Point where P54 : "Line_on (Li p4 p1) p7 \<and> Bet_Point (Se p5 p2) p7" by blast
  from P33 P44 have P55 : "\<not> Eq (Geos (Lin (Li p4 p1)) add Emp) (Geos (Lin (Li p2 p5)) add Emp)" by (simp add:Line_not_on_Eq)
  from P39 have P56 : "Line_on (Li p4 p1) p6" by (simp add:Line_Bet_on)
  from P54 have P57 : "Line_on (Li p2 p5) p7" by (simp add:Line_Bet_on)
  from P39 P54 P55 P56 P57 have P58 : "Eq (Geos (Poi p7) add Emp) (Geos (Poi p6) add Emp)" by (blast intro:Line_unique_Point)
  from P54 have P59 : "Bet_Point (Se p5 p2) p7" by simp
  from P58 P59 have P60 : "Bet_Point (Se p5 p2) p6" by (simp add:Point_Eq)
  from P39 P60 show "\<exists>p. Bet_Point (Se p1 p4) p \<and> Bet_Point (Se p5 p2) p" by blast
qed

lemma(in Order_Rule) Bet_swap_lemma_4 : 
  assumes 
    "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)"
    "Bet_Point (Se A E) G"
    "Bet_Point (Se D G) H"
    "\<not> Line_on (Li A D) E"
  shows "\<exists>p. Line_on (Li H E) p \<and> Bet_Point (Se D A) p"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def)
  from assms P1 have P2 : "\<not> Line_on (Li A E) D" by (blast intro:Line_on_rev)
  from P1 have P3 : "Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li E A)) add Emp)" by (simp add:Line_rev)
  from P2 P3 have P4 : "\<not> Line_on (Li E A) D" by (simp add:Line_not_on_trans)
  from assms have P5 : "Bet_Point (Se E A) G" by (simp add:Bet_rev)
  from P4 P5 have P6 : "\<not> Eq (Geos (Lin (Li D G)) add Emp) (Geos (Lin (Li D A)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms have P7 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from assms have P8 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P6 P7 P8 have P9 : "\<not> Line_on (Li D G) A" by (simp add:Line_not_Eq_on)
  from assms P2 have P10 : "\<not> Eq (Geos (Lin (Li D G)) add Emp) (Geos (Lin (Li D E)) add Emp)" by (simp add:Line_Bet_not_Eq)
  have "Line_on (Li A D) D" by (simp add:Line_on_rule)
  then have P11 : "Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li A D) E" by (simp add:Point_Eq)
  from assms P11 have P12 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi E) add Emp)" by blast
  from P7 P10 P12 have P13 : "\<not> Line_on (Li D G) E" by (simp add:Line_not_Eq_on)
  from assms P13 have P14 : "\<not> Eq (Geos (Lin (Li E H)) add Emp) (Geos (Lin (Li E G)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms have "Line_on (Li D G) H" by (simp add:Line_Bet_on)
  then have P15 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li D G) E" by (simp add:Point_Eq)
  from P13 P15 have P16 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi H) add Emp)" by (blast intro:Eq_rev)
  from assms have "Line_on (Li D G) G" by (simp add:Line_on_rule)
  then have P17 : "Eq (Geos (Poi G) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li D G) E" by (simp add:Point_Eq)
  from P13 P17 have P18 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi G) add Emp)" by (blast intro:Eq_rev)
  from P14 P16 P18 have P19 : "\<not> Line_on (Li E H) G" by (simp add:Line_not_Eq_on)
  from P7 have P20 : "Eq (Geos (Lin (Li D G)) add Emp) (Geos (Lin (Li G D)) add Emp)" by (simp add:Line_rev)
  from P13 P20 have P21 : "\<not> Line_on (Li G D) E" by (simp add:Line_not_on_trans)
  from assms have P22 : "Bet_Point (Se G D) H" by (simp add:Bet_rev)
  from P21 P22 have P23 : "\<not> Eq (Geos (Lin (Li E H)) add Emp) (Geos (Lin (Li E D)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P12 have P24 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P16 P23 P24 have P25 : "\<not> Line_on (Li E H) D" by (simp add:Line_not_Eq_on)
  from P16 have P26 : "Eq (Geos (Lin (Li E H)) add Emp) (Geos (Lin (Li H E)) add Emp)" by (simp add:Line_rev)
  from P25 P26 have P27 : "\<not> Line_on (Li H E) D" by (simp add:Line_not_on_trans)
  have P28 : "Line_on (Li A E) A" by (simp add:Line_on_rule)
  have P29 : "Line_on (Li A E) E" by (simp add:Line_on_rule)
  have P30 : "Line_on (Li E H) E" by (simp add:Line_on_rule)
  from P1 P28 P29 P30 have P31 : "Line_on (Li E H) A \<Longrightarrow> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li E H)) add Emp)" by (simp add:Line_unique)
  from assms have P32 : "Line_on (Li A E) G" by (simp add:Line_Bet_on)
  from assms have "\<not> Eq (Geos (Poi G) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P33 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi G) add Emp)" by (blast intro:Eq_rev)
  from P31 P32 have P34 : "Line_on (Li E H) A \<Longrightarrow> Line_on (Li E H) G" by (simp add:Line_on_trans)
  from P19 P34 have P35 : "\<not> Line_on (Li E H) A" by blast
  from P26 P35 have P36 : "\<not> Line_on (Li H E) A" by (simp add:Line_not_on_trans)
  from P26 P19 have P37 : "\<not> Line_on (Li H E) G" by (simp add:Line_not_on_trans)
  have P38 : "Line_on (Li H E) H" by (simp add:Line_on_rule)
  from assms P9 P27 P36 P37 P38 have P39 : "Line_on_Seg (Li H E) (Se D A) \<and> \<not> Line_on_Seg (Li H E) (Se G A) \<or> Line_on_Seg (Li H E) (Se G A) \<and> \<not> Line_on_Seg (Li H E) (Se D A)" by (simp add:Pachets_axiom)
  then have "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> \<exists>p. Line_on (Li H E) p \<and> Bet_Point (Se G A) p" by (simp add:Line_on_Seg_rule)
  then obtain C2 :: Point where P40 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> Line_on (Li H E) C2 \<and> Bet_Point (Se G A) C2" by blast
  from assms have P41 : "Line_on (Li G A) E" by (simp add:Line_Bet_on)
  from P40 have P42 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> Line_on (Li G A) C2" by (simp add:Line_Bet_on)
  have P43 : "Line_on (Li H E) E" by (simp add:Line_on_rule)
  from P40 have "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> Bet_Point (Se G A) C2" by simp
  then have P44 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> Eq (Geos (Poi C2) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow>
    Bet_Point (Se G A) E" by (simp add:Point_Eq)
  from assms have "Inv (Bet_Point (Se E G) A) \<and> Inv (Bet_Point (Se G A) E)" by (simp add:Bet_iff)
  then have P45 : "\<not> Bet_Point (Se G A) E" by (simp add:Inv_def)
  from P44 P45 have P46 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> \<not> Eq (Geos (Poi C2) add Emp) (Geos (Poi E) add Emp)" by blast
  from P40 P41 P42 P43 P46 have P47 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> 
    Eq (Geos (Lin (Li G A)) add Emp) (Geos (Lin (Li H E)) add Emp)" by (simp add:Line_unique)
  have P48 : "Line_on (Li G A) G" by (simp add:Line_on_rule)
  from P47 P48 have P49 : "Line_on_Seg (Li H E) (Se G A) \<Longrightarrow> Line_on (Li H E) G" by (simp add:Line_on_trans)
  from P37 P49 have P50 : "\<not> Line_on_Seg (Li H E) (Se G A)" by blast
  from P39 P40 P50 have "Line_on_Seg (Li H E) (Se D A)" by blast
  thus "\<exists>p. Line_on (Li H E) p \<and> Bet_Point (Se D A) p" by (simp add:Line_on_Seg_rule)
qed

lemma(in Order_Rule) Bet_swap_lemma_5 : 
  assumes 
    "Bet_Point (Se A C) B"
    "Bet_Point (Se B D) C"
    "Bet_Point (Se C F) E"
    "\<not> Line_on (Li A D) F"
    "\<not> Line_on (Li A C) F"
  shows "Bet_Point (Se A D) C"
proof -
  from assms have P1 : "Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Bet_Point (Se D C) B" by (simp add:Bet_Point_Eq)
  from assms have "Inv (Bet_Point (Se D C) B) \<and> Inv (Bet_Point (Se C B) D)" by (simp add:Bet_iff)
  then have P2 : "\<not> Bet_Point (Se D C) B" by (simp add:Inv_def)
  from P1 P2 have P3 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by blast
  from assms P3 have P4 : "Line_on (Li A D) B \<and> Line_on (Li A D) C" by (simp add:Bet_swap_lemma_1)
  then have P5 : "Line_on (Li A D) C" by simp
  from assms have "\<exists>p. Bet_Point (Se A E) p \<and> Bet_Point (Se F B) p" by (simp add:Bet_swap_lemma_3)
  then obtain G :: Point where P6 : "Bet_Point (Se A E) G \<and> Bet_Point (Se F B) G" by blast 
  from P3 have P7 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li D A)) add Emp)" by (simp add:Line_rev)
  from P4 P7 have P8 : "Line_on (Li D A) B" by (blast intro:Line_on_trans)
  from assms P7 have P9 : "\<not> Line_on (Li D A) F" by (simp add:Line_not_on_trans)
  have P10 : "Line_on (Li D A) D" by (simp add:Line_on_rule)
  have P11 : "Line_on (Li D B) D" by (simp add:Line_on_rule)
  have P12 : "Line_on (Li D B) B" by (simp add:Line_on_rule)
  from assms have P13 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P8 P10 P11 P12 P13 have P14 : "Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin (Li D B)) add Emp)" by (simp add:Line_unique)
  from P9 P14 have P15 : "\<not> Line_on (Li D B) F" by (simp add:Line_not_on_trans) 
  from assms have P16 : "Bet_Point (Se D B) C" by (simp add:Bet_rev)
  from P6 have P17 : "Bet_Point (Se B F) G" by (simp add:Bet_rev)
  from P15 P16 P17 have "\<exists>p. Bet_Point (Se D G) p \<and> Bet_Point (Se F C) p" by (simp add:Bet_swap_lemma_3)
  then obtain H :: Point where P18 : "Bet_Point (Se D G) H \<and> Bet_Point (Se F C) H" by blast
  from assms have P19 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  then have P20 : "Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li C A)) add Emp)" by (simp add:Line_rev)
  from assms P20 have P21 : "\<not> Line_on (Li C A) F" by (simp add:Line_not_on_trans)
  from P19 have P22 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from assms have P23 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp)" by (simp add:Bet_Point_def)
  from P21 P22 P23 have P24 : "\<not> Line_on (Li C F) A" by (blast intro:Line_on_rev)
  from assms have P25 : "Bet_Point (Se F C) E" by (simp add:Bet_rev)
  from P23 have P26 : "Eq (Geos (Lin (Li C F)) add Emp) (Geos (Lin (Li F C)) add Emp)" by (simp add:Line_rev)
  from P24 P26 have P27 : "\<not> Line_on (Li F C) A" by (simp add:Line_not_on_trans)
  from P25 P27 have P28 : "\<not> Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P25 have "Line_on (Li F C) E" by (simp add:Line_Bet_on)
  then have P29 : "Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp) \<Longrightarrow> Line_on (Li F C) A" by (simp add:Point_Eq)
  from P27 P29 have "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi A) add Emp)" by blast
  then have P30 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi E) add Emp)" by (blast intro:Eq_rev)
  from P19 P28 P30 have P31 : "\<not> Line_on (Li A E) C" by (simp add:Line_not_Eq_on)
  from P19 P30 P31 have P32 : "\<not> Line_on (Li A C) E" by (blast intro:Line_on_rev) 
  from P5 P19 P32 have P33 : "\<not> Line_on (Li A D) E" by (simp add:Line_not_on_ex) 
  from P3 P30 P33 have P34 : "\<not> Line_on (Li A E) D" by (blast intro:Line_on_rev)
  from P30 have P35 : "Eq (Geos (Lin (Li A E)) add Emp) (Geos (Lin (Li E A)) add Emp)" by (simp add:Line_rev)
  from P18 have P36 : "Bet_Point (Se D G) H" by simp
  from P6 have P37 : "Bet_Point (Se A E) G" by simp
  from P3 P18 P33 P37 have "\<exists>p. Line_on (Li H E) p \<and> Bet_Point (Se D A) p" by (simp add:Bet_swap_lemma_4)
  then obtain C2 :: Point where P38 : "Line_on (Li H E) C2 \<and> Bet_Point (Se D A) C2" by blast
  have "Line_on (Li H E) E" by (simp add:Line_on_rule)
  then have P39 : "Eq (Geos (Lin (Li H E)) add Emp) (Geos (Lin (Li A D)) add Emp) \<Longrightarrow> Line_on (Li A D) E" by (simp add:Line_on_trans)
  from P33 P39 have P40 : "\<not> Eq (Geos (Lin (Li H E)) add Emp) (Geos (Lin (Li A D)) add Emp)" by blast
  from P23 have P41 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P25 have P42 : "Line_on (Li F E) C" by (simp add:Line_Bet_on)
  from P18 have P43 : "Line_on (Li F H) C" by (simp add:Line_Bet_on)
  from P36 have P44 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Bet_Point (Se D G) E" by (simp add:Point_Eq)
  then have P45 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li D G) E" by (simp add:Line_Bet_on)
  have P46 : "Line_on (Li D G) G" by (simp add:Line_on_rule)
  have P47 : "Line_on (Li A E) E" by (simp add:Line_on_rule)
  from P37 have P48 : "Line_on (Li A E) G" by (simp add:Line_Bet_on)
  from P44 have P49 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> \<not> Eq (Geos (Poi G) add Emp) (Geos (Poi E) add Emp)" by (simp add:Bet_Point_def)
  from P45 P46 P47 P48 P49 have P50 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li D G)) add Emp) (Geos (Lin (Li A E)) add Emp)" by (simp add:Line_unique)
  have P51 : "Line_on (Li D G) D" by (simp add:Line_on_rule)
  from P50 P51 have P52 : "Eq (Geos (Poi H) add Emp) (Geos (Poi E) add Emp) \<Longrightarrow> Line_on (Li A E) D" by (simp add:Line_on_trans)
  from P34 P52 have P53 : "\<not> Eq (Geos (Poi E) add Emp) (Geos (Poi H) add Emp)" by (blast intro:Eq_rev)
  from P41 P42 P43 P53 have P54 : "Line_on (Li E H) C" by (blast intro:Line_on_dens)
  from P53 have P55 : "Eq (Geos (Lin (Li E H)) add Emp) (Geos (Lin (Li H E)) add Emp)" by (simp add:Line_rev)
  from P54 P55 have P56 : "Line_on (Li H E) C" by (blast intro:Line_on_trans)
  from P38 have P57 : "Line_on (Li A D) C2" by (simp add:Line_Bet_on)
  from P5 P38 P40 P56 P57 have P58 : "Eq (Geos (Poi C2) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Line_unique_Point)
  from P38 have P59 : "Bet_Point (Se D A) C2" by simp
  from P58 P59 have "Bet_Point (Se D A) C" by (simp add:Point_Eq)
  thus "Bet_Point (Se A D) C" by (simp add:Bet_rev)
qed

theorem(in Order_Rule) Bet_swap_234_134 : 
  assumes 
    "Bet_Point (Se A C) B"
    "Bet_Point (Se B D) C"
  shows "Bet_Point (Se A D) C"
proof -
  from assms have P1 : "Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Bet_Point (Se D C) B" by (simp add:Bet_Point_Eq)
  from assms have "Inv (Bet_Point (Se D C) B) \<and> Inv (Bet_Point (Se C B) D)" by (simp add:Bet_iff)
  then have P2 : "\<not> Bet_Point (Se D C) B" by (simp add:Inv_def)
  from P1 P2 have P3 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by blast
  from assms P3 have "Line_on (Li A D) B \<and> Line_on (Li A D) C" by (simp add:Bet_swap_lemma_1)
  then have P4 : "Line_on (Li A D) C" by simp
  have "\<exists>p q r. \<not> Line_on (Li A D) p \<and> \<not> Line_on (Li A D) q \<and> \<not> Line_on (Li A D) r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain F :: Point where P5 : "\<not> Line_on (Li A D) F" by blast
  from P4 have P6 : "Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P5 P6 have "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp)" by blast
  then have "\<exists>p. Bet_Point (Se C F) p" by (simp add:Seg_density)
  then obtain E :: Point where P7 : "Bet_Point (Se C F) E" by blast 
  have P8 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  have P10 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  from assms have P11 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P4 P8 P9 P10 P11 have "Eq (Geos (Lin (Li A C)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_unique)
  then have P12 : "Line_on (Li A C) F \<Longrightarrow> Line_on (Li A D) F" by (simp add:Line_on_trans)
  from P5 P12 have P13 : "\<not> Line_on (Li A C) F" by blast
  from assms P5 P7 P13 show "Bet_Point (Se A D) C" by (blast intro:Bet_swap_lemma_5)
qed

theorem(in Order_Rule) Bet_swap_234_124 : 
  assumes 
    "Bet_Point (Se A C) B"
    "Bet_Point (Se B D) C"
  shows "Bet_Point (Se A D) B"
proof -
  from assms have P1 : "Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Bet_Point (Se D C) B" by (simp add:Bet_Point_Eq)
  from assms have "Inv (Bet_Point (Se D C) B) \<and> Inv (Bet_Point (Se C B) D)" by (simp add:Bet_iff)
  then have P2 : "\<not> Bet_Point (Se D C) B" by (simp add:Inv_def)
  from P1 P2 have P3 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by blast
  from assms P3 have "Line_on (Li A D) B \<and> Line_on (Li A D) C" by (simp add:Bet_swap_lemma_1)
  then have P4 : "Line_on (Li A D) B" by simp
  have "\<exists>p q r. \<not> Line_on (Li A D) p \<and> \<not> Line_on (Li A D) q \<and> \<not> Line_on (Li A D) r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain F :: Point where P5 : "\<not> Line_on (Li A D) F" by blast
  from P4 have P6 : "Eq (Geos (Poi B) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P5 P6 have "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi F) add Emp)" by blast
  then have "\<exists>p. Bet_Point (Se B F) p" by (simp add:Seg_density)
  then obtain E :: Point where P7 : "Bet_Point (Se B F) E" by blast 
  from assms have P8 : "Bet_Point (Se D B) C" by (simp add:Bet_rev)
  from assms have P9 : "Bet_Point (Se C A) B" by (simp add:Bet_rev)
  from P3 have P10 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li D A)) add Emp)" by (simp add:Line_rev)
  from P5 P10 have P11 : "\<not> Line_on (Li D A) F" by (simp add:Line_not_on_trans)
  from P4 P10 have P12 : "Line_on (Li D A) B" by (simp add:Line_on_trans)
  have P13 : "Line_on (Li D A) D" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li D B) D" by (simp add:Line_on_rule)
  have P15 : "Line_on (Li D B) B" by (simp add:Line_on_rule)
  from assms have P16 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  from P12 P13 P14 P15 P16 have "Eq (Geos (Lin (Li D B)) add Emp) (Geos (Lin (Li D A)) add Emp)" by (simp add:Line_unique)
  then have P17 : "Line_on (Li D B) F \<Longrightarrow> Line_on (Li D A) F" by (simp add:Line_on_trans)
  from P11 P17 have P18 : "\<not> Line_on (Li D B) F" by blast
  from P7 P8 P9 P11 P18 have "Bet_Point (Se D A) B" by (blast intro:Bet_swap_lemma_5)
  thus "Bet_Point (Se A D) B" by (blast intro:Bet_rev)
qed

theorem(in Order_Rule) Bet_swap_134_234 : 
  assumes 
    "Bet_Point (Se A C) B"
    "Bet_Point (Se A D) C"
  shows "Bet_Point (Se B D) C"
proof -
  from assms have P2 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from assms have P3 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi A) add Emp)" by (simp add:Bet_Point_def)
  then have P4 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from assms have P5 : "Line_on (Li A B) C" by (simp add:Line_Bet_on)
  have P6 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  from assms have P7 : "Line_on (Li A D) C" by (simp add:Line_Bet_on)
  have P8 : "Line_on (Li A D) A" by (simp add:Line_on_rule)
  from P2 P5 P6 P7 P8 have P9 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_unique)
  have P10 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from P9 P10 have P11 : "Line_on (Li A D) B" by (simp add:Line_on_trans)
  from assms have P12 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi D) add Emp)" by (simp add:Bet_Point_def)
  then have P13 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li D A)) add Emp)" by (simp add:Line_rev)
  from P11 P13 have P14 : "Line_on (Li D A) B" by (simp add:Line_on_trans)
  from P12 have P15 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from assms have P16 : "Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp) \<Longrightarrow> Bet_Point (Se A C) D" by (simp add:Point_Eq)
  from assms have "Inv (Bet_Point (Se D C) A) \<and> Inv (Bet_Point (Se C A) D)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se C A) D" by (simp add:Inv_def)
  then have P17 : "\<not> Bet_Point (Se A C) D" by (blast intro:Bet_rev)
  from P16 P17 have P18 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P14 P15 P18 have P19 : "Line_on (Li D B) A" by (simp add:Line_on_rev)
  from P18 have P20 : "Eq (Geos (Lin (Li D B)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_rev)
  from P19 P20 have P21 : "Line_on (Li B D) A" by (simp add:Line_on_trans)
  have P22 : "Line_on (Li B D) B" by (simp add:Line_on_rule)
  from P4 P8 P11 P21 P22 have P23 : "Eq (Geos (Lin (Li A D)) add Emp) (Geos (Lin (Li B D)) add Emp)" by (simp add:Line_unique)
  from P7 P23 have P24 : "Line_on (Li B D) C" by (simp add:Line_on_trans)
  have "\<exists>p q r. \<not> Line_on (Li A D) p \<and> \<not> Line_on (Li A D) q \<and> \<not> Line_on (Li A D) r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain F :: Point where P25 : "\<not> Line_on (Li A D) F" by blast
  from P11 have P26 : "Eq (Geos (Poi B) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P25 P26 have "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi F) add Emp)" by blast
  then have "\<exists>p. Bet_Point (Se B F) p" by (simp add:Seg_density)
  then obtain G :: Point where P27 : "Bet_Point (Se B F) G" by blast 
  from P11 P25 P27 have "Inv (Line_on (Li A D) G)" by (simp add:Line_Bet_not_on)
  then have P28 : "\<not> Line_on (Li A D) G" by (simp add:Inv_def) 
  from assms P25 have P29 : "\<not> Eq (Geos (Lin (Li F C)) add Emp) (Geos (Lin (Li F D)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P7 have P30 : "Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P25 P30 have P31 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  have P32 : "Line_on (Li A D) D" by (simp add:Line_on_rule)
  then have P33 : "Eq (Geos (Poi D) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P25 P33 have P34 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P29 P31 P34 have P35 : "\<not> Line_on (Li F C) D" by (simp add:Line_not_Eq_on)
  from P31 have P36 : "Eq (Geos (Lin (Li F C)) add Emp) (Geos (Lin (Li C F)) add Emp)" by (simp add:Line_rev)
  from P35 P36 have P37 : "\<not> Line_on (Li C F) D" by (simp add:Line_not_on_trans) 
  from assms have P38 : "Bet_Point (Se D A) C" by (simp add:Bet_rev)
  from P13 P25 have P39 : "\<not> Line_on (Li D A) F" by (simp add:Line_not_on_trans)
  from P38 P39 have P40 : "\<not> Eq (Geos (Lin (Li F C)) add Emp) (Geos (Lin (Li F A)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P8 have P41 : "Eq (Geos (Poi A) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P25 P41 have P42 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P31 P40 P42 have P43 : "\<not> Line_on (Li F C) A" by (simp add:Line_not_Eq_on)
  from P36 P43 have P44 : "\<not> Line_on (Li C F) A" by (simp add:Line_not_on_trans) 
  from P2 have P45 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)" by (blast intro:Eq_rev)
  from P31 have P46 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi F) add Emp)" by (blast intro:Eq_rev)
  from P44 P45 P46 have P47 : "\<not> Line_on (Li C A) F" by (blast intro:Line_on_rev)
  from P45 have P48 : "Eq (Geos (Lin (Li C A)) add Emp) (Geos (Lin (Li A C)) add Emp)" by (simp add:Line_rev)
  from P47 P48 have P49 : "\<not> Line_on (Li A C) F" by (simp add:Line_not_on_trans)
  from assms P49 have P50 : "\<not> Eq (Geos (Lin (Li F B)) add Emp) (Geos (Lin (Li F C)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from P11 have P51 : "Eq (Geos (Poi B) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) F" by (simp add:Point_Eq)
  from P25 P51 have P52 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi B) add Emp)" by (blast intro:Eq_rev)
  from P31 P50 P52 have P53 : "\<not> Line_on (Li F B) C" by (simp add:Line_not_Eq_on)
  from P27 have P54 : "Line_on (Li B F) G" by (simp add:Line_Bet_on)
  from P27 have P56 : "Line_on (Li F B) G" by (simp add:Line_Bet_on)
  have P57 : "Line_on (Li F B) F" by (simp add:Line_on_rule)
  have P58 : "Line_on (Li C F) F" by (simp add:Line_on_rule)
  from P27 have P59 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi G) add Emp)" by (simp add:Bet_Point_def)
  from P56 P57 P58 P59 have P60 : "Line_on (Li C F) G \<Longrightarrow> Eq (Geos (Lin (Li C F)) add Emp) (Geos (Lin (Li F B)) add Emp)" by (simp add:Line_unique)
  have P61 : "Line_on (Li C F) C" by (simp add:Line_on_rule)
  from P60 P61 have P62 : "Line_on (Li C F) G \<Longrightarrow> Line_on (Li F B) C" by (simp add:Line_on_trans)
  from P53 P62 have P63 : "\<not> Line_on (Li C F) G" by blast
  have P64 : "Line_on (Li C F) C" by (simp add:Line_on_rule)
  from assms P28 P37 P44 P63 P64 have P65 : "Line_on_Seg (Li C F) (Se A G) \<and> \<not> Line_on_Seg (Li C F) (Se D G) \<or> Line_on_Seg (Li C F) (Se D G) \<and> \<not> Line_on_Seg (Li C F) (Se A G)" by (simp add:Pachets_axiom)
  then have "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> \<exists>p. Line_on (Li C F) p \<and> Bet_Point (Se A G) p" by (simp add:Line_on_Seg_rule)
  then obtain H :: Point where P66 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li C F) H \<and> Bet_Point (Se A G) H" by blast
  from P9 have P67 : "Line_on (Li A B) F \<Longrightarrow> Line_on (Li A D) F" by (simp add:Line_on_trans)
  from P25 P67 have P68 : "\<not> Line_on (Li A B) F" by blast
  from P4 have P69 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li B A)) add Emp)" by (simp add:Line_rev)
  from P68 P69 have P70 : "\<not> Line_on (Li B A) F" by (simp add:Line_not_on_trans)
  from P3 P27 P66 P70 have "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> \<exists>p. Line_on (Li H F) p \<and> Bet_Point (Se A B) p" by (simp add:Bet_swap_lemma_4)
  then obtain E :: Point where P71 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li H F) E \<and> Bet_Point (Se A B) E" by blast
  then have P72 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li A B) E" by (simp add:Line_Bet_on)
  from P36 have P73 : "Eq (Geos (Lin (Li C F)) add Emp) (Geos (Lin (Li F C)) add Emp)" by (simp add:Eq_rev)
  from P66 P73 have P74 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li F C) H" by (simp add:Line_on_trans)
  from P66 have "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Bet_Point (Se A G) H" by simp
  then have "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> 
    Bet_Point (Se A G) F" by (simp add:Point_Eq)
  then have P75 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> 
    Line_on (Li A G) F" by (simp add:Line_Bet_on)
  have P76 : "Line_on (Li A G) G" by (simp add:Line_on_rule)
  have P77 : "Line_on (Li B F) F" by (simp add:Line_on_rule)
  from P54 P59 P75 P76 P77 have P78 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li A G)) add Emp) (Geos (Lin (Li B F)) add Emp)" by (simp add:Line_unique)
  have P79 : "Line_on (Li A G) A" by (simp add:Line_on_rule)
  from P78 P79 have P80 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Line_on (Li B F) A" by (simp add:Line_on_trans)
  have P81 : "Line_on (Li B F) B" by (simp add:Line_on_rule)
  from P4 P6 P10 P80 P81 have P82 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li B F)) add Emp) (Geos (Lin (Li A B)) add Emp)" by (simp add:Line_unique)
  from P77 P82 have P83 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi H) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Line_on (Li A B) F" by (simp add:Line_on_trans)
  from P68 P83 have P84 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> \<not> Eq (Geos (Poi F) add Emp) (Geos (Poi H) add Emp)" by (blast intro:Eq_rev)
  from P46 have P85 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P74 P84 P85 have P86 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li F H) C" by (blast intro:Line_on_rev)
  from P84 have P87 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Lin (Li F H)) add Emp) (Geos (Lin (Li H F)) add Emp)" by (simp add:Line_rev)
  from P86 P87 have P88 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li H F) C" by (simp add:Line_on_trans)
  from P71 have "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Bet_Point (Se A B) E" by simp
  then have P89 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Bet_Point (Se A B) C" by (simp add:Point_Eq)
  from assms have "Inv (Bet_Point (Se C B) A) \<and> Inv (Bet_Point (Se B A) C)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se B A) C" by (simp add:Inv_def)
  then have P90 : "\<not> Bet_Point (Se A B) C" by (blast intro:Bet_rev)
  from P89 P90 have P91 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> \<not> Eq (Geos (Poi E) add Emp) (Geos (Poi C) add Emp)" by blast
  from P5 P71 P72 P88 P91 have P92 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow>
    Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin (Li H F)) add Emp)" by (simp add:Line_unique)
  from P4 P11 P12 have P93 : "Line_on (Li A B) D" by (simp add:Line_on_rev)
  from P92 P93 have P94 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li H F) D" by (simp add:Line_on_trans)
  have P95 : "Line_on (Li C F) F" by (simp add:Line_on_rule)
  have P96 : "Line_on (Li H F) H" by (simp add:Line_on_rule)
  have P97 : "Line_on (Li H F) F" by (simp add:Line_on_rule)
  from P66 P84 P95 P96 P97 have P98 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> 
    Eq (Geos (Lin (Li H F)) add Emp) (Geos (Lin (Li C F)) add Emp)" by (simp add:Line_unique)
  from P94 P98 have P99 : "Line_on_Seg (Li C F) (Se A G) \<Longrightarrow> Line_on (Li C F) D" by (simp add:Line_on_trans)
  from P37 P99 have P100 : "\<not> Line_on_Seg (Li C F) (Se A G)" by blast
  from P65 P100 have "Line_on_Seg (Li C F) (Se D G)" by blast
  then have "\<exists>p. Line_on (Li C F) p \<and> Bet_Point (Se D G) p" by (simp add:Line_on_Seg_rule)
  then obtain H2 :: Point where P101 : "Line_on (Li C F) H2 \<and> Bet_Point (Se D G) H2" by blast
  from P23 have "Eq (Geos (Lin (Li B D)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Eq_rev)
  then have P102 : "Line_on (Li B D) F \<Longrightarrow> Line_on (Li A D) F" by (simp add:Line_on_trans)
  from P25 P102 have P103 : "\<not> Line_on (Li B D) F" by blast
  from P18 have P104 : "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi D) add Emp)" by (blast intro:Eq_rev)
  from P27 P101 P103 P104 have "\<exists>p. Line_on (Li H2 F) p \<and> Bet_Point (Se D B) p" by (simp add:Bet_swap_lemma_4)
  then obtain C2 :: Point where P105 : "Line_on (Li H2 F) C2 \<and> Bet_Point (Se D B) C2" by blast
  have "Line_on (Li H2 F) F" by (simp add:Line_on_rule)
  then have P106 : "Eq (Geos (Lin (Li H2 F)) add Emp) (Geos (Lin (Li B D)) add Emp) \<Longrightarrow> Line_on (Li B D) F" by (simp add:Line_on_trans)
  from P103 P106 have P107 : "\<not> Eq (Geos (Lin (Li H2 F)) add Emp) (Geos (Lin (Li B D)) add Emp)" by blast
  from P73 P101 have P108 : "Line_on (Li F C) H2" by (simp add:Line_on_trans)
  from P101 have "Bet_Point (Se D G) H2" by simp
  then have "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Bet_Point (Se D G) F" by (simp add:Point_Eq)
  then have P109 : "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li D G) F" by (simp add:Line_Bet_on)
  have P110 : "Line_on (Li D G) G" by (simp add:Line_on_rule)
  from P54 P59 P77 P109 P110 have P111 : "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li B F)) add Emp) (Geos (Lin (Li D G)) add Emp)" by (simp add:Line_unique)
  from P81 P111 have P112 : "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li D G) B" by (simp add:Line_on_trans)
  have P113 : "Line_on (Li D G) D" by (simp add:Line_on_rule)
  from P11 P18 P32 P112 P113 have P114 : "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow>
    Eq (Geos (Lin (Li D G)) add Emp) (Geos (Lin (Li A D)) add Emp)" by (simp add:Line_unique)
  from P110 P114 have P115 : "Eq (Geos (Poi H2) add Emp) (Geos (Poi F) add Emp) \<Longrightarrow> Line_on (Li A D) G" by (simp add:Line_on_trans)
  from P28 P115 have P116 : "\<not> Eq (Geos (Poi F) add Emp) (Geos (Poi H2) add Emp)" by (blast intro:Eq_rev)
  from P31 P108 P116 have P117 : "Line_on (Li F H2) C" by (simp add:Line_on_rev)
  from P116 have P118 : "Eq (Geos (Lin (Li F H2)) add Emp) (Geos (Lin (Li H2 F)) add Emp)" by (simp add:Line_rev)
  from P117 P118 have P119 : "Line_on (Li H2 F) C" by (simp add:Line_on_trans)
  from P105 have P121 : "Line_on (Li B D) C2" by (simp add:Line_Bet_on)
  from P24 P105 P107 P119 P121 have P122 : "Eq (Geos (Poi C2) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Line_unique_Point)
  from P105 have P123 : "Bet_Point (Se D B) C2" by simp
  from P122 P123 have "Bet_Point (Se D B) C" by (simp add:Point_Eq)
  thus "Bet_Point (Se B D) C" by (blast intro:Bet_rev)
qed

lemma(in Order_Rule) Bet_swap_134_124 : 
  assumes 
    "Bet_Point (Se A C) B"
    "Bet_Point (Se A D) C"
  shows "Bet_Point (Se A D) B"
proof -
  from assms have P1 : "Bet_Point (Se B D) C" by (blast intro:Bet_swap_134_234)
  from assms P1 show "Bet_Point (Se A D) B" by (blast intro:Bet_swap_234_124)
qed

theorem(in Order_Rule) Bet_swap_243_124 : 
  assumes 
    "Bet_Point (Se A D) B"
    "Bet_Point (Se B D) C"
  shows "Bet_Point (Se A C) B"
proof -
  from assms have P1 : "Bet_Point (Se D B) C" by (simp add:Bet_rev)
  from assms have P2 : "Bet_Point (Se D A) B" by (simp add:Bet_rev)
  from P1 P2 have "Bet_Point (Se C A) B" by (blast intro:Bet_swap_134_234)
  thus "Bet_Point (Se A C) B" by (simp add:Bet_rev)
qed

theorem(in Order_Rule) Bet_swap_243_143 : 
  assumes 
    "Bet_Point (Se A D) B"
    "Bet_Point (Se B D) C"
  shows "Bet_Point (Se A D) C"
proof -
  from assms have P1 : "Bet_Point (Se D B) C" by (simp add:Bet_rev)
  from assms have P2 : "Bet_Point (Se D A) B" by (simp add:Bet_rev)
  from P1 P2 have "Bet_Point (Se D A) C" by (blast intro:Bet_swap_134_124)
  thus "Bet_Point (Se A D) C" by (simp add:Bet_rev)
qed

text\<open>Theorem5\<close>

lemma(in Order_Rule) Bet_four_Point_case : 
  assumes 
    "Line_on l1 P"
    "Line_on l1 Q"
    "Line_on l1 R"
    "Line_on l1 S"
    "Bet_Point (Se P R) Q"
    "\<not> Eq (Geos (Poi P) add Emp) (Geos (Poi S) add Emp)"
    "\<not> Eq (Geos (Poi Q) add Emp) (Geos (Poi S) add Emp)"
    "\<not> Eq (Geos (Poi R) add Emp) (Geos (Poi S) add Emp)"
  shows "Bet_Point (Se P S) R \<or> Bet_Point (Se R S) P
    \<or> Bet_Point (Se P R) S \<and> Bet_Point (Se P S) Q
    \<or> Bet_Point (Se P Q) S \<or> Bet_Point (Se Q S) P"
proof -
  from assms have P1 : "\<not> Eq (Geos (Poi P) add Emp) (Geos (Poi R) add Emp)" by (simp add:Bet_Point_def)
  from assms have P2 : "\<not> Eq (Geos (Poi S) add Emp) (Geos (Poi P) add Emp)" by (blast intro:Eq_rev)
  from assms P1 P2 have "Bet_Point (Se P S) R \<or> Bet_Point (Se S R) P \<or> Bet_Point (Se R P) S" by (simp add:Bet_case)
  then have P3 : "Bet_Point (Se P S) R \<or> Bet_Point (Se R S) P \<or> Bet_Point (Se P R) S" by (blast intro:Bet_rev)
  from assms have P4 : "\<not> Eq (Geos (Poi S) add Emp) (Geos (Poi Q) add Emp)" by (blast intro:Eq_rev)
  from assms have P5 : "\<not> Eq (Geos (Poi Q) add Emp) (Geos (Poi P) add Emp)" by (simp add:Bet_Point_def)
  from assms P4 P5 have "Bet_Point (Se P Q) S \<or> Bet_Point (Se Q S) P \<or> Bet_Point (Se S P) Q" by (simp add:Bet_case)
  then have P6 : "Bet_Point (Se P Q) S \<or> Bet_Point (Se Q S) P \<or> Bet_Point (Se P S) Q" by (blast intro:Bet_rev)
  from P3 P6 show "Bet_Point (Se P S) R \<or> Bet_Point (Se R S) P
    \<or> Bet_Point (Se P R) S \<and> Bet_Point (Se P S) Q
    \<or> Bet_Point (Se P Q) S \<or> Bet_Point (Se Q S) P" by blast
qed

lemma(in Order_Rule) Plane_diffside_rev : 
  assumes 
    "Plane_diffside l1 p1 p2"
  shows "Plane_diffside l1 p2 p1"
proof -
  from assms have "\<exists>p. Bet_Point (Se p1 p2) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by (simp add:Plane_diffside_def)
  then obtain p3 :: Point where P1 : "Bet_Point (Se p1 p2) p3 \<and> Line_on l1 p3 \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by blast
  then have P2 : "Bet_Point (Se p2 p1) p3" by (simp add:Bet_rev)
  from P1 P2 have "\<exists>p. Bet_Point (Se p2 p1) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p2 \<and> \<not> Line_on l1 p1" by blast
  thus "Plane_diffside l1 p2 p1" by (simp add:Plane_diffside_def)
qed

lemma(in Order_Rule) Plane_sameside_rev : 
  assumes 
    "Plane_sameside l1 p1 p2"
  shows "Plane_sameside l1 p2 p1"
proof -
  have "Line_on_Seg l1 (Se p2 p1) \<Longrightarrow> \<exists>p. Line_on l1 p \<and> Bet_Point (Se p2 p1) p" by (simp add:Line_on_Seg_rule)
  then obtain p3 :: Point where P1 : "Line_on_Seg l1 (Se p2 p1) \<Longrightarrow> 
    Line_on l1 p3 \<and> Bet_Point (Se p2 p1) p3" by blast
  then have P2 : "Line_on_Seg l1 (Se p2 p1) \<Longrightarrow> Bet_Point (Se p1 p2) p3" by (simp add:Bet_rev)
  from P1 P2 have "Line_on_Seg l1 (Se p2 p1) \<Longrightarrow> \<exists>p. Line_on l1 p \<and> Bet_Point (Se p1 p2) p" by blast
  then have "Line_on_Seg l1 (Se p2 p1) \<Longrightarrow> Line_on_Seg l1 (Se p1 p2)" by (simp add:Line_on_Seg_rule)
  then have P3 : "\<not> Line_on_Seg l1 (Se p1 p2) \<Longrightarrow> \<not> Line_on_Seg l1 (Se p2 p1)" by blast
  from assms have P4 : "\<not> Line_on_Seg l1 (Se p1 p2) \<and> \<not> Line_on l1 p1 
    \<and> \<not> Line_on l1 p2 \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Plane_sameside_def)
  from P3 P4 have P5 : "\<not> Line_on_Seg l1 (Se p2 p1)" by blast
  from P4 have P6 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from P4 P5 P6 show "Plane_sameside l1 p2 p1" by (simp add:Plane_sameside_def)
qed

lemma(in Order_Rule) Plane_sameside_not_diffside : 
  assumes N : 
    "Plane_sameside l1 p1 p2"
  shows "\<not> Plane_diffside l1 p1 p2"
proof 
  assume W : "Plane_diffside l1 p1 p2"
  then have "\<exists>p. Bet_Point (Se p1 p2) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by (simp add:Plane_diffside_def)
  then have "\<exists>p. Line_on l1 p \<and> Bet_Point (Se p1 p2) p" by blast
  then have P1 : "Line_on_Seg l1 (Se p1 p2)" by (simp add:Line_on_Seg_rule)
  from N have P2 : "\<not> Line_on_Seg l1 (Se p1 p2)" by (simp add:Plane_sameside_def)
  from P1 P2 show False by blast
qed

lemma(in Order_Rule) Plane_diffside_not_sameside : 
  assumes N :
    "Plane_diffside l1 p1 p2"
  shows "\<not> Plane_sameside l1 p1 p2"
proof 
  assume W : "Plane_sameside l1 p1 p2"
  then have P1 : "\<not> Plane_diffside l1 p1 p2" by (simp add:Plane_sameside_not_diffside)
  from N P1 show False by blast
qed

lemma(in Order_Rule) Plane_not_sameside_diffside : 
  assumes "\<not> Plane_sameside l1 p1 p2"
    "\<not> Line_on l1 p1" "\<not> Line_on l1 p2"
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
  shows "Plane_diffside l1 p1 p2"
proof -
  from assms have P1 : "\<not> Line_on_Seg l1 (Se p1 p2) \<Longrightarrow> Plane_sameside l1 p1 p2" by (simp add:Plane_sameside_def)
  from assms P1 have P2 : "Line_on_Seg l1 (Se p1 p2)" by blast
  from P2 have P3 : "\<exists>p. Line_on l1 p \<and> Bet_Point (Se p1 p2) p" by (simp add:Line_on_Seg_rule)
  from assms P3 have "\<exists>p. Bet_Point (Se p1 p2) p
    \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by blast
  thus "Plane_diffside l1 p1 p2" by (simp add:Plane_diffside_def)
qed

lemma(in Order_Rule) Plane_not_diffside_sameside : 
  assumes "\<not> Plane_diffside l1 p1 p2"
    "\<not> Line_on l1 p1" "\<not> Line_on l1 p2"
    "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)"
  shows "Plane_sameside l1 p1 p2"
proof -
  from assms have P1 : "\<not> Plane_sameside l1 p1 p2 \<Longrightarrow> Plane_diffside l1 p1 p2" by (simp add:Plane_not_sameside_diffside)
  from assms P1 show "Plane_sameside l1 p1 p2" by blast
qed

lemma(in Order_Rule) Plane_Line_diff_trans : 
  assumes 
    "Plane_diffside l1 p1 p2"
    "Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
  shows "Plane_diffside l2 p1 p2"
proof -
  from assms have "\<exists>p. Bet_Point (Se p1 p2) p \<and> Line_on l1 p \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by (simp add:Plane_diffside_def)
  then obtain p3 :: Point where P1 : "Bet_Point (Se p1 p2) p3 \<and> Line_on l1 p3 \<and> \<not> Line_on l1 p1 \<and> \<not> Line_on l1 p2" by blast
  from assms P1 have P2 : "Line_on l2 p3" by (simp add:Line_on_trans)
  from assms P1 have P3 : "\<not> Line_on l2 p1" by (simp add:Line_not_on_trans)
  from assms P1 have P4 : "\<not> Line_on l2 p2" by (simp add:Line_not_on_trans)
  from P1 P2 P3 P4 have "\<exists>p. Bet_Point (Se p1 p2) p \<and> Line_on l2 p \<and> \<not> Line_on l2 p1 \<and> \<not> Line_on l2 p2" by blast
  thus "Plane_diffside l2 p1 p2" by (simp add:Plane_diffside_def)
qed

lemma(in Order_Rule) Plane_Line_trans : 
  assumes 
    "Plane_sameside l1 p1 p2"
    "Eq (Geos (Lin l1) add Emp) (Geos (Lin l2) add Emp)"
  shows "Plane_sameside l2 p1 p2"
proof -
  have "Line_on_Seg l2 (Se p1 p2) \<Longrightarrow> \<exists>p. Line_on l2 p \<and> Bet_Point (Se p1 p2) p" by (simp add:Line_on_Seg_rule)
  then obtain p3 :: Point where P1 : "Line_on_Seg l2 (Se p1 p2) \<Longrightarrow> Line_on l2 p3 \<and> Bet_Point (Se p1 p2) p3" by blast
  from assms P1 have P2 : "Line_on_Seg l2 (Se p1 p2) \<Longrightarrow> Line_on l1 p3" by (blast intro:Line_on_trans Eq_rev)
  from P1 P2 have "Line_on_Seg l2 (Se p1 p2) \<Longrightarrow> \<exists>p. Line_on l1 p \<and> Bet_Point (Se p1 p2) p" by blast
  then have P3 : "Line_on_Seg l2 (Se p1 p2) \<Longrightarrow> Line_on_Seg l1 (Se p1 p2)" by (simp add:Line_on_Seg_rule)
  from assms have P4 : "\<not> Line_on_Seg l1 (Se p1 p2) \<and> \<not> Line_on l1 p1 
    \<and> \<not> Line_on l1 p2 \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Plane_sameside_def)
  from P3 P4 have P5 : "\<not> Line_on_Seg l2 (Se p1 p2)" by blast
  from assms P4 have P6 : "Line_on l2 p1 \<Longrightarrow> Line_on l1 p1" by (blast intro:Line_on_trans Eq_rev)
  from P4 P6 have P7 : "\<not> Line_on l2 p1" by blast
  from assms P4 have P8 : "Line_on l2 p2 \<Longrightarrow> Line_on l1 p2" by (blast intro:Line_on_trans Eq_rev)
  from P4 P8 have P9 : "\<not> Line_on l2 p2" by blast
  from P4 P5 P7 P9 show "Plane_sameside l2 p1 p2" by (simp add:Plane_sameside_def)
qed

lemma(in Order_Rule) Line_other_Point : 
  assumes "Line_on l1 p1"
  shows "\<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)"
proof -
  have "\<exists>p q. Line_on l1 p \<and> Line_on l1 q \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp)" by (blast intro:Line_on_exist)
  then obtain p2 p3 :: Point where P1 : "Line_on l1 p2 \<and> Line_on l1 p3 \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by blast
  then have P2 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp) \<Longrightarrow>
    Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_trans Eq_rev)
  from P1 P2 have "\<not> (Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp))" by blast
  then have P3 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)
    \<or> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)
    \<or> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by blast
  from P1 have P4 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp) \<Longrightarrow>
    \<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)" by blast
  from P1 have P5 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp) \<Longrightarrow>
    \<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)" by blast
  from P1 have P6 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p2) add Emp) \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp) \<Longrightarrow>
    \<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)" by blast
  from P3 P4 P5 P6 show "\<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)" by blast
qed

lemma(in Order_Rule) Plane_Bet_sameside : 
  assumes 
    "Bet_Point (Se p1 p3) p2"
    "Line_on l1 p1"
    "\<not> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)"
  shows "Plane_sameside l1 p2 p3"
proof -
  from assms have "\<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p) add Emp)" by (simp add:Line_other_Point)
  then obtain p4 :: Point where P1 : "Line_on l1 p4 \<and> \<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp)" by blast
  have P2 : "Line_on (Li p4 p1) p4" by (simp add:Line_on_rule)
  have P3 : "Line_on (Li p4 p1) p1" by (simp add:Line_on_rule)
  have "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> 
    (\<exists>p. Bet_Point (Se p2 p3) p \<and> Line_on (Li p4 p1) p \<and> \<not> Line_on (Li p4 p1) p2 \<and> \<not> Line_on (Li p4 p1) p3)" by (simp add:Plane_diffside_def)
  then obtain p5 :: Point where P4 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> 
    Bet_Point (Se p2 p3) p5 \<and> Line_on (Li p4 p1) p5 \<and> \<not> Line_on (Li p4 p1) p2 \<and> \<not> Line_on (Li p4 p1) p3" by blast
  then have P5 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Bet_Point (Se p3 p2) p5" by (simp add:Bet_rev)
  from assms have P6 : "Bet_Point (Se p3 p1) p2" by (simp add:Bet_rev)
  from P5 P6 have "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Bet_Point (Se p3 p1) p5" by (blast intro:Bet_swap_134_124)
  then have P7 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Line_on (Li p3 p1) p5" by (simp add:Line_Bet_on)
  have P8 : "Line_on (Li p3 p1) p1" by (simp add:Line_on_rule)
  from P4 have "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Bet_Point (Se p2 p3) p5" by simp
  then have P9 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Eq (Geos (Poi p5) add Emp) (Geos (Poi p1) add Emp) \<Longrightarrow>
    Bet_Point (Se p2 p3) p1" by (simp add:Point_Eq)
  from assms have "Inv (Bet_Point (Se p3 p2) p1) \<and> Inv (Bet_Point (Se p2 p1) p3)" by (simp add:Bet_iff)
  then have "\<not> Bet_Point (Se p3 p2) p1" by (simp add:Inv_def)
  then have P10 : "\<not> Bet_Point (Se p2 p3) p1" by (blast intro:Bet_rev)
  from P9 P10 have P11 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> \<not> Eq (Geos (Poi p5) add Emp) (Geos (Poi p1) add Emp)" by blast
  from P3 P4 P7 P8 P11 have P12 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> 
    Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin (Li p4 p1)) add Emp)" by (simp add:Line_unique)
  have P13 : "Line_on (Li p3 p1) p3" by (simp add:Line_on_rule)
  from P12 P13 have P14 : "Plane_diffside (Li p4 p1) p2 p3 \<Longrightarrow> Line_on (Li p4 p1) p3" by (simp add:Line_on_trans)
  from P4 P14 have P15 : "\<not> Plane_diffside (Li p4 p1) p2 p3" by blast
  from assms P1 P2 P3 have "Eq (Geos (Lin (Li p4 p1)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  then have P16 : "Plane_diffside l1 p2 p3 \<Longrightarrow> Plane_diffside (Li p4 p1) p2 p3" by (blast intro:Plane_Line_diff_trans Eq_rev)
  from P15 P16 have P17 : "\<not> Plane_diffside l1 p2 p3" by blast
  from assms have P18 : "Line_on (Li p1 p3) p2" by (simp add:Line_Bet_on)
  have P19 : "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  have P20 : "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  from assms have P21 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from assms P19 P20 P21 have P22 : "Line_on l1 p3 \<Longrightarrow> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from assms P22 have P23 : "\<not> Line_on l1 p3" by blast
  from assms have P24 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  from assms P18 P19 P24 have P25 : "Line_on l1 p2 \<Longrightarrow> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from assms P25 have P26 : "\<not> Line_on l1 p2" by blast
  from assms have "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  then have P27 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from P17 P23 P26 P27 show "Plane_sameside l1 p2 p3" by (simp add:Plane_not_diffside_sameside)
qed

lemma(in Order_Rule) Plane_Bet_diffside : 
  assumes 
    "Bet_Point (Se p1 p3) p2"
    "Line_on l1 p2"
    "\<not> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)"
  shows "Plane_diffside l1 p1 p3"
proof -
  from assms have "\<exists>p. Line_on l1 p \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p) add Emp)" by (simp add:Line_other_Point)
  then obtain p4 :: Point where P1 : "Line_on l1 p4 \<and> \<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp)" by blast
  from assms have P2 : "Line_on (Li p1 p3) p2" by (simp add:Line_Bet_on)
  from assms P1 P2 have P3 : "Line_on (Li p1 p3) p4 \<Longrightarrow> Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from assms P3 have P4 : "\<not> Line_on (Li p1 p3) p4" by blast
  have P5 : "Line_on (Li p4 p2) p4" by (simp add:Line_on_rule)
  have P6 : "Line_on (Li p4 p2) p2" by (simp add:Line_on_rule)
  from assms P4 have P7 : "\<not> Eq (Geos (Lin (Li p4 p2)) add Emp) (Geos (Lin (Li p4 p3)) add Emp)" by (simp add:Line_Bet_not_Eq)
  from assms have "Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp) \<Longrightarrow> Bet_Point (Se p1 p3) p4" by (simp add:Point_Eq)
  then have P8 : "Eq (Geos (Poi p2) add Emp) (Geos (Poi p4) add Emp) \<Longrightarrow> Line_on (Li p1 p3) p4" by (simp add:Line_Bet_on)
  from assms P4 P8 have P9 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p2) add Emp)" by (blast intro:Eq_rev)
  have "Line_on (Li p1 p3) p3" by (simp add:Line_on_rule)
  then have P10 : "Eq (Geos (Poi p3) add Emp) (Geos (Poi p4) add Emp) \<Longrightarrow> Line_on (Li p1 p3) p4" by (simp add:Point_Eq)
  from assms P4 P10 have P11 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p3) add Emp)" by (blast intro:Eq_rev)
  from P7 P9 P11 have P12 : "\<not> Line_on (Li p4 p2) p3" by (simp add:Line_not_Eq_on)
  from assms have P13 : "Bet_Point (Se p3 p1) p2" by (simp add:Bet_rev)
  from assms have "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  then have P14 : "Eq (Geos (Lin (Li p1 p3)) add Emp) (Geos (Lin (Li p3 p1)) add Emp)" by (simp add:Line_rev)
  from assms P4 P14 have P15 : "\<not> Line_on (Li p3 p1) p4" by (simp add:Line_not_on_trans)
  from P13 P15 have P16 : "\<not> Eq (Geos (Lin (Li p4 p2)) add Emp) (Geos (Lin (Li p4 p1)) add Emp)" by (simp add:Line_Bet_not_Eq)
  have "Line_on (Li p1 p3) p1" by (simp add:Line_on_rule)
  then have P17 : "Eq (Geos (Poi p1) add Emp) (Geos (Poi p4) add Emp) \<Longrightarrow> Line_on (Li p1 p3) p4" by (simp add:Point_Eq)
  from assms P4 P17 have P18 : "\<not> Eq (Geos (Poi p4) add Emp) (Geos (Poi p1) add Emp)" by (blast intro:Eq_rev)
  from P9 P16 P18 have P19 : "\<not> Line_on (Li p4 p2) p1" by (simp add:Line_not_Eq_on)
  from assms P6 P12 P19 have "\<exists>p. Bet_Point (Se p1 p3) p \<and> Line_on (Li p4 p2) p \<and> \<not> Line_on (Li p4 p2) p1 \<and> \<not> Line_on (Li p4 p2) p3" by blast
  then have P20 : "Plane_diffside (Li p4 p2) p1 p3" by (simp add:Plane_diffside_def)
  from assms P1 P5 P6 have P21 : "Eq (Geos (Lin (Li p4 p2)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  from P20 P21 show "Plane_diffside l1 p1 p3" by (simp add:Plane_Line_diff_trans)
qed

lemma(in Order_Rule) Plane_trans_inv : 
  assumes 
    "Plane_diffside l1 A B"
    "Plane_diffside l1 A C"
    "\<not> Eq (Geos (Poi B) add Emp) (Geos (Poi C) add Emp)"
  shows "Plane_sameside l1 B C"
proof -
  from assms have "\<exists>p. Bet_Point (Se A B) p \<and> Line_on l1 p \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 B" by (simp add:Plane_diffside_def)
  then obtain D :: Point where P1 : "Bet_Point (Se A B) D \<and> Line_on l1 D \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 B" by blast
  then have P2 : "Bet_Point (Se A B) D" by simp
  from assms have "\<exists>p. Bet_Point (Se A C) p \<and> Line_on l1 p \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 C" by (simp add:Plane_diffside_def)
  then obtain p2 :: Point where P3 : "Bet_Point (Se A C) p2 \<and> Line_on l1 p2 \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 C" by blast
  then have "Bet_Point (Se A C) p2" by simp
  then have P4 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (simp add:Bet_Point_def)
  from P3 have P5 : "\<not> Line_on l1 C" by simp
  from P1 have P6 : "Line_on l1 D" by simp
  from P1 have P7 : "\<not> Line_on l1 A" by simp
  from P1 have P8 : "\<not> Line_on l1 B" by simp
  from P2 P5 P6 P7 P8 have P9 : "\<not> Line_on (Li A B) C \<Longrightarrow> Line_on_Seg l1 (Se A C) \<and> \<not> Line_on_Seg l1 (Se B C)
        \<or> Line_on_Seg l1 (Se B C) \<and> \<not> Line_on_Seg l1 (Se A C)" by (simp add:Pachets_axiom)
  from P3 have "Bet_Point (Se A C) p2 \<and> Line_on l1 p2" by simp
  then have "\<exists>p. Line_on l1 p \<and> Bet_Point (Se A C) p" by blast
  then have P10 : "Line_on_Seg l1 (Se A C)" by (simp add:Line_on_Seg_rule)
  from P9 P10 have P11 : "\<not> Line_on (Li A B) C \<Longrightarrow> \<not> Line_on_Seg l1 (Se B C)" by blast
  from assms P5 P8 P11 have P12 : "\<not> Line_on (Li A B) C \<Longrightarrow> Plane_sameside l1 B C" by (simp add:Plane_sameside_def)
  from P6 have P13 : "Eq (Geos (Poi D) add Emp) (Geos (Poi C) add Emp) \<Longrightarrow> Line_on l1 C" by (simp add:Point_Eq)
  from P5 P13 have P14 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi C) add Emp)" by blast
  from P2 have P15 : "Line_on (Li A B) D" by (simp add:Line_Bet_on)
  from P2 have P16 : "Line_on (Li A B) A" by (simp add:Line_on_rule)
  from P2 have P17 : "Line_on (Li A B) B" by (simp add:Line_on_rule)
  from assms P2 P4 P14 P15 P16 P17 have P18 : "Line_on (Li A B) C \<Longrightarrow> Bet_Point (Se A C) B \<or> Bet_Point (Se B C) A
    \<or> Bet_Point (Se A B) C \<and> Bet_Point (Se A C) D \<or> Bet_Point (Se A D) C \<or> Bet_Point (Se D C) A" by (simp add:Bet_four_Point_case)  
  from P2 have P19 : "Line_on (Li A B) C \<Longrightarrow> Bet_Point (Se A C) B \<Longrightarrow> Bet_Point (Se D C) B" by (blast intro:Bet_swap_134_234)
  have "Line_on (Li D C) C" by (simp add:Line_on_rule)
  then have P20 : "Eq (Geos (Lin (Li D C)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 C" by (simp add:Line_on_trans)
  from P5 P20 have P21 : "\<not> Eq (Geos (Lin (Li D C)) add Emp) (Geos (Lin l1) add Emp)" by blast
  from P6 P19 P21 have P22 : "Line_on (Li A B) C \<Longrightarrow> Bet_Point (Se A C) B \<Longrightarrow> Plane_sameside l1 B C" by (simp add:Plane_Bet_sameside)
  from P2 have "Bet_Point (Se B A) D" by (simp add:Bet_rev)
  then have P23 : "Bet_Point (Se B C) A \<Longrightarrow> Bet_Point (Se D C) A" by (blast intro:Bet_swap_134_234)
  from P6 P21 P23 have P24 : "Bet_Point (Se B C) A \<Longrightarrow> Plane_sameside l1 A C" by (simp add:Plane_Bet_sameside)
  from assms have P25 : "\<not> Plane_sameside l1 A C" by (simp add:Plane_diffside_not_sameside)
  from P24 P25 have P26 : "\<not> Bet_Point (Se B C) A" by blast 
  have "Bet_Point (Se A B) C \<and> Bet_Point (Se A C) D \<Longrightarrow> Bet_Point (Se B A) C \<and> Bet_Point (Se C A) D" by (simp add:Bet_rev)
  then have P27 : "Bet_Point (Se A B) C \<and> Bet_Point (Se A C) D \<Longrightarrow> Bet_Point (Se D B) C" by (blast intro:Bet_swap_243_124 Bet_rev)
  have "Line_on (Li D B) B" by (simp add:Line_on_rule)
  then have P28 : "Eq (Geos (Lin (Li D B)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 B" by (simp add:Line_on_trans)
  from P8 P28 have P29 : "\<not> Eq (Geos (Lin (Li D B)) add Emp) (Geos (Lin l1) add Emp)" by blast
  from P6 P27 P29 have P30 : "Bet_Point (Se A B) C \<and> Bet_Point (Se A C) D \<Longrightarrow> Plane_sameside l1 B C" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  have P31 : "Bet_Point (Se A D) C \<Longrightarrow> Bet_Point (Se D A) C" by (simp add:Bet_rev)
  have "Line_on (Li D A) A" by (simp add:Line_on_rule)
  then have P32 : "Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 A" by (simp add:Line_on_trans)
  from P7 P32 have P33 : "\<not> Eq (Geos (Lin (Li D A)) add Emp) (Geos (Lin l1) add Emp)" by blast
  from P6 P31 P33 have P34 : "Bet_Point (Se A D) C \<Longrightarrow> Plane_sameside l1 A C" by (simp add:Plane_Bet_sameside Plane_sameside_rev)
  from P25 P34 have P35 : "\<not> Bet_Point (Se A D) C" by blast
  from P6 P21 have P36 : "Bet_Point (Se D C) A \<Longrightarrow> Plane_sameside l1 A C" by (simp add:Plane_Bet_sameside)
  from P25 P36 have P37 : "\<not> Bet_Point (Se D C) A" by blast
  from P18 P22 P26 P30 P35 P37 have P38 : "Line_on (Li A B) C \<Longrightarrow> Plane_sameside l1 B C" by blast
  from P12 P38 show "Plane_sameside l1 B C" by blast
qed 

lemma(in Order_Rule) Plane_trans : 
  assumes 
    "Plane_sameside l1 A B"
    "Plane_diffside l1 A C"
  shows "Plane_diffside l1 B C"
proof -
  from assms have "\<exists>p. Bet_Point (Se A C) p \<and> Line_on l1 p \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 C" by (simp add:Plane_diffside_def)
  then obtain D :: Point where P1 : "Bet_Point (Se A C) D \<and> Line_on l1 D \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 C" by blast
  from assms have P2 : "\<not> Line_on l1 B" by (simp add:Plane_sameside_def)
  from P1 have P3 : "Bet_Point (Se A C) D" by simp
  from P1 have P4 : "\<not> Line_on l1 A" by simp
  from P1 have P5 : "\<not> Line_on l1 C" by simp
  from P1 have P6 : "Line_on l1 D" by simp
  from P2 P3 P4 P5 P6 have P7 : "\<not> Line_on (Li A C) B \<Longrightarrow> Line_on_Seg l1 (Se A B) \<and> \<not> Line_on_Seg l1 (Se C B)
    \<or> Line_on_Seg l1 (Se C B) \<and> \<not> Line_on_Seg l1 (Se A B)" by (simp add:Pachets_axiom)
  have P8 : "Line_on_Seg l1 (Se A B) \<Longrightarrow> \<exists>p. Line_on l1 p \<and> Bet_Point (Se A B) p" by (simp add:Line_on_Seg_rule)
  from P2 P4 P8 have "Line_on_Seg l1 (Se A B) \<Longrightarrow> \<exists>p. Bet_Point (Se A B) p \<and> Line_on l1 p \<and> \<not> Line_on l1 A \<and> \<not> Line_on l1 B" by blast
  then have "Line_on_Seg l1 (Se A B) \<Longrightarrow> Plane_diffside l1 A B" by (simp add:Plane_diffside_def)
  then have P9 : "Line_on_Seg l1 (Se A B) \<Longrightarrow> \<not> Plane_sameside l1 A B" by (simp add:Plane_diffside_not_sameside)
  from assms P9 have P10 : "\<not> Line_on_Seg l1 (Se A B)" by blast
  from P7 P10 have "\<not> Line_on (Li A C) B \<Longrightarrow> Line_on_Seg l1 (Se C B)"by blast
  then have P11 : "\<not> Line_on (Li A C) B \<Longrightarrow> \<exists>p. Line_on l1 p \<and> Bet_Point (Se C B) p" by (simp add:Line_on_Seg_rule)
  from P2 P5 P11 have "\<not> Line_on (Li A C) B \<Longrightarrow> \<exists>p. Bet_Point (Se C B) p \<and> Line_on l1 p \<and> \<not> Line_on l1 C \<and> \<not> Line_on l1 B" by blast
  then have "\<not> Line_on (Li A C) B \<Longrightarrow> Plane_diffside l1 C B" by (simp add:Plane_diffside_def)
  then have P12 : "\<not> Line_on (Li A C) B \<Longrightarrow> Plane_diffside l1 B C" by (simp add:Plane_diffside_rev)
  have P13 : "Line_on (Li A C) A" by (simp add:Line_on_rule)
  have P14 : "Line_on (Li A C) C" by (simp add:Line_on_rule)
  from P3 have P15 : "Line_on (Li A C) D" by (simp add:Line_Bet_on)
  from assms have "Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> Plane_sameside l1 A C" by (blast intro:Point_Eq Eq_rev)
  then have P16 : "Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> \<not> Plane_diffside l1 A C" by (simp add:Plane_sameside_not_diffside)
  from assms P16 have P17 : "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi B) add Emp)" by blast
  from P6 have P18 : "Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp) \<Longrightarrow> Line_on l1 B" by (simp add:Point_Eq)
  from P2 P18 have P19 : "\<not> Eq (Geos (Poi D) add Emp) (Geos (Poi B) add Emp)" by blast
  from assms have P20 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi B) add Emp)" by (simp add:Plane_sameside_def)
  from assms P3 P13 P14 P15 P17 P19 P20 have P21 : "Line_on (Li A C) B \<Longrightarrow> Bet_Point (Se A B) C \<or> Bet_Point (Se C B) A
    \<or> Bet_Point (Se A C) B \<and> Bet_Point (Se A B) D \<or> Bet_Point (Se A D) B \<or> Bet_Point (Se D B) A" by (simp add:Bet_four_Point_case)
  from P3 have P22 : "Bet_Point (Se A B) C \<Longrightarrow> Bet_Point (Se A B) D" by (blast intro:Bet_swap_134_124)
  have "Line_on (Li A B) A" by (simp add:Line_on_rule)
  then have P23 : "Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 A" by (simp add:Line_on_trans)
  from P4 P23 have P24 : "\<not> Eq (Geos (Lin (Li A B)) add Emp) (Geos (Lin l1) add Emp)" by blast
  from P6 P22 P24 have "Bet_Point (Se A B) C \<Longrightarrow> Plane_diffside l1 A B" by (simp add:Plane_Bet_diffside)
  then have P25 : "Bet_Point (Se A B) C \<Longrightarrow> \<not> Plane_sameside l1 A B" by (simp add:Plane_diffside_not_sameside)
  from assms P25 have P26 : "\<not> Bet_Point (Se A B) C" by blast
  from P3 have P27 : "Bet_Point (Se C A) D" by (simp add:Bet_rev)
  from P27 have P28 : "Bet_Point (Se C B) A \<Longrightarrow> Bet_Point (Se C B) D" by (blast intro:Bet_swap_134_124)
  have "Line_on (Li C B) B" by (simp add:Line_on_rule)
  then have P29 : "Eq (Geos (Lin (Li C B)) add Emp) (Geos (Lin l1) add Emp) \<Longrightarrow> Line_on l1 B" by (simp add:Line_on_trans)
  from P2 P29 have P30 : "\<not> Eq (Geos (Lin (Li C B)) add Emp) (Geos (Lin l1) add Emp)" by blast
  from P6 P28 P30 have "Bet_Point (Se C B) A \<Longrightarrow> Plane_diffside l1 C B" by (simp add:Plane_Bet_diffside)
  then have P31 : "Bet_Point (Se C B) A \<Longrightarrow> Plane_diffside l1 B C" by (blast intro:Plane_diffside_rev)  
  from P6 P24 have "Bet_Point (Se A B) D \<Longrightarrow> Plane_diffside l1 A B" by (simp add:Plane_Bet_diffside)
  then have P32 : "Bet_Point (Se A B) D \<Longrightarrow> \<not> Plane_sameside l1 A B" by (simp add:Plane_diffside_not_sameside)
  from assms P32 have "\<not> Bet_Point (Se A B) D" by blast
  then have P33 : "\<not> (Bet_Point (Se A C) B \<and> Bet_Point (Se A B) D)" by blast
  from P3 have P34 : "Bet_Point (Se A D) B \<Longrightarrow> Bet_Point (Se C B) D" by (blast intro:Bet_swap_134_234 Bet_rev)
  from P6 P30 P34 have "Bet_Point (Se A D) B \<Longrightarrow> Plane_diffside l1 C B" by (simp add:Plane_Bet_diffside)
  then have P35 : "Bet_Point (Se A D) B \<Longrightarrow> Plane_diffside l1 B C" by (simp add:Plane_diffside_rev)
  from P27 have P36 : "Bet_Point (Se D B) A \<Longrightarrow> Bet_Point (Se C B) D" by (blast intro:Bet_swap_234_124 Bet_rev)
  from P6 P30 P36 have "Bet_Point (Se D B) A \<Longrightarrow> Plane_diffside l1 C B" by (simp add:Plane_Bet_diffside)
  then have P37 : "Bet_Point (Se D B) A \<Longrightarrow> Plane_diffside l1 B C" by (simp add:Plane_diffside_rev)
  from P21 P26 P31 P33 P35 P37 have P38 : "Line_on (Li A C) B \<Longrightarrow> Plane_diffside l1 B C" by blast
  from P12 P38 show "Plane_diffside l1 B C" by blast
qed

lemma(in Order_Rule) Plane_sameside_trans : 
  assumes 
    "Plane_sameside l1 A B"
    "Plane_sameside l1 B C"
    "\<not> Eq (Geos (Poi C) add Emp) (Geos (Poi A) add Emp)"
  shows "Plane_sameside l1 A C"
proof -
  from assms have P1 : "Plane_diffside l1 A C \<Longrightarrow> Plane_diffside l1 B C" by (blast intro:Plane_trans)
  from assms have P2 : "\<not> Plane_diffside l1 B C" by (simp add:Plane_sameside_not_diffside)
  from P1 P2 have P3 : "\<not> Plane_diffside l1 A C" by blast
  from assms have P4 : "\<not> Line_on l1 A" by (simp add:Plane_sameside_def)
  from assms have P5 : "\<not> Line_on l1 C" by (simp add:Plane_sameside_def)
  from assms have P6 : "\<not> Eq (Geos (Poi A) add Emp) (Geos (Poi C) add Emp)" by (blast intro:Eq_rev)
  from P3 P4 P5 P6 show "Plane_sameside l1 A C" by (simp add:Plane_not_diffside_sameside)
qed

lemma (in Order_Rule) Seg_Bet_not_on : 
  assumes 
    "Bet_Point (Se p1 p3) p2"
  shows "\<not> Seg_on_Seg (Se p1 p2) (Se p2 p3)"
proof -
  from assms have "\<exists>l. Line_on l p1 \<and> Line_on l p3 \<and> Line_on l p2" by (simp add:Line_Bet_exist)
  then obtain l1 :: Line where P1 : "Line_on l1 p1 \<and> Line_on l1 p3 \<and> Line_on l1 p2" by blast
  have "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> \<exists>p. Bet_Point (Se p1 p2) p \<and> Bet_Point (Se p2 p3) p" by (simp add:Seg_on_Seg_rule)
  then obtain p4 :: Point where P2 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Bet_Point (Se p1 p2) p4 \<and> Bet_Point (Se p2 p3) p4" by blast
  then have P3 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Bet_Point (Se p2 p1) p4" by (blast intro:Bet_rev)
  from assms have P4 : "Bet_Point (Se p3 p1) p2" by (simp add:Bet_rev)
  from P3 P4 have P5 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Bet_Point (Se p3 p1) p4" by (blast intro:Bet_swap_243_143)
  have "\<exists>p q r. \<not> Line_on l1 p \<and> \<not> Line_on l1 q \<and> \<not> Line_on l1 r
        \<and> \<not> Eq (Geos (Poi p) add Emp) (Geos (Poi q) add Emp) \<and> \<not> Eq (Geos (Poi q) add Emp) (Geos (Poi r) add Emp)
        \<and> \<not> Eq (Geos (Poi r) add Emp) (Geos (Poi p) add Emp)" by (blast intro:Line_not_on_exist)
  then obtain p5 :: Point where P6 : "\<not> Line_on l1 p5" by blast
  have P7 : "Line_on (Li p5 p4) p5" by (simp add:Line_on_rule)
  have P8 : "Line_on (Li p3 p1) p3" by (simp add:Line_on_rule)
  have P9 : "Line_on (Li p3 p1) p1" by (simp add:Line_on_rule)
  from assms have P10 : "\<not> Eq (Geos (Poi p1) add Emp) (Geos (Poi p3) add Emp)" by (simp add:Bet_Point_def)
  from P1 P8 P9 P10 have "Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  then have P11 : "Line_on (Li p3 p1) p5 \<Longrightarrow> Line_on l1 p5" by (simp add:Line_on_trans)
  from P6 P11 have P12 : "\<not> Line_on (Li p3 p1) p5" by blast
  from P7 have P13 : "Eq (Geos (Lin (Li p5 p4)) add Emp) (Geos (Lin (Li p3 p1)) add Emp) \<Longrightarrow> Line_on (Li p3 p1) p5" by (simp add:Line_on_trans)
  from P12 P13 have P14 : "\<not> Eq (Geos (Lin (Li p3 p1)) add Emp) (Geos (Lin (Li p5 p4)) add Emp)" by (blast intro:Eq_rev)
  have P15 : "Line_on (Li p5 p4) p4" by (simp add:Line_on_rule)
  from P5 P14 P15 have P16 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_diffside (Li p5 p4) p3 p1" by (simp add:Plane_Bet_diffside)
  have P17 : "Line_on (Li p1 p2) p1" by (simp add:Line_on_rule)
  have P18 : "Line_on (Li p1 p2) p2" by (simp add:Line_on_rule)
  from assms have P19 : "\<not> Eq (Geos (Poi p2) add Emp) (Geos (Poi p1) add Emp)" by (simp add:Bet_Point_def)
  from P1 P17 P18 P19 have "Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  then have P20 : "Line_on (Li p1 p2) p5 \<Longrightarrow> Line_on l1 p5" by (simp add:Line_on_trans)
  from P6 P20 have P21 : "\<not> Line_on (Li p1 p2) p5" by blast
  from P7 have P22 : "Eq (Geos (Lin (Li p5 p4)) add Emp) (Geos (Lin (Li p1 p2)) add Emp) \<Longrightarrow> Line_on (Li p1 p2) p5" by (simp add:Line_on_trans)
  from P21 P22 have P23 : "\<not> Eq (Geos (Lin (Li p1 p2)) add Emp) (Geos (Lin (Li p5 p4)) add Emp)" by (blast intro:Eq_rev)
  from P2 have P24 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Bet_Point (Se p1 p2) p4" by simp
  from P15 P23 P24 have "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_diffside (Li p5 p4) p1 p2" by (simp add:Plane_Bet_diffside)
  then have P25 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_diffside (Li p5 p4) p2 p1" by (simp add:Plane_diffside_rev)
  have P26 : "Line_on (Li p2 p3) p2" by (simp add:Line_on_rule)
  have P27 : "Line_on (Li p2 p3) p3" by (simp add:Line_on_rule)
  from assms have P28 : "\<not> Eq (Geos (Poi p3) add Emp) (Geos (Poi p2) add Emp)" by (simp add:Bet_Point_def)
  from P1 P26 P27 P28 have "Eq (Geos (Lin (Li p2 p3)) add Emp) (Geos (Lin l1) add Emp)" by (simp add:Line_unique)
  then have P29 : "Line_on (Li p2 p3) p5 \<Longrightarrow> Line_on l1 p5" by (simp add:Line_on_trans)
  from P6 P29 have P30 : "\<not> Line_on (Li p2 p3) p5" by blast
  from P7 have P31 : "Eq (Geos (Lin (Li p5 p4)) add Emp) (Geos (Lin (Li p2 p3)) add Emp) \<Longrightarrow> Line_on (Li p2 p3) p5" by (simp add:Line_on_trans)
  from P30 P31 have P32 : "\<not> Eq (Geos (Lin (Li p2 p3)) add Emp) (Geos (Lin (Li p5 p4)) add Emp)" by (blast intro:Eq_rev)
  from P2 have P33 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Bet_Point (Se p2 p3) p4" by simp
  from P15 P32 P33 have P34 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_diffside (Li p5 p4) p2 p3" by (simp add:Plane_Bet_diffside)
  from P10 P25 P28 P34 have "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_sameside (Li p5 p4) p1 p3" by (blast intro:Plane_trans_inv)
  then have "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> Plane_sameside (Li p5 p4) p3 p1" by (simp add:Plane_sameside_rev)
  then have P35 : "Seg_on_Seg (Se p1 p2) (Se p2 p3) \<Longrightarrow> \<not> Plane_diffside (Li p5 p4) p3 p1" by (simp add:Plane_sameside_not_diffside)
  from P16 P35 show "\<not> Seg_on_Seg (Se p1 p2) (Se p2 p3)" by blast
qed

end
  