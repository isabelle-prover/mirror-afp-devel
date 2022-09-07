(* Title: thys/BlanksDoNotMatter.thy
   Author: Franz Regensburger (FABR) 04/2022
 *)

section \<open>Trailing Blanks on the input tape do not matter\<close>

theory BlanksDoNotMatter
  imports Turing
begin

(* ----- Configure sledgehammer ------ *)
sledgehammer_params[minimize=false,preplay_timeout=10,timeout=30,strict=true,
                    provers="e z3 cvc4 vampire "]

(*
sledgehammer_params[minimize=false,preplay_timeout=10,timeout=30,verbose=true,strict=true,
                    provers="spass e z3 cvc4 vampire "]
*)
(* ----------------------------------- *)


subsection \<open>Replication of symbols\<close>

abbreviation exponent :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<up> _" [100, 99] 100)
  where "x \<up> n == replicate n x"

lemma hd_repeat_cases:
  "P (hd (a \<up> m @ r)) \<longleftrightarrow> (m = 0 \<longrightarrow> P (hd r)) \<and> (\<forall>nat. m = Suc nat \<longrightarrow> P a)"
  by (cases m,auto)

lemma hd_repeat_cases':
  "P (hd (a \<up> m @ r)) = (if m = 0 then P (hd r) else P a)"
  by auto

(* hd_repeat_cases \<equiv> hd_repeat_cases'.
 * However, hd_repeat_cases' is better for rewriting
 *)

lemma
  "(if m = 0 then P (hd r) else P a) = ((m = 0 \<longrightarrow> P (hd r)) \<and> (\<forall>nat. m = Suc nat \<longrightarrow> P a))"
proof -
  have "(if m = 0 then P (hd r) else P a) = P (hd (a \<up> m @ r))" by auto
  also have "... = ((m = 0 \<longrightarrow> P (hd r)) \<and> (\<forall>nat. m = Suc nat \<longrightarrow> P a))"
    by (simp add: iffI hd_repeat_cases)
  finally show ?thesis .
qed

lemma split_head_repeat[simp]:
  "Oc # list1 = Bk \<up> j @ list2 \<longleftrightarrow> j = 0 \<and> Oc # list1 = list2"
  "Bk # list1 = Oc \<up> j @ list2 \<longleftrightarrow> j = 0 \<and> Bk # list1 = list2"
  "Bk \<up> j @ list2 = Oc # list1 \<longleftrightarrow> j = 0 \<and> Oc # list1 = list2"
  "Oc \<up> j @ list2 = Bk # list1 \<longleftrightarrow> j = 0 \<and> Bk # list1 = list2"
  by(cases j;force)+

lemma Bk_no_Oc_repeatE[elim]: "Bk # list = Oc \<up> t \<Longrightarrow> RR"
  by (cases t, auto)

lemma replicate_Suc_1: "a \<up> (z1 + Suc z2) = (a \<up> z1) @ (a \<up> Suc z2)"
  by (meson replicate_add)

lemma replicate_Suc_2: "a \<up> (z1 + Suc z2) = (a \<up> Suc z1) @ (a \<up> z2)"
    by (simp add: replicate_add)



subsection \<open>Trailing blanks on the left tape do not matter\<close>

text\<open>In this section we will show that we may add or remove trailing blanks on the
initial left and right portions of the tape at will.
However, we may not add or remove trailing blanks on the tape resulting from the computation.
The resulting tape is completely determined by the contents of the initial tape.\<close>

(* -------------------- Remove trailing blanks from the left tape -------------------------- *)

lemma step_left_tape_ShrinkBkCtx_right_Nil:
  assumes "step0 (s,CL@Bk\<up> z1 , []) tm = (s',l',r')"
    and "za < z1"
  shows "\<exists>CL' zb. l' = CL'@Bk\<up>za@Bk\<up>zb \<and>
                 (step0 (s,CL@Bk\<up>za, []) tm = (s',CL'@Bk\<up>za,r') \<or>
                  step0 (s,CL@Bk\<up>za, []) tm = (s',CL'@Bk\<up>(za-1),r'))"
proof (cases "fetch tm (s - 0) (read [])")
  case (Pair a s2)
  then have A1: "fetch tm (s - 0) (read []) = (a, s2)" .
  show ?thesis 
  proof (cases a)
    assume "a = WB"
    from \<open>a = WB\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, CL@Bk \<up> z1, [Bk])" by auto
    moreover from \<open>a = WB\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, []) tm =  (s2,CL@Bk\<up>za , [Bk])" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm = (s2,CL@Bk\<up>za , [Bk])"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, []) tm = (s2, CL @ Bk \<up> z1, [Bk])\<close> assms(1) by auto
  next
    assume "a = WO"
    from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, CL@Bk \<up> z1, [Oc])" by auto
    moreover from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, []) tm =  (s2,CL@Bk\<up>za , [Oc])" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm = (s2,CL@Bk\<up>za , [Oc])"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, []) tm = (s2, CL @ Bk \<up> z1, [Oc])\<close> assms(1) by auto
  next
    assume "a = Nop"
    from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, CL@Bk \<up> z1, [])" by auto
    moreover from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, []) tm =  (s2,CL@Bk\<up>za , [])" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm = (s2,CL@Bk\<up>za , [])"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, []) tm = (s2, CL @ Bk \<up> z1, [])\<close> assms(1) by auto
  next
    assume "a = R"
    from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, [Bk]@CL@Bk\<up>z1, [])"
      by auto
    moreover from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, []) tm =  (s2,[Bk]@CL@Bk\<up>za, [])" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm = (s2,[Bk]@CL@Bk\<up>za, [])"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, []) tm = (s2, [Bk] @ CL @ Bk \<up> z1, [])\<close>
      by (metis  append_Cons append_Nil assms(1) fst_conv snd_conv)
  next
    assume "a = L"
    show ?thesis
    proof (cases CL)
      case Nil
      then have "CL = []" .
      then show ?thesis
      proof (cases z1)
        case 0
        then have "z1 = 0" .
        with assms and \<open>CL = []\<close> show ?thesis by auto
      next
        case (Suc nat)
        then have "z1 = Suc nat" .
        from \<open>a = L\<close> and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and assms and A1
        have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, []@Bk \<up>(z1-1), [Bk])"
          by auto
        moreover from \<open>a = L\<close> and \<open>CL = []\<close> and A1 have "step0 (s, CL@Bk\<up>za, []) tm =  (s2, []@Bk\<up>(za-1) , [Bk])" by auto
        ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm =  (s2, []@Bk\<up>(za-1) , [Bk])"
          using assms using \<open>z1 = Suc nat\<close>
          by (metis diff_Suc_1 le_eq_less_or_eq less_Suc_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
        with assms  and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and \<open>step0 (s, CL@Bk\<up>z1, []) tm = (s2, [] @ Bk \<up> (z1 - 1), [Bk])\<close>
        show ?thesis
          by auto
      qed
    next
      case (Cons c cs)
      then have "CL = c # cs" .
      from \<open>a = L\<close> and \<open>CL = c # cs\<close> and assms and A1
      have "step0 (s, CL@Bk \<up> z1, []) tm =  (s2, cs@Bk \<up>z1, [c])"
        by auto
      moreover from \<open>a = L\<close> and \<open>CL = c # cs\<close> and A1
      have "step0 (s, CL@Bk\<up>za, []) tm =  (s2, cs@Bk \<up>za, [c])" by auto
      ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm =  (s2, cs@Bk \<up>za, [c])"
        using assms
        by (metis One_nat_def Suc_pred add_diff_inverse_nat neq0_conv not_less_eq not_less_zero replicate_add)
      with assms  and \<open>CL = c # cs\<close> and \<open>Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, []) tm =  (s2, cs@Bk \<up>za, [c])\<close>
      show ?thesis
        using \<open>step0 (s, CL @ Bk \<up> z1, []) tm = (s2, cs @ Bk \<up> z1, [c])\<close> 
        by (metis fst_conv nat_le_linear not_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add snd_conv)
    qed
  qed
qed

lemma step_left_tape_ShrinkBkCtx_right_Bk:
  assumes "step0 (s,CL@Bk\<up> z1 , Bk#rs) tm = (s',l',r')"
    and "za < z1"
  shows "\<exists>CL' zb. l' = CL'@Bk\<up>za@Bk\<up>zb \<and>
                 (step0 (s,CL@Bk\<up>za, Bk#rs) tm = (s',CL'@Bk\<up>za,r') \<or>
                  step0 (s,CL@Bk\<up>za, Bk#rs) tm = (s',CL'@Bk\<up>(za-1),r'))"
proof (cases "fetch tm (s - 0) (read (Bk#rs))")
  case (Pair a s2)
  then have A1: "fetch tm (s - 0) (read (Bk#rs)) = (a, s2)" .
  show ?thesis 
  proof (cases a)
    assume "a = WB"
    from \<open>a = WB\<close> and assms A1
    have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, CL@Bk \<up> z1, Bk#rs)"
      by (auto simp add:  split: if_splits)
    moreover from \<open>a = WB\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2,CL@Bk\<up>za , Bk#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm = (s2,CL@Bk\<up>za , Bk#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Bk#rs) tm = (s2, CL @ Bk \<up> z1, Bk#rs)\<close> assms(1) by auto
  next
    assume "a = WO"
    from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, CL@Bk \<up> z1, Oc#rs)" by auto
    moreover from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2,CL@Bk\<up>za , Oc#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm = (s2,CL@Bk\<up>za , Oc#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Bk#rs) tm = (s2, CL @ Bk \<up> z1, Oc#rs)\<close> assms(1) by auto
  next
    assume "a = Nop"
    from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, CL@Bk \<up> z1, Bk#rs)" by auto
    moreover from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2,CL@Bk\<up>za , Bk#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm = (s2,CL@Bk\<up>za , Bk#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Bk#rs) tm = (s2, CL @ Bk \<up> z1, Bk#rs)\<close> assms(1) by auto
  next
    assume "a = R"
    from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, [Bk]@CL@Bk\<up>z1, rs)"
      by auto
    moreover from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2,[Bk]@CL@Bk\<up>za, rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm = (s2,[Bk]@CL@Bk\<up>za, rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Bk#rs) tm = (s2, [Bk] @ CL @ Bk \<up> z1, rs)\<close>
      by (metis  append_Cons append_Nil assms(1) fst_conv snd_conv)
  next
    assume "a = L"
    show ?thesis
    proof (cases CL)
      case Nil
      then have "CL = []" .
      then show ?thesis
      proof (cases z1)
        case 0
        then have "z1 = 0" .
        with assms and \<open>CL = []\<close> show ?thesis by auto
      next
        case (Suc nat)
        then have "z1 = Suc nat" .
        from \<open>a = L\<close> and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and assms and A1
        have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, []@Bk \<up>(z1-1), Bk#Bk#rs)"
          by auto
        moreover from \<open>a = L\<close> and \<open>CL = []\<close> and A1 have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2, []@Bk\<up>(za-1) ,  Bk#Bk#rs)" by auto
        ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2, []@Bk\<up>(za-1) ,  Bk#Bk#rs)"
          using assms using \<open>z1 = Suc nat\<close>
          by (metis diff_Suc_1 le_eq_less_or_eq less_Suc_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
        with assms  and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and \<open>step0 (s, CL@Bk\<up>z1, Bk#rs) tm = (s2, [] @ Bk \<up> (z1 - 1),  Bk#Bk#rs)\<close>
        show ?thesis
          by auto
      qed
    next
      case (Cons c cs)
      then have "CL = c # cs" .
      from \<open>a = L\<close> and \<open>CL = c # cs\<close> and assms and A1
      have "step0 (s, CL@Bk \<up> z1, Bk#rs) tm =  (s2, cs@Bk \<up>z1, c#Bk#rs)"
        by auto
      moreover from \<open>a = L\<close> and \<open>CL = c # cs\<close> and A1
      have "step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2, cs@Bk \<up>za, c#Bk#rs)" by auto
      ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2, cs@Bk \<up>za, c#Bk#rs)"
        using assms
        by (metis One_nat_def Suc_pred add_diff_inverse_nat neq0_conv not_less_eq not_less_zero replicate_add)
      with assms  and \<open>CL = c # cs\<close> and \<open>Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Bk#rs) tm =  (s2, cs@Bk \<up>za, c#Bk#rs)\<close>
      show ?thesis
        using \<open>step0 (s, CL @ Bk \<up> z1, Bk#rs) tm = (s2, cs @ Bk \<up> z1, c#Bk#rs)\<close> 
        by (metis fst_conv nat_le_linear not_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add snd_conv)
    qed
  qed
qed

lemma step_left_tape_ShrinkBkCtx_right_Oc:
  assumes "step0 (s,CL@Bk\<up> z1 , Oc#rs) tm = (s',l',r')"
    and "za < z1"
  shows "\<exists>CL' zb. l' = CL'@Bk\<up>za@Bk\<up>zb \<and>
                 (step0 (s,CL@Bk\<up>za, Oc#rs) tm = (s',CL'@Bk\<up>za,r') \<or>
                  step0 (s,CL@Bk\<up>za, Oc#rs) tm = (s',CL'@Bk\<up>(za-1),r'))"
proof (cases "fetch tm (s - 0) (read (Oc#rs))")
  case (Pair a s2)
  then have A1: "fetch tm (s - 0) (read (Oc#rs)) = (a, s2)" .
  show ?thesis 
  proof (cases a)
    assume "a = WB"
    from \<open>a = WB\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, CL@Bk \<up> z1, Bk#rs)" by auto
    moreover from \<open>a = WB\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2,CL@Bk\<up>za , Bk#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm = (s2,CL@Bk\<up>za ,Bk#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Oc#rs) tm = (s2, CL @ Bk \<up> z1, Bk#rs)\<close> assms(1) by auto
  next
    assume "a = WO"
    from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, CL@Bk \<up> z1, Oc#rs)" by auto
    moreover from \<open>a = WO\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2,CL@Bk\<up>za , Oc#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm = (s2,CL@Bk\<up>za , Oc#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Oc#rs) tm = (s2, CL @ Bk \<up> z1, Oc#rs)\<close> assms(1) by auto
  next
    assume "a = Nop"
    from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, CL@Bk \<up> z1, Oc#rs)" by auto
    moreover from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2,CL@Bk\<up>za , Oc#rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm = (s2,CL@Bk\<up>za , Oc#rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Oc#rs) tm = (s2, CL @ Bk \<up> z1, Oc#rs)\<close> assms(1) by auto
  next
    assume "a = R"
    from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, [Oc]@CL@Bk\<up>z1, rs)"
      by auto
    moreover from \<open>a = R\<close> and assms A1 have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2,[Oc]@CL@Bk\<up>za, rs)" by auto
    ultimately have "Bk\<up>z1 = Bk\<up>za@Bk\<up>(z1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm = (s2,[Oc]@CL@Bk\<up>za, rs)"
      using assms
      by (metis le_eq_less_or_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
    then show ?thesis
      using \<open>step0 (s, CL @ Bk \<up> z1, Oc#rs) tm = (s2, [Oc] @ CL @ Bk \<up> z1, rs)\<close>
      by (metis  append_Cons append_Nil assms(1) fst_conv snd_conv)
  next
    assume "a = L"
    show ?thesis
    proof (cases CL)
      case Nil
      then have "CL = []" .
      then show ?thesis
      proof (cases z1)
        case 0
        then have "z1 = 0" .
        with assms and \<open>CL = []\<close> show ?thesis by auto
      next
        case (Suc nat)
        then have "z1 = Suc nat" .
        from \<open>a = L\<close> and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and assms and A1
        have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, []@Bk \<up>(z1-1), Bk#Oc#rs)"
          by auto
        moreover from \<open>a = L\<close> and \<open>CL = []\<close> and A1 have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2, []@Bk\<up>(za-1) ,  Bk#Oc#rs)" by auto
        ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2, []@Bk\<up>(za-1) ,  Bk#Oc#rs)"
          using assms using \<open>z1 = Suc nat\<close>
          by (metis diff_Suc_1 le_eq_less_or_eq less_Suc_eq ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add)
        with assms  and \<open>CL = []\<close> and \<open>z1 = Suc nat\<close> and \<open>step0 (s, CL@Bk\<up>z1, Oc#rs) tm = (s2, [] @ Bk \<up> (z1 - 1),  Bk#Oc#rs)\<close>
        show ?thesis
          by auto
      qed
    next
      case (Cons c cs)
      then have "CL = c # cs" .
      from \<open>a = L\<close> and \<open>CL = c # cs\<close> and assms and A1
      have "step0 (s, CL@Bk \<up> z1, Oc#rs) tm =  (s2, cs@Bk \<up>z1, c#Oc#rs)"
        by auto
      moreover from \<open>a = L\<close> and \<open>CL = c # cs\<close> and A1
      have "step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2, cs@Bk \<up>za, c#Oc#rs)" by auto
      ultimately have "Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2, cs@Bk \<up>za, c#Oc#rs)"
        using assms
        by (metis One_nat_def Suc_pred add_diff_inverse_nat neq0_conv not_less_eq not_less_zero replicate_add)
      with assms  and \<open>CL = c # cs\<close> and \<open>Bk\<up>(z1-1) = Bk\<up>za@Bk\<up>(z1-1-za) \<and> step0 (s, CL@Bk\<up>za, Oc#rs) tm =  (s2, cs@Bk \<up>za, c#Oc#rs)\<close>
      show ?thesis
        using \<open>step0 (s, CL @ Bk \<up> z1, Oc#rs) tm = (s2, cs @ Bk \<up> z1, c#Oc#rs)\<close> 
        by (metis fst_conv nat_le_linear not_less ordered_cancel_comm_monoid_diff_class.add_diff_inverse replicate_add snd_conv)
    qed
  qed
qed

corollary step_left_tape_ShrinkBkCtx:
  assumes "step0 (s,CL@Bk\<up> z1 , r) tm = (s',l',r')"
    and "za < z1"
  shows "\<exists>zb CL'. l' = CL'@Bk\<up>za@Bk\<up>zb \<and>
                 (step0 (s,CL@Bk\<up>za, r) tm = (s',CL'@Bk\<up>za,r') \<or>
                 step0 (s,CL@Bk\<up>za, r) tm = (s',CL'@Bk\<up>(za-1),r'))"
proof (cases r)
  case Nil
  then show ?thesis using step_left_tape_ShrinkBkCtx_right_Nil
    using assms by blast
next
  case (Cons rx rs)
  then have "r = rx # rs" .
  show ?thesis
  proof (cases rx)
    case Bk
    with assms and \<open>r = rx # rs\<close> show ?thesis using step_left_tape_ShrinkBkCtx_right_Bk by blast
  next
    case Oc
    with assms and \<open>r = rx # rs\<close> show ?thesis using step_left_tape_ShrinkBkCtx_right_Oc by blast
  qed
qed

(* propagate the step lemmas step_left_tape_ShrinkBkCtx* to steps *)

lemma steps_left_tape_ShrinkBkCtx_arbitrary_CL:
  "\<lbrakk> steps0 (s, CL@Bk\<up>z1 , r) tm stp = (s',l',r'); 0 < z1 \<rbrakk> \<Longrightarrow> 
     \<exists>zb CL'. l' = CL'@Bk\<up>zb  \<and> steps0 (s,CL, r) tm stp = (s',CL',r')"
proof (induct stp arbitrary: s CL z1 r s' l' r' z1)
  case 0
  assume "steps0 (s, CL @ Bk \<up> z1, r) tm 0 = (s', l', r')" and "0 < z1"
  then show ?case
    using less_imp_add_positive replicate_add by fastforce
next
  fix stp s CL z1 r s' l' r'
  assume IV: "\<And>s2 CL2 z12 r2 s2' l2' r2'. \<lbrakk>steps0 (s2, CL2 @ Bk \<up> z12, r2) tm stp = (s2', l2', r2'); 0 < z12\<rbrakk>
          \<Longrightarrow> \<exists>zb2' CL2'. l2' = CL2' @ Bk \<up> zb2' \<and> 
                    steps0 (s2, CL2, r2) tm stp = (s2', CL2', r2')"
    and major: "steps0 (s, CL @ Bk \<up> z1, r) tm (Suc stp) = (s', l', r')"
    and minor: "0< z1"
  show "\<exists>zb CL'. l' = CL' @ Bk \<up> zb \<and> steps0 (s, CL, r) tm (Suc stp) = (s', CL', r')"
  proof -
    have F1: "steps0 (s, CL, r) tm (Suc stp) = step0 (steps0 (s, CL, r) tm stp) tm"
      by (rule step_red)

    have "steps0 (s, CL @ Bk \<up> z1, r) tm (Suc stp) = step0 (steps0 (s, CL @ Bk \<up> z1, r) tm stp) tm"
      by (rule step_red)

    with major
    have F3: "step0 (steps0 (s, CL @ Bk \<up> z1, r) tm stp) tm = (s', l', r')" by auto

    show ?thesis
    proof (cases z1)
      case 0
      then have "z1 = 0" .
      with minor 
      show ?thesis by auto
    next
      case (Suc z1')
      then have "z1 = Suc z1'" .
      show ?thesis
      proof (cases "steps0 (s, CL @ Bk \<up> z1, r) tm stp")
        case (fields sx lx rx)
        then have C: "steps0 (s, CL @ Bk \<up> z1, r) tm stp = (sx, lx, rx)" .
        with  minor and IV
        have F0: "\<exists>zb2' CL2'. lx = CL2' @ Bk \<up> zb2' \<and> 
                                 steps0 (s, CL, r) tm stp = (sx, CL2', rx)"
          by auto

        then obtain zb2' CL2' where
          w_zb2'_CL2'_zc2': "lx = CL2' @ Bk \<up> zb2' \<and> 
                    steps0 (s, CL, r) tm stp = (sx, CL2', rx)"
          by blast

        from F3 and C have "step0 (sx,lx,rx) tm = (s',l',r')" by auto

        with w_zb2'_CL2'_zc2' have F4: "step0 (sx,CL2' @ Bk \<up> zb2',rx) tm = (s',l',r')" by auto

        then have "step0 (sx,CL2' @ Bk \<up> (zb2'),rx) tm = (s',l',r')"
          by (simp add: replicate_add)

        show ?thesis
        proof (cases zb2')
          case 0
          then show ?thesis 

            using F1 \<open>step0 (sx, lx, rx) tm = (s', l', r')\<close> append_Nil2 replicate_0 w_zb2'_CL2'_zc2' by auto
        next
          case (Suc zb3')
          then have "zb2' = Suc zb3'" .

          then show ?thesis
            by (metis F1 F4
                append_Nil2 diff_is_0_eq'
                replicate_0 self_append_conv2 step_left_tape_ShrinkBkCtx w_zb2'_CL2'_zc2'
                zero_le_one zero_less_Suc)
        qed
      qed
    qed
  qed
qed

(* -------------------- Add trailing blanks on the left tape ------------------------------- *)

lemma step_left_tape_EnlargeBkCtx_eq_Bks:
  assumes "step0 (s,Bk\<up> z1,     r) tm = (s',l',r')"
  shows   "step0 (s,Bk\<up>(z1+Suc z2), r) tm = (s',l'@Bk\<up>Suc z2,r') \<or>
           step0 (s,Bk\<up>(z1+Suc z2), r) tm = (s',l'@Bk\<up>z2,r')"
proof (cases s)
  assume "s = 0"
  with assms have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s',l'@Bk\<up>Suc z2,r')"
    using replicate_Suc_1 by fastforce
  then show ?thesis by auto
next
  fix s2
  assume "s = Suc s2"
  then show ?thesis
  proof (cases r)
    assume "r = []"
    then show "step0 (s, Bk \<up> (z1 + Suc z2), r) tm = (s', l' @ Bk \<up> Suc z2, r') \<or>
               step0 (s, Bk \<up> (z1 + Suc z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3, Bk\<up>(z1+Suc z2), [Bk])" by auto
        moreover from  \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk \<up> z1, r) tm = (s3, Bk \<up> z1, [Bk])" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce    
      next
        case WO
        from \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,Bk\<up>(z1+Suc z2), r) tm = (s3, Bk\<up>(z1+Suc z2), [Oc])" by auto
        moreover from  \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk \<up> z1, r) tm = (s3, Bk \<up> z1, [Oc])" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce
      next
        case L
        from \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3, Bk \<up> (z1 + z2), [Bk])" by auto
        moreover from  \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3,  Bk \<up> (z1-1), [Bk])" by auto
        ultimately show ?thesis   
          by (metis (no_types, lifting) Pair_inject add_Suc_right add_eq_if
              assms diff_is_0_eq' replicate_add zero_le_one)
      next
        case R
        from \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3, Bk# Bk\<up>(z1+Suc z2), [])" by auto
        moreover from  \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk \<up> z1, r) tm = (s3, Bk# Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3,  Bk\<up>(z1+Suc z2), [])" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3, Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce
      qed
    qed
  next
    fix ra rrs
    assume "r = ra # rrs"
    then show "step0 (s, Bk \<up> (z1 + Suc z2), r) tm = (s', l' @ Bk \<up> Suc z2, r') \<or>
               step0 (s, Bk \<up> (z1 + Suc z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk\<up>(z1+Suc z2), r) tm = (s3, Bk\<up>(z1+Suc z2), Bk# rrs)" by auto
        moreover from  \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3,  Bk \<up> z1, Bk# rrs)" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce    
      next
        case WO
        from \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3, Bk\<up>(z1+Suc z2), Oc# rrs)" by auto
        moreover from  \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk \<up> z1, r) tm = (s3, Bk \<up> z1, Oc# rrs)" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce    
      next
        case L
        from \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, Bk\<up>(z1+Suc z2), r) tm = (s3, Bk \<up> (z1 + z2), Bk#ra#rrs)" by auto
        moreover from  \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3,  Bk \<up> (z1-1), Bk#ra#rrs)" by auto
        ultimately show ?thesis   
          by (metis (no_types, lifting) Pair_inject add_Suc_right add_eq_if
              assms diff_is_0_eq' replicate_add zero_le_one)
      next
        case R
        from \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,   Bk\<up>(z1+Suc z2), r) tm = (s3, ra#   Bk\<up>(z1+Suc z2), rrs)" by auto
        moreover from  \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3, ra# Bk \<up> z1,rrs)" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce    
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk\<up>(z1+Suc z2), r) tm = (s3, Bk\<up>(z1+Suc z2), ra # rrs)" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s,  Bk \<up> z1, r) tm = (s3,  Bk \<up> z1, ra # rrs)" by auto
        ultimately show ?thesis
          using assms replicate_Suc_1 by fastforce    
      qed
    qed
  qed
qed

lemma step_left_tape_EnlargeBkCtx_eq_Bk_C_Bks:
  assumes "step0 (s,(Bk#C)@Bk\<up> z1,     r) tm = (s',l',r')"
  shows "  step0 (s,(Bk#C)@Bk\<up>(z1+z2), r) tm = (s',l'@Bk\<up>z2,r')"
proof (cases s)
  assume "s = 0"
  with assms show "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    by (auto simp add: replicate_add)
next
  fix s2
  assume "s = Suc s2"
  then show "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
  proof (cases r)
    assume "r = []"
    then show ?thesis
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), [Bk])" by auto
        moreover from  \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, [Bk])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case WO
        from \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), [Oc])" by auto
        moreover from  \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, [Oc])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case L
        from \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (C) @ Bk \<up> (z1 + z2), [Bk])" by auto
        moreover from  \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (C) @ Bk \<up> z1, [Bk])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case R
        from \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk# Bk # C) @ Bk \<up> (z1 + z2), [])" by auto
        moreover from  \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk#Bk # C) @ Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), [])" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      qed
    qed
  next
    fix ra rrs
    assume "r = ra # rrs"
    then show "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), Bk# rrs)" by auto
        moreover from  \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, Bk# rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case WO
        from \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), Oc# rrs)" by auto
        moreover from  \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, Oc# rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case L
        from \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (C) @ Bk \<up> (z1 + z2), Bk#ra#rrs)" by auto
        moreover from  \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (C) @ Bk \<up> z1, Bk#ra#rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case R
        from \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (ra# Bk # C) @ Bk \<up> (z1 + z2), rrs)" by auto
        moreover from  \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (ra#Bk # C) @ Bk \<up> z1,rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk # C) @ Bk \<up> (z1 + z2), ra # rrs)" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Bk # C) @ Bk \<up> z1, r) tm = (s3, (Bk # C) @ Bk \<up> z1, ra # rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      qed
    qed
  qed
qed

lemma step_left_tape_EnlargeBkCtx_eq_Oc_C_Bks:
  assumes "step0 (s,(Oc#C)@Bk\<up> z1,     r) tm = (s',l',r')"
  shows "  step0 (s,(Oc#C)@Bk\<up>(z1+z2), r) tm = (s',l'@Bk\<up>z2,r')"
proof (cases s)
  assume "s = 0"
  with assms show "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    by (auto simp add: replicate_add)
next
  fix s2
  assume "s = Suc s2"
  then show "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
  proof (cases r)
    assume "r = []"
    then show ?thesis
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), [Bk])" by auto
        moreover from  \<open>a = WB\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, [Bk])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case WO
        from \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), [Oc])" by auto
        moreover from  \<open>a = WO\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, [Oc])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case L
        from \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (C) @ Bk \<up> (z1 + z2), [Oc])" by auto
        moreover from  \<open>a = L\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (C) @ Bk \<up> z1, [Oc])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case R
        from \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Bk# Oc # C) @ Bk \<up> (z1 + z2), [])" by auto
        moreover from  \<open>a = R\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Bk#Oc # C) @ Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), [])" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = []\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, [])" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      qed
    qed
  next
    fix ra rrs
    assume "r = ra # rrs"
    then show "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s', l' @ Bk \<up> z2, r')"
    proof (cases "fetch tm (s - 0) (read r)")
      case (Pair a s3)
      then have "fetch tm (s - 0) (read r) = (a, s3)" .
      then show ?thesis
      proof (cases a)
        case WB
        from \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), Bk# rrs)" by auto
        moreover from  \<open>a = WB\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, Bk# rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case WO
        from \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), Oc# rrs)" by auto
        moreover from  \<open>a = WO\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, Oc# rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case L
        from \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (C) @ Bk \<up> (z1 + z2), Oc#ra#rrs)" by auto
        moreover from  \<open>a = L\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (C) @ Bk \<up> z1, Oc#ra#rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case R
        from \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (ra# Oc # C) @ Bk \<up> (z1 + z2), rrs)" by auto
        moreover from  \<open>a = R\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (ra#Oc # C) @ Bk \<up> z1,rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      next
        case Nop
        from \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> (z1 + z2), r) tm = (s3, (Oc # C) @ Bk \<up> (z1 + z2), ra # rrs)" by auto
        moreover from  \<open>a = Nop\<close> \<open>r = ra # rrs\<close> \<open>fetch tm (s - 0) (read r) = (a, s3)\<close>
        have "step0 (s, (Oc # C) @ Bk \<up> z1, r) tm = (s3, (Oc # C) @ Bk \<up> z1, ra # rrs)" by auto
        ultimately show ?thesis
          using assms 
          by (auto simp add: replicate_add)
      qed
    qed
  qed
qed

lemma step_left_tape_EnlargeBkCtx_eq_C_Bks_Suc:
  assumes "step0 (s,C@Bk\<up> z1,     r) tm = (s',l',r')"
  shows   "step0 (s,C@Bk\<up>(z1+ Suc z2), r) tm = (s',l'@Bk\<up>Suc z2,r') \<or>
           step0 (s,C@Bk\<up>(z1+ Suc z2), r) tm = (s',l'@Bk\<up>z2,r')"
proof (cases C)
  case Nil
  then have "C = []" .
  with assms show ?thesis by (metis append.left_neutral step_left_tape_EnlargeBkCtx_eq_Bks)
next
  case (Cons x C')
  then have "C = x # C'" .
  then show ?thesis
  proof (cases x)
    case Bk
    then have "x = Bk" .
    then show ?thesis
      using assms local.Cons step_left_tape_EnlargeBkCtx_eq_Bk_C_Bks by blast
  next
    case Oc
    then have "x = Oc" .
    then show ?thesis
      using assms local.Cons step_left_tape_EnlargeBkCtx_eq_Oc_C_Bks by blast
  qed
qed

lemma step_left_tape_EnlargeBkCtx_eq_C_Bks:
  assumes "step0 (s,C@Bk\<up> z1,     r) tm = (s',l',r')"
  shows   "step0 (s,C@Bk\<up>(z1+ z2), r) tm = (s',l'@Bk\<up>z2,r') \<or>
           step0 (s,C@Bk\<up>(z1+ z2), r) tm = (s',l'@Bk\<up>(z2-1),r')"
  by (smt step_left_tape_EnlargeBkCtx_eq_C_Bks_Suc One_nat_def Suc_pred add.right_neutral
          append.right_neutral assms neq0_conv replicate_empty)

(* propagate the step lemmas step_left_tape_EnlargeBkCtx* to steps *)

lemma steps_left_tape_EnlargeBkCtx_arbitrary_CL:
  "steps0 (s, CL @ Bk\<up>z1, r) tm stp = (s', l',r')
   \<Longrightarrow>
   \<exists>z3. z3 \<le> z1 + z2 \<and>
        steps0 (s, CL @ Bk\<up>(z1 + z2), r) tm stp = (s',l' @ Bk\<up>z3 ,r')"
proof (induct stp arbitrary: s CL z1 r z2 s' l' r')
  fix s CL z1 r z2 s' l' r'
  assume  "steps0 (s, CL @ Bk \<up> z1, r) tm 0 = (s', l', r')"
  show "\<exists>z3\<le>z1 + z2. steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm 0 = (s', l' @ Bk \<up> z3, r')"  
    by (metis \<open>steps0 (s, CL @ Bk \<up> z1, r) tm 0 = (s', l', r')\<close>
        append.assoc fst_conv le_add2 replicate_add snd_conv steps.simps(1))
next
  fix stp s CL z1 r z2 s' l' r'
  assume IV: "\<And>s CL z1 r z2 s' l' r'. steps0 (s, CL @ Bk \<up> z1, r) tm stp = (s', l', r')
              \<Longrightarrow> \<exists>z3\<le>z1 + z2. steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm stp = (s', l' @ Bk \<up> z3, r')"
    and minor: "steps0 (s, CL @ Bk \<up> z1, r) tm (Suc stp) = (s', l', r')"
  show "\<exists>z3\<le>z1 + z2. steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = (s', l' @ Bk \<up> z3, r')"

  proof -
    have F1: "steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = step0 (steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm stp) tm"
      by (rule step_red)

    have "steps0 (s, CL @ Bk \<up> z1, r) tm (Suc stp) = step0 (steps0 (s, CL @ Bk \<up> z1, r) tm stp) tm"
      by (rule step_red)

    with minor
    have F3: "step0 (steps0 (s, CL @ Bk \<up> z1, r) tm stp) tm = (s', l', r')" by auto

    show "\<exists>z3. z3 \<le> z1 + z2 \<and> steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = (s', l' @ Bk \<up> z3, r')"
    proof (cases "steps0 (s, CL @ Bk \<up> z1, r) tm stp")
      case (fields sx lx rx)
      then have CL: "steps0 (s, CL @ Bk \<up> z1, r) tm stp = (sx, lx, rx)" .
      with IV
      have "\<exists>z3'\<le>z1 + z2. steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm stp = (sx, lx @ Bk \<up> z3', rx)" by auto
      then obtain z3' where
        w_z3': "z3'\<le>z1 + z2 \<and>
              steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm stp = (sx, lx @ Bk \<up> z3', rx)" by blast

      moreover
      have "step0 (sx,lx@Bk\<up>z3', rx) tm = (s',l' @ Bk\<up>(z3')  ,r') \<or>
            step0 (sx,lx@Bk\<up>z3', rx) tm = (s',l' @ Bk\<up>(z3'-1),r')"
      proof -
        from F3 and CL have "step0 (sx, lx@Bk\<up>0, rx) tm = (s', l', r')" by auto

        then have "step0 (sx,lx@Bk\<up>(0+z3'), rx) tm = (s',l' @ Bk\<up>(z3')   ,r') \<or>
                   step0 (sx,lx@Bk\<up>(0+z3'), rx) tm = (s',l' @ Bk\<up>(z3'-1) ,r')"
          by (rule step_left_tape_EnlargeBkCtx_eq_C_Bks)  (* <-- the step argument *)

        then show "step0 (sx,lx@Bk\<up>z3', rx) tm = (s',l' @ Bk\<up>(z3')  ,r') \<or>
                   step0 (sx,lx@Bk\<up>z3', rx) tm = (s',l' @ Bk\<up>(z3'-1),r')"
          by auto
      qed

      moreover from w_z3' and F1
      have "steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = step0 (sx, lx @ Bk \<up> z3', rx) tm"
        by auto

      ultimately
      have "steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = (s', l' @ Bk \<up> z3', r') \<or>
            steps0 (s, CL @ Bk \<up> (z1 + z2), r) tm (Suc stp) = (s', l' @ Bk \<up> (z3'-1), r')"
        by auto
      with w_z3' show ?thesis
        by (auto simp add:  split: if_splits)
    qed
  qed
qed

(* ---------------------------------------------------------------------------------- *)
(* The grand lemmas about trailing blanks on the left tape                            *)
(* ---------------------------------------------------------------------------------- *)

corollary steps_left_tape_EnlargeBkCtx:
  "     steps0 (s, Bk \<up> k, r) tm stp = (s', Bk \<up> l, r')
   \<Longrightarrow>
   \<exists>z3. z3 \<le> k + z2 \<and>
        steps0 (s, Bk \<up> (k + z2), r) tm stp = (s',Bk \<up> (l + z3), r')"

proof -
  assume "steps0 (s, Bk \<up> k, r) tm stp = (s', Bk \<up> l, r')"
  then have "\<exists>z3. z3 \<le> k + z2 \<and>
        steps0 (s, Bk \<up> (k + z2), r) tm stp = (s',Bk \<up> l @ Bk \<up> z3, r')"
  by (metis append_Nil steps_left_tape_EnlargeBkCtx_arbitrary_CL)
  then show ?thesis by (simp add: replicate_add)
qed

corollary steps_left_tape_ShrinkBkCtx_to_NIL:
  "     steps0 (s, Bk \<up> k, r) tm stp = (s', Bk \<up> l, r')
   \<Longrightarrow> 
   \<exists>z3. z3 \<le> l \<and>
        steps0 (s, [], r) tm stp = (s', Bk \<up> z3, r')"
proof -
  assume A: "steps0 (s, Bk \<up> k, r) tm stp = (s', Bk \<up> l, r')"
  then have F0: "\<exists>zb CL'. Bk \<up> l = CL'@Bk\<up>zb  \<and> steps0 (s,[], r) tm stp = (s',CL',r')"
  proof (cases k)
    case 0
    then show ?thesis
      using A append_Nil2 replicate_0 by auto
  next
    case (Suc nat)
    then have "0 < k" by auto
    with A show ?thesis
      using steps_left_tape_ShrinkBkCtx_arbitrary_CL by auto
  qed
  then obtain zb CL' where
    w: "Bk \<up> l = CL'@Bk\<up>zb  \<and> steps0 (s,[], r) tm stp = (s',CL',r')" by blast
  then show ?thesis 
    by (metis  append_same_eq le_add1 length_append length_replicate replicate_add)
qed

lemma steps_left_tape_Nil_imp_All:
      "steps0 (s, ([]  , r)) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)
   \<Longrightarrow>
   \<forall>z. \<exists>stp k l. (steps0 (s, (Bk\<up>z, r)) p stp) = (s', Bk \<up> k, CR @ Bk \<up> l)"
proof
  fix z
  assume A: "steps0 (s, [], r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)"

  then have "steps0 (s, Bk \<up> 0 , r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)" by auto
  then have "\<exists>z3. z3 \<le> 0 + z \<and>
        steps0 (s, Bk \<up> (0 + z), r) p stp = (s',Bk \<up> (k + z3), CR @ Bk \<up> l)"
    by (rule steps_left_tape_EnlargeBkCtx)
  then have "\<exists>z3. steps0 (s, Bk \<up> z,  r) p stp = (s',Bk \<up> (k + z3), CR @ Bk \<up> l)"
    by auto
  then obtain z3 where
    "steps0 (s, Bk \<up> z,  r) p stp = (s',Bk \<up> (k + z3), CR @ Bk \<up> l)" by blast
  then show "\<exists>stp k l. steps0 (s, Bk \<up> z,r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)"
    by auto
qed

lemma ex_steps_left_tape_Nil_imp_All:
      "\<exists>stp k l. (steps0 (s, ([]  , r)) p stp) = (s', Bk \<up> k, CR @ Bk \<up> l)
   \<Longrightarrow>
   \<forall>z. \<exists>stp k l. (steps0 (s, (Bk\<up>z, r)) p stp) = (s', Bk \<up> k, CR @ Bk \<up> l)"
proof
  fix z
  assume A: "\<exists>stp k l. steps0 (s, [], r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)"
  then obtain stp k l where
    "steps0 (s, [], r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)" by blast
  then show "\<exists>stp k l. steps0 (s, Bk \<up> z, r) p stp = (s', Bk \<up> k, CR @ Bk \<up> l)"
    using steps_left_tape_Nil_imp_All
    by auto
qed

subsection \<open>Trailing blanks on the right tape do not matter\<close>

(* --------------------------------------------------------------- *)
(* Blanks on the right tape, too                                   *)
(* --------------------------------------------------------------- *)

lemma step_left_tape_Nil_imp_all_trailing_right_Nil:
  assumes "step0 (s, CL1, [] ) tm = (s', CR1, CR2 )"
  shows   "step0 (s, CL1, [] @ Bk \<up> y) tm = (s', CR1, CR2 @ Bk \<up> y) \<or>
           step0 (s, CL1, [] @ Bk \<up> y) tm = (s', CR1, CR2 @ Bk \<up> (y-1))"
proof (cases "fetch tm (s - 0) (read ([] ))")
  case (Pair a s2)
  then have A1: "fetch tm (s - 0) (read ([])) = (a, s2)" .
  show ?thesis
  proof (cases a)
    assume "a = WB"
    from \<open>a = WB\<close> and assms A1          have "step0 (s, CL1, []     ) tm = (s2, CL1, [Bk])" by auto
    moreover from \<open>a = WB\<close> and assms A1 have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, CL1, [Bk]@Bk \<up> (y-1))" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = WO"
    from \<open>a = WO\<close> and assms A1          have "step0 (s, CL1, []     ) tm = (s2, CL1, [Oc])" by auto
    moreover from \<open>a = WO\<close> and assms A1 have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, CL1, [Oc] @ Bk \<up> (y-1))" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = L"
    show ?thesis
    proof (cases CL1)
      case Nil
      then have "CL1 = []" .
      from \<open>CL1 = []\<close> and \<open>a = L\<close> and assms A1          have "step0 (s, CL1, []     ) tm = (s2, CL1, [Bk])"
        by auto
      moreover from \<open>CL1 = []\<close> and \<open>a = L\<close> and assms A1
      have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, CL1, Bk # Bk \<up> y)"
        by (auto simp add:  split: if_splits)
      ultimately show ?thesis using assms by auto
    next
      case (Cons c cs)
      then have "CL1 = c # cs" .
      from \<open>CL1 = c # cs \<close> and \<open>a = L\<close> and assms A1         have "step0 (s, CL1, []     ) tm = (s2, cs, [c])"
        by auto
      moreover from \<open>CL1 = c # cs\<close> and \<open>a = L\<close> and assms A1
      have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, cs, c # Bk \<up> y)"
        by (auto simp add:  split: if_splits)
      ultimately show ?thesis using assms by auto
    qed
  next
    assume "a = Nop"
    from \<open>a = Nop\<close> and assms and A1          have "step0 (s, CL1, []     ) tm = (s2, CL1, [] )"
      by auto
    moreover from \<open>a = Nop\<close> and assms and A1 have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, CL1, [] @ Bk \<up> y)" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = R"
    from \<open>a = R\<close> and assms A1 have "step0 (s, CL1, []     ) tm = (s2, Bk#CL1, [] )"
      by auto
    moreover from \<open>a = R\<close> and assms A1 have "step0 (s, CL1, [] @ Bk \<up> y) tm = (s2, Bk#CL1, []@ Bk \<up> (y-1) )"
      by auto
    ultimately show ?thesis using assms by auto
  qed
qed

lemma step_left_tape_Nil_imp_all_trailing_right_Cons:
  assumes "step0 (s, CL1, rx#rs     ) tm = (s', CR1, CR2 )"
  shows   "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s', CR1, CR2 @ Bk \<up> y)"
proof (cases "fetch tm (s - 0) (read (rx#rs ))")
  case (Pair a s2)
  then have A1: "fetch tm (s - 0) (read (rx#rs )) = (a, s2)" .
  show ?thesis
  proof (cases a)
    assume "a = WB"
    from \<open>a = WB\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, CL1, Bk#rs )" by auto
    moreover from \<open>a = WB\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, CL1, Bk#rs @ Bk \<up> y)" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = WO"
    from \<open>a = WO\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, CL1, Oc#rs )" by auto
    moreover from \<open>a = WO\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, CL1, Oc#rs @ Bk \<up> y)" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = L"
    show ?thesis
    proof (cases CL1)
      case Nil
      then have "CL1 = []" .
      show ?thesis
      proof -
        from \<open>a = L\<close> and \<open>CL1 = []\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, CL1, Bk#rx#rs )" by auto
        moreover from \<open>a = L\<close> and \<open>CL1 = []\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, CL1, Bk#rx#rs @ Bk \<up> y)" by auto
        ultimately show ?thesis using assms by auto
      qed
    next
      case (Cons c cs)
      then have "CL1 = c # cs" .
      show ?thesis
      proof -
        from \<open>a = L\<close> and \<open>CL1 = c # cs\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, cs, c#rx#rs )" by auto
        moreover from \<open>a = L\<close> and \<open>CL1 = c # cs\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, cs, c#rx#rs @ Bk \<up> y)" by auto
        ultimately show ?thesis using assms by auto
      qed
    qed
  next
    assume "a = R"
    from \<open>a = R\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, rx#CL1, rs )" by auto
    moreover from \<open>a = R\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, rx#CL1, rs @ Bk \<up> y)" by auto
    ultimately show ?thesis using assms by auto
  next
    assume "a = Nop"
    from \<open>a = Nop\<close> and assms A1          have "step0 (s, CL1, rx#rs     ) tm = (s2, CL1, rx#rs )"
      by (auto simp add:  split: if_splits)
    moreover from \<open>a = Nop\<close> and assms A1 have "step0 (s, CL1, rx#rs @ Bk \<up> y) tm = (s2, CL1, rx#rs @ Bk \<up> y)" by auto
    ultimately show ?thesis using assms by auto
  qed
qed

lemma step_left_tape_Nil_imp_all_trailing_right: 
  assumes "step0 (s, CL1, r     ) tm = (s', CR1, CR2 )"
  shows   "step0 (s, CL1, r @ Bk \<up> y) tm = (s', CR1, CR2 @ Bk \<up> y) \<or>
           step0 (s, CL1, r @ Bk \<up> y) tm = (s', CR1, CR2 @ Bk \<up> (y-1))"
proof (cases r)
  case Nil
  then show ?thesis using step_left_tape_Nil_imp_all_trailing_right_Nil assms by auto
next
  case (Cons a list)
  then show ?thesis using step_left_tape_Nil_imp_all_trailing_right_Cons assms by auto
qed

(* propagate to steps *)

lemma steps_left_tape_Nil_imp_all_trailing_right:
          "steps0 (s, CL1, r ) tm stp = (s', CR1, CR2)
   \<Longrightarrow>
      \<exists>x1 x2. y = x1 + x2 \<and>
              steps0 (s, CL1, r @ Bk \<up> y ) tm stp = (s', CR1, CR2 @ Bk \<up> x2)"
proof (induct stp arbitrary: s CL1 r y s' CR1 CR2)
  case 0
  then show ?case
    by (simp add: "0.prems" steps_left_tape_Nil_imp_All)
next
  fix stp s CL1 r y s' CR1 CR2
  assume IV: "\<And>s CL1 r y s' CR1 CR2. steps0 (s, CL1, r) tm stp = (s', CR1, CR2) \<Longrightarrow> \<exists>x1 x2. y = x1 + x2 \<and> steps0 (s, CL1, r @ Bk \<up> y) tm stp = (s', CR1, CR2 @ Bk \<up> x2)"
  and major: "steps0 (s, CL1, r) tm (Suc stp) = (s', CR1, CR2)"

  show "\<exists>x1 x2. y = x1 + x2 \<and> steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = (s', CR1, CR2 @ Bk \<up> x2)"
   proof -
    have F1: "steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = step0 (steps0 (s, CL1, r @ Bk \<up> y) tm stp) tm"
      by (rule step_red)

    have "steps0 (s, CL1, r) tm (Suc stp) = step0 (steps0 (s, CL1, r) tm stp) tm"
      by (rule step_red)

    with major
    have F3: "step0 (steps0 (s, CL1, r) tm stp) tm = (s', CR1, CR2)" by auto

    show "\<exists>x1 x2. y = x1 + x2 \<and> steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = (s', CR1, CR2 @ Bk \<up> x2)"
    proof (cases y)
      case 0
      then have "y = 0" .
      with major show ?thesis by auto
    next
      case (Suc y')
      then have "y = Suc y'" .
      then show ?thesis 
      proof (cases "steps0 (s, CL1, r) tm stp")
        case (fields sx lx rx)
        then have C: "steps0 (s, CL1, r) tm stp = (sx, lx, rx)" .
        with major and IV have F0:               "\<exists>x1' x2'. y = x1' + x2' \<and> steps0 (s, CL1, r @ Bk \<up> y) tm stp = (sx, lx, rx @ Bk \<up> x2')"
          by auto
        then obtain x1' x2' where w_x1'_x2': " y = x1' + x2' \<and> steps0 (s, CL1, r @ Bk \<up> y) tm stp = (sx, lx, rx @ Bk \<up> x2')" by blast

        moreover have "step0 (sx, lx, rx @ Bk \<up> x2') tm =  (s', CR1, CR2 @ Bk \<up> x2') \<or>
                       step0 (sx, lx, rx @ Bk \<up> x2') tm = (s', CR1, CR2 @ Bk \<up> (x2'-1))"

        proof -
          from F3 and C have F5: "step0 (sx, lx, rx) tm = (s', CR1, CR2)" by auto

          then have "step0 (sx, lx, rx @ Bk \<up> x2') tm = (s', CR1, CR2 @ Bk \<up> x2') \<or>
                     step0 (sx, lx, rx @ Bk \<up> x2') tm = (s', CR1, CR2 @ Bk \<up> (x2'-1))"
            by (rule step_left_tape_Nil_imp_all_trailing_right)
          then show "step0 (sx, lx, rx @ Bk \<up> x2') tm =  (s', CR1, CR2 @ Bk \<up> x2') \<or>
                       step0 (sx, lx, rx @ Bk \<up> x2') tm = (s', CR1, CR2 @ Bk \<up> (x2'-1))"
            by auto
        qed

        moreover from w_x1'_x2' and F1
        have "steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = step0 (sx, lx, rx @ Bk \<up> x2') tm" by auto 

        ultimately have F5: "y = x1' + x2' \<and>
                         (steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = (s', CR1, CR2 @ Bk \<up> x2') \<or> 
                          steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = (s', CR1, CR2 @ Bk \<up> (x2' - 1)))"
          by auto
        with w_x1'_x2' show ?thesis
        proof (cases x2')
          case 0
          with F5 have  "y = x1' + 0 \<and>
                         steps0 (s, CL1, r @ Bk \<up> y) tm (Suc stp) = (s', CR1, CR2 @ Bk \<up> 0)"
            by (auto simp add:  split: if_splits)
          with w_x1'_x2' show ?thesis
            by (auto simp add:  split: if_splits)
        next
          case (Suc x2'')        
          with w_x1'_x2' show ?thesis
            using F5 add_Suc_right add_Suc_shift diff_Suc_1 by fastforce
        qed
      qed
    qed
  qed
qed

(* ---------------------------------------------------------------------------------- *)
(* The grand lemmas about trailing blanks on the right tape                           *)
(* ---------------------------------------------------------------------------------- *)

lemma ex_steps_left_tape_Nil_imp_All_left_and_right:
 "(\<exists>kr lr.         steps0 (1, ([]     , r          )) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr))
  \<Longrightarrow>
   \<forall>kl ll. \<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)"
proof -
  assume "(\<exists>kr lr.         steps0 (1, ([]     , r          )) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
  then obtain kr lr where
    w_kr_lr: "steps0 (1, ([]     , r          )) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)" by blast

  then have "steps0 (1, (Bk \<up> 0     , r          )) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)"
    by auto

  then have "\<And>kl. \<exists>z3. z3 \<le> 0 + kl \<and> steps0 (1, Bk \<up> (0 + kl), r) p stp = (0,Bk \<up> (kr + z3), r' @ Bk \<up> lr)"
    using steps_left_tape_EnlargeBkCtx
    using plus_nat.add_0 w_kr_lr by blast

  then have "\<And>kl. \<exists>z3. z3 \<le> kl \<and> steps0 (1, Bk \<up> kl, r) p stp = (0,Bk \<up> (kr + z3), r' @ Bk \<up> lr)"
    by auto

  then have F0: "\<And>kl.      \<exists>z4.    steps0 (1, Bk \<up> kl, r           ) p stp =  (0,Bk \<up> z4 , r' @ Bk \<up> lr)"
    by auto

  show ?thesis
  proof 
    fix kl
    show " \<forall>ll. \<exists>kr lr. steps0 (1, Bk \<up> kl, r @ Bk \<up> ll) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)"
    proof
      fix ll
      show "\<exists>kr lr. steps0 (1, Bk \<up> kl, r @ Bk \<up> ll) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)"

      proof -
        from F0 have "\<exists>z4.    steps0 (1, Bk \<up> kl, r           ) p stp =  (0,Bk \<up> z4 , r' @ Bk \<up> lr)"
          by auto
        then obtain z4 where w_z4: "steps0 (1, Bk \<up> kl, r           ) p stp =  (0,Bk \<up> z4 , r' @ Bk \<up> lr)" by blast

        then have "\<exists>x1 x2. ll = x1 + x2 \<and>
                steps0 (1, Bk \<up> kl , r @ Bk \<up> ll ) p stp = (0, Bk \<up> z4    , r' @ Bk \<up> lr @ Bk \<up> x2)"
          using steps_left_tape_Nil_imp_all_trailing_right

          using append_assoc by fastforce

        then show "\<exists>kr lr. steps0 (1, Bk \<up> kl, r @ Bk \<up> ll) p stp = (0, Bk \<up> kr, r' @ Bk \<up> lr)"
          by (metis replicate_add)
      qed
    qed
  qed
qed

end
