(* Title: thys/Turing_HaltingConditions.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Further contributions by Franz Regensburger (FABR) 02/2022
 *)

section \<open>Halting Conditions and Standard Halting Configuration\<close>

theory Turing_HaltingConditions
  imports Turing_Hoare
begin

subsection \<open>Looping of Turing Machines\<close>

definition TMC_loops :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "TMC_loops p ns \<equiv> (\<forall>stp.\<not> is_final (steps0 (1, [], <ns::nat list>) p stp))"

subsection \<open>Reaching the Final State\<close>

definition reaches_final :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "reaches_final p ns \<equiv> \<lbrace>(\<lambda>tap. tap = ([], <ns>))\<rbrace> p \<lbrace>(\<lambda>tap. True)\<rbrace>"

text \<open>The definition @{term reaches_final} and all lemmas about it are only needed for the special halting problem K0. \<close>

lemma True_holds_for_all: "(\<lambda>tap. True) holds_for c"
  by (cases c)(auto)

lemma reaches_final_iff: "reaches_final p ns \<longleftrightarrow> (\<exists>n. is_final (steps0 (1, ([], <ns>)) p n))"
  by (auto simp add: reaches_final_def Hoare_halt_def True_holds_for_all)



text \<open>Some lemmas about reaching the Final State.\<close>

lemma Hoare_halt_from_init_imp_reaches_final:
  assumes "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> p \<lbrace>Q\<rbrace>"
  shows "reaches_final p ns"
proof -
  from assms have "\<forall>tap. tap = ([], <ns>) \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n))"
    using Hoare_halt_def by auto
  then show ?thesis
    using reaches_final_iff by auto
qed

lemma Hoare_unhalt_impl_not_reaches_final:
  assumes "\<lbrace>(\<lambda>tap. tap = ([], <ns>))\<rbrace> p \<up>"
  shows "\<not>(reaches_final p ns)"
proof 
  assume "reaches_final p ns"
  then have "(\<exists>n. is_final (steps0 (1, ([], <ns>)) p n))" by (auto simp add: reaches_final_iff)
  then obtain n where w_n: "is_final (steps0 (1, ([], <ns>)) p n)" by blast
  from assms have "\<forall>tap. (\<lambda>tap. tap = ([], <ns>)) tap \<longrightarrow> (\<forall> n . \<not> (is_final (steps0 (1, tap) p n)))"
    by (auto simp add: Hoare_unhalt_def)
  then have "\<not> (is_final (steps0 (1, ([], <ns>)) p n))" by blast
  with w_n show False by auto
qed

subsection \<open>What is a Standard Tape\<close>

text \<open>A tape is called {\em standard}, if the left tape is empty or contains only blanks and
the right tape contains a single nonempty block of strokes (occupied cells) followed by zero or more blanks..

Thus, by definition of left and right tape, the head of the machine is always
scanning the first cell of this single block of strokes.

We extend the notion of a standard tape to lists of numerals as well.
\<close>

definition std_tap :: "tape \<Rightarrow> bool"
  where
    "std_tap tap  \<equiv> (\<exists>k n l. tap = (Bk \<up> k,  <n::nat> @ Bk \<up> l))"

definition std_tap_list :: "tape \<Rightarrow> bool"
  where
    "std_tap_list tap  \<equiv> (\<exists>k ml l. tap = (Bk \<up> k,  <ml::nat list> @ Bk \<up> l))"


lemma "std_tap tap \<Longrightarrow> std_tap_list tap"
  unfolding std_tap_def std_tap_list_def
  by (metis tape_of_list_def tape_of_nat_list.simps(2))

text \<open>A configuration @{term "(st, l, r)"} of a Turing machine is called a {\em standard configuration},
 if the state  @{term "st"} is the final state $0$ and the @{term "(l, r)"} is a standard tape. 
\<close>

(* A duplicate from UTM just for comparison of concepts *)

definition TSTD':: "config \<Rightarrow> bool"
  where
    "TSTD' c = ((let (st, l, r) = c in 
             st = 0 \<and> (\<exists> m. l = Bk\<up>(m)) \<and> (\<exists> rs n. r = Oc\<up>(Suc rs) @ Bk\<up>(n))))"

(* Relate definition of TSTD' to std_tap *)

lemma "TSTD' (st, l, r) = ((st = 0) \<and> std_tap (l,r))"
  unfolding TSTD'_def std_tap_def
proof -
  have "(let (st, l, r) = (st, l, r) in st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>rs n. r = Oc \<up> Suc rs @ Bk \<up> n))
        = (st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>rs n. r = Oc \<up> Suc rs @ Bk \<up> n))"
    by auto
  also have "... = (st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>n la. r = (<n::nat> @ Bk \<up> la)))"
    by (auto simp add: tape_of_nat_def)
  finally have "(let (st, l, r) = (st, l, r) in st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>rs n. r = Oc \<up> Suc rs @ Bk \<up> n))
                = (st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>n la. r = (<n::nat> @ Bk \<up> la)))"
    by (auto simp add: tape_of_nat_def)
  moreover have "((\<exists>m. l = Bk \<up> m) \<and> (\<exists>n la. r = <n::nat> @ Bk \<up> la)) = (\<exists>k n la. (l, r) = (Bk \<up> k, <n::nat> @ Bk \<up> la))"
    by auto
  ultimately show "(let (st, l, r) = (st, l, r)
                    in  st = 0 \<and> (\<exists>m. l = Bk \<up> m) \<and> (\<exists>rs n. r = Oc \<up> Suc rs @ Bk \<up> n))
                    = 
                    (st = 0 \<and> (\<exists>k n la. (l, r) = (Bk \<up> k, <n::nat> @ Bk \<up> la)))"
    by blast
qed

subsection \<open>What does Hoare\_halt mean in general?\<close>

text \<open>We say {\em in general} because the result computed on the right tape is not necessarily a numeral but some arbitrary component @{term "r'"} . \<close>

lemma Hoare_halt2_iff:
"\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, r @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>
 \<longleftrightarrow>
 (\<forall>kl ll. \<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr)))"
proof
  assume "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, r @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
  then show "\<forall>kl ll. \<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
    by (smt Hoare_halt_def Pair_inject holds_for.elims(2) is_final.elims(2))
next
  assume "\<forall>kl ll. \<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
  then show "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, r @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
  unfolding Hoare_halt_def  
  using holds_for.simps by fastforce
qed

lemma Hoare_halt_D:
  assumes "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, r @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
  shows "\<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
proof -
  from assms show "\<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
    by (simp add: Hoare_halt2_iff is_final_eq)
qed

lemma Hoare_halt_I2:
  assumes "\<And>kl ll. \<exists>n. is_final (steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> kl, r @ Bk \<up> ll)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
  shows "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, r @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
  unfolding Hoare_halt_def  
  using assms holds_for.simps by fastforce


lemma Hoare_halt_D_Nil:
  assumes "\<lbrace>\<lambda>tap. tap = ([], r)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
  shows "\<exists>n. is_final (steps0 (1, ([], r)) p n) \<and> (\<exists>kr lr. steps0 (1, ([], r)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
proof -
  from assms have "\<lbrace>\<lambda>tap. tap = (Bk \<up> 0, r @ Bk \<up> 0)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
    by simp
  then have "\<exists>n. is_final (steps0 (1, (Bk \<up> 0, r @ Bk \<up> 0)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> 0, r @ Bk \<up> 0)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
    using Hoare_halt_E0 append_self_conv assms is_final_eq old.prod.inject prod.inject replicate_0
    by force
  then show ?thesis by auto
qed

lemma Hoare_halt_I2_Nil:
  assumes "\<exists>n. is_final (steps0 (1, ([], r )) p n) \<and> (\<exists>kr lr. steps0 (1, ([], r )) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
  shows "\<lbrace>\<lambda>tap. tap = ([], r)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
proof -
  from assms have "\<exists>n. is_final (steps0 (1, (Bk \<up> 0, r @ Bk \<up> 0)) p n) \<and> (\<exists>kr lr. steps0 (1, (Bk \<up> 0, r @ Bk \<up> 0)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr))"
    by auto
  then have "\<lbrace>\<lambda>tap. tap = (Bk \<up> 0, r @ Bk \<up> 0)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>"
    using Hoare_halt_iff by auto
  then show ?thesis by auto
qed

lemma Hoare_halt2_Nil_iff:
  "\<lbrace>\<lambda>tap. tap = ([], r)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, r' @ Bk \<up> lr)\<rbrace>
   \<longleftrightarrow>
   (\<exists>n. is_final (steps0 (1, ([], r)) p n) \<and> (\<exists>kr lr. steps0 (1, ([], r)) p n = (0, Bk \<up> kr, r' @ Bk \<up> lr)))"
  using Hoare_halt_D_Nil Hoare_halt_I2_Nil by blast

corollary Hoare_halt_left_tape_Nil_imp_All_left_and_right:
  assumes "\<lbrace>\<lambda>tap.       tap = ([]    , r         )\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k , r' @ Bk \<up> l)\<rbrace>"
  shows   "\<lbrace>\<lambda>tap. \<exists>x y. tap = (Bk \<up> x, r @ Bk \<up> y)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k , r' @ Bk \<up> l)\<rbrace>"
proof -
  from assms have "\<exists>n. is_final (steps0 (1, ([], r)) p n) \<and> (\<exists>k l. steps0 (1, ([], r)) p n = (0, Bk \<up> k,  r' @ Bk \<up> l))"
    using Hoare_halt_D_Nil by auto
  then have "\<And>x y. \<exists>n. is_final (steps0 (1, (Bk \<up> x, r @ Bk \<up> y)) p n) \<and> (\<exists>k l. steps0 (1, (Bk \<up> x, r @ Bk \<up> y)) p n = (0, Bk \<up> k,  r' @ Bk \<up> l))"
    using ex_steps_left_tape_Nil_imp_All_left_and_right
    using is_final.simps by force
  then show ?thesis using Hoare_halt_I2
    by auto
qed

subsubsection \<open>What does Hoare\_halt with a numeral list result mean?\<close>

text \<open>About computations that result in numeral lists on the final right tape.\<close>

(* Adding trailing blanks to the initial right tape needs tough lemmas (see BlanksDoNotMatter)  *)

lemma TMC_has_num_res_list_without_initial_Bks_imp_TMC_has_num_res_list_after_adding_Bks_to_initial_right_tape:
  " \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>
  \<Longrightarrow>
    \<lbrace>\<lambda>tap. \<exists>ll. tap = ([], <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
proof -
  assume A: "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  then have "\<exists>n. is_final (steps0 (1, ([], <ns::nat list>)) p n) \<and>
                 (\<exists>ms kr lr. steps0 (1, ([], <ns::nat list>)) p n = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr))"
    using Hoare_halt_E0 is_finalI by force
  then obtain stp where
    w_stp: "is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and>
            (\<exists>ms kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr))"
    by blast

  then obtain ms where  "\<exists>kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)" by blast

  then have "\<forall>ll. \<exists>kr lr. steps0 (1, ([], <ns::nat list>@ Bk \<up> ll)) p stp = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)"
    using ex_steps_left_tape_Nil_imp_All_left_and_right steps_left_tape_ShrinkBkCtx_to_NIL by blast

  then have "\<forall>ll. is_final (steps0 (1, ([], <ns::nat list>@ Bk \<up> ll)) p stp) \<and>
                 (\<exists>ms kr lr. steps0 (1, ([], <ns::nat list>@ Bk \<up> ll)) p stp = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr))"   
    by (metis is_finalI)

  then have "\<forall>tap. (\<exists>ll. tap = ([], <ns::nat list> @ Bk \<up> ll))
                    \<longrightarrow> (\<exists>n. is_final (steps0 (1, tap) p n) \<and>
                             (\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)) holds_for steps0 (1, tap) p n)"
    using holds_for.simps by force
  then show ?thesis
    unfolding Hoare_halt_def
    by auto
qed

(* Removing trailing blanks on the initial right tape (is easy) *)

lemma TMC_has_num_res_list_without_initial_Bks_iff_TMC_has_num_res_list_after_adding_Bks_to_initial_right_tape:
  "\<lbrace>\<lambda>tap.      tap = ([], <ns::nat list>)          \<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>
    \<longleftrightarrow>
   \<lbrace>\<lambda>tap. \<exists>ll. tap = ([], <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
proof
  assume "\<lbrace>\<lambda>tap.      tap = ([], <ns::nat list>)          \<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  then show "\<lbrace>\<lambda>tap. \<exists>ll. tap = ([], <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  using  TMC_has_num_res_list_without_initial_Bks_imp_TMC_has_num_res_list_after_adding_Bks_to_initial_right_tape by blast
next
  assume "\<lbrace>\<lambda>tap. \<exists>ll. tap = ([], <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  then show "\<lbrace>\<lambda>tap.      tap = ([], <ns::nat list>)          \<rbrace> p \<lbrace>\<lambda>tap. \<exists>ms kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
    by (simp add: Hoare_halt_def assert_imp_def)
qed


(* In addition we may add or remove blanks on the initial left tape *)

lemma TMC_has_num_res_list_without_initial_Bks_imp_TMC_has_num_res_list_after_adding_Bks_to_initial_left_and_right_tape:
  " \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap.\<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>
  \<Longrightarrow>
    \<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  using Hoare_halt_left_tape_Nil_imp_All_left_and_right by auto

(*
proof -
  assume A: "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap.\<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"

  then have "\<exists>stp. is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and>
                   (\<exists> kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr,  <ms::nat list> @ Bk \<up> lr))"
    using Hoare_halt2_Nil_iff tape_of_list_def tape_of_nat_list.simps(2)  by blast

  then obtain stp where
    w_stp: "is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and>
                   (\<exists> kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr,  <ms::nat list> @ Bk \<up> lr))"
    by blast

  then have "\<forall>kl ll.\<exists>kr lr. steps0 (1, Bk \<up> kl, <ns::nat list> @ Bk \<up> ll) p stp = (0, Bk \<up> kr,  <ms::nat list> @ Bk \<up> lr)"
    using ex_steps_left_tape_Nil_imp_All_left_and_right steps_left_tape_ShrinkBkCtx_to_NIL by blast

  then have "\<forall>kl ll. is_final (steps0 (1, Bk \<up> kl, <ns::nat list> @ Bk \<up> ll) p stp) \<and>
                  (\<exists>kr lr. steps0 (1, Bk \<up> kl , <ns::nat list> @ Bk \<up> ll) p stp = (0, Bk \<up> kr,  <ms::nat list> @ Bk \<up> lr))"
    by (metis is_finalI)

  then have "\<forall>tap. (\<exists>kl ll. tap = (Bk \<up> kl, <ns::nat list> @ Bk \<up> ll) )
                    \<longrightarrow> (\<exists>stp. is_final (steps0 (1, tap) p stp) \<and>
                  (\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr,  <ms::nat list> @ Bk \<up> lr)) holds_for steps0 (1, tap) p stp)"
    using holds_for.simps by force
  then show ?thesis
    unfolding Hoare_halt_def
    by auto
qed
*)

lemma TMC_has_num_res_list_without_initial_Bks_iff_TMC_has_num_res_list_after_adding_Bks_to_initial_left_and_right_tape:
  " \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap.\<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>
  \<longleftrightarrow>
    \<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
proof
  assume "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap.\<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  then show "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
    using TMC_has_num_res_list_without_initial_Bks_imp_TMC_has_num_res_list_after_adding_Bks_to_initial_left_and_right_tape by auto
next
  assume "\<lbrace>\<lambda>tap. \<exists>kl ll. tap = (Bk \<up> kl, <ns::nat list> @ Bk \<up> ll)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap.\<exists>kr lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
    by (simp add: Hoare_halt_def assert_imp_def)
qed


subsection \<open>Halting in a Standard Configuration\<close>

subsubsection \<open>Definition of Halting in a Standard Configuration\<close>

text \<open>The predicates \<open>TMC_has_num_res p ns\<close> and \<open>TMC_has_num_list_res\<close> describe that
 a run of the Turing program \<open>p\<close> on input \<open>ns\<close> reaches the final state 0
 and the final tape produced thereby is standard.
 Thus, the computation of the Turing machine \<open>p\<close> produced a result, which is
 either a single numeral or a list of numerals.

Since trailing blanks on the initial left or right tape do not matter,
we may restrict our definitions to the case where
 the initial left tape is empty and
 there are no trailing blanks on the initial right tape!
\<close>

definition TMC_has_num_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "TMC_has_num_res p ns \<equiv>
     \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"

lemma TMC_has_num_res_iff: "TMC_has_num_res p ns
         \<longleftrightarrow>
       (\<exists>stp. is_final (steps0 (1, [],<ns::nat list>) p stp) \<and>
              (\<exists>k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)))"
  unfolding TMC_has_num_res_def
proof
  assume "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
  then show "\<exists>stp. is_final (steps0 (1, [], <ns::nat list>) p stp) \<and> (\<exists>k n l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
    by (smt Hoare_halt_def holds_for.elims(2) is_final.elims(2) is_final_eq)
next
  assume "\<exists>stp. is_final (steps0 (1, [], <ns::nat list>) p stp) \<and> (\<exists>k n l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
    by (metis (mono_tags, lifting) Hoare_halt_def holds_for.simps)
qed

(* for clarification
lemma TMC_has_num_res_iff': "TMC_has_num_res p ns \<equiv>
       (\<exists>stp k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
  by (smt TMC_has_num_res_iff is_finalI steps_0 steps_add)
*)

(* --- *)

definition TMC_has_num_list_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> bool"
  where
    "TMC_has_num_list_res p ns \<equiv>
     \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ms lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
 
lemma TMC_has_num_list_res_iff: "TMC_has_num_list_res p ns
         \<longleftrightarrow>
       (\<exists>stp. is_final (steps0 (1, [],<ns::nat list>) p stp) \<and>
              (\<exists>k ms l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk \<up> l)))"
  unfolding TMC_has_num_list_res_def
proof
  assume "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k ms l. tap = (Bk \<up> k, <ms::nat list> @ Bk \<up> l)\<rbrace>"
  then show "\<exists>stp. is_final (steps0 (1, [], <ns::nat list>) p stp) \<and> (\<exists>k ms l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk \<up> l))"
    by (smt Hoare_halt_def holds_for.elims(2) is_final.elims(2) is_final_eq)
next
  assume "\<exists>stp. is_final (steps0 (1, [], <ns::nat list>) p stp) \<and> (\<exists>k ms l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk \<up> l))"
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k ms l.   tap = (Bk \<up> k, <ms::nat list> @ Bk \<up> l)\<rbrace>"
    by (metis (mono_tags, lifting) Hoare_halt_def holds_for.simps)
qed

(* for clarification
lemma TMC_has_num_list_res_iff': "TMC_has_num_list_res p ns \<equiv>
        (\<exists>stp k ms l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk \<up> l))"
  by (smt TMC_has_num_list_res_iff is_finalI steps_0 steps_add)
*)

subsubsection \<open>Relation between TMC\_has\_num\_res and TMC\_has\_num\_list\_res\<close>

text \<open>A computation of a Turing machine, which started on a list of numerals and halts in a
 standard configuration with a single numeral result is a special case of a halt in a standard configuration that
halts with a list of numerals.\<close>

(* FABR: this is an important lemma, since it motivates and validates our extension
 * of various concepts to lists of natural numbers or numerals
 *)

theorem TMC_has_num_res_imp_TMC_has_num_list_res: 
  "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>
   \<Longrightarrow>
   \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ms lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
proof -
  assume A: "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"

  then have "\<exists>stp. is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and>
                 (\<exists>n kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <n::nat> @ Bk \<up> lr))"
    by (smt Hoare_halt_def holds_for.elims(2) is_final.elims(2) is_final_eq)
  then obtain stp where
    w_stp: "is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and>
                 (\<exists>n kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <n::nat> @ Bk \<up> lr))"
    by blast

  then have "(\<exists>n kr lr. steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <n::nat> @ Bk \<up> lr))"
    by auto

  then obtain n kr lr where "steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <n::nat> @ Bk \<up> lr)"
    by blast
  then have "steps0 (1, ([], <ns::nat list>)) p stp = (0, Bk \<up> kr, <[n::nat]> @ Bk \<up> lr)"
    by (simp add: tape_of_list_def)
  then have "is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and> (\<exists>kr lr. (steps0 (1, ([], <ns::nat list>)) p stp) = (0, Bk \<up> kr, <[n::nat]> @ Bk \<up> lr))"
    by (simp add: is_final_eq)

  then have "is_final (steps0 (1, ([], <ns::nat list>)) p stp) \<and> (\<exists>ms kr lr. (steps0 (1, ([], <ns::nat list>)) p stp) = (0, Bk \<up> kr, <ms::nat list> @ Bk \<up> lr))"
    by blast

  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ms lr. tap = (Bk \<up> kr, <ms::nat list> @ Bk \<up> lr)\<rbrace>"
    by (metis (mono_tags, lifting) Hoare_halt_def  holds_for.simps)
qed

corollary TMC_has_num_res_imp_TMC_has_num_list_res': "TMC_has_num_res p ns \<Longrightarrow> TMC_has_num_list_res p ns"
  unfolding TMC_has_num_res_def TMC_has_num_list_res_def 
  using TMC_has_num_res_imp_TMC_has_num_list_res
  by auto


subsubsection \<open>Convenience Lemmas for Halting Problems \<close>

lemma Hoare_halt_with_Oc_imp_std_tap:
  assumes "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up> l)\<rbrace>"
  shows "TMC_has_num_res p ns"
  unfolding TMC_has_num_res_def
proof -
  from assms have F0: "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>"
    by (auto simp add: tape_of_nat_def)
  show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
  by (smt F0 Hoare_halt_E0 Hoare_halt_I0)
qed

lemma Hoare_halt_with_OcOc_imp_std_tap:
  assumes "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @ Bk \<up> l)\<rbrace>"
  shows "TMC_has_num_res p ns"
  unfolding TMC_has_num_res_def
proof -
  from assms have "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>"
    by (auto simp add: tape_of_nat_def)
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
 by (smt Hoare_haltE Hoare_haltI holds_for.elims(2) holds_for.simps)
qed

subsubsection \<open>Hoare\_halt on numeral lists with single numeral result\<close>
(* For automation we use Hoare triples directly instead of the concept TMC_has_num_res.
 * Reason: reduce number of theorems used by the simplifier.
 *)

lemma Hoare_halt_on_numeral_imp_result: (* special case of Hoare_halt_D *)
  assumes "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)))\<rbrace>"
  shows "\<exists>stp k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk\<up> l)"
  using TMC_has_num_res_def TMC_has_num_res_iff assms by blast

lemma Hoare_halt_on_numeral_imp_result_rev: (* special case of Hoare_halt_I2 *)
  assumes "\<exists>stp k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk\<up> l)"
  shows "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)))\<rbrace>"
  using TMC_has_num_res_def TMC_has_num_res_iff assms is_final_eq by force

lemma Hoare_halt_on_numeral_imp_result_iff: (* special case of Hoare_halt2_iff *)
"\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)))\<rbrace>
 \<longleftrightarrow>
 (\<exists>stp k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk\<up> l))"
  using Hoare_halt_on_numeral_imp_result Hoare_halt_on_numeral_imp_result_rev by blast

subsubsection \<open>Hoare\_halt on numeral lists with numeral list result\<close>
(* For automation we use Hoare triples directly instead of the concept TMC_has_num_list_res.
 * Reason: reduce number of theorems used by the simplifier.
 *)

lemma Hoare_halt_on_numeral_imp_list_result: (* special case of Hoare_halt_D *)
  assumes "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k ms l. tap = (Bk \<up> k, <ms::nat list> @ Bk \<up> l)))\<rbrace>"
  shows "\<exists>stp k ms l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk\<up> l)"  
  using TMC_has_num_list_res_def TMC_has_num_list_res_iff assms by blast

lemma Hoare_halt_on_numeral_imp_list_result_rev: (* special case of Hoare_halt_I2 *)
  assumes "\<exists>stp k ms l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk\<up> l)"
  shows "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k ms l. tap = (Bk \<up> k, <ms::nat list> @ Bk \<up> l)))\<rbrace>"
  by (metis (mono_tags, lifting) Hoare_haltI assms holds_for.simps is_finalI)

lemma Hoare_halt_on_numeral_imp_list_result_iff: (* special case of Hoare_halt2_iff *)
  "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k ms l. tap = (Bk \<up> k, <ms::nat list> @ Bk \<up> l)))\<rbrace>
   \<longleftrightarrow>
   (\<exists>stp k ms l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <ms::nat list> @ Bk\<up> l))"  
  using Hoare_halt_on_numeral_imp_list_result Hoare_halt_on_numeral_imp_list_result_rev by blast

subsection \<open>Trailing left blanks do not matter for computations with result\<close>

(* adding trailing blanks on the initial left tape needs tough lemmas (see BlanksDoNotMatter)  *)

lemma TMC_has_num_res_NIL_impl_TMC_has_num_res_with_left_BKs:
  "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>
   \<Longrightarrow>
   \<lbrace>(\<lambda>tap. \<exists>z. tap = (Bk\<up>z, <ns>))\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
proof -
  assume   "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
  then have "\<exists>stp k n l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk\<up> l)"
    by (rule Hoare_halt_on_numeral_imp_result)

  then obtain n where "\<exists>stp k l. steps0 (1, [],<ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk\<up> l)" by blast

  then have "\<forall>z. \<exists>stp k l. (steps0 (1, (Bk\<up>z, <ns::nat list>)) p stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    by (rule ex_steps_left_tape_Nil_imp_All)

  then have "\<lbrace>(\<lambda>tap. \<exists>z. tap = (Bk\<up>z, <ns::nat list>))\<rbrace> p \<lbrace> (\<lambda>tap. (\<exists>k l. tap = (Bk \<up> k,  <n::nat> @ Bk \<up> l))) \<rbrace>"
    by (rule Hoare_halt_add_Bks_left_tape_L2)
    
  then show "\<lbrace>\<lambda>tap. \<exists>z. tap = (Bk \<up> z, <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
    using Hoare_halt_iff \<open>\<forall>z. \<exists>stp k l. steps0 (1, Bk \<up> z, <ns>) p stp = (0, Bk \<up> k, <n> @ Bk \<up> l)\<close> by fastforce
qed

(* removing trailing blanks on the initial left tape (is easy) *)

corollary TMC_has_num_res_NIL_iff_TMC_has_num_res_with_left_BKs:
  " \<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>
    \<longleftrightarrow>
    \<lbrace>(\<lambda>tap. \<exists>z. tap = (Bk\<up>z, <ns>))\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
proof
  assume "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  then show "\<lbrace>\<lambda>tap. \<exists>z. tap = (Bk \<up> z, <ns>)\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
    using TMC_has_num_res_NIL_impl_TMC_has_num_res_with_left_BKs by blast
next
  assume "\<lbrace>\<lambda>tap. \<exists>z. tap = (Bk \<up> z, <ns>)\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
    by (simp add: Hoare_halt_def assert_imp_def)
qed

subsection \<open>About Turing Computations and the result they yield\<close>

definition TMC_yields_num_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "TMC_yields_num_res tm ns n \<equiv> (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"

definition TMC_yields_num_list_res :: "tprog0 \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where "TMC_yields_num_list_res tm ns ms \<equiv> (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <ms::nat list> @ Bk \<up> l))"

(* This is for documentation and explanation: TMC_yields_num_res_unfolded_into_Hoare_halt *)
lemma TMC_yields_num_res_unfolded_into_Hoare_halt:
  "TMC_yields_num_res tm ns n \<equiv> \<lbrace>(\<lambda>tap. tap = ([], <ns>))\<rbrace> tm \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk\<up> l))\<rbrace>"
  by (smt Hoare_halt_iff TMC_yields_num_res_def)

(* This is for documentation and explanation: TMC_yields_num_list_res_unfolded_into_Hoare_halt *)
lemma TMC_yields_num_list_res_unfolded_into_Hoare_halt:
  "TMC_yields_num_list_res tm ns ms \<equiv> \<lbrace>(\<lambda>tap. tap = ([], <ns>))\<rbrace> tm \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <ms::nat list> @ Bk\<up> l))\<rbrace>"
  by (smt Hoare_halt_iff TMC_yields_num_list_res_def)


(* A variant of rule Hoare_plus_halt using TMC_yields_num_list_res and TMC_yields_num_res *)
lemma TMC_yields_num_res_Hoare_plus_halt:
  assumes "TMC_yields_num_list_res tm1 nl r1"
    and "TMC_yields_num_res tm2 r1 r2"
    and "composable_tm0 tm1"
  shows "TMC_yields_num_res (tm1 |+| tm2) nl r2"
proof -
  from assms
  have "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> tm1 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <r1::nat list> @ Bk \<up> l)\<rbrace>"
    using TMC_yields_num_list_res_unfolded_into_Hoare_halt 
    by auto
  moreover from assms
  have "\<lbrace>\<lambda>tap. tap = ([], <r1>)\<rbrace> tm2 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <r2> @ Bk \<up> l)\<rbrace>"
    using TMC_yields_num_res_unfolded_into_Hoare_halt
      Hoare_halt_def Hoare_halt_iff TMC_yields_num_res_def by blast
  ultimately
  have "\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> (tm1 |+| tm2) \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <r2> @ Bk \<up> l)\<rbrace>"  
    using \<open>composable_tm0 tm1\<close>
    using Hoare_halt_left_tape_Nil_imp_All_left_and_right Hoare_plus_halt 
    by (simp add: tape_of_list_def)
  then show ?thesis
    using TMC_yields_num_res_unfolded_into_Hoare_halt by auto
qed


(*

 TODO test mixfix notation for TMC_yields_num_res:  \<llangle>tm: ns \<mapsto> n\<rrangle> 
 TODO test mixfix notation for TMC_has_num_res:     \<llangle>tm: ns\<down>\<rrangle> 
 
    Trial for notation of TMC_yields_num_res tm ns n: 
    
      "TMC_yields_num_res tm ns n \<equiv> (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
    
         ns \<midarrow><tm>\<rightarrow> n
    
         \<llangle>tm: ns \<leadsto> n\<rrangle>   that's good
    
         \<llangle>tm: ns \<mapsto> n\<rrangle>   that's good as well
         
     TMC_has_num_res 
    
      "TMC_has_num_res p ns \<equiv> \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> p \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
    
         \<llangle>tm: ns\<down>\<rrangle> 

 *)

end
