(* Title: thys/TuringComputable.thy
   Author: Franz Regensburger (FABR) 03/2022
 *)

section \<open>Turing Computable Functions\<close>

theory TuringComputable
  imports
    "HaltingProblems_K_H"
begin

(* -------------------------------------------------------------------------- *)

(*
declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]
*)

subsection \<open>Definition of Partial Turing Computability\<close>

text \<open>We present two variants for a definition of Partial Turing Computability,
 which we prove to be equivalent, later on.\<close>

subsubsection \<open>Definition Variant 1\<close>

definition turing_computable_partial :: "(nat list \<Rightarrow> nat option) \<Rightarrow> bool"
  where "turing_computable_partial f \<equiv> (\<exists>tm. \<forall>ns n.
          (f ns = Some n \<longrightarrow> (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
          (f ns = None   \<longrightarrow> \<not>\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>))"

(* Major consequences of the definition *)

(* This is for documentation and explanation: turing_computable_partial_unfolded_into_TMC_yields_TMC_has_conditions *)
lemma turing_computable_partial_unfolded_into_TMC_yields_TMC_has_conditions:
 "turing_computable_partial f \<equiv> (\<exists>tm. \<forall>ns n.
          (f ns = Some n \<longrightarrow>   TMC_yields_num_res tm ns n) \<and>
          (f ns = None   \<longrightarrow> \<not> TMC_has_num_res  tm ns   ) )"
  unfolding TMC_yields_num_res_def TMC_has_num_res_def
  by (simp add: turing_computable_partial_def)

(* This is for rewriting *)
lemma turing_computable_partial_unfolded_into_Hoare_halt_conditions:
 "turing_computable_partial f \<longleftrightarrow> (\<exists>tm. \<forall>ns n.
          (f ns = Some n \<longrightarrow>  \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk\<up> l) \<rbrace> ) \<and>
          (f ns = None   \<longrightarrow> \<not>\<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l) \<rbrace>))"
  unfolding turing_computable_partial_def
proof
  assume "\<exists>tm. \<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                      (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l) \<rbrace>)"
  then obtain tm where
    w_tm1:"\<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                 (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l) \<rbrace>)"
    by blast
  have "\<forall>ns n. (f ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
               (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l) \<rbrace>)"
    apply (safe)
  proof -
    (* ---- Some case *)
    show "\<And>ns n. f ns = Some n \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n> @ Bk \<up> l)\<rbrace>"
    proof -
      fix ns n
      assume "f ns = Some n"
      with w_tm1 have F1: "\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" by auto
      show "\<lbrace>\<lambda>tap.  tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
      proof (rule Hoare_haltI)
        fix l r
        assume "(l, r) = ([]::cell list, <ns::nat list>)"
        then show "\<exists>stp. is_final (steps0 (1, l, r) tm stp) \<and> (\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) holds_for steps0 (1, l, r) tm stp"
          by (metis (mono_tags, lifting) F1 holds_for.simps is_finalI)
      qed
    qed
  next
    (* ---- None case *)
    show "\<And>ns n. \<lbrakk>f ns = None; \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace> \<rbrakk> \<Longrightarrow> False"
    proof -
      fix ns n
      assume "f ns = None" and "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
      with w_tm1 show False
        by simp
    qed
  qed
  then show "\<exists>tm. \<forall>ns n. (f ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n> @ Bk \<up> l)\<rbrace>) \<and>
            (f ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
    by auto
next
  assume "\<exists>tm. \<forall>ns n. (f ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
                      (f ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
  then obtain tm where
    w_tm2: "\<forall>ns n. (f ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
                   (f ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
    by blast
  have "\<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
               (f ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
    apply (safe)
  proof -
    (* ---- Some case *)
    show "\<And>ns n . f ns = Some n \<Longrightarrow> \<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n> @ Bk \<up> l)"
    proof -
      fix ns n z
      assume "f ns = Some n"
      with w_tm2 have "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>" by blast

      then show "\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
        by (smt Hoare_halt_def holds_for.elims(2) is_final.elims(2) snd_conv)
    qed
  next
    (* ---- None case *)
    show "\<And>ns n. \<lbrakk>f ns = None; \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>\<rbrakk> \<Longrightarrow> False"
    proof -
      fix ns n
      assume "f ns = None" and "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
      with w_tm2 show False
        by simp
    qed
  qed
  then
  show "\<exists>tm. \<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                    (f ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
    by blast
qed


(* --------------------------------------------------------------------------------------------------------- *)

subsubsection \<open>Characteristic Functions of Sets\<close>

definition chi_fun :: "(nat list) set \<Rightarrow> (nat list \<Rightarrow> nat option)"
  where
    "chi_fun nls = (\<lambda>nl. if nl \<in> nls then Some 1 else Some 0)"

lemma chi_fun_0_iff: "nl \<notin> nls \<longleftrightarrow> chi_fun nls nl = Some 0"
  unfolding chi_fun_def by auto

lemma chi_fun_1_iff: "nl \<in> nls \<longleftrightarrow> chi_fun nls nl = Some 1"
  unfolding chi_fun_def by auto

lemma chi_fun_0_I: "nl \<notin> nls \<Longrightarrow> chi_fun nls nl = Some 0"
  unfolding chi_fun_def by auto

lemma chi_fun_0_E: "(chi_fun nls nl = Some 0 \<Longrightarrow> P) \<Longrightarrow> nl \<notin> nls \<Longrightarrow> P"
  unfolding chi_fun_def by auto

lemma chi_fun_1_I: "nl \<in> nls \<Longrightarrow> chi_fun nls nl = Some 1"
  unfolding chi_fun_def by auto

lemma chi_fun_1_E: "(chi_fun nls nl = Some 1 \<Longrightarrow> P) \<Longrightarrow> nl \<in> nls \<Longrightarrow> P"
  unfolding chi_fun_def by auto

(* --------------------------------------------------------------------------------------------------------- *)

subsubsection \<open>Relation between Partial Turing Computability and Turing Decidability\<close>

text \<open>If a set A is Turing Decidable its characteristic function is Turing Computable partial and vice versa.
Please note, that although the characteristic function has an option type it will always yield Some value.
\<close>

theorem turing_decidable_imp_turing_computable_partial:
  "turing_decidable A \<Longrightarrow> turing_computable_partial (chi_fun A)"
proof -
  assume "turing_decidable A"
  then have
    "(\<exists>D. (\<forall>nl. 
         (nl \<in> A \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk\<up> l))\<rbrace>)
       \<and> (nl \<notin> A \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk\<up> l))\<rbrace>)
     ))"
    unfolding turing_decidable_def by auto

  then obtain D where w_D:
    "(\<forall>nl. 
         (nl \<in> A \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk\<up> l))\<rbrace>)
       \<and> (nl \<notin> A \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk\<up> l))\<rbrace>)
     )" by blast

  then have F1:
    "(\<forall>nl. 
         (chi_fun A nl = Some 1 \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk\<up> l))\<rbrace>)
       \<and> (chi_fun A nl = Some 0 \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk\<up> l))\<rbrace>)
     )" using chi_fun_def by force

  have F2: "\<forall>nl. (chi_fun A nl = Some 1 \<or> chi_fun A nl = Some 0)" using chi_fun_def
    by simp

  show ?thesis
  proof (rule turing_computable_partial_unfolded_into_Hoare_halt_conditions[THEN iffD2])
    have "\<forall>ns n. (chi_fun A ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> D \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n> @ Bk \<up> l)\<rbrace>) \<and>
                 (chi_fun A ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> D \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"
      apply (safe)
    proof -
      show "\<And>ns n. chi_fun A ns = Some n \<Longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> D \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n> @ Bk \<up> l)\<rbrace>"
      proof -
        fix ns :: "nat list" and n :: nat
        assume "chi_fun A ns = Some n"
        then have "Some n = Some 1 \<or> Some n = Some 0"
          by (metis F2)
        then show "\<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> D \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n> @ Bk \<up> l)\<rbrace>"
          using \<open>chi_fun A ns = Some n\<close> F1 by blast
      qed
    next
      show " \<And>ns n. \<lbrakk>chi_fun A ns = None; \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> D \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace> \<rbrakk> \<Longrightarrow> False"
        by (metis F2 option.distinct(1))
    qed
    then show "\<exists>tm. \<forall>ns n.
                    (chi_fun A ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
                    (chi_fun A ns = None \<longrightarrow> \<not> \<lbrace>\<lambda>tap. tap = ([], <ns>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>)"     
      using F2 option.simps(3) by blast 
  qed
qed

theorem turing_computable_partial_imp_turing_decidable:
  "turing_computable_partial (chi_fun A) \<Longrightarrow> turing_decidable A"
proof -
  assume "turing_computable_partial (chi_fun A)"
  then have "\<exists>tm. \<forall>ns n.
            (chi_fun A ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
            (chi_fun A ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace> )"
    using turing_computable_partial_unfolded_into_Hoare_halt_conditions[THEN iffD1] by auto

  then obtain tm where w_tm: "\<forall>ns n.
            (chi_fun A ns = Some n \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>) \<and>
            (chi_fun A ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
    by auto
  then have "\<forall>ns.
          (ns \<in> A \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>) \<and>
          (ns \<notin> A \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>)"
    by (blast intro: chi_fun_0_I chi_fun_1_I)

  then have "(\<exists>D.(\<forall>ns.
          (ns \<in> A \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>) \<and>
          (ns \<notin> A \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> tm \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>) ))"
    by auto

  then show ?thesis using turing_decidable_def by auto
qed

corollary turing_computable_partial_iff_turing_decidable:
 "turing_decidable A \<longleftrightarrow> turing_computable_partial (chi_fun A)"
  by (auto simp add: turing_computable_partial_imp_turing_decidable turing_decidable_imp_turing_computable_partial)

subsubsection \<open>Examples for uncomputable functions\<close>

text \<open>Now, we prove that the characteristic functions of the undecidable sets K1 and H1 are both uncomputable.\<close>

context hpk
begin

theorem "\<not>(turing_computable_partial (chi_fun K1))"
  using not_Turing_decidable_K1 turing_computable_partial_imp_turing_decidable by blast

theorem "\<not>(turing_computable_partial (chi_fun H1))"
  using not_Turing_decidable_H1 turing_computable_partial_imp_turing_decidable by blast

end

subsubsection \<open>The Function associated with a Turing Machine\<close>

text \<open>With every Turing machine, we can associate a function.\<close>

(* 
Compare to definition of \<psi>\<^sub>P(r1, ... , rm)
in the book

[DSW94, pp 29]
Computability, Complexity, and Languages
Davis, Sigal and Weyuker
Academic Press, 2nd Edition, 1994
ISBN 0-12-206382-1

Relation between our notion fun_of_tm and \<psi>\<^sub>P of [DSW94, pp 29]

  \<psi>\<^sub>P(r1, ... , rm) = y  \<longleftrightarrow>  fun_of_tm tm <[r1, ... , rm]> = Some y

and 

  \<psi>\<^sub>P(r1, ... , rm)\<up>  \<longleftrightarrow>  fun_of_tm tm <[r1, ... , rm]> = None

Note: for the GOTO pgms of [DSW94] the question whether the program P halts
      with a standard tape or with a non-standard tape does not matter since
      there are no tapes to consider. There are only registers with values.
      If the program P halts on input (r1, ... , rm) it yields a result, always.

      On the other hand, our Turing machines may reach the final state 0
      with a non-standard tape and thus provide no valid output.

      In such a case, fun_of_tm tm <[r1, ... , rm]> = None per definition.
*)

definition fun_of_tm :: "tprog0 \<Rightarrow> (nat list \<Rightarrow> nat option)"
  where "fun_of_tm tm ns \<equiv>
           (if \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>
            then 
              let result =
                 (THE n. \<exists>stp k l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))
              in Some result                     
            else None)"

text \<open>Some immediate consequences of the definition.\<close>

(* This is for documentation and explanation: fun_of_tm_unfolded_into_TMC_yields_TMC_has_conditions *)

lemma fun_of_tm_unfolded_into_TMC_yields_TMC_has_conditions:  
   "fun_of_tm tm  \<equiv>
      (\<lambda>ns. (if TMC_has_num_res tm ns
             then 
               let result = (THE n. TMC_yields_num_res tm ns n)
               in Some result                     
             else None)
       )"          
  unfolding TMC_yields_num_res_def TMC_has_num_res_def          
  using fun_of_tm_def by presburger

lemma fun_of_tm_is_None:
  assumes "\<not>(\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
  shows "fun_of_tm tm ns = None"
proof -
  from assms show "fun_of_tm tm ns = None" by (auto simp add: fun_of_tm_def)
qed

lemma fun_of_tm_is_None_rev:
  assumes "fun_of_tm tm ns = None"
  shows "\<not>(\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
  using assms fun_of_tm_def by auto

corollary fun_of_tm_is_None_iff: "fun_of_tm tm ns = None \<longleftrightarrow> \<not>(\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
  by (auto simp add: fun_of_tm_is_None fun_of_tm_is_None_rev)

(* This is for documentation and explanation: fun_of_tm_is_None_iff' *)
corollary fun_of_tm_is_None_iff': "fun_of_tm tm ns = None \<longleftrightarrow> \<not> TMC_has_num_res tm ns"
  unfolding TMC_has_num_res_def
  by (auto simp add: fun_of_tm_is_None fun_of_tm_is_None_rev )

lemma fun_of_tm_ex_Some_n':
  assumes "\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  shows "\<exists>n. fun_of_tm tm ns = Some n"
  using assms fun_of_tm_def by auto

lemma fun_of_tm_ex_Some_n'_rev:
  assumes "\<exists>n. fun_of_tm tm ns = Some n"
  shows "\<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  using assms fun_of_tm_is_None by fastforce

corollary fun_of_tm_ex_Some_n'_iff:
 "(\<exists>n. fun_of_tm tm ns = Some n)
  \<longleftrightarrow>
  \<lbrace> \<lambda>tap. tap = ([], <ns>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  by (auto simp add: fun_of_tm_ex_Some_n' fun_of_tm_ex_Some_n'_rev)

subsubsection \<open>Stronger results about uniqueness of results\<close>

corollary Hoare_halt_on_numeral_list_yields_unique_list_result_iff:
  "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ml lr. tap = (Bk \<up> kr, <ml::nat list> @ Bk \<up> lr)\<rbrace>
    \<longleftrightarrow>
    (\<exists>!ml. \<exists>stp k l. steps0 (1,[], <nl::nat list>) p stp = (0, Bk \<up> k, <ml::nat list> @ Bk \<up> l))"
proof
  assume A: "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ml lr. tap = (Bk \<up> kr,  <ml::nat list> @ Bk \<up> lr)\<rbrace>"
  show "\<exists>!ml. \<exists>stp k l. steps0 (1, [], <nl::nat list>) p stp = (0, Bk \<up> k, <ml::nat list> @ Bk \<up> l)"
  proof (rule ex_ex1I)
    show "\<exists>ml stp k l. steps0 (1, [], <nl::nat list>) p stp = (0, Bk \<up> k, <ml::nat list> @ Bk \<up> l)"
      using A
      using Hoare_halt_iff by auto
  next
    show "\<And>ml y. \<lbrakk>\<exists>stp k l. steps0 (1, [], <nl::nat list>) p stp = (0, Bk \<up> k, <ml::nat list> @ Bk \<up> l);
                   \<exists>stp k l. steps0 (1, [], <nl::nat list>) p stp = (0, Bk \<up> k, <y::nat list> @ Bk \<up> l)\<rbrakk> \<Longrightarrow> ml = y"
      by (metis nat_le_linear prod.inject prod.inject stable_config_after_final_ge' unique_Bk_postfix_numeral_list)
  qed
next
  assume "(\<exists>!ml. \<exists>stp k l. steps0 (1,[], <nl::nat list>) p stp = (0, Bk \<up> k, <ml::nat list> @ Bk \<up> l))"
  then show "\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>kr ml lr. tap = (Bk \<up> kr, <ml::nat list> @ Bk \<up> lr)\<rbrace>"
    using Hoare_halt_on_numeral_imp_list_result_rev by blast
qed

corollary Hoare_halt_on_numeral_yields_unique_result_iff:
  "\<lbrace>(\<lambda>tap. tap = ([], <ns::nat list>))\<rbrace> p \<lbrace>(\<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)))\<rbrace>
  \<longleftrightarrow>
  (\<exists>!n. \<exists>stp k l. steps0 (1,[], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
proof 
  assume A: "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
  show "\<exists>!n. \<exists>stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  proof (rule ex_ex1I)
    show "\<exists>n stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
      using A 
      using Hoare_halt_on_numeral_imp_result by blast
  next
    show "\<And>n y. \<lbrakk>\<exists>stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l);
                 \<exists>stp k l. steps0 (1, [], <ns>) p stp = (0, Bk \<up> k, <y> @ Bk \<up> l)\<rbrakk> \<Longrightarrow> n = y"
      by (smt before_final is_final_eq le_less least_steps less_Suc_eq not_less_iff_gr_or_eq snd_conv unique_decomp_std_tap)
  qed
next
  assume "\<exists>!n. \<exists>stp k l. steps0 (1, [], <ns::nat list>) p stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  then show "\<lbrace>\<lambda>tap. tap = ([], <ns::nat list>)\<rbrace> p \<lbrace>\<lambda>tap. \<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)\<rbrace>"
    using Hoare_halt_on_numeral_imp_result_rev by blast
qed

(* --- *)

lemma fun_of_tm_is_Some_unique_value:
  assumes "steps0 (1, ([], <ns>)) tm stp = (0, Bk \<up> k1, <n::nat> @ Bk \<up> l1)"
  shows "fun_of_tm tm ns = Some n"
proof -
  from assms have F0: "TMC_has_num_res tm ns"   
    using Hoare_halt_on_numeral_imp_result_rev TMC_has_num_res_def by blast
  then have 
  "fun_of_tm tm ns = (
        let result =
            (THE n. \<exists>stp k l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))
        in Some result)"
    by (simp add: F0 TMC_has_num_res_def fun_of_tm_def fun_of_tm_ex_Some_n' )
  then have F1: "fun_of_tm tm ns =
                 Some (THE n. \<exists>stp k l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
    by auto
  have "(THE n. \<exists>stp k l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)) = n"
  proof (rule the1I2)
    from F0
    have F2: "(\<exists>!n.\<exists>stp k l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"      
      using Hoare_halt_on_numeral_imp_result_rev Hoare_halt_on_numeral_yields_unique_result_iff assms by blast
    then 
    show "\<exists>!n. \<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
      by auto
  next
    show "\<And>x. \<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <x> @ Bk \<up> l) \<Longrightarrow> x = n"
      using Hoare_halt_on_numeral_imp_result_rev Hoare_halt_on_numeral_yields_unique_result_iff assms by blast
  qed
  then show ?thesis
    using F1 by blast
qed

(* --- *)

lemma fun_of_tm_ex_Some_n:
  assumes "\<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  shows "\<exists>stp k n l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l) \<and>
                     fun_of_tm tm ns = Some (n::nat)"
  using Hoare_halt_on_numeral_imp_result assms fun_of_tm_is_Some_unique_value by blast

lemma fun_of_tm_ex_Some_n_rev:
  assumes "\<exists>stp k n l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l) \<and>
                       fun_of_tm tm ns = Some n"
  shows "\<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
proof -
  from assms have "\<exists>stp k n l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
    by blast

  then show ?thesis    
    using Hoare_haltE Hoare_haltI assms fun_of_tm_ex_Some_n'_rev steps.simps(1)
    by auto
qed

corollary fun_of_tm_ex_Some_n_iff:
  "(\<exists>stp k n l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l) \<and>
                fun_of_tm tm ns = Some n)
    \<longleftrightarrow>
   \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
  using fun_of_tm_ex_Some_n fun_of_tm_ex_Some_n_rev
  by blast

(* --- *)

lemma fun_of_tm_eq_Some_n_imp_same_numeral_result:
  assumes "fun_of_tm tm ns = Some n"
  shows "\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" 
  by (metis (no_types, lifting) assms assms fun_of_tm_def fun_of_tm_ex_Some_n_iff fun_of_tm_is_None option.inject option.simps(3))

lemma numeral_result_n_imp_fun_of_tm_eq_n:
  assumes "\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)"
  shows "fun_of_tm tm ns = Some n"
  using  assms fun_of_tm_is_Some_unique_value by blast

corollary numeral_result_n_iff_fun_of_tm_eq_n:
  "fun_of_tm tm ns = Some n
  \<longleftrightarrow>
  (\<exists>stp k l. steps0 (1, [], <ns::nat list>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))"
  using fun_of_tm_eq_Some_n_imp_same_numeral_result numeral_result_n_imp_fun_of_tm_eq_n
  by blast

(* This is for documentation and explanation: numeral_result_n_iff_fun_of_tm_eq_n' *)
corollary numeral_result_n_iff_fun_of_tm_eq_n':
  "fun_of_tm tm ns = Some n \<longleftrightarrow> TMC_yields_num_res tm ns n"
  using fun_of_tm_eq_Some_n_imp_same_numeral_result numeral_result_n_imp_fun_of_tm_eq_n
  unfolding TMC_yields_num_res_def
  by blast

subsubsection \<open>Definition of Turing computability Variant 2\<close>

definition turing_computable_partial' :: "(nat list \<Rightarrow> nat option) \<Rightarrow> bool"
  where "turing_computable_partial' f \<equiv> \<exists>tm. fun_of_tm tm = f"

lemma turing_computable_partial'I:
  "(\<And>ns. fun_of_tm tm ns = f ns) \<Longrightarrow> turing_computable_partial' f"
  unfolding turing_computable_partial'_def
proof -
  assume "(\<And>ns. fun_of_tm tm ns = f ns)"
  then have "fun_of_tm tm = f" by (rule ext)
  then show "\<exists>tm. fun_of_tm tm = f" by auto
qed


subsubsection \<open>Definitional Variants 1 and 2 of Partial Turing Computability are equivalent\<close>

text \<open>Now, we prove the equivalence of the two definitions of Partial Turing Computability.\<close>

lemma turing_computable_partial'_imp_turing_computable_partial:
  "turing_computable_partial' f \<longrightarrow> turing_computable_partial f"
  unfolding turing_computable_partial'_def turing_computable_partial_def
proof
  assume "\<exists>tm. fun_of_tm tm = f"
  then obtain tm where w_tm: "fun_of_tm tm = f" by blast
  show "\<exists>tm. \<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                    (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
  proof
    show "\<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
    proof
      fix ns
      show "\<forall>n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
      proof
        fix n::nat
        show "(f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n> @ Bk \<up> l))) \<and>
              (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
        proof
          show "f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n> @ Bk \<up> l))"
          proof
            assume "f ns = Some n"
            with w_tm have A: "fun_of_tm tm ns = Some n" by auto
            then have "\<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>" using fun_of_tm_ex_Some_n'_rev by auto

            then have "\<exists>stp k m l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <m::nat> @ Bk \<up> l) \<and>
                                    fun_of_tm tm ns = Some m"
              by (rule fun_of_tm_ex_Some_n)

            with A show "\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" by auto
          qed
        next
          show "f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>"
          proof
            assume "f ns = None"
            with w_tm have A: "fun_of_tm tm ns = None" by auto
            then show "\<not>(\<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)" by (rule fun_of_tm_is_None_rev)
          qed
        qed
      qed
    qed
  qed
qed

lemma turing_computable_partial_imp_turing_computable_partial':
  "turing_computable_partial f \<longrightarrow> turing_computable_partial' f"
  unfolding turing_computable_partial_def
proof
  assume major: "\<exists>tm. \<forall>ns n.
                      (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                      (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)"
  show "turing_computable_partial' f"
  proof -
    from major obtain tm where w_tm:
      "\<forall>ns n. (f ns = Some n \<longrightarrow> (\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) \<and>
                  (f ns = None \<longrightarrow> \<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>)" by blast
    show "turing_computable_partial' f"
    proof (rule turing_computable_partial'I)
      show "\<And>ns. fun_of_tm tm ns = f ns"
      proof -
        fix ns
        show "fun_of_tm tm ns = f ns"
        proof (cases "f ns")
          case None
          then have "f ns = None" .
          with w_tm have "\<not> \<lbrace> \<lambda>tap. tap = ([], <ns::nat list>) \<rbrace> tm \<lbrace> \<lambda>tap. (\<exists>k n l. tap = (Bk \<up> k, <n::nat> @ Bk \<up> l)) \<rbrace>" by auto
          then have "fun_of_tm tm ns = None" by (rule fun_of_tm_is_None)
          with \<open>f ns = None\<close> show ?thesis by auto
        next
          case (Some m)
          then have "f ns = Some m" .
          with w_tm have B: "(\<exists>stp k l. steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <m::nat> @ Bk \<up> l))" by auto
          then obtain stp k l where w_stp_k_l: "steps0 (1, [], <ns>) tm stp = (0, Bk \<up> k, <m::nat> @ Bk \<up> l)" by blast
          then have "\<exists>stp k n l. (steps0 (1, ([], <ns>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)" by blast
          from this and w_stp_k_l have "fun_of_tm tm ns = Some m"
            by (simp add: w_stp_k_l fun_of_tm_is_Some_unique_value)
          with \<open>f ns = Some m\<close> show ?thesis by auto
        qed
      qed
    qed
  qed
qed

corollary turing_computable_partial'_turing_computable_partial_iff:
  "turing_computable_partial' f \<longleftrightarrow> turing_computable_partial f"
  by (auto simp add: turing_computable_partial'_imp_turing_computable_partial
      turing_computable_partial_imp_turing_computable_partial')

text \<open>As a now trivial consequence we obtain:\<close>

corollary "turing_computable_partial f \<equiv> \<exists>tm. fun_of_tm tm = f"
  using turing_computable_partial'_turing_computable_partial_iff turing_computable_partial'_def
  by auto


subsection \<open>Definition of Total Turing Computability\<close>

definition turing_computable_total :: "(nat list \<Rightarrow> nat option) \<Rightarrow> bool"
  where "turing_computable_total f \<equiv> (\<exists>tm. \<forall>ns. \<exists>n.
          f ns = Some n \<and>
          (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l)) )"

(* This is for documentation and explanation: turing_computable_total_unfolded_into_TMC_yields_condition *)

lemma turing_computable_total_unfolded_into_TMC_yields_condition:
  "turing_computable_total f \<equiv> (\<exists>tm. \<forall>ns. \<exists>n. f ns = Some n \<and> TMC_yields_num_res tm ns n )"
  unfolding TMC_yields_num_res_def
  by (simp add: turing_computable_total_def)

(* Major consequences of the definition *)

lemma turing_computable_total_imp_turing_computable_partial:
  "turing_computable_total f \<Longrightarrow> turing_computable_partial f"
  unfolding turing_computable_total_def turing_computable_partial_def
  by (metis option.inject option.simps(3))

corollary turing_decidable_imp_turing_computable_total_chi_fun:
  "turing_decidable A \<Longrightarrow> turing_computable_total (chi_fun A)"
  unfolding turing_computable_total_unfolded_into_TMC_yields_condition
proof -
  assume "turing_decidable A"
  then have "\<exists>D. (\<forall>nl. 
         (nl \<in> A \<longrightarrow> TMC_yields_num_res D nl (1::nat) )
       \<and> (nl \<notin> A \<longrightarrow> TMC_yields_num_res D nl (0::nat) ) )" 
    unfolding turing_decidable_unfolded_into_TMC_yields_conditions
    by auto
  then obtain D where
    w_D: "\<forall>nl. (nl \<in> A \<longrightarrow> TMC_yields_num_res D nl (1::nat) ) \<and>
               (nl \<notin> A \<longrightarrow> TMC_yields_num_res D nl (0::nat) )"
    by blast
  then have "\<forall>ns. \<exists>n. chi_fun A ns = Some n \<and> TMC_yields_num_res D ns n"
    by (simp add: w_D chi_fun_0_E chi_fun_def)
  then show "\<exists>tm. \<forall>ns. \<exists>n. chi_fun A ns = Some n \<and> TMC_yields_num_res tm ns n"
    by auto
qed

(* --- alternative definition turing_computable_total' --- *)

definition turing_computable_total' :: "(nat list \<Rightarrow> nat option) \<Rightarrow> bool"
  where "turing_computable_total' f \<equiv> (\<exists>tm. \<forall>ns. \<exists>n. f ns = Some n \<and> fun_of_tm tm = f)"

theorem turing_computable_total'_eq_turing_computable_total:
  "turing_computable_total' f = turing_computable_total f"
proof
  show "turing_computable_total' f \<Longrightarrow> turing_computable_total f"
    unfolding turing_computable_total_def unfolding turing_computable_total'_def
    using fun_of_tm_eq_Some_n_imp_same_numeral_result by blast
next
  show "turing_computable_total f \<Longrightarrow> turing_computable_total' f"
    unfolding turing_computable_total_def unfolding turing_computable_total'_def
    by (metis numeral_result_n_imp_fun_of_tm_eq_n tape_of_list_def turing_computable_partial'I turing_computable_partial'_def)
qed

(* --- alternative definition turing_computable_total'' --- *)

definition turing_computable_total'' :: "(nat list \<Rightarrow> nat option) \<Rightarrow> bool"
  where "turing_computable_total'' f \<equiv> (\<exists>tm. fun_of_tm tm = f \<and> (\<forall>ns. \<exists>n. f ns = Some n))"

theorem turing_computable_total''_eq_turing_computable_total:
  "turing_computable_total'' f = turing_computable_total f"
proof
  show "turing_computable_total'' f \<Longrightarrow> turing_computable_total f"
    unfolding turing_computable_total_def unfolding turing_computable_total''_def
    by (meson fun_of_tm_eq_Some_n_imp_same_numeral_result)
next
  show "turing_computable_total f \<Longrightarrow> turing_computable_total'' f"
    unfolding turing_computable_total_def unfolding turing_computable_total''_def
    by (metis numeral_result_n_imp_fun_of_tm_eq_n tape_of_list_def turing_computable_partial'I turing_computable_partial'_def)
qed

(* --- Definition for turing_computable_total_on --- *)

definition turing_computable_total_on :: "(nat list \<Rightarrow> nat option) \<Rightarrow> (nat list) set \<Rightarrow> bool"
  where "turing_computable_total_on f A \<equiv> (\<exists>tm. \<forall>ns.
          ns \<in> A \<longrightarrow>
           (\<exists>n. f ns = Some n \<and>
                (\<exists>stp k l. (steps0 (1, ([], <ns::nat list>)) tm stp) = (0, Bk \<up> k, <n::nat> @ Bk \<up> l))) )"

(* This is for documentation and explanation: turing_computable_total_on_unfolded_into_TMC_yields_condition *)

lemma turing_computable_total_on_unfolded_into_TMC_yields_condition:
  "turing_computable_total_on f A \<equiv> (\<exists>tm. \<forall>ns. ns \<in> A \<longrightarrow> (\<exists>n. f ns = Some n \<and> TMC_yields_num_res tm ns n ))"
  unfolding TMC_yields_num_res_def
  by (simp add: turing_computable_total_on_def)

(* Major consequences of the definition *)

lemma turing_computable_total_on_UNIV_imp_turing_computable_total:
  "turing_computable_total_on f UNIV \<Longrightarrow> turing_computable_total f"
  by (simp add: turing_computable_total_on_unfolded_into_TMC_yields_condition
                turing_computable_total_unfolded_into_TMC_yields_condition)


end
