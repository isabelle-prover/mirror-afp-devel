(* Title: thys/TuringReducible.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

section \<open>Turing Reducibility\<close>

theory TuringReducible
  imports
    TuringDecidable
    StrongCopyTM
begin

subsection \<open>Definition of Turing Reducibility of Sets and Relations of Natural Numbers\<close>

(* See the book
   Computability, Complexity, and Languages,
   Davis, Sigal, Weyuker,
   Academic Press, 1983,
   ISBN 0-12-206382-1

   Chapter 4: Diagonalization and Reducibility, pp 91 
*)

text \<open>Let @{term A} and @{term B} be two sets of lists of natural numbers.

The set @{term A} is called many-one reducible to set @{term B},
if there is a Turing machine @{term tm} such that
  for all @{term "a"} we have:

\begin{enumerate}
  \item the Turing machine always computes a list @{term "b"} of natural numbers
      from the list @{term "b"} of natural numbers

  \item @{term "a \<in> A"} if and only if
      the value @{term "b"} computed by @{term tm} from @{term "a"}
      is an element of set @{term "B"}.
\end{enumerate}

We generalized our definition to lists, which eliminates the need to encode lists of natural numbers into a single natural number.
Compare this to the theory of recursive functions, where all values computed must be a single natural number.

Note however, that our notion of reducibility is not stronger than the one used in recursion theory.
Every finite list of natural numbers can be encoded into a single natural number.
Our definition is just more convenient for Turing machines, which are capable of producing lists of values.
\<close>

definition turing_reducible :: "(nat list) set \<Rightarrow> (nat list) set  \<Rightarrow> bool"
  where

    "turing_reducible A B \<equiv>
         (\<exists>tm. \<forall>nl::nat list. \<exists>ml::nat list.
              \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> tm \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <ml> @ Bk\<up> l))\<rbrace> \<and>
              (nl \<in> A \<longleftrightarrow> ml \<in> B)
         )"

(* This is for documentation and explanation: turing_reducible_unfolded_into_TMC_yields_condition *)

lemma turing_reducible_unfolded_into_TMC_yields_condition:
    "turing_reducible A B \<equiv>
         (\<exists>tm. \<forall>nl::nat list. \<exists>ml::nat list.
              TMC_yields_num_list_res tm nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B)
         )"
  unfolding TMC_yields_num_list_res_unfolded_into_Hoare_halt
  by (simp add: turing_reducible_def)

subsection \<open>Theorems about Turing Reducibility of Sets and Relations of Natural Numbers\<close>

(* A convenience lemma for the main proof *)

lemma turing_reducible_A_B_imp_composable_reducer_ex: "turing_reducible A B
       \<Longrightarrow>
       \<exists>Red. composable_tm0 Red \<and>
             (\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B))"
proof -
  assume "turing_reducible A B"
  then have "\<exists>tm. \<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res tm nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B)"
    using turing_reducible_unfolded_into_TMC_yields_condition by auto

  then obtain Red' where
    w_RedTM': "\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res Red' nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B)"
    by blast

  (* create a composable version Red from the potentially non-composable machine Red' *)

  then have "composable_tm0 (mk_composable0 Red') \<and>
             (\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res (mk_composable0 Red') nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B))"
    using w_RedTM' Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list_rev Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list composable_tm0_mk_composable0
    using TMC_yields_num_list_res_unfolded_into_Hoare_halt by blast

  then show "\<exists>Red. composable_tm0 Red \<and>
             (\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B))"
    by (rule exI)
qed

(* The main theorem about problem reduction *)

theorem turing_reducible_AB_and_decB_imp_decA:
  "\<lbrakk> turing_reducible A B; turing_decidable B \<rbrakk> \<Longrightarrow> turing_decidable A"
proof -
  assume "turing_reducible A B"
    and  "turing_decidable B"

  (* first, obtain a composable reducer machine Red *)

  from \<open>turing_reducible A B\<close>
  have "\<exists>Red. composable_tm0 Red \<and>
               (\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B))"
    by (rule turing_reducible_A_B_imp_composable_reducer_ex)

  then obtain Red where
    w_RedTM: "composable_tm0 Red \<and>
               (\<forall>nl::nat list. \<exists>ml::nat list. TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B))"
    by blast

  (* second, obtain a decider DB for problem B *)

  from \<open>turing_decidable B\<close>
  have "(\<exists>D. (\<forall>nl::nat list. 
           (nl \<in> B \<longrightarrow> TMC_yields_num_res D nl (1::nat))
         \<and> (nl \<notin> B \<longrightarrow> TMC_yields_num_res D nl (0::nat))
       ))"
    unfolding turing_decidable_unfolded_into_TMC_yields_conditions by auto

  then obtain DB where
    w_DB: "(\<forall>nl. 
           (nl \<in> B \<longrightarrow> TMC_yields_num_res DB nl (1::nat))
         \<and> (nl \<notin> B \<longrightarrow> TMC_yields_num_res DB nl (0::nat))
       )" by blast

  (* third, define the composed machine DA = Red |+| DB that is able to decide A *)

  define DA where "DA = Red |+| DB"

  (* now, go for the main part of the proof *) 
  show "turing_decidable A"
    unfolding turing_decidable_unfolded_into_TMC_yields_conditions
  proof -
    have "\<forall>nl. (nl \<in> A \<longrightarrow> TMC_yields_num_res DA nl (1::nat)) \<and>
                 (nl \<notin> A \<longrightarrow> TMC_yields_num_res DA nl (0::nat))"
    proof (rule allI)
      fix nl
      show "(nl \<in> A \<longrightarrow> TMC_yields_num_res DA nl (1::nat)) \<and>
              (nl \<notin> A \<longrightarrow> TMC_yields_num_res DA nl (0::nat))"
      proof
        show "nl \<in> A \<longrightarrow> TMC_yields_num_res DA nl (1::nat)"
        proof
          assume "nl \<in> A" 
          from \<open>nl \<in> A\<close> and w_RedTM
          obtain ml where w_ml: "composable_tm0 Red \<and> TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B)"
            by blast  
          with \<open>nl \<in> A\<close> w_DB have "TMC_yields_num_res (Red |+| DB) nl  (1::nat)"
            using TMC_yields_num_res_Hoare_plus_halt by auto
          then show "TMC_yields_num_res DA nl 1"
            using DA_def by auto
        qed
      next
        show "nl \<notin> A \<longrightarrow>  TMC_yields_num_res DA nl 0"
        proof
          assume "nl \<notin> A"
          from \<open>nl \<notin> A\<close> and w_RedTM
          obtain ml where w_ml: "composable_tm0 Red \<and> TMC_yields_num_list_res Red nl ml \<and> (nl \<in> A \<longleftrightarrow> ml \<in> B)"
            by blast
          with \<open>nl \<notin> A\<close> w_DB have "TMC_yields_num_res (Red |+| DB) nl  (0::nat)"
            using TMC_yields_num_res_Hoare_plus_halt by auto
          then show "TMC_yields_num_res DA nl 0"
            using DA_def by auto
        qed
      qed
    qed
    then show "\<exists>D. \<forall>nl. (nl \<in> A \<longrightarrow> TMC_yields_num_res D nl 1) \<and> (nl \<notin> A \<longrightarrow> TMC_yields_num_res D nl 0)"
      by auto
  qed
qed

(* The corollary about obtaining undecidability from reducibility *)

corollary turing_reducible_AB_and_non_decA_imp_non_decB:
  "\<lbrakk>turing_reducible A B; \<not> turing_decidable A \<rbrakk> \<Longrightarrow> \<not>turing_decidable B"
  using turing_reducible_AB_and_decB_imp_decA 
  by blast

end
