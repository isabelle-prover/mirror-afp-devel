(* Title: thys/TuringDecidable.thy
   Author: Franz Regensburger (FABR) 02/2022
 *)

section \<open>Turing Decidability\<close>

theory TuringDecidable
  imports
    OneStrokeTM
    Turing_HaltingConditions
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

subsection \<open>Turing Decidable Sets and Relations of natural numbers\<close>

text \<open>We use lists of natural numbers in order to model tuples of
 arity @{term k} of natural numbers,
 where @{term "0 \<le> (k::nat)"}. 
\<close>

(*
 For a relation R of @\<lbrace>term k\<rbrace>-ary tuples use a set nls of nat lists,
 where each of its elements nl (which is a nat list) has length k.
    
     (n1, ... , nk) \<in> R \<longleftrightarrow> [<[n1, ... , nk]>] \<in> nls .
  
 For a plain set of natural numbers S simply use a set of singleton nat lists nls
 where

      n \<in> S \<longleftrightarrow> [<n>] \<in> nls.
*)

text \<open>Now, we define the notion of {\em Turing Decidable Sets and Relations}.
In our definition, we directly relate decidability of sets and relations to Turing machines
and do not adhere to the formal concept of a characteristic function.

However, the notion of a characteristic function is introduced in the theory about Turing
computable functions.
\<close>

definition turing_decidable :: "(nat list) set \<Rightarrow> bool"
  where
    "turing_decidable nls \<equiv> (\<exists>D. (\<forall>nl. 
         (nl \<in> nls \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk\<up> l))\<rbrace>)
       \<and> (nl \<notin> nls \<longrightarrow> \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk\<up> l))\<rbrace>)
     ))"

(* This is for documentation and explanation: turing_decidable_unfolded_into_TMC_yields_conditions *)

lemma turing_decidable_unfolded_into_TMC_yields_conditions:
"turing_decidable nls \<equiv> (\<exists>D. (\<forall>nl. 
         (nl \<in> nls \<longrightarrow> TMC_yields_num_res D nl (1::nat) )
       \<and> (nl \<notin> nls \<longrightarrow> TMC_yields_num_res D nl (0::nat) )
     ))"
  unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
  by (simp add: turing_decidable_def)

(* --------------------------------------------------------------------------------------------- *)

subsection \<open>Examples for decidable sets of natural numbers\<close>

text \<open>Using the machine OneStrokeTM as a decider
we are able to proof the decidability of the empty set.
Moreover, in the theory about Halting Problems, we will show that there are undecidable sets as well.
Thus, the notion of Turing Decidability is not a trivial concept.
\<close>

lemma turing_decidable_empty_set_iff:
  "turing_decidable {} = (\<exists>D. \<forall>(nl:: nat list).
        \<lbrace>(\<lambda>tap. tap = ([], <nl>))\<rbrace> D \<lbrace>(\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk \<up>l))\<rbrace>)"
  unfolding turing_decidable_def
  by (simp add: tape_of_nat_def)

theorem turing_decidable_empty_set: "turing_decidable {}"
  by (rule turing_decidable_empty_set_iff[THEN iffD2])
     (blast intro: tm_onestroke_total_correctness)

(* For demo in classes *)
(*
lemma tm_onestroke_total_correctness':
  "\<forall>nl. TMC_yields_num_res tm_onestroke nl (0::nat)"
  unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
  using tm_onestroke_total_correctness by (simp add: tape_of_nat_def)

theorem turing_decidable_empty_set':
  "(\<forall>nl. 
             (nl \<in> {} \<longrightarrow> TMC_yields_num_res tm_onestroke nl (1::nat) )
           \<and> (nl \<notin> {} \<longrightarrow> TMC_yields_num_res tm_onestroke nl (0::nat) )
         )"
  unfolding TMC_yields_num_res_unfolded_into_Hoare_halt
proof -
  show "\<forall>nl. (nl \<in> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>) \<and>
               (nl \<notin> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>)"
  proof
    fix nl:: "nat list"
    show "(nl \<in> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>) \<and>
          (nl \<notin> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>)"
    proof
      show "nl \<in> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>"
      proof
        assume "nl \<in> {}" (* nothing can ever be an element of the empty set {}, thus contradiction *)
        then have False by auto
        then show "\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @ Bk \<up> l)\<rbrace>" by auto
      qed
    next
      show "nl \<notin> {} \<longrightarrow> \<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>"
      proof
        assume "nl \<notin> {}"
        have "\<forall>nl.\<lbrace>\<lambda>tap. tap = ([], <nl::nat list>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>"
          using TMC_yields_num_res_unfolded_into_Hoare_halt tm_onestroke_total_correctness' by blast
        then show "\<lbrace>\<lambda>tap. tap = ([], <nl>)\<rbrace> tm_onestroke \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @ Bk \<up> l)\<rbrace>" by auto
      qed
    qed
  qed
qed

corollary "turing_decidable {}"
  unfolding turing_decidable_unfolded_into_TMC_yields_conditions
  using turing_decidable_empty_set' by auto
*)

(* ---------------------------------------------------- *)
(* ENHANCE: add a means for turing_semi_decidable       *)
(* ---------------------------------------------------- *)

(* ---------------------------------------------------- *)
(* ENHANCE: add a means for dove-tailing                *)
(* ---------------------------------------------------- *)

(* ---------------------------------------------------- *)
(* ENHANCE: prove advanced theorems about decidability  *)
(* ---------------------------------------------------- *)
(* - Step counter theorem ;aka (s,m,n) theorem          *)
(* - Rice's theorem for Turing Machines                 *)
(* ---------------------------------------------------- *)

end
