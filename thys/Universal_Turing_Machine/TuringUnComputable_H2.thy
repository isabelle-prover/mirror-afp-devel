(* Title: thys/TuringUnComputable_H2.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Further contributions and enhancements by Franz Regensburger (FABR) 02/2022 :

   - Splitted and reordered theory file Uncomputable.thy into
     several smaller theory files.

   - Completed the proof of the undecidability of the Halting problem H2.

     The original version by Jian Xu, Xingyuan Zhang, and Christian Urban
     only formalizes a weaker version of the undecidability result.
     Their formalization just shows that the set H2 is not
     decidable by any composable (aka well-formed) Turing machine.

     However, the set H2 might be decidable by some none composable TM.
     We close this gap in the following and show that no Turing machine,
     may it be composable or not, is able to decide the set H2.

   - Corrected the presentation of the theory.

     The entire hierarchy of theories formalized in HOL is based on the
     principle of Conservative Theory Extension.

     One major law of this principle is that for every locale there must be at least
     one instance proof in order to ensure that the locale is inhabited (has models).

     The original version of the theory TuringUnComputable_H2 intentionally used
     locale axioms that have no model.
     There is not a single valid reason to justify this miss-use of the locale concept!

     In our version, we present the theory in accordance with the principle of
     Conservative Theory Extension.
 *)

subsection \<open>Existence of an uncomputable Function\<close>

theory TuringUnComputable_H2
  imports
     CopyTM
     DitherTM

begin

(*
declare adjust.simps[simp del]

declare seq_tm.simps [simp del] 
declare shift.simps[simp del]
declare composable_tm.simps[simp del]
declare step.simps[simp del]
declare steps.simps[simp del]
*)

subsubsection \<open>Undecidability of the General Halting Problem H, Variant 2, revised version\<close>

text \<open>
  This variant of the decision problem H is discussed in the book
  Computability and Logic by Boolos, Burgess and Jeffrey~\<^cite>\<open>"Boolos07"\<close> in chapter 4.

  The proof makes use of the TMs @{term "tm_copy"} and @{term "tm_dither"}.
  In \<^cite>\<open>"Boolos07"\<close>, the machines are called {\em copy} and {\em dither}.
\<close>

fun dummy_code :: "tprog0 \<Rightarrow> nat"  (* the witness for the instantiation of class hph2 *)
  where "dummy_code tp = 0"

locale hph2 = 

  (* Interestingly, the detailed definition of the coding function @{text "code"}
     for Turing machines does not affect the final result.

     In the proof there is no need to appeal on properties of the coding function
     like e.g. injectivity! *)

fixes code :: "instr list \<Rightarrow> nat" 

(* FABR Note about the old formalization:

    * The first axiom states that the Turing machine H is well-formed (composable).
    * However, this manifests a principle weakness of the old modelling of the locale!
    *
    * Due to this locale axiom, we only prove that there exists no composable TM H
    * that is able to decide the Halting problem 'TMC_has_num_res M ns'
    *
    * See theories ComposableTMs.thy and HaltingProblems_K_H.thy for a fix by FABR.

    These are the old locale axioms, which we do not use any longer.

    assumes h_composable[intro]: "composable_tm0 H"

    and h_case:
    "\<And> M ns.  TMC_has_num_res M ns
        \<Longrightarrow> \<lbrace>(\<lambda>tap. tap = ([Bk], <(code M, ns)>))\<rbrace> H \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>))\<rbrace>"

    and nh_case:
    "\<And> M ns. \<not>  TMC_has_num_res M ns 
     \<Longrightarrow> \<lbrace>(\<lambda>tap. tap = ([Bk], <(code M, ns)>))\<rbrace> H \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>))\<rbrace>"

    An additional weakness of these locale axioms are the post-conditions used:

    \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <0::nat>))\<rbrace>"
    \<lbrace>(\<lambda>tap. \<exists>k. tap = (Bk \<up> k, <1::nat>))\<rbrace>"

    These need to be relaxed into: 

    \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <0::nat> @Bk\<up>l)\<rbrace>)
    \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, <1::nat> @Bk\<up>l)\<rbrace>)

    Otherwise, there might simply be no TM that is able to compute just the output
    <0::nat> or <1:nat> without any further trailing blanks.

*)

begin

text \<open>The function @{term dummy_code} is a witness that the locale hph2 is inhabited.

Note: there just has to be some function with the correct type since we did not
specify any axioms for the locale. The behaviour of the instance of the locale
function code does not matter at all.

This detail differs from the locale hpk, where a locale axiom specifies that the
coding function has to be injective.

Obviously, the entire logical argument of the undecidability proof H2
relies on the combination of the machines @{term "tm_copy"} and @{term "tm_dither"}.
\<close>
 
interpretation dummy_code: hph2 "dummy_code :: tprog0 \<Rightarrow> nat"
proof unfold_locales
qed

text \<open>The next lemma plays a crucial role in the proof by contradiction.
Due to our general results about trailing blanks on the left tape,
we are able to compensate for the additional blank, which is a mandatory
by-product of the @{term "tm_copy"}.
\<close>

lemma add_single_BK_to_left_tape:
  "\<lbrace>\<lambda>tap. tap = ([]  , <(m::nat, m)> ) \<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, r' @Bk\<up>l )\<rbrace>
  \<Longrightarrow>
   \<lbrace>\<lambda>tap. tap = ([Bk], <(m     , m)> ) \<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, r' @Bk\<up>l )\<rbrace>"
proof -
  assume    "\<lbrace>\<lambda>tap. tap = ([], <(m::nat, m)> ) \<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, r' @Bk\<up>l)\<rbrace>"
  then have  "\<forall>z.\<lbrace>\<lambda>tap. tap = (Bk \<up> z, <(m::nat, m)> ) \<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, r' @Bk\<up>l)\<rbrace>"
    using Hoare_halt_add_Bks_left_tape_L1 Hoare_halt_add_Bks_left_tape  by blast
  then have  "\<lbrace>\<lambda>tap. tap = (Bk \<up> 1, <(m::nat, m)> ) \<rbrace> p \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, r' @Bk\<up>l)\<rbrace>"
    by blast
  then show ?thesis
    by (simp add: Hoare_haltE Hoare_haltI)
qed
 
text \<open>Definition of the General Halting Problem H2.\<close>

definition H2 :: "((instr list) \<times> (nat list)) set"  (* behold the type of the set *)
  where
     "H2 \<equiv> {(tm,nl). TMC_has_num_res tm nl }"

text \<open>No Turing Machine is able to decide the General Halting Problem H2.\<close>

lemma existence_of_decider_H2D0_for_H2_imp_False:
  assumes "\<exists>H2D0'. (\<forall>nl (tm::instr list).
          ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @ Bk\<up>l)\<rbrace>)
       \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"
  shows False
proof -
  from assms obtain H2D0' where
    w_H2D0': "(\<forall>nl (tm::instr list).
          ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>)
       \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"
    by blast

(* first, create a composable version of the arbitrary and thus potentially non-composable machine H2D0' *)

  then have "composable_tm0 (mk_composable0 H2D0') \<and> (\<forall>nl (tm::instr list).
          ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> mk_composable0 H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>)
       \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> mk_composable0 H2D0' \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"

    by (auto simp add: Hoare_halt_tm_impl_Hoare_halt_mk_composable0_cell_list composable_tm0_mk_composable0 )

  then have "\<exists>H2D0. composable_tm0 H2D0 \<and> (\<forall>nl (tm::instr list).
          ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace>  H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>)
       \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"
    by blast

(* here we obtain the composable variant H2D0 of  H2D0' *)

  then obtain H2D0 where w_H2D0: "composable_tm0 H2D0 \<and> (\<forall>nl (tm::instr list).
          ((tm,nl) \<in> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace>  H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>)
       \<and>  ((tm,nl) \<notin> H2 \<longrightarrow>\<lbrace>\<lambda>tap. tap = ([], <(code tm, nl)>)\<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>) )"
    by blast

(* define the culprit tm_contra from the diagonal by using tm_copy and tm_dither *)

  define tm_contra where "tm_contra = (tm_copy |+| H2D0 |+| tm_dither)"

  from w_H2D0 have H_composable: "composable_tm0 (tm_copy |+| H2D0)" by auto

(* the stage is set: now, we derive the contradiction *)

  show False
  proof (cases "(tm_contra, [code tm_contra]) \<in> H2")

    case True  
    then have "(tm_contra, [code tm_contra]) \<in> H2" .

    then have inH2: "TMC_has_num_res tm_contra [code tm_contra]"
      by (auto simp add: H2_def)

    show False  (* (tm_contra, [code tm_contra]) \<in> H2  \<Longrightarrow> (tm_contra, [code tm_contra]) \<notin> H2 *)
    proof -

      (* assertions *)
      define P1 where "P1 \<equiv> \<lambda>tap. tap = ([]::cell list, <code tm_contra>)"
      define P2 where "P2 \<equiv> \<lambda>tap. tap = ([Bk]::cell list, <(code tm_contra, code tm_contra)>)"
      define Q3 where "Q3 \<equiv> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)"

(* the play book for derivation of the contradiction,
   for the case: (tm_contra, [code tm_contra]) \<in> H2

         \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H2D0 \<lbrace>Q3\<rbrace>
         ---------------------------------
         first: \<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>Q3\<rbrace>    second: \<lbrace>Q3\<rbrace> tm_dither loops
         -------------------------------------------------------------------
                        \<lbrace>P1\<rbrace> tm_contra loops
*)

(* from \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H2D0 \<lbrace>Q3\<rbrace>   show  first: \<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>Q3\<rbrace> *)

      have first: "\<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>Q3\<rbrace>" 
      proof (cases rule: Hoare_plus_halt)
        case A_halt (* of tm_copy *)
        show "\<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>" unfolding P1_def P2_def tape_of_nat_def
          by (rule tm_copy_correct)
      next
        case B_halt (* of H2D0 *)
        from \<open>(tm_contra, [code tm_contra]) \<in> H2\<close> and w_H2D0
        have      "\<lbrace>\<lambda>tap. tap = ([], <(code tm_contra, [code tm_contra])> ) \<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>"          
          by auto
        then have "\<lbrace>\<lambda>tap. tap = ([], <(code tm_contra, code tm_contra)  > ) \<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc] @Bk\<up>l)\<rbrace>"
          by (simp add: Hoare_haltE Hoare_haltI tape_of_list_def tape_of_prod_def)

        then show "\<lbrace>P2\<rbrace> H2D0 \<lbrace>Q3\<rbrace>"
          unfolding P2_def Q3_def
          using add_single_BK_to_left_tape
          by blast
      next
        show "composable_tm0 tm_copy" by auto
      qed

(* second: \<lbrace>P3\<rbrace> tm_dither loops *)

      have second: "\<lbrace>Q3\<rbrace> tm_dither \<up>" unfolding Q3_def
        using tm_dither_loops''
        by (simp add: tape_of_nat_def )

(* from first and second show  \<lbrace>P1\<rbrace> tm_contra loops *)

      have "\<lbrace>P1\<rbrace> tm_contra \<up>" 
        unfolding tm_contra_def
        by (rule Hoare_plus_unhalt[OF first second H_composable])

(* from \<lbrace>P1\<rbrace> tm_contra \<up>   show  \<not>TMC_has_num_res tm_contra [code tm_contra] *)

      then have "\<not>TMC_has_num_res tm_contra [code tm_contra]"
        unfolding P1_def
        
        by (metis (mono_tags) Hoare_halt_impl_not_Hoare_unhalt
                  TMC_has_num_res_def inH2 tape_of_list_def tape_of_nat_list.simps(2))

(* thus have contradiction *)

      with inH2 show False by auto
    qed

  next

    case False
    then have "(tm_contra, [code tm_contra]) \<notin> H2" .
    then have not_inH2: "\<not>TMC_has_num_res tm_contra [code tm_contra]"
      by (auto simp add: H2_def)

    show False  (* (tm_contra, [code tm_contra]) \<notin> H2 \<Longrightarrow> (tm_contra, [code tm_contra]) \<in> H2 *)
    proof -

      (* assertions *)
      define P1 where "P1 \<equiv> \<lambda>tap. tap = ([]::cell list, <code tm_contra>)"
      define P2 where "P2 \<equiv> \<lambda>tap. tap = ([Bk], <(code tm_contra, code tm_contra)>)"
      define P3 where "P3 \<equiv> \<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l )"

(* the play book for derivation of the contradiction,
   for the case: (tm_contra, [code tm_contra]) \<notin> H2

         \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H2D0 \<lbrace>P3\<rbrace> 
         --------------------------------
         first: \<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>P3\<rbrace>   second: \<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace>
         ----------------------------------------------------------------
                           \<lbrace>P1\<rbrace> tm_contra \<lbrace>P3\<rbrace>
*)

(* from \<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>  \<lbrace>P2\<rbrace> H2D0 \<lbrace>P3\<rbrace>     show    first: \<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>P3\<rbrace> *)

      have first: "\<lbrace>P1\<rbrace> (tm_copy |+| H2D0) \<lbrace>P3\<rbrace>"
      proof (cases rule: Hoare_plus_halt)
        case A_halt (* of tm_copy *)
        show "\<lbrace>P1\<rbrace> tm_copy \<lbrace>P2\<rbrace>" unfolding P1_def P2_def tape_of_nat_def
          by (rule tm_copy_correct)
      next
        case B_halt (* of H2D0 *)
        from \<open>(tm_contra, [code tm_contra]) \<notin> H2\<close> and w_H2D0
        have      "\<lbrace>\<lambda>tap. tap = ([], <(code tm_contra, [code tm_contra])> ) \<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>"            
          by auto
        then have "\<lbrace>\<lambda>tap. tap = ([], <(code tm_contra, code tm_contra)  > ) \<rbrace> H2D0 \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>"
          by (simp add: Hoare_haltE Hoare_haltI tape_of_list_def tape_of_prod_def)

        then show "\<lbrace>P2\<rbrace> H2D0 \<lbrace>P3\<rbrace>"
          unfolding P2_def P3_def
          by (rule add_single_BK_to_left_tape)
      next
        show "composable_tm0 tm_copy" by simp
      qed

(* second: \<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace> *)

      from tm_dither_halts
      have "\<lbrace>\<lambda>tap. tap = ([], [Oc, Oc])\<rbrace> tm_dither \<lbrace>\<lambda>tap. \<exists>k l. tap = (Bk \<up> k, [Oc, Oc] @Bk\<up>l)\<rbrace>"
      proof -
        have "\<forall>n. \<exists>l. steps0 (1, Bk \<up> n, [Oc, Oc]) tm_dither (Suc 1) = (0, Bk \<up> n, [Oc, Oc] @Bk\<up>l)"
          by (metis One_nat_def tm_dither_halts_aux Suc_1 append.right_neutral replicate.simps(1) )
        then show ?thesis
          using Hoare_halt_add_Bks_left_tape_L2 Hoare_halt_del_Bks_left_tape by blast          
      qed

      then have second: "\<lbrace>P3\<rbrace> tm_dither \<lbrace>P3\<rbrace>" unfolding P3_def       
      proof -
        have "Oc # [Oc] = [Oc, Oc]"
          using One_nat_def replicate_Suc tape_of_nat_def by fastforce
        then show "\<lbrace>\<lambda>p. \<exists>n na. p = (Bk \<up> n, [Oc, Oc] @ Bk \<up> na)\<rbrace> tm_dither \<lbrace>\<lambda>p. \<exists>n na. p = (Bk \<up> n, [Oc, Oc] @ Bk \<up> na)\<rbrace>"
          using tm_dither_halts'' by presburger
      qed

(* from first and second show  \<lbrace>P1\<rbrace> tm_contra \<lbrace>P3\<rbrace> *)

      with first have "\<lbrace>P1\<rbrace> tm_contra \<lbrace>P3\<rbrace>"
        unfolding tm_contra_def
      proof (rule Hoare_plus_halt)
        from H_composable show "composable_tm0 (tm_copy |+| H2D0)" by auto
      qed

(* from  \<lbrace>P1\<rbrace> tm_contra \<lbrace>P3\<rbrace>    show    TMC_has_num_res tm_contra [code tm_contra] *)

      then have "TMC_has_num_res tm_contra [code tm_contra]" unfolding P1_def P3_def
        by (simp add: Hoare_haltE Hoare_haltI Hoare_halt_with_OcOc_imp_std_tap tape_of_list_def)

(* thus have contradiction *)

      with not_inH2
      show ?thesis by auto
    qed
  qed
qed

text \<open>Note: since we did not formalize the concept of Turing Computable Functions and
 Characteristic Functions of sets yet, we are (at the moment) not able to formalize the existence
 of an  uncomputable function, namely the characteristic function of the set H2.

 Another caveat is the fact that the set H2 has type @{typ "((instr list) \<times> (nat list)) set"}.
 This is in contrast to the classical formalization of decision problems, where the sets discussed
 only contain tuples respectively lists of natural numbers. 
  \<close>
end (* locale uncomputable *)

end

