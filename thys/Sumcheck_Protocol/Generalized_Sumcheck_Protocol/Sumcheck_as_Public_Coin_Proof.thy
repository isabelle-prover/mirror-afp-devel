(*******************************************************************************

  Project: Sumcheck Protocol

  Authors: Azucena Garvia Bosshard <zucegb@gmail.com>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
           Jonathan Bootle, IBM Research Europe <jbt@zurich.ibm.com>

*******************************************************************************)

section \<open>Sumcheck Protocol as Public-coin Proof\<close>

theory Sumcheck_as_Public_Coin_Proof
  imports 
     Completeness_Proof 
     Soundness_Proof 
begin


context multi_variate_polynomial begin

subsection \<open>Property-related definitions\<close>

fun sc_sound_err :: "('p, 'a, 'b) sc_inst \<Rightarrow> real" where
  "sc_sound_err (H, p, v) = real (arity p) * real (deg p) / real (CARD('a))"

fun sc_compl_assm where
  "sc_compl_assm vs ps (H, p, v) xs \<longleftrightarrow> 
     set xs = vars p \<and> distinct xs \<and> H \<noteq> {}"

fun sc_sound_assm where
  "sc_sound_assm vs ps (H, p, v) xs \<longleftrightarrow> 
     set xs = vars p \<and> distinct xs \<and> H \<noteq> {}"


subsection \<open>Public coin proof locale interpretation\<close>

sublocale 
  scp: public_coin_proof_strong_props 
        sc_ver0 sc_ver1 Sumcheck honest_prover sc_sound_err sc_compl_assm sc_sound_assm
proof 
  fix I :: "('p, 'a, 'b) sc_inst" and 
      vs :: unit and ps :: unit and 
      rm :: "('v \<times> 'a) list" and r :: 'a  
  assume "I \<in> Sumcheck" and "sc_compl_assm vs ps I (map fst rm)" 
  then show "sc.prove vs honest_prover ps I r rm"
    by (cases I) (simp add: prove_sc_eq_sumcheck completeness)
next
  fix I :: "('p, 'a, 'b) sc_inst" and 
      vs :: unit and ps :: 'ps and 
      r :: 'a and rs :: "'a list" and xs :: "'v list" and pr
  assume "I \<notin> Sumcheck" and "sc_sound_assm vs ps I xs"
  then show 
    "measure_pmf.prob 
       (pmf_of_set (tuples UNIV (length xs))) 
       {rs. sc.prove vs pr ps I r (zip xs rs)}
     \<le> sc_sound_err I"
  proof (cases I)
    case (fields H p v)
    have "length xs = arity p" using \<open>sc_sound_assm vs ps I xs\<close> fields
      by (auto simp add: arity_def distinct_card dest: sym)
    then show ?thesis using \<open>I \<notin> Sumcheck\<close> \<open>sc_sound_assm vs ps I xs\<close> fields
      by (auto simp add: prove_sc_eq_sumcheck intro: soundness)
  qed
qed


end \<comment> \<open>context @{locale "multi_variate_polynomial"}\<close>


end
