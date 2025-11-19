chapter\<open>Löb's Theorem\<close>

(*  Title:       Löb's Theorem
    Author:      Janis Bailitis, 2024
    Maintainer:  Janis Bailitis
*)

section "Preliminaries"

text\<open>This formalisation relies on Paulson's formalisation of Gödel's incompleteness theorems.\<close>

theory Loebs_Theorem
  imports Goedel_II Goedel_I Quote 
begin

section "Needed Facts on HF and Paulson's Provability Predicate"

text\<open>The formalised proof of Löb's theorem below relies on a few facts about the deduction rules
of HF set theory and Paulson's provability predicate \<^cite>\<open>paulson_companion\<close>.
All these facts follow readily from results that Paulson already formalised.\<close>

text\<open>The modus ponens rule for the provability predicate.\<close>

lemma PfP_inner_ModPon: assumes "ground_fm \<alpha>" "ground_fm \<beta>" shows "{} \<turnstile> PfP \<guillemotleft>\<alpha> IMP \<beta>\<guillemotright> IMP PfP \<guillemotleft>\<alpha>\<guillemotright> IMP PfP \<guillemotleft>\<beta>\<guillemotright>"
proof -
  have "{} \<turnstile> \<alpha> IMP (\<alpha> IMP \<beta>) IMP \<beta>"
    by blast
  then have aux: "{} \<turnstile> PfP \<guillemotleft>\<alpha>\<guillemotright> IMP PfP \<guillemotleft>\<alpha> IMP \<beta>\<guillemotright> IMP PfP \<guillemotleft>\<beta>\<guillemotright>"
    using assms
    using qp0.quote_all_MonPon2_PfP_ssubst
    by (auto simp: qp0.quote_all_MonPon2_PfP_ssubst ground_fm_aux_def) (** This is fully inspired by a proof of Paulson *)
  then have "{ PfP \<guillemotleft>\<alpha> IMP \<beta>\<guillemotright>,  PfP \<guillemotleft>\<alpha>\<guillemotright> } \<turnstile>  PfP \<guillemotleft>\<beta>\<guillemotright>"
    by (metis anti_deduction)
  then have "{ PfP \<guillemotleft>\<alpha>\<guillemotright>, PfP \<guillemotleft>\<alpha> IMP \<beta>\<guillemotright> } \<turnstile>  PfP \<guillemotleft>\<beta>\<guillemotright>"
     by (metis rotate2)
  thus ?thesis
     by (metis Imp_I)
 qed

text\<open>Slight reformulation of @{thm PfP_inner_ModPon}
where one of the implications is on the meta level.\<close>

lemma PfP_distr: assumes "ground_fm \<alpha>" "ground_fm \<beta>" "{} \<turnstile> PfP \<guillemotleft>\<alpha> IMP \<beta>\<guillemotright>" shows "{} \<turnstile> PfP \<guillemotleft>\<alpha>\<guillemotright> IMP PfP \<guillemotleft>\<beta>\<guillemotright>" 
proof -
  have "{} \<turnstile> \<alpha> IMP \<beta>"
    using assms
    by (metis proved_iff_proved_PfP)
  thus ?thesis
    using assms
    by (metis Imp_I MonPon_PfP_implies_PfP)
qed

text\<open>The provability predicate also satisfies internal necessitation.\<close>

lemma Int_nec: assumes "ground_fm \<delta>" shows "{} \<turnstile> PfP \<guillemotleft>\<delta>\<guillemotright> IMP PfP \<guillemotleft>PfP \<guillemotleft>\<delta>\<guillemotright>\<guillemotright>"
  by (auto simp: Provability ground_fm_aux_def supp_conv_fresh)

text\<open>Fact on HF set theory stating that implications are transitive. Follows readily from the 
deduction theorem (@{thm anti_deduction}).\<close>

lemma Imp_trans: assumes "{} \<turnstile> \<alpha> IMP \<beta>" "{} \<turnstile> \<beta> IMP \<gamma>" shows "{} \<turnstile> \<alpha> IMP \<gamma>"
proof -
  have "{\<alpha>} \<turnstile> \<beta>" 
    using assms(1)
    by (metis anti_deduction)
  moreover have "{\<beta>} \<turnstile> \<gamma>"
    using assms(2)
    by (metis anti_deduction)
  ultimately have "{\<alpha>} \<turnstile> \<gamma>"
    by (metis rcut1)
  thus ?thesis
    by (metis Imp_I)
qed

text\<open>Specialisation of the S deduction rule (@{thm S}) for empty contexts.\<close>

lemma S': assumes "{} \<turnstile> \<alpha> IMP \<beta> IMP \<gamma>" "{} \<turnstile> \<alpha> IMP \<beta>" shows "{} \<turnstile> \<alpha> IMP \<gamma>"
proof -
  have "{} \<union> {} \<turnstile> \<alpha> IMP \<gamma>"
    using assms
    by (metis S)
  thus ?thesis
    by simp
qed

section "Proof of Löb's Theorem"

text\<open>The proof of Löb's theorem for HF set theory and Paulson's provability predicate, roughly
following the paper version by Smith \<^cite>\<open>smith2020\<close>. The key ideas in the proof are due to
Löb \<^cite>\<open>loeb1955\<close> himself, but Smith gives a much more structured version.\<close>

theorem Loeb: assumes "ground_fm \<alpha>" "{} \<turnstile> PfP \<guillemotleft>\<alpha>\<guillemotright> IMP \<alpha>" shows "{} \<turnstile> \<alpha>"
proof -
  obtain k::name
    where atoms: "atom k \<sharp> \<alpha>"
    by (metis obtain_fresh)
  obtain \<delta> where del: "{} \<turnstile> \<delta> IFF ((PfP (Var k)) IMP \<alpha>)(k::=\<guillemotleft>\<delta>\<guillemotright>)"
             and suppd: "supp \<delta> = supp ((PfP (Var k)) IMP \<alpha>) - {atom k}"
    by (metis diagonal)
  then have "{} \<turnstile> \<delta> IFF ((PfP (Var k))(k::=\<guillemotleft>\<delta>\<guillemotright>) IMP \<alpha>(k::=\<guillemotleft>\<delta>\<guillemotright>))"
    by (metis SyntaxN.Neg SyntaxN.Disj)
  moreover have "atom k \<sharp> \<alpha>"
    using assms
    by simp
  ultimately have "{} \<turnstile> \<delta> IFF ((PfP (Var k))(k::=\<guillemotleft>\<delta>\<guillemotright>) IMP \<alpha>)"
    by (metis forget_subst_fm)
  then have diag: "{} \<turnstile> \<delta> IFF ((PfP \<guillemotleft>\<delta>\<guillemotright>) IMP \<alpha>)"
    by simp
  then have del_supp: "ground_fm \<delta>"
    using assms
    using suppd
    by (auto simp: ground_fm_aux_def supp_conv_fresh) 
  then have imp_supp: "ground_fm  (PfP \<guillemotleft>\<delta>\<guillemotright> IMP \<alpha>)"
    using assms
    using suppd
    by (auto simp: ground_fm_aux_def supp_conv_fresh) 
  then have prf_del_supp: "ground_fm (PfP \<guillemotleft>\<delta>\<guillemotright>)"
    using suppd
    by (auto simp: ground_fm_aux_def supp_conv_fresh) 
  then have "{} \<turnstile> \<delta> IMP ((PfP \<guillemotleft>\<delta>\<guillemotright>) IMP \<alpha>)"
    by (metis Conj_E2 Iff_def Iff_sym diag) 
  then have "{} \<turnstile> PfP \<guillemotleft>\<delta> IMP ((PfP \<guillemotleft>\<delta>\<guillemotright>) IMP \<alpha>)\<guillemotright>"
    by (metis  proved_iff_proved_PfP)
  then have "{} \<turnstile> PfP \<guillemotleft>\<delta>\<guillemotright> IMP (PfP \<guillemotleft>PfP \<guillemotleft>\<delta>\<guillemotright> IMP \<alpha>\<guillemotright>)"
    using imp_supp
    using del_supp
    by (metis PfP_distr)
  moreover have "{} \<turnstile> PfP \<guillemotleft>PfP \<guillemotleft>\<delta>\<guillemotright> IMP \<alpha>\<guillemotright> IMP PfP \<guillemotleft>PfP \<guillemotleft>\<delta>\<guillemotright>\<guillemotright> IMP PfP \<guillemotleft>\<alpha>\<guillemotright>"
    using assms(1)
    using prf_del_supp
    by (metis PfP_inner_ModPon)
  ultimately have "{} \<turnstile>  PfP \<guillemotleft>\<delta>\<guillemotright> IMP PfP \<guillemotleft>PfP \<guillemotleft>\<delta>\<guillemotright>\<guillemotright> IMP PfP \<guillemotleft>\<alpha>\<guillemotright>"
    by (metis Imp_trans)
  then have "{} \<turnstile> PfP \<guillemotleft>\<delta>\<guillemotright> IMP PfP \<guillemotleft>\<alpha>\<guillemotright>"
    using del_supp
    by (metis Int_nec S')
  then have imp_a: "{} \<turnstile> PfP \<guillemotleft>\<delta>\<guillemotright> IMP \<alpha>"
    using assms(2)
    by (metis Imp_trans)
  then have "{} \<turnstile> PfP \<guillemotleft>\<delta>\<guillemotright>"
    using diag
    by (metis Iff_MP2_same proved_iff_proved_PfP)
  thus ?thesis
    using imp_a
    by (metis MP_same)
qed
  
end