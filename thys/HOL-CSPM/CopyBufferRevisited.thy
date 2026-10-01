theory CopyBufferRevisited
imports  "HOL-CSPM" "HOL-CSP.CopyBuffer"

begin

section\<open>Objective\<close>

text\<open>This theory contains a number of standard proof techniques for classical assertions
of the paradigmatic \<^verbatim>\<open>CopyBuffer\<close> example (arbitrary alphabet). The core of this example
has already been presented in the \<^theory>\<open>HOL-CSP\<close> session, here we add the missing proofs 
for the assertions \<^term>\<open>deadlock_free\<close> and  \<^term>\<open>lifelock_free\<close> known from FDR4 for CSPM.
The proof-style is deliberately optimized for readability and clear algebraic presentation 
rather than for brievity and automation.\<close>

section\<open>Deadlock-Freeness of COPY, SEND and REC\<close>

lemma deadlock_free_COPY : \<open>deadlock_free (COPY :: 'a channel process)\<close>
proof (rule deadlock_free_gen_n_coinduct[where A = \<open>range left \<union> range right\<close> and n = 1])
  show \<open>range left \<union> range right \<noteq> ({} :: 'a channel set)\<close> by blast
next
  fix x :: \<open>'a channel process\<close>
  assume hyp : \<open>x \<sqsubseteq>\<^sub>F\<^sub>D COPY\<close>
  have 1 : \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range right \<rightarrow> x\<close>
    by (rule Mndetprefix_FD_subset) simp_all
  have 2 : \<open>\<sqinter>a\<in>range right \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!v \<rightarrow> x\<close> for v
    apply (unfold write_def, rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{right v}\<close> \<open>range right\<close>]])
    by (simp_all add: Mndetprefix_FD_Mprefix Mprefix_singl)
  have ab : \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!v \<rightarrow> x\<close> for v
    using 1 2 trans_FD by blast
  have 3 : \<open>left\<^bold>?v \<rightarrow> \<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> x\<close>
    by (simp add: ab mono_read_FD)
  have 4 : \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range left \<rightarrow> X\<close> for X
    by (rule Mndetprefix_FD_subset) simp_all
  have 5 : \<open>\<sqinter>a\<in>range left \<rightarrow> X \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> X\<close> for X
    unfolding read_def by (subst K_record_comp) (fact Mndetprefix_FD_Mprefix)
  have 6 : \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> \<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x
              \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> x\<close> for v
    using 3 4[of \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x\<close>]
      5[of \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow> x\<close>] trans_FD by blast
  have 7 : \<open>left\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> COPY\<close> for v
    by (simp add: hyp mono_read_FD mono_write_FD)
  show \<open>\<sqinter>a\<in>(range left \<union> range right) \<rightarrow>
        ((\<lambda>X. \<sqinter>a\<in>(range left \<union> range right) \<rightarrow> X) ^^ 1) x \<sqsubseteq>\<^sub>F\<^sub>D COPY\<close>
    using 6 7 by simp (metis (mono_tags, lifting) COPY_rec trans_FD)
qed

text\<open>\<^const>\<open>SEND\<close> and \<^const>\<open>REC\<close> cycle over three steps instead of two, so we instantiate
\<open>deadlock_free_gen_n_coinduct\<close> at \<^term>\<open>n = (2::nat)\<close> this time, with the alphabet being
the whole set of events \<^const>\<open>SEND\<close> (resp.\ \<^const>\<open>REC\<close>) ever touches along its cycle.\<close>

lemma deadlock_free_SEND : \<open>deadlock_free (SEND :: 'a channel process)\<close>
proof (rule deadlock_free_gen_n_coinduct
         [where A = \<open>range left \<union> range mid \<union> {ack}\<close> and n = 2])
  show \<open>range left \<union> range mid \<union> {ack} \<noteq> ({} :: 'a channel set)\<close> by blast
next
  define A :: \<open>'a channel set\<close> where \<open>A \<equiv> range left \<union> range mid \<union> {ack}\<close>
  fix x :: \<open>'a channel process\<close>
  assume hyp : \<open>x \<sqsubseteq>\<^sub>F\<^sub>D SEND\<close>
  have step_ack : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D ack \<rightarrow> Z\<close> for Z
    apply (rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{ack}\<close> A]])
    by (simp_all add: A_def Mndetprefix_FD_Mprefix Mprefix_singl)
  have M1 : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range mid \<rightarrow> Z\<close> for Z
    by (rule Mndetprefix_FD_subset) (auto simp: A_def)
  have M2 : \<open>\<sqinter>a\<in>range mid \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>!v \<rightarrow> Z\<close> for Z v
    apply (unfold write_def, rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{mid v}\<close> \<open>range mid\<close>]])
    by (simp_all add: Mndetprefix_FD_Mprefix Mprefix_singl)
  have step_mid : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>!v \<rightarrow> Z\<close> for Z v 
    by (metis M1 M2 trans_FD)
  have L1 : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range left \<rightarrow> Z\<close> for Z
    by (rule Mndetprefix_FD_subset) (auto simp: A_def)
  have L2 : \<open>\<sqinter>a\<in>range left \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> Z\<close> for Z
    unfolding read_def by (subst K_record_comp) (fact Mndetprefix_FD_Mprefix)
  have step_left : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> Z\<close> for Z
    using L1 L2 trans_FD by blast
  have level2 : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>!v \<rightarrow> ack \<rightarrow> x\<close> for v
    using step_mid[of \<open>\<sqinter>a\<in>A \<rightarrow> x\<close> v] step_ack[of x] mono_write_FD trans_FD 
    by fast
  have level1 : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> mid\<^bold>!v \<rightarrow> ack \<rightarrow> x\<close> for v
    using step_left[of \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> x\<close>] level2 mono_read_FD trans_FD
    by (metis (no_types, lifting))
  have final : \<open>left\<^bold>?v \<rightarrow> mid\<^bold>!v \<rightarrow> ack \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?v \<rightarrow> mid\<^bold>!v \<rightarrow> ack \<rightarrow> SEND\<close> for v
    by (simp add: hyp mono_read_FD mono_write_FD mono_write0_FD)
  have conv : "2 = Suc(Suc 0)" by simp 
  show \<open>\<sqinter>a\<in>A \<rightarrow> ((\<lambda>X. \<sqinter>a\<in>A \<rightarrow> X) ^^ 2) x \<sqsubseteq>\<^sub>F\<^sub>D SEND\<close>
    apply(subst conv) (* why is this necessary ? *)
    using level1 final conv apply simp
    by (metis (mono_tags, lifting) SEND_rec dual_order.trans)
qed

text\<open>\<^const>\<open>REC\<close> mirrors \<^const>\<open>SEND\<close> exactly (read on \<^const>\<open>mid\<close>, write on \<^const>\<open>right\<close>,
then the fixed event \<^const>\<open>ack\<close>), so the same three-layer peeling argument applies. This time
each intermediate \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close>-fact is built by an explicit \<open>rule trans_FD[OF \<dots>]\<close> application
rather than handing several facts to \<open>blast\<close>/\<open>metis\<close> at once: the underlying monotonicity
lemmas (\<open>mono_read_FD\<close>, \<open>mono_write_FD\<close>) are themselves \<open>\<And>\<close>-quantified rules, and leaving
their instantiation to an unguided search over several such rules simultaneously is what made
the analogous \<^const>\<open>SEND\<close> proof slow above; fully applying each step explicitly keeps every
call a single, cheap, fully-determined unification.\<close>

lemma deadlock_free_REC : \<open>deadlock_free (REC :: 'a channel process)\<close>
proof (rule deadlock_free_gen_n_coinduct
         [where A = \<open>range mid \<union> range right \<union> {ack}\<close> and n = 2])
  show \<open>range mid \<union> range right \<union> {ack} \<noteq> ({} :: 'a channel set)\<close> by blast
next
  define A :: \<open>'a channel set\<close> where \<open>A \<equiv> range mid \<union> range right \<union> {ack}\<close>
  fix x :: \<open>'a channel process\<close>
  assume hyp : \<open>x \<sqsubseteq>\<^sub>F\<^sub>D REC\<close>
  have step_ack : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D ack \<rightarrow> Z\<close> for Z
    apply (rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{ack}\<close> A]])
    by (simp_all add: A_def Mndetprefix_FD_Mprefix Mprefix_singl)
  have R1 : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range right \<rightarrow> Z\<close> for Z
    by (rule Mndetprefix_FD_subset) (auto simp: A_def)
  have R2 : \<open>\<sqinter>a\<in>range right \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!v \<rightarrow> Z\<close> for Z v
    apply (unfold write_def, rule trans_FD[OF Mndetprefix_FD_subset[of \<open>{right v}\<close> \<open>range right\<close>]])
    by (simp_all add: Mndetprefix_FD_Mprefix Mprefix_singl)
  have step_right : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!v \<rightarrow> Z\<close> for Z v
    by (rule trans_FD[OF R1 R2])
  have M1 : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D \<sqinter>a\<in>range mid \<rightarrow> Z\<close> for Z
    by (rule Mndetprefix_FD_subset) (auto simp: A_def)
  have M2 : \<open>\<sqinter>a\<in>range mid \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>?v \<rightarrow> Z\<close> for Z
    unfolding read_def by (subst K_record_comp) (fact Mndetprefix_FD_Mprefix)
  have step_mid : \<open>\<sqinter>a\<in>A \<rightarrow> Z \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>?v \<rightarrow> Z\<close> for Z
    by (rule trans_FD[OF M1 M2])
  have level2 : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D right\<^bold>!v \<rightarrow> ack \<rightarrow> x\<close> for v
    by (rule trans_FD[OF step_right[of \<open>\<sqinter>a\<in>A \<rightarrow> x\<close> v]]) (simp add: step_ack mono_write_FD)
  have level1 : \<open>\<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> \<sqinter>a\<in>A \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> ack \<rightarrow> x\<close> for v
    by (rule trans_FD[OF step_mid]) (simp add: level2 mono_read_FD)
  have final : \<open>mid\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> ack \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D mid\<^bold>?v \<rightarrow> right\<^bold>!v \<rightarrow> ack \<rightarrow> REC\<close> for v
    by (simp add: hyp mono_read_FD mono_write_FD mono_write0_FD)
  show \<open>\<sqinter>a\<in>A \<rightarrow> ((\<lambda>X. \<sqinter>a\<in>A \<rightarrow> X) ^^ 2) x \<sqsubseteq>\<^sub>F\<^sub>D REC\<close>
    using level1 final by (simp add: eval_nat_numeral) (metis (mono_tags, lifting) REC_rec trans_FD)
qed

subsection\<open>Deadlock-Freeness of SYSTEM\<close>

text\<open>\<^const>\<open>SYSTEM\<close> is built from \<^const>\<open>SEND\<close> and \<^const>\<open>REC\<close> by synchronisation and hiding,
so its own alphabet does not fit the simple \<open>deadlock_free_gen_n_coinduct\<close> pattern at all
(it is not a bounded lasso over a fixed set). Instead we transport deadlock-freeness from
\<^const>\<open>COPY\<close> along the classical refinement \<^term>\<open>COPY \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM\<close>: since
\<^term>\<open>deadlock_free P \<equiv> DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D P\<close>, deadlock-freeness is monotone under \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close>
by plain transitivity, so \<^const>\<open>deadlock_free\<close> \<^const>\<open>COPY\<close> together with \<^term>\<open>COPY \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM\<close>
gives \<^const>\<open>deadlock_free\<close> \<^const>\<open>SYSTEM\<close> directly, without needing the stronger fact
(\<^term>\<open>SYSTEM = COPY\<close>, which only holds when \<^term>\<open>SYN\<close> is finite).\<close>

lemma simplification_lemmas [simp] :
  \<open>range left \<inter> SYN = {}\<close>  \<open>range right \<inter> SYN = {}\<close>  \<open>ack \<in> SYN\<close>    \<open>range mid \<subseteq> SYN\<close>
  \<open>mid x \<in> SYN\<close>            \<open>right x \<notin> SYN\<close>           \<open>left x \<notin> SYN\<close> \<open>inj mid\<close>
  by (auto simp: SYN_def inj_on_def)

lemmas Sync_rules   = read_Sync_read_subset_forced_read_same_chan
                      read_Sync_read_left read_Sync_read_right
                      write_Sync_read_left write_Sync_read_right
                      read_Sync_write_left read_Sync_write_right
                      write_Sync_write_subset
                      write_Sync_read_subset read_Sync_write_subset
                      write0_Sync_write_right write0_Sync_write0

lemmas Hiding_rules = Hiding_read_disjoint Hiding_write_subset Hiding_write_disjoint
                      Hiding_write0_non_disjoint Hiding_write0_disjoint

text\<open>Again the refineness proof known from the \<^verbatim>\<open>CopyBuffer\<close>-theory:\<close>
lemma COPY_FD_SYSTEM : \<open>(COPY :: 'a channel process) \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM\<close>
  unfolding SYSTEM_def COPY_def
proof (rule fix_ind)
  show \<open>adm (\<lambda>a. a \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \ SYN))\<close>
    by (simp add: cont2mono)
next
  show \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \ SYN)\<close>
    by simp
next
  fix x :: \<open>'a channel process\<close>
  assume hyp : \<open>x \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \ SYN)\<close>
  show \<open>(\<Lambda> x. left\<^bold>?xa \<rightarrow> right\<^bold>!xa \<rightarrow> x)\<cdot>x \<sqsubseteq>\<^sub>F\<^sub>D (SEND \<lbrakk>SYN\<rbrakk> REC \ SYN)\<close>
    apply (subst SEND_rec, subst REC_rec)
    apply (simp add: cont_fun)
  proof -
    have \<open>left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC \ SYN
             =  left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> mid\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC \ SYN)\<close>
      (is \<open>?lhs = _\<close>)
      by (simp add: Sync_rules Hiding_rules)
    also have \<open>\<dots> =  left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC) \ SYN)\<close>
      by (simp add: Sync_rules Hiding_rules)
    also have \<open>\<dots> = left\<^bold>?x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC) \ SYN\<close>
      by (simp add: Sync_rules Hiding_rules)
    also have \<open>\<dots> = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> (ack \<rightarrow> SEND \<lbrakk>SYN\<rbrakk> ack \<rightarrow> REC) \ SYN\<close>
      by (simp add: Sync_rules Hiding_rules)
    also have \<open>\<dots> = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> (SEND \<lbrakk>SYN\<rbrakk> REC \ SYN)\<close> (is \<open>_ = ?rhs\<close>)
      by (simp add: Sync_rules Hiding_rules)
    finally have * : \<open>?lhs = ?rhs\<close> .
    show \<open>left\<^bold>?xa \<rightarrow> right\<^bold>!xa \<rightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close>
      by (simp only: "*" mono_read_FD mono_write_FD hyp)
  qed
qed

lemma deadlock_free_SYSTEM : \<open>deadlock_free (SYSTEM :: 'a channel process)\<close>
  using deadlock_free_COPY COPY_FD_SYSTEM deadlock_free_mono_FD by blast

section\<open>Lifelock-Freeness of COPY, SEND, REC and SYSTEM\<close>

text\<open>A direct CHAOS-based coinduction here (mirroring \<open>deadlock_free_gen_n_coinduct\<close>) would
not simply reuse the same combinatorics: \<^const>\<open>CHAOS\<close>'s step is built on \<^emph>\<open>external\<close>
choice (\<^term>\<open>\<box>a\<in>A \<rightarrow> X\<close>), for which restricting the offered alphabet is not a refinement the
way it is for \<^const>\<open>Mndetprefix\<close> (\<open>Mndetprefix_FD_subset\<close>) --- internal choice may always
commit to fewer branches, but external choice genuinely changes what is offered. Fortunately
none of that is needed here: the library already proves the general, unconditional fact
\<open>deadlock_free_implies_lifelock_free\<close> : \<^term>\<open>deadlock_free P \<Longrightarrow> lifelock_free P\<close> (deadlock-freeness
is always the stronger property), so lifelock-freeness of \<^const>\<open>COPY\<close>, \<^const>\<open>SEND\<close>,
\<^const>\<open>REC\<close> and \<^const>\<open>SYSTEM\<close> follows at once from what is already proved above.\<close>

lemma lifelock_free_COPY : \<open>lifelock_free (COPY :: 'a channel process)\<close>
  by (rule deadlock_free_implies_lifelock_free[OF deadlock_free_COPY])

lemma lifelock_free_SEND : \<open>lifelock_free (SEND :: 'a channel process)\<close>
  by (rule deadlock_free_implies_lifelock_free[OF deadlock_free_SEND])

lemma lifelock_free_REC : \<open>lifelock_free (REC :: 'a channel process)\<close>
  by (rule deadlock_free_implies_lifelock_free[OF deadlock_free_REC])

lemma lifelock_free_SYSTEM : \<open>lifelock_free (SYSTEM :: 'a channel process)\<close>
  by (rule deadlock_free_implies_lifelock_free[OF deadlock_free_SYSTEM])



end