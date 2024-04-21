(*<*)
theory FindP
imports
  "Optics.Lenses"
  Assume_Guarantee
begin

declare lens_comp_def[simp] fst_lens_def[simp] snd_lens_def[simp]

lemma get_1[simp]:
  shows "get\<^bsub>1\<^sub>L\<^esub> = id"
unfolding id_lens_def by simp

(*>*)
section\<open> Example: findP\label{sec:ex_findP} \<close>

text\<open>

We demonstrate assume/guarantee reasoning by showing the safety of \<open>findP\<close>, a classic exercise in
concurrency verification. It has been treated by at least:

 \<^item> \<^citet>\<open>\<open>Example~5.1\<close> in "KarpMiller:1969"\<close>
 \<^item> \<^citet>\<open>\<open>\S3\<close> in "Rosen:1976"\<close>
 \<^item> \<^citet>\<open>\<open>\S4 Example~2\<close> in "OwickiGries:1976"\<close>
 \<^item> \<^citet>\<open>\<open>\S2.4\<close> in "Jones:1983"\<close>
 \<^item> \<^citet>\<open>\<open>\S3.1\<close> in "XuCauCollette:1994"\<close>
 \<^item> \<^citet>\<open>\<open>p161\<close> in "Brookes:1996"\<close> (no proof)
 \<^item> \<^citet>\<open>\<open>Examples~3.57~and~8.26\<close> in "deRoeverEtAl:2001"\<close> (atomic guarded commands)
 \<^item> \<^citet>\<open>\<open>\S6.2\<close> in "Dingel:2002"\<close> (refinement)
 \<^item> \<^citet>\<open>\<open>\S10\<close> in "PrensaNieto:2003"\<close> (mechanized, arbitrary number of threads)
 \<^item> \<^citet>\<open>\<open>\S7.4, \S8.6\<close> in "AptDeBoerOlderog:2009"\<close>
 \<^item> \<^citet>\<open>\<open>\S4\<close> in "HayesJones:2017"\<close> (refinement)

We take the task to be of finding the first element of a given
array \<open>A\<close> that satisfies a given predicate
\<open>pred\<close>, if it exists, or yielding \<open>length A\<close>
if it does not. This search is performed with two threads: one
searching the even indices and the other the odd. There is the
possibility of a thread terminating early if it notices that the other
thread has found a better candidate than it could.

We generalise previous treatments by allowing the predicate to be
specified modularly and to be a function of the state. It is required
to be pure, i.e., it cannot change the observable/shared state, though
it could have its own local state.

Our search loops are defined recursively; one could just as easily use
\<^const>\<open>prog.while\<close>. We use a list and not an array for
simplicity -- at this level of abstraction there is no difference --
and a mix of variables, where the monadic ones are purely local and
the state-based are shared between the threads. The lens allows the
array to be a value or reside in the (observable/shared) state.

\<close>
(* The program and proofs should carry over to TSO directly: the assume is already strong enough. *)

type_synonym 's state = "(nat \<times> nat) \<times> 's"

abbreviation foundE :: "nat \<Longrightarrow> 's state" where "foundE \<equiv> fst\<^sub>L ;\<^sub>L fst\<^sub>L"
abbreviation foundO :: "nat \<Longrightarrow> 's state" where "foundO \<equiv> snd\<^sub>L ;\<^sub>L fst\<^sub>L"

context
  fixes pred :: "'a \<Rightarrow> ('s, bool) prog"
  fixes predPre :: "'s pred"
  fixes predP :: "'a \<Rightarrow> 's pred"
  fixes A :: "'s rel"
  fixes array :: "'a list \<Longrightarrow> 's"
  \<comment>\<open> A guarantee of \<open>Id\<close> indicates that \<open>pred a\<close> is observationally pure. \<close>
  assumes iag_pred: "\<And>a. prog.p2s (pred a) \<le> \<lbrace>predPre \<^bold>\<and> \<langle>a\<rangle> \<^bold>\<in> SET get\<^bsub>array\<^esub>\<rbrace>, A\<^sup>= \<inter> Id\<^bsub>get\<^bsub>array\<^esub>\<^esub> \<inter> ceilr predPre \<inter> Id\<^bsub>predP a\<^esub> \<turnstile> Id, \<lbrace>\<lambda>rv. \<langle>rv\<rangle> \<^bold>= predP a\<rbrace>"
begin

abbreviation array' :: "'a list \<Longrightarrow> 's state" where "array' \<equiv> array ;\<^sub>L snd\<^sub>L"

partial_function (lfp) findP_loop_evens :: "nat \<Rightarrow> ('s state, unit) prog" where
  "findP_loop_evens i =
    do { fO \<leftarrow> prog.read get\<^bsub>foundO\<^esub>
       ; prog.whenM (i < fO)
          (do { v \<leftarrow> prog.read (\<lambda>s. get\<^bsub>array'\<^esub> s ! i)
              ; b \<leftarrow> prog.localize (pred v)
              ; if b then prog.write (\<lambda>s. put\<^bsub>foundE\<^esub> s i) else findP_loop_evens (i + 2)
              })
       }"

partial_function (lfp) findP_loop_odds :: "nat \<Rightarrow> ('s state, unit) prog" where
  "findP_loop_odds i =
    do { fE \<leftarrow> prog.read get\<^bsub>foundE\<^esub>
       ; prog.whenM (i < fE)
          (do { v \<leftarrow> prog.read (\<lambda>s. get\<^bsub>array'\<^esub> s ! i)
              ; b \<leftarrow> prog.localize (pred v)
              ; if b then prog.write (\<lambda>s. put\<^bsub>foundO\<^esub> s i) else findP_loop_odds (i + 2)
              })
       }"

definition findP :: "('s, nat) prog" where
  "findP = prog.local (
    do { N \<leftarrow> prog.read (SIZE get\<^bsub>array'\<^esub>)
       ; prog.write (\<lambda>s. put\<^bsub>foundE\<^esub> s N)
       ; prog.write (\<lambda>s. put\<^bsub>foundO\<^esub> s N)
       ; (findP_loop_evens 0 \<parallel> findP_loop_odds 1)
       ; fE \<leftarrow> prog.read (get\<^bsub>foundE\<^esub>)
       ; fO \<leftarrow> prog.read (get\<^bsub>foundO\<^esub>)
       ; prog.return (min fE fO)
       })"


paragraph\<open> Relies and guarantees \<close>

abbreviation (input) A' :: "'s rel" where "A' \<equiv> A\<^sup>= \<inter> ceilr predPre \<inter> (\<Inter>a. Id\<^bsub>predP a\<^esub>)"

definition AE :: "'s state rel" where
  "AE = UNIV \<times>\<^sub>R A' \<inter> Id\<^bsub>get\<^bsub>array'\<^esub>\<^esub> \<inter> Id\<^bsub>get\<^bsub>foundE\<^esub>\<^esub> \<inter> \<^bold>\<le>\<^bsub>get\<^bsub>foundO\<^esub>\<^esub>"

definition GE :: "'s state rel" where
  "GE = Id\<^bsub>snd\<^esub> \<inter> Id\<^bsub>get\<^bsub>foundO\<^esub>\<^esub> \<inter> \<^bold>\<le>\<^bsub>get\<^bsub>foundE\<^esub>\<^esub>"

definition AO :: "'s state rel" where
  "AO = UNIV \<times>\<^sub>R A' \<inter> Id\<^bsub>get\<^bsub>array'\<^esub>\<^esub> \<inter> Id\<^bsub>get\<^bsub>foundO\<^esub>\<^esub> \<inter> \<^bold>\<le>\<^bsub>get\<^bsub>foundE\<^esub>\<^esub>"

definition GO :: "'s state rel" where
  "GO = Id\<^bsub>snd\<^esub> \<inter> Id\<^bsub>get\<^bsub>foundE\<^esub>\<^esub> \<inter> \<^bold>\<le>\<^bsub>get\<^bsub>foundO\<^esub>\<^esub>"

lemma AG_refl_trans:
  shows
    "refl AE"
    "refl AO"
    "trans A \<Longrightarrow> trans AE"
    "trans A \<Longrightarrow> trans AO"
    "refl GE"
    "refl GO"
    "trans GE"
    "trans GO"
unfolding AE_def AO_def GE_def GO_def
by (auto simp: refl_inter_conv refl_relprod_conv
       intro!: trans_Int refl_UnionI refl_INTER trans_INTER)

lemma AG_containment:
  shows "GO \<subseteq> AE"
    and "GE \<subseteq> AO"
by (auto simp: AE_def AO_def GO_def GE_def refl_onD[OF ceilr.refl])

lemma G_containment:
  shows "GE \<union> GO \<subseteq> UNIV \<times>\<^sub>R Id"
by (fastforce simp: GE_def GO_def)

paragraph\<open> Safety proofs \<close>

lemma ag_findP_loop_evens:
  shows "prog.p2s (findP_loop_evens i)
       \<le> \<lbrace>\<langle>even i\<rangle> \<^bold>\<and> (\<lambda>s. predPre (snd s)) \<^bold>\<and> get\<^bsub>foundE\<^esub> \<^bold>= SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> get\<^bsub>foundO\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub>\<rbrace>, AE \<turnstile> GE,
                   \<lbrace>\<lambda>_. (get\<^bsub>foundE\<^esub> \<^bold>< SIZE get\<^bsub>array'\<^esub> \<^bold>\<longrightarrow> localize1 predP \<^bold>$\<^bold>$ get\<^bsub>array'\<^esub> \<^bold>! get\<^bsub>foundE\<^esub>)
                      \<^bold>\<and> (\<^bold>\<forall>j. \<langle>i \<le> j \<and> even j\<rangle> \<^bold>\<and> \<langle>j\<rangle> \<^bold>< pred_min get\<^bsub>foundE\<^esub> get\<^bsub>foundO\<^esub> \<^bold>\<longrightarrow> \<^bold>\<not> localize1 predP \<^bold>$\<^bold>$ get\<^bsub>array'\<^esub> \<^bold>! \<langle>j\<rangle>)\<rbrace>"
proof(intro ag.gen_asm,
      induct arbitrary: i rule: findP_loop_evens.fixp_induct[case_names bot adm step])
  case (step R i) show ?case
apply (rule iag.init)
  apply (rule iag.intro)+
      \<comment>\<open> else branch, recursive call \<close>
      apply (rename_tac v va vb)
      apply (rule_tac P="\<langle>va\<rangle> \<^bold>= get\<^bsub>array'\<^esub> \<^bold>! \<langle>i\<rangle> \<^bold>\<and> \<langle>vb\<rangle> \<^bold>= localize1 predP va"
                   in iag.stable_augment[OF step.hyps])
        apply (simp add: \<open>even i\<close>; fail)
       apply clarsimp
       apply (metis \<open>even i\<close> even_Suc less_Suc_eq not_less)
      apply (force simp: GE_def AE_def stable_def monotone_def) (* stability for \<open>iag.stable_augment\<close> *)
     \<comment>\<open> \<open>prog.localize (pred ...)\<close> \<close>
     apply (rename_tac v va)
     apply (rule_tac Q="\<lambda>vb. (\<lambda>s. predPre (snd s)) \<^bold>\<and> get\<^bsub>foundE\<^esub> \<^bold>= SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> get\<^bsub>foundO\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> \<langle>v\<rangle> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> \<langle>va\<rangle> \<^bold>= get\<^bsub>array'\<^esub> \<^bold>! \<langle>i\<rangle> \<^bold>\<and> \<langle>vb\<rangle> \<^bold>= localize1 predP va"
                  in ag.post_imp)
      apply (clarsimp simp: GE_def exI[where x="\<langle>i\<rangle> \<^bold>\<le> get\<^bsub>foundE\<^esub>"]; fail)
     apply (rule iag.pre_g[where G'=GE, OF iag.stable_augment_post[OF iag.augment_a[where A'=AE, OF ag.prog.localize_lift[OF iag_pred, simplified]]]])
      apply (fastforce simp: AE_def stable_def monotone_def)
     apply (metis AG_refl_trans(5) refl_alt_def)
    apply (rule iag.intro)+
 \<comment>\<open> precondition \<close>
 apply force
\<comment>\<open> assume \<close>
apply (intro conjI Int_greatest INT_greatest ceilr.largest)
apply ((fastforce simp: stable_def monotone_def AE_def)+)[6]
apply (clarsimp simp: stable_def monotone_def AE_def GE_def; rule exI[where x="\<langle>i\<rangle> \<^bold>\<le> get\<^bsub>foundE\<^esub>"]; clarsimp; metis) (* FIXME ouch *)
apply (fastforce simp: stable_def monotone_def AE_def)+
done
qed simp_all

lemma ag_findP_loop_odds:
  shows "prog.p2s (findP_loop_odds i)
       \<le> \<lbrace>\<langle>odd i\<rangle> \<^bold>\<and> (\<lambda>s. predPre (snd s)) \<^bold>\<and> get\<^bsub>foundO\<^esub> \<^bold>= SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> get\<^bsub>foundE\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub>\<rbrace>, AO \<turnstile> GO,
                   \<lbrace>\<lambda>_. (get\<^bsub>foundO\<^esub> \<^bold>< SIZE get\<^bsub>array'\<^esub> \<^bold>\<longrightarrow> localize1 predP \<^bold>$\<^bold>$ get\<^bsub>array'\<^esub> \<^bold>! get\<^bsub>foundO\<^esub>)
                      \<^bold>\<and> (\<^bold>\<forall>j. \<langle>i \<le> j \<and> odd j\<rangle> \<^bold>\<and> \<langle>j\<rangle> \<^bold>< pred_min get\<^bsub>foundE\<^esub> get\<^bsub>foundO\<^esub> \<^bold>\<longrightarrow> \<^bold>\<not> localize1 predP \<^bold>$\<^bold>$ get\<^bsub>array'\<^esub> \<^bold>! \<langle>j\<rangle>)\<rbrace>"
proof(intro ag.gen_asm,
      induct arbitrary: i rule: findP_loop_odds.fixp_induct[case_names bot adm step])
  case (step R i) show ?case
apply (rule iag.init)
  apply (rule iag.intro)+
      \<comment>\<open> else branch, recursive call \<close>
      apply (rename_tac v va vb)
      apply (rule_tac P="\<langle>va\<rangle> \<^bold>= get\<^bsub>array'\<^esub> \<^bold>! \<langle>i\<rangle> \<^bold>\<and> \<langle>vb\<rangle> \<^bold>= localize1 predP va"
                   in iag.stable_augment[OF step.hyps])
        apply (simp add: \<open>odd i\<close>; fail)
       apply clarsimp
       apply (metis \<open>odd i\<close> even_Suc less_Suc_eq not_less)
      apply (force simp: GO_def AO_def stable_def monotone_def) (* stability for \<open>ag.stable_augment\<close> *)
     \<comment>\<open> \<open>prog.localize (pred ...)\<close> \<close>
     apply (rename_tac v va)
     apply (rule_tac Q="\<lambda>vb. (\<lambda>s. predPre (snd s)) \<^bold>\<and> get\<^bsub>foundO\<^esub> \<^bold>= SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> get\<^bsub>foundE\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> \<langle>v\<rangle> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> \<langle>va\<rangle> \<^bold>= get\<^bsub>array'\<^esub> \<^bold>! \<langle>i\<rangle> \<^bold>\<and> \<langle>vb\<rangle> \<^bold>= localize1 predP va"
                  in ag.post_imp)
      apply (clarsimp simp: GO_def exI[where x="\<langle>i\<rangle> \<^bold>\<le> get\<^bsub>foundO\<^esub>"]; fail)
     apply (rule iag.pre_g[where G'=GO, OF iag.stable_augment_post[OF iag.augment_a[where A'=AO, OF ag.prog.localize_lift[OF iag_pred, simplified]]]])
      apply (fastforce simp: AO_def stable_def monotone_def)
     apply (metis AG_refl_trans(6) refl_alt_def)
    apply (rule iag.intro)+
 \<comment>\<open> precondition \<close>
 apply force
\<comment>\<open> assume \<close>
apply (intro conjI Int_greatest INT_greatest ceilr.largest)
apply ((fastforce simp: AO_def stable_def monotone_def)+)[6]
apply (clarsimp simp: AO_def GO_def stable_def monotone_def; rule exI[where x="\<langle>i\<rangle> \<^bold>\<le> get\<^bsub>foundO\<^esub>"]; clarsimp; metis) (* FIXME ouch *)
apply (fastforce simp: AO_def stable_def monotone_def)+
done
qed simp_all

theorem ag_findP:
  shows "prog.p2s findP
           \<le> \<lbrace>predPre\<rbrace>, A' \<inter> Id\<^bsub>get\<^bsub>array\<^esub>\<^esub>
                \<turnstile> Id, \<lbrace>\<lambda>v s. v = (LEAST i. i < SIZE get\<^bsub>array\<^esub> s \<longrightarrow> predP (get\<^bsub>array\<^esub> s ! i) s)\<rbrace>"
unfolding findP_def
apply (rule ag.prog.local)
apply (rule iag.init)
  apply (rule iag.intro)+
     apply (rule iag.augment_post_imp[where Q="\<lambda>v. get\<^bsub>foundE\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub> \<^bold>\<and> get\<^bsub>foundO\<^esub> \<^bold>\<le> SIZE get\<^bsub>array'\<^esub>"])
     apply (rule iag.pre_g[OF _ G_containment])
     apply (rule iag.stable_augment_frame)
      apply (rule iag.parallel[OF ag_findP_loop_evens ag_findP_loop_odds _ AG_containment order.refl])
      \<comment>\<open> postcondition from \<open>iag.parallel\<close> \<close>
      apply clarsimp
      apply (rule Least_equality, linarith)
      subgoal for x y s z by (clarsimp simp: min_le_iff_disj not_less not_le dest!: spec[where x=z])
     \<comment>\<open> stability for \<open>iag.stable_augment_frame\<close> \<close>
     apply (force simp: stable_def monotone_def AE_def AO_def GE_def GO_def)
    apply (rule iag.intro)+
 \<comment>\<open> precondition \<close>
 apply fastforce
\<comment>\<open> assume \<close>
 apply (simp;
        intro conjI Int_greatest INT_greatest ceilr.largest;
        fastforce simp: AE_def AO_def stable_def monotone_def)
done

end

text\<open>

We conclude by showing how we can instantiate the above with a \<open>coprime\<close> predicate.

\<close>

setup \<open>Sign.mandatory_path "gcd"\<close>

type_synonym 's state = "(nat \<times> nat) \<times> 's"

abbreviation x :: "nat \<Longrightarrow> 's gcd.state" where "x \<equiv> fst\<^sub>L ;\<^sub>L fst\<^sub>L"
abbreviation y :: "nat \<Longrightarrow> 's gcd.state" where "y \<equiv> snd\<^sub>L ;\<^sub>L fst\<^sub>L"

definition seq :: "nat \<Rightarrow> nat \<Rightarrow> ('s, nat) prog" where
  "seq a b =
     prog.local (
       do { prog.write (\<lambda>s. put\<^bsub>gcd.x\<^esub> s a)
          ; prog.write (\<lambda>s. put\<^bsub>gcd.y\<^esub> s b)
          ; prog.while (\<lambda>_.
              do { xv \<leftarrow> prog.read get\<^bsub>gcd.x\<^esub>
                 ; yv \<leftarrow> prog.read get\<^bsub>gcd.y\<^esub>
                 ; if xv = yv
                   then prog.return (Inr ())
                   else (do { (if xv < yv
                               then prog.write (\<lambda>s. put\<^bsub>gcd.y\<^esub> s (yv - xv))
                               else prog.write (\<lambda>s. put\<^bsub>gcd.x\<^esub> s (xv - yv)))
                            ; prog.return (Inl ()) })
                 }) ()
          ; prog.read get\<^bsub>gcd.x\<^esub>
          })"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.gcd"\<close>

lemma seq:
  shows "prog.p2s (gcd.seq a b) \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, UNIV \<turnstile> Id, \<lbrace>\<lambda>v. \<langle>v = gcd a b\<rangle>\<rbrace>"
unfolding gcd.seq_def
apply (rule ag.prog.local)
apply (rule iag.init)
  apply (rule iag.intro iag.while[where I="\<lambda>_ s. gcd (get\<^bsub>gcd.x\<^esub> s) (get\<^bsub>gcd.y\<^esub> s) = gcd a b"])+
 \<comment>\<open> precond \<close>
 apply (auto simp: gcd_diff1_nat)[1]
 apply (metis gcd.commute gcd_diff1_nat less_or_eq_imp_le)
\<comment>\<open> assume \<close>
apply (intro stable.intro stable.local_only INFI infI)
apply auto
done

setup \<open>Sign.parent_path\<close>

definition findP_coprime :: "(nat \<times> nat list, nat) prog" where
  "findP_coprime = findP (\<lambda>a. prog.read get\<^bsub>fst\<^sub>L\<^esub> \<bind> gcd.seq a \<bind> (\<lambda>c. prog.return (c = 1))) snd\<^sub>L"

lemma ag_findP_coprime':
  shows "prog.p2s findP_coprime
           \<le> \<lbrace>\<langle>True\<rangle>\<rbrace>, Id
                \<turnstile> Id, \<lbrace>\<lambda>rv s. rv = (LEAST i. i < length (get\<^bsub>snd\<^sub>L\<^esub> s) \<longrightarrow> coprime (get\<^bsub>fst\<^sub>L\<^esub> s) (get\<^bsub>snd\<^sub>L\<^esub> s ! i))\<rbrace>"
unfolding findP_coprime_def
apply (rule iag.init)
  apply (rule ag_findP[where A=Id and array="snd\<^sub>L" and predP="\<lambda>b s. coprime (get\<^bsub>fst\<^sub>L\<^esub> s) b" and predPre="\<langle>True\<rangle>"])
  apply (rule iag.init)
    apply (rule iag.intro)+
     apply (rule_tac Q="\<langle>\<langle>v\<rangle> \<^bold>= get\<^bsub>fst\<^sub>L\<^esub>\<rangle>" in iag.augment_post_imp)
     apply (rule iag.stable_augment_frame)
      apply (rule iag.pre[OF ag.gcd.seq, where A'=Id and P'="\<langle>True\<rangle>", simplified, OF order.refl])
      apply (clarsimp simp: ac_simps coprime_iff_gcd_eq_1 simp flip: One_nat_def; fail)
     apply (force simp: stable_def monotone_def)
    apply (rule iag.intro)+
 apply (simp; intro conjI INT_greatest ceilr.largest; fastforce simp: stable_def monotone_def)+
done

lemma ag_findP_coprime: \<comment>\<open> Shuffle the parameter to the precondition, exploiting purity. \<close>
  shows "prog.p2s findP_coprime
           \<le> \<lbrace>\<langle>a\<rangle> \<^bold>= get\<^bsub>fst\<^sub>L\<^esub>\<rbrace>, Id
                \<turnstile> Id, \<lbrace>\<lambda>rv s. rv = (LEAST i. i < length (get\<^bsub>snd\<^sub>L\<^esub> s) \<longrightarrow> coprime a (get\<^bsub>snd\<^sub>L\<^esub> s ! i))\<rbrace>"
apply (rule ag.pre_pre)
 apply (rule ag.stable_augment_post[OF ag_findP_coprime'])
 apply (fastforce simp: stable_def)+
done
(*<*)

end
(*>*)
