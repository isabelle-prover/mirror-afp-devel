(*
  Author: Jørgen Villadsen, DTU Compute, 2020
*)

section \<open>Appendix: Completeness\<close>

theory Sequent_Calculus_Verifier imports Sequent1 SeCaV begin

primrec from_tm and from_tm_list where
  \<open>from_tm (Var n) = FOL_Fitting.Var n\<close> |
  \<open>from_tm (Fun a ts) = App a (from_tm_list ts)\<close> |
  \<open>from_tm_list [] = []\<close> |
  \<open>from_tm_list (t # ts) = from_tm t # from_tm_list ts\<close>

primrec from_fm where
  \<open>from_fm (Pre b ts) = Pred b (from_tm_list ts)\<close> |
  \<open>from_fm (Con p q) = And (from_fm p) (from_fm q)\<close> |
  \<open>from_fm (Dis p q) = Or (from_fm p) (from_fm q)\<close> |
  \<open>from_fm (Imp p q) = Impl (from_fm p) (from_fm q)\<close> |
  \<open>from_fm (Neg p) = FOL_Fitting.Neg (from_fm p)\<close> |
  \<open>from_fm (Uni p) = Forall (from_fm p)\<close> |
  \<open>from_fm (Exi p) = Exists (from_fm p)\<close>

primrec to_tm and to_tm_list where
  \<open>to_tm (FOL_Fitting.Var n) = Var n\<close> |
  \<open>to_tm (App a ts) = Fun a (to_tm_list ts)\<close> |
  \<open>to_tm_list [] = []\<close> |
  \<open>to_tm_list (t # ts) = to_tm t # to_tm_list ts\<close>

primrec to_fm where
  \<open>to_fm \<bottom> = Neg (Imp (Pre 0 []) (Pre 0 []))\<close> |
  \<open>to_fm \<top> = Imp (Pre 0 []) (Pre 0 [])\<close> |
  \<open>to_fm (Pred b ts) = Pre b (to_tm_list ts)\<close> |
  \<open>to_fm (And p q) = Con (to_fm p) (to_fm q)\<close> |
  \<open>to_fm (Or p q) = Dis (to_fm p) (to_fm q)\<close> |
  \<open>to_fm (Impl p q) = Imp (to_fm p) (to_fm q)\<close> |
  \<open>to_fm (FOL_Fitting.Neg p) = Neg (to_fm p)\<close> |
  \<open>to_fm (Forall p) = Uni (to_fm p)\<close> |
  \<open>to_fm (Exists p) = Exi (to_fm p)\<close>

theorem to_from_tm [simp]: \<open>to_tm (from_tm t) = t\<close> \<open>to_tm_list (from_tm_list ts) = ts\<close>
  by (induct t and ts rule: from_tm.induct from_tm_list.induct) simp_all

theorem to_from_fm [simp]: \<open>to_fm (from_fm p) = p\<close>
  by (induct p) simp_all

lemma Truth [simp]: \<open>\<tturnstile> Imp (Pre 0 []) (Pre 0 []) # z\<close>
  using AlphaImp Basic Ext ext.simps member.simps(2) by metis

lemma paramst [simp]:
  \<open>FOL_Fitting.new_term c t = new_term c (to_tm t)\<close>
  \<open>FOL_Fitting.new_list c l = new_list c (to_tm_list l)\<close>
  by (induct t and l rule: FOL_Fitting.paramst.induct FOL_Fitting.paramsts.induct) simp_all

lemma params [iff]: \<open>FOL_Fitting.new c p \<longleftrightarrow> new c (to_fm p)\<close>
  by (induct p) simp_all

lemma list_params [iff]: \<open>FOL_Fitting.news c z \<longleftrightarrow> news c (map to_fm z)\<close>
  by (induct z) simp_all

lemma liftt [simp]:
  \<open>to_tm (FOL_Fitting.liftt t) = inc_term (to_tm t)\<close>
  \<open>to_tm_list (FOL_Fitting.liftts l) = inc_list (to_tm_list l)\<close>
  by (induct t and l rule: FOL_Fitting.liftt.induct FOL_Fitting.liftts.induct) simp_all

lemma substt [simp]:
  \<open>to_tm (FOL_Fitting.substt t s v) = sub_term v (to_tm s) (to_tm t)\<close>
  \<open>to_tm_list (FOL_Fitting.substts l s v) = sub_list v (to_tm s) (to_tm_list l)\<close>
  by (induct t and l rule: FOL_Fitting.substt.induct FOL_Fitting.substts.induct) simp_all

lemma subst [simp]: \<open>to_fm (FOL_Fitting.subst A t s) = sub s (to_tm t) (to_fm A)\<close>
  by (induct A arbitrary: t s) simp_all

lemma sim: \<open>(\<turnstile> x) \<Longrightarrow> (\<tturnstile> (map to_fm x))\<close>
  by (induct rule: SC.induct) (force intro: sequent_calculus.intros)+

lemma evalt [simp]:
  \<open>semantics_term e f t = evalt e f (from_tm t)\<close>
  \<open>semantics_list e f ts = evalts e f (from_tm_list ts)\<close>
  by (induct t and ts rule: from_tm.induct from_tm_list.induct) simp_all

lemma shift [simp]: \<open>shift e 0 x = e\<langle>0:x\<rangle>\<close>
  unfolding shift_def FOL_Fitting.shift_def by simp

lemma semantics [iff]: \<open>semantics e f g p \<longleftrightarrow> eval e f g (from_fm p)\<close>
  by (induct p arbitrary: e) simp_all

abbreviation valid ("\<then> _" 0) where
  \<open>(\<then> p) \<equiv> \<forall>(e :: _ \<Rightarrow> nat hterm) f g. semantics e f g p\<close>

theorem complete_sound: \<open>\<then> p \<Longrightarrow> \<tturnstile> [p]\<close> \<open>\<tturnstile> [q] \<Longrightarrow> semantics e f g q\<close>
  by (metis to_from_fm sim semantics list.map SC_completeness) (use sound in force)

corollary \<open>(\<then> p) \<longleftrightarrow> (\<tturnstile> [p])\<close>
  using complete_sound by fast

section \<open>Reference\<close>

text \<open>Asta Halkjær From (2019): Sequent Calculus \<^url>\<open>https://www.isa-afp.org/entries/FOL_Seq_Calc1.html\<close>\<close>

end
