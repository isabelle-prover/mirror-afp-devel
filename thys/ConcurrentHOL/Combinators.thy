(*<*)
theory Combinators
imports
  Programs
begin

(*>*)
section\<open> More combinators\label{sec:combinators} \<close>

text\<open>

Extra combinators:
 \<^item> \<open>prog.select\<close> shows how we can handle arbitrary choice
 \<^item> \<open>prog.while\<close> combinator expresses all tail-recursive computations. Its condition is a pure value.

\<close>

setup \<open>Sign.mandatory_path "prog"\<close>

definition select :: "'v set \<Rightarrow> ('s, 'v) prog" where
  "select X = (\<Squnion>x\<in>X. prog.return x)"

context
  notes [[function_internals]]
begin

partial_function (lfp) while :: "('k \<Rightarrow> ('s, 'k + 'v) prog) \<Rightarrow> 'k \<Rightarrow> ('s, 'v) prog" where
  "while c k = c k \<bind> (\<lambda>rv. case rv of Inl k' \<Rightarrow> while c k' | Inr v \<Rightarrow> prog.return v)"

end

abbreviation loop :: "('s, unit) prog \<Rightarrow> ('s, 'w) prog" where
  "loop P \<equiv> prog.while (\<lambda>(). P \<then> prog.return (Inl ())) ()"

abbreviation guardM :: "bool \<Rightarrow> ('s, unit) prog" where
  "guardM b \<equiv> if b then \<bottom> else prog.return ()"

abbreviation unlessM :: "bool \<Rightarrow> ('s, unit) prog \<Rightarrow> ('s, unit) prog" where
  "unlessM b c \<equiv> if b then prog.return () else c"

abbreviation whenM :: "bool \<Rightarrow> ('s, unit) prog \<Rightarrow> ('s, unit) prog" where
  "whenM b c \<equiv> if b then c else prog.return ()"

definition app :: "('a \<Rightarrow> ('s, unit) prog) \<Rightarrow> 'a list \<Rightarrow> ('s, unit) prog" where \<comment>\<open> Haskell's \<open>mapM_\<close> \<close>
  "app f xs = foldr (\<lambda>x m. f x \<then> m) xs (prog.return ())"

definition set_app :: "('a \<Rightarrow> ('s, unit) prog) \<Rightarrow> 'a set \<Rightarrow> ('s, unit) prog" where
  "set_app f =
    prog.while (\<lambda>X. if X = {} then prog.return (Inr ())
                              else prog.select X \<bind> (\<lambda>x. f x \<then> prog.return (Inl (X - {x}))))"

primrec foldM :: "('b \<Rightarrow> 'a \<Rightarrow> ('s, 'b) prog) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> ('s, 'b) prog" where
  "foldM f b [] = prog.return b"
| "foldM f b (x # xs) = do {
     b' \<leftarrow> f b x;
     foldM f b' xs
   }"

primrec fold_mapM :: "('a \<Rightarrow> ('s, 'b) prog) \<Rightarrow> 'a list \<Rightarrow> ('s, 'b list) prog" where
  "fold_mapM f [] = prog.return []"
| "fold_mapM f (x # xs) = do {
     y \<leftarrow> f x;
     ys \<leftarrow> fold_mapM f xs;
     prog.return (y # ys)
   }"

setup \<open>Sign.mandatory_path "select"\<close>

lemma empty:
  shows "prog.select {} = \<bottom>"
by (simp add: prog.select_def)

lemma singleton:
  shows "prog.select {x} = prog.return x"
by (simp add: prog.select_def)

lemma monotone:
  shows "mono prog.select"
by (simp add: monoI prog.select_def SUP_subset_mono)

lemmas strengthen[strg] = st_monotone[OF prog.select.monotone]
lemmas mono = monotoneD[OF prog.select.monotone, of P Q for P Q]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.select.monotone, simplified, of orda P for orda P]

lemma Sup:
  shows "prog.select (\<Union>X) = (\<Squnion>x\<in>X. prog.select x)"
by (simp add: prog.select_def flip: SUP_UNION)

lemma mcont:
  shows "mcont \<Union> (\<subseteq>) Sup (\<le>) prog.select"
by (simp add: mcontI contI prog.select.monotone prog.select.Sup)

lemmas mcont2mcont[cont_intro] = mcont2mcont[OF prog.select.mcont, of supa orda P for supa orda P]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "return"\<close>

lemma select_le:
  assumes "x \<in> X"
  shows "prog.return x \<le> prog.select X"
by (simp add: assms prog.select_def SUP_upper)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "bind"\<close>

lemma selectL:
  shows "prog.select X \<bind> g = (\<Squnion>x\<in>X. g x)"
by (simp add: prog.select_def prog.bind.SUPL prog.bind.returnL)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "while"\<close>

lemma bot:
  shows "prog.while \<bottom> = \<bottom>"
by (simp add: fun_eq_iff prog.while.simps prog.bind.botL)

lemma monotone: \<comment>\<open> could hope to prove this with a \<open>strengthen\<close> rule for \<^const>\<open>lfp.fixp_fun\<close> \<close>
  shows "mono (\<lambda>P. prog.while P s)"
by (rule monoI)
   (induct arbitrary: s rule: prog.while.fixp_induct; simp add: prog.bind.mono le_funD split: sum.split)

lemmas strengthen[strg] = st_monotone[OF prog.while.monotone]
lemmas mono' = monotoneD[OF prog.while.monotone, of P Q for P Q] \<comment>\<open> compare with @{thm [source] "prog.while.mono"} \<close>
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.while.monotone, simplified, of orda P for orda P]

lemma Sup_le:
  shows "(\<Squnion>P\<in>X. prog.while P s) \<le> prog.while (\<Squnion>X) s"
by (simp add: SUP_le_iff SupI prog.while.mono')

lemma Inf_le:
  shows "prog.while (\<Sqinter>X) s \<le> (\<Sqinter>P\<in>X. prog.while P s)"
by (simp add: le_INF_iff Inf_lower prog.while.mono')

lemma True_skip_eq_bot:
  shows "prog.while \<langle>prog.return (Inl x)\<rangle> s = \<bottom>"
by (induct arbitrary: s rule: prog.while.fixp_induct) (simp_all add: prog.bind.returnL)

lemma Inr_eq_return:
  shows "prog.while \<langle>prog.return (Inr v)\<rangle> s = prog.return v"
by (subst prog.while.simps) (simp add: prog.bind.returnL)

lemma kleene_star:
  shows "prog.kleene.star P
       = prog.while (\<lambda>_. (P \<then> prog.return (Inl ())) \<squnion> prog.return (Inr ())) ()" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof(induct rule: prog.kleene.star.fixp_induct[case_names adm bot step])
    case (step P) then show ?case
      by (subst prog.while.simps) (simp add: prog.bind.supL prog.bind.bind prog.bind.mono sup.coboundedI1 prog.bind.returnL)
  qed simp_all
  show "?rhs \<le> ?lhs"
  proof(induct rule: prog.while.fixp_induct[case_names adm bot step])
    case (step k) then show ?case
      by (subst prog.kleene.star.simps) (simp add: prog.bind.supL prog.bind.bind prog.bind.mono prog.bind.returnL le_supI1)
  qed simp_all
qed

lemma invmap_le:
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  shows "prog.while (\<lambda>k. prog.invmap sf (map_sum id vf) (c k)) k
      \<le> prog.invmap sf vf (prog.while c k)" (is "?lhs prog.while k \<le> ?rhs k")
proof(rule spec[where x=k],
      induct rule: prog.while.fixp_induct[where P="\<lambda>R. \<forall>k. ?lhs R k \<le> ?rhs k", case_names adm bot step])
  case (step k) show ?case
    apply (subst prog.while.simps)
    apply (strengthen ord_to_strengthen(1)[OF step[rule_format]])
    apply (auto intro!: SUPE prog.bind.mono[OF order.refl]
                 split: sum.splits
                  simp: prog.invmap.bind prog.invmap.return
                        prog.invmap.split_vinvmap[where sf=sf and vf="map_sum id vf"]
                        prog.bind.bind prog.bind.return prog.bind.SUPL
                        SUP_upper
                        order.trans[OF _ prog.bind.mono[OF prog.return.rel_le order.refl]])
    done
qed (simp_all add: prog.invmap.bot)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "loop"\<close>

lemma bindL:
  fixes P :: "('s, unit) prog"
  fixes Q :: "('s, 'w) prog"
  shows "prog.loop P \<then> Q = prog.loop P" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (rule prog.while.fixp_induct[where P="\<lambda>R. R (\<lambda>(). P \<then> prog.return (Inl ())) () \<then> Q \<le> ?rhs"]; simp add: prog.bind.botL)
       (subst prog.while.simps; simp add: prog.bind.bind prog.bind.mono lambda_unit_futzery prog.bind.returnL)
  show "?rhs \<le> ?lhs"
    by (rule prog.while.fixp_induct[where P="\<lambda>R. R (\<lambda>(). P \<then> prog.return (Inl ())) () \<le> ?lhs"]; simp)
       (subst prog.while.simps; simp add: prog.bind.bind prog.bind.mono lambda_unit_futzery prog.bind.returnL)
qed

lemma parallel_le:
  shows "prog.loop P \<le> lfp (\<lambda>R. P \<parallel> R)"
proof(induct rule: prog.while.fixp_induct[case_names adm bot step])
  case (step k) show ?case
    apply (subst lfp_unfold, simp)
    apply (strengthen ord_to_strengthen[OF prog.bind.parallel_le])
    apply (simp add: prog.bind.bind prog.bind.mono prog.bind.returnL step)
    done
qed simp_all

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "foldM"\<close>

lemma append:
  shows "prog.foldM f b (xs @ ys) = prog.foldM f b xs \<bind> (\<lambda>b'. prog.foldM f b' ys)"
by (induct xs arbitrary: b) (simp_all add: prog.bind.returnL prog.bind.bind)

setup \<open>Sign.parent_path\<close>

lemma foldM_alt_def:
  shows "prog.foldM f b xs = foldr (\<lambda>x m. prog.bind m (\<lambda>b. f b x)) (rev xs) (prog.return b)"
by (induct xs arbitrary: b rule: rev_induct) (simp_all add: prog.foldM.append prog.bind.returnR)

setup \<open>Sign.mandatory_path "fold_mapM"\<close>

lemma bot:
  shows "prog.fold_mapM \<bottom> = (\<lambda>xs. case xs of [] \<Rightarrow> prog.return [] | _ \<Rightarrow> \<bottom>)"
by (simp add: fun_eq_iff prog.bind.botL split: list.split)

lemma append:
  shows "prog.fold_mapM f (xs @ ys)
       = prog.fold_mapM f xs \<bind> (\<lambda>xs. prog.fold_mapM f ys \<bind> (\<lambda>ys. prog.return (xs @ ys)))"
by (induct xs) (simp_all add: prog.bind.bind prog.bind.returnL prog.bind.returnR)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "app"\<close>

lemma bot:
  shows "prog.app \<bottom> = (\<lambda>xs. case xs of [] \<Rightarrow> prog.return () | _ \<Rightarrow> \<bottom>)"
    and "prog.app (\<lambda>_. \<bottom>) = (\<lambda>xs. case xs of [] \<Rightarrow> prog.return () | _ \<Rightarrow> \<bottom>)"
by (simp_all add: fun_eq_iff prog.app_def prog.bind.botL split: list.split)

lemma Nil:
  shows "prog.app f [] = prog.return ()"
by (simp add: prog.app_def)

lemma Cons:
  shows "prog.app f (x # xs) = f x \<then> prog.app f xs"
by (simp add: prog.app_def)

lemmas simps =
  prog.app.bot
  prog.app.Nil
  prog.app.Cons

lemma append:
  shows "prog.app f (xs @ ys) = prog.app f xs \<then> prog.app f ys"
by (induct xs arbitrary: ys) (simp_all add: prog.app.simps prog.bind.returnL prog.bind.bind)

lemma monotone:
  shows "mono (\<lambda>f. prog.app f xs)"
by (induct xs) (simp_all add: prog.app.simps le_fun_def monotone_on_def prog.bind.mono)

lemmas strengthen[strg] = st_monotone[OF prog.app.monotone]
lemmas mono = monotoneD[OF prog.app.monotone]
lemmas mono2mono[cont_intro, partial_function_mono] = monotone2monotone[OF prog.app.monotone, simplified, of orda P for orda P]

lemma Sup_le:
  shows "(\<Squnion>f\<in>X. prog.app f xs) \<le> prog.app (\<Squnion>X) xs"
by (simp add: SUP_le_iff SupI prog.app.mono)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma app:
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> unit"
  shows "prog.invmap sf vf (prog.app f xs)
       = prog.app (\<lambda>x. prog.sinvmap sf (f x)) xs \<then> prog.invmap sf vf (prog.return ())"
by (induct xs)
   (simp_all add: prog.app.simps prog.bind.return prog.invmap.bind prog.bind.bind id_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "sinvmap"\<close>

lemma app_le:
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> unit"
  shows "prog.app (\<lambda>x. prog.sinvmap sf (f x)) xs \<le> prog.sinvmap sf (prog.app f xs)"
by (simp add: prog.invmap.app prog.invmap.return prog.bind.return
              order.trans[OF _ prog.bind.mono[OF order.refl prog.return.rel_le]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "set_app"\<close>

lemma bot:
  shows "X \<noteq> {} \<Longrightarrow> prog.set_app \<bottom> X = \<bottom>"
    and "X \<noteq> {} \<Longrightarrow> prog.set_app (\<lambda>_. \<bottom>) X = \<bottom>"
by (simp_all add: prog.set_app_def prog.while.simps prog.bind.bind prog.bind.botL prog.bind.selectL)

lemma empty:
  shows "prog.set_app f {} = prog.return ()"
by (simp add: prog.set_app_def prog.while.simps prog.bind.returnL)

lemma not_empty:
  assumes "X \<noteq> {}"
  shows "prog.set_app f X = prog.select X \<bind> (\<lambda>x. f x \<then> prog.set_app f (X - {x}))"
using assms by (simp add: prog.set_app_def prog.while.simps prog.bind.returnL prog.bind.bind)

lemmas simps =
  prog.set_app.bot
  prog.set_app.empty
  prog.set_app.not_empty

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "app"\<close>

lemma set_app_le:
  assumes "X = set xs"
  assumes "distinct xs"
  shows "prog.app f xs \<le> prog.set_app f X"
using assms
proof(induct xs arbitrary: X)
  case (Cons x xs) then show ?case
    apply (simp add: prog.set_app.simps prog.app.simps)
    apply (strengthen ord_to_strengthen(2)[OF prog.return.select_le[of x]], blast)
    apply (simp add: prog.bind.returnL prog.bind.mono)
    done
qed (simp add: prog.app.simps prog.set_app.simps)

setup \<open>Sign.parent_path\<close>

lemma set_app_alt_def:
  assumes "finite X"
  shows "prog.set_app f X = (\<Squnion>xs\<in>{ys. set ys = X \<and> distinct ys}. prog.app f xs)" (is "?lhs = ?rhs")
proof(rule antisym)
  from assms show "?lhs \<le> ?rhs"
  proof(induct rule: finite_remove_induct)
    case (remove X)
    from \<open>finite X\<close> \<open>X \<noteq> {}\<close> have *: "{ys. set ys = X - {x} \<and> distinct ys} \<noteq> {}" for x
      by (simp add: finite_distinct_list)
    from \<open>X \<noteq> {}\<close> show ?case
      apply (clarsimp simp: prog.set_app.simps prog.bind.selectL)
      apply (strengthen ord_to_strengthen[OF remove.hyps(4)], blast)
      apply (fastforce simp: prog.app.simps prog.bind.SUPR_not_empty[OF *] Sup_le_iff
                      intro: rev_SUPI[where x="x # xs" for x xs])
      done
  qed (simp add: prog.set_app.simps prog.app.simps)
  show "?rhs \<le> ?lhs"
    by (simp add: Sup_le_iff prog.app.set_app_le)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.prog"\<close>

lemma select_sp:
  assumes "\<And>s x. \<lbrakk>P s; x \<in> X\<rbrakk> \<Longrightarrow> Q x s"
  assumes "\<And>v. stable A (P \<^bold>\<and> Q v)"
  shows "prog.p2s (prog.select X) \<le> \<lbrace>P\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>v. P \<^bold>\<and> Q v\<rbrace>"
by (clarsimp simp: prog.select_def prog.p2s.Sup spec.interference.cl.bot ag.spec.term.none_inteference)
   (rule ag.pre[OF ag.prog.return[OF assms(2)]]; blast intro: assms(1))

lemma while:
  fixes c :: "'k \<Rightarrow> ('s, 'k + 'v) prog"
  assumes c: "\<And>k. prog.p2s (c k) \<le> \<lbrace>P k\<rbrace>, A \<turnstile> G, \<lbrace>case_sum I Q\<rbrace>"
  assumes IP: "\<And>s v. I v s \<Longrightarrow> P v s"
  assumes sQ: "\<And>v. stable A (Q v)"
  shows "prog.p2s (prog.while c k) \<le> \<lbrace>I k\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
proof -
  have "prog.p2s (prog.while c k) \<le> \<lbrace>P k\<rbrace>, A \<turnstile> G, \<lbrace>Q\<rbrace>"
  proof(induct arbitrary: k rule: prog.while.fixp_induct[case_names adm bot step])
    case (step k) show ?case
      apply (rule ag.prog.bind[OF _ c])
      apply (rule ag.pre_pre[OF ag.prog.case_sum[OF step ag.prog.return[OF sQ]]])
      apply (simp add: IP split: sum.splits)
      done
  qed (simp_all add: ag.prog.galois)
  then show ?thesis
    by (meson IP ag.pre_pre)
qed

lemma app:
  fixes xs :: "'a list"
  fixes f :: "'a \<Rightarrow> ('s, unit) prog"
  fixes P :: "'a list \<Rightarrow> 's pred"
  assumes "\<And>x ys zs. xs = ys @ x # zs \<Longrightarrow> prog.p2s (f x) \<le> \<lbrace>P ys\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_. P (ys @ [x])\<rbrace>"
  assumes "\<And>ys. prefix ys xs \<Longrightarrow> stable A (P ys)"
  shows "prog.p2s (prog.app f xs) \<le> \<lbrace>P []\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_. P xs\<rbrace>"
using assms
by (induct xs rule: rev_induct;
    fastforce intro: ag.prog.bind ag.prog.return
               simp: prog.app.append prog.bind.returnR prog.app.simps)

lemma app_set:
  fixes X :: "'a set"
  fixes f :: "'a \<Rightarrow> ('s, unit) prog"
  fixes P :: "'a set \<Rightarrow> 's pred"
  assumes "\<And>Y x. \<lbrakk>Y \<subseteq> X; x \<in> X - Y\<rbrakk> \<Longrightarrow> prog.p2s (f x) \<le> \<lbrace>P Y\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_. P (insert x Y)\<rbrace>"
  assumes "\<And>Y. Y \<subseteq> X \<Longrightarrow> Stability.stable A (P Y)"
  shows "prog.p2s (prog.set_app f X) \<le> \<lbrace>P {}\<rbrace>, A \<turnstile> G, \<lbrace>\<lambda>_. P X\<rbrace>"
proof -
  have *: "X - (Y - {x}) = insert x (X - Y)" if "Y \<subseteq> X" and "x \<in> Y" for x and X Y :: "'a set"
    using that by blast
  show ?thesis
    unfolding prog.set_app_def
    apply (rule ag.prog.while[where I="\<lambda>Y s. Y \<subseteq> X \<and> P (X - Y) s" and Q="\<langle>P X\<rangle>" and k="X", simplified])
      apply (rename_tac k)
      apply (rule ag.prog.if)
       apply (rule ag.prog.return)
       apply (simp add: assms; fail)
      apply (rule_tac P="\<lambda>s. k \<subseteq> X \<and> P (X - k) s" in ag.prog.bind[rotated])
       apply (rule_tac Q="\<lambda>x s. x \<in> k" in ag.prog.select_sp, assumption)
       apply (simp add: assms(2) stable.conjI stable.const; fail)
      apply (intro ag.gen_asm)
      apply (rule ag.prog.bind[rotated])
       apply (rule assms(1); force)
      apply (rule ag.pre_pre[OF ag.prog.return])
       apply (simp add: assms(2) stable.conjI stable.const; fail)
      using * apply fastforce
     apply force
    apply (simp add: assms(2))
    done
qed

lemma foldM:
  fixes xs :: "'a list"
  fixes f :: "'b \<Rightarrow> 'a \<Rightarrow> ('s, 'b) prog"
  fixes I :: "'b \<Rightarrow> 'a \<Rightarrow> 's pred"
  fixes P :: "'b \<Rightarrow> 's pred"
  assumes f: "\<And>b x. x \<in> set xs \<Longrightarrow> prog.p2s (f b x) \<le> \<lbrace>I b x\<rbrace>, A \<turnstile> G, \<lbrace>P\<rbrace>"
  assumes P: "\<And>b x s. \<lbrakk>P b s; x \<in> set xs\<rbrakk> \<Longrightarrow> I b x s"
  assumes sP: "\<And>b. stable A (P b)"
  shows "prog.p2s (prog.foldM f b xs) \<le> \<lbrace>P b\<rbrace>, A \<turnstile> G, \<lbrace>P\<rbrace>"
using f P by (induct xs arbitrary: b) (fastforce intro!: ag.prog.bind intro: ag.pre_pre ag.prog.return[OF sP])+

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
