(*<*)
theory TLS
imports
  "Safety_Logic"
begin

(*>*)
section\<open> A Temporal Logic of Safety (TLS) \label{sec:tls} \<close>

text\<open>

We model systems with finite and infinite sequences of states, closed
under stuttering following \<^citet>\<open>"Lamport:1994"\<close>. This theory relates
the safety logic of \S\ref{sec:safety_logic} to the powerset
(quotiented by stuttering) representing properties of these sequences
(see \S\ref{sec:tls-safety}). Most of this story is standard but the
addition of finite sequences does have some impact.

References:
 \<^item> historical motivations for future-time linear temporal logic (LTL): \<^citet>\<open>"MannaPnueli:1991" and "OwickiLamport:1982"\<close>.
 \<^item> a discussion on the merits of proving liveness: \<^url>\<open>https://cs.nyu.edu/acsys/beyond-safety/liveness.htm\<close>

Observations:
 \<^item> Lamport (and Abadi et al) treat infinite stuttering as termination
  \<^item> \<^citet>\<open>\<open>p189\<close> in "Lamport:1999"\<close>: ``we can represent a terminating execution of any system by an
   infinite behavior that ends with a sequence of nothing but stuttering steps. We have no need of
   finite behaviors (finite sequences of states), so we consider only infinite ones.''
  \<^item> this conflates divergence with termination
  \<^item> we separate those concepts here so we can support sequential composition
 \<^item> the traditional account of liveness properties breaks down (see \S\ref{sec:safety_closure})

\<close>


subsection\<open> Stuttering\label{sec:tls-stuttering} \<close>

text\<open>

An infinitary version of \<^const>\<open>trace.natural'\<close>.

Observations:
 \<^item> we need to normalize the agent labels for sequences that infinitely stutter

Source materials:
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/Corec_Examples/LFilter.thy\<close>.
 \<^item> \<^file>\<open>$AFP/Coinductive/Coinductive_List.thy\<close>
 \<^item> \<^file>\<open>$AFP/Coinductive/TLList.thy\<close>
 \<^item> \<^file>\<open>$AFP/TLA/Sequence.thy\<close>.

\<close>

definition trailing :: "'c \<Rightarrow> ('a, 'b) tllist \<Rightarrow> ('c, 'b) tllist" where
  "trailing s xs = (if tfinite xs then TNil (terminal xs) else trepeat s)"

corecursive collapse :: "'s \<Rightarrow> ('a \<times> 's, 'v) tllist \<Rightarrow> ('a \<times> 's, 'v) tllist" where
  "collapse s xs = (if snd ` tset xs \<subseteq> {s} then trailing (undefined, s) xs
               else if snd (thd xs) = s then collapse s (ttl xs)
               else TCons (thd xs) (collapse (snd (thd xs)) (ttl xs)))"
proof -
  have "(LEAST i. s \<noteq> snd (tnth (ttl xs) i)) < (LEAST i. s \<noteq> snd (tnth xs i))"
    if *: "\<not> snd ` tset xs \<subseteq> {s}"
   and **: "snd (thd xs) = s"
   for s and xs :: "('a \<times> 's, 'v) tllist"
  proof -
    from * obtain a s' where "(a, s') \<in> tset xs" and "s \<noteq> s'" by fastforce
    then obtain i where "snd (tnth xs i) \<noteq> s"
      by (atomize_elim, induct rule: tset_induct) (auto intro: exI[of _ 0] exI[of _ "Suc i" for i])
    with * ** have "(LEAST i. s \<noteq> snd (tnth xs i)) = Suc (LEAST i. s \<noteq> snd (tnth xs (Suc i)))"
      by (cases xs) (simp_all add: Least_Suc[where n=i])
    with * show "(LEAST i. s \<noteq> snd (tnth (ttl xs) i)) < (LEAST i. s \<noteq> snd (tnth xs i))"
      by (cases xs) simp_all
  qed
  then show ?thesis
    by (relation "measure (\<lambda>(s, xs). LEAST i. s \<noteq> snd (tnth xs i))"; simp)
qed

setup \<open>Sign.mandatory_path "tmap"\<close>

lemma trailing:
  shows "tmap sf vf (trailing s xs) = trailing (sf s) (tmap sf vf xs)"
by (simp add: trailing_def tmap_trepeat)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tlength"\<close>

lemma trailing:
  shows "tlength (trailing s xs) \<le> tlength xs"
by (fastforce simp: trailing_def dest: not_lfinite_llength)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trailing"\<close>

lemma simps[simp]:
  shows TNil: "trailing s (TNil b) = TNil b"
    and TCons: "trailing s (TCons x xs) = trailing s xs"
    and ttl: "ttl (trailing s xs) = trailing s xs"
    and idempotent: "trailing s (trailing s xs) = trailing s xs"
    and tset_finite: "tset (trailing s xs) = (if tfinite xs then {} else {s})"
    and trepeat: "trailing s (trepeat s) = trepeat s"
by (simp_all add: trailing_def)

lemma eq_TNil_conv:
  shows "trailing s xs = TNil b \<longleftrightarrow> tfinite xs \<and> terminal xs = b"
    and "TNil b = trailing s xs \<longleftrightarrow> tfinite xs \<and> terminal xs = b"
    and "is_TNil (trailing s xs) \<longleftrightarrow> tfinite xs"
by (auto simp: trailing_def dest: is_TNil_tfinite)

lemma eq_TCons_conv:
  shows "trailing s xs = TCons y ys \<longleftrightarrow> \<not>tfinite xs \<and> TCons y ys = trepeat s"
    and "TCons y ys = trailing s xs \<longleftrightarrow> \<not>tfinite xs \<and> TCons y ys = trepeat s"
by (auto simp: trailing_def)

lemma tmap:
  shows "trailing s (tmap sf vf xs) = tmap id vf (trailing s xs)"
by (simp add: trailing_def tmap_trepeat)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "collapse"\<close>

lemma unique:
  assumes "\<And>s xs. f s xs = (if snd ` tset xs \<subseteq> {s} then trailing (undefined, s) xs
                      else if snd (thd xs) = s then f s (ttl xs)
                      else TCons (thd xs) (f (snd (thd xs)) (ttl xs)))"
  shows "f = collapse"
proof(intro ext)
  show "f s xs = collapse s xs" for s xs
  proof(coinduction arbitrary: s xs)
    case (Eq_tllist s xs) show ?case
      apply (induct arg\<equiv>"(s, xs)" arbitrary: s xs rule: collapse.inner_induct)
      apply (subst (1 2 3) assms)
      apply (subst (1 2 3) collapse.code)
      apply simp
      apply (subst (1 2 3) assms)
      apply (subst (1 2 3) collapse.code)
      apply simp
      apply (metis assms collapse.code)
      done
  qed
qed

lemma collapse:
  shows "collapse s (collapse s xs) = collapse s xs"
proof -
  have "(\<lambda>s xs. collapse s (collapse s xs)) = collapse"
    apply (rule collapse.unique)
    apply (subst (1 2 3) collapse.code)
    apply auto
    done
  then show ?thesis
    by (fastforce simp: fun_eq_iff)
qed

lemma simps[simp]:
  shows TNil: "collapse s (TNil b) = TNil b"
    and TCons: "collapse s (TCons x xs) = (if snd x = s then collapse s xs else TCons x (collapse (snd x) xs))"
    and trailing: "collapse s (trailing (undefined, s) xs) = trailing (undefined, s) xs"
by (simp_all add: collapse.code trailing_def)

lemma tshift_stuttering:
  assumes "snd ` set xs \<subseteq> {s}"
  shows "collapse s (tshift xs ys) = collapse s ys"
using assms by (induct xs) simp_all

lemma infinite_trailing:
  assumes "\<not>tfinite xs"
  assumes "snd ` tset xs \<subseteq> {s'}"
  shows "collapse s xs = (if s = s' then trepeat (undefined, s') else TCons (thd xs) (trepeat (undefined, s')))"
using assms by (cases xs) (simp_all add: assms collapse.code trailing_def)

lemma eq_TNil_conv:
  shows "collapse s xs = TNil b \<longleftrightarrow> tfinite xs \<and> snd ` tset xs \<subseteq> {s} \<and> terminal xs = b" (is "?lhs \<longleftrightarrow> ?rhs")
    and "TNil b = collapse s xs \<longleftrightarrow> tfinite xs \<and> snd ` tset xs \<subseteq> {s} \<and> terminal xs = b" (is "?thesis1")
proof -
  show "?lhs \<longleftrightarrow> ?rhs"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
    proof(induct arg\<equiv>"(s, xs)" arbitrary: s xs rule: collapse.inner_induct[case_names step])
      case (step s xs) then show ?case
        by (cases xs; clarsimp split: if_splits)
           (subst (asm) collapse.code; clarsimp simp: trailing.eq_TNil_conv split: if_splits)
    qed
    show "?rhs \<Longrightarrow> ?lhs"
      by (simp add: conj_explode) (induct arbitrary: s rule: tfinite_induct; simp)
  qed
  then show ?thesis1
    by (rule eq_commute_conv)
qed

lemma is_TNil_conv:
  shows "is_TNil (collapse s xs) \<longleftrightarrow> tfinite xs \<and> snd ` tset xs \<subseteq> {s}" (is "?thesis2")
by (simp add: is_TNil_def collapse.eq_TNil_conv)

lemma eq_TConsE:
  assumes "collapse s xs = TCons y ys"
  obtains
    (trailing_stuttering) "\<not> tfinite xs"
                      and "snd ` tset xs = {s}"
                      and "TCons y ys = trepeat (undefined, s)"
  | (step) us ys' where "xs = tshift us (TCons y ys')"
                    and "snd ` set us \<subseteq> {s}"
                    and "snd y \<noteq> s"
                    and "collapse (snd y) ys' = ys"
apply atomize_elim
using assms
proof(induct arg\<equiv>"(s, xs)" arbitrary: s xs rule: collapse.inner_induct[case_names step])
  case (step s xs) show ?case
  proof(cases xs)
    case (TNil v) with step.prems show ?thesis by simp
  next
    case (TCons x xs') show ?thesis
    proof(cases "snd ` tset xs' \<subseteq> {snd x}")
      case True with TCons trans[OF collapse.code[symmetric] step.prems] show ?thesis
        by (force simp: trailing.eq_TCons_conv tshift_eq_TCons_conv split: if_split_asm)
    next
      case False with TCons trans[OF collapse.code[symmetric] step.prems] step.hyps[OF refl]
      show ?thesis
        by (cases x, cases y)
           (simp add: trailing.eq_TCons_conv tshift_eq_TCons_conv trepeat_eq_TCons_conv
                      eq_snd_iff exI[where x="[]"]
               split: if_split_asm; safe; force dest!: spec[where x="(fst x, s) # us" for us])
    qed
  qed
qed

lemma eq_TCons_conv:
  shows "collapse s xs = TCons y ys
     \<longleftrightarrow> (\<not>tfinite xs \<and> snd ` tset xs = {s} \<and> TCons y ys = trepeat (undefined, s))
       \<or> (\<exists>xs' ys'. xs = tshift xs' (TCons y ys') \<and> snd ` set xs' \<subseteq> {s} \<and> snd y \<noteq> s \<and> collapse (snd y) ys' = ys)" (is "?lhs \<longleftrightarrow> ?rhs")
    and "TCons y ys = collapse s xs
     \<longleftrightarrow> (\<not>tfinite xs \<and> snd ` tset xs = {s} \<and> TCons y ys = trepeat (undefined, s))
       \<or> (\<exists>xs' ys'. xs = tshift xs' (TCons y ys') \<and> snd ` set xs' \<subseteq> {s} \<and> snd y \<noteq> s \<and> collapse (snd y) ys' = ys)" (is ?thesis1)
proof -
  show "?lhs \<longleftrightarrow> ?rhs"
    by (auto elim: collapse.eq_TConsE simp: collapse.tshift_stuttering collapse.infinite_trailing)
  then show ?thesis1
    by (rule eq_commute_conv)
qed

lemma tfinite:
  shows "tfinite (collapse s xs) \<longleftrightarrow> tfinite xs" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show ?lhs if ?rhs
    using that by (induct arbitrary: s rule: tfinite_induct) simp_all
  show ?rhs if ?lhs
    using that by (induct "collapse s xs" arbitrary: s xs rule: tfinite_induct)
                  (auto simp: collapse.eq_TNil_conv collapse.eq_TCons_conv trepeat_eq_TCons_conv)
qed

lemma tfinite_conv:
  assumes "collapse s xs = collapse s' xs'"
  shows "tfinite xs \<longleftrightarrow> tfinite xs'"
by (metis assms collapse.tfinite)

lemma terminal:
  shows "terminal (collapse s xs) = terminal xs"
proof(cases "tfinite xs")
  case True
  then obtain i where "tlength xs \<le> enat i"
    using llength_eq_infty_conv_lfinite by fastforce
  then show ?thesis
  proof(induct i arbitrary: s xs)
    case (Suc i s xs) then show ?case
      by (cases xs) (simp_all flip: eSuc_enat)
  qed (clarsimp simp: enat_0 tlength_0_conv)
qed (simp add: collapse.tfinite terminal_tinfinite)

lemma tlength:
  shows "tlength (collapse s xs) \<le> tlength xs"
proof(cases "tfinite xs")
  case True then show ?thesis
    by (induct arbitrary: s rule: tfinite_induct) (auto intro: order.trans[OF _ ile_eSuc])
next
  case False then show ?thesis
    by (fastforce dest: not_lfinite_llength)
qed

lemma tset_memberD:
  assumes "(a, s') \<in> tset (collapse s xs)"
  shows "s' \<in> snd ` tset xs"
using assms
by (induct "collapse s xs" arbitrary: s xs rule: tset_induct)
   (auto simp: collapse.eq_TCons_conv trepeat_eq_TCons_conv tset_tshift image_Un)

lemma tset_memberD2:
  assumes "(a, s') \<in> tset xs"
  shows "s = s' \<or> s' \<in> snd ` tset (collapse s xs)"
using assms by (induct xs arbitrary: a s rule: tset_induct; simp; fast)

lemma tshift:
  shows "collapse s (tshift xs ys) = tshift (trace.natural' s xs) (collapse (trace.final' s xs) ys)"
by (induct xs arbitrary: s) simp_all

lemma trepeat:
  shows "collapse s (trepeat (a, s)) = trepeat (undefined, s)"
by (subst collapse.code) (simp add: trailing_def)

lemma eq_trepeat_conv:
  shows "trepeat (undefined, s) = collapse s xs \<longleftrightarrow> \<not>tfinite xs \<and> snd ` tset xs = {s}" (is "?thesis1")
    and "collapse s xs = trepeat (undefined, s) \<longleftrightarrow> \<not>tfinite xs \<and> snd ` tset xs = {s}" (is "?thesis2")
proof -
  show ?thesis1
    by (rule iffI,
        (subst (asm) trepeat_unfold, simp add: collapse.eq_TCons_conv),
        simp add: collapse.infinite_trailing)
  then show ?thesis2
    by (rule eq_commute_conv)
qed

lemma treplicate:
  shows "collapse s (treplicate i (a, s) v) = TNil v"
by (subst collapse.code) (simp add: trailing.eq_TNil_conv split: nat.split)

lemma eq_tshift_conv:
  shows "collapse s xs = tshift ys zs
     \<longleftrightarrow> (\<exists>xs' xs'' ys'. tshift xs' xs'' = xs \<and> trace.natural' s xs' @ ys' = ys
          \<and> ((\<not>tfinite xs'' \<and> snd ` tset xs'' = {trace.final' s xs'} \<and> tshift ys' zs = trepeat (undefined, trace.final' s xs'))
            \<or> (ys' = [] \<and> collapse (trace.final' s xs') xs'' = zs)))" (is "?lhs \<longleftrightarrow> ?rhs")
    and "tshift ys zs = collapse s xs
     \<longleftrightarrow> (\<exists>xs' xs'' ys'. tshift xs' xs'' = xs \<and> trace.natural' s xs' @ ys' = ys
          \<and> ((\<not>tfinite xs'' \<and> snd ` tset xs'' = {trace.final' s xs'} \<and> tshift ys' zs = trepeat (undefined, trace.final' s xs'))
            \<or> (ys' = [] \<and> collapse (trace.final' s xs') xs'' = zs)))" (is ?thesis1)
proof -
  show "?lhs \<longleftrightarrow> ?rhs"
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
    proof(induct ys arbitrary: s xs)
      case Nil then show ?case
        by (simp add: exI[where x="[]"])
    next
      case (Cons y ys s xs)
      from Cons.prems[simplified] show ?case
      proof(cases rule: collapse.eq_TConsE)
        case trailing_stuttering then show ?thesis
          by (simp add: exI[where x="[]"])
      next
        case (step xs' ys')
        from step(1-3) Cons.hyps[OF step(4)] show ?thesis
          by (fastforce simp: trace.natural'.append tshift_append
                   simp flip: trace.natural'.eq_Nil_conv
                       intro: exI[where x="xs' @ y # ys''" for ys''])
      qed
    qed
    show "?rhs \<Longrightarrow> ?lhs"
      by (auto simp: collapse.tshift tshift_append collapse.infinite_trailing)
  qed
  then show ?thesis1
    by (rule eq_commute_conv)
qed

lemma eq_collapse_ttake_dropn_conv:
  shows "collapse s xs = collapse s ys
     \<longleftrightarrow> (\<exists>j. trace.natural' s (fst (ttake i xs)) = trace.natural' s (fst (ttake j ys))
            \<and> snd (ttake i xs) = snd (ttake j ys)
            \<and> collapse (trace.final' s (fst (ttake i xs))) (tdropn i xs)
            = collapse (trace.final' s (fst (ttake i xs))) (tdropn j ys))" (is "?lhs \<longleftrightarrow> (\<exists>j. ?rhs i j s xs ys)")
proof(rule iffI)
  show "?lhs \<Longrightarrow> (\<exists>j. ?rhs i j s xs ys)"
  proof(induct i arbitrary: s xs ys)
    case (Suc i s xs ys) show ?case
    proof(cases xs)
      case (TNil b) with Suc.prems show ?thesis
        by (fastforce intro: exI[where x="case tlength ys of \<infinity> \<Rightarrow> undefined | enat j \<Rightarrow> Suc j"]
                       simp: collapse.eq_TNil_conv trace.natural'.eq_Nil_conv
                             ttake_eq_Some_conv tfinite_tlength_conv tdropn_tlength
                       dest: in_set_ttakeD)
    next
      case (TCons x xs') show ?thesis
      proof(cases "snd x = s")
        case True with Suc TCons show ?thesis by simp
      next
        case False
        note Suc.prems TCons False
        moreover from calculation
        obtain us ys'
          where "ys = tshift us (TCons x ys')"
            and "snd ` set us \<subseteq> {s}"
            and "collapse (snd x) ys' = collapse (snd x) xs'"
          by (auto simp: collapse.eq_TCons_conv trepeat_eq_TCons_conv)
        moreover from calculation Suc.hyps[of "snd x" "xs'" "ys'"]
        obtain j where "?rhs i j (snd x) xs' ys'"
          by presburger
        ultimately show ?thesis
          by (auto simp: ttake_tshift trace.natural'.append tdropn_tshift
              simp flip: trace.natural'.eq_Nil_conv
                  intro: exI[where x="Suc (length us) + j"])
      qed
    qed
  qed (simp add: exI[where x=0])
  show "\<exists>j. ?rhs i j s xs ys \<Longrightarrow> ?lhs"
    by (metis collapse.tshift trace.final'.natural' tshift_fst_ttake_tdropn_id)
qed

lemmas eq_collapse_ttake_dropnE = exE[OF iffD1[OF collapse.eq_collapse_ttake_dropn_conv]]

lemma tshift_tdropn:
  assumes "trace.natural' s (fst (ttake i xs)) = trace.natural' s ys"
  shows "collapse s (tshift ys (tdropn i xs)) = collapse s xs"
by (metis assms collapse.tshift trace.final'.natural' tshift_fst_ttake_tdropn_id)

lemma map_collapse:
  shows "collapse (sf s) (tmap (map_prod af sf) vf (collapse s xs))
       = collapse (sf s) (tmap (map_prod af sf) vf xs)" (is "?lhs s xs = ?rhs s xs")
proof(coinduction arbitrary: s xs)
  case (Eq_tllist s xs) show ?case
  proof(intro conjI; (intro impI)?)
    have *: "sf s' = sf s"
      if "tfinite xs" and "sf ` snd ` tset (collapse s xs) \<subseteq> {sf s}" and "(a, s') \<in> tset xs"
    for a s s'
      using that by (induct arbitrary: s rule: tfinite_induct; clarsimp split: if_split_asm; metis)
    show "is_TNil (?lhs s xs) \<longleftrightarrow> is_TNil (?rhs s xs)"
      by (rule iffI,
          fastforce dest!: * simp: collapse.is_TNil_conv collapse.tfinite tllist.set_map snd_image_map_prod,
          fastforce dest!: collapse.tset_memberD simp: collapse.is_TNil_conv collapse.tfinite tllist.set_map)
    show "terminal (?lhs s xs) = terminal (?rhs s xs)"
      if "is_TNil (?lhs s xs)" and "is_TNil (?rhs s xs)"
      using that by (simp add: collapse.is_TNil_conv collapse.terminal)
    assume "\<not>is_TNil (?lhs s xs)" and "\<not>is_TNil (?rhs s xs)"
    then obtain y ys z zs where l: "?lhs s xs = TCons y ys" and r: "?rhs s xs = TCons z zs"
      by (simp add: tllist.disc_eq_case(2) split: tllist.split_asm)
    from l show "thd (?lhs s xs) = thd (?rhs s xs)
              \<and> (\<exists>s' xs'. ttl (?lhs s xs) = ?lhs s' xs' \<and> ttl (?rhs s xs) = ?rhs s' xs')"
    proof(cases rule: collapse.eq_TConsE)
      case trailing_stuttering
      note left = this
      from r show ?thesis
      proof(cases rule: collapse.eq_TConsE)
        case trailing_stuttering
        from left(3) trailing_stuttering(3) show ?thesis
          by (fold l r) (simp; metis)
      next
        case (step us zs')
        from left(2) step(1,3) have False
          by (clarsimp simp: tset_tshift tset_tmap tmap_eq_tshift_conv TCons_eq_tmap_conv collapse.tshift
                      split: if_split_asm)
             (use step(2) in \<open>fastforce simp flip: trace.final'.map[where af=af]\<close>)
        then show ?thesis ..
      qed
    next
      case (step us ys')
      note left = this
      from r show ?thesis
      proof(cases rule: collapse.eq_TConsE)
        case trailing_stuttering
        have False
          if "sf s' \<noteq> sf s"
         and "(\<lambda>x. sf (snd x)) ` tset xs = {sf s}"
         and "(\<lambda>x. sf (snd x)) ` set us \<subseteq> {sf s}"
         and "collapse s xs = tshift us (TCons (a, s') vs)"
         for a s' us vs
          using that
          by (force simp: tset_tshift
                   dest!: arg_cong[where f="\<lambda>xs. s' \<in> snd ` tset xs"] collapse.tset_memberD
                   intro: imageI[where f="\<lambda>x. sf (snd x)"])
        with l left(3) trailing_stuttering(2) have False
          by (fastforce simp: tset_tmap tmap_eq_tshift_conv TCons_eq_tmap_conv collapse.eq_TCons_conv
                              trepeat_eq_TCons_conv snd_image_map_prod image_image)
        then show ?thesis ..
      next
        case (step vs zs')
        from left step show ?thesis
          unfolding l r
          apply (clarsimp simp: tmap_eq_tshift_conv collapse.tshift TCons_eq_tmap_conv
                                tmap_tshift trace.natural'.map_natural'[where af=af and sf=sf and s=s]
                                iffD2[OF trace.natural'.eq_Nil_conv(1)]
                         dest!: arg_cong[where f="\<lambda>xs. collapse (sf s) (tmap (map_prod af sf) vf xs)"]
                         split: if_split_asm)
            apply (use step(2) in \<open>fastforce simp flip: trace.final'.map[where af=af]\<close>)
           apply (metis list.set_map trace.final'.idle trace.final'.map trace.final'.natural')
          apply metis
          done
      qed
    qed
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "behavior"\<close>

definition natural :: "('a, 's, 'v) behavior.t \<Rightarrow> ('a, 's, 'v) behavior.t" ("\<natural>\<^sub>T") where
  "\<natural>\<^sub>T\<omega> = behavior.B (behavior.init \<omega>) (collapse (behavior.init \<omega>) (behavior.rest \<omega>))"

setup \<open>Sign.mandatory_path "sset"\<close>

lemma collapse[simp]:
  shows "behavior.sset (behavior.B s (collapse s xs)) = behavior.sset (behavior.B s xs)"
by (auto simp: behavior.sset.simps collapse.tset_memberD dest: collapse.tset_memberD2[where s=s])

lemma natural[simp]:
  shows "behavior.sset (\<natural>\<^sub>T\<omega>) = behavior.sset \<omega>"
by (simp add: behavior.natural_def)

lemma continue:
  shows "behavior.sset (\<sigma> @-\<^sub>B xs) = trace.sset \<sigma> \<union> (case trace.term \<sigma> of None \<Rightarrow> snd ` tset xs | Some _ \<Rightarrow> {})"
by (cases \<sigma>)
   (simp add: behavior.sset.simps behavior.continue_def tshift2_def tset_tshift image_Un trace.sset.simps
       split: option.split)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "natural"\<close>

lemma sel[simp]:
  shows "behavior.init (\<natural>\<^sub>T\<omega>) = behavior.init \<omega>"
    and "behavior.rest (\<natural>\<^sub>T\<omega>) = collapse (behavior.init \<omega>) (behavior.rest \<omega>)"
by (simp_all add: behavior.natural_def)

lemma TNil:
  shows "\<natural>\<^sub>T(behavior.B s (TNil v)) = behavior.B s (TNil v)"
by (simp add: behavior.natural_def)

lemma tfinite:
  shows "tfinite (behavior.rest (\<natural>\<^sub>T \<omega>)) \<longleftrightarrow> tfinite (behavior.rest \<omega>)"
by (simp add: behavior.natural_def collapse.tfinite)

lemma continue:
  shows "\<natural>\<^sub>T(\<sigma> @-\<^sub>B xs) = \<natural>\<sigma> @-\<^sub>B (collapse (trace.final \<sigma>) xs)"
by (simp add: behavior.t.expand tshift2_def collapse.tshift split: option.split)

lemma tshift:
  shows "\<natural>\<^sub>T(behavior.B s (tshift as xs)) = behavior.B s (collapse s (tshift as xs))"
by (simp add: behavior.natural_def)

lemma trepeat:
  shows "\<natural>\<^sub>T(behavior.B s (trepeat (a, s))) = behavior.B s (trepeat (undefined, s))"
by (simp add: behavior.natural_def collapse.trepeat)

lemma treplicate:
  shows "\<natural>\<^sub>T(behavior.B s (treplicate i (a, s) v)) = behavior.B s (TNil v)"
by (simp add: behavior.natural_def collapse.treplicate)

lemma map_natural:
  shows "\<natural>\<^sub>T(behavior.map af sf vf (\<natural>\<^sub>T\<omega>)) = \<natural>\<^sub>T(behavior.map af sf vf \<omega>)"
by (simp add: behavior.natural_def collapse.map_collapse)

lemma idle:
  assumes "behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}"
  shows "\<natural>\<^sub>T\<omega> = behavior.B (behavior.init \<omega>) (trailing (undefined, behavior.init \<omega>) (behavior.rest \<omega>))"
using assms by (cases \<omega>) (simp add: behavior.natural_def behavior.sset.simps collapse.code)

setup \<open>Sign.parent_path\<close>

interpretation stuttering: galois.image_vimage_idempotent "\<natural>\<^sub>T"
by standard (simp add: behavior.natural_def collapse.collapse)

setup \<open>Sign.mandatory_path "stuttering"\<close>

setup \<open>Sign.mandatory_path "equiv"\<close>

abbreviation syn :: "('a, 's, 'v) behavior.t \<Rightarrow> ('a, 's, 'v) behavior.t \<Rightarrow> bool" (infix "\<simeq>\<^sub>T" 50) where
  "\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2 \<equiv> behavior.stuttering.equivalent \<omega>\<^sub>1 \<omega>\<^sub>2"

lemma map:
  assumes "\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2"
  shows "behavior.map af sf vf \<omega>\<^sub>1 \<simeq>\<^sub>T behavior.map af sf vf \<omega>\<^sub>2"
by (metis assms behavior.natural.map_natural)

lemma takeE:
  assumes "\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2"
  obtains j where "behavior.take i \<omega>\<^sub>1 \<simeq>\<^sub>S behavior.take j \<omega>\<^sub>2"
using assms
by (fastforce simp: behavior.natural_def trace.natural_def
              elim: collapse.eq_collapse_ttake_dropnE[where s="behavior.init \<omega>\<^sub>2" and i=i and xs="behavior.rest \<omega>\<^sub>1" and ys="behavior.rest \<omega>\<^sub>2"])

lemma idle_dropn:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  assumes "behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}"
  shows "\<omega> \<simeq>\<^sub>T \<omega>'"
proof -
  from behavior.sset.dropn_le[OF assms(1)] assms(2)
  have "behavior.sset \<omega>' \<subseteq> {behavior.init \<omega>'}" and "behavior.init \<omega>' = behavior.init \<omega>"
    using behavior.t.set_sel(2) subset_singletonD by fastforce+
  from assms(1) behavior.natural.idle[OF assms(2)] behavior.natural.idle[OF this(1)] this(2)
  show ?thesis
    by (simp add: trailing_def)
       (metis  behavior.dropn.tfiniteD behavior.dropn.eq_Some_tdropnD terminal_tdropn)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trace.stuttering.equiv.behavior"\<close>

lemma takeE:
  fixes \<sigma> :: "('a, 's, 'v) trace.t"
  assumes "behavior.take i \<omega> \<simeq>\<^sub>S \<sigma>"
  obtains \<omega>' j where "\<omega> \<simeq>\<^sub>T \<omega>'" and "\<sigma> = behavior.take j \<omega>'"
proof atomize_elim
  have "\<exists>ys j. collapse s xs = collapse s ys \<and> trace.T s xs' (snd (ttake i xs)) = behavior.take j (behavior.B s ys)"
    if "trace.natural' s (fst (ttake i xs)) = trace.natural' s xs'"
   for s xs' and xs :: "('a \<times> 's, 'v) tllist"
    using that
    by (cases "snd (ttake i xs)")
       (fastforce simp: behavior.take.tshift ttake_eq_Some_conv tdropn_tlength
                        trace.take.all trace.take.all_iff
                 intro: exI[where x="tshift xs' (tdropn i xs)"]
                        exI[where x="length xs'"] exI[where x="Suc (length xs')"]
                  dest: collapse.tshift_tdropn)+
  with assms show "\<exists>\<omega>' j. \<omega> \<simeq>\<^sub>T \<omega>' \<and> \<sigma> = behavior.take j \<omega>'"
    by (cases \<sigma>)
       (clarsimp simp: behavior.natural_def trace.natural_def behavior.split_Ex)
qed

lemmas rev_takeE = trace.stuttering.equiv.behavior.takeE[OF sym]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trace.natural.behavior"\<close>

lemma takeE:
  fixes \<omega> :: "('a, 's, 'v) behavior.t"
  obtains j where "\<natural>(behavior.take i \<omega>) = behavior.take j (\<natural>\<^sub>T\<omega>)"
proof atomize_elim
  have "\<exists>j. trace.natural' s (fst (ttake i xs)) = fst (ttake j (collapse s xs))
          \<and> snd (ttake i xs) = snd (ttake j (collapse s xs))"
   for s and xs :: "('a \<times> 's, 'v) tllist"
  proof(induct i arbitrary: s xs)
    case 0 show ?case by (fastforce simp: ttake_eq_Nil_conv)
  next
    case (Suc i s xs) show ?case
    proof(cases xs)
      case (TCons x' xs') with Suc[where s="snd x'" and xs=xs'] show ?thesis
        by (fastforce intro: exI[where x="Suc j" for j])
    qed (simp add: exI[where x=1])
  qed
  then show "\<exists>j. \<natural> (behavior.take i \<omega>) = behavior.take j (\<natural>\<^sub>T \<omega>)"
    by (simp add: behavior.take_def trace.natural_def split_def)
qed

setup \<open>Sign.parent_path\<close>


subsection\<open> The \<^emph>\<open>('a, 's, 'v) tls\<close> lattice \label{sec:tls-tls} \<close>

text\<open>

This is our version of Lamport's TLA lattice which we treat in a ``semantic'' way similarly to
\<^citet>\<open>"AbadiMerz:1996"\<close>.

Observations:
 \<^item> there is a somewhat natural partial ordering on the \<open>tls\<close> lattice induced by the connection with
   the \<open>spec\<close> lattice (see \S\ref{sec:tls-safety} and \S\ref{sec:safety_closure}) which we do not use

\<close>

typedef ('a, 's, 'v) tls = "behavior.stuttering.closed :: ('a, 's, 'v) behavior.t set set"
morphisms unTLS TLS
by blast

setup_lifting type_definition_tls

instantiation tls :: (type, type, type) complete_boolean_algebra
begin

lift_definition bot_tls :: "('a, 's, 'v) tls" is empty ..
lift_definition top_tls :: "('a, 's, 'v) tls" is UNIV ..
lift_definition sup_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" is sup ..
lift_definition inf_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" is inf ..
lift_definition less_eq_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> bool" is less_eq .
lift_definition less_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> bool" is less .
lift_definition Inf_tls :: "('a, 's, 'v) tls set \<Rightarrow> ('a, 's, 'v) tls" is Inf ..
lift_definition Sup_tls :: "('a, 's, 'v) tls set \<Rightarrow> ('a, 's, 'v) tls" is "\<lambda>X. Sup X \<squnion> behavior.stuttering.cl {}" ..
lift_definition minus_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" is minus ..
lift_definition uminus_tls :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" is uminus ..

instance
by (standard; transfer;
    auto simp: behavior.stuttering.cl_bot
               behavior.stuttering.closed_strict_complete_distrib_lattice_axiomI[OF behavior.stuttering.cl_bot])

end

declare
  SUPE[where 'a="('a, 's, 'v) tls", intro!]
  SupE[where 'a="('a, 's, 'v) tls", intro!]
  Sup_le_iff[where 'a="('a, 's, 'v) tls", simp]
  SupI[where 'a="('a, 's, 'v) tls", intro]
  SUPI[where 'a="('a, 's, 'v) tls", intro]
  rev_SUPI[where 'a="('a, 's, 'v) tls", intro?]
  INFE[where 'a="('a, 's, 'v) tls", intro]

setup \<open>Sign.mandatory_path "tls"\<close>

lemma boolean_implication_transfer[transfer_rule]:
  shows "rel_fun (pcr_tls (=) (=) (=)) (rel_fun (pcr_tls (=) (=) (=)) (pcr_tls (=) (=) (=))) (\<^bold>\<longrightarrow>\<^sub>B) (\<^bold>\<longrightarrow>\<^sub>B)"
unfolding boolean_implication_def by transfer_prover

lemma bot_not_top:
  shows "\<bottom> \<noteq> (\<top> :: ('a, 's, 'v) tls)"
by transfer simp

setup \<open>Sign.parent_path\<close>


subsection\<open> Irreducible elements\label{sec:tls-singleton} \<close>

setup \<open>Sign.mandatory_path "raw"\<close>

definition singleton :: "('a, 's, 'v) behavior.t \<Rightarrow> ('a, 's, 'v) behavior.t set" where
  "singleton \<omega> = behavior.stuttering.cl {\<omega>}"

lemma singleton_le_conv:
  shows "raw.singleton \<sigma>\<^sub>1 \<le> raw.singleton \<sigma>\<^sub>2 \<longleftrightarrow> \<natural>\<^sub>T\<sigma>\<^sub>1 = \<natural>\<^sub>T\<sigma>\<^sub>2"
by (rule iffI; fastforce simp: raw.singleton_def simp flip: behavior.stuttering.cl_axiom
                         dest: behavior.stuttering.clE behavior.stuttering.equiv_cl_singleton)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tls"\<close>

lift_definition singleton :: "('a, 's, 'v) behavior.t \<Rightarrow> ('a, 's, 'v) tls" ("\<lblot>_\<rblot>\<^sub>T" [0]) is raw.singleton
by (simp add: raw.singleton_def)

abbreviation singleton_behavior_syn :: "'s \<Rightarrow> ('a \<times> 's, 'v) tllist \<Rightarrow> ('a, 's, 'v) tls" ("\<lblot>_, _\<rblot>\<^sub>T" [0, 0]) where
  "\<lblot>s, xs\<rblot>\<^sub>T \<equiv> \<lblot>behavior.B s xs\<rblot>\<^sub>T"

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma Sup_prime:
  shows "Sup_prime \<lblot>\<omega>\<rblot>\<^sub>T"
by (clarsimp simp: Sup_prime_on_def)
   (transfer; auto simp: raw.singleton_def behavior.stuttering.cl_bot
                  elim!: Sup_prime_onE[OF behavior.stuttering.Sup_prime_on_singleton])

lemma nchotomy:
  shows "\<exists>X\<in>behavior.stuttering.closed. x = \<Squnion>(tls.singleton ` X)"
by transfer
   (use behavior.stuttering.closed_conv in \<open>auto simp add: raw.singleton_def
                                                simp flip: behavior.stuttering.distributive\<close>)

lemmas exhaust = bexE[OF tls.singleton.nchotomy]

lemma collapse[simp]:
  shows "\<Squnion>(tls.singleton ` {\<omega>. \<lblot>\<omega>\<rblot>\<^sub>T \<le> P}) = P"
by (rule tls.singleton.exhaust[of P]) (simp add: antisym SUP_le_iff SUP_upper)

lemmas not_bot = Sup_prime_not_bot[OF tls.singleton.Sup_prime] \<comment>\<open> Non-triviality \<close>

setup \<open>Sign.parent_path\<close>

lemma singleton_le_ext_conv:
  shows "P \<le> Q \<longleftrightarrow> (\<forall>\<omega>. \<lblot>\<omega>\<rblot>\<^sub>T \<le> P \<longrightarrow> \<lblot>\<omega>\<rblot>\<^sub>T \<le> Q)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?rhs \<Longrightarrow> ?lhs"
    by (rule tls.singleton.exhaust[where x=P]; rule tls.singleton.exhaust[where x=Q]; blast)
qed fastforce

lemmas singleton_le_conv = raw.singleton_le_conv[transferred]
lemmas singleton_le_extI = iffD2[OF tls.singleton_le_ext_conv, rule_format]

lemma singleton_eq_conv[simp]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T = \<lblot>\<omega>'\<rblot>\<^sub>T \<longleftrightarrow> \<omega> \<simeq>\<^sub>T \<omega>'"
using tls.singleton_le_conv by (force intro: antisym)

lemma singleton_cong:
  assumes "\<omega> \<simeq>\<^sub>T \<omega>'"
  shows "\<lblot>\<omega>\<rblot>\<^sub>T = \<lblot>\<omega>'\<rblot>\<^sub>T"
using assms by simp

setup \<open>Sign.mandatory_path "singleton"\<close>

named_theorems le_conv \<open> simplification rules for \<open>\<lblot>\<sigma>\<rblot>\<^sub>T \<le> const \<dots>\<close> \<close>

lemma boolean_implication_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<sigma>\<rblot>\<^sub>T \<le> P \<^bold>\<longrightarrow>\<^sub>B Q \<longleftrightarrow> (\<lblot>\<sigma>\<rblot>\<^sub>T \<le> P \<longrightarrow> \<lblot>\<sigma>\<rblot>\<^sub>T \<le> Q)"
by transfer
   (auto simp: raw.singleton_def boolean_implication.set_alt_def
        elim!: behavior.stuttering.clE behavior.stuttering.closed_in[OF _ sym])

lemmas antisym = antisym[OF tls.singleton_le_extI tls.singleton_le_extI]

lemmas top = tls.singleton.collapse[of \<top>, simplified, symmetric]

lemma simps[simp]:
  shows "\<lblot>\<natural>\<^sub>T\<omega>\<rblot>\<^sub>T = \<lblot>\<omega>\<rblot>\<^sub>T"
    and "\<lblot>s, xs\<rblot>\<^sub>T \<le> \<lblot>s, collapse s xs\<rblot>\<^sub>T"
    and "snd ` set ys \<subseteq> {s} \<Longrightarrow> \<lblot>s, tshift ys xs\<rblot>\<^sub>T = \<lblot>s, xs\<rblot>\<^sub>T"
    and "\<lblot>s, TCons (a, s) xs\<rblot>\<^sub>T = \<lblot>s, xs\<rblot>\<^sub>T"
by (simp_all add: antisym tls.singleton_le_conv behavior.natural_def
                  behavior.stuttering.f_idempotent collapse.collapse collapse.tshift_stuttering)

lemmas Sup_irreducible = iffD1[OF heyting.Sup_prime_Sup_irreducible_iff tls.singleton.Sup_prime]
lemmas sup_irreducible = Sup_irreducible_on_imp_sup_irreducible_on[OF tls.singleton.Sup_irreducible, simplified]
lemmas Sup_leE[elim] = Sup_prime_onE[OF tls.singleton.Sup_prime, simplified]
lemmas sup_le_conv[simp] = sup_irreducible_le_conv[OF tls.singleton.sup_irreducible]
lemmas Sup_le_conv[simp] = Sup_prime_on_conv[OF tls.singleton.Sup_prime, simplified]
lemmas compact_point = Sup_prime_is_compact[OF tls.singleton.Sup_prime]
lemmas compact[cont_intro] = compact_points_are_ccpo_compact[OF tls.singleton.compact_point]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> The idle process\label{sec:tls-idle} \<close>

text\<open>

The idle process contains no transitions and does not terminate.

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

definition idle :: "('a, 's, 'v) behavior.t set" where
  "idle = (\<Union>s. raw.singleton (behavior.B s (trepeat (undefined, s))))"

lemma idle_alt_def:
  shows "raw.idle = {\<omega>. \<not>tfinite (behavior.rest \<omega>) \<and> behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}}" (is "?lhs = ?rhs")
proof(rule antisym[OF _ subsetI])
  show "?lhs \<subseteq> ?rhs"
    by (force simp: raw.idle_def raw.singleton_def behavior.split_all behavior.natural_def
                    behavior.sset.simps collapse.trepeat collapse.eq_trepeat_conv
              elim: behavior.stuttering.clE
              dest: collapse.tfinite_conv)
  show "\<omega> \<in> ?lhs" if "\<omega> \<in> ?rhs" for \<omega>
    using that
    by (cases \<omega>)
       (auto simp: raw.idle_def raw.singleton_def behavior.natural_def behavior.sset.simps
                   behavior.stuttering.idemI collapse.infinite_trailing
             elim: behavior.stuttering.clE
            intro: exI[where x="behavior.init \<omega>"])
qed

setup \<open>Sign.mandatory_path "idle"\<close>

lemma not_tfinite:
  assumes "\<omega> \<in> raw.idle"
  shows "\<not>tfinite (behavior.rest \<omega>)"
using assms by (simp add: raw.idle_alt_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "behavior.stuttering.closed"\<close>

lemma idle[iff]:
  shows "raw.idle \<in> behavior.stuttering.closed"
by (simp add: raw.idle_def raw.singleton_def
              behavior.stuttering.closed_UNION[simplified behavior.stuttering.cl_bot, simplified])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tls"\<close>

lift_definition idle :: "('a, 's, 'v) tls" is raw.idle ..

lemma idle_alt_def:
  shows "tls.idle = (\<Squnion>s. \<lblot>s, trepeat (undefined, s)\<rblot>\<^sub>T)"
by transfer (simp add: raw.idle_def behavior.stuttering.cl_bot)

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma idle_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.idle \<longleftrightarrow> \<not>tfinite (behavior.rest \<omega>) \<and> behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}"
by transfer (simp add: raw.singleton_def behavior.stuttering.least_conv; simp add: raw.idle_alt_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma minimal_le:
  shows "\<lblot>s, trepeat (undefined, s)\<rblot>\<^sub>T \<le> tls.idle"
by (simp add: tls.singleton.idle_le_conv behavior.sset.simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Temporal Logic for \<^emph>\<open>('a, 's, 'v) tls\<close> \label{sec:tls-ltl} \<close>

text\<open>

The following is a straightforward shallow embedding of the
now-traditional anchored semantics of LTL \<^citet>\<open>"MannaPnueli:1988"\<close>.

References:
 \<^item> \<^file>\<open>$AFP/TLA/Liveness.thy\<close>
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/TLA/TLA.thy\<close>
 \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Linear_temporal_logic\<close>
 \<^item> \<^citet>\<open>"KroegerMerz:2008"\<close>
 \<^item> \<^citet>\<open>"WarfordVegaStaley:2020"\<close>

Observations:
 \<^item> as we lack next/X/\<open>\<circle>\<close> (due to stuttering closure) we do not have induction for \<open>\<U>\<close> (until)
 \<^item> \<^citet>\<open>"Lamport:1994"\<close> omitted the LTL ``until'' operator from TLA as he considered it too hard to use
 \<^item> As \<^citet>\<open>"DeGiacomoVardi:2013"\<close> observe, things get non-standard on finite traces
  \<^item> see \S\ref{sec:safety_closure} for an example
  \<^item> \<^citet>\<open>"Maier:2004"\<close> provides an alternative account

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

definition state_prop :: "'s pred \<Rightarrow> ('a, 's, 'v) behavior.t set" where
  "state_prop P = {\<omega>. P (behavior.init \<omega>)}"

definition
  until :: "('a, 's, 'v) behavior.t set \<Rightarrow> ('a, 's, 'v) behavior.t set \<Rightarrow> ('a, 's, 'v) behavior.t set"
where
  "until P Q = {\<omega> . \<exists>i. \<exists>\<omega>'\<in>Q. behavior.dropn i \<omega> = Some \<omega>' \<and> (\<forall>j<i. the (behavior.dropn j \<omega>) \<in> P)}"

definition
  eventually :: "('a, 's, 'v) behavior.t set \<Rightarrow> ('a, 's, 'v) behavior.t set"
where
  "eventually P = raw.until UNIV P"

definition
  always :: "('a, 's, 'v) behavior.t set \<Rightarrow> ('a, 's, 'v) behavior.t set"
where
  "always P = -raw.eventually (-P)"

abbreviation (input) "unless P Q \<equiv> raw.until P Q \<union> raw.always P"

definition terminated :: "('a, 's, 'v) behavior.t set" where
  "terminated = {\<omega>. tfinite (behavior.rest \<omega>) \<and> behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}}"

lemma untilI:
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  assumes "\<omega>' \<in> Q"
  assumes "\<And>j. j < i \<Longrightarrow> the (behavior.dropn j \<omega>) \<in> P"
  shows "\<omega> \<in> raw.until P Q"
using assms unfolding raw.until_def by blast

lemma eventually_alt_def:
  shows "raw.eventually P = {\<omega> . \<exists>\<omega>'\<in>P. \<exists>i. behavior.dropn i \<omega> = Some \<omega>'}"
by (auto simp: raw.eventually_def raw.until_def)

lemma always_alt_def:
  shows "raw.always P = {\<omega> . \<forall>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<longrightarrow> \<omega>' \<in> P}"
by (auto simp: raw.always_def raw.eventually_alt_def)

lemma alwaysI:
  assumes "\<And>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<Longrightarrow> \<omega>' \<in> P"
  shows "\<omega> \<in> raw.always P"
by (simp add: raw.always_alt_def assms)

lemma alwaysD:
  assumes "\<omega> \<in> raw.always P"
  assumes "behavior.dropn i \<omega> = Some \<omega>'"
  shows "\<omega>' \<in> P"
using assms by (simp add: raw.always_alt_def)

setup \<open>Sign.mandatory_path "state_prop"\<close>

lemma monotone:
  shows "mono raw.state_prop"
by (fastforce intro: monoI simp: raw.state_prop_def)

lemma simps:
  shows
    "raw.state_prop \<langle>False\<rangle> = {}"
    "raw.state_prop \<bottom> = {}"
    "raw.state_prop \<langle>True\<rangle> = UNIV"
    "raw.state_prop \<top> = UNIV"
    "- raw.state_prop P = raw.state_prop (- P)"
    "raw.state_prop P \<union> raw.state_prop Q = raw.state_prop (P \<squnion> Q)"
    "raw.state_prop P \<inter> raw.state_prop Q = raw.state_prop (P \<sqinter> Q)"
    "(raw.state_prop P \<^bold>\<longrightarrow>\<^sub>B raw.state_prop Q) = raw.state_prop (P \<^bold>\<longrightarrow>\<^sub>B Q)"
by (auto simp: raw.state_prop_def boolean_implication.set_alt_def)

lemma Inf:
  shows "raw.state_prop (\<Sqinter>X) = \<Inter>(raw.state_prop ` X)"
by (fastforce simp: raw.state_prop_def)

lemma Sup:
  shows "raw.state_prop (\<Squnion>X) = \<Union>(raw.state_prop ` X)"
by (fastforce simp: raw.state_prop_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "terminated"\<close>

lemma inf_always_le:
  fixes P :: "('a, 's, 'v) behavior.t set"
  assumes "P \<in> behavior.stuttering.closed"
  shows "raw.terminated \<inter> P \<subseteq> raw.always P"
by (rule subsetI[OF raw.alwaysI])
   (auto simp: raw.terminated_def
         elim: behavior.stuttering.closed_in[OF _ _ assms] behavior.stuttering.equiv.idle_dropn)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "until"\<close>

lemma base:
  shows "\<omega> \<in> Q \<Longrightarrow> \<omega> \<in> raw.until P Q"
    and "Q \<subseteq> raw.until P Q"
by (force simp: raw.until_def)+

lemma step:
  assumes "\<omega> \<in> P"
  assumes "behavior.tl \<omega> = Some \<omega>'"
  assumes "\<omega>' \<in> raw.until P Q"
  shows "\<omega> \<in> raw.until P Q"
proof -
  from \<open>\<omega>' \<in> raw.until P Q\<close>
  obtain i \<omega>''
    where "\<omega>'' \<in> Q" and "\<forall>j<i. the (behavior.dropn j \<omega>') \<in> P" and "behavior.dropn i \<omega>' = Some \<omega>''"
    by (clarsimp simp: raw.until_def)
  with assms(1,2) show ?thesis
    by (clarsimp simp: raw.until_def behavior.dropn.Suc less_Suc_eq_0_disj
               intro!: exI[where x="Suc i"])
qed

lemmas intro[intro] =
  raw.until.base
  raw.until.step

lemma induct[case_names base step, consumes 1, induct set: raw.until]:
  assumes "\<omega> \<in> raw.until P Q"
  assumes base: "\<And>\<omega>. \<omega> \<in> Q \<Longrightarrow> R \<omega>"
  assumes step: "\<And>\<omega> \<omega>'. \<lbrakk>\<omega> \<in> P; behavior.tl \<omega> = Some \<omega>'; \<omega>' \<in> raw.until P Q; R \<omega>'\<rbrakk> \<Longrightarrow> R \<omega>"
  shows "R \<omega>"
proof -
  from \<open>\<omega> \<in> raw.until P Q\<close> obtain \<omega>' i
    where "behavior.dropn i \<omega> = Some \<omega>'" and "\<omega>' \<in> Q" and "\<forall>j<i. the (behavior.dropn j \<omega>) \<in> P"
    unfolding raw.until_def by blast
  then show ?thesis
  proof(induct i arbitrary: \<omega>)
    case 0 then show ?case
      by (force intro: base)
  next
    case Suc from Suc.prems show ?case
      by (fastforce intro: step Suc.hyps dest: spec[where x="Suc j" for j]
                     simp: behavior.dropn.Suc raw.until_def
                    split: Option.bind_split_asm)
  qed
qed

lemma mono:
  assumes "P \<subseteq> P'"
  assumes "Q \<subseteq> Q'"
  shows "raw.until P Q \<subseteq> raw.until P' Q'"
unfolding raw.until_def using assms by blast

lemma botL:
  shows "raw.until {} Q = Q"
by (force simp: raw.until_def)

lemma botR:
  shows "raw.until P {} = {}"
by (force simp: raw.until_def)

lemma untilR:
  shows "raw.until P (raw.until P Q) = raw.until P Q" (is "?lhs = ?rhs")
proof(rule antisym[OF subsetI])
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega> using that by induct blast+
  show "?rhs \<subseteq> ?lhs" by blast
qed

lemma InfL_not_empty:
  assumes "X \<noteq> {}"
  shows "raw.until (\<Inter>X) Q = (\<Inter>x\<in>X. raw.until x Q)" (is "?lhs = ?rhs")
proof(rule antisym[OF _ subsetI])
  show "?lhs \<subseteq> ?rhs"
    by (simp add: INT_greatest Inter_lower raw.until.mono)
  show "\<omega> \<in> ?lhs" if "\<omega> \<in> ?rhs" for \<omega>
  proof -
    from \<open>X \<noteq> {}\<close> obtain P where "P \<in> X" by blast
    with that obtain i \<omega>'
      where *: "behavior.dropn i \<omega> = Some \<omega>'" "\<omega>' \<in> Q" "\<forall>j<i. the (behavior.dropn j \<omega>) \<in> P"
      unfolding raw.until_def by blast
    from this(1,2) obtain k \<omega>''
      where **: "k \<le> i" "behavior.dropn k \<omega> = Some \<omega>''" "\<omega>'' \<in> Q" "\<forall>j<k. the (behavior.dropn j \<omega>) \<notin> Q"
      using ex_has_least_nat[where k=i and P="\<lambda>k. k \<le> i \<and> (\<forall>\<omega>''. behavior.dropn k \<omega> = Some \<omega>'' \<longrightarrow> \<omega>'' \<in> Q)" and m=id]
      by clarsimp (metis (no_types, lifting) behavior.dropn.shorterD leD nle_le option.sel order.trans)
    from that * ** show ?thesis
      by (clarsimp simp: raw.until_def intro!: exI[where x=k])
         (metis order.strict_trans1 linorder_not_le option.sel)
  qed
qed

lemma SupR:
  shows "raw.until P (\<Union>X) = \<Union>(raw.until P ` X)"
unfolding raw.until_def by blast

lemma weakenL:
  shows "raw.until UNIV P = raw.until (- P) P" (is "?lhs = ?rhs")
proof(rule antisym[OF subsetI])
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega> using that by induct blast+
  show "?rhs \<subseteq> ?lhs" by (simp add: raw.until.mono)
qed

lemma implication_ordering_le: \<comment>\<open> \<^citet>\<open>\<open>(16)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "raw.until P Q \<inter> raw.until (-Q) R \<subseteq> raw.until P R"
by (clarsimp simp: raw.until_def) (metis order.trans linorder_not_le option.sel)

lemma infR_ordering_le: \<comment>\<open> \<^citet>\<open>\<open>(18)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "raw.until P (Q \<inter> R) \<subseteq> raw.until (raw.until P Q) R" (is "?lhs\<subseteq> ?rhs")
proof(rule subsetI)
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega>
    using that
  proof induct
    case (step \<omega> \<omega>') then show ?case
      by - (rule raw.until.step, rule raw.until.step;
            blast intro: subsetD[OF raw.until.mono, rotated -1])
  qed blast
qed

lemma untilL:
  shows "raw.until (raw.until P Q) Q \<subseteq> raw.until P Q" (is "?lhs\<subseteq> ?rhs")
proof(rule subsetI)
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega>
    using that by induct auto
qed

lemma alwaysR_le:
  shows "raw.until P (raw.always Q) \<subseteq> raw.always (raw.until P Q)" (is "?lhs \<subseteq> ?rhs")
proof(rule subsetI)
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega>
    using that
  proof induct
    case (base \<omega>) then show ?case by (auto simp: raw.always_alt_def)
  next
    case (step \<omega> \<omega>') show ?case
    proof(rule raw.alwaysI)
      fix i \<omega>'' assume "behavior.dropn i \<omega> = Some \<omega>''"
      with step "behavior.dropn.0" show "\<omega>'' \<in> raw.until P Q"
        by (cases i; clarsimp simp: raw.always_alt_def behavior.dropn.Suc; blast)
    qed
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "unless"\<close>

lemma neg:
  shows "- (raw.until P Q \<union> raw.always P) = raw.until (- Q) (- P \<inter> - Q)" (is "?lhs = ?rhs")
proof(rule antisym[OF subsetI], (unfold Compl_Un Int_iff conj_explode Compl_iff)[1])
  fix \<omega>
  assume *: "\<omega> \<notin> raw.until P Q"
  assume "\<omega> \<notin> raw.always P"
  then obtain k \<omega>'
    where "behavior.dropn k \<omega> = Some \<omega>'"
      and "\<omega>' \<notin> P"
    by (clarsimp simp: raw.always_alt_def)
  with ex_has_least_nat[where k=k and P="\<lambda>i. \<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<omega>' \<notin> P" and m=id]
  obtain k \<omega>'
    where "behavior.dropn k \<omega> = Some \<omega>'"
      and "\<omega>' \<notin> P"
      and "\<forall>j<k. the (behavior.dropn j \<omega>) \<in> P"
    by clarsimp (metis behavior.dropn.shorterD less_le_not_le option.distinct(1) option.exhaust_sel)
  with * behavior.dropn.shorterD show "\<omega> \<in> ?rhs"
    by (fastforce simp: raw.until_def intro: exI[where x=k])
next
  show "?rhs \<subseteq> ?lhs"
    by (clarsimp simp: raw.always_alt_def raw.until_def subset_iff; metis nat_neq_iff option.sel)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "eventually"\<close>

lemma terminated:
  shows "raw.eventually raw.terminated = {\<omega>. tfinite (behavior.rest \<omega>)}" (is "?lhs = ?rhs")
proof(rule antisym[OF _ subsetI])
  show "?lhs \<subseteq> ?rhs"
    by (clarsimp simp: raw.eventually_alt_def raw.terminated_def behavior.dropn.tfiniteD)
  show "\<omega> \<in> ?lhs" if "\<omega> \<in> ?rhs" for \<omega>
  proof -
    note \<open>\<omega> \<in> ?rhs\<close>
    moreover from calculation
    obtain i where "tlength (behavior.rest \<omega>) = enat i"
      by (clarsimp simp: tfinite_tlength_conv)
    moreover from calculation
    obtain \<omega>' where "behavior.dropn i \<omega> = Some \<omega>'"
      using behavior.dropn.eq_Some_tlength_conv by fastforce
    moreover from calculation
    have "behavior.sset \<omega>' \<subseteq> {behavior.init \<omega>'}"
      by (cases \<omega>')
         (clarsimp dest!: behavior.dropn.eq_Some_tdropnD simp: tdropn_tlength behavior.sset.simps)
    ultimately show "\<omega> \<in> ?lhs"
      by (auto simp: raw.eventually_alt_def raw.terminated_def dest: behavior.dropn.tfiniteD)
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "behavior.stuttering.closed.raw"\<close>

lemma state_prop[intro]:
  shows "raw.state_prop P \<in> behavior.stuttering.closed"
by (fastforce simp: raw.state_prop_def behavior.natural_def elim: behavior.stuttering.clE)

lemma terminated[intro]:
  shows "raw.terminated \<in> behavior.stuttering.closed"
by (rule behavior.stuttering.closedI)
   (clarsimp simp: raw.terminated_def elim!: behavior.stuttering.clE;
    metis behavior.natural.sel(1) behavior.natural.tfinite behavior.sset.natural)

lemma until[intro]:
  assumes "P \<in> behavior.stuttering.closed"
  assumes "Q \<in> behavior.stuttering.closed"
  shows "raw.until P Q \<in> behavior.stuttering.closed"
proof -
  have "\<omega>\<^sub>2 \<in> raw.until P Q" if "\<omega>\<^sub>1 \<in> raw.until P Q" and "\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2" for \<omega>\<^sub>1 \<omega>\<^sub>2
    using that
  proof(induct arbitrary: \<omega>\<^sub>2 rule: raw.until.induct)
    case (base \<omega>\<^sub>1 \<omega>\<^sub>2) with assms(2) show ?case
      by (blast intro: behavior.stuttering.closed_in)
  next
    case (step \<omega>\<^sub>1 \<omega>' \<omega>\<^sub>2)
    show ?case
    proof(cases "\<omega>' \<simeq>\<^sub>T \<omega>\<^sub>1")
      case True with \<open>\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2\<close> step.hyps(4) show ?thesis
        by simp
    next
      case False
      from assms(1) \<open>\<omega>\<^sub>1 \<in> P\<close> \<open>\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2\<close> have "\<omega>\<^sub>2 \<in> P"
        by (blast intro: behavior.stuttering.closed_in)
      from False \<open>\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2\<close> \<open>behavior.tl \<omega>\<^sub>1 = Some \<omega>'\<close>
      obtain a s\<^sub>0 s\<^sub>1 xs\<^sub>1 xs' ys'
        where \<omega>\<^sub>1: "\<omega>\<^sub>1 = behavior.B s\<^sub>0 (TCons (a, s\<^sub>1) xs\<^sub>1)"
          and \<omega>\<^sub>2: "\<omega>\<^sub>2 = behavior.B s\<^sub>0 (tshift xs' (TCons (a, s\<^sub>1) ys'))"
          and *: "collapse s\<^sub>0 (TCons (a, s\<^sub>1) xs\<^sub>1) = collapse s\<^sub>0 (tshift xs' (TCons (a, s\<^sub>1) ys'))"
                 "s\<^sub>0 \<noteq> s\<^sub>1"
          and **: "collapse s\<^sub>1 ys' = collapse s\<^sub>1 xs\<^sub>1"
          and xs': "snd ` set xs' \<subseteq> {s\<^sub>0}"
        by (cases \<omega>\<^sub>1; cases \<omega>\<^sub>2; cases "behavior.rest \<omega>\<^sub>1"; simp)
           (fastforce simp: behavior.natural_def collapse.eq_TCons_conv trepeat_eq_TCons_conv
                     split: if_splits)
      from \<omega>\<^sub>2 \<open>\<omega>\<^sub>2 \<in> P\<close> xs' show ?thesis
      proof(induct xs' arbitrary: \<omega>\<^sub>2)
        case Nil with \<omega>\<^sub>1 ** step.hyps(2,4) show ?case
          by (auto simp: behavior.natural_def)
      next
        case (Cons x' xs')
        with behavior.stuttering.closed_in[OF _ _ \<open>P \<in> behavior.stuttering.closed\<close>] \<omega>\<^sub>1 ** step(3)
        show ?case
          by (auto simp: behavior.natural_def  behavior.split_all)
      qed
    qed
  qed
  then show ?thesis
    by (fastforce elim: behavior.stuttering.clE)
qed

lemma eventually[intro]:
  assumes "P \<in> behavior.stuttering.closed"
  shows "raw.eventually P \<in> behavior.stuttering.closed"
using assms by (auto simp: raw.eventually_def)

lemma always[intro]:
  assumes "P \<in> behavior.stuttering.closed"
  shows "raw.always P \<in> behavior.stuttering.closed"
using assms by (auto simp: raw.always_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tls"\<close>

definition valid :: "('a, 's, 'v) tls \<Rightarrow> bool" where
  "valid P \<longleftrightarrow> P = \<top>"

lift_definition state_prop :: "'s pred \<Rightarrow> ('a, 's, 'v) tls" is raw.state_prop ..
lift_definition terminated :: "('a, 's, 'v) tls" is raw.terminated ..
lift_definition until :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" is raw.until ..

definition eventually :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "eventually P = tls.until \<top> P"

definition always :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "always P = -tls.eventually (-P)"

definition release :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "release P Q = -(tls.until (-P) (-Q))"

definition unless :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "unless P Q = tls.until P Q \<squnion> tls.always P"

abbreviation (input) always_imp_syn :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "always_imp_syn P Q \<equiv> tls.always (P \<^bold>\<longrightarrow>\<^sub>B Q)"

abbreviation (input) leads_to :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "leads_to P Q \<equiv> tls.always_imp_syn P (tls.eventually Q)"

bundle "notation"
begin

notation tls.valid ("\<Turnstile> _" [30] 30)
notation tls.state_prop ("\<llangle>_\<rrangle>" [0])
notation tls.until (infix "\<U>" 85)
notation tls.eventually ("\<diamond>_" [87] 87)
notation tls.always ("\<box>_" [87] 87)
notation tls.release (infixr "\<R>" 85)
notation tls.unless (infixr "\<W>" 85)
notation tls.always_imp_syn (infixr "\<^bold>\<longrightarrow>\<^sub>\<box>" 75)
notation tls.leads_to (infixr "\<^bold>\<leadsto>" 75)

end

bundle "no_notation"
begin

no_notation tls.valid ("\<Turnstile> _" [30] 30)
no_notation tls.state_prop ("\<llangle>_\<rrangle>" [0])
no_notation tls.until (infixr "\<U>" 85)
no_notation tls.eventually ("\<diamond>_" [87] 87)
no_notation tls.always ("\<box>_" [87] 87)
no_notation tls.release (infixr "\<R>" 85)
no_notation tls.unless (infixr "\<W>" 85)
no_notation tls.always_imp_syn (infixr "\<^bold>\<longrightarrow>\<^sub>\<box>" 75)
no_notation tls.leads_to (infixr "\<^bold>\<leadsto>" 75)

end

unbundle tls.notation

lemma validI:
  assumes "\<top> \<le> P"
  shows "\<Turnstile> P"
by (simp add: assms tls.valid_def top.extremum_uniqueI)

setup \<open>Sign.mandatory_path "valid"\<close>

lemma trans[trans]:
  assumes "\<Turnstile> P"
  assumes "P \<le> Q"
  shows "\<Turnstile> Q"
using assms by (simp add: tls.valid_def top.extremum_unique)

lemma mp:
  assumes "\<Turnstile> P \<^bold>\<longrightarrow>\<^sub>B Q"
  assumes "\<Turnstile> P"
  shows "\<Turnstile> Q"
using assms by (simp add: tls.valid_def)

lemmas rev_mp = tls.valid.mp[rotated]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma uminus_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> -P \<longleftrightarrow> \<not>\<lblot>\<omega>\<rblot>\<^sub>T \<le> P"
by transfer
   (simp add: raw.singleton_def behavior.stuttering.closed_uminus behavior.stuttering.least_conv)

lemma state_prop_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.state_prop P \<longleftrightarrow> P (behavior.init \<omega>)"
by transfer
   (simp add: raw.singleton_def behavior.stuttering.least_conv[OF behavior.stuttering.closed.raw.state_prop];
    simp add: raw.state_prop_def)

lemma terminated_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.terminated \<longleftrightarrow> tfinite (behavior.rest \<omega>) \<and> behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}"
by transfer
   (simp add: raw.singleton_def behavior.stuttering.least_conv[OF behavior.stuttering.closed.raw.terminated];
    simp add: raw.terminated_def)

lemma until_le_conv[tls.singleton.le_conv]:
  fixes P :: "('a, 's, 'v) tls"
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> P \<U> Q \<longleftrightarrow> (\<exists>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>'
                                \<and> \<lblot>\<omega>'\<rblot>\<^sub>T \<le> Q
                                \<and> (\<forall>j<i. \<lblot>the (behavior.dropn j \<omega>)\<rblot>\<^sub>T \<le> P))" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
  proof transfer
    fix \<omega> and P Q :: "('a, 's, 'v) behavior.t set"
    assume *: "P \<in> behavior.stuttering.closed" "Q \<in> behavior.stuttering.closed"
       and "raw.singleton \<omega> \<subseteq> raw.until P Q"
    then have "\<exists>i. \<exists>\<omega>'\<in>Q. behavior.dropn i \<omega> = Some \<omega>' \<and> (\<forall>j<i. the (behavior.dropn j \<omega>) \<in> P)"
      by (auto simp: raw.singleton_def raw.until_def)
    with * show "\<exists>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>'
                      \<and> raw.singleton \<omega>' \<subseteq> Q \<and> (\<forall>j<i. raw.singleton (the (behavior.dropn j \<omega>)) \<subseteq> P)"
      by (auto simp: raw.singleton_def behavior.stuttering.least_conv)
  qed
  show "?rhs \<Longrightarrow> ?lhs"
    by transfer
       (unfold raw.singleton_def;
        rule behavior.stuttering.least[OF _ behavior.stuttering.closed.raw.until];
        auto 10 0 intro: iffD2[OF eqset_imp_iff[OF raw.until_def]])
qed

lemma eventually_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> \<diamond>P \<longleftrightarrow> (\<exists>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<lblot>\<omega>'\<rblot>\<^sub>T \<le> P)"
by (simp add: tls.eventually_def tls.singleton.le_conv)

lemma always_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.always P \<longleftrightarrow> (\<forall>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<longrightarrow> \<lblot>\<omega>'\<rblot>\<^sub>T \<le> P)"
by (simp add: tls.always_def tls.singleton.le_conv)

setup \<open>Sign.parent_path\<close>

interpretation until: closure_complete_lattice_distributive_class "tls.until P" for P
proof standard
  show "(x \<le> tls.until P y) = (tls.until P x \<le> tls.until P y)" for x y
  by transfer
     (intro iffD2[OF order_class.order.closure_axioms_alt_def[unfolded closure_axioms_def], rule_format]
            conjI allI raw.until.base monoI raw.until.mono order.refl raw.until.untilR, assumption)
  show "tls.until P (\<Squnion>X) \<le> \<Squnion>(tls.until P ` X) \<squnion> tls.until P \<bottom>" for X
    by transfer (simp add: raw.until.SupR behavior.stuttering.cl_bot)
qed

setup \<open>Sign.mandatory_path "until"\<close>

lemmas botL = raw.until.botL[transferred]
lemmas botR = raw.until.botR[transferred]
lemmas topR = tls.until.cl_top
lemmas expansiveR = tls.until.expansive[of P Q for P Q]

lemmas weakenL = raw.until.weakenL[transferred]

lemmas mono = raw.until.mono[transferred]

lemma strengthen[strg]:
  assumes "st_ord F P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (P \<U> Q) (P' \<U> Q')"
using assms by (cases F) (auto simp: tls.until.mono)

lemma SupL_le:
  shows "(\<Squnion>x\<in>X. x \<U> R) \<le> (\<Squnion>X) \<U> R"
by (simp add: SupI tls.until.mono)

lemma supL_le:
  shows "P \<U> R \<squnion> Q \<U> R \<le> (P \<squnion> Q) \<U> R"
by (simp add: tls.until.mono)

lemma SupR:
  shows "P \<U> (\<Squnion>X) = \<Squnion>((\<U>) P ` X)"
by (simp add: tls.until.cl_Sup tls.until.botR)

lemmas supR = tls.until.cl_sup

lemmas InfL_not_empty = raw.until.InfL_not_empty[transferred]
lemmas infL = tls.until.InfL_not_empty[where X="{P, Q}" for P Q, simplified, of P Q R for P Q R]
lemmas InfR_le = tls.until.cl_Inf_le
lemmas infR_le = tls.until.cl_inf_le[of P Q R for P Q R]

lemma implication_ordering_le: \<comment>\<open> \<^citet>\<open>\<open>(16)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> Q \<sqinter> (-Q) \<U> R \<le> P \<U> R"
by transfer (rule raw.until.implication_ordering_le)

lemma supL_ordering_le: \<comment>\<open> \<^citet>\<open>\<open>(17)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> (Q \<U> R) \<le> (P \<squnion> Q) \<U> R" (is "?lhs \<le> ?rhs")
proof -
  have "?rhs = (P \<squnion> Q) \<U> ((P \<squnion> Q) \<U> R)" by (rule tls.until.idempotent(1)[symmetric])
  also have "?lhs \<le> \<dots>" by (blast intro: tls.until.mono le_supI1 le_supI2)
  finally show ?thesis .
qed

lemma infR_ordering_le: \<comment>\<open> \<^citet>\<open>\<open>(18)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> (Q \<sqinter> R) \<le> (P \<U> Q) \<U> R"
by transfer (rule raw.until.infR_ordering_le)

lemma boolean_implication_distrib_le: \<comment>\<open> \<^citet>\<open>\<open>(19)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "(P \<^bold>\<longrightarrow>\<^sub>B Q) \<U> R \<le> (P \<U> R) \<^bold>\<longrightarrow>\<^sub>B (Q \<U> R)"
by (metis galois.conj_imp.galois order.refl tls.until.infL tls.until.mono)

lemma excluded_middleR: \<comment>\<open> \<^citet>\<open>\<open>(23)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<Turnstile> P \<U> Q \<squnion> P \<U> (-Q)"
by (simp add: tls.validI tls.until.cl_top flip: tls.until.cl_sup)

lemmas untilR = tls.until.idempotent(1)[of P Q for P Q]

lemma untilL:
  shows "(P \<U> Q) \<U> Q = P \<U> Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by transfer (rule raw.until.untilL)
  show "?rhs \<le> ?lhs"
    using tls.until.infR_ordering_le[where P=P and Q=Q and R=Q] by simp
qed

lemma absorb:
  shows "P \<U> P = P"
by (metis tls.until.botL tls.until.untilL)

lemma absorb_supL: \<comment>\<open> \<^citet>\<open>\<open>(23)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<squnion> P \<U> Q = P \<squnion> Q"
by (metis inf_commute inf_sup_absorb le_iff_sup
          tls.until.absorb tls.until.cl_sup tls.until.expansive tls.until.infL)

lemma absorb_supR: \<comment>\<open> \<^citet>\<open>\<open>(23)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "Q \<squnion> P \<U> Q = P \<U> Q"
by (simp add: sup.absorb2 tls.until.expansive)

lemma eventually_le:
  shows "P \<U> Q \<le> \<diamond>Q"
by (simp add: tls.eventually_def tls.until.mono)

lemma absorb_eventually:
  shows inf_eventually_absorbR: "P \<U> Q \<sqinter> \<diamond>Q = P \<U> Q" \<comment>\<open> \<^citet>\<open>\<open>(39)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
    and sup_eventually_absorbR: "P \<U> Q \<squnion> \<diamond>Q = \<diamond>Q" \<comment>\<open> \<^citet>\<open>\<open>(40)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
    and eventually_absorbR: "P \<U> \<diamond>Q = \<diamond>Q" \<comment>\<open> \<^citet>\<open>\<open>(41)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
by (simp_all add: tls.eventually_def sup.absorb2 tls.until.mono
                  order.eq_iff order.trans[OF tls.until.supL_ordering_le] tls.until.expansiveR
            flip: tls.until.infL)

lemma sup_le: \<comment>\<open> \<^citet>\<open>\<open>(28)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> Q \<le> P \<squnion> Q"
by (simp add: ac_simps sup.absorb_iff1 tls.until.absorb_supL tls.until.absorb_supR)

lemma ordering: \<comment>\<open> \<^citet>\<open>\<open>(251)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "(-P) \<U> Q \<squnion> (-Q) \<U> P = \<diamond>(P \<squnion> Q)" (is "?lhs = ?rhs")
proof -
  have "?lhs = \<top> \<U> P \<sqinter> (- Q) \<U> P \<squnion> \<top> \<U> Q \<sqinter> (- P) \<U> Q"
    by (simp add: ac_simps inf.absorb2 tls.until.mono)
  also have "\<dots> = (- P) \<U> P \<sqinter> (- Q) \<U> P \<squnion> (- Q) \<U> Q \<sqinter> (- P) \<U> Q"
    by (simp add: tls.until.weakenL)
  also have "\<dots> = (- (P \<squnion> Q)) \<U> (P \<squnion> Q)"
    by (simp add: ac_simps tls.until.cl_sup flip: tls.until.infL)
  also have "\<dots> = ?rhs"
    by (simp add: tls.eventually_def tls.until.weakenL)
  finally show ?thesis .
qed

lemmas simps =
  tls.until.expansiveR
  tls.until.botL
  tls.until.botR
  tls.until.absorb
  tls.until.absorb_supL
  tls.until.absorb_supR
  tls.until.untilL
  tls.until.untilR

setup \<open>Sign.parent_path\<close>

interpretation eventually: closure_complete_lattice_distributive_class tls.eventually
unfolding tls.eventually_def
by (simp add: tls.until.closure_complete_lattice_distributive_class_axioms)

lemma eventually_alt_def:
  shows "\<diamond>P = (-P) \<U> P"
by (simp add: tls.eventually_def tls.until.weakenL)

setup \<open>Sign.mandatory_path "eventually"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (pcr_tls (=) (=) (=)) (pcr_tls (=) (=) (=)) raw.eventually tls.eventually"
unfolding tls.eventually_def raw.eventually_def by transfer_prover

lemma bot:
  shows "\<diamond>\<bottom> = \<bottom>"
by (simp add: tls.eventually_def tls.until.simps)

lemma bot_conv:
  shows "\<diamond>P = \<bottom> \<longleftrightarrow> P = \<bottom>"
by (auto simp: tls.eventually.bot bot.extremum_uniqueI[OF order.trans[OF tls.eventually.expansive]])

lemmas top = tls.eventually.cl_top

lemmas monotone = tls.eventually.monotone_cl
lemmas mono = tls.eventually.mono_cl

lemmas Sup = tls.eventually.cl_Sup[simplified tls.eventually.bot, simplified]
lemmas sup = tls.eventually.Sup[where X="{P, Q}" for P Q, simplified]

lemmas Inf_le = tls.eventually.cl_Inf_le
lemmas inf_le = tls.eventually.cl_inf_le

lemma neg:
  shows "-\<diamond>P = \<box>(-P)"
by (simp add: tls.always_def)

lemma boolean_implication_le:
  shows "\<diamond>P \<^bold>\<longrightarrow>\<^sub>B \<diamond>Q \<le> \<diamond>(P \<^bold>\<longrightarrow>\<^sub>B Q)"
by (simp add: boolean_implication.conv_sup tls.eventually.sup)
   (meson le_supI1 compl_mono order.trans le_supI1 tls.eventually.expansive)

lemmas simps =
  tls.eventually.bot
  tls.eventually.top
  tls.eventually.expansive
  tls.eventually_def[symmetric]

lemma terminated:
  shows "\<diamond>tls.terminated = \<Squnion>(tls.singleton ` {\<omega>. tfinite (behavior.rest \<omega>)})"
by transfer
   (auto elim!: behavior.stuttering.clE
          dest: iffD2[OF behavior.natural.tfinite]
          simp: raw.eventually.terminated behavior.stuttering.cl_bot raw.singleton_def collapse.tfinite)

lemma always_imp_le:
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> \<diamond>P \<^bold>\<longrightarrow>\<^sub>B \<diamond>Q"
by (simp add: tls.always_def boolean_implication.conv_sup flip: shunt2)
   (metis inf_commute order.refl shunt2 sup.commute tls.eventually.mono tls.eventually.sup)

lemma until:
  shows "\<diamond>(P \<U> Q) = \<diamond>Q"
by (meson antisym tls.eventually.cl tls.eventually.mono tls.until.eventually_le tls.until.expansiveR)

setup \<open>Sign.parent_path\<close>

lemma always_alt_def:
  shows "\<box>P = P \<W> \<bottom>"
by (simp add: tls.unless_def tls.until.simps)

setup \<open>Sign.mandatory_path "always"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (pcr_tls (=) (=) (=)) (pcr_tls (=) (=) (=)) raw.always tls.always"
unfolding tls.always_def raw.always_def by transfer_prover

text\<open> \<^const>\<open>tls.always\<close> is an interior operator \<close>

lemma idempotent[simp]:
  shows "\<box>\<box>P = \<box>P"
by (simp add: tls.always_def)

lemma contractive:
  shows "\<box>P \<le> P"
by (simp add: tls.always_def compl_le_swap2 tls.eventually.expansive)

lemma monotone[iff]:
  shows "mono tls.always"
by (simp add: tls.always_def monoI tls.eventually.mono)

lemmas strengthen[strg] = st_monotone[OF tls.always.monotone]
lemmas mono[trans] = monoD[OF tls.always.monotone]

lemma bot:
  shows "\<box>\<bottom> = \<bottom>"
by (simp add: tls.always_def tls.eventually.simps)

lemma top:
  shows "\<box>\<top> = \<top>"
by (simp add: tls.always_def tls.eventually.simps)

lemma top_conv:
  shows "\<box>P = \<top> \<longleftrightarrow> P = \<top>"
by (auto simp: tls.always.top intro: top.extremum_uniqueI[OF order.trans[OF _ tls.always.contractive]])

lemma Sup_le:
  shows "\<Squnion>(tls.always ` X) \<le> \<box>(\<Squnion>X)"
by (simp add: SupI tls.always.mono)

lemma sup_le:
  shows "\<box>P \<squnion> \<box>Q \<le> \<box>(P \<squnion> Q)"
by (simp add: tls.always.mono)

lemma Inf:
  shows "\<box>(\<Sqinter>X) = \<Sqinter>(tls.always ` X)"
by (rule iffD1[OF compl_eq_compl_iff])
   (simp add: tls.always_def image_image tls.eventually.Sup uminus_Inf)

lemma inf:
  shows "\<box>(P \<sqinter> Q) = \<box>P \<sqinter> \<box>Q"
by (simp add: tls.always_def tls.eventually.sup)

lemma neg:
  shows "-\<box>P = \<diamond>(-P)"
by (simp add: tls.always_def)

lemma always_necessitation:
  assumes "\<Turnstile> P"
  shows "\<Turnstile> \<box>P"
using assms by (simp add: tls.valid_def tls.always.top)

lemma valid_conv:
  shows "\<Turnstile> \<box>P \<longleftrightarrow> \<Turnstile> P"
by (simp add: tls.valid_def tls.always.top_conv)

lemma always_imp_le:
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> \<box>P \<^bold>\<longrightarrow>\<^sub>B \<box>Q"
by (simp add: galois.conj_imp.lower_upper_contractive tls.always.mono
        flip: galois.conj_imp.galois tls.always.inf)

lemma eventually_le:
  shows "\<box>P \<le> \<diamond>P"
using tls.always.contractive tls.eventually.cl tls.eventually.mono by blast

lemma not_until_le: \<comment>\<open> \<^citet>\<open>\<open>(81)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<box>P \<le> -(Q \<U> (-P))"
by (simp add: compl_le_swap1 tls.always.neg tls.until.eventually_le)

lemmas simps =
  tls.always.bot
  tls.always.top
  tls.always.contractive
  tls.always_alt_def[symmetric]

setup \<open>Sign.parent_path\<close>

lemma until_alwaysR_le: \<comment>\<open> \<^citet>\<open>\<open>(140)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> \<box>Q \<le> \<box>(P \<U> Q)"
by transfer (rule raw.until.alwaysR_le)

lemma until_alwaysR: \<comment>\<open> \<^citet>\<open>\<open>(141)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<U> \<box>P = \<box>P"
by (simp add: order.eq_iff order.trans[OF tls.until_alwaysR_le] tls.until.simps)

lemma eventually_always_always_eventually_le: \<comment>\<open> \<^citet>\<open>\<open>(145)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<diamond>\<box>P \<le> \<box>\<diamond>P"
by (simp add: tls.eventually_def tls.until_alwaysR_le)

lemma always_inf_eventually_eventually_le:
  shows "\<box>P \<sqinter> \<diamond>Q \<le> \<diamond>(P \<sqinter> Q)"
by (simp add: shunt1 order.trans[OF _ tls.eventually.always_imp_le] boolean_implication.mp
              tls.always.mono
        flip: boolean_implication_def)

lemma always_always_imp: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T33 frame\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "\<Turnstile> \<box>P \<^bold>\<longrightarrow>\<^sub>B \<box>Q \<^bold>\<longrightarrow>\<^sub>B \<box>(P \<sqinter> Q)"
by (simp add: tls.validI tls.always.inf flip: boolean_implication.infL)

lemma always_eventually_imp: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T34 frame\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "\<Turnstile> \<box>P \<^bold>\<longrightarrow>\<^sub>B \<diamond>Q \<^bold>\<longrightarrow>\<^sub>B \<diamond>(P \<sqinter> Q)"
by (simp add: tls.validI boolean_implication.mp tls.always_inf_eventually_eventually_le)

lemma always_imp_always_generalization: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T35\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "\<box>P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> \<box>P \<^bold>\<longrightarrow>\<^sub>B \<box>Q"
by (simp add: order.trans[OF tls.always.always_imp_le])

lemma always_imp_eventually_generalization: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T36\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> \<diamond>Q \<le> \<diamond>P \<^bold>\<longrightarrow>\<^sub>B \<diamond>Q"
by (metis tls.eventually.always_imp_le tls.eventually.idempotent(1))

text\<open>

The following show that there is no point nesting \<^const>\<open>tls.always\<close> and \<^const>\<open>tls.eventually\<close>
more than two deep.
\<close>

lemma always_eventually_always_absorption: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T37\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "\<diamond>\<box>\<diamond>P = \<box>\<diamond>P"
by (metis order.eq_iff tls.eventually.expansive tls.eventually.idempotent(1)
          tls.eventually_always_always_eventually_le)

lemma eventually_always_eventually_absorption: \<comment>\<open>\<^citet>\<open>\<open>\S2.2: T38\<close> in "KroegerMerz:2008"\<close> \<close>
  shows "\<box>\<diamond>\<box>P = \<diamond>\<box>P"
by (metis tls.always.neg tls.always_def tls.always_eventually_always_absorption)

lemma always_imp_always_eventually_le: \<comment>\<open> \<^citet>\<open>\<open>(157)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> \<box>\<diamond>P \<^bold>\<longrightarrow>\<^sub>B \<box>\<diamond>Q"
by (simp add: order.trans[OF _ tls.always.always_imp_le]
              order.trans[OF _ tls.always.mono[OF tls.eventually.always_imp_le]])

lemma always_imp_eventually_always_le: \<comment>\<open> \<^citet>\<open>\<open>(158)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> \<diamond>\<box>P \<^bold>\<longrightarrow>\<^sub>B \<diamond>\<box>Q"
by (simp add: order.trans[OF _ tls.eventually.always_imp_le]
              order.trans[OF _ tls.always.mono[OF tls.always.always_imp_le]])

lemma always_eventually_inf_le:
  shows "\<box>\<diamond>(P \<sqinter> Q) \<le> \<box>\<diamond>P \<sqinter> \<box>\<diamond>Q" \<comment>\<open> \<^citet>\<open>\<open>(159)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
by (simp add: tls.always.mono tls.eventually.mono)

lemma eventually_always_sup_le:
  shows "\<diamond>\<box>P \<sqinter> \<diamond>\<box>Q \<le> \<diamond>\<box>(P \<squnion> Q)" \<comment>\<open> \<^citet>\<open>\<open>(160)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
by (simp add: le_infI2 tls.always.mono tls.eventually.mono)

lemma always_eventually_sup: \<comment>\<open> \<^citet>\<open>\<open>(161)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  fixes P :: "('a, 's, 'v) tls"
  shows "\<box>\<diamond>(P \<squnion> Q) = \<box>\<diamond>P \<squnion> \<box>\<diamond>Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
  proof transfer
    fix P Q :: "('a, 's, 'v) behavior.t set"
    have "\<exists>\<omega>'\<in>P. \<exists>i. behavior.dropn i \<omega>\<^sub>j = Some \<omega>'"
      if "\<forall>i \<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<longrightarrow> (\<exists>\<omega>''\<in>P \<union> Q. \<exists>i. behavior.dropn i \<omega>' = Some \<omega>'')"
     and "behavior.dropn i \<omega> = Some \<omega>\<^sub>i"
     and "\<forall>\<omega>'\<in>Q. \<forall>i. behavior.dropn i \<omega>\<^sub>i \<noteq> Some \<omega>'"
     and "behavior.dropn j \<omega> = Some \<omega>\<^sub>j"
      for \<omega> i j \<omega>\<^sub>i \<omega>\<^sub>j
      using spec[where x="max i j", OF that(1)] that(2,3,4)
      by (clarsimp simp: nat_le_iff_add split: split_asm_max;
          metis add_diff_inverse_nat behavior.dropn.dropn bind.bind_lunit order.asym)
    then show "raw.always (raw.eventually (P \<union> Q))
            \<subseteq> raw.always (raw.eventually P) \<union> raw.always (raw.eventually Q)"
      by (clarsimp simp: raw.eventually_alt_def raw.always_alt_def)
  qed
  show "?rhs \<le> ?lhs"
    by (simp add: tls.eventually.sup order.trans[OF _ tls.always.sup_le])
qed

lemma eventually_always_inf: \<comment>\<open> \<^citet>\<open>\<open>(162)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<diamond>\<box>(P \<sqinter> Q) = \<diamond>\<box>P \<sqinter> \<diamond>\<box>Q"
by (subst compl_eq_compl_iff[symmetric])
   (simp add: tls.always.neg tls.always_eventually_sup tls.eventually.neg)

lemma eventual_latching: \<comment>\<open> \<^citet>\<open>\<open>(163)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<diamond>\<box>(P \<^bold>\<longrightarrow>\<^sub>B \<box>Q) = \<diamond>\<box>(-P) \<squnion> \<diamond>\<box>Q" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs"
    by (rule order.trans[OF tls.eventually.mono[OF tls.always_imp_always_eventually_le]])
       (simp add: boolean_implication.conv_sup tls.always.neg
                  tls.eventually.neg tls.eventually.sup tls.eventually_always_eventually_absorption)
  have "\<diamond>\<box>Q \<le> \<diamond>\<box>(- P \<squnion> \<box>Q)"
    apply (rule order.trans[OF tls.eventually.mono[OF eq_refl[OF tls.always.idempotent[symmetric]]]])
    apply (rule tls.eventually.mono[OF tls.always.mono])
    apply simp
    done
  then show "?rhs \<le> ?lhs"
    by (simp add: le_sup_iff boolean_implication.conv_sup monoD)
qed

setup \<open>Sign.mandatory_path "unless"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (pcr_tls (=) (=) (=)) (rel_fun (pcr_tls (=) (=) (=)) (pcr_tls (=) (=) (=)))
                 (\<lambda>P Q. raw.until P Q \<union> raw.always P)
                 tls.unless"
unfolding tls.unless_def by transfer_prover

lemma neg: \<comment>\<open> \<^citet>\<open>\<open>(170)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "-(P \<W> Q) = (-Q) \<U> (-P \<sqinter> -Q)"
by transfer (rule raw.unless.neg)

lemma alwaysR_le: \<comment>\<open> \<^citet>\<open>\<open>(177)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<W> \<box>Q \<le> \<box>(P \<W> Q)"
by (simp add: tls.unless_def order.trans[OF tls.until_alwaysR_le] tls.always.mono
              order.trans[OF _ tls.always.sup_le])

lemma sup_le: \<comment>\<open> \<^citet>\<open>\<open>(206)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<W> Q \<le> P \<squnion> Q"
by (rule iffD1[OF compl_le_compl_iff]) (simp add: tls.unless.neg tls.until.expansive)

lemma ordering: \<comment>\<open> \<^citet>\<open>\<open>(252)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<Turnstile> (-P) \<W> Q \<squnion> (-Q) \<W> P"
by (simp add: ac_simps tls.validI tls.unless_def tls.until.ordering tls.eventually.sup flip: tls.eventually.neg)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "until"\<close>

lemma eq_unless_inf_eventually:
  shows "P \<U> Q = (P \<W> Q) \<sqinter> \<diamond>Q"
by transfer (force simp: raw.until_def raw.eventually_def raw.always_alt_def behavior.dropn.shorterD)

lemma always_strengthen_le: \<comment>\<open> \<^citet>\<open>\<open>(83)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<box>P \<sqinter> (Q \<U> R) \<le> (P \<sqinter> Q) \<U> (P \<sqinter> R)"
by transfer
   (clarsimp simp: raw.until_def raw.always_alt_def;
    fastforce simp: behavior.dropn.shorterD del: exI intro!: exI)

lemma until_weakI:
  shows "\<box>P \<sqinter> \<diamond>Q \<le> P \<U> Q" (is "?lhs \<le> ?rhs") \<comment>\<open> \<^citet>\<open>\<open>(84)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
by (simp add: tls.eventually_def order.trans[OF tls.until.always_strengthen_le] tls.until.mono)

lemma always_impL: \<comment>\<open> \<^citet>\<open>\<open>(86)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> P' \<sqinter> P \<U> Q \<le> P' \<U> Q" (is ?thesis1)
    and "P \<U> Q \<sqinter> P \<^bold>\<longrightarrow>\<^sub>\<box> P' \<le> P' \<U> Q" (is ?thesis2)
proof -
  show ?thesis1
    by (rule order.trans[OF tls.until.always_strengthen_le])
       (simp add: tls.until.mono boolean_implication.shunt1)
  then show ?thesis2
    by (simp add: inf_commute)
qed

lemma always_impR: \<comment>\<open> \<^citet>\<open>\<open>(85)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "Q \<^bold>\<longrightarrow>\<^sub>\<box> Q' \<sqinter> P \<U> Q \<le> P \<U> Q'" (is ?thesis1)
    and "P \<U> Q \<sqinter> Q \<^bold>\<longrightarrow>\<^sub>\<box> Q' \<le> P \<U> Q'" (is ?thesis2)
proof -
  show ?thesis1
    by (rule order.trans[OF tls.until.always_strengthen_le])
       (simp add: tls.until.mono boolean_implication.shunt1)
  then show ?thesis2
    by (simp add: inf_commute)
qed

lemma neg: \<comment>\<open> \<^citet>\<open>\<open>(173)\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "-(P \<U> Q) = (-Q) \<W> (-P \<sqinter> -Q)"
unfolding tls.unless_def
by (simp flip: tls.until.eq_unless_inf_eventually tls.unless.neg tls.eventually.neg
               boolean_algebra.de_Morgan_conj)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "state_prop"\<close>

lemmas monotone = raw.state_prop.monotone[transferred]
lemmas strengthen[strg] = st_monotone[OF tls.state_prop.monotone]
lemmas mono = monoD[OF tls.state_prop.monotone]

lemma Sup:
  shows "tls.state_prop (\<Squnion>X) = \<Squnion>(tls.state_prop ` X)"
by transfer (simp add: raw.state_prop.Sup behavior.stuttering.cl_bot)

lemma Inf:
  shows "tls.state_prop (\<Sqinter>X) = \<Sqinter>(tls.state_prop ` X)"
by transfer (simp add: raw.state_prop.Inf)

lemmas simps = raw.state_prop.simps[transferred]

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "terminated"\<close>

lemma not_bot:
  shows "tls.terminated \<noteq> \<bottom>"
by transfer
   (simp add: raw.terminated_def exI[where x="behavior.B undefined (TNil undefined)"] behavior.sset.simps)

lemma not_top:
  shows "tls.terminated \<noteq> \<top>"
by transfer
   (fastforce simp: raw.terminated_def
              dest: subsetD[OF Set.equalityD2, where c="behavior.B undefined (trepeat (undefined, undefined))"])

lemma inf_always:
  shows "tls.terminated \<sqinter> \<box>P = tls.terminated \<sqinter> P"
by (rule antisym[OF inf.mono[OF order.refl tls.always.contractive]])
   (transfer; simp add: raw.terminated.inf_always_le)

lemma always_le_conv:
  shows "tls.terminated \<le> \<box>P \<longleftrightarrow> tls.terminated \<le> P"
by (simp add: inf.order_iff tls.terminated.inf_always)

lemma inf_eventually:
  shows "tls.terminated \<sqinter> \<diamond>P = tls.terminated \<sqinter> P" (is "?lhs = ?rhs")
proof(rule antisym[OF _ inf.mono[OF order.refl tls.eventually.expansive]])
  have "tls.terminated \<sqinter> - P \<le> tls.terminated \<sqinter> -\<diamond>P"
    by (simp add: tls.terminated.inf_always tls.eventually.neg)
  then show "?lhs \<le> ?rhs"
    by (simp add: boolean_implication.shunt1 boolean_implication.imp_trivialI)
qed

lemma eventually_le_conv:
  shows "tls.terminated \<le> tls.eventually P \<longleftrightarrow> tls.terminated \<le> P"
by (simp add: inf.order_iff tls.terminated.inf_eventually)

lemma eq_always_terminated:
  shows "tls.terminated = \<box>tls.terminated"
by (rule order.antisym[OF _ tls.always.contractive])
   (simp add: tls.terminated.always_le_conv)

setup \<open>Sign.parent_path\<close>


subsubsection\<open> Leads-to and leads-to-via \label{sec:TLS_leads-to} \<close>

text\<open>

So-called \<^emph>\<open>response\<close> properties are of the form
\<open>P \<^bold>\<longrightarrow>\<^sub>\<box> \<diamond>Q\<close> (pronounced ``\<open>P\<close> leads to \<open>Q\<close>'', written
\<open>P \<^bold>\<leadsto> Q\<close>) \<^citep>\<open>"MannaPnueli:1991"\<close>. This connective is similar
to the ``ensures'' modality of \<^citet>\<open>\<open>\S3.4.4\<close> in "ChandyMisra:1989"\<close>.

\<^citet>\<open>"Jackson:1998"\<close> used the more general
``\<open>P\<close> leads to \<open>Q\<close> via \<open>I\<close>'' form \<open>P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q\<close>
to establish liveness properties in a sequential setting.

\<close>

lemma leads_to_refl:
  shows "\<Turnstile> P \<^bold>\<leadsto> P"
by (simp add: tls.validI boolean_implication.shunt_top tls.always.top_conv tls.eventually.expansive
              top.extremum_unique)

lemma leads_to_mono:
  assumes "P' \<le> P"
  assumes "Q \<le> Q'"
  shows "P \<^bold>\<leadsto> Q \<le> P' \<^bold>\<leadsto> Q'"
by (simp add: assms boolean_implication.mono tls.always.mono tls.eventually.mono)

lemma leads_to_supL:
  shows "(P \<^bold>\<leadsto> R) \<sqinter> (Q \<^bold>\<leadsto> R) \<le> (P \<squnion> Q) \<^bold>\<leadsto> R"
by (simp add: boolean_implication.conv_sup sup_inf_distrib2 tls.always.inf)

lemma always_imp_leads_to:
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<le> P \<^bold>\<leadsto> Q"
by (simp add: boolean_implication.mono tls.always.mono tls.eventually.expansive)

lemma leads_to_eventually:
  shows "\<diamond>P \<sqinter> (P \<^bold>\<leadsto> Q) \<le> \<diamond>Q"
by (simp add: galois.conj_imp.galois tls.always_imp_eventually_generalization)

lemma leads_to_leads_to_via:
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> Q \<U> R \<le> P \<^bold>\<leadsto> R"
by (simp add: boolean_implication.mono tls.always.mono tls.until.eventually_le)

lemma leads_to_trans:
  shows "P \<^bold>\<leadsto> Q \<sqinter> Q \<^bold>\<leadsto> R \<le> P \<^bold>\<leadsto> R" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> P \<^bold>\<leadsto> Q \<sqinter> \<box>(Q \<^bold>\<leadsto> R)"
    by (simp add: tls.always.simps)
  also have "\<dots> \<le> P \<^bold>\<leadsto> Q \<sqinter> \<diamond>Q \<^bold>\<leadsto> R"
    by (meson order.refl inf_mono tls.always.mono tls.always_imp_eventually_generalization)
  also have "\<dots> \<le> ?rhs"
    by (simp add: boolean_implication.trans tls.always.mono flip: tls.always.inf)
  finally show ?thesis .
qed

lemma leads_to_via_weakenR:
  shows "Q \<^bold>\<longrightarrow>\<^sub>\<box> Q' \<sqinter> P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q \<le> P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q'"
by transfer
   (clarsimp simp: raw.always_alt_def raw.until_def boolean_implication.set_alt_def;
    metis behavior.dropn.dropn Option.bind.bind_lunit)

lemma leads_to_via_supL: \<comment>\<open> useful for case distinctions \<close>
  shows "P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q \<sqinter> P' \<^bold>\<longrightarrow>\<^sub>\<box> I' \<U> Q \<le> P \<squnion> P' \<^bold>\<longrightarrow>\<^sub>\<box> (I \<squnion> I') \<U> Q"
by (simp add: boolean_implication.conv_sup ac_simps le_infI2 le_supI2
              monoD[OF tls.always.monotone] tls.until.mono)

lemma leads_to_via_trans:
  shows "(P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>\<box> I' \<U> R) \<le> P \<^bold>\<longrightarrow>\<^sub>\<box> (I \<squnion> I') \<U> R" (is "?lhs \<le> ?rhs")
proof -
  have "?lhs \<le> \<box>(P \<^bold>\<longrightarrow>\<^sub>B I \<U> (I' \<U> R))"
    by (subst inf.commute) (rule tls.leads_to_via_weakenR)
  also have "\<dots> \<le> ?rhs"
    by (strengthen ord_to_strengthen(1)[OF tls.until.supL_ordering_le]) (rule order.refl)
  finally show ?thesis .
qed

lemma leads_to_via_disj: \<comment>\<open> more like a chaining rule \<close>
  shows "(P \<^bold>\<longrightarrow>\<^sub>\<box> I \<U> Q) \<sqinter> (Q \<^bold>\<longrightarrow>\<^sub>\<box> I' \<U> R) \<le> (P \<squnion> Q \<^bold>\<longrightarrow>\<^sub>\<box> (I \<squnion> I') \<U> R)"
by (simp add: boolean_implication_def inf.coboundedI2 le_supI2 tls.always.mono tls.until.mono)


subsubsection\<open> Fairness\label{sec:tls-fairness} \<close>

text\<open>

A few renderings of weak fairness. \<^citet>\<open>"vanGlabbeekHofner:2019"\<close> call this
``response to insistence'' as a generalisation of weak fairness.

\<close>

definition weakly_fair :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "weakly_fair enabled taken = \<box>enabled \<^bold>\<longrightarrow>\<^sub>\<box> \<diamond>taken"

lemma weakly_fair_def2:
  shows "tls.weakly_fair enabled taken = \<box>(-(\<box>(enabled \<sqinter> -taken)))"
by (simp add: tls.weakly_fair_def tls.always_def tls.eventually.sup)

lemma weakly_fair_def3:
  shows "tls.weakly_fair enabled taken = \<diamond>\<box>enabled \<^bold>\<longrightarrow>\<^sub>B \<box>\<diamond>taken"
by (simp add: tls.weakly_fair_def boolean_implication.conv_sup
              tls.always.neg tls.always_eventually_sup tls.eventually.neg
        flip: tls.eventually.sup)

lemma weakly_fair_def4:
  shows "tls.weakly_fair enabled taken = \<box>\<diamond>(enabled \<^bold>\<longrightarrow>\<^sub>B taken)"
by (simp add: tls.weakly_fair_def boolean_implication.conv_sup tls.always.neg tls.eventually.sup)

setup \<open>Sign.mandatory_path "weakly_fair"\<close>

lemma mono:
  assumes "P' \<le> P"
  assumes "Q \<le> Q'"
  shows "tls.weakly_fair P Q \<le> tls.weakly_fair P' Q'"
unfolding tls.weakly_fair_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (rule order.refl)
done

lemma strengthen[strg]:
  assumes "st_ord (\<not>F) P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (tls.weakly_fair P Q) (tls.weakly_fair P' Q')"
using assms by (cases F) (auto simp: tls.weakly_fair.mono)

lemma weakly_fair_triv:
  shows "\<box>\<diamond>(-enabled) \<le> tls.weakly_fair enabled taken"
by (simp add: tls.weakly_fair_def3 boolean_implication.conv_sup tls.always.neg tls.eventually.neg)

lemma mp:
  shows "tls.weakly_fair enabled taken \<sqinter> \<box>enabled \<le> \<diamond>taken"
by (simp add: tls.weakly_fair_def boolean_implication.shunt1 tls.always.contractive)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "always"\<close>

lemma weakly_fair:
  shows "\<box>(tls.weakly_fair enabled taken) = tls.weakly_fair enabled taken"
by (simp add: tls.weakly_fair_def tls.always.simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "eventually"\<close>

lemma weakly_fair:
  shows "\<diamond>(tls.weakly_fair enabled taken) = tls.weakly_fair enabled taken"
by (simp add: tls.weakly_fair_def4 tls.always_eventually_always_absorption)

setup \<open>Sign.parent_path\<close>

text\<open>

Similarly for strong fairness. \<^citet>\<open>"vanGlabbeekHofner:2019"\<close> call this
"response to persistence" as a generalisation of strong fairness.

\<close>

definition strongly_fair :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "strongly_fair enabled taken = \<box>\<diamond>enabled \<^bold>\<longrightarrow>\<^sub>\<box> \<diamond>taken"

lemma strongly_fair_def2:
  shows "tls.strongly_fair enabled taken = \<box>(-\<box>(\<diamond>enabled \<sqinter> -taken))"
by (simp add: tls.strongly_fair_def boolean_implication.conv_sup tls.always.neg tls.eventually.sup)

lemma strongly_fair_def3:
  shows "tls.strongly_fair enabled taken = \<box>\<diamond>enabled \<^bold>\<longrightarrow>\<^sub>B \<box>\<diamond>taken"
by (simp add: tls.strongly_fair_def boolean_implication.conv_sup tls.always.neg tls.eventually.neg
                 tls.always_eventually_sup tls.eventually_always_eventually_absorption
        flip: tls.eventually.sup)

setup \<open>Sign.mandatory_path "strongly_fair"\<close>

lemma mono:
  assumes "P' \<le> P"
  assumes "Q \<le> Q'"
  shows "tls.strongly_fair P Q \<le> tls.strongly_fair P' Q'"
unfolding tls.strongly_fair_def
apply (strengthen ord_to_strengthen(1)[OF assms(1)])
apply (strengthen ord_to_strengthen(1)[OF assms(2)])
apply (rule order.refl)
done

lemma strengthen[strg]:
  assumes "st_ord (\<not>F) P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (tls.strongly_fair P Q) (tls.strongly_fair P' Q')"
using assms by (cases F) (auto simp: tls.strongly_fair.mono)

lemma supL: \<comment>\<open> does not hold for \<^const>\<open>tls.weakly_fair\<close> \<close>
  shows "tls.strongly_fair (enabled1 \<squnion> enabled2) taken
      = (tls.strongly_fair enabled1 taken \<sqinter> tls.strongly_fair enabled2 taken)"
by (simp add: boolean_implication.conv_sup sup_inf_distrib2 tls.always.inf tls.always_eventually_sup
              tls.strongly_fair_def)

lemma weakly_fair_le:
  shows "tls.strongly_fair enabled taken \<le> tls.weakly_fair enabled taken"
by (simp add: tls.strongly_fair_def3 tls.weakly_fair_def3 boolean_implication.mono
              tls.eventually_always_always_eventually_le)

lemma always_enabled_weakly_fair_strongly_fair:
  shows "\<box>enabled \<le> tls.weakly_fair enabled taken \<^bold>\<longleftrightarrow>\<^sub>B tls.strongly_fair enabled taken"
by (simp add: boolean_eq_def boolean_implication_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "always"\<close>

lemma strongly_fair:
  shows "\<box>(tls.strongly_fair enabled taken) = tls.strongly_fair enabled taken"
by (simp add: tls.strongly_fair_def)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "eventually"\<close>

lemma strongly_fair:
  shows "\<diamond>(tls.strongly_fair enabled taken) = tls.strongly_fair enabled taken"
by (simp add: tls.strongly_fair_def2 tls.always.neg tls.always_eventually_always_absorption)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Safety Properties\label{sec:tls-safety} \<close>

text\<open>

We now carve the safety properties out of the \<^typ>\<open>('a, 's, 'v) tls\<close> lattice.

References:
 \<^item> \<^citet>\<open>\<open>\S2\<close> in "AlpernSchneider:1985" and "AlpernDemersSchneider:1986" and "Schneider:1987"\<close>
  \<^item> observes that Lamport's earlier definitions do not work without stuttering
  \<^item> provides the now standard definition that works with and without stuttering
 \<^item> \<^citet>\<open>\<open>\S2.2\<close> in "AbadiLamport:1991"\<close>: topological definitions and intuitions
 \<^item> \<^citet>\<open>\<open>\S2.2\<close> in "Sistla:1994"\<close>

We go a different way: we establish a Galois connection with \<^typ>\<open>('a, 's, 'v) spec\<close>.

Observations:
 \<^item> our safety closure for \<^typ>\<open>('a, 's, 'v) tls\<close> introduces infinite sequences to stand for the
   prefixes in \<^typ>\<open>('a, 's, 'v) spec\<close>
  \<^item> i.e., the non-termination of trace \<open>\<sigma>\<close> (\<open>trace.term \<sigma> = None\<close>)
    is represented by a behavior ending with \<open>trace.final \<sigma>\<close> infinitely stuttered
  \<^item> \<^citet>\<open>\<open>\S2.1\<close> in "AbadiLamport:1991"\<close> consider these behaviors to represent terminating processes

\<close>

setup \<open>Sign.mandatory_path "raw"\<close>

definition to_spec :: "('a, 's, 'v) behavior.t set \<Rightarrow> ('a, 's, 'v) trace.t set" where
  "to_spec T = {behavior.take i \<omega> |\<omega> i. \<omega> \<in> T}"

definition from_spec :: "('a, 's, 'v) trace.t set \<Rightarrow> ('a, 's, 'v) behavior.t set" where
  "from_spec S = {\<omega> . \<forall>i. behavior.take i \<omega> \<in> S}"

interpretation safety: galois.powerset raw.to_spec raw.from_spec
by standard (fastforce simp: raw.to_spec_def raw.from_spec_def)

setup \<open>Sign.mandatory_path "from_spec"\<close>

lemma empty:
  shows "raw.from_spec {} = {}"
by (simp add: raw.from_spec_def)

lemma singleton:
  shows "raw.from_spec (Safety_Logic.raw.singleton \<sigma>)
       = \<Union>(raw.singleton ` {\<omega> . \<forall>i. behavior.take i \<omega> \<in> Safety_Logic.raw.singleton \<sigma>})" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs" by (force simp: raw.from_spec_def TLS.raw.singleton_def)
  show "?rhs \<subseteq> ?lhs"
    by (clarsimp simp: raw.from_spec_def TLS.raw.singleton_def Safety_Logic.raw.singleton_def
                 elim!: behavior.stuttering.clE)
       (metis behavior.stuttering.equiv.takeE raw.spec.closed raw.spec.closed.stuttering_closed
              trace.stuttering.clI trace.stuttering.closed_conv)
qed

lemma sup:
  assumes "P \<in> raw.spec.closed"
  assumes "Q \<in> raw.spec.closed"
  shows "raw.from_spec (P \<union> Q) = raw.from_spec P \<union> raw.from_spec Q"
by (rule antisym[OF _ raw.safety.sup_upper_le])
   (clarsimp simp: raw.from_spec_def;
    meson behavior.take.mono downwards.closed_in linorder_le_cases
          raw.spec.closed.downwards_closed[OF assms(1)] raw.spec.closed.downwards_closed[OF assms(2)])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "to_spec"\<close>

lemma singleton:
  shows "raw.to_spec (TLS.raw.singleton \<omega>)
       = (\<Union>i. Safety_Logic.raw.singleton (behavior.take i \<omega>))" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    by (fastforce simp: TLS.raw.singleton_def raw.to_spec_def
                        Safety_Logic.raw.singleton_def raw.spec.cl_def
                  elim: behavior.stuttering.clE behavior.stuttering.equiv.takeE[OF sym]
                        trace.stuttering.clI[OF _ sym, rotated])
  show "?rhs \<subseteq> ?lhs"
    by (fastforce simp: Safety_Logic.raw.singleton_def raw.spec.cl_def TLS.raw.singleton_def
                        raw.to_spec_def trace.less_eq_take_def trace.take.behavior.take
                  elim: downwards.clE trace.stuttering.clE trace.stuttering.equiv.behavior.takeE)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "safety"\<close>

lemma cl_altI:
  assumes "\<And>i. \<exists>\<omega>' \<in> P. behavior.take i \<omega> = behavior.take i \<omega>'"
  shows "\<omega> \<in> raw.safety.cl P"
using assms by (fastforce simp: raw.safety.cl_def raw.from_spec_def raw.to_spec_def)

lemma cl_altE:
  assumes "\<omega> \<in> raw.safety.cl P"
  obtains \<omega>' where "\<omega>' \<in> P" and "behavior.take i \<omega> = behavior.take i \<omega>'"
proof(atomize_elim, cases "enat i \<le> tlength (behavior.rest \<omega>)")
  case True with assms show "\<exists>\<omega>'. \<omega>' \<in> P \<and> behavior.take i \<omega> = behavior.take i \<omega>'"
    by (clarsimp simp: raw.safety.cl_def raw.from_spec_def raw.to_spec_def)
       (metis behavior.take.length behavior.take.sel(3)  ttake_eq_None_conv(1)
              min.absorb2 min_enat2_conv_enat the_enat.simps)
next
  case False with assms show "\<exists>\<omega>'. \<omega>' \<in> P \<and> behavior.take i \<omega> = behavior.take i \<omega>'"
    by (clarsimp simp: raw.safety.cl_def raw.from_spec_def raw.to_spec_def)
       (metis behavior.continue.take_drop_id behavior.take.continue_id leI)
qed

lemma cl_alt_def: \<comment>\<open> \<^citet>\<open>"AlpernDemersSchneider:1986"\<close>: the classical definition: \<open>\<omega>\<close> belongs to the safety closure of \<open>P\<close> if every prefix of \<open>\<omega>\<close> can be extended to a behavior in \<open>P\<close> \<close>
  shows "raw.safety.cl P = {\<omega>. \<forall>i. \<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> P}" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<subseteq> ?rhs"
    by clarsimp (metis behavior.continue.take_drop_id raw.safety.cl_altE)
  show "?rhs \<subseteq> ?lhs"
  proof(clarify intro!: raw.safety.cl_altI)
    fix \<omega> i
    assume "\<forall>j. \<exists>\<beta>. behavior.take j \<omega> @-\<^sub>B \<beta> \<in> P"
    then show "\<exists>\<omega>'\<in>P. behavior.take i \<omega> = behavior.take i \<omega>'"
      by (force dest: spec[where x=i]
               intro: exI[where x=i] rev_bexI
                simp: behavior.take.continue trace.take.behavior.take trace.continue.self_conv
                      ttake_eq_None_conv length_ttake
               split: option.split enat.split)
  qed
qed

lemma closed_alt_def: \<comment>\<open> If \<open>\<omega>\<close> is not in \<open>P\<close> then some prefix of \<open>\<omega>\<close> has irretrievably gone wrong \<close>
  shows "raw.safety.closed = {P. \<forall>\<omega>. \<omega> \<notin> P \<longrightarrow> (\<exists>i. \<forall>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<notin> P)}"
unfolding raw.safety.closed_def raw.safety.cl_alt_def by fast

lemma closed_alt_def2: \<comment>\<open> Contraposition gives the customary prefix-closure definition \<close>
  shows "raw.safety.closed = {P. \<forall>\<omega>. (\<forall>i. \<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> P) \<longrightarrow> \<omega> \<in> P}"
unfolding raw.safety.closed_alt_def by fast

lemma closedI2:
  assumes "\<And>\<omega>. (\<And>i. \<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> P) \<Longrightarrow> \<omega> \<in> P"
  shows "P \<in> raw.safety.closed"
using assms unfolding raw.safety.closed_alt_def2 by fast

lemma closedE2:
  assumes "P \<in> raw.safety.closed"
  assumes "\<And>i. \<omega> \<notin> P \<Longrightarrow> \<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> P"
  shows "\<omega> \<in> P"
using assms unfolding raw.safety.closed_alt_def2 by blast

setup \<open>Sign.mandatory_path "cl"\<close>

lemma state_prop:
  shows "raw.safety.cl (raw.state_prop P) = raw.state_prop P"
by (simp add: raw.safety.cl_alt_def raw.state_prop_def)

lemma terminated_iff:
  assumes "\<omega> \<in> raw.terminated"
  shows "\<omega> \<in> raw.safety.cl P \<longleftrightarrow> \<omega> \<in> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  from assms obtain i where "tlength (behavior.rest \<omega>) = enat i"
    by (clarsimp simp: raw.terminated_def tfinite_tlength_conv)
  then show "?lhs \<Longrightarrow> ?rhs"
    by (metis raw.safety.cl_altE[where i="Suc i"]
              behavior.continue.take_drop_id behavior.take.continue_id enat_ord_simps(2) lessI)
qed (simp add: raw.safety.expansive')

lemma terminated:
  shows "raw.safety.cl raw.terminated = raw.idle \<union> raw.terminated" (is "?lhs = ?rhs")
proof(rule antisym[OF subsetI subsetI])
  fix \<omega>
  assume "\<omega> \<in> ?lhs"
  then have "snd (tnth (behavior.rest \<omega>) i) = behavior.init \<omega>"
         if "enat i < tlength (behavior.rest \<omega>)"
        for i
    using that
    by (clarsimp simp: raw.terminated_def behavior.take_def behavior.split_all behavior.sset.simps
                       split_def
             simp del: ttake.simps
                elim!: raw.safety.cl_altE[where i="Suc i"])
       (metis (no_types, lifting) Suc_ile_eq in_tset_conv_tnth nth_ttake
              doubleton_eq_iff insert_image insert_absorb2 lessI subset_singletonD ttake_eq_None_conv(1))
  then have "behavior.sset \<omega> \<subseteq> {behavior.init \<omega>}"
    by (cases \<omega>) (clarsimp simp: behavior.sset.simps tset_conv_tnth)
  then show "\<omega> \<in> ?rhs"
    by (simp add: raw.idle_alt_def raw.terminated_def)
next
  show "\<omega> \<in> ?lhs" if "\<omega> \<in> ?rhs" for \<omega>
    using that
  proof(cases rule: UnE[consumes 1, case_names idle terminated])
    case idle show ?thesis
    proof(rule raw.safety.cl_altI)
      fix i
      let ?\<omega>' = "behavior.take i \<omega> @-\<^sub>B TNil undefined"
      from idle have "?\<omega>' \<in> raw.terminated"
        by (auto simp: raw.idle_alt_def raw.terminated_def behavior.sset.continue
                 dest: subsetD[OF behavior.sset.take_le]
                split: option.split)
      moreover
      from idle have "behavior.take i \<omega> = behavior.take i ?\<omega>'"
        by (simp add: raw.idle_alt_def behavior.take.continue trace.take.behavior.take
                      length_ttake tfinite_tlength_conv)
      ultimately show "\<exists>\<omega>'\<in>raw.terminated. behavior.take i \<omega> = behavior.take i \<omega>'"
        by blast
    qed
  qed (auto intro: raw.safety.expansive')
qed

lemma le_terminated_bot:
  assumes "P \<in> behavior.stuttering.closed"
  assumes "raw.safety.cl P \<subseteq> raw.terminated"
  shows "P = {}"
proof(rule ccontr)
  assume \<open>P \<noteq> {}\<close> then obtain \<omega> where "\<omega> \<in> P" by blast
  let ?\<omega>' = "behavior.B (behavior.init \<omega>) (trepeat (undefined, behavior.init \<omega>))"
  from \<open>\<omega> \<in> P\<close> have "?\<omega>' \<in> raw.safety.cl P"
    by (fastforce intro: exI[where x="behavior.rest \<omega>"]
                         behavior.stuttering.f_closedI[OF \<open>P \<in> behavior.stuttering.closed\<close>]
                   simp: raw.safety.cl_alt_def behavior.take.trepeat behavior.continue.simps
                         behavior.natural.tshift collapse.tshift trace.natural'.replicate
                         trace.final'.replicate
                         behavior.stuttering.f_closed[OF \<open>P \<in> behavior.stuttering.closed\<close>]
              simp flip: behavior.natural_def)
  moreover have "?\<omega>' \<notin> raw.terminated"
    by (simp add: raw.terminated_def)
  moreover note \<open>raw.safety.cl P \<subseteq> raw.terminated\<close>
  ultimately show False by blast
qed

lemma always_le:
  shows "raw.safety.cl (raw.always P) \<subseteq> raw.always (raw.safety.cl P)"
unfolding raw.always_alt_def raw.safety.cl_alt_def subset_iff mem_Collect_eq
proof(intro allI impI)
  fix \<omega> i \<omega>' j
  assume *: "\<forall>i. \<exists>\<beta>. \<forall>k \<omega>'. behavior.dropn k (behavior.take i \<omega> @-\<^sub>B \<beta>) = Some \<omega>' \<longrightarrow> \<omega>' \<in> P"
     and **: "behavior.dropn i \<omega> = Some \<omega>'"
  from spec[where x="i + j", OF *] ** behavior.take.dropn[OF **, where j=j]
  show "\<exists>\<beta>. behavior.take j \<omega>' @-\<^sub>B \<beta> \<in> P"
    by (clarsimp dest!: spec[where x=i])
       (subst (asm) behavior.dropn.continue_shorter;
        force simp: length_ttake trace.dropn.behavior.take
              dest: behavior.dropn.eq_Some_tlengthD
             split: enat.split)
qed

lemma eventually:
  assumes "P \<noteq> \<bottom>"
  shows "raw.safety.cl (raw.eventually P)
      = -raw.eventually raw.terminated \<union> raw.eventually P" (is "?lhs = ?rhs")
proof(rule antisym[OF subsetI iffD2[OF Un_subset_iff, simplified conj_explode, rule_format, OF subsetI]])
  show "\<omega> \<in> ?rhs" if "\<omega> \<in> ?lhs" for \<omega>
  proof(cases "tlength (behavior.rest \<omega>)")
    case (enat i) with that show ?thesis
      by (fastforce dest: spec[where x="Suc i"]
                    simp: raw.safety.cl_alt_def raw.terminated_def behavior.take.continue_id)
  qed (simp add: raw.eventually.terminated tfinite_tlength_conv)
  from assms obtain \<omega>\<^sub>P where "\<omega>\<^sub>P \<in> P" by blast
  show "\<omega> \<in> ?lhs" if "\<omega> \<in> -raw.eventually raw.terminated" for \<omega>
  proof(intro raw.safety.cl_altI exI bexI)
    fix i
    let ?\<omega>' = "behavior.take i \<omega> @-\<^sub>B TCons (undefined, behavior.init \<omega>\<^sub>P) (behavior.rest \<omega>\<^sub>P)"
    from \<open>\<omega>\<^sub>P \<in> P\<close> \<open>\<omega> \<in> -raw.eventually raw.terminated\<close> show "?\<omega>' \<in> raw.eventually P"
      unfolding raw.eventually.terminated
      by (auto intro!: exI[where x="Suc i"]
                 simp: raw.eventually_alt_def tfinite_tlength_conv behavior.dropn.continue
                       length_ttake ttake_eq_None_conv)
    from \<open>\<omega> \<in> -raw.eventually raw.terminated\<close> show "behavior.take i \<omega> = behavior.take i ?\<omega>'"
      by (simp add: raw.eventually.terminated behavior.take.continue trace.take.behavior.take
                    length_ttake tfinite_tlength_conv
             split: enat.split)
  qed
  show "raw.eventually P \<subseteq> ?lhs"
    by (fast intro!: order.trans[OF _ raw.safety.expansive])
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma always_eventually:
  assumes "P \<in> raw.safety.closed"
  assumes "\<forall>i. \<exists>j\<ge>i. \<exists>\<beta>. behavior.take j \<omega> @-\<^sub>B \<beta> \<in> P"
  shows "\<omega> \<in> P"
using assms(1)
proof(rule raw.safety.closedE2)
  fix i
  from spec[OF assms(2), where x=i] obtain j \<beta> where "i \<le> j" and "behavior.take j \<omega> @-\<^sub>B \<beta> \<in> P"
    by blast
  then show "\<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> P" if "\<omega> \<notin> P"
    using that
    by (clarsimp simp: tdropn_tshift2 behavior.continue.tshift2 behavior.continue.take_drop_shorter length_ttake
                        behavior.continue.term_Some behavior.take.term_Some_conv ttake_eq_Some_conv
                split: enat.split split_min
               intro!: exI[where x="tdropn i (behavior.rest (behavior.take j \<omega> @-\<^sub>B \<beta>))"])
qed

lemma sup:
  assumes "P \<in> raw.safety.closed"
  assumes "Q \<in> raw.safety.closed"
  shows "P \<union> Q \<in> raw.safety.closed"
by (clarsimp simp: raw.safety.closed_alt_def2)
   (meson assms raw.safety.closed.always_eventually sup.cobounded1 sup.cobounded2)

lemma unless: \<comment>\<open> \<^citet>\<open> \<open>\S3.1\<close> in "Sistla:1994"\<close> -- minimality is irrelevant \<close>
  assumes "P \<in> raw.safety.closed"
  assumes "Q \<in> raw.safety.closed"
  shows "raw.unless P Q \<in> raw.safety.closed"
proof(rule raw.safety.closedI2)
  fix \<omega> assume *: "\<exists>\<beta>. behavior.take i \<omega> @-\<^sub>B \<beta> \<in> raw.unless P Q" for i
  show "\<omega> \<in> raw.unless P Q"
  proof(cases "\<forall>i j \<omega>'. \<exists>\<beta>. behavior.dropn i \<omega> = Some \<omega>' \<longrightarrow> behavior.take j \<omega>' @-\<^sub>B \<beta> \<in> P")
    case True
    with \<open>P \<in> raw.safety.closed\<close> have "behavior.dropn i \<omega> = Some \<omega>' \<longrightarrow> \<omega>' \<in> P" for i \<omega>'
      by (blast intro: raw.safety.closedE2)
    then show ?thesis
      by (simp add: raw.always_alt_def)
  next
    case False
    then obtain \<omega>' k l
      where **: "behavior.dropn k \<omega> = Some \<omega>'" "\<forall>\<beta>. behavior.take l \<omega>' @-\<^sub>B \<beta> \<notin> P"
      by clarsimp
    {
      fix i \<beta>
      assume kli: "k + l \<le> i"
      moreover
      note **
      moreover
      from kli have "\<exists>j. i - k = l + j" by presburger
      moreover
      from \<open>behavior.dropn k \<omega> = Some \<omega>'\<close> kli
      have ***: "k \<le> length (trace.rest (behavior.take i \<omega>))"
        by (fastforce simp: length_ttake split: enat.splits
                      dest: behavior.dropn.eq_Some_tlengthD)
      ultimately have ****: "\<forall>\<omega>''. behavior.dropn k (behavior.take i \<omega> @-\<^sub>B \<beta>) = Some \<omega>'' \<longrightarrow> \<omega>'' \<notin> P"
        by (force simp: behavior.dropn.continue_shorter trace.dropn.behavior.take behavior.take.add
             simp flip: behavior.continue.tshift2)
      {
        assume PQ: "behavior.take i \<omega> @-\<^sub>B \<beta> \<in> raw.unless P Q"
        from **** PQ obtain m
          where "m \<le> k"
            and "\<forall>\<omega>'. behavior.dropn m (behavior.take i \<omega> @-\<^sub>B \<beta>) = Some \<omega>' \<longrightarrow> \<omega>' \<in> Q"
            and "\<forall>p<m. (\<forall>\<omega>'. behavior.dropn p (behavior.take i \<omega> @-\<^sub>B \<beta>) = Some \<omega>' \<longrightarrow> \<omega>' \<in> P)"
          by (auto 6 0 simp: raw.until_def raw.always_alt_def)
             (metis behavior.dropn.shorterD leI nle_le option.sel)
        with kli ***
        have "(\<exists>m\<le>k. (\<forall>\<omega>'. behavior.dropn m \<omega> = Some \<omega>' \<longrightarrow> behavior.take (i - m) \<omega>' @-\<^sub>B \<beta> \<in> Q)
                   \<and> (\<forall>p<m. (\<forall>\<omega>'. behavior.dropn p \<omega> = Some \<omega>' \<longrightarrow> behavior.take (i - p) \<omega>' @-\<^sub>B \<beta> \<in> P)))"
          by (clarsimp simp: exI[where x=m] behavior.dropn.continue_shorter trace.dropn.behavior.take)
      }
    }
    then have "\<forall>i. \<exists>n\<ge>i. \<exists>m\<le>k. \<exists>\<beta>. (\<forall>\<omega>'. behavior.dropn m \<omega> = Some \<omega>' \<longrightarrow> behavior.take (n - m) \<omega>' @-\<^sub>B \<beta> \<in> Q)
                                  \<and> (\<forall>p<m. \<forall>\<omega>'. behavior.dropn p \<omega> = Some \<omega>' \<longrightarrow> behavior.take (n - p) \<omega>' @-\<^sub>B \<beta> \<in> P)"
      using * by (metis nle_le)
    then obtain m
      where "m \<le> k" "\<forall>i. \<exists>n\<ge>i. \<exists>\<beta>. (\<forall>\<omega>'. behavior.dropn m \<omega> = Some \<omega>' \<longrightarrow> behavior.take (n - m) \<omega>' @-\<^sub>B \<beta> \<in> Q)
                              \<and> (\<forall>p<m. \<forall>\<omega>'. behavior.dropn p \<omega> = Some \<omega>' \<longrightarrow> behavior.take (n - p) \<omega>' @-\<^sub>B \<beta> \<in> P)"
      by (clarsimp simp: always_eventually_pigeonhole)
    with behavior.dropn.shorterD[OF \<open>behavior.dropn k \<omega> = Some \<omega>'\<close> \<open>m \<le> k\<close>]
         raw.safety.closed.always_eventually[OF \<open>P \<in> raw.safety.closed\<close>]
         raw.safety.closed.always_eventually[OF \<open>Q \<in> raw.safety.closed\<close>]
    show "\<omega> \<in> raw.unless P Q"
      apply -
      apply clarsimp
      apply (rule raw.untilI, assumption)
       apply (meson add_le_imp_le_diff)
      apply (metis add_le_imp_le_diff option.sel behavior.dropn.shorterD[OF _ less_imp_le])
      done
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "downwards.closed"\<close>

lemma to_spec:
  shows "range raw.to_spec \<subseteq> downwards.closed"
by (fastforce elim: downwards.clE simp: raw.to_spec_def trace.less_eq_take_def trace.take.behavior.take)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "trace.stuttering.closed"\<close>

lemma to_spec:
  shows "raw.to_spec ` behavior.stuttering.closed \<subseteq> trace.stuttering.closed"
by (fastforce simp: raw.to_spec_def
              elim: trace.stuttering.clE trace.stuttering.equiv.E trace.stuttering.equiv.behavior.takeE
              dest: behavior.stuttering.closed_in)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "raw.spec.closed"\<close>

lemma to_spec:
  shows "raw.to_spec ` behavior.stuttering.closed \<subseteq> raw.spec.closed"
using downwards.closed.to_spec trace.stuttering.closed.to_spec by (blast intro: raw.spec.closed.I)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "behavior.stuttering.closed"\<close>

lemma from_spec:
  shows "raw.from_spec ` trace.stuttering.closed
      \<subseteq> (behavior.stuttering.closed :: ('a, 's, 'v) behavior.t set set)"
proof -
  have *: "behavior.take i \<omega>\<^sub>2 \<in> P "
    if "\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2" and "\<forall>i. behavior.take i \<omega>\<^sub>1 \<in> P" and "P \<in> trace.stuttering.closed"
   for \<omega>\<^sub>1 \<omega>\<^sub>2 i and P :: "('a, 's, 'v) trace.t set"
    using that(2-)
    by - (rule behavior.stuttering.equiv.takeE[OF sym[OF \<open>\<omega>\<^sub>1 \<simeq>\<^sub>T \<omega>\<^sub>2\<close>], where i=i];
          fastforce intro: trace.stuttering.closed_in)
  show ?thesis
    by (fastforce simp: raw.from_spec_def elim: behavior.stuttering.clE *)
qed

lemma safety_cl:
  assumes "P \<in> behavior.stuttering.closed"
  shows "raw.safety.cl P \<in> behavior.stuttering.closed"
unfolding raw.safety.cl_def using assms
by (blast intro: subsetD[OF behavior.stuttering.closed.from_spec]
                 subsetD[OF trace.stuttering.closed.to_spec])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "tls"\<close>

lift_definition to_spec :: "('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) spec" is raw.to_spec
using raw.spec.closed.to_spec by blast

lift_definition from_spec :: "('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) tls" is raw.from_spec
by (meson image_subset_iff behavior.stuttering.closed.from_spec raw.spec.closed.stuttering_closed)

interpretation safety: galois.complete_lattice_class tls.to_spec tls.from_spec
by standard (transfer; simp add: raw.safety.galois)

setup \<open>Sign.mandatory_path "from_spec"\<close>

lemma singleton:
  notes spec.singleton.transfer[transfer_rule]
  shows "tls.from_spec (spec.singleton \<sigma>)
       = \<Squnion>(tls.singleton ` {\<omega> . \<forall>i. behavior.take i \<omega> \<in> Safety_Logic.raw.singleton \<sigma>})"
by transfer (simp add: behavior.stuttering.cl_bot raw.from_spec.singleton)

lemmas bot = raw.from_spec.empty[transferred]

lemma sup:
  shows "tls.from_spec (P \<squnion> Q) = tls.from_spec P \<squnion> tls.from_spec Q"
by transfer (rule raw.from_spec.sup)

lemmas Inf = tls.safety.upper_Inf
lemmas inf = tls.safety.upper_inf

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "to_spec"\<close>

lemma singleton:
  notes spec.singleton.transfer[transfer_rule]
  shows "tls.to_spec (tls.singleton \<omega>) = (\<Squnion>i. spec.singleton (behavior.take i \<omega>))"
by transfer (simp add: raw.to_spec.singleton)

lemmas bot = tls.safety.lower_bot

lemmas Sup = tls.safety.lower_Sup
lemmas sup = tls.safety.lower_sup

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "safety"\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

lemma transfer[transfer_rule]:
  shows "rel_fun (pcr_tls (=) (=) (=)) (pcr_tls (=) (=) (=)) raw.safety.cl tls.safety.cl"
unfolding raw.safety.cl_def tls.safety.cl_def by transfer_prover

lemma bot[iff]:
  shows "tls.safety.cl \<bottom> = \<bottom>"
by (simp add: tls.safety.cl_def tls.from_spec.bot tls.safety.lower_bot)

lemma sup:
  shows "tls.safety.cl (P \<squnion> Q) = tls.safety.cl P \<squnion> tls.safety.cl Q"
by (simp add: tls.safety.cl_def tls.from_spec.sup tls.to_spec.sup)

lemmas state_prop = raw.safety.cl.state_prop[transferred]
lemmas always_le = raw.safety.cl.always_le[transferred]

lemma eventually: \<comment>\<open> all the infinite traces and any finite ones that satisfy \<open>\<diamond>P\<close> \<close>
  assumes "P \<noteq> \<bottom>"
  shows "tls.safety.cl (\<diamond>P) = -\<diamond>tls.terminated \<squnion> \<diamond>P"
using assms by transfer (rule raw.safety.cl.eventually)

lemma terminated_iff:
  assumes "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.terminated"
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.safety.cl P \<longleftrightarrow> \<lblot>\<omega>\<rblot>\<^sub>T \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
using assms
by transfer
   (simp add: raw.singleton_def behavior.stuttering.least_conv raw.safety.cl.terminated_iff
              behavior.stuttering.closed.safety_cl behavior.stuttering.closed.raw.terminated)

lemma terminated:
  shows "tls.safety.cl tls.terminated = tls.idle \<squnion> tls.terminated"
by transfer (simp add: raw.safety.cl.terminated)

lemma not_terminated:
  shows "tls.safety.cl (- tls.terminated) = - tls.terminated" (is "?lhs = ?rhs")
proof -
  have "?lhs = tls.safety.cl (\<diamond>(- tls.terminated))"
    by (simp flip: tls.always.neg tls.terminated.eq_always_terminated)
  also have "\<dots> = - \<diamond>tls.terminated \<squnion> \<diamond>(- tls.terminated)"
    by (metis tls.safety.cl.eventually tls.terminated.not_top
              boolean_algebra.compl_zero boolean_algebra_class.boolean_algebra.double_compl)
  also have "\<dots> = ?rhs"
    by (simp add: sup.absorb2 tls.eventually.expansive
            flip: tls.always.neg tls.terminated.eq_always_terminated)
  finally show ?thesis .
qed

lemma le_terminated_conv:
  shows "tls.safety.cl P \<le> tls.terminated \<longleftrightarrow> P = \<bottom>" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by transfer (rule raw.safety.cl.le_terminated_bot)
  show "?rhs \<Longrightarrow> ?lhs"
    by simp
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma transfer[transfer_rule]:
  shows "rel_set (pcr_tls (=) (=) (=))
                 (behavior.stuttering.closed \<inter> raw.safety.closed)
                 tls.safety.closed" (is "rel_set _ ?lhs ?rhs")
proof(rule rel_setI)
  fix X assume "X \<in> ?lhs" then show "\<exists>Y\<in>?rhs. pcr_tls (=) (=) (=) X Y"
    by (metis (no_types, opaque_lifting) raw.safety.cl_def raw.safety.closed_conv tls.safety.closed_upper
              tls.from_spec.rep_eq TLS_inverse cr_tls_def tls.pcr_cr_eq tls.to_spec.rep_eq Int_iff)
next
  fix Y assume "Y \<in> ?rhs" then show "\<exists>X\<in>?lhs. pcr_tls (=) (=) (=) X Y"
    by (metis tls.safety.cl_def tls.safety.closed_conv tls.from_spec.rep_eq
              tls.pcr_cr_eq cr_tls_def unTLS raw.safety.closed_upper Int_iff)
qed

lemma bot:
  shows "\<bottom> \<in> tls.safety.closed"
by (simp add: tls.safety.closed_clI)

lemma sup:
  assumes "P \<in> tls.safety.closed"
  assumes "Q \<in> tls.safety.closed"
  shows "P \<squnion> Q \<in> tls.safety.closed"
by (simp add: assms tls.safety.closed_clI tls.safety.cl.sup flip: tls.safety.closed_conv)

lemmas inf = tls.safety.closed_inf

lemma boolean_implication:
  assumes "-P \<in> tls.safety.closed"
  assumes "Q \<in> tls.safety.closed"
  shows "P \<^bold>\<longrightarrow>\<^sub>B Q \<in> tls.safety.closed"
by (simp add: assms boolean_implication.conv_sup tls.safety.closed.sup)

lemma state_prop:
  shows "tls.state_prop P \<in> tls.safety.closed"
by (simp add: tls.safety.closed_clI tls.safety.cl.state_prop)

lemma not_terminated:
  shows "- tls.terminated \<in> tls.safety.closed"
by (simp add: tls.safety.closed_clI tls.safety.cl.not_terminated)

lemma unless:
  assumes "P \<in> tls.safety.closed"
  assumes "Q \<in> tls.safety.closed"
  shows "tls.unless P Q \<in> tls.safety.closed"
using assms by transfer (blast intro: raw.safety.closed.unless)

lemma always:
  assumes "P \<in> tls.safety.closed"
  shows "tls.always P \<in> tls.safety.closed"
by (simp add: assms tls.always_alt_def tls.safety.closed.bot tls.safety.closed.unless)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

lemma until_unless_le:
  assumes "P \<in> tls.safety.closed"
  assumes "Q \<in> tls.safety.closed"
  shows "tls.safety.cl (tls.until P Q) \<le> tls.unless P Q"
by (simp add: order.trans[OF tls.safety.cl_inf_le] tls.until.eq_unless_inf_eventually
        flip: tls.safety.closed_conv[OF tls.safety.closed.unless[OF assms]])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma to_spec_le_conv[tls.singleton.le_conv]:
  notes spec.singleton.transfer[transfer_rule]
  shows "\<lblot>\<sigma>\<rblot> \<le> tls.to_spec P \<longleftrightarrow> (\<exists>\<omega> i. \<lblot>\<omega>\<rblot>\<^sub>T \<le> P \<and> \<sigma> = behavior.take i \<omega>)"
by transfer
   (simp add: TLS.raw.singleton_def behavior.stuttering.least_conv Safety_Logic.raw.singleton_def
              raw.spec.least_conv[OF subsetD[OF raw.spec.closed.to_spec]];
    fastforce simp: raw.to_spec_def)

lemma from_spec_le_conv[tls.singleton.le_conv]:
  notes spec.singleton.transfer[transfer_rule]
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.from_spec P \<longleftrightarrow> (\<forall>i. \<lblot>behavior.take i \<omega>\<rblot> \<le> P)"
by transfer
   (simp add: TLS.raw.singleton_def Safety_Logic.raw.singleton_def raw.spec.least_conv
              behavior.stuttering.least_conv
              subsetD[OF behavior.stuttering.closed.from_spec
                         imageI[OF raw.spec.closed.stuttering_closed]];
    simp add: raw.from_spec_def)

lemma safety_cl_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.safety.cl P \<longleftrightarrow> (\<forall>i. \<exists>\<omega>'. \<lblot>\<omega>'\<rblot>\<^sub>T \<le> P \<and> behavior.take i \<omega> = behavior.take i \<omega>')"
by transfer
   (simp add: TLS.raw.singleton_def behavior.stuttering.least_conv behavior.stuttering.closed.safety_cl;
    fastforce intro: raw.safety.cl_altI
               elim: raw.safety.cl_altE)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Maps\label{sec:tls-maps} \<close>

setup \<open>Sign.mandatory_path "tls"\<close>

definition map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('b, 't, 'w) tls" where
  "map af sf vf P = \<Squnion>(tls.singleton ` behavior.map af sf vf ` {\<sigma>. \<lblot>\<sigma>\<rblot>\<^sub>T \<le> P})"

definition invmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s \<Rightarrow> 't) \<Rightarrow> ('v \<Rightarrow> 'w) \<Rightarrow> ('b, 't, 'w) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "invmap af sf vf P = \<Squnion>(tls.singleton ` behavior.map af sf vf -` {\<sigma>. \<lblot>\<sigma>\<rblot>\<^sub>T \<le> P})"

abbreviation amap ::"('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('b, 's, 'v) tls" where
  "amap af \<equiv> tls.map af id id"
abbreviation ainvmap ::"('a \<Rightarrow> 'b) \<Rightarrow> ('b, 's, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "ainvmap af \<equiv> tls.invmap af id id"
abbreviation smap ::"('s \<Rightarrow> 't) \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 't, 'v) tls" where
  "smap sf \<equiv> tls.map id sf id"
abbreviation sinvmap ::"('s \<Rightarrow> 't) \<Rightarrow> ('a, 't, 'v) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "sinvmap sf \<equiv> tls.invmap id sf id"
abbreviation vmap ::"('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'v) tls \<Rightarrow> ('a, 's, 'w) tls" where \<comment>\<open> aka \<open>liftM\<close> \<close>
  "vmap vf \<equiv> tls.map id id vf"
abbreviation vinvmap ::"('v \<Rightarrow> 'w) \<Rightarrow> ('a, 's, 'w) tls \<Rightarrow> ('a, 's, 'v) tls" where
  "vinvmap vf \<equiv> tls.invmap id id vf"

interpretation map_invmap: galois.complete_lattice_distributive_class
  "tls.map af sf vf"
  "tls.invmap af sf vf" for af sf vf
proof standard
  show "tls.map af sf vf P \<le> Q \<longleftrightarrow> P \<le> tls.invmap af sf vf Q" (is "?lhs \<longleftrightarrow> ?rhs") for P Q
  proof(rule iffI)
    show "?lhs \<Longrightarrow> ?rhs"
      by (fastforce simp: tls.map_def tls.invmap_def intro: tls.singleton_le_extI)
    show "?rhs \<Longrightarrow> ?lhs"
      by (fastforce simp: tls.map_def tls.invmap_def tls.singleton_le_conv
                    dest: order.trans[of _ P] behavior.stuttering.equiv.map[where af=af and sf=sf and vf=vf]
                    cong: tls.singleton_cong)
  qed
  show "tls.invmap af sf vf (\<Squnion>X) \<le> \<Squnion>(tls.invmap af sf vf ` X)" for X
    by (fastforce simp: tls.invmap_def)
qed

setup \<open>Sign.mandatory_path "singleton"\<close>

lemma map_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.map af sf vf P \<longleftrightarrow> (\<exists>\<omega>'. \<lblot>\<omega>'\<rblot>\<^sub>T \<le> P \<and> \<lblot>\<omega>\<rblot>\<^sub>T \<le> \<lblot>behavior.map af sf vf \<omega>'\<rblot>\<^sub>T)"
by (simp add: tls.map_def)

lemma invmap_le_conv[tls.singleton.le_conv]:
  shows "\<lblot>\<omega>\<rblot>\<^sub>T \<le> tls.invmap af sf vf P \<longleftrightarrow> \<lblot>behavior.map af sf vf \<omega>\<rblot>\<^sub>T \<le> P"
by (simp add: tls.invmap_def tls.singleton_le_conv)
   (metis behavior.natural.map_natural tls.singleton_eq_conv)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map"\<close>

lemmas bot = tls.map_invmap.lower_bot

lemmas monotone = tls.map_invmap.monotone_lower
lemmas mono = monotoneD[OF tls.map.monotone]

lemmas Sup = tls.map_invmap.lower_Sup
lemmas sup = tls.map_invmap.lower_sup

lemmas Inf_le = tls.map_invmap.lower_Inf_le \<comment>\<open> Converse does not hold \<close>
lemmas inf_le = tls.map_invmap.lower_inf_le \<comment>\<open> Converse does not hold \<close>

lemmas invmap_le = tls.map_invmap.lower_upper_contractive

lemma singleton:
  shows "tls.map af sf vf \<lblot>\<omega>\<rblot>\<^sub>T = \<lblot>behavior.map af sf vf \<omega>\<rblot>\<^sub>T"
by (auto simp: tls.map_def order.eq_iff tls.singleton_le_conv intro: behavior.stuttering.equiv.map)

lemma top:
  assumes "surj af"
  assumes "surj sf"
  assumes "surj vf"
  shows "tls.map af sf vf \<top> = \<top>"
by (rule antisym)
   (auto simp: assms tls.singleton.top tls.map.Sup tls.map.singleton surj_f_inv_f
        intro: exI[where x="behavior.map (inv af) (inv sf) (inv vf) \<sigma>" for \<sigma>])

lemma id:
  shows "tls.map id id id P = P"
    and "tls.map (\<lambda>x. x) (\<lambda>x. x) (\<lambda>x. x) P = P"
by (simp_all add: tls.map_def flip: id_def)

lemma comp:
  shows "tls.map af sf vf \<circ> tls.map ag sg vg = tls.map (af \<circ> ag) (sf \<circ> sg) (vf \<circ> vg)" (is "?lhs = ?rhs")
    and "tls.map af sf vf (tls.map ag sg vg P) = tls.map (\<lambda>a. af (ag a)) (\<lambda>s. sf (sg s)) (\<lambda>v. vf (vg v)) P" (is ?thesis1)
proof -
  have "?lhs P = ?rhs P" for P
    by (rule tls.singleton.exhaust[where x=P])
       (simp add: tls.map.Sup tls.map.singleton map_prod.comp image_image comp_def)
  then show "?lhs = ?rhs" and ?thesis1 by (simp_all add: comp_def)
qed

lemmas map = tls.map.comp

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemmas bot = tls.map_invmap.upper_bot
lemmas top = tls.map_invmap.upper_top

lemmas monotone = tls.map_invmap.monotone_upper
lemmas mono = monotoneD[OF tls.invmap.monotone]

lemmas Sup = tls.map_invmap.upper_Sup
lemmas sup = tls.map_invmap.upper_sup

lemmas Inf = tls.map_invmap.upper_Inf
lemmas inf = tls.map_invmap.upper_inf

lemma singleton:
  shows "tls.invmap af sf vf \<lblot>\<omega>\<rblot>\<^sub>T = \<Squnion>(tls.singleton ` {\<omega>'. \<lblot>behavior.map af sf vf \<omega>'\<rblot>\<^sub>T \<le> \<lblot>\<omega>\<rblot>\<^sub>T})"
by (simp add: tls.invmap_def)

lemma id:
  shows "tls.invmap id id id P = P"
    and "tls.invmap (\<lambda>x. x) (\<lambda>x. x) (\<lambda>x. x) P = P"
unfolding id_def[symmetric] by (metis tls.map.id(1) tls.map_invmap.lower_upper_lower(2))+

lemma comp:
  shows "tls.invmap af sf vf (tls.invmap ag sg vg P) = tls.invmap (\<lambda>x. ag (af x)) (\<lambda>s. sg (sf s)) (\<lambda>v. vg (vf v)) P"  (is "?lhs P = ?rhs P")
    and "tls.invmap af sf vf \<circ> tls.invmap ag sg vg = tls.invmap (ag \<circ> af) (sg \<circ> sf) (vg \<circ> vf)" (is ?thesis1)
proof -
  show "?lhs P = ?rhs P" for P
    by (auto intro: tls.singleton.antisym tls.singleton_le_extI simp: tls.singleton.le_conv)
  then show ?thesis1
    by (simp add: fun_eq_iff comp_def)
qed

lemmas invmap = tls.invmap.comp

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "to_spec"\<close>

lemma map:
  shows "tls.to_spec (tls.map af sf vf P) = spec.map af sf vf (tls.to_spec P)"
by (rule tls.singleton.exhaust[of P])
   (simp add: tls.map.Sup tls.map.singleton spec.map.Sup spec.map.singleton image_image
              tls.to_spec.singleton tls.to_spec.Sup behavior.take.map)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Abadi's axioms for TLA\label{sec:tls-abadi_axioms} \<close>

text\<open>

The axioms for ``propositional'' TLA due to \<^citet>\<open>"Abadi:1990"\<close> hold in this model.
These are complete for \<^const>\<open>tls.always\<close> and \<^const>\<open>tls.eventually\<close>.

Observations:
 \<^item> Abadi says that the temporal system is D aka S4.3Dum; see \<^citet>\<open>\<open>\S8\<close> in "Goldblatt:1992"\<close>
  \<^item> the only interesting axiom here is 5: the discrete-time Dummett axiom
 \<^item> ``propositional'' means that actions are treated separately; we omit this part as we don't have actions ala TLA

\<close>

setup \<open>Sign.mandatory_path "tls.Abadi"\<close>

lemma Ax1:
  shows "\<Turnstile> \<box>(P \<^bold>\<longrightarrow>\<^sub>B Q)\<^bold>\<longrightarrow>\<^sub>B \<box>P \<^bold>\<longrightarrow>\<^sub>B \<box>Q"
by (simp add: tls.valid_def boolean_implication.shunt_top tls.always.always_imp_le)

lemma Ax2:
  shows "\<Turnstile> \<box>P \<^bold>\<longrightarrow>\<^sub>B P"
by (simp add: tls.valid_def boolean_implication.shunt_top tls.always.contractive)

lemma Ax3:
  shows "\<Turnstile> \<box>P \<^bold>\<longrightarrow>\<^sub>B \<box>\<box>P"
by (simp add: tls.validI)

lemma Ax4:
   \<comment>\<open> ``a classical way to express that time is linear -- that any two instants in the future are ordered''
       \<^citet>\<open>\<open>(254) Lemmon formula\<close> in "WarfordVegaStaley:2020"\<close> \<close>
  shows "\<Turnstile> \<box>(\<box>P \<^bold>\<longrightarrow>\<^sub>B Q) \<squnion> \<box>(\<box>Q \<^bold>\<longrightarrow>\<^sub>B P)"
proof -
  have "\<Turnstile> (-\<box>P) \<W> \<box>Q \<squnion> (-\<box>Q) \<W> \<box>P" by (rule tls.unless.ordering)
  also have "\<dots> \<le> \<box>((-\<box>P) \<W> \<box>Q) \<squnion> \<box>((-\<box>Q) \<W> \<box>P)"
    by (metis sup_mono tls.always.idempotent tls.unless.alwaysR_le)
  also have "\<dots> \<le> \<box>(-\<box>P \<squnion> Q) \<squnion> \<box>(-\<box>Q \<squnion> P)"
    by (strengthen ord_to_strengthen(1)[OF tls.unless.sup_le])
       (meson order.refl sup_mono tls.always.contractive tls.always.mono)
  also have "\<dots> = \<box>(\<box>P \<^bold>\<longrightarrow>\<^sub>B Q) \<squnion> \<box>(\<box>Q \<^bold>\<longrightarrow>\<^sub>B P)"
    by (simp add: boolean_implication.conv_sup)
  finally show ?thesis .
qed

lemma Ax5:
  \<comment>\<open> ``expresses the discreteness of time''
      See also \<^citet>\<open>\<open>\S4.1 ``the Dummett formula''\<close> in "WarfordVegaStaley:2020"\<close>: for them
      ``next'' encodes discreteness \<close>
  fixes P :: "('a, 's, 'v) tls"
  shows "\<Turnstile> \<box>(\<box>(P \<^bold>\<longrightarrow>\<^sub>B \<box>P) \<^bold>\<longrightarrow>\<^sub>B P) \<^bold>\<longrightarrow>\<^sub>B \<diamond>\<box>P \<^bold>\<longrightarrow>\<^sub>B P" (is "\<Turnstile> ?goal")
proof -
  have raw_Ax5: "raw.always (raw.eventually (P \<inter> raw.eventually (-P)) \<union> P)
                   \<inter> raw.eventually (raw.always P)
               \<subseteq> P" (is "?lhs \<subseteq> ?rhs")
   for P :: "('a, 's, 'v) behavior.t set"
proof(rule subsetI)
  fix \<omega> assume "\<omega> \<in> ?lhs"
  from IntD2[OF \<open>\<omega> \<in> ?lhs\<close>]
  obtain i
    where "\<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P"
    by (force simp: raw.always_alt_def raw.eventually_alt_def)
  then obtain i
    where i: "\<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P"
      and "\<forall>j<i. \<forall>\<omega>'. behavior.dropn j \<omega> = Some \<omega>' \<longrightarrow> \<omega>' \<notin> raw.always P"
    using ex_has_least_nat[where k=i and P="\<lambda>i. \<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P" and m=id]
    by (auto dest: leD)
  have "\<exists>\<omega>'. behavior.dropn (i - j) \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P" for j
  proof(induct j)
    case (Suc j) show ?case
    proof(cases "j < i")
      case True show ?thesis
      proof(rule ccontr)
        assume "\<nexists>\<omega>'. behavior.dropn (i - Suc j) \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P"
        with \<open>\<exists>\<omega>'. behavior.dropn i \<omega> = Some \<omega>' \<and> \<omega>' \<in> raw.always P\<close>
        have "\<exists>\<omega>'. behavior.dropn (i - Suc j) \<omega> = Some \<omega>' \<and> \<omega>' \<notin> raw.always P"
          using behavior.dropn.shorterD[OF _ diff_le_self] by blast
        then obtain k where "\<exists>\<omega>'. behavior.dropn (i - Suc j + k) \<omega> = Some \<omega>' \<and> \<omega>' \<notin> P"
          by (clarsimp simp: raw.always_alt_def behavior.dropn.add behavior.dropn.Suc) blast
        with Suc.hyps \<open>j < i\<close>
        have "\<exists>\<omega>'. behavior.dropn (i - Suc j) \<omega> = Some \<omega>' \<and> \<omega>' \<notin> P"
          by (fastforce simp: raw.always_alt_def behavior.dropn.add
                       split: nat_diff_split_asm
                        dest: spec[where x="k - 1"])
        with \<open>j < i\<close> IntD1[OF \<open>\<omega> \<in> ?lhs\<close>]
        obtain m n where "\<exists>\<omega>' \<omega>'' \<omega>'''. behavior.dropn (i - Suc j) \<omega> = Some \<omega>' \<and> \<omega>' \<notin> P
                                      \<and> behavior.dropn m \<omega>' = Some \<omega>''         \<and> \<omega>'' \<in> P
                                      \<and> behavior.dropn n \<omega>'' = Some \<omega>'''       \<and> \<omega>''' \<notin> P"
          by (simp add: raw.always_alt_def raw.eventually_alt_def)
             (blast dest: spec[where x="i - Suc j"])
        with \<open>j < i\<close> Suc.hyps
        show False
          by (clarsimp simp: raw.always_alt_def dest!: spec[where x="m + n - 1"] split: nat_diff_split_asm)
             (metis behavior.dropn.Suc behavior.dropn.bind_tl_commute behavior.dropn.dropn bind.bind_lunit)
      qed
    qed (use Suc.hyps in simp)
  qed (use i in simp)
  from this[of i] show "\<omega> \<in> P"
    by (fastforce simp: raw.always_alt_def dest: spec[where x=0])
  qed
  show ?thesis
  proof(rule tls.validI)
    have "\<box>(\<diamond>(P \<sqinter> \<diamond>(- P)) \<squnion> P) \<sqinter> \<diamond>\<box>P \<le> P"
      by (rule raw_Ax5[transferred])
    then have "\<box>(\<diamond>(P \<sqinter> \<diamond>(- P)) \<squnion> P) \<sqinter> \<diamond>\<box>P \<le> P"
      by (simp add: boolean_implication.conv_sup tls.always.neg)
    then show "\<top> \<le> ?goal"
      by - (intro iffD1[OF boolean_implication.shunt1];
            simp add: boolean_implication.conv_sup tls.always.neg)
  qed
qed

lemma Ax6:
  assumes "\<Turnstile> P"
  shows "\<Turnstile> \<box>P"
by (rule tls.always.always_necessitation[OF assms])

\<comment>\<open> Ax7: propositional tautologies: given by the \<^class>\<open>boolean_algebra\<close> instance \<close>

lemma Ax8:
  assumes "\<Turnstile> P"
  assumes "\<Turnstile> P \<^bold>\<longrightarrow>\<^sub>B Q"
  shows "\<Turnstile> Q"
by (rule tls.valid.rev_mp[OF assms])

setup \<open>Sign.parent_path\<close>


subsection\<open> Tweak syntax \<close>

unbundle tls.no_notation
no_notation tls.singleton ("\<lblot>_\<rblot>\<^sub>T")

setup \<open>Sign.mandatory_path "tls"\<close>

bundle extra_notation
begin

notation tls.singleton ("\<lblot>_\<rblot>\<^sub>T" [0])
notation tls.from_spec ("\<lparr>_\<rparr>" [0])

end

bundle no_extra_notation
begin

no_notation tls.singleton ("\<lblot>_\<rblot>\<^sub>T" [0])
no_notation tls.from_spec ("\<lparr>_\<rparr>" [0])

end

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
