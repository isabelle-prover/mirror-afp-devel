subsection \<open>Soundness of the Rules\<close>

theory Soundness
  imports Safety AbstractCommutativity
begin

subsubsection Skip

lemma safe_skip:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "(s, h) \<in> S"
  shows "safe n \<Delta> Cskip (s, h) S"
  using assms
proof (induct n)
  case (Suc n)
  then show ?case
  proof (cases \<Delta>)
    case None
    then show ?thesis
      by (simp add: Suc.prems)
  next
    case (Some a)
    then show ?thesis
      by (simp add: assms)
  qed
qed (simp)


theorem rule_skip:
  "hoare_triple_valid \<Gamma> P Cskip P"
proof (rule hoare_triple_validI)
  let ?\<Sigma> = "\<lambda>\<sigma>. {\<sigma>}"
  show "\<And>s h n. (s, h), (s, h) \<Turnstile> P \<Longrightarrow> safe n \<Gamma> Cskip (s, h) (?\<Sigma> (s, h))"
    by (simp add: safe_skip)
  show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> P \<Longrightarrow> pair_sat {(s, h)} {(s', h')} P"
    by (metis pair_sat_smallerI singleton_iff)
qed

subsubsection \<open>Assign\<close>

inductive_cases red_assign_cases: "red (Cassign x E) \<sigma> C' \<sigma>'"
inductive_cases aborts_assign_cases: "aborts (Cassign x E) \<sigma>"

lemma safe_assign:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>)"
  shows "safe m \<Delta> (Cassign x E) (s, h) { (s(x := edenot E s), h) }"
proof (induct m)
  case (Suc n)
  show "safe (Suc n) \<Delta> (Cassign x E) (s, h) {(s(x := edenot E s), h)}"
  proof (rule safeI)
    show "no_abort \<Delta> (Cassign x E) s h"
      using aborts_assign_cases no_abortI by blast

    show "\<And>H hf C' s' h'.
       \<Delta> = None \<Longrightarrow>
       Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red (Cassign x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       \<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n None C' (s', h'') {(s(x := edenot E s), h)}"
      by (metis Pair_inject insertI1 red_assign_cases safe_skip)

    fix H hf C' s' h' hj v0 \<Gamma>
    assume asm0: "\<Delta> = Some \<Gamma>" "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cassign x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    then have "sat_inv (s(x := edenot E s)) hj \<Gamma>"
      by (meson agrees_update assms sat_inv_agrees)
    then show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s(x := edenot E s), h)}"
      by (metis (no_types, lifting) asm0(2) insertI1 old.prod.inject red_assign_cases safe_skip)
  qed (simp)
qed (simp)

theorem assign_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>)"
      and "collect_existentials P \<inter> fvE E = {}"
  shows "hoare_triple_valid \<Delta> (subA x E P) (Cassign x E) P"
proof -
  define \<Sigma> :: "store \<times> ('i, 'a) heap \<Rightarrow> (store \<times> ('i, 'a) heap) set " where "\<Sigma> = (\<lambda>\<sigma>. { ((fst \<sigma>)(x := edenot E (fst \<sigma>)), snd \<sigma>) })"

  show ?thesis
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> subA x E P \<Longrightarrow> safe n \<Delta> (Cassign x E) (s, h) (\<Sigma> (s, h))"
      using assms safe_assign by (metis \<Sigma>_def fst_eqD snd_eqD)
    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> subA x E P \<Longrightarrow> pair_sat (\<Sigma> (s, h)) (\<Sigma> (s', h')) P"
      by (metis assms(2) \<Sigma>_def fst_conv pair_sat_smallerI singleton_iff snd_conv subA_assign)
  qed
qed

subsubsection \<open>Alloc\<close>


inductive_cases red_alloc_cases: "red (Calloc x E) \<sigma> C' \<sigma>'"
inductive_cases aborts_alloc_cases: "aborts (Calloc x E) \<sigma>"


lemma safe_new_None:
  "safe n (None :: ('i, 'a, nat) cont) (Calloc x E) (s, (Map.empty, gs, gu)) { (s(x := a), (Map.empty(a \<mapsto> (pwrite, edenot E s)), gs, gu)) |a. True }"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeNoneI)
    show "Calloc x E = Cskip \<Longrightarrow> (s, Map.empty, gs, gu) \<in> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}" by simp
    show "no_abort None (Calloc x E) s (Map.empty, gs, gu)"
      using aborts_alloc_cases no_abort.simps(1) by blast
    fix H hf C' s' h'
    assume asm0: "Some H = Some (Map.empty, gs, gu) \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> no_guard H \<and> red (Calloc x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"


    show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
    proof (rule red_alloc_cases)
      show "red (Calloc x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h v
      assume asm1: "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip" "(s', h') = (sa(x := v), h(v \<mapsto> edenot E sa))"
  "v \<notin> dom h"
      then have "v \<notin> dom (get_fh H)"
        by (simp add: dom_normalize)
      then have "v \<notin> dom (get_fh hf)"
        by (metis asm0 fst_conv get_fh.simps no_guard_and_no_heap no_guard_then_smaller_same no_guards_remove plus_comm)

      moreover have "(Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) ## hf"
      proof (rule compatibleI)
        show "compatible_fract_heaps (get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu)) (get_fh hf)"
        proof (rule compatible_fract_heapsI)
          fix l p p'
          assume asm0: "get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) l = Some p \<and> get_fh hf l = Some p'"
          then show "pgte pwrite (padd (fst p) (fst p'))"
            by (metis calculation domIff fst_conv fun_upd_other get_fh.elims option.distinct(1))
          show "snd p = snd p'"
            by (metis asm0 calculation domIff fst_conv fun_upd_other get_fh.elims option.distinct(1))
        qed
        show "\<And>k. get_gu ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) k = None \<or> get_gu hf k = None"
          by (metis asm0 compatible_def compatible_eq get_gu.simps option.discI snd_conv)
        show "\<And>p p'. get_gs ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) = Some p \<and> get_gs hf = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
          by (metis asm0 no_guard_def no_guard_then_smaller_same option.simps(3) plus_comm)
      qed
      then obtain H' where "Some H' = Some (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) \<oplus> Some hf"
        by auto
      moreover have "(s', (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu)) \<in> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        using asm1(1) asm1(3) by blast
      then have "safe n (None :: ('i, 'a, nat) cont) C' (s', (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu)) {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        by (simp add: asm1(2) safe_skip)
      moreover have "full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H')"
      proof -
        have "full_ownership (get_fh H')"
        proof (rule full_ownershipI)
          fix l p
          assume "get_fh H' l = Some p"
          show "fst p = pwrite"
          proof (cases "l = v")
            case True
            then have "get_fh hf l = None"
              using calculation(1) by blast
            then have "get_fh H' l = (Map.empty(v \<mapsto> (pwrite, edenot E sa))) l"
              by (metis calculation(2) fst_conv get_fh.simps sum_second_none_get_fh)
            then show ?thesis
              using True \<open>get_fh H' l = Some p\<close> by fastforce
          next
            case False
            then have "get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) l = None"
              by simp
            then show "fst p = pwrite"
              by (metis (mono_tags, lifting) \<open>get_fh H' l = Some p\<close> asm0 calculation(2) fst_conv full_ownership_def get_fh.elims sum_first_none_get_fh)
          qed
        qed
        moreover have "no_guard H'"
        proof -
          have "no_guard hf"
            by (metis asm0 no_guard_then_smaller_same plus_comm)
          moreover have "no_guard (Map.empty, gs, gu)"
            using asm0 no_guard_then_smaller_same by blast
          ultimately show ?thesis
            by (metis \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hf\<close> decompose_heap_triple no_guard_remove(1) no_guard_remove(2) no_guards_remove remove_guards_def snd_conv)
        qed
        moreover have "h' = FractionalHeap.normalize (get_fh H')"
        proof (rule ext)
          fix l show "h' l = FractionalHeap.normalize (get_fh H') l"
          proof (cases "l = v")
            case True
            then have "get_fh (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) l = Some (pwrite, edenot E sa)"
              by auto
            then have "get_fh hf l = None"
              using True \<open>v \<notin> dom (get_fh hf)\<close> by force
            then show "h' l = FractionalHeap.normalize (get_fh H') l"
              apply (cases "h' l")
              using True asm1(3) apply auto[1]
              by (metis (no_types, lifting) FractionalHeap.normalize_def True \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hf\<close> \<open>get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) l = Some (pwrite, edenot E sa)\<close> apply_opt.simps(2) asm1(3) fun_upd_same snd_conv sum_second_none_get_fh)
          next
            case False
            then have "get_fh (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) l = None"
              by simp
            then have "get_fh H' l = get_fh hf l"
              using \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hf\<close> sum_first_none_get_fh by blast
            moreover have "get_fh H l = get_fh hf l"
              by (metis asm0 fst_conv get_fh.elims plus_comm sum_second_none_get_fh)
            ultimately show ?thesis
            proof (cases "get_fh hf l")
              case None
              then show ?thesis
                by (metis False FractionalHeap.normalize_eq(1) \<open>get_fh H l = get_fh hf l\<close> \<open>get_fh H' l = get_fh hf l\<close> asm1(1) asm1(3) fun_upd_apply old.prod.inject)
            next
              case (Some f)
              then show ?thesis
                by (metis (no_types, lifting) False FractionalHeap.normalize_eq(1) FractionalHeap.normalize_eq(2) \<open>get_fh H l = get_fh hf l\<close> \<open>get_fh H' l = get_fh hf l\<close> asm1(1) asm1(3) domD not_in_dom fun_upd_apply old.prod.inject)
            qed
          qed
        qed
        ultimately show ?thesis
          by auto
      qed
      ultimately show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        by blast
    qed
  qed
qed (simp)

lemma safe_new_Some:
  assumes "x \<notin> fvA (invariant \<Gamma>)"
      and "view_function_of_inv \<Gamma>"
  shows "safe n (Some \<Gamma>) (Calloc x E) (s, (Map.empty, gs, gu)) { (s(x := a), (Map.empty(a \<mapsto> (pwrite, edenot E s)), gs, gu)) |a. True }"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeSomeI)
    show "Calloc x E = Cskip \<Longrightarrow> (s, Map.empty, gs, gu) \<in> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}" by simp
    show "no_abort (Some \<Gamma>) (Calloc x E) s (Map.empty, gs, gu)"
      using aborts_alloc_cases no_abort.simps(2) by blast
    fix H hf C' s' h' hj v0
    assume asm0: "Some H = Some (Map.empty, gs, gu) \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Calloc x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"


    then obtain hjf where "Some hjf = Some hj \<oplus> Some hf"
      by (metis plus.simps(2) plus.simps(3) plus_asso)
    then have "Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf"
      by (metis asm0 plus_asso)

    show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s' hj' \<Gamma> \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
    proof (rule red_alloc_cases)
      show "red (Calloc x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h v
      assume asm1: "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip" "(s', h') = (sa(x := v), h(v \<mapsto> edenot E sa))"
  "v \<notin> dom h"
      then have "v \<notin> dom (get_fh H)"
        by (simp add: dom_normalize)
      then have "v \<notin> dom (get_fh hjf)"
        by (metis (no_types, lifting) \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> addition_smaller_domain in_mono plus_comm)

      moreover have "(Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) ## hjf"
      proof (rule compatibleI)
        show "compatible_fract_heaps (get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu)) (get_fh hjf)"
        proof (rule compatible_fract_heapsI)
          fix l p p'
          assume asm2: "get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) l = Some p \<and> get_fh hjf l = Some p'"
          then show "pgte pwrite (padd (fst p) (fst p'))"
            by (metis calculation domIff fst_conv fun_upd_other get_fh.elims option.distinct(1))
          show "snd p = snd p'"
            using asm2 calculation domIff fst_conv fun_upd_other get_fh.elims option.distinct(1) by metis
        qed
        show "\<And>k. get_gu ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) k = None \<or> get_gu hjf k = None"
          by (metis \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> compatible_def compatible_eq get_gu.simps option.discI snd_conv)
        show "\<And>p p'. get_gs ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) = Some p \<and> get_gs hjf = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
          by (metis \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> compatible_def compatible_eq get_gs.simps option.simps(3) snd_eqD)
      qed
      then obtain H' where "Some H' = Some (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) \<oplus> Some hjf"
        by auto
      moreover have "(s', (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu)) \<in> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        using asm1(1) asm1(3) by blast
      then have "safe n (Some \<Gamma>) C' (s', (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu)) {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        by (simp add: asm1(2) safe_skip)

      moreover have "full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> h' = FractionalHeap.normalize (get_fh H')"
      proof -
        have "full_ownership (get_fh H')"
        proof (rule full_ownershipI)
          fix l p
          assume "get_fh H' l = Some p"
          show "fst p = pwrite"
          proof (cases "l = v")
            case True
            then have "get_fh hjf l = None"
              using calculation(1) by blast
            then have "get_fh H' l = (Map.empty(v \<mapsto> (pwrite, edenot E sa))) l"
              by (metis calculation(2) fst_conv get_fh.simps sum_second_none_get_fh)
            then show ?thesis
              using True \<open>get_fh H' l = Some p\<close> by fastforce
          next
            case False
            then have "get_fh H' l = get_fh hjf l" using sum_first_none_get_fh[of H' _ hjf l]
              using calculation(2) by force
            then show ?thesis
              by (metis (no_types, lifting) \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> \<open>get_fh H' l = Some p\<close> asm0 fst_conv full_ownership_def get_fh.elims plus_comm sum_second_none_get_fh)
          qed
        qed
        moreover have "h' = FractionalHeap.normalize (get_fh H')"
        proof (rule ext)
          fix l show "h' l = FractionalHeap.normalize (get_fh H') l"
          proof (cases "l = v")
            case True
            then have "get_fh (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) l = Some (pwrite, edenot E sa)"
              by auto
            then have "get_fh hjf l = None"
              using True \<open>v \<notin> dom (get_fh hjf)\<close> by force
            then show ?thesis
              apply (cases "h' l")
              using True asm1(3) apply auto[1]
              by (metis (no_types, lifting) FractionalHeap.normalize_def True \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hjf\<close> \<open>get_fh ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) l = Some (pwrite, edenot E sa)\<close> apply_opt.simps(2) asm1(3) fun_upd_same snd_conv sum_second_none_get_fh)
          next
            case False
            then have "get_fh (Map.empty(v \<mapsto> (pwrite, edenot E sa)), gs, gu) l = None"
              by simp
            then have "get_fh H' l = get_fh hjf l"
              using \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hjf\<close> sum_first_none_get_fh by blast
            moreover have "get_fh H l = get_fh hjf l"
              by (metis \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> fst_eqD get_fh.simps sum_first_none_get_fh)
            ultimately show ?thesis
            proof (cases "get_fh hjf l")
              case None
              then show ?thesis
                by (metis False FractionalHeap.normalize_eq(1) \<open>get_fh H l = get_fh hjf l\<close> \<open>get_fh H' l = get_fh hjf l\<close> asm1(1) asm1(3) fun_upd_apply old.prod.inject)
            next
              case (Some f)
              then show ?thesis
                by (metis (no_types, lifting) False FractionalHeap.normalize_eq(1) FractionalHeap.normalize_eq(2) \<open>get_fh H l = get_fh hjf l\<close> \<open>get_fh H' l = get_fh hjf l\<close> asm1(1) asm1(3) domD not_in_dom fun_upd_apply old.prod.inject)
            qed
          qed
        qed
        moreover have "semi_consistent \<Gamma> v0 H'"
        proof (rule semi_consistentI)
          have "get_gs H' = get_gs H"
            by (metis \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hjf\<close> fst_conv get_gs.simps option.discI option.sel plus.simps(3) snd_conv)
          moreover have "get_gu H' = get_gu H"
            by (metis \<open>Some H = Some (Map.empty, gs, gu) \<oplus> Some hjf\<close> \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hjf\<close> get_gu.simps option.discI option.sel plus.simps(3) snd_conv)
          ultimately show "all_guards H'"
            by (metis all_guards_def asm0 semi_consistent_def)
          show "reachable \<Gamma> v0 H'"
          proof (rule reachableI)
            fix sargs uargs
            assume "get_gs H' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu H' k = Some (uargs k))"
            then have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh H)))"
              by (metis \<open>get_gs H' = get_gs H\<close> \<open>get_gu H' = get_gu H\<close> asm0 reachableE semi_consistent_def)
            moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh H)) = view \<Gamma> (FractionalHeap.normalize (get_fh H'))"
            proof -
              have "view \<Gamma> (FractionalHeap.normalize (get_fh H)) = view \<Gamma> (FractionalHeap.normalize (get_fh hj))"
                using view_function_of_invE[of \<Gamma> s hj H] by (simp add: asm0 assms(2) larger3)
              moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh H')) = view \<Gamma> (FractionalHeap.normalize (get_fh hj))"
                using view_function_of_invE[of \<Gamma> s hj H']
                by (metis \<open>Some H' = Some ([v \<mapsto> (pwrite, edenot E sa)], gs, gu) \<oplus> Some hjf\<close> \<open>Some hjf = Some hj \<oplus> Some hf\<close> asm0 assms(2) larger3 plus_comm)
              ultimately show ?thesis by simp
            qed
            ultimately show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh H')))"
              by simp
          qed
        qed
        ultimately show ?thesis
          by auto
      qed
      
      moreover have "sat_inv s' hj \<Gamma>"
      proof (rule sat_invI)
        show "no_guard hj"
          using asm0 sat_inv_def by blast
        have "agrees (fvA (invariant \<Gamma>)) s s'"
          using asm1(1) asm1(3) assms
          by (simp add: agrees_update)
        then show "(s', hj), (s', hj) \<Turnstile> invariant \<Gamma>"
          using asm0 sat_inv_agrees sat_inv_def by blast
      qed

      ultimately show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], gs, gu) |a. True}"
        by (metis (no_types, lifting) \<open>Some hjf = Some hj \<oplus> Some hf\<close> plus_asso)
    qed
  qed
qed (simp)


lemma safe_new:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma>"
  shows "safe n \<Delta> (Calloc x E) (s, (Map.empty, gs, gu)) { (s(x := a), (Map.empty(a \<mapsto> (pwrite, edenot E s)), gs, gu)) |a. True }"
  apply (cases \<Delta>)
  using safe_new_None safe_new_Some assms by blast+


theorem new_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "x \<notin> fvE E"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma>"
  shows "hoare_triple_valid \<Delta> Emp (Calloc x E) (PointsTo (Evar x) pwrite E)"
proof (rule hoare_triple_validI)
  define \<Sigma> :: "store \<times> ('i, 'a) heap \<Rightarrow> (store \<times> ('i, 'a) heap) set" where "\<Sigma> = (\<lambda>(s, h). { (s(x := a), (Map.empty(a \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)) |a. True })"

  show "\<And>s h n. (s, h), (s, h) \<Turnstile> Emp \<Longrightarrow> safe n \<Delta> (Calloc x E) (s, h) (\<Sigma> (s, h))"
  proof -
    fix s h n assume "(s, h :: ('i, 'a) heap), (s, h) \<Turnstile> Emp" then have "get_fh h = Map.empty"
      by simp
    then have "h = (Map.empty, get_gs h, get_gu h)" using decompose_heap_triple
      by metis
    moreover have "safe n \<Delta> (Calloc x E) (s, Map.empty, get_gs h, get_gu h) {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], get_gs h, get_gu h) |a. True}"
      using safe_new assms(2) by blast
    moreover have "\<Sigma> (s, h) = { (s(x := a), (Map.empty(a \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)) |a. True }"
      using \<Sigma>_def by force
    ultimately show "safe n \<Delta> (Calloc x E) (s, h) (\<Sigma> (s, h))"
      by presburger
  qed
  fix s1 h1 s2 h2
  assume "(s1, h1 :: ('i, 'a) heap), (s2, h2) \<Turnstile> Emp"
  show "pair_sat (case (s1, h1) of (s, h) \<Rightarrow> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], get_gs h, get_gu h) |a. True})
        (case (s2, h2) of (s, h) \<Rightarrow> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], get_gs h, get_gu h) |a. True}) (PointsTo (Evar x) pwrite E)"
  proof (rule pair_satI)
    fix s1' h1' s2' h2'
    assume asm0: "(s1', h1') \<in> (case (s1, h1) of (s, h) \<Rightarrow> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], get_gs h, get_gu h) |a. True}) \<and>
       (s2', h2') \<in> (case (s2, h2) of (s, h) \<Rightarrow> {(s(x := a), [a \<mapsto> (pwrite, edenot E s)], get_gs h, get_gu h) |a. True})"
    then obtain a1 a2 where "s1' = s1(x := a1)" "s2' = s2(x := a2)" "h1' = ([a1 \<mapsto> (pwrite, edenot E s1)], get_gs h1, get_gu h1)"
      "h2' = ([a2 \<mapsto> (pwrite, edenot E s2)], get_gs h2, get_gu h2)"
      by blast
    then show "(s1', h1'), (s2', h2') \<Turnstile> PointsTo (Evar x) pwrite E"
      by (simp add: assms(1))
  qed
qed



subsubsection \<open>Write\<close>


inductive_cases red_write_cases: "red (Cwrite x E) \<sigma> C' \<sigma>'"
inductive_cases aborts_write_cases: "aborts (Cwrite x E) \<sigma>"

lemma safe_write_None:
  assumes "fh (edenot loc s) = Some (pwrite, v)"
  shows "safe n (None :: ('i, 'a, nat) cont) (Cwrite loc E) (s, (fh, gs, gu)) { (s, (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)) }"
  using assms
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeNoneI)
    show "Cwrite loc E = Cskip \<Longrightarrow> (s, fh, gs, gu) \<in> {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
      by simp
    show "no_abort None (Cwrite loc E) s (fh, gs, gu)"
    proof (rule no_abortNoneI)
      fix hf H assume asm0: "Some H = Some (fh, gs, gu) \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H"
      then have "edenot loc s \<in> dom (normalize (get_fh H))"
        by (metis (mono_tags, lifting) Suc.prems addition_smaller_domain dom_def dom_normalize fst_conv get_fh.simps mem_Collect_eq option.discI subsetD)
      then show "\<not> aborts (Cwrite loc E) (s, normalize (get_fh H))"
        by (metis aborts_write_cases fst_eqD snd_eqD)
    qed


    fix H hf C' s' h'
    assume asm0: "Some H = Some (fh, gs, gu) \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H
  \<and> red (Cwrite loc E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    then have "get_fh hf (edenot loc s) = None"
    proof -
      have "compatible_fract_heaps fh (get_fh hf)"
        by (metis asm0 compatible_def compatible_eq fst_conv get_fh.elims option.discI)
      then show ?thesis using compatible_then_dom_disjoint(2)[of fh "get_fh hf"]
          assms disjoint_iff_not_equal[of "dom (get_fh hf)" "fpdom fh"] not_in_dom fpdom_def mem_Collect_eq
        by fastforce
    qed

    show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H')
  \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n None C' (s', h'') {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
    proof (rule red_write_cases)
      show "red (Cwrite loc E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h
      assume asm1: "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip"
       "(s', h') = (sa, h(edenot loc sa \<mapsto> edenot E sa))"
      then obtain "s = sa" "h' = h(edenot loc s \<mapsto> edenot E s)" by blast

      let ?h = "(fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)"
      have "?h ## hf"
      proof (rule compatibleI)
        show "compatible_fract_heaps (get_fh (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)) (get_fh hf)"
        proof (rule compatible_fract_heapsI)
          fix l p p' assume asm2: "get_fh (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) l = Some p \<and> get_fh hf l = Some p'"
          then show "pgte pwrite (padd (fst p) (fst p'))"
            apply (cases "l = edenot loc s")
             apply (metis Suc.prems asm0 fst_conv fun_upd_same get_fh.elims option.sel plus_extract_point_fh)
            by (metis asm0 fst_conv fun_upd_other get_fh.elims plus_extract_point_fh)
          show "snd p = snd p'"
            apply (cases "l = edenot loc s")
            using \<open>pgte pwrite (padd (fst p) (fst p'))\<close> asm2 not_pgte_charact sum_larger apply fastforce
            by (metis (mono_tags, opaque_lifting) asm0 asm2 fst_eqD get_fh.simps map_upd_Some_unfold plus_extract_point_fh)
        qed
        show "\<And>k. get_gu (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) k = None \<or> get_gu hf k = None"
          by (metis asm0 compatible_def compatible_eq get_gu.simps option.discI snd_conv)
        show "\<And>p p'. get_gs (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) = Some p \<and> get_gs hf = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
          by (metis asm0 no_guard_def no_guard_then_smaller_same option.simps(3) plus_comm)
      qed
      then obtain H' where "Some H' = Some ?h \<oplus> Some hf" by auto
      moreover have "H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
      proof (rule heap_ext)
        show "get_fh H' = get_fh ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
          using calculation asm0 by (metis \<open>get_fh hf (edenot loc s) = None\<close> add_fh_update add_get_fh fst_conv get_fh.simps)
        show "get_gs H' = get_gs ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)" 
          using calculation asm0
          by (metis fst_conv get_gs.simps plus_extract(2) snd_conv)
        show "get_gu H' = get_gu ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
          using add_fh_update[of "get_fh hf" "edenot E s" fh "(pwrite, edenot E s)"] asm0 calculation 
          by (metis get_gu.elims plus_extract(3) snd_conv)
      qed
      moreover have "safe n (None :: ('i, 'a, nat) cont) C' (s', ?h) {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
        using \<open>s = sa\<close> asm1(2) asm1(3) safe_skip by fastforce
      moreover have "full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H')"
      proof -
        have "full_ownership (get_fh H')"
        proof (rule full_ownershipI)
          fix l p
          assume asm: "get_fh H' l = Some p"
          then show "fst p = pwrite"
          proof (cases "l = edenot loc s")
            case True
            then show ?thesis
              using asm calculation(2) by fastforce
          next
            case False
            then show ?thesis
              by (metis (mono_tags, lifting) asm asm0 calculation(2) fst_eqD full_ownership_def get_fh.simps map_upd_Some_unfold)
          qed
        qed
        moreover have "no_guard H'" using asm0 
          by (simp add: \<open>H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)\<close> no_guard_def)
        moreover have "h' = FractionalHeap.normalize (get_fh H')"
        proof (rule ext)
          fix l show "h' l = FractionalHeap.normalize (get_fh H') l"
          proof(cases "l = edenot loc s")
            case True
            then show ?thesis
              by (metis (no_types, lifting) FractionalHeap.normalize_eq(2) \<open>H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)\<close> \<open>h' = h(edenot loc s \<mapsto> edenot E s)\<close> fst_conv fun_upd_same get_fh.elims)
          next
            case False
            then have "FractionalHeap.normalize (get_fh H') l = FractionalHeap.normalize (get_fh H) l"
              using FractionalHeap.normalize_eq(2)[of "get_fh H'" l]
                FractionalHeap.normalize_eq(2)[of "get_fh H" l] \<open>H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)\<close>
                fst_conv fun_upd_other[of l "edenot loc s" "get_fh H"] get_fh.simps option.exhaust
              by metis
            then show ?thesis
              using False \<open>h' = h(edenot loc s \<mapsto> edenot E s)\<close> asm1(1) by force
          qed
        qed
        ultimately show ?thesis
          by auto
      qed
      ultimately show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hf \<and> safe n None C' (s', h'') {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
        by (metis \<open>Some H' = Some (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) \<oplus> Some hf\<close> \<open>s = sa\<close> asm1(2) asm1(3) fst_conv insertI1 safe_skip)
    qed
  qed
qed (simp)



lemma safe_write_Some:
  assumes "fh (edenot loc s) = Some (pwrite, v)"
      and "view_function_of_inv \<Gamma>"
  shows "safe n (Some \<Gamma>) (Cwrite loc E) (s, (fh, gs, gu)) { (s, (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)) }"
  using assms
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeSomeI)
    show "Cwrite loc E = Cskip \<Longrightarrow> (s, fh, gs, gu) \<in> {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
      by simp
    show "no_abort (Some \<Gamma>) (Cwrite loc E) s (fh, gs, gu)"
    proof (rule no_abortSomeI)
      fix H hf hj v0
      assume asm0: "Some H = Some (fh, gs, gu) \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>"
      then have "edenot loc s \<in> dom (get_fh H)"
        by (metis Un_iff assms(1) domI dom_three_sum fst_conv get_fh.simps)
      then have "edenot loc s \<in> dom (normalize (get_fh H))"
        by (simp add: dom_normalize)
      then show "\<not> aborts (Cwrite loc E) (s, FractionalHeap.normalize (get_fh H))"
        by (metis aborts_write_cases fst_eqD snd_eqD)
    qed

    fix H hf C' s' h' hj v0

    assume asm0: "Some H = Some (fh, gs, gu) \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cwrite loc E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    then obtain hjf where hjf_def: "Some hjf = Some hj \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) option.exhaust_sel plus.simps(1) plus_asso plus_comm)
    then have asm00: "Some H = Some (fh, gs, gu) \<oplus> Some hjf"
      by (metis asm0 plus_asso)
    then have "get_fh hjf (edenot loc s) = None"
    proof -
      have "compatible_fract_heaps fh (get_fh hjf)"
        by (metis asm00 compatible_def compatible_eq fst_conv get_fh.elims option.discI)
      then show ?thesis using compatible_then_dom_disjoint(2)[of fh "get_fh hjf"]
          assms disjoint_iff_not_equal[of "dom (get_fh hjf)" "fpdom fh"] not_in_dom fpdom_def mem_Collect_eq
        by fastforce
    qed

    show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
    proof (rule red_write_cases)
      show "red (Cwrite loc E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h
      assume asm1: "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip"
       "(s', h') = (sa, h(edenot loc sa \<mapsto> edenot E sa))"
      then obtain "s = sa" "h' = h(edenot loc s \<mapsto> edenot E s)" by blast

      let ?h = "(fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)"
      have "?h ## hjf"
      proof (rule compatibleI)
        show "compatible_fract_heaps (get_fh (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)) (get_fh hjf)"
        proof (rule compatible_fract_heapsI)
          fix l p p' assume asm2: "get_fh (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) l = Some p \<and> get_fh hjf l = Some p'"
          then show "pgte pwrite (padd (fst p) (fst p'))"
            apply (cases "l = edenot loc s")
             apply (metis Suc.prems(1) asm00 fst_conv fun_upd_same get_fh.elims option.sel plus_extract_point_fh)
            by (metis asm00 fst_conv fun_upd_other get_fh.elims plus_extract_point_fh)
          show "snd p = snd p'"
            apply (cases "l = edenot loc s")
            using \<open>pgte pwrite (padd (fst p) (fst p'))\<close> asm2 not_pgte_charact sum_larger apply fastforce
            by (metis (mono_tags, opaque_lifting) asm00 asm2 fst_eqD get_fh.simps map_upd_Some_unfold plus_extract_point_fh)
        qed
        show "\<And>k. get_gu (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) k = None \<or> get_gu hjf k = None"
          by (metis asm00 compatible_def compatible_eq get_gu.simps option.discI snd_conv)
        show "\<And>p p'. get_gs (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu) = Some p \<and> get_gs hjf = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
          by (metis asm00 compatible_def compatible_eq get_gs.simps option.discI snd_conv)
      qed
      then obtain H' where "Some H' = Some ?h \<oplus> Some hjf" by auto
      moreover have "H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
      proof (rule heap_ext)
        show "get_fh H' = get_fh ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
          using asm00 calculation
          by (metis \<open>get_fh hjf (edenot loc s) = None\<close> add_fh_update add_get_fh fst_conv get_fh.simps)
        show "get_gs H' = get_gs ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)" 
          using asm00 calculation 
          by (metis fst_conv get_gs.simps plus_extract(2) snd_conv)
        show "get_gu H' = get_gu ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)"
          by (metis asm00 calculation get_gu.simps plus_extract(3) snd_conv)
      qed
      moreover have "safe n (Some \<Gamma>) C' (s', ?h) {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
        using \<open>s = sa\<close> asm1(2) asm1(3) safe_skip by fastforce
      moreover have "full_ownership (get_fh H') \<and> h' = FractionalHeap.normalize (get_fh H')"
      proof -
        have "full_ownership (get_fh H')"
        proof (rule full_ownershipI)
          fix l p
          assume asm: "get_fh H' l = Some p"
          then show "fst p = pwrite"
          proof (cases "l = edenot loc s")
            case True
            then show ?thesis
              using asm calculation(2) by fastforce
          next
            case False
            then show ?thesis
              by (metis (mono_tags, lifting) asm asm0 calculation(2) fst_eqD full_ownership_def get_fh.simps map_upd_Some_unfold)
          qed
        qed
        moreover have "h' = FractionalHeap.normalize (get_fh H')"
        proof (rule ext)
          fix l show "h' l = FractionalHeap.normalize (get_fh H') l"
          proof(cases "l = edenot loc s")
            case True
            then show ?thesis
              by (metis (no_types, lifting) FractionalHeap.normalize_eq(2) \<open>H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)\<close> \<open>h' = h(edenot loc s \<mapsto> edenot E s)\<close> fst_conv fun_upd_same get_fh.elims)
          next
            case False
            then have "FractionalHeap.normalize (get_fh H') l = FractionalHeap.normalize (get_fh H) l"
              using FractionalHeap.normalize_eq(2)[of "get_fh H'" l]
                FractionalHeap.normalize_eq(2)[of "get_fh H" l] \<open>H' = ((get_fh H)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs H, get_gu H)\<close>
                fst_conv fun_upd_other[of l "edenot loc s" "get_fh H"] get_fh.simps option.exhaust
              by metis
            then show ?thesis
              using False \<open>h' = h(edenot loc s \<mapsto> edenot E s)\<close> asm1(1) by force
          qed
        qed
        ultimately show ?thesis
          by auto
      qed
      moreover have "Some H' = Some ?h \<oplus> Some hj \<oplus> Some hf"
        by (metis calculation(1) hjf_def simpler_asso)
      moreover have "semi_consistent \<Gamma> v0 H'"
      proof (rule semi_consistentI)
        show "all_guards H'"
          by (metis all_guards_def asm0 calculation(2) fst_conv get_gs.simps get_gu.simps semi_consistent_def snd_conv)
        have "view \<Gamma> (normalize (get_fh H')) = view \<Gamma> (normalize (get_fh H))"
        proof -
          have "view \<Gamma> (normalize (get_fh H')) = view \<Gamma> (normalize (get_fh hj))"
            by (metis asm0 assms(2) calculation(5) larger3 view_function_of_invE)
          then show ?thesis using assms(2) larger3 view_function_of_invE
            by (metis asm0)
        qed
        then show "reachable \<Gamma> v0 H'"
          by (metis asm0 calculation(2) fst_eqD get_gs.simps get_gu.simps reachableE reachableI semi_consistent_def snd_eqD)
      qed
      ultimately show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s' hj' \<Gamma> \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s, fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)}"
        using \<open>s = sa\<close> asm0 asm1(2) asm1(3) by blast
    qed
  qed
qed (simp)


lemma safe_write:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "fh (edenot loc s) = Some (pwrite, v)"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> view_function_of_inv \<Gamma>"
  shows "safe n \<Delta> (Cwrite loc E) (s, (fh, gs, gu)) { (s, (fh(edenot loc s \<mapsto> (pwrite, edenot E s)), gs, gu)) }"
  apply (cases \<Delta>)
  using safe_write_None safe_write_Some assms by blast+

theorem write_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> view_function_of_inv \<Gamma>"
      and "v \<notin> fvE loc"
  shows "hoare_triple_valid \<Delta> (Exists v (PointsTo loc pwrite (Evar v))) (Cwrite loc E) (PointsTo loc pwrite E)"
proof (rule hoare_triple_validI)

  define \<Sigma> :: "store \<times> ('i, 'a) heap \<Rightarrow> (store \<times> ('i, 'a) heap) set" where
    "\<Sigma> = (\<lambda>(s, h). { (s, ((get_fh h)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)) })"

  show "\<And>s h n. (s, h), (s, h) \<Turnstile> Exists v (PointsTo loc pwrite (Evar v)) \<Longrightarrow> safe n \<Delta> (Cwrite loc E) (s, h) (\<Sigma> (s, h))"
  proof -
    fix s h n assume "(s, h :: ('i, 'a) heap), (s, h) \<Turnstile> Exists v (PointsTo loc pwrite (Evar v))"
    then obtain vv where "(s(v := vv), h), (s(v := vv), h) \<Turnstile> PointsTo loc pwrite (Evar v)"      
      by (meson hyper_sat.simps(6) hyper_sat.simps(7))
    then have "get_fh h (edenot loc (s(v := vv))) = Some (pwrite, vv)"
      by simp
    then have "get_fh h (edenot loc s) = Some (pwrite, vv)"
      using assms(2) by auto
    then show "safe n \<Delta> (Cwrite loc E) (s, h) (\<Sigma> (s, h))"
      by (metis (mono_tags, lifting) \<Sigma>_def assms(1) decompose_heap_triple old.prod.case safe_write)
  qed
  fix s1 h1 s2 h2
  assume "(s1, h1 :: ('i, 'a) heap), (s2, h2) \<Turnstile> Exists v (PointsTo loc pwrite (Evar v))"
  then obtain v1 v2 where "get_fh h1 (edenot loc s1) = Some (pwrite, v1)" "get_fh h2 (edenot loc s2) = Some (pwrite, v2)"
    using assms(2) by auto


  show "pair_sat (case (s1, h1) of (s, h) \<Rightarrow> {(s, (get_fh h)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)})
        (case (s2, h2) of (s, h) \<Rightarrow> {(s, (get_fh h)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)}) (PointsTo loc pwrite E)"
  proof (rule pair_satI)
    fix s1' h1' s2' h2'
    assume asm0: "(s1', h1') \<in> (case (s1, h1) of (s, h) \<Rightarrow> {(s, (get_fh h)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)}) \<and>
       (s2', h2') \<in> (case (s2, h2) of (s, h) \<Rightarrow> {(s, (get_fh h)(edenot loc s \<mapsto> (pwrite, edenot E s)), get_gs h, get_gu h)})"
    then show "(s1', h1'), (s2', h2') \<Turnstile> PointsTo loc pwrite E"
      using \<open>(s1, h1), (s2, h2) \<Turnstile> Exists v (PointsTo loc pwrite (Evar v))\<close> assms(2) by auto
  qed
qed


subsubsection \<open>Read\<close>


inductive_cases red_read_cases: "red (Cread x E) \<sigma> C' \<sigma>'"
inductive_cases aborts_read_cases: "aborts (Cread x E) \<sigma>"

lemma safe_read_None:
  "safe n (None :: ('i, 'a, nat) cont) (Cread x E) (s, ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) { (s(x := v), ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) }"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeNoneI)

    show "no_abort (None :: ('i, 'a, nat) cont) (Cread x E) s ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)"
    proof (rule no_abortNoneI)
      fix hf H
      assume asm0: "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H"
      then have "edenot E s \<in> dom (get_fh H)"
        by (metis Un_iff dom_eq_singleton_conv dom_sum_two fst_eqD get_fh.elims insert_iff)
      then have "edenot E s \<in> dom (FractionalHeap.normalize (get_fh H))"
        by (simp add: dom_normalize)
      then show "\<not> aborts (Cread x E) (s, FractionalHeap.normalize (get_fh H))"
        by (metis aborts_read_cases fst_eqD snd_eqD)
    qed
    fix H hf C' s' h'
    assume asm0: "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> no_guard H \<and> red (Cread x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    
    let ?S = "{ (s(x := v), ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) }"


    show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') ?S"
    proof (rule red_read_cases)

      show "red (Cread x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h va
      assume "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip" "(s', h') = (sa(x := va), h)"
      "h (edenot E sa) = Some va"
      then have "s = sa"
        by force
      then have "va = v"
      proof -
        have "\<exists>\<pi>'. get_fh H (edenot E s) = Some (\<pi>', v)"
        proof (rule one_value_sum_same)
          show "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hf"
            using asm0 by fastforce
        qed (simp)
        then show ?thesis
          by (metis FractionalHeap.normalize_eq(2) Pair_inject \<open>(s, FractionalHeap.normalize (get_fh H)) = (sa, h)\<close> \<open>h (edenot E sa) = Some va\<close> option.sel)
      qed

      then have "safe n (None :: ('i, 'a, nat) cont) C' (s', ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) ?S"
        using \<open>(s', h') = (sa(x := va), h)\<close> \<open>C' = Cskip\<close> \<open>s = sa\<close> safe_skip by fastforce

      then show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and> no_guard H' \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') {(s(x := v), [edenot E s \<mapsto> (\<pi>, v)], gs, gu)}"
        using \<open>(s', h') = (sa(x := va), h)\<close> \<open>(s, FractionalHeap.normalize (get_fh H)) = (sa, h)\<close> asm0 by blast
    qed
  qed (simp)
qed (simp)

lemma safe_read_Some:
  assumes "view_function_of_inv \<Gamma>"
      and "x \<notin> fvA (invariant \<Gamma>)"
  shows "safe n (Some \<Gamma>) (Cread x E) (s, ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) { (s(x := v), ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) }"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeSomeI)

    show "no_abort (Some \<Gamma>) (Cread x E) s ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)"
    proof (rule no_abortSomeI)
      fix hf H hj v0
      assume asm0: "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>"
      then obtain hjf where "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hjf"
        by (metis (no_types, lifting) plus.simps(2) plus.simps(3) plus_asso)
      then have "edenot E s \<in> dom (get_fh H)"
        by (metis Un_iff dom_eq_singleton_conv dom_sum_two fst_eqD get_fh.elims insert_iff)
      then have "edenot E s \<in> dom (FractionalHeap.normalize (get_fh H))"
        by (simp add: dom_normalize)
      then show "\<not> aborts (Cread x E) (s, FractionalHeap.normalize (get_fh H))"
        by (metis aborts_read_cases fst_eqD snd_eqD)
    qed
    fix H hf C' s' h' hj v0
    assume asm0: "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cread x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    then obtain hjf where "Some hjf = Some hj \<oplus> Some hf"
      using compatible_last_two by (metis plus.simps(3) plus_asso)
    then have "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hjf"
      by (metis asm0 plus_asso)

    let ?S = "{ (s(x := v), ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) }"

    show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s(x := v), [edenot E s \<mapsto> (\<pi>, v)], gs, gu)}"
    proof (rule red_read_cases)

      show "red (Cread x E) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      fix sa h va
      assume "(s, FractionalHeap.normalize (get_fh H)) = (sa, h)" "C' = Cskip" "(s', h') = (sa(x := va), h)"
      "h (edenot E sa) = Some va"
      then have "s = sa"
        by force
      then have "va = v"
      proof -
        have "\<exists>\<pi>'. get_fh H (edenot E s) = Some (\<pi>', v)"
        proof (rule one_value_sum_same)
          show "Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hjf"
            by (simp add: \<open>Some H = Some ([edenot E s \<mapsto> (\<pi>, v)], gs, gu) \<oplus> Some hjf\<close>)
        qed (simp)
        then show ?thesis
          by (metis FractionalHeap.normalize_eq(2) Pair_inject \<open>(s, FractionalHeap.normalize (get_fh H)) = (sa, h)\<close> \<open>h (edenot E sa) = Some va\<close> option.sel)
      qed

      then have "safe n (Some \<Gamma>) C' (s', ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) ?S"
        using \<open>(s', h') = (sa(x := va), h)\<close> \<open>C' = Cskip\<close> \<open>s = sa\<close> safe_skip by fastforce
      moreover have "sat_inv s' hj \<Gamma>"
        by (metis \<open>(s', h') = (sa(x := va), h)\<close> \<open>s = sa\<close> agrees_update asm0 assms(2) prod.inject sat_inv_agrees)
      ultimately show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and>
          Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') {(s(x := v), [edenot E s \<mapsto> (\<pi>, v)], gs, gu)}"
        using \<open>(s', h') = (sa(x := va), h)\<close> \<open>(s, FractionalHeap.normalize (get_fh H)) = (sa, h)\<close> asm0 by blast
    qed
  qed (simp)
qed (simp)

lemma safe_read:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma>"
  shows "safe n \<Delta> (Cread x E) (s, ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) { (s(x := v), ([edenot E s \<mapsto> (\<pi>, v)], gs, gu)) }"
  apply (cases \<Delta>)
  using safe_read_None safe_read_Some assms by blast+

theorem read_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>) \<and> view_function_of_inv \<Gamma>"
      and "x \<notin> fvE E \<union> fvE e"
  shows "hoare_triple_valid \<Delta> (PointsTo E \<pi> e) (Cread x E) (And (PointsTo E \<pi> e) (Bool (Beq (Evar x) e)))"
proof (rule hoare_triple_validI)

  define \<Sigma> :: "store \<times> ('i, 'a) heap \<Rightarrow> (store \<times> ('i, 'a) heap) set" where
    "\<Sigma> = (\<lambda>(s, h). { (s(x := edenot e s), ([edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)) })"

  show "\<And>s h n. (s, h), (s, h) \<Turnstile> PointsTo E \<pi> e \<Longrightarrow> safe n \<Delta> (Cread x E) (s, h) (\<Sigma> (s, h))"
  proof -
    fix s h n
    assume "(s, h :: ('i, 'a) heap), (s, h) \<Turnstile> PointsTo E \<pi> e"
    then have "get_fh h = [edenot E s \<mapsto> (\<pi>, edenot e s)]"
      using sat_points_to by blast
    then have "h = ([edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)"
      by (metis decompose_heap_triple)
    then have "safe n \<Delta> (Cread x E) (s, ([edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h))
      { (s(x := edenot e s), ([edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)) }"
      using assms safe_read by blast
    then show "safe n \<Delta> (Cread x E) (s, h) (\<Sigma> (s, h))"
      using \<Sigma>_def \<open>h = ([edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)\<close> by auto
  qed

  fix s1 h1 s2 h2
  assume "(s1, h1 :: ('i, 'a) heap), (s2, h2) \<Turnstile> PointsTo E \<pi> e"

  show "pair_sat (case (s1, h1) of (s, h) \<Rightarrow> {(s(x := edenot e s), [edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)})
        (case (s2, h2) of (s, h) \<Rightarrow> {(s(x := edenot e s), [edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)}) (And (PointsTo E \<pi> e) (Bool (Beq (Evar x) e)))"
 proof (rule pair_satI)
    fix s1' h1' s2' h2'
    assume asm0: "(s1', h1') \<in> (case (s1, h1) of (s, h) \<Rightarrow> {(s(x := edenot e s), [edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)}) \<and>
       (s2', h2') \<in> (case (s2, h2) of (s, h) \<Rightarrow> {(s(x := edenot e s), [edenot E s \<mapsto> (\<pi>, edenot e s)], get_gs h, get_gu h)})"
    then obtain "s1' = s1(x := edenot e s1)" "h1' = ([edenot E s1 \<mapsto> (\<pi>, edenot e s1)], get_gs h1, get_gu h1)"
      "s2' = s2(x := edenot e s2)" "h2' = ([edenot E s2 \<mapsto> (\<pi>, edenot e s2)], get_gs h2, get_gu h2)"
      by force
    then show "(s1', h1'), (s2', h2') \<Turnstile> And (PointsTo E \<pi> e) (Bool (Beq (Evar x) e))"
      using assms(2) by auto
  qed
qed




subsubsection \<open>Share\<close>


lemma share_no_abort:
  assumes "no_abort (Some \<Gamma>) C s (h :: ('i, 'a) heap)"
      and "Some (h' :: ('i, 'a) heap) = Some h \<oplus> Some hj"
      and "sat_inv s hj \<Gamma>"
      and "get_gs h = Some (pwrite, sargs)"
      and "\<And>k. get_gu h k = Some (uargs k)"
      and "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (normalize (get_fh hj)))"
      and "view_function_of_inv \<Gamma>"
    shows "no_abort None C s (remove_guards h')"
proof (rule no_abortI)
  show "\<And>H hf hj v0 \<Gamma>.
       None = Some \<Gamma> \<and>
       Some H = Some (remove_guards h') \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<Longrightarrow>
       \<not> aborts C (s, FractionalHeap.normalize (get_fh H))" by blast

  fix hf H :: "('i, 'a) heap"
  assume asm0: "Some H = Some (remove_guards h') \<oplus> Some hf \<and> None = None \<and> full_ownership (get_fh H) \<and> no_guard H"

  have "compatible h' hf"
  proof (rule compatibleI)
    show "compatible_fract_heaps (get_fh h') (get_fh hf)"
      by (metis asm0 compatible_def compatible_eq fst_eqD get_fh.simps option.distinct(1) remove_guards_def)
    show "\<And>k. get_gu h' k = None \<or> get_gu hf k = None"
      by (metis asm0 no_guard_def no_guard_then_smaller_same plus_comm)
    fix p p' assume "get_gs h' = Some p \<and> get_gs hf = Some p'"
    then show "pgte pwrite (padd (fst p) (fst p'))"
      by (metis asm0 no_guard_def no_guard_then_smaller_same option.distinct(1) plus_comm)
  qed
  then obtain H' where "Some H' = Some h' \<oplus> Some hf"
    by simp
  then have "get_fh H' = get_fh H"
    by (metis asm0 fst_eqD get_fh.elims option.discI remove_guards_def option.sel plus.simps(3))

  have "\<not> aborts C (s, FractionalHeap.normalize (get_fh H'))"
  proof (rule no_abortE(2))
    show "no_abort (Some \<Gamma>) C s h"
      using assms by blast
    show "Some \<Gamma> = Some \<Gamma>" by blast
    show "full_ownership (get_fh H')"
      using \<open>get_fh H' = get_fh H\<close> asm0 by presburger
    show "semi_consistent \<Gamma> v0 H'"
    proof (rule semi_consistentI)
      show "all_guards H'"
        by (metis \<open>Some H' = Some h' \<oplus> Some hf\<close> all_guards_def all_guards_same assms(2) assms(4) assms(5) option.discI)

      have "view \<Gamma> (normalize (get_fh hj)) = view \<Gamma> (normalize (get_fh H'))"
        using assms(7)
      proof (rule view_function_of_invE)
        show "H' \<succeq> hj"
          using larger_trans
          by (simp add: \<open>Some H' = Some h' \<oplus> Some hf\<close> assms(2) larger3)
        show "sat_inv s hj \<Gamma>"
          by (simp add: assms(3))
      qed

      show "reachable \<Gamma> v0 H'"
      proof (rule reachableI)
        fix sargs' uargs'
        assume asm1: "get_gs H' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H' k = Some (uargs' k))"
        then have "sargs = sargs'"
          by (metis \<open>Some H' = Some h' \<oplus> Some hf\<close> assms(2) assms(4) full_sguard_sum_same option.inject snd_conv)
        moreover have "uargs = uargs'"
        proof (rule ext)

          fix k
          show "uargs k = uargs' k"
            using full_uguard_sum_same[of h' k _ H' hf]
            by (metis \<open>Some H' = Some h' \<oplus> Some hf\<close> asm1 assms(2) assms(5) full_uguard_sum_same option.inject)
        qed
        ultimately show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs' uargs' (view \<Gamma> (FractionalHeap.normalize (get_fh H')))"
          using \<open>view \<Gamma> (FractionalHeap.normalize (get_fh hj)) = view \<Gamma> (FractionalHeap.normalize (get_fh H'))\<close> assms(6) by presburger
      qed
    qed
    show "Some H' = Some h \<oplus> Some hj \<oplus> Some hf"
      using \<open>Some H' = Some h' \<oplus> Some hf\<close> assms(2) by presburger
    show "sat_inv s hj \<Gamma>"
      by (simp add: assms(3))
  qed

  then show "\<not> aborts C (s, FractionalHeap.normalize (get_fh H))"
    using \<open>get_fh H' = get_fh H\<close> by auto
qed

definition S_after_share where
  "S_after_share S \<Gamma> v0 = { (s, remove_guards h') |h hj h' s. semi_consistent \<Gamma> v0 h' \<and> Some h' = Some h \<oplus> Some hj \<and> (s, h) \<in> S \<and> sat_inv s hj \<Gamma> }"

lemma share_lemma:
  assumes "safe n (Some \<Gamma>) C (s, h :: ('i, 'a) heap) S"
      and "Some (h' :: ('i, 'a) heap) = Some h \<oplus> Some hj"
      and "sat_inv s hj \<Gamma>"
      and "semi_consistent \<Gamma> v0 h'"
      and "view_function_of_inv \<Gamma>"
    shows "safe n (None :: ('i, 'a, nat) cont) C (s, remove_guards h') (S_after_share S \<Gamma> v0)"
  using assms
proof (induct n arbitrary: C s h h' hj)
  case (Suc n)

  let ?S' = "S_after_share S \<Gamma> v0"

  have is_in_s': "\<And>h hj h'. Some h' = Some h \<oplus> Some hj \<and> (s, h) \<in> S \<and> sat_inv s hj \<Gamma> \<and> semi_consistent \<Gamma> v0 h' \<Longrightarrow> (s, remove_guards h') \<in> ?S'"
  proof -
    fix h hj h' assume "Some h' = Some h \<oplus> Some hj \<and> (s, h) \<in> S \<and> sat_inv s hj \<Gamma> \<and> semi_consistent \<Gamma> v0 h'"
    then show "(s, remove_guards h') \<in> ?S'"
      using S_after_share_def[of S \<Gamma> v0] mem_Collect_eq by blast
  qed
  show ?case
  proof (rule safeNoneI)


    show "C = Cskip \<Longrightarrow> (s, remove_guards h') \<in> ?S'"
    proof -
      assume "C = Cskip"
      show "(s, remove_guards h') \<in> ?S'"
      proof (rule is_in_s')
        show "Some h' = Some h \<oplus> Some hj \<and> (s, h) \<in> S \<and> sat_inv s hj \<Gamma> \<and> semi_consistent \<Gamma> v0 h'"
          using Suc.prems \<open>C = Cskip\<close> safeSomeE(1) sat_inv_def by blast
      qed
    qed

    obtain sargs uargs where " get_gs h' = Some (pwrite, sargs) \<and>
   (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))"
      by (meson Suc.prems(4) semi_consistentE)
    show "no_abort None C s (remove_guards h')"
    proof (rule share_no_abort)
      show "no_abort (Some \<Gamma>) C s h"
        using Suc.prems(1) safeSomeE(2) by blast
      show "Some h' = Some h \<oplus> Some hj"
        using Suc.prems(2) by blast
      show "sat_inv s hj \<Gamma>"
        using Suc.prems(3) by auto
      show "get_gs h = Some (pwrite, sargs)"
        by (metis Suc.prems(2) \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> \<open>sat_inv s hj \<Gamma>\<close> no_guard_remove(1) sat_inv_def)
      show "\<And>k. get_gu h k = Some (uargs k)"
        by (metis Suc.prems(2) \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> \<open>sat_inv s hj \<Gamma>\<close> no_guard_remove(2) sat_inv_def)
      show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh hj)))"     
        by (metis Suc.prems(2) Suc.prems(3) \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> assms(5) larger_def plus_comm view_function_of_invE)
      show "view_function_of_inv \<Gamma>"
        by (simp add: assms(5))
    qed

    fix H hf C' s' h'a
    assume asm0: "Some H = Some (remove_guards h') \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h'a)"


    have "compatible h' hf"
    proof (rule compatibleI)
      show "compatible_fract_heaps (get_fh h') (get_fh hf)"
        by (metis asm0 compatible_def compatible_eq fst_eqD get_fh.simps option.distinct(1) remove_guards_def)
      show "\<And>k. get_gu h' k = None \<or> get_gu hf k = None"
        by (metis asm0 no_guard_def no_guard_then_smaller_same plus_comm)
      fix p p' assume "get_gs h' = Some p \<and> get_gs hf = Some p'"
      then show "pgte pwrite (padd (fst p) (fst p'))"
        by (metis asm0 no_guard_def no_guard_then_smaller_same option.distinct(1) plus_comm)
    qed
    then obtain Hg where "Some Hg = Some h' \<oplus> Some hf"
      by simp
    then have "get_fh Hg = get_fh H"
      by (metis asm0 fst_eqD get_fh.elims option.discI remove_guards_def option.sel plus.simps(3))
  
    have "\<exists>h'' H' hj'.
       full_ownership (get_fh H') \<and>
       semi_consistent \<Gamma> v0 H' \<and>
       sat_inv s' hj' \<Gamma> \<and> h'a = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S"
      using Suc(2)
    proof (rule safeSomeE(3)[of n \<Gamma> C s h S Hg hj hf v0 C' s' h'a])
      show "Some Hg = Some h \<oplus> Some hj \<oplus> Some hf"
        by (simp add: Suc.prems(2) \<open>Some Hg = Some h' \<oplus> Some hf\<close>)
      show "full_ownership (get_fh Hg)"
        using \<open>get_fh Hg = get_fh H\<close> asm0 by presburger
      show "sat_inv s hj \<Gamma>"
        by (simp add: Suc.prems(3))
      show "red C (s, FractionalHeap.normalize (get_fh Hg)) C' (s', h'a)"
        using \<open>get_fh Hg = get_fh H\<close> asm0 by presburger
      show "semi_consistent \<Gamma> v0 Hg"
      proof (rule semi_consistentI)
        show "all_guards Hg"
          by (meson Suc.prems(4) \<open>Some Hg = Some h' \<oplus> Some hf\<close> all_guards_same semi_consistent_def)
        have "view \<Gamma> (normalize (get_fh hj)) = view \<Gamma> (normalize (get_fh Hg))"
          using assms(5)
        proof (rule view_function_of_invE)
          show "Hg \<succeq> hj"
            using larger_trans
            using \<open>Some Hg = Some h \<oplus> Some hj \<oplus> Some hf\<close> larger3 by blast
          show "sat_inv s hj \<Gamma>"
            by (simp add: \<open>sat_inv s hj \<Gamma>\<close>)
        qed
        show "reachable \<Gamma> v0 Hg"
        proof (rule reachableI)
          fix sargs' uargs'
          assume asm1: "get_gs Hg = Some (pwrite, sargs') \<and> (\<forall>k. get_gu Hg k = Some (uargs' k))"
          then have "sargs = sargs'"
            by (metis Pair_inject \<open>Some Hg = Some h' \<oplus> Some hf\<close> \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> full_sguard_sum_same option.inject)
          moreover have "uargs = uargs'"
          proof (rule ext)
            fix k
            show "uargs k = uargs' k"
              by (metis \<open>Some Hg = Some h' \<oplus> Some hf\<close> \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> asm1 full_uguard_sum_same option.inject)
          qed
          ultimately show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs' uargs' (view \<Gamma> (FractionalHeap.normalize (get_fh Hg)))"
            by (metis Suc.prems(2) \<open>get_gs h' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu h' k = Some (uargs k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs (view \<Gamma> (FractionalHeap.normalize (get_fh h')))\<close> \<open>sat_inv s hj \<Gamma>\<close> \<open>view \<Gamma> (FractionalHeap.normalize (get_fh hj)) = view \<Gamma> (FractionalHeap.normalize (get_fh Hg))\<close> assms(5) larger_def plus_comm view_function_of_invE)
        qed
      qed
    qed
    then obtain h'' H' hj' where asm1: "full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and>
       sat_inv s' hj' \<Gamma> \<and> h'a = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S"
      by blast
    obtain hj'' where "Some hj'' = Some h'' \<oplus> Some hj'"
      by (metis asm1 not_Some_eq plus.simps(1))
    moreover obtain sargs' uargs' where new_guards_def:
      "get_gs H' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H' k = Some (uargs' k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs' uargs' (view \<Gamma> (FractionalHeap.normalize (get_fh H')))"
      by (meson asm1 semi_consistentE)


    have "safe n (None :: ('i, 'a, nat) cont) C' (s', remove_guards hj'') ?S'"
    proof (rule Suc(1)[of C' s' h'' hj'' hj'])

      show "safe n (Some \<Gamma>) C' (s', h'') S"
        using asm1 by blast
      show "Some hj'' = Some h'' \<oplus> Some hj'"
        using \<open>Some hj'' = Some h'' \<oplus> Some hj'\<close> by blast
      show "sat_inv s' hj' \<Gamma>"
        using asm1 by fastforce

      have "no_guard hf"
        by (metis asm0 no_guard_then_smaller_same plus_comm)
      moreover have "no_guard hj'"
        using \<open>sat_inv s' hj' \<Gamma>\<close> sat_inv_def by blast

      have "view \<Gamma> (normalize (get_fh hj')) = view \<Gamma> (normalize (get_fh H'))"
        using assms(5)
      proof (rule view_function_of_invE)
        show "H' \<succeq> hj'"
          using larger_trans
          using asm1 larger3 by blast
        show "sat_inv s' hj' \<Gamma>"
          by (simp add: asm1)
      qed

      obtain uargs' sargs' where args': "get_gs H' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H' k = Some (uargs' k)) \<and> reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs' uargs'
                                                                 (view \<Gamma> (FractionalHeap.normalize (get_fh H')))"
        using semi_consistentE[of \<Gamma> v0 H'] asm1
        by blast
      then have "get_gs hj'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu hj'' k = Some (uargs' k))"
        by (metis \<open>Some hj'' = Some h'' \<oplus> Some hj'\<close> asm1 calculation no_guard_remove(1) no_guard_remove(2))

      show "semi_consistent \<Gamma> v0 hj''"
      proof (rule semi_consistentI)

        show "all_guards hj''"
          by (metis \<open>get_gs hj'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu hj'' k = Some (uargs' k))\<close> all_guards_def option.discI)
        have "view \<Gamma> (FractionalHeap.normalize (get_fh H')) = view \<Gamma> (FractionalHeap.normalize (get_fh hj''))"
          by (metis \<open>Some hj'' = Some h'' \<oplus> Some hj'\<close> \<open>view \<Gamma> (FractionalHeap.normalize (get_fh hj')) = view \<Gamma> (FractionalHeap.normalize (get_fh H'))\<close> asm1 assms(5) larger_def plus_comm view_function_of_invE)
        then show "reachable \<Gamma> v0 hj''"
          by (metis \<open>get_gs hj'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu hj'' k = Some (uargs' k))\<close> args' asm1 ext get_fh.simps new_guards_def option.sel reachable_def snd_conv)
      qed
      show "view_function_of_inv \<Gamma>"
        by (simp add: assms(5))
    qed

    let ?h'' = "remove_guards hj''"
    have "hj'' ## hf"
      by (metis asm1 calculation option.simps(3) plus.simps(3))
    then obtain H'' where "Some H'' = Some ?h'' \<oplus> Some hf"
      by (simp add: remove_guards_smaller smaller_more_compatible)

    then have "get_fh H'' = get_fh H'"
      by (metis asm1 calculation equiv_sum_get_fh get_fh_remove_guards)
    moreover have "no_guard H''"
      by (metis \<open>Some H'' = Some (remove_guards hj'') \<oplus> Some hf\<close> asm0 no_guard_remove_guards no_guard_then_smaller_same plus_comm sum_of_no_guards)

    ultimately show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and> h'a = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') ?S'"
      by (metis \<open>Some H'' = Some (remove_guards hj'') \<oplus> Some hf\<close> \<open>safe n None C' (s', remove_guards hj'') ?S'\<close> asm1)
  qed
qed (simp)

definition no_need_guards where
  "no_need_guards A \<longleftrightarrow> (\<forall>s1 h1 s2 h2. (s1, h1), (s2, h2) \<Turnstile> A \<longrightarrow> (s1, remove_guards h1), (s2, remove_guards h2) \<Turnstile> A)"

lemma has_guard_then_safe_none:
  assumes "\<not> no_guard h"
      and "C = Cskip \<Longrightarrow> (s, h) \<in> S"
  shows "safe n (None :: ('i, 'a, nat) cont) C (s, h) S"
proof (induct n)
  case (Suc n)
  show ?case
  proof (rule safeNoneI)
    show "C = Cskip \<Longrightarrow> (s, h) \<in> S"
      by (simp add: assms(2))
    show "no_abort None C s h"
      using assms(1) no_abortNoneI no_guard_then_smaller_same by blast
    show "\<And>H hf C' s' h'.
       Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red C (s, FractionalHeap.normalize (get_fh H)) C' (s', h') \<Longrightarrow>
       \<exists>h'' H'.
          full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n None C' (s', h'') S"
      using assms(1) no_guard_then_smaller_same by blast
  qed
qed (simp)




theorem share_rule:
  fixes \<Gamma> :: "('i, 'a, nat) single_context"
  assumes "\<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr>"
      and "all_axioms \<alpha> sact spre uact upre"
      and "hoare_triple_valid (Some \<Gamma>) (Star P EmptyFullGuards) C (Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre))))"
      and "view_function_of_inv \<Gamma>"
      and "unary J \<and> precise J"
      and "wf_indexed_precondition upre \<and> wf_precondition spre"
      and "x \<notin> fvA J"
      and "no_guard_assertion (Star P (LowView (\<alpha> \<circ> f) J x))"
    shows "hoare_triple_valid (None :: ('i, 'a, nat) cont) (Star P (LowView (\<alpha> \<circ> f) J x)) C (Star Q (LowView (\<alpha> \<circ> f) J x))"
proof -
  let ?P = "Star P EmptyFullGuards"
  let ?Q = "Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre)))"

  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> Star P EmptyFullGuards \<Longrightarrow> safe n (Some \<Gamma>) C \<sigma> (\<Sigma> \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> Star P EmptyFullGuards \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre))))"
    using hoare_triple_validE[of "Some \<Gamma>" ?P C ?Q] assms(3) by blast

  text \<open>Steps:
  1) Remove the hj and add empty-guards
  2) Apply sigma
  3) Remove the guards and add hj, using S-after-share\<close>

  define input_\<Sigma> where "input_\<Sigma> = (\<lambda>\<sigma>. { (fst \<sigma>, add_empty_guards hp) |hp hj. Some (snd \<sigma>) = Some hp \<oplus> Some hj \<and>
    (fst \<sigma>, hp), (fst \<sigma>, hp) \<Turnstile> P \<and>  sat_inv (fst \<sigma>) hj \<Gamma>})"

  define \<Sigma>' where "\<Sigma>' = (\<lambda>\<sigma>. \<Union>p \<in> input_\<Sigma> \<sigma>. S_after_share (\<Sigma> p) \<Gamma> (f (normalize (get_fh (snd \<sigma>)))))"

  show ?thesis 
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> Star P (LowView (\<alpha> \<circ> f) J x) \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C (s, h) (\<Sigma>' (s, h))"
    proof -
      fix s h n assume asm1: "(s, h), (s, h) \<Turnstile> Star P (LowView (\<alpha> \<circ> f) J x)"
      then obtain hp hj where "no_guard h" "Some h = Some hp \<oplus> Some hj" "(s, hp), (s, hp) \<Turnstile> P"
        "(s, hj), (s, hj) \<Turnstile> LowView (\<alpha> \<circ> f) J x"
        by (meson always_sat_refl assms(8) hyper_sat.simps(4) no_guard_assertion_def)
      then have "sat_inv s hj \<Gamma>"
        by (metis LowViewE assms(1) assms(7) no_guard_then_smaller_same plus_comm sat_inv_def select_convs(5))
      then have "(s, add_empty_guards hp) \<in> input_\<Sigma> (s, h)"
        using \<open>(s, hp), (s, hp) \<Turnstile> P\<close> \<open>Some h = Some hp \<oplus> Some hj\<close> input_\<Sigma>_def by force

      let ?v0 = "f (normalize (get_fh h))"
      let ?p = "(s, add_empty_guards hp)"

      have "safe n (None :: ('i, 'a, nat) cont) C (s, remove_guards (add_empty_guards h)) (S_after_share (\<Sigma> ?p) \<Gamma> ?v0)"
      proof (rule share_lemma)
        show "safe n (Some \<Gamma>) C ?p (\<Sigma> ?p)"
        proof (rule asm0(1))
          show "(s, add_empty_guards hp), (s, add_empty_guards hp) \<Turnstile> Star P EmptyFullGuards"
            using \<open>(s, hp), (s, hp) \<Turnstile> P\<close> \<open>Some h = Some hp \<oplus> Some hj\<close> \<open>no_guard h\<close> no_guard_and_sat_p_empty_guards no_guard_then_smaller_same by blast
        qed
        show "Some (add_empty_guards h) = Some (add_empty_guards hp) \<oplus> Some hj"
          using \<open>Some h = Some hp \<oplus> Some hj\<close> \<open>no_guard h\<close> no_guard_add_empty_guards_sum by blast
        show "sat_inv s hj \<Gamma>"
          using \<open>sat_inv s hj \<Gamma>\<close> by auto
        show "view_function_of_inv \<Gamma>"
          by (simp add: assms(4))
        show "semi_consistent \<Gamma> (f (FractionalHeap.normalize (get_fh h))) (add_empty_guards h)"
          by (metis \<open>no_guard h\<close> assms(1) select_convs(1) semi_consistent_empty_no_guard_initial_value)
      qed
      moreover have "(S_after_share (\<Sigma> ?p) \<Gamma> ?v0) \<subseteq> \<Sigma>' (s, h)"
        using \<Sigma>'_def \<open>(s, add_empty_guards hp) \<in> input_\<Sigma> (s, h)\<close> by auto
      ultimately show "safe n (None :: ('i, 'a, nat) cont) C (s, h) (\<Sigma>' (s, h))"
        by (metis \<open>no_guard h\<close> no_guards_remove_same safe_larger_set)
    qed



    fix s1 h1 s2 h2
    assume "(s1, h1), (s2, h2) \<Turnstile> Star P (LowView (\<alpha> \<circ> f) J x)"
    then obtain hp1 hj1 hp2 hj2 where asm1: "Some h1 = Some hp1 \<oplus> Some hj1"
      "Some h2 = Some hp2 \<oplus> Some hj2" "(s1, hp1), (s2, hp2) \<Turnstile> P" "no_guard h1" "no_guard h2"
      "(s1, hj1), (s2, hj2) \<Turnstile> LowView (\<alpha> \<circ> f) J x"
      using assms(8) hyper_sat.simps(4) no_guard_assertion_def by blast
    then obtain "(s1, hj1), (s2, hj2) \<Turnstile> J" "\<alpha> (f (normalize (get_fh hj1))) = \<alpha> (f (normalize (get_fh hj2)))"
      by (metis LowViewE assms(7) comp_apply)

    show "pair_sat (\<Sigma>' (s1, h1)) (\<Sigma>' (s2, h2)) (Star Q (LowView (\<alpha> \<circ> f) J x))"
    proof (rule pair_satI)
      fix s1' h1' s2' h2'
      assume asm2: "(s1', h1') \<in> \<Sigma>' (s1, h1) \<and> (s2', h2') \<in> \<Sigma>' (s2, h2)"
      then obtain p1 p2 where p_assms: "p1 \<in> input_\<Sigma> (s1, h1)" "p2 \<in> input_\<Sigma> (s2, h2)"
        "(s1', h1') \<in> S_after_share (\<Sigma> p1) \<Gamma> (f (normalize (get_fh h1)))"
        "(s2', h2') \<in> S_after_share (\<Sigma> p2) \<Gamma> (f (normalize (get_fh h2)))"
        using \<Sigma>'_def by force
      moreover have "pair_sat (\<Sigma> p1) (\<Sigma> p2) (Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre))))"
      proof (rule asm0(2))
        obtain hj1' hj2' hp1' hp2' where "snd p1 = add_empty_guards hp1'" "snd p2 = add_empty_guards hp2'"
           "Some h1 = Some hp1' \<oplus> Some hj1'" "Some h2 = Some hp2' \<oplus> Some hj2'" "sat_inv s1 hj1' \<Gamma>" "sat_inv s2 hj2' \<Gamma>"
            "fst p1 = s1" "fst p2 = s2"
          using p_assms(1) p_assms(2) input_\<Sigma>_def by auto
        moreover have "hj1 = hj1' \<and> hj2 = hj2'"
        proof (rule preciseE)
          show "precise J"
            by (simp add: assms(5))
          show "h1 \<succeq> hj1' \<and> h1 \<succeq> hj1 \<and> h2 \<succeq> hj2' \<and> h2 \<succeq> hj2"
            by (metis asm1(1) asm1(2) calculation(3) calculation(4) larger_def plus_comm)
          show "(s1, hj1'), (s2, hj2') \<Turnstile> J \<and> (s1, hj1), (s2, hj2) \<Turnstile> J"
            by (metis \<open>(s1, hj1), (s2, hj2) \<Turnstile> J\<close> assms(1) assms(5) calculation(5) calculation(6) sat_inv_def select_convs(5) unaryE)
        qed
        then have "hp1 = hp1' \<and> hp2 = hp2'"
          using addition_cancellative asm1(1) asm1(2) calculation(3) calculation(4) by blast
        then show "p1, p2 \<Turnstile> Star P EmptyFullGuards"
          using no_guard_and_sat_p_empty_guards[of "fst p1" "snd p1" "fst p2" "snd p2" P]
          by (metis asm1(3) asm1(4) asm1(5) calculation(1) calculation(2) calculation(3) calculation(4) calculation(7) calculation(8) no_guard_and_sat_p_empty_guards no_guard_then_smaller_same prod.exhaust_sel)
      qed


      let ?v1 = "f (normalize (get_fh h1))"
      let ?v2 = "f (normalize (get_fh h2))"

      obtain hj1' hg1 H1 hj2' hg2 H2  where asm3: "h1' = remove_guards H1" "semi_consistent \<Gamma> ?v1 H1"
        "Some H1 = Some hg1 \<oplus> Some hj1'" "(s1', hg1) \<in> \<Sigma> p1" "sat_inv s1' hj1' \<Gamma>"
        "h2' = remove_guards H2" "semi_consistent \<Gamma> ?v2 H2"
        "Some H2 = Some hg2 \<oplus> Some hj2'" "(s2', hg2) \<in> \<Sigma> p2" "sat_inv s2' hj2' \<Gamma>"
        using p_assms(3) S_after_share_def[of "\<Sigma> p1" \<Gamma> ?v1] p_assms(4) S_after_share_def[of "\<Sigma> p2" \<Gamma> ?v2] by blast

      then have "(s1', hg1), (s2', hg2) \<Turnstile> Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre)))"
        using \<open>pair_sat (\<Sigma> p1) (\<Sigma> p2) (Star Q (And (PreSharedGuards (Abs_precondition spre)) (PreUniqueGuards (Abs_indexed_precondition upre))))\<close> pair_satE by blast
      then obtain q1 g1 q2 g2 where "Some hg1 = Some q1 \<oplus> Some g1" "Some hg2 = Some q2 \<oplus> Some g2"
      "(s1', q1), (s2', q2) \<Turnstile> Q" "(s1', g1), (s2', g2) \<Turnstile> PreSharedGuards (Abs_precondition spre)" "(s1', g1), (s2', g2) \<Turnstile> PreUniqueGuards (Abs_indexed_precondition upre)"
        by (meson hyper_sat.simps(3) hyper_sat.simps(4))
      moreover have "Rep_precondition (Abs_precondition spre) = spre \<and> Rep_indexed_precondition (Abs_indexed_precondition upre) = upre"
        by (simp add: assms(6) wf_indexed_precondition_rep_prec wf_precondition_rep_prec)
      ultimately obtain sargs1 sargs2 where
        "get_gs g1 = Some (pwrite, sargs1)" "get_gs g2 = Some (pwrite, sargs2)" "PRE_shared_simpler spre sargs1 sargs2"
        "get_fh g1 = Map.empty" "get_fh g2 = Map.empty"
        by auto
      moreover obtain uargs1 uargs2 where
        unique_facts: "\<And>k. get_gu g1 k = Some (uargs1 k) \<and> get_gu g2 k = Some (uargs2 k) \<and> PRE_unique (upre k) (uargs1 k) (uargs2 k)"
        using sat_PreUniqueE[OF \<open>(s1', g1), (s2', g2) \<Turnstile> PreUniqueGuards (Abs_indexed_precondition upre)\<close>]
        by (metis \<open>Rep_precondition (Abs_precondition spre) = spre \<and> Rep_indexed_precondition (Abs_indexed_precondition upre) = upre\<close>)
      moreover obtain "get_gs H1 = Some (pwrite, sargs1)" "\<And>k. get_gu H1 k = Some (uargs1 k)"
        by (metis (no_types, opaque_lifting) \<open>Some hg1 = Some q1 \<oplus> Some g1\<close> asm3(3) calculation(1) calculation(6) full_sguard_sum_same full_uguard_sum_same plus_comm)
      then have reach1: "reachable_value sact uact ?v1 sargs1 uargs1 (f (normalize (get_fh H1)))"
        by (metis asm3(2) assms(1) reachableE select_convs(1) select_convs(3) select_convs(4) semi_consistent_def)
      moreover obtain "get_gs H2 = Some (pwrite, sargs2)" "\<And>k. get_gu H2 k = Some (uargs2 k)"
        by (metis (no_types, lifting) \<open>Some hg2 = Some q2 \<oplus> Some g2\<close> asm3(8) calculation(2) calculation(6) full_sguard_sum_same full_uguard_sum_same plus_comm)
      then have reach2: "reachable_value sact uact ?v2 sargs2 uargs2 (f (normalize (get_fh H2)))"
        by (metis asm3(7) assms(1) reachableE semi_consistent_def simps(1) simps(3) simps(4))
      moreover have "\<alpha> (f (normalize (get_fh h1))) = \<alpha> (f (normalize (get_fh hj1)))"
        using view_function_of_invE[of \<Gamma> s1 hj1 h1]
        by (metis \<open>(s1, hj1), (s2, hj2) \<Turnstile> J\<close> always_sat_refl asm1(1) asm1(4) assms(1) assms(4) larger_def no_guard_then_smaller_same plus_comm sat_inv_def select_convs(1) select_convs(5))
      moreover have "\<alpha> (f (normalize (get_fh h2))) = \<alpha> (f (normalize (get_fh hj2)))"
        using view_function_of_invE[of \<Gamma> s2 hj2 h2]
        by (metis \<open>(s1, hj1), (s2, hj2) \<Turnstile> J\<close> always_sat_refl asm1(2) asm1(5) assms(1) assms(4) larger_def no_guard_then_smaller_same plus_comm sat_comm sat_inv_def select_convs(1) select_convs(5))
      ultimately have low_abstract_view: "\<alpha> (f (FractionalHeap.normalize (get_fh H1))) = \<alpha> (f (FractionalHeap.normalize (get_fh H2)))"
        using reach1 reach2 main_result[of sact uact ?v1 sargs1 uargs1 "f (normalize (get_fh H1))" ?v2 sargs2 uargs2 "f (normalize (get_fh H2))" spre upre \<alpha>]
        using \<open>\<alpha> (f (FractionalHeap.normalize (get_fh hj1))) = \<alpha> (f (FractionalHeap.normalize (get_fh hj2)))\<close> assms(2) by presburger
      moreover have "\<alpha> (f (normalize (get_fh H1))) = \<alpha> (f (normalize (get_fh hj1')))"
        using view_function_of_invE[of \<Gamma> s1' hj1' H1]
        by (metis asm3(3) asm3(5) assms(1) assms(4) larger_def plus_comm select_convs(1))
      moreover have "\<alpha> (f (normalize (get_fh H2))) = \<alpha> (f (normalize (get_fh hj2')))"
        using view_function_of_invE[of \<Gamma> s2' hj2' H2]
        by (metis asm3(10) asm3(8) assms(1) assms(4) larger_def plus_comm select_convs(1))
      moreover have "(s1', hj1'), (s2', hj2') \<Turnstile> J"
        by (metis asm3(10) asm3(5) assms(1) assms(5) sat_inv_def select_convs(5) unaryE)
      ultimately have "(s1', hj1'), (s2', hj2') \<Turnstile> LowView (\<alpha> \<circ> f) J x"
        by (simp add: LowViewI assms(7))
      moreover have "Some h1' = Some q1 \<oplus> Some hj1'"
      proof -
        have "Some h1' = Some (remove_guards hg1) \<oplus> Some (remove_guards hj1')"
          using asm3(1) asm3(3) remove_guards_sum by blast
        moreover have "remove_guards hg1 = remove_guards q1"
          by (metis \<open>Some hg1 = Some q1 \<oplus> Some g1\<close> \<open>get_fh g1 = Map.empty\<close> get_fh_remove_guards no_guard_and_no_heap no_guard_remove_guards no_guards_remove remove_guards_sum)
        moreover have "remove_guards hj1' = hj1'"
          by (metis asm3(5) no_guards_remove sat_inv_def)
        ultimately show ?thesis
          by (metis \<open>Some hg1 = Some q1 \<oplus> Some g1\<close> \<open>get_gs g1 = Some (pwrite, sargs1)\<close> unique_facts all_guards_def full_guard_comp_then_no no_guards_remove option.distinct(1) plus.simps(3) plus_comm)
      qed
      moreover have "Some h2' = Some q2 \<oplus> Some hj2'"
      proof -
        have "Some h2' = Some (remove_guards hg2) \<oplus> Some (remove_guards hj2')"
          using asm3(6) asm3(8) remove_guards_sum by blast
        moreover have "remove_guards hg2 = remove_guards q2"
          by (metis \<open>Some hg2 = Some q2 \<oplus> Some g2\<close> \<open>get_fh g2 = Map.empty\<close> get_fh_remove_guards no_guard_and_no_heap no_guard_remove_guards no_guards_remove remove_guards_sum)
        moreover have "remove_guards hj2' = hj2'"
          by (metis asm3(10) no_guards_remove sat_inv_def)
        ultimately show ?thesis
          by (metis \<open>Some hg2 = Some q2 \<oplus> Some g2\<close> \<open>get_gs g2 = Some (pwrite, sargs2)\<close> unique_facts all_guards_def full_guard_comp_then_no no_guards_remove option.distinct(1) plus.simps(3) plus_comm)
      qed
      ultimately show "(s1', h1'), (s2', h2') \<Turnstile> Star Q (LowView (\<alpha> \<circ> f) J x)"
        by (meson LowViewI \<open>(s1', q1), (s2', q2) \<Turnstile> Q\<close> assms(7) hyper_sat.simps(9) hyper_sat.simps(4))
    qed
  qed
qed

subsubsection \<open>Atomic\<close>


lemma red_rtrans_induct:
  assumes "red_rtrans C \<sigma> C' \<sigma>'"
    and "\<And>C \<sigma>. P C \<sigma> C \<sigma>"
    and "\<And>C \<sigma> C' \<sigma>' C'' \<sigma>''. red C \<sigma> C' \<sigma>' \<Longrightarrow> red_rtrans C' \<sigma>' C'' \<sigma>'' \<Longrightarrow> P C' \<sigma>' C'' \<sigma>'' \<Longrightarrow> P C \<sigma> C'' \<sigma>''"
  shows "P C \<sigma> C' \<sigma>'"
  using red_red_rtrans.inducts[of _ _ _ _ "\<lambda>_ _ _ _. True" P] assms by auto

lemma safe_atomic:
  assumes "red_rtrans C1 \<sigma>1 C2 \<sigma>2"
      and "\<sigma>1 = (s1, H1)"
      and "\<sigma>2 = (s2, H2)"
      and "\<And>n. safe n (None :: ('i, 'a, nat) cont) C1 (s1, h) S"
      and "H = denormalize H1"
      and "Some H = Some h \<oplus> Some hf"
      and "full_ownership (get_fh H) \<and> no_guard H"
    shows "\<not> aborts C2 \<sigma>2 \<and> (C2 = Cskip \<longrightarrow>
    (\<exists>h1 H'. Some H' = Some h1 \<oplus> Some hf \<and> H2 = normalize (get_fh (H')) \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> S))"
  using assms
proof (induction arbitrary: s1 H1 H h rule: red_rtrans_induct[of C1 \<sigma>1 C2 \<sigma>2])
  case 1
  then show ?case by (simp add: assms(1))
next
  case (2 C \<sigma>)
  then have "\<not> aborts C (s1, FractionalHeap.normalize (get_fh H))"
    using no_abortE(1) safe.simps(2) by blast
  then have "\<not> aborts C \<sigma>"
    by (metis "2.prems"(2) "2.prems"(5) denormalize_properties(3))
  moreover have "safe (Suc 1) (None :: ('i, 'a, nat) cont) C (s1, h) S"
    using "2.prems"(4) by blast
  then have "C = Cskip \<Longrightarrow> (s2, h) \<in> S"
    by (metis "2.prems"(2) "2.prems"(3) Pair_inject safeNoneE(1))
  then have "C = Cskip \<Longrightarrow> Some H = Some h \<oplus> Some hf \<and> H2 = FractionalHeap.normalize (get_fh H) \<and> no_guard H \<and> full_ownership (get_fh H) \<and> (s2, h) \<in> S"
    by (metis "2.prems"(3) "2.prems"(2) "2.prems"(6) "2.prems"(5) "2.prems"(7) denormalize_properties(3) old.prod.inject)
  ultimately show ?case 
    by blast
next
  case (3 C \<sigma> C' \<sigma>' C'' \<sigma>'')
    obtain s0 H0 where "\<sigma>' = (s0, H0)" using prod.exhaust_sel by blast

  have "safe (Suc 0) (None :: ('i, 'a, nat) cont) C (s1, h) S"
    using "3.prems"(4) by force
  then have "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> H0 = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe 0 (None :: ('i, 'a, nat) cont) C' (s0, h'') S"
  proof (rule safeNoneE(3)[of 0 C s1 h S H hf C' s0 H0])
    show "Some H = Some h \<oplus> Some hf" using "3.prems"(6) by blast
    show "full_ownership (get_fh H)" using "3.prems"(7) by blast
    show "no_guard H" using "3.prems"(7) by auto
    show "red C (s1, FractionalHeap.normalize (get_fh H)) C' (s0, H0)"
      by (metis "3.hyps"(1) "3.prems"(2) "3.prems"(5) \<open>\<sigma>' = (s0, H0)\<close> denormalize_properties(3))
  qed
  then obtain h0 H0' where
    r1: "full_ownership (get_fh H0') \<and> no_guard H0' \<and> H0 = FractionalHeap.normalize (get_fh H0') \<and> Some H0' = Some h0 \<oplus> Some hf \<and> safe 0 (None :: ('i, 'a, nat) cont) C' (s0, h0) S"
    by blast
  then have "Some (denormalize H0) = Some h0 \<oplus> Some hf"
    by (metis denormalize_properties(4))
  have ih:
    "\<not> aborts C'' \<sigma>'' \<and> (C'' = Cskip \<longrightarrow>
(\<exists>h1 H'. Some H' = Some h1 \<oplus> Some hf \<and> H2 = FractionalHeap.normalize (get_fh H') \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> S))"
  proof (rule 3(3)[of s0 H0 h0 H0'])
    show "\<sigma>' = (s0, H0)" by (simp add: \<open>\<sigma>' = (s0, H0)\<close>)
    show "\<sigma>'' = (s2, H2)"
      by (simp add: "3.prems"(3))
    show "H0' = denormalize H0" by (metis denormalize_properties(4) r1)
    show "Some H0' = Some h0 \<oplus> Some hf" using r1 by blast
    show "full_ownership (get_fh H0') \<and> no_guard H0'" using r1 by blast
    show "red_rtrans C' \<sigma>' C'' \<sigma>''"
      by (simp add: "3.hyps"(2))

    fix n
    have "safe (Suc n) (None :: ('i, 'a, nat) cont) C (s1, h) S"
      using "3.prems"(4) by force

    then have "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> H0 = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s0, h'') S"
    proof (rule safeNoneE(3)[of n C s1 h S H hf C' s0 H0])
      show "Some H = Some h \<oplus> Some hf" using "3.prems"(6) by blast
      show "full_ownership (get_fh H)" using "3.prems"(7) by blast
      show "no_guard H" using "3.prems"(7) by auto
      show "red C (s1, FractionalHeap.normalize (get_fh H)) C' (s0, H0)"
        by (metis "3.hyps"(1) "3.prems"(2) "3.prems"(5) \<open>\<sigma>' = (s0, H0)\<close> denormalize_properties(3))
    qed
    then obtain h3 H3' where
      r2: "full_ownership (get_fh H3') \<and> no_guard H3' \<and> H0 = FractionalHeap.normalize (get_fh H3') \<and> Some H3' = Some h3 \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s0, h3) S"
      by blast
    then have "h3 = h0"
      by (metis \<open>Some (denormalize H0) = Some h0 \<oplus> Some hf\<close> addition_cancellative denormalize_properties(4))
    moreover have "H3' = H0'"
      by (metis \<open>Some H0' = Some h0 \<oplus> Some hf\<close> calculation option.inject r2)
    ultimately show "safe n (None :: ('i, 'a, nat) cont) C' (s0, h0) S" using r2 by blast
  qed
  then show ?case by blast
qed

theorem atomic_rule_unique:
  fixes \<Gamma> :: "('i, 'a, nat) single_context"

  fixes map_to_list :: "nat \<Rightarrow> 'a list"
  fixes map_to_arg :: "nat \<Rightarrow> 'a"

  assumes "\<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr>"
      and "hoare_triple_valid (None :: ('i, 'a, nat) cont) (Star P (View f J (\<lambda>s. s x)))
          C (Star Q (View f J (\<lambda>s. uact index (s x) (map_to_arg (s uarg)))))"

      and "precise J \<and> unary J"
      and "view_function_of_inv \<Gamma>"
      and "x \<notin> fvC C \<union> fvA P \<union> fvA Q \<union> fvA J"

      and "uarg \<notin> fvC C"
      and "l \<notin> fvC C"

      and "x \<notin> fvS (\<lambda>s. map_to_list (s l))"
      and "x \<notin> fvS (\<lambda>s. map_to_arg (s uarg) # map_to_list (s l))"

      and "no_guard_assertion P"
      and "no_guard_assertion Q"

    shows "hoare_triple_valid (Some \<Gamma>) (Star P (UniqueGuard index (\<lambda>s. map_to_list (s l)))) (Catomic C)
                          (Star Q (UniqueGuard index (\<lambda>s. map_to_arg (s uarg) # map_to_list (s l))))"
proof -
  let ?J = "View f J (\<lambda>s. s x)"
  let ?J' = "View f J (\<lambda>s. uact index (s x) (map_to_arg (s uarg)))"
  let ?pre_l = "(\<lambda>s. map_to_list (s l))"
  let ?G = "UniqueGuard index ?pre_l"
  let ?l = "\<lambda>s. map_to_arg (s uarg) # map_to_list (s l)"
  let ?G' = "UniqueGuard index ?l"

  have unaries: "unary ?J \<and> unary ?J'"
    by (simp add: assms(3) unary_inv_then_view)
  moreover have precises: "precise ?J \<and> precise ?J'"
    by (simp add: assms(3) precise_inv_then_view)

  obtain \<Sigma> where asm0: "\<And>n \<sigma>. \<sigma>, \<sigma> \<Turnstile> Star P ?J \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C \<sigma> (\<Sigma> \<sigma>)"
      "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> Star P ?J \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (Star Q ?J')"
    using assms(2) hoare_triple_valid_def by blast

  define start where "start = (\<lambda>\<sigma>. { (s, h) |s h hj. agrees (- {x}) (fst \<sigma>) s \<and> Some h = Some (remove_guards (snd \<sigma>)) \<oplus> Some hj \<and> (s, hj), (s, hj) \<Turnstile> ?J})"
  define end_qj where "end_qj = (\<lambda>\<sigma>. \<Union>\<sigma>' \<in> start \<sigma>. \<Sigma> \<sigma>')"
  define \<Sigma>' where "\<Sigma>' = (\<lambda>\<sigma>. { (s, add_uguard_to_no_guard index hq (?l s)) |s hq h hj. (s, h) \<in> end_qj \<sigma> \<and> Some h = Some hq \<oplus> Some hj \<and> (s, hj), (s, hj) \<Turnstile> ?J' })"

  let ?\<Sigma>' = "\<lambda>\<sigma>. close_var (\<Sigma>' \<sigma>) x"

  show "hoare_triple_valid (Some \<Gamma>) (Star P ?G) (Catomic C) (Star Q ?G')"
  proof (rule hoare_triple_validI)
    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> Star P ?G \<Longrightarrow> pair_sat (?\<Sigma>' (s, h)) (?\<Sigma>' (s', h')) (Star Q ?G')"
    proof -
      fix s1 h1 s2 h2
      assume asm1: "(s1, h1), (s2, h2) \<Turnstile> Star P ?G"
      then obtain p1 p2 g1 g2 where r0: "Some h1 = Some p1 \<oplus> Some g1"
      "Some h2 = Some p2 \<oplus> Some g2"
      "(s1, p1), (s2, p2) \<Turnstile> P" "(s1, g1), (s2, g2) \<Turnstile> ?G"
        using hyper_sat.simps(4) by auto
      then obtain "remove_guards h1 = p1" "remove_guards h2 = p2"
        by (meson assms(10) hyper_sat.simps(13) no_guard_and_no_heap no_guard_assertion_def)

      have "pair_sat (\<Sigma>' (s1, h1)) (\<Sigma>' (s2, h2)) (Star Q ?G')"
      proof (rule pair_satI)
        fix s1' hqg1 s2' hqg2 \<sigma>2'
        assume asm2: "(s1', hqg1) \<in> \<Sigma>' (s1, h1) \<and> (s2', hqg2) \<in> \<Sigma>' (s2, h2)"
        then obtain h1' hj1' h2' hj2' hq1 hq2 where r: "(s1', h1') \<in> end_qj (s1, h1)" "Some h1' = Some hq1 \<oplus> Some hj1'"
          "(s1', hj1'), (s1', hj1') \<Turnstile> ?J'" "(s2', h2') \<in> end_qj (s2, h2)" "Some h2' = Some hq2 \<oplus> Some hj2'" "(s2', hj2'), (s2', hj2') \<Turnstile> ?J'"
          "hqg1 = add_uguard_to_no_guard index hq1 (?l s1')" "hqg2 = add_uguard_to_no_guard index hq2 (?l s2')"
          using \<Sigma>'_def by blast
        then obtain \<sigma>1' \<sigma>2' where "\<sigma>1' \<in> start (s1, h1)" "\<sigma>2' \<in> start (s2, h2)" "(s1', h1') \<in> \<Sigma> \<sigma>1'" "(s2', h2') \<in> \<Sigma> \<sigma>2'"
          using end_qj_def by blast
        then obtain hj1 hj2 where "agrees (- {x}) s1 (fst \<sigma>1')" "Some (snd \<sigma>1') = Some p1 \<oplus> Some hj1" "(fst \<sigma>1', hj1), (fst \<sigma>1', hj1) \<Turnstile> ?J"
          "agrees (- {x}) s2 (fst \<sigma>2')" "Some (snd \<sigma>2') = Some p2 \<oplus> Some hj2" "(fst \<sigma>2', hj2), (fst \<sigma>2', hj2) \<Turnstile> ?J"
          using start_def \<open>remove_guards h1 = p1\<close> \<open>remove_guards h2 = p2\<close> by force

        moreover have "(fst \<sigma>1', hj1), (fst \<sigma>2', hj2) \<Turnstile> ?J"
          using calculation(3) calculation(6) unaries unaryE by blast
        moreover have "(fst \<sigma>1', p1), (fst \<sigma>2', p2) \<Turnstile> P"
        proof -
          have "fvA P \<subseteq> - {x}"
            using assms(5) by force
          then have "agrees (fvA P) (fst \<sigma>1') s1 \<and> agrees (fvA P) (fst \<sigma>2') s2"
            using calculation(1) calculation(4)
            by (metis agrees_comm agrees_union subset_Un_eq)
          then show ?thesis using r0(3)
            by (meson agrees_same sat_comm)
        qed

        ultimately have "\<sigma>1', \<sigma>2' \<Turnstile> Star P ?J" using hyper_sat.simps(4)[of "fst \<sigma>1'" "snd \<sigma>1'" "fst \<sigma>2'" "snd \<sigma>2'"] prod.collapse
          by metis
        then have "pair_sat (\<Sigma> \<sigma>1') (\<Sigma> \<sigma>2') (Star Q ?J')"
          using asm0(2)[of \<sigma>1' \<sigma>2'] by blast
        then have "(s1', h1'), (s2', h2') \<Turnstile> Star Q ?J'"
          using \<open>(s1', h1') \<in> \<Sigma> \<sigma>1'\<close> \<open>(s2', h2') \<in> \<Sigma> \<sigma>2'\<close> pair_sat_def by blast
        moreover have "(s1', hj1'), (s2', hj2') \<Turnstile> ?J'"
          using r(3) r(6) unaries unaryE by blast
        moreover have "(s1', hq1), (s2', hq2) \<Turnstile> Q" using magic_lemma
          using calculation(1) calculation(2) precises r(2) r(5) by blast
        have "(s1', add_uguard_to_no_guard index hq1 (?l s1')), (s2', add_uguard_to_no_guard index hq2 (?l s2')) \<Turnstile> Star Q ?G'"
        proof (rule no_guard_then_sat_star_uguard)
          show "no_guard hq1 \<and> no_guard hq2"
            using \<open>(s1', hq1), (s2', hq2) \<Turnstile> Q\<close> assms(11) no_guard_assertion_def by blast
          show "(s1', hq1), (s2', hq2) \<Turnstile> Q"
            using \<open>(s1', hq1), (s2', hq2) \<Turnstile> Q\<close> by auto
        qed
        then show "(s1', hqg1), (s2', hqg2) \<Turnstile> Star Q ?G'"
          using r(7) r(8) by force
      qed
      then show "pair_sat (?\<Sigma>' (s1, h1)) (?\<Sigma>' (s2, h2)) (Star Q ?G')"
      proof (rule pair_sat_close_var_double)
        show "x \<notin> fvA (Star Q (UniqueGuard index (\<lambda>s. map_to_arg (s uarg) # map_to_list (s l))))"
          using assms(5) assms(9) by auto
      qed
    qed

    fix pre_s h k
    assume "(pre_s, h), (pre_s, h) \<Turnstile> Star P ?G"
    then obtain pp gg where "Some h = Some pp \<oplus> Some gg" "(pre_s, pp), (pre_s, pp) \<Turnstile> P" "(pre_s, gg), (pre_s, gg) \<Turnstile> ?G"
      using always_sat_refl hyper_sat.simps(4) by blast
    then have "remove_guards h = pp"
      using assms(10) hyper_sat.simps(13) no_guard_and_no_heap no_guard_assertion_def by metis
    then have "(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P"
      using \<open>(pre_s, pp), (pre_s, pp) \<Turnstile> P\<close> hyper_sat.simps(9) by blast
    then have "(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P"
      by (simp add: no_guard_remove_guards)

    show "safe k (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))"
    proof (cases k)
      case (Suc n)
      moreover have "safe (Suc n) (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))"
      proof (rule safeSomeAltI)
        show "Catomic C = Cskip \<Longrightarrow> (pre_s, h) \<in> ?\<Sigma>' (pre_s, h)" by simp

        fix H hf hj v0

        assume asm2: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv pre_s hj \<Gamma>"

        define v where "v = f (normalize (get_fh H))"
        define s where "s = pre_s(x := v)"
        then have "v = s x" by simp
        moreover have agreements: "agrees (fvC C \<union> fvA P \<union> fvA Q \<union> fvA J \<union> fvA (UniqueGuard k ?pre_l)) s pre_s"
          by (metis UnE agrees_comm agrees_update assms(5) assms(8) fvA.simps(9) s_def)
        have asm1: "(s, h), (s, h) \<Turnstile> Star P ?G"
          using Un_iff[of x] \<open>(pre_s, h), (pre_s, h) \<Turnstile> Star P (UniqueGuard index (\<lambda>s. map_to_list (s l)))\<close>
            agrees_same agrees_update[of x] always_sat_refl assms(5) assms(8) fvA.simps(3)[of P "UniqueGuard index (\<lambda>s. map_to_list (s l))"]
            fvA.simps(9)[of index " (\<lambda>s. map_to_list (s l))"] s_def
          by metis
        moreover have asm2_bis: "sat_inv s hj \<Gamma>"
        proof (rule sat_inv_agrees)
          show "sat_inv pre_s hj \<Gamma>" using asm2 by simp
          show "agrees (fvA (invariant \<Gamma>)) pre_s s"
            using assms(1) assms(5) s_def
            by (simp add: agrees_update)
        qed
        moreover have "(s, remove_guards h), (s, remove_guards h) \<Turnstile> P"
          by (meson \<open>(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P\<close> agreements agrees_same agrees_union always_sat_refl)

        moreover have "agrees (- {x}) pre_s s"
        proof (rule agreesI)
          fix y assume "y \<in> - {x}"
          then have "y \<noteq> x" 
            by force
          then show "pre_s y = s y"
            by (simp add: s_def)
        qed

        moreover obtain "(s, pp), (s, pp) \<Turnstile> P" "(s, gg), (s, gg) \<Turnstile> ?G"
          by (metis \<open>(pre_s, gg), (pre_s, gg) \<Turnstile> UniqueGuard index (\<lambda>s. map_to_list (s l))\<close> \<open>remove_guards h = pp\<close> agrees_same_aux agrees_update always_sat_refl_aux assms(8) calculation(4) fvA.simps(9) s_def)

        let ?hf = "remove_guards hf"
        let ?H = "remove_guards H"
        let ?h = "remove_guards h"

        obtain hhj where "Some hhj = Some h \<oplus> Some hj"
          by (metis asm2 plus.simps(2) plus.simps(3) plus_comm)
        then have "Some H = Some hhj \<oplus> Some hf"
          using asm2 by presburger
        then have "Some (remove_guards hhj) = Some ?h \<oplus> Some hj"
          by (metis \<open>Some hhj = Some h \<oplus> Some hj\<close> asm2 no_guards_remove remove_guards_sum sat_inv_def)

        moreover have "f (normalize (get_fh hj)) = v"
        proof -
          have "view \<Gamma> (normalize (get_fh hj)) = view \<Gamma> (normalize (get_fh H))"
            using assms(4) view_function_of_invE
            by (metis (no_types, opaque_lifting) \<open>Some hhj = Some h \<oplus> Some hj\<close> asm2 larger_def larger_trans plus_comm)
          then show ?thesis using assms(1) v_def by fastforce
        qed


        then have "(s, hj), (s, hj) \<Turnstile> ?J"
          by (metis \<open>v = s x\<close> asm2_bis assms(1) hyper_sat.simps(11) sat_inv_def select_convs(5))

        ultimately have "(s, remove_guards hhj), (s, remove_guards hhj) \<Turnstile> Star P ?J"
          using \<open>(s, remove_guards h), (s, remove_guards h) \<Turnstile> P\<close> hyper_sat.simps(4) by blast



        then have all_safes: "\<And>n. safe n (None :: ('i, 'a, nat) cont) C (s, remove_guards hhj) (\<Sigma> (s, remove_guards hhj))"
          using asm0(1) by blast
        then have "\<And>\<sigma>1 H1 \<sigma>2 H2 s2 C2. red_rtrans C \<sigma>1 C2 \<sigma>2 \<Longrightarrow> \<sigma>1 = (s, H1) \<Longrightarrow> \<sigma>2 = (s2, H2) \<Longrightarrow>
          ?H = denormalize H1 \<Longrightarrow>
\<not> aborts C2 \<sigma>2 \<and> (C2 = Cskip \<longrightarrow> (\<exists>h1 H'. Some H' = Some h1 \<oplus> Some ?hf \<and> H2 = FractionalHeap.normalize (get_fh H')
  \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"
        proof -
          fix \<sigma>1 H1 \<sigma>2 H2 s2 C2
          assume "?H = denormalize H1"
          assume "red_rtrans C \<sigma>1 C2 \<sigma>2" "\<sigma>1 = (s, H1)" "\<sigma>2 = (s2, H2)"

          then show "\<not> aborts C2 \<sigma>2 \<and>
       (C2 = Cskip \<longrightarrow>
        (\<exists>h1 H'.
            Some H' = Some h1 \<oplus> Some (remove_guards hf) \<and>
            H2 = FractionalHeap.normalize (get_fh H') \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"
            using all_safes
          proof (rule safe_atomic)
            show "?H = denormalize H1" using \<open>?H = denormalize H1\<close> by simp
            show "Some ?H = Some (remove_guards hhj) \<oplus> Some ?hf"
              using \<open>Some H = Some hhj \<oplus> Some hf\<close> remove_guards_sum by blast
            show "full_ownership (get_fh (remove_guards H)) \<and> no_guard (remove_guards H)"
              by (metis asm2 get_fh_remove_guards no_guard_remove_guards)
          qed
        qed
        moreover have "?H = denormalize (normalize (get_fh H))"
          by (metis asm2 denormalize_properties(5))
        ultimately have safe_atomic_simplified: "\<And>\<sigma>2 H2 s2 C2. red_rtrans C (s, normalize (get_fh H)) C2 \<sigma>2
         \<Longrightarrow> \<sigma>2 = (s2, H2) \<Longrightarrow> \<not> aborts C2 \<sigma>2 \<and> (C2 = Cskip \<longrightarrow> (\<exists>h1 H'. Some H' = Some h1 \<oplus> Some ?hf \<and> H2 = FractionalHeap.normalize (get_fh H')
  \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"
          by presburger

        have "\<not> aborts (Catomic C) (s, normalize (get_fh H))"
        proof (rule ccontr)
          assume "\<not> \<not> aborts (Catomic C) (s, normalize (get_fh H))"
          then obtain C' \<sigma>' where asm3: "red_rtrans C (s, FractionalHeap.normalize (get_fh H)) C' \<sigma>'"
          "aborts C' \<sigma>'"
            using abort_atomic_cases by blast
          then have "\<not> aborts C' \<sigma>'" using safe_atomic_simplified[of C' \<sigma>' "fst \<sigma>'" "snd \<sigma>'"] by simp
          then show False using asm3(2) by simp
        qed
        then show "\<not> aborts (Catomic C) (pre_s, normalize (get_fh H))"
          by (metis agreements aborts_agrees agrees_comm agrees_union fst_eqD fvC.simps(11) snd_conv)

        fix C' pre_s' h'
        assume "red (Catomic C) (pre_s, FractionalHeap.normalize (get_fh H)) C' (pre_s', h')"
        then obtain s' where "red (Catomic C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
          "agrees (- {x}) s' pre_s'"
          by (metis (no_types, lifting) UnI1 \<open>agrees (- {x}) pre_s s\<close> agrees_comm assms(5) fst_eqD fvC.simps(11) red_agrees snd_conv subset_Compl_singleton)

        then obtain h1 H' where asm3: "Some H' = Some h1 \<oplus> Some (remove_guards hf)" "C' = Cskip"
          "h' = FractionalHeap.normalize (get_fh H')" "no_guard H' \<and> full_ownership (get_fh H')" "(s', h1) \<in> \<Sigma> (s, remove_guards hhj)"
          using safe_atomic_simplified[of C' "(s', h')" s' h']  by (metis red_atomic_cases)

        moreover have "s x = s' x  \<and> s' uarg = s uarg \<and> s l = s' l" using red_not_in_fv_not_touched
          using \<open>red (Catomic C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')\<close>
          by (metis Un_iff assms(5) assms(6) assms(7) fst_conv fvC.simps(11))
        have "\<exists>hq' hj'. Some h1 = Some hq' \<oplus> Some hj' \<and> (s', add_uguard_to_no_guard index hq' (?l s')) \<in> \<Sigma>' (pre_s, h) \<and> sat_inv s' hj' \<Gamma>
          \<and> f (normalize (get_fh hj')) = uact index (s' x) (map_to_arg (s' uarg))"
        proof -

          have "pair_sat (\<Sigma> (s, remove_guards hhj)) (\<Sigma> (s, remove_guards hhj)) (Star Q ?J')"
            using asm0(2)[of "(s, remove_guards hhj)" "(s, remove_guards hhj)"]
            using \<open>(s, remove_guards hhj), (s, remove_guards hhj) \<Turnstile> Star P ?J\<close> by blast
          then have "(s', h1), (s', h1) \<Turnstile> Star Q ?J'"
            using asm3(5) pair_sat_def by blast
          then obtain hq' hj' where "Some h1 = Some hq' \<oplus> Some hj'" "(s', hq'), (s', hq') \<Turnstile> Q" "(s', hj'), (s', hj') \<Turnstile> ?J'"
            using always_sat_refl hyper_sat.simps(4) by blast
          then have "no_guard hj'"
            by (metis (no_types, opaque_lifting) calculation(1) calculation(4) no_guard_then_smaller_same plus_comm)
          moreover have "f (normalize (get_fh hj')) = uact index (s' x) (map_to_arg (s' uarg))"
            using \<open>(s', hj'), (s', hj') \<Turnstile> View f J (\<lambda>s. uact index (s x) (map_to_arg (s uarg)))\<close> by auto
          moreover have "(s, remove_guards hhj) \<in> start (pre_s, h)"
          proof -
            have "Some (remove_guards hhj) = Some ?h \<oplus> Some hj"
              using \<open>Some (remove_guards hhj) = Some (remove_guards h) \<oplus> Some hj\<close> by blast
            moreover have "(s, hj), (s, hj) \<Turnstile> ?J"
              using \<open>(s, hj), (s, hj) \<Turnstile> ?J\<close> by fastforce
            ultimately show ?thesis using start_def
              using \<open>agrees (- {x}) pre_s s\<close> by fastforce
          qed
          then have "(s', h1) \<in> end_qj (pre_s, h)"
            using \<open>end_qj \<equiv> \<lambda>\<sigma>. \<Union> (\<Sigma> ` start \<sigma>)\<close> asm3(5) by blast

          then have "(s', add_uguard_to_no_guard index hq' (?l s')) \<in> \<Sigma>' (pre_s, h)"
            using \<Sigma>'_def \<open>(s', hj'), (s', hj') \<Turnstile> ?J'\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> by blast
          ultimately show "\<exists>hq' hj'.
       Some h1 = Some hq' \<oplus> Some hj' \<and>
       (s', add_uguard_to_no_guard index hq' (map_to_arg (s' uarg) # map_to_list (s' l))) \<in> \<Sigma>' (pre_s, h) \<and>
       sat_inv s' hj' \<Gamma> \<and> f (FractionalHeap.normalize (get_fh hj')) = uact index (s' x) (map_to_arg (s' uarg))"
            using \<open>(s', hj'), (s', hj') \<Turnstile> ?J'\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close>
              assms(1) hyper_sat.simps(11) sat_inv_def select_convs(5)
            by fastforce
        qed
        then obtain hq' hj' where "Some h1 = Some hq' \<oplus> Some hj'" "(s', add_uguard_to_no_guard index hq' (?l s')) \<in> \<Sigma>' (pre_s, h)" "sat_inv s' hj' \<Gamma>"
  "f (normalize (get_fh hj')) = uact index (s' x) (map_to_arg (s' uarg))"
          by blast
        then have "safe n (Some \<Gamma>) C' (s', add_uguard_to_no_guard index hq' (?l s')) (\<Sigma>' (pre_s, h))"
          using asm3(2) safe_skip by blast

        moreover have "\<exists>H''. semi_consistent \<Gamma> v0 H'' \<and> Some H'' = Some (add_uguard_to_no_guard index hq' (?l s')) \<oplus> Some hj' \<oplus> Some hf"
        proof -
          have "Some (add_uguard_to_no_guard index hq' (?l s')) = Some hq' \<oplus> Some (Map.empty, None, [index \<mapsto> ?l s'])"
            by (metis \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> add_uguard_as_sum calculation(1) calculation(4) no_guard_then_smaller_same)

          obtain hhf where "Some hhf = Some h \<oplus> Some hf"
            by (metis (no_types, opaque_lifting) \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>Some hhj = Some h \<oplus> Some hj\<close> option.exhaust_sel plus.simps(1) plus_asso plus_comm)
          then have "all_guards hhf"
            by (metis (no_types, lifting) all_guards_no_guard_propagates asm2 plus_asso plus_comm sat_inv_def semi_consistent_def)
          moreover have "get_gs h = None \<and> get_gu h index = Some (?pre_l s)"
          proof -
            have "no_guard pp"
              using \<open>remove_guards h = pp\<close> no_guard_remove_guards by blast
            then show ?thesis
              by (metis (no_types, lifting) \<open>Some h = Some pp \<oplus> Some gg\<close> \<open>\<And>thesis. (\<lbrakk>(s, pp), (s, pp) \<Turnstile> P; (s, gg), (s, gg) \<Turnstile> UniqueGuard index (\<lambda>s. map_to_list (s l))\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> full_uguard_sum_same hyper_sat.simps(13) no_guard_remove(1) plus_comm)
          qed
          moreover have "\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu h i' = None"
            by (metis \<open>Some h = Some pp \<oplus> Some gg\<close> \<open>\<And>thesis. (\<lbrakk>(s, pp), (s, pp) \<Turnstile> P; (s, gg), (s, gg) \<Turnstile> UniqueGuard index (\<lambda>s. map_to_list (s l))\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>remove_guards h = pp\<close> hyper_sat.simps(13) no_guard_remove(2) no_guard_remove_guards plus_comm)
          then obtain sargs where "get_gu hf index = None \<and> get_gs hf = Some (pwrite, sargs)"
            by (metis (no_types, opaque_lifting) \<open>Some hhf = Some h \<oplus> Some hf\<close> add_gs.simps(1) all_guards_def calculation(1) calculation(2) compatible_def compatible_eq option.distinct(1) plus_extract(2))
          moreover obtain uargs where "\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu hf i' = Some (uargs i')"
            by (metis (no_types, opaque_lifting) \<open>Some hhf = Some h \<oplus> Some hf\<close> \<open>\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu h i' = None\<close> add_gu_def add_gu_single.simps(1) all_guards_exists_uargs calculation(1) plus_extract(3))

          then obtain ghf where ghf_def: "Some hf = Some (remove_guards hf) \<oplus> Some ghf"
          "get_fh ghf = Map.empty" "get_gu ghf index = None"
          "get_gs ghf = Some (pwrite, sargs)" "\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu ghf i' = Some (uargs i')"
            using decompose_guard_remove_easy[of hf]
            using calculation(3) by auto

          have "(Map.empty, None, [index \<mapsto> ?l s']) ## ghf"
          proof (rule compatibleI)
            show "compatible_fract_heaps (get_fh (Map.empty, None, [index \<mapsto> map_to_arg (s' uarg) # map_to_list (s' l)])) (get_fh ghf)"
              using compatible_fract_heapsI by fastforce
            show "\<And>k. get_gu (Map.empty, None, [index \<mapsto> map_to_arg (s' uarg) # map_to_list (s' l)]) k = None \<or> get_gu ghf k = None"
              using ghf_def(3) by auto
          qed (simp)
          then obtain g where g_def: "Some g = Some (Map.empty, None, [index \<mapsto> ?l s']) \<oplus> Some ghf"
            by simp
          moreover have "H' ## g"
          proof (rule compatibleI)
            have "get_fh g = add_fh Map.empty Map.empty"
              using add_get_fh[of g "(Map.empty, None, [index \<mapsto> ?l s'])" ghf]
                g_def \<open>get_fh ghf = Map.empty\<close>
              by fastforce
            then have "get_fh g = Map.empty"
              using add_fh_map_empty by auto
            then show "compatible_fract_heaps (get_fh H') (get_fh g)"
              using compatible_fract_heapsI by force
            show "\<And>k. get_gu H' k = None \<or> get_gu g k = None"
              by (meson asm3(4) no_guard_def)
            show "\<And>p p'. get_gs H' = Some p \<and> get_gs g = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
              by (metis asm3(4) no_guard_def option.simps(3))
          qed
          then obtain H'' where "Some H'' = Some H' \<oplus> Some g"
            by simp
          then have "Some H'' = Some (add_uguard_to_no_guard index hq' (?l s')) \<oplus> Some hj' \<oplus> Some hf"
          proof -
            have "Some H'' = Some h1 \<oplus> Some g \<oplus> Some (remove_guards hf)"
              by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> asm3(1) plus_comm simpler_asso)
            moreover have "Some (add_uguard_to_no_guard index hq' (?l s')) = Some hq' \<oplus> Some (Map.empty, None, [index \<mapsto> ?l s'])"
              using \<open>Some (add_uguard_to_no_guard index hq' (map_to_arg (s' uarg) # map_to_list (s' l))) = Some hq' \<oplus> Some (Map.empty, None, [index \<mapsto> map_to_arg (s' uarg) # map_to_list (s' l)])\<close> by blast
            ultimately show ?thesis
              by (metis (no_types, lifting) \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> g_def ghf_def(1) plus_comm simpler_asso)
          qed

          moreover have "semi_consistent \<Gamma> v0 H''"
          proof (rule semi_consistentI)
            have "get_gs g = Some (pwrite, sargs)"
              by (metis full_sguard_sum_same g_def ghf_def(4) plus_comm)
            moreover have "get_gu g index = Some (?l s')"
            proof (rule full_uguard_sum_same)
              show "get_gu (Map.empty, None, [index \<mapsto> ?l s']) index = Some (?l s')"
                using get_gu.simps by auto
              show "Some g = Some (Map.empty, None, [index \<mapsto> ?l s']) \<oplus> Some ghf"
                using g_def by auto
            qed
            moreover have "\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu g i' = Some (uargs i')"
              by (metis full_uguard_sum_same g_def ghf_def(5) plus_comm)
            ultimately have "all_guards g"
              by (metis all_guardsI option.discI)
            then show "all_guards H''"
              by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> all_guards_same plus_comm)
            show "reachable \<Gamma> v0 H''"
            proof (rule reachableI)
              fix sargs' uargs'
              assume "get_gs H'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H'' k = Some (uargs' k))"
              then have "sargs = sargs'"
                by (metis (no_types, opaque_lifting) Pair_inject \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>get_gs g = Some (pwrite, sargs)\<close> full_sguard_sum_same option.inject plus_comm)
              moreover have "uargs' index = ?l s'"
                by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>get_gs H'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H'' k = Some (uargs' k))\<close> \<open>get_gu g index = Some (map_to_arg (s' uarg) # map_to_list (s' l))\<close> asm3(4) no_guard_remove(2) option.inject plus_comm)
              moreover have "\<And>i'. i' \<noteq> index \<Longrightarrow> uargs' i' = uargs i'"
                by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu g i' = Some (uargs i')\<close> \<open>get_gs H'' = Some (pwrite, sargs') \<and> (\<forall>k. get_gu H'' k = Some (uargs' k))\<close> asm3(4) no_guard_remove(2) option.sel plus_comm)
              moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh hj')) = view \<Gamma> (FractionalHeap.normalize (get_fh H''))"
                using assms(4) \<open>sat_inv s' hj' \<Gamma>\<close>
              proof (rule view_function_of_invE)
                show "H'' \<succeq> hj'"
                  by (metis (no_types, opaque_lifting) \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> asm3(1) larger_def larger_trans plus_comm)
              qed
              moreover have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs (uargs(index := ?l s')) (uact index (s' x) (map_to_arg (s' uarg)))"
              proof -

                have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs (uargs(index := ?pre_l s')) (view \<Gamma> (FractionalHeap.normalize (get_fh H)))"
                proof -
                  have "reachable \<Gamma> v0 H"
                    by (meson asm2 semi_consistent_def)
                  moreover have "get_gs H = Some (pwrite, sargs)"
                    by (metis \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>get_gu hf index = None \<and> get_gs hf = Some (pwrite, sargs)\<close> full_sguard_sum_same plus_comm)
                  moreover have "get_gu H index = Some (?pre_l s')"
                    by (metis \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>Some hhj = Some h \<oplus> Some hj\<close> \<open>get_gs h = None \<and> get_gu h index = Some (map_to_list (s l))\<close> \<open>s x = s' x \<and> s' uarg = s uarg \<and> s l = s' l\<close> full_uguard_sum_same)
                  moreover have "\<And>i. i \<noteq> index \<Longrightarrow> get_gu H i = Some (uargs i)"
                    by (metis \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>\<And>i'. i' \<noteq> index \<Longrightarrow> get_gu hf i' = Some (uargs i')\<close> full_uguard_sum_same plus_comm)
                  ultimately show ?thesis
                    by (simp add: reachable_def)
                qed
                moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh hj)) = view \<Gamma> (FractionalHeap.normalize (get_fh H))"
                  using assms(4)
                proof (rule view_function_of_invE)
                  show "sat_inv s hj \<Gamma>"
                    by (simp add: asm2_bis)
                  show "H \<succeq> hj"
                    by (metis (no_types, opaque_lifting) \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>Some hhj = Some h \<oplus> Some hj\<close> larger_def larger_trans plus_comm)
                qed
                moreover have "s' x = v"
                  using \<open>s x = s' x \<and> s' uarg = s uarg \<and> s l = s' l\<close> \<open>v = s x\<close> by presburger
                ultimately have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs (uargs(index := ?pre_l s')) v"
                  using \<open>f (FractionalHeap.normalize (get_fh hj)) = v\<close> assms(1) by auto
                then show ?thesis
                  by (metis UniqueStep \<open>s' x = v\<close> assms(1) fun_upd_same fun_upd_upd select_convs(4))
              qed
              moreover have "uargs' =  (uargs(index := map_to_arg (s' uarg) # map_to_list (s' l)))"
              proof (rule ext)
                fix i show "uargs' i = (uargs(index := map_to_arg (s' uarg) # map_to_list (s' l))) i"
                  apply (cases "i = index")
                  using calculation(2) apply auto[1]
                  using calculation(3) by force
              qed
              ultimately show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs' uargs' (view \<Gamma> (FractionalHeap.normalize (get_fh H'')))"
                using \<open>f (FractionalHeap.normalize (get_fh hj')) = uact index (s' x) (map_to_arg (s' uarg))\<close> assms(1) by force
            qed
          qed
          ultimately show "\<exists>H''. semi_consistent \<Gamma> v0 H'' \<and> Some H'' = Some (add_uguard_to_no_guard index hq' (map_to_arg (s' uarg) # map_to_list (s' l))) \<oplus> Some hj' \<oplus> Some hf"
            by blast
        qed
        ultimately obtain H'' where "semi_consistent \<Gamma> v0 H'' \<and>
  Some H'' = Some (add_uguard_to_no_guard index hq' (map_to_arg (s' uarg) # map_to_list (s' l))) \<oplus> Some hj' \<oplus> Some hf" by blast
        moreover have "full_ownership (get_fh H'') \<and> h' = FractionalHeap.normalize (get_fh H'')"
        proof -
          obtain x where "Some x = Some (add_uguard_to_no_guard index hq' (?l s')) \<oplus> Some hj'"
            by (metis calculation not_Some_eq plus.simps(1))
          then have "get_fh H'' = add_fh (add_fh (get_fh (add_uguard_to_no_guard index hq' (?l s'))) (get_fh hj')) (get_fh hf)"
            by (metis add_get_fh calculation)
          moreover have "get_fh (add_uguard_to_no_guard index hq' (?l s')) = get_fh hq' \<and> get_fh hf = get_fh (remove_guards hf)"
            by (metis get_fh_add_uguard get_fh_remove_guards)
          ultimately show ?thesis
            by (metis \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> add_get_fh asm3(1) asm3(3) asm3(4))
        qed
        moreover have "sat_inv pre_s' hj' \<Gamma>"
        proof (rule sat_inv_agrees)
          show "sat_inv s' hj' \<Gamma>"
            by (simp add: \<open>sat_inv s' hj' \<Gamma>\<close>)
          show "agrees (fvA (invariant \<Gamma>)) s' pre_s'"
            using UnCI \<open>agrees (- {x}) s' pre_s'\<close> assms(1) assms(5) select_convs(5) subset_Compl_singleton
            by (metis agrees_union sup.orderE)
        qed
        moreover have "safe n (Some \<Gamma>) C' (pre_s', add_uguard_to_no_guard index hq' (?l s')) (?\<Sigma>' (pre_s, h))"
        proof (rule safe_free_vars_Some)
          show "safe n (Some \<Gamma>) C' (s', add_uguard_to_no_guard index hq' (?l s')) (?\<Sigma>' (pre_s, h))"
            by (meson \<open>safe n (Some \<Gamma>) C' (s', add_uguard_to_no_guard index hq' (map_to_arg (s' uarg) # map_to_list (s' l))) (\<Sigma>' (pre_s, h))\<close> close_var_subset safe_larger_set)
          show "agrees (fvC C' \<union> (- {x}) \<union> fvA (invariant \<Gamma>)) s' pre_s'"
            by (metis UnI2 Un_absorb1 \<open>agrees (- {x}) s' pre_s'\<close> asm3(2) assms(1) assms(5) empty_iff fvC.simps(1) inf_sup_aci(5) select_convs(5) subset_Compl_singleton)
          show "upper_fvs (close_var (\<Sigma>' (pre_s, h)) x) (- {x})"
            by (simp add: upper_fvs_close_vars)
        qed
        ultimately show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv pre_s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf
          \<and> safe n (Some \<Gamma>) C' (pre_s', h'') (?\<Sigma>' (pre_s, h))" using \<open>sat_inv s' hj' \<Gamma>\<close> by blast
      qed
      ultimately show "safe k (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))" by blast
    qed (simp)
  qed
qed


theorem atomic_rule_shared:
  fixes \<Gamma> :: "('i, 'a, nat) single_context"

  fixes map_to_multiset :: "nat \<Rightarrow> 'a multiset"
  fixes map_to_arg :: "nat \<Rightarrow> 'a"

  assumes "\<Gamma> = \<lparr> view = f, abstract_view = \<alpha>, saction = sact, uaction = uact, invariant = J \<rparr>"
      and "hoare_triple_valid (None :: ('i, 'a, nat) cont) (Star P (View f J (\<lambda>s. s x))) C
          (Star Q (View f J (\<lambda>s. sact (s x) (map_to_arg (s sarg)))))"
      and "precise J \<and> unary J"
      and "view_function_of_inv \<Gamma>"
      and "x \<notin> fvC C \<union> fvA P \<union> fvA Q \<union> fvA J"

      and "sarg \<notin> fvC C"
      and "ms \<notin> fvC C"

      and "x \<notin> fvS (\<lambda>s. map_to_multiset (s ms))"
      and "x \<notin> fvS (\<lambda>s. {# map_to_arg (s sarg) #} + map_to_multiset (s ms))"

      and "no_guard_assertion P"
      and "no_guard_assertion Q"
  
  shows "hoare_triple_valid (Some \<Gamma>) (Star P (SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms)))) (Catomic C)
        (Star Q (SharedGuard \<pi> (\<lambda>s. {# map_to_arg (s sarg) #} + map_to_multiset (s ms))))"
proof -

  let ?J = "View f J (\<lambda>s. s x)"
  let ?J' = "View f J (\<lambda>s. sact (s x) (map_to_arg (s sarg)))"
  let ?pre_ms = "\<lambda>s. map_to_multiset (s ms)"
  let ?G = "SharedGuard \<pi> ?pre_ms"
  let ?ms = "\<lambda>s. {# map_to_arg (s sarg) #} + map_to_multiset (s ms)"
  let ?G' = "SharedGuard \<pi> ?ms"

  have unaries: "unary ?J \<and> unary ?J'"
    by (simp add: assms(3) unary_inv_then_view)
  moreover have precises: "precise ?J \<and> precise ?J'"
    by (simp add: assms(3) precise_inv_then_view)

  obtain \<Sigma> where asm0: "\<And>n \<sigma>. \<sigma>, \<sigma> \<Turnstile> Star P ?J \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C \<sigma> (\<Sigma> \<sigma>)"
      "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> Star P ?J \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (Star Q ?J')"
    using assms(2) hoare_triple_valid_def by blast

  define start where "start = (\<lambda>\<sigma>. { (s, h) |s h hj. agrees (- {x}) (fst \<sigma>) s \<and> Some h = Some (remove_guards (snd \<sigma>)) \<oplus> Some hj \<and> (s, hj), (s, hj) \<Turnstile> ?J})"
  define end_qj where "end_qj = (\<lambda>\<sigma>. \<Union>\<sigma>' \<in> start \<sigma>. \<Sigma> \<sigma>')"
  define \<Sigma>' where "\<Sigma>' = (\<lambda>\<sigma>. { (s, add_sguard_to_no_guard hq \<pi> (?ms s)) |s hq h hj. (s, h) \<in> end_qj \<sigma> \<and> Some h = Some hq \<oplus> Some hj \<and> (s, hj), (s, hj) \<Turnstile> ?J' })"

  let ?\<Sigma>' = "\<lambda>\<sigma>. close_var (\<Sigma>' \<sigma>) x"

  show "hoare_triple_valid (Some \<Gamma>) (Star P ?G) (Catomic C) (Star Q ?G')"
  proof (rule hoare_triple_validI)
    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> Star P ?G \<Longrightarrow> pair_sat (?\<Sigma>' (s, h)) (?\<Sigma>' (s', h')) (Star Q ?G')"
    proof -
      fix s1 h1 s2 h2
      assume asm1: "(s1, h1), (s2, h2) \<Turnstile> Star P ?G"
      then obtain p1 p2 g1 g2 where r0: "Some h1 = Some p1 \<oplus> Some g1"
      "Some h2 = Some p2 \<oplus> Some g2"
      "(s1, p1), (s2, p2) \<Turnstile> P" "(s1, g1), (s2, g2) \<Turnstile> ?G"
        using hyper_sat.simps(4) by auto
      then obtain "remove_guards h1 = p1" "remove_guards h2 = p2"
        using assms(10) hyper_sat.simps(12) no_guard_and_no_heap no_guard_assertion_def
        by metis

      have "pair_sat (\<Sigma>' (s1, h1)) (\<Sigma>' (s2, h2)) (Star Q ?G')"
      proof (rule pair_satI)
        fix s1' hqg1 s2' hqg2 \<sigma>2'
        assume asm2: "(s1', hqg1) \<in> \<Sigma>' (s1, h1) \<and> (s2', hqg2) \<in> \<Sigma>' (s2, h2)"
        then obtain h1' hj1' h2' hj2' hq1 hq2 where r: "(s1', h1') \<in> end_qj (s1, h1)" "Some h1' = Some hq1 \<oplus> Some hj1'"
          "(s1', hj1'), (s1', hj1') \<Turnstile> ?J'" "(s2', h2') \<in> end_qj (s2, h2)" "Some h2' = Some hq2 \<oplus> Some hj2'" "(s2', hj2'), (s2', hj2') \<Turnstile> ?J'"
          "hqg1 = add_sguard_to_no_guard hq1 \<pi> (?ms s1')" "hqg2 = add_sguard_to_no_guard hq2 \<pi> (?ms s2')"
          using \<Sigma>'_def by blast
        then obtain \<sigma>1' \<sigma>2' where "\<sigma>1' \<in> start (s1, h1)" "\<sigma>2' \<in> start (s2, h2)" "(s1', h1') \<in> \<Sigma> \<sigma>1'" "(s2', h2') \<in> \<Sigma> \<sigma>2'"
          using end_qj_def by blast
        then obtain hj1 hj2 where "agrees (- {x}) s1 (fst \<sigma>1')" "Some (snd \<sigma>1') = Some p1 \<oplus> Some hj1" "(fst \<sigma>1', hj1), (fst \<sigma>1', hj1) \<Turnstile> ?J"
          "agrees (- {x}) s2 (fst \<sigma>2')" "Some (snd \<sigma>2') = Some p2 \<oplus> Some hj2" "(fst \<sigma>2', hj2), (fst \<sigma>2', hj2) \<Turnstile> ?J"
          using start_def \<open>remove_guards h1 = p1\<close> \<open>remove_guards h2 = p2\<close> by force

        moreover have "(fst \<sigma>1', hj1), (fst \<sigma>2', hj2) \<Turnstile> ?J"
          using calculation(3) calculation(6) unaries unaryE by blast
        moreover have "(fst \<sigma>1', p1), (fst \<sigma>2', p2) \<Turnstile> P"
        proof -
          have "fvA P \<subseteq> - {x}"
            using assms(5) by force
          then have "agrees (fvA P) (fst \<sigma>1') s1 \<and> agrees (fvA P) (fst \<sigma>2') s2"
            using calculation(1) calculation(4)
            by (metis agrees_comm agrees_union subset_Un_eq)
          then show ?thesis using r0(3)
            by (meson agrees_same sat_comm)
        qed

        ultimately have "\<sigma>1', \<sigma>2' \<Turnstile> Star P ?J" using hyper_sat.simps(4)[of "fst \<sigma>1'" "snd \<sigma>1'" "fst \<sigma>2'" "snd \<sigma>2'"] prod.collapse
          by metis
        then have "pair_sat (\<Sigma> \<sigma>1') (\<Sigma> \<sigma>2') (Star Q ?J')"
          using asm0(2)[of \<sigma>1' \<sigma>2'] by blast
        then have "(s1', h1'), (s2', h2') \<Turnstile> Star Q ?J'"
          using \<open>(s1', h1') \<in> \<Sigma> \<sigma>1'\<close> \<open>(s2', h2') \<in> \<Sigma> \<sigma>2'\<close> pair_sat_def by blast
        moreover have "(s1', hj1'), (s2', hj2') \<Turnstile> ?J'"
          using r(3) r(6) unaries unaryE by blast
        moreover have "(s1', hq1), (s2', hq2) \<Turnstile> Q" using magic_lemma
          using calculation(1) calculation(2) precises r(2) r(5) by blast
        moreover have "no_guard hq1 \<and> no_guard hq2"
          using assms(11) calculation(3) no_guard_assertion_def by blast
        ultimately show "(s1', hqg1), (s2', hqg2) \<Turnstile> Star Q ?G'"
          using no_guard_then_sat_star r(7) r(8)
          by (metis (mono_tags, lifting))
      qed
      then show "pair_sat (?\<Sigma>' (s1, h1)) (?\<Sigma>' (s2, h2)) (Star Q ?G')"
      proof (rule pair_sat_close_var_double)
        show "x \<notin> fvA (Star Q (SharedGuard \<pi> (\<lambda>s. {#map_to_arg (s sarg)#} + map_to_multiset (s ms))))"
          using assms(5) assms(9) by auto
      qed
    qed

    fix pre_s h k
    assume "(pre_s, h), (pre_s, h) \<Turnstile> Star P ?G"
    then obtain pp gg where "Some h = Some pp \<oplus> Some gg" "(pre_s, pp), (pre_s, pp) \<Turnstile> P" "(pre_s, gg), (pre_s, gg) \<Turnstile> ?G"
      using always_sat_refl hyper_sat.simps(4) by blast
    then have "remove_guards h = pp"
      by (meson assms(10) hyper_sat.simps(12) no_guard_and_no_heap no_guard_assertion_def)
    then have "(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P"
      using \<open>(pre_s, pp), (pre_s, pp) \<Turnstile> P\<close> hyper_sat.simps(9) by blast
    then have "(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P"
      by (simp add: no_guard_remove_guards)

    show "safe k (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))"
    proof (cases k)
      case (Suc n)
      moreover have "safe (Suc n) (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))"
      proof (rule safeSomeAltI)
        show "Catomic C = Cskip \<Longrightarrow> (pre_s, h) \<in> ?\<Sigma>' (pre_s, h)" by simp

        fix H hf hj v0

        assume asm2: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv pre_s hj \<Gamma>"

        define v where "v = f (normalize (get_fh H))"
        define s where "s = pre_s(x := v)"
        then have "v = s x" by simp
        moreover have agreements: "agrees (fvC C \<union> fvA P \<union> fvA Q \<union> fvA J \<union> fvA (SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms)))) s pre_s"          
          by (metis (mono_tags, lifting) Un_iff agrees_def assms(5) assms(8) fun_upd_other fvA.simps(8) s_def)
        then have asm1: "(s, h), (s, h) \<Turnstile> Star P ?G"
\<comment>\<open>~10s\<close>
          by (metis (mono_tags, lifting) \<open>(pre_s, h), (pre_s, h) \<Turnstile> Star P (SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms)))\<close> agrees_same agrees_union fvA.simps(3) fvA.simps(8) sat_comm)
        moreover have asm2_bis: "sat_inv s hj \<Gamma>"
        proof (rule sat_inv_agrees)
          show "sat_inv pre_s hj \<Gamma>" using asm2 by simp
          show "agrees (fvA (invariant \<Gamma>)) pre_s s"
            using assms(1) assms(5) s_def
            by (simp add: agrees_update)
        qed
        moreover have "(s, remove_guards h), (s, remove_guards h) \<Turnstile> P"
          by (meson \<open>(pre_s, remove_guards h), (pre_s, remove_guards h) \<Turnstile> P\<close> agreements agrees_same agrees_union always_sat_refl)
        then have "(s, remove_guards h), (s, remove_guards h) \<Turnstile> P"
          by (simp add: no_guard_remove_guards)

        moreover have "agrees (- {x}) pre_s s"
        proof (rule agreesI)
          fix y assume "y \<in> - {x}"
          then have "y \<noteq> x" 
            by force
          then show "pre_s y = s y"
            by (simp add: s_def)
        qed

        moreover obtain "(s, pp), (s, pp) \<Turnstile> P" "(s, gg), (s, gg) \<Turnstile> ?G"
          using \<open>(pre_s, gg), (pre_s, gg) \<Turnstile> SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms))\<close> \<open>remove_guards h = pp\<close> agreements agrees_same agrees_union always_sat_refl_aux calculation(4) by blast

        let ?hf = "remove_guards hf"
        let ?H = "remove_guards H"
        let ?h = "remove_guards h"
        
        obtain hhj where "Some hhj = Some h \<oplus> Some hj"
          by (metis asm2 plus.simps(2) plus.simps(3) plus_comm)
        then have "Some H = Some hhj \<oplus> Some hf"
          using asm2 by presburger
        then have "Some (remove_guards hhj) = Some ?h \<oplus> Some hj"
          by (metis \<open>Some hhj = Some h \<oplus> Some hj\<close> asm2 no_guards_remove remove_guards_sum sat_inv_def)

        moreover have "f (normalize (get_fh hj)) = v"
        proof -
          have "view \<Gamma> (normalize (get_fh hj)) = view \<Gamma> (normalize (get_fh H))"
            using assms(4) view_function_of_invE
            by (metis (no_types, opaque_lifting) \<open>Some hhj = Some h \<oplus> Some hj\<close> asm2 larger_def larger_trans plus_comm)
          then show ?thesis using assms(1) v_def by fastforce
        qed


        then have "(s, hj), (s, hj) \<Turnstile> ?J"
          by (metis \<open>v = s x\<close> asm2_bis assms(1) hyper_sat.simps(11) sat_inv_def select_convs(5))

        ultimately have "(s, remove_guards hhj), (s, remove_guards hhj) \<Turnstile> Star P ?J"
          using \<open>(s, remove_guards h), (s, remove_guards h) \<Turnstile> P\<close> hyper_sat.simps(4) by blast


        then have all_safes: "\<And>n. safe n (None :: ('i, 'a, nat) cont) C (s, remove_guards hhj) (\<Sigma> (s, remove_guards hhj))"
          using asm0(1) by blast
        then have "\<And>\<sigma>1 H1 \<sigma>2 H2 s2 C2. red_rtrans C \<sigma>1 C2 \<sigma>2 \<Longrightarrow> \<sigma>1 = (s, H1) \<Longrightarrow> \<sigma>2 = (s2, H2) \<Longrightarrow>
          ?H = denormalize H1 \<Longrightarrow>
\<not> aborts C2 \<sigma>2 \<and> (C2 = Cskip \<longrightarrow> (\<exists>h1 H'. Some H' = Some h1 \<oplus> Some ?hf \<and> H2 = FractionalHeap.normalize (get_fh H')
  \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"
        proof -
          fix \<sigma>1 H1 \<sigma>2 H2 s2 C2
          assume "?H = denormalize H1"
          assume "red_rtrans C \<sigma>1 C2 \<sigma>2" "\<sigma>1 = (s, H1)" "\<sigma>2 = (s2, H2)"

          then show "\<not> aborts C2 \<sigma>2 \<and>
       (C2 = Cskip \<longrightarrow>
        (\<exists>h1 H'.
            Some H' = Some h1 \<oplus> Some (remove_guards hf) \<and>
            H2 = FractionalHeap.normalize (get_fh H') \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"
            using all_safes
          proof (rule safe_atomic)
            show "?H = denormalize H1" using \<open>?H = denormalize H1\<close> by simp
            show "Some ?H = Some (remove_guards hhj) \<oplus> Some ?hf"
              using \<open>Some H = Some hhj \<oplus> Some hf\<close> remove_guards_sum by blast
            show "full_ownership (get_fh (remove_guards H)) \<and> no_guard (remove_guards H)"
              by (metis asm2 get_fh_remove_guards no_guard_remove_guards)
          qed
        qed
        moreover have "?H = denormalize (normalize (get_fh H))"
          by (metis asm2 denormalize_properties(5))
        ultimately have safe_atomic_simplified: "\<And>\<sigma>2 H2 s2 C2. red_rtrans C (s, normalize (get_fh H)) C2 \<sigma>2
         \<Longrightarrow> \<sigma>2 = (s2, H2) \<Longrightarrow> \<not> aborts C2 \<sigma>2 \<and> (C2 = Cskip \<longrightarrow> (\<exists>h1 H'. Some H' = Some h1 \<oplus> Some ?hf \<and> H2 = FractionalHeap.normalize (get_fh H')
  \<and> no_guard H' \<and> full_ownership (get_fh H') \<and> (s2, h1) \<in> \<Sigma> (s, remove_guards hhj)))"          
          by presburger

        have "\<not> aborts (Catomic C) (s, normalize (get_fh H))"
        proof (rule ccontr)
          assume "\<not> \<not> aborts (Catomic C) (s, normalize (get_fh H))"
          then obtain C' \<sigma>' where asm3: "red_rtrans C (s, FractionalHeap.normalize (get_fh H)) C' \<sigma>'"
          "aborts C' \<sigma>'"
            using abort_atomic_cases by blast
          then have "\<not> aborts C' \<sigma>'" using safe_atomic_simplified[of C' \<sigma>' "fst \<sigma>'" "snd \<sigma>'"] by simp
          then show False using asm3(2) by simp
        qed
        then show "\<not> aborts (Catomic C) (pre_s, normalize (get_fh H))"
          by (metis agreements aborts_agrees agrees_comm agrees_union fst_eqD fvC.simps(11) snd_conv)

        fix C' pre_s' h'
        assume "red (Catomic C) (pre_s, FractionalHeap.normalize (get_fh H)) C' (pre_s', h')"
        then obtain s' where "red (Catomic C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
          "agrees (- {x}) s' pre_s'"
          by (metis (no_types, lifting) UnI1 \<open>agrees (- {x}) pre_s s\<close> agrees_comm assms(5) fst_eqD fvC.simps(11) red_agrees snd_conv subset_Compl_singleton)

        then obtain h1 H' where asm3: "Some H' = Some h1 \<oplus> Some (remove_guards hf)" "C' = Cskip"
          "h' = FractionalHeap.normalize (get_fh H')" "no_guard H' \<and> full_ownership (get_fh H')" "(s', h1) \<in> \<Sigma> (s, remove_guards hhj)"
          using safe_atomic_simplified[of C' "(s', h')" s' h']  by (metis red_atomic_cases)

        moreover have "s x = s' x \<and> s sarg = s' sarg \<and> s ms = s' ms" using red_not_in_fv_not_touched
          using \<open>red (Catomic C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')\<close>
          by (metis UnI1 assms(5) assms(6) assms(7) fst_eqD fvC.simps(11))

        have "\<exists>hq' hj'. Some h1 = Some hq' \<oplus> Some hj' \<and> (s', add_sguard_to_no_guard hq' \<pi> (?ms s')) \<in> \<Sigma>' (pre_s, h)
        \<and> sat_inv s' hj' \<Gamma> \<and> f (normalize (get_fh hj')) = sact v (map_to_arg (s' sarg))"
        proof -
          have "pair_sat (\<Sigma> (s, remove_guards hhj)) (\<Sigma> (s, remove_guards hhj)) (Star Q ?J')"
            using asm0(2)[of "(s, remove_guards hhj)" "(s, remove_guards hhj)"]
            using \<open>(s, remove_guards hhj), (s, remove_guards hhj) \<Turnstile> Star P ?J\<close> by blast
          then have "(s', h1), (s', h1) \<Turnstile> Star Q ?J'"
            using asm3(5) pair_sat_def by blast
          then obtain hq' hj' where "Some h1 = Some hq' \<oplus> Some hj'" "(s', hq'), (s', hq') \<Turnstile> Q" "(s', hj'), (s', hj') \<Turnstile> ?J'"
            using always_sat_refl hyper_sat.simps(4) by blast
          then have "no_guard hj'"
            by (metis (no_types, opaque_lifting) calculation(1) calculation(4) no_guard_then_smaller_same plus_comm)
          moreover have "f (normalize (get_fh hj')) = sact v (map_to_arg (s' sarg))"
            using \<open>(s', hj'), (s', hj') \<Turnstile> View f J (\<lambda>s. sact (s x) (map_to_arg (s sarg)))\<close> \<open>s x = s' x \<and> s sarg = s' sarg \<and> s ms = s' ms\<close> \<open>v = s x\<close> by fastforce
          moreover have "(s, remove_guards hhj) \<in> start (pre_s, h)"
          proof -
            have "Some (remove_guards hhj) = Some ?h \<oplus> Some hj"
              using \<open>Some (remove_guards hhj) = Some (remove_guards h) \<oplus> Some hj\<close> by blast
            moreover have "(s, hj), (s, hj) \<Turnstile> ?J"
              using \<open>(s, hj), (s, hj) \<Turnstile> ?J\<close> by fastforce
            ultimately show ?thesis using start_def
              using \<open>agrees (- {x}) pre_s s\<close> by fastforce
          qed
          then have "(s', h1) \<in> end_qj (pre_s, h)"
            using \<open>end_qj \<equiv> \<lambda>\<sigma>. \<Union> (\<Sigma> ` start \<sigma>)\<close> asm3(5) by blast

          then have "(s', add_sguard_to_no_guard hq' \<pi> (?ms s')) \<in> \<Sigma>' (pre_s, h)"
            using \<Sigma>'_def \<open>(s', hj'), (s', hj') \<Turnstile> ?J'\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> by blast
          ultimately show "\<exists>hq' hj'.
       Some h1 = Some hq' \<oplus> Some hj' \<and>
       (s', add_sguard_to_no_guard hq' \<pi> ({#map_to_arg (s' sarg)#} + map_to_multiset (s' ms))) \<in> \<Sigma>' (pre_s, h) \<and>
       sat_inv s' hj' \<Gamma> \<and> f (FractionalHeap.normalize (get_fh hj')) = sact v (map_to_arg (s' sarg))"
            using \<open>(s', hj'), (s', hj') \<Turnstile> View f J (\<lambda>s. sact (s x) (map_to_arg (s sarg)))\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> assms(1) sat_inv_def by fastforce
        qed
        then obtain hq' hj' where "Some h1 = Some hq' \<oplus> Some hj'" "(s', add_sguard_to_no_guard hq' \<pi> (?ms s')) \<in> \<Sigma>' (pre_s, h)" "sat_inv s' hj' \<Gamma>"
          "f (FractionalHeap.normalize (get_fh hj')) = sact v (map_to_arg (s' sarg))"
          by blast
        then have "safe n (Some \<Gamma>) C' (s', add_sguard_to_no_guard hq' \<pi> (?ms s')) (\<Sigma>' (pre_s, h))"
          using asm3(2) safe_skip by blast

        moreover have "\<exists>H''. semi_consistent \<Gamma> v0 H'' \<and> Some H'' = Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) \<oplus> Some hj' \<oplus> Some hf"
        proof -
          have "Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) = Some hq' \<oplus> Some (Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None))"
            using \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> add_sguard_as_sum asm3(1) asm3(4) no_guard_then_smaller_same by blast


          obtain hhf where "Some hhf = Some h \<oplus> Some hf"
            by (metis (no_types, opaque_lifting) \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>Some hhj = Some h \<oplus> Some hj\<close> option.exhaust_sel plus.simps(1) plus_asso plus_comm)
          then have "all_guards hhf"
            by (metis (no_types, lifting) all_guards_no_guard_propagates asm2 plus_asso plus_comm sat_inv_def semi_consistent_def)

          moreover have "get_gu h = (\<lambda>_. None) \<and> get_gs h = Some (\<pi>, ?pre_ms s)"
          proof -
            have "no_guard pp"
              using \<open>(pre_s, pp), (pre_s, pp) \<Turnstile> P\<close> assms(10) no_guard_assertion_def by blast
              then show ?thesis
                by (metis \<open>Some h = Some pp \<oplus> Some gg\<close> \<open>\<And>thesis. (\<lbrakk>(s, pp), (s, pp) \<Turnstile> P; (s, gg), (s, gg) \<Turnstile> SharedGuard \<pi> (\<lambda>s. map_to_multiset (s ms))\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>remove_guards h = pp\<close> decompose_heap_triple fst_conv hyper_sat.simps(12) no_guard_remove(2) plus_comm remove_guards_def snd_conv sum_gs_one_none)
            qed
            then have " \<exists>\<pi>' msf uargs. (\<forall>k. get_gu hf k = Some (uargs k)) \<and>
              (\<pi> = pwrite \<and> get_gs hf = None \<and> msf = {#} \<or> pwrite = padd \<pi> \<pi>' \<and> get_gs hf = Some (\<pi>', msf))"
            using all_guards_sum_known_one[of hhf h hf \<pi>]
            using \<open>Some hhf = Some h \<oplus> Some hf\<close> calculation by fastforce

          then obtain \<pi>' uargs msf where "(\<forall>k. get_gu hf k = Some (uargs k)) \<and> ((\<pi> = pwrite \<and> get_gs hf = None \<and> msf = {#}) \<or> (pwrite = padd \<pi> \<pi>' \<and> get_gs hf = Some (\<pi>', msf)))"
            by blast

          then obtain ghf where ghf_def: "Some hf = Some (remove_guards hf) \<oplus> Some ghf"
          "get_fh ghf = Map.empty" "(\<pi> = pwrite \<and> get_gs ghf = None \<and> msf = {#}) \<or> (padd \<pi> \<pi>' = pwrite \<and> get_gs ghf = Some (\<pi>', msf))"
            "\<And>i. get_gu ghf i = Some (uargs i)"
            using decompose_guard_remove_easy[of hf]
            by (metis fst_conv get_fh.elims get_gs.elims get_gu.simps snd_conv)


          have "(Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None)) ## ghf"
          proof (rule compatibleI)
            show "compatible_fract_heaps (get_fh (Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None))) (get_fh ghf)"
              using compatible_fract_heapsI by fastforce
            show "\<And>k. get_gu (Map.empty, Some (\<pi>, {#map_to_arg (s' sarg)#} + map_to_multiset (s' ms)), Map.empty) k = None \<or> get_gu ghf k = None"
              by simp
            fix p p'
            assume "get_gs (Map.empty, Some (\<pi>, {#map_to_arg (s' sarg)#} + map_to_multiset (s' ms)), Map.empty) = Some p \<and> get_gs ghf = Some p'"
            then have "p = (\<pi>, ?ms s') \<and> p' = (\<pi>', msf) \<and> padd \<pi> \<pi>' = pwrite"
              using ghf_def by auto
            then show "pgte pwrite (padd (fst p) (fst p'))"
              using not_pgte_charact pgt_implies_pgte by auto
          qed
          then obtain g where g_def: "Some g = Some (Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None)) \<oplus> Some ghf"
            by simp
          moreover have "H' ## g"
          proof (rule compatibleI)
            have "get_fh g = add_fh Map.empty Map.empty" using add_get_fh[of g "(Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None))" ghf]
                g_def \<open>get_fh ghf = Map.empty\<close>
              by fastforce
            then have "get_fh g = Map.empty"
              using add_fh_map_empty by auto
            then show "compatible_fract_heaps (get_fh H') (get_fh g)"
              using compatible_fract_heapsI by force
            show "\<And>k. get_gu H' k = None \<or> get_gu g k = None"
              by (meson asm3(4) no_guard_def)
            show "\<And>p p'. get_gs H' = Some p \<and> get_gs g = Some p' \<Longrightarrow> pgte pwrite (padd (fst p) (fst p'))"
              by (metis asm3(4) no_guard_def option.simps(3))
          qed
          then obtain H'' where "Some H'' = Some H' \<oplus> Some g"
            by simp
          then have "Some H'' = Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) \<oplus> Some hj' \<oplus> Some hf"
          proof -
            have "Some H'' = Some h1 \<oplus> Some g \<oplus> Some (remove_guards hf)"
              by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> asm3(1) plus_comm simpler_asso)
            moreover have "Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) = Some hq' \<oplus> Some (Map.empty, Some (\<pi>, ?ms s'), (\<lambda>_. None))"
              using \<open>Some (add_sguard_to_no_guard hq' \<pi> ({#map_to_arg (s' sarg)#} + map_to_multiset (s' ms))) = Some hq' \<oplus> Some (Map.empty, Some (\<pi>, {#map_to_arg (s' sarg)#} + map_to_multiset (s' ms)), (\<lambda>_. None))\<close> by blast
            ultimately show ?thesis
              by (metis (no_types, lifting) \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> g_def ghf_def(1) plus_comm simpler_asso)
          qed



          moreover have "semi_consistent \<Gamma> v0 H''"
          proof (rule semi_consistentI)
            have "get_gs g = Some (pwrite, ?ms s' + msf)"
            proof (cases "\<pi> = pwrite")
              case True
              then have "\<pi> = pwrite \<and> get_gs ghf = None \<and> msf = {#}" using ghf_def(3)
                by (metis not_pgte_charact pgt_implies_pgte sum_larger)
              then show ?thesis
                by (metis add.right_neutral fst_conv g_def get_gs.simps snd_conv sum_gs_one_none)
            next
              case False
              then have "padd \<pi> \<pi>' = pwrite \<and> get_gs ghf = Some (\<pi>', msf)"
                using ghf_def(3) by blast
              then show ?thesis
                by (metis calculation(2) fst_conv get_gs.elims snd_conv sum_gs_one_some)
            qed

            moreover have "\<And>i. get_gu g i = Some (uargs i)"
              by (metis full_uguard_sum_same ghf_def(4) g_def plus_comm)
            ultimately have "all_guards g"
              using all_guards_def by blast
            then show "all_guards H''"
              by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> all_guards_same plus_comm)
            show "reachable \<Gamma> v0 H''"
            proof (rule reachableI)
              fix  sargs uargs'
              assume "get_gs H'' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu H'' k = Some (uargs' k))"
              then have "sargs = ?ms s' + msf"
                by (metis (no_types, opaque_lifting) \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>get_gs g = Some (pwrite, {#map_to_arg (s' sarg)#} + map_to_multiset (s' ms) + msf)\<close> asm3(4) no_guard_remove(1) option.inject plus_comm snd_conv)
              moreover have "uargs = uargs'"
                apply (rule ext)
                by (metis \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>\<And>i. get_gu g i = Some (uargs i)\<close> \<open>get_gs H'' = Some (pwrite, sargs) \<and> (\<forall>k. get_gu H'' k = Some (uargs' k))\<close> asm3(4) no_guard_remove(2) option.sel plus_comm)
              moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh hj')) = view \<Gamma> (FractionalHeap.normalize (get_fh H''))"
                using assms(4) \<open>sat_inv s' hj' \<Gamma>\<close>
              proof (rule view_function_of_invE)
                show "H'' \<succeq> hj'"
                  by (metis (no_types, opaque_lifting) \<open>Some H'' = Some H' \<oplus> Some g\<close> \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> asm3(1) larger_def larger_trans plus_comm)
              qed
              moreover have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 (?ms s' + msf) uargs (sact v (map_to_arg (s' sarg)))"
              proof -

                have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 (?pre_ms s + msf) uargs (view \<Gamma> (FractionalHeap.normalize (get_fh H)))"
                proof -
                  have "reachable \<Gamma> v0 H"
                    by (meson asm2 semi_consistent_def)
                  moreover have "get_gs H = Some (pwrite, ?pre_ms s + msf) \<and> (\<forall>k. get_gu H k = Some (uargs k))"
                  proof (rule conjI)
                    show "\<forall>k. get_gu H k = Some (uargs k)"
                      by (metis \<open>Some H = Some hhj \<oplus> Some hf\<close> full_uguard_sum_same ghf_def(1) ghf_def(4) plus_comm)

                    moreover have "get_gs hhj = Some (\<pi>, ?pre_ms s)"
                    proof -
                      have "get_gs hj = None"
                        using asm2 no_guard_def sat_inv_def by blast
                      moreover have "get_gs h = Some (\<pi>, ?pre_ms s)"
                        using \<open>get_gu h = Map.empty \<and> get_gs h = Some (\<pi>, map_to_multiset (s ms))\<close> by blast
                      ultimately show ?thesis
                        by (metis \<open>Some hhj = Some h \<oplus> Some hj\<close> sum_gs_one_none)
                    qed
                    ultimately show "get_gs H = Some (pwrite, ?pre_ms s + msf)"
                    proof (cases "\<pi> = pwrite")
                      case True
                      then have "\<pi> = pwrite \<and> get_gs ghf = None \<and> msf = {#}" using ghf_def(3)
                        by (metis not_pgte_charact pgt_implies_pgte sum_larger)
                      then show ?thesis
                        by (metis \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>get_gs hhj = Some (\<pi>, map_to_multiset (s ms))\<close> add.right_neutral full_sguard_sum_same)
                    next
                      case False
                      then have "padd \<pi> \<pi>' = pwrite \<and> get_gs ghf = Some (\<pi>', msf)"
                        using ghf_def(3) by blast
                      then show ?thesis using \<open>Some H = Some hhj \<oplus> Some hf\<close> sum_gs_one_some ghf_def(1)
                          \<open>get_gs hhj = Some (\<pi>, ?pre_ms s)\<close> asm3(1) asm3(4) no_guard_remove(1)[of hf ghf "remove_guards hf"] no_guard_then_smaller_same plus_comm
                        by metis
                    qed
                  qed
                  ultimately show ?thesis
                    by (meson reachableE)
                qed
                moreover have "view \<Gamma> (FractionalHeap.normalize (get_fh hj)) = view \<Gamma> (FractionalHeap.normalize (get_fh H))"
                  using assms(4)
                proof (rule view_function_of_invE)
                  show "sat_inv s hj \<Gamma>"
                    by (simp add: asm2_bis)
                  show "H \<succeq> hj"
                    by (metis (no_types, opaque_lifting) \<open>Some H = Some hhj \<oplus> Some hf\<close> \<open>Some hhj = Some h \<oplus> Some hj\<close> larger_def larger_trans plus_comm)
                qed
                ultimately have "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 (?pre_ms s + msf) uargs v"
                  using \<open>f (FractionalHeap.normalize (get_fh hj)) = v\<close> assms(1) by auto
                then show ?thesis
                  using SharedStep assms(1)
                  using \<open>s x = s' x \<and> s sarg = s' sarg \<and> s ms = s' ms\<close> by fastforce
              qed
              ultimately show "reachable_value (saction \<Gamma>) (uaction \<Gamma>) v0 sargs uargs' (view \<Gamma> (FractionalHeap.normalize (get_fh H'')))"
                using \<open>f (FractionalHeap.normalize (get_fh hj')) = sact v (map_to_arg (s' sarg))\<close> assms(1) by force
            qed
          qed
          ultimately show "\<exists>H''. semi_consistent \<Gamma> v0 H'' \<and> Some H'' = Some (add_sguard_to_no_guard hq' \<pi> ({#map_to_arg (s' sarg)#} + map_to_multiset (s' ms))) \<oplus> Some hj' \<oplus> Some hf"
            by blast
        qed
        ultimately obtain H'' where "semi_consistent \<Gamma> v0 H'' \<and> Some H'' = Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) \<oplus> Some hj' \<oplus> Some hf
          \<and> safe n (Some \<Gamma>) C' (s', add_sguard_to_no_guard hq' \<pi> (?ms s')) (\<Sigma>' (pre_s, h))" by blast
        moreover have "full_ownership (get_fh H'') \<and> h' = FractionalHeap.normalize (get_fh H'')"
        proof -
          obtain x where "Some x = Some (add_sguard_to_no_guard hq' \<pi> (?ms s')) \<oplus> Some hj'"
            by (metis calculation not_Some_eq plus.simps(1))
          then have "get_fh H'' = add_fh (add_fh (get_fh (add_sguard_to_no_guard hq' \<pi> (?ms s'))) (get_fh hj')) (get_fh hf)"
            by (metis add_get_fh calculation)
          moreover have "get_fh (add_sguard_to_no_guard hq' \<pi> (?ms s')) = get_fh hq' \<and> get_fh hf = get_fh (remove_guards hf)"
            by (metis get_fh_add_sguard get_fh_remove_guards)
          ultimately show ?thesis
            by (metis \<open>Some h1 = Some hq' \<oplus> Some hj'\<close> add_get_fh asm3(1) asm3(3) asm3(4))
        qed
        moreover have "sat_inv pre_s' hj' \<Gamma>"
        proof (rule sat_inv_agrees)
          show "sat_inv s' hj' \<Gamma>"
            by (simp add: \<open>sat_inv s' hj' \<Gamma>\<close>)
          show "agrees (fvA (invariant \<Gamma>)) s' pre_s'"
            using UnCI \<open>agrees (- {x}) s' pre_s'\<close> assms(1) assms(5) select_convs(5) subset_Compl_singleton
            by (metis (mono_tags, lifting) agrees_def in_mono)
        qed
        moreover have "safe n (Some \<Gamma>) C' (pre_s', add_sguard_to_no_guard hq' \<pi> (?ms s')) (?\<Sigma>' (pre_s, h))"
        proof (rule safe_free_vars_Some)
          show "safe n (Some \<Gamma>) C' (s', add_sguard_to_no_guard hq' \<pi> (?ms s')) (?\<Sigma>' (pre_s, h))"
            by (meson \<open>safe n (Some \<Gamma>) C' (s', add_sguard_to_no_guard hq' \<pi> ({#map_to_arg (s' sarg)#} + map_to_multiset (s' ms))) (\<Sigma>' (pre_s, h))\<close> close_var_subset safe_larger_set)
          show "agrees (fvC C' \<union> (- {x}) \<union> fvA (invariant \<Gamma>)) s' pre_s'"
            by (metis UnI2 Un_absorb1 \<open>agrees (- {x}) s' pre_s'\<close> asm3(2) assms(1) assms(5) empty_iff fvC.simps(1) inf_sup_aci(5) select_convs(5) subset_Compl_singleton)
          show "upper_fvs (close_var (\<Sigma>' (pre_s, h)) x) (- {x})"
            by (simp add: upper_fvs_close_vars)
        qed
        ultimately show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv pre_s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf
          \<and> safe n (Some \<Gamma>) C' (pre_s', h'') (?\<Sigma>' (pre_s, h))" using \<open>sat_inv s' hj' \<Gamma>\<close> by blast
      qed
      ultimately show "safe k (Some \<Gamma>) (Catomic C) (pre_s, h) (?\<Sigma>' (pre_s, h))" by blast
    qed (simp)
  qed
qed


subsubsection \<open>Parallel\<close>

lemma par_cases:
  assumes "red (Cpar C1 C2) \<sigma> C' \<sigma>'"
  and "\<And>C1'. C' = Cpar C1' C2 \<and> red C1 \<sigma> C1' \<sigma>' \<Longrightarrow> P"
  and "\<And>C2'. C' = Cpar C1 C2' \<and> red C2 \<sigma> C2' \<sigma>' \<Longrightarrow> P"
  and "C1 = Cskip \<and> C2 = Cskip \<and> C' = Cskip \<and> \<sigma> = \<sigma>' \<Longrightarrow> P"
  shows P
  using assms(1)
  apply (rule red.cases)
  apply blast+
  apply (simp add: assms(2))
  apply (simp add: assms(3))
  apply (simp add: assms(4))
  apply blast+
  done

lemma no_abort_par:
  assumes "no_abort \<Gamma> C1 s h"
      and "no_abort \<Gamma> C2 s h"
    shows "no_abort \<Gamma> (Cpar C1 C2) s h"
proof (rule no_abortI)
  show "\<And>hf H.
       Some H = Some h \<oplus> Some hf \<and> \<Gamma> = None \<and> full_ownership (get_fh H) \<and> no_guard H \<Longrightarrow>
       \<not> aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))"
  proof -
    fix hf H assume asm0: "Some H = Some h \<oplus> Some hf \<and> \<Gamma> = None \<and> full_ownership (get_fh H) \<and> no_guard H"
    let ?H = "FractionalHeap.normalize (get_fh H)"
    show "\<not> aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))"
    proof (rule ccontr)
      assume "\<not> \<not> aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))"
      then have "aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))" by simp
      then have "aborts C1 (s, ?H) \<or> aborts C2 (s, ?H)"
        by (rule aborts.cases) auto
      then show False
        using asm0 assms(1) assms(2) no_abortE(1) by blast
    qed
  qed
  fix H hf hj v0 \<Gamma>'
  assume asm0: "\<Gamma> = Some \<Gamma>' \<and> Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma>' v0 H \<and> sat_inv s hj \<Gamma>'"
  let ?H = "FractionalHeap.normalize (get_fh H)"
  show "\<not> aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))"
  proof (rule ccontr)
    assume "\<not> \<not> aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))"
    then have "aborts (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H))" by simp
    then have "aborts C1 (s, ?H) \<or> aborts C2 (s, ?H)"
      by (rule aborts.cases) auto
    then show False
      using asm0 assms(1) assms(2) no_abortE(2) by blast
  qed
qed

lemma parallel_comp_none:
  assumes "safe n (None :: ('i, 'a, nat) cont) C1 (s, h1) S1"
      and "safe n (None :: ('i, 'a, nat) cont) C2 (s, h2) S2"
      and "Some h = Some h1 \<oplus> Some h2"

      and "disjoint (fvC C1 \<union> vars1) (wrC C2)"
      and "disjoint (fvC C2 \<union> vars2) (wrC C1)"

      and "upper_fvs S1 vars1"
      and "upper_fvs S2 vars2"

    shows "safe n (None :: ('i, 'a, nat) cont) (Cpar C1 C2) (s, h) (add_states S1 S2)"
  using assms
proof (induct n arbitrary: C1 h1 C2 h2 s h S1 S2)
  case (Suc n)  
  show ?case
  proof (rule safeNoneI)
    show "Cpar C1 C2 = Cskip \<Longrightarrow> (s, h) \<in> add_states S1 S2"
      by simp
    show "no_abort (None :: ('i, 'a, nat) cont) (Cpar C1 C2) s h"
    proof (rule no_abort_par)
      show "no_abort (None :: ('i, 'a, nat) cont) C1 s h"
        using Suc.prems(1) Suc.prems(3) larger_def no_abort_larger safe.simps(2) by blast
      have "h \<succeq> h2"
        by (metis Suc.prems(3) larger_def plus_comm)
      then show "no_abort (None :: ('i, 'a, nat) cont) C2 s h"
        using Suc.prems(2) no_abort_larger safeNoneE_bis(2) by blast
    qed
    fix H hf C' s' h'
    assume asm0: "Some H = Some h \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> no_guard H \<and> red (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"


    obtain hf1 where "Some hf1 = Some h1 \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asm0 plus.simps(1) plus.simps(3) plus_asso plus_comm)
    then have "Some H = Some h2 \<oplus> Some hf1"
      by (metis (no_types, lifting) Suc.prems(3) asm0 plus_asso plus_comm)
    obtain hf2 where "Some hf2 = Some h2 \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) \<open>Some H = Some h2 \<oplus> Some hf1\<close> \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> option.exhaust_sel plus.simps(1) plus_asso plus_comm)
    then have "Some H = Some h1 \<oplus> Some hf2"
      by (metis Suc.prems(3) asm0 plus_asso)

    let ?H = "normalize (get_fh H)"

    show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
    proof (rule par_cases)
      show "red (Cpar C1 C2) (s, ?H) C' (s', h')"
        using asm0 by blast

      show "C1 = Cskip \<and> C2 = Cskip \<and> C' = Cskip \<and> (s, FractionalHeap.normalize (get_fh H)) = (s', h') \<Longrightarrow>
      \<exists>h'' H'. full_ownership (get_fh H') \<and>
       no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
      proof -
        assume asm1: "C1 = Cskip \<and> C2 = Cskip \<and> C' = Cskip \<and> (s, FractionalHeap.normalize (get_fh H)) = (s', h')"
        then have "(s, h1) \<in> S1 \<and> (s, h2) \<in> S2"
          using Suc.prems(1) Suc.prems(2) safe.simps(2) by blast
        moreover have "(s, h) \<in> add_states S1 S2"
          by (metis (mono_tags, lifting) Suc.prems(3) add_states_def calculation mem_Collect_eq)
        ultimately show "\<exists>h'' H'.
       full_ownership (get_fh H') \<and>
       no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
          by (metis asm0 asm1 old.prod.inject safe_skip)
      qed

      show "\<And>C1'. C' = Cpar C1' C2 \<and> red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h') \<Longrightarrow>
           \<exists>h'' H'.
              full_ownership (get_fh H') \<and>
              no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
      proof -
        fix C1'
        assume asm1: "C' = Cpar C1' C2 \<and> red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')"
        then obtain h1' H' where asm2: "full_ownership (get_fh H')" "no_guard H'" "h' = FractionalHeap.normalize (get_fh H')"
          "Some H' = Some h1' \<oplus> Some hf2" "safe n (None :: ('i, 'a, nat) cont) C1' (s', h1') S1"
          using Suc.prems(1) asm0 safeNoneE(3)[of n C1 s h1 S1 H hf2 C1' s' h'] \<open>Some H = Some h1 \<oplus> Some hf2\<close> by blast

        moreover have "safe n (None :: ('i, 'a, nat) cont) C2 (s, h2) S2"
          by (meson Suc.prems(2) Suc_leD le_Suc_eq safe_smaller)

        then have "safe n (None :: ('i, 'a, nat) cont) C2 (s', h2) S2"
        proof (rule safe_free_vars_None)
          show "agrees (fvC C2 \<union> vars2) s s'"
            using Suc.prems(5) agrees_minusD[of ] agrees_comm asm1 fst_eqD red_properties(1) disjoint_def inf_commute 
            by metis
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
        qed

        moreover obtain h'' where "Some h'' = Some h1' \<oplus> Some h2"
          by (metis \<open>Some hf2 = Some h2 \<oplus> Some hf\<close> calculation(4) not_Some_eq plus.simps(1) plus_asso)
        have "safe n (None :: ('i, 'a, nat) cont) (Cpar C1' C2) (s', h'') (add_states S1 S2)"
        proof (rule Suc.hyps)
          show "safe n (None :: ('i, 'a, nat) cont) C1' (s', h1') S1"
            using calculation(5) by blast
          show "safe n (None :: ('i, 'a, nat) cont) C2 (s', h2) S2"
            using calculation(6) by auto
          show "Some h'' = Some h1' \<oplus> Some h2"
            using \<open>Some h'' = Some h1' \<oplus> Some h2\<close> by blast
          show "disjoint (fvC C1' \<union> vars1) (wrC C2)"
            using Suc.prems(4) asm1 red_properties(1) Un_iff disjoint_def[of "fvC C1 \<union> vars1" "wrC C2"]
              disjoint_def[of "fvC C1' \<union> vars1" "wrC C2"]
              inf_shunt subset_iff by blast
          show "disjoint (fvC C2 \<union> vars2) (wrC C1')"
            by (metis (no_types, lifting) Suc.prems(5) asm1 disjoint_def inf_commute inf_shunt red_properties(1) subset_Un_eq sup_assoc)
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
        qed

        ultimately show "\<exists>h'' H'.
              full_ownership (get_fh H') \<and>
              no_guard H' \<and>
              h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
          by (metis \<open>Some h'' = Some h1' \<oplus> Some h2\<close> \<open>Some hf2 = Some h2 \<oplus> Some hf\<close> asm1 plus_asso)
      qed
      show "\<And>C2'. C' = Cpar C1 C2' \<and> red C2 (s, FractionalHeap.normalize (get_fh H)) C2' (s', h') \<Longrightarrow>
           \<exists>h'' H'.
              full_ownership (get_fh H') \<and>
              no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
      proof -
        fix C2'
        assume asm1: "C' = Cpar C1 C2' \<and> red C2 (s, FractionalHeap.normalize (get_fh H)) C2' (s', h')"
        then obtain h2' H' where asm2: "full_ownership (get_fh H')" "no_guard H'" "h' = FractionalHeap.normalize (get_fh H')"
          "Some H' = Some h2' \<oplus> Some hf1" "safe n (None :: ('i, 'a, nat) cont) C2' (s', h2') S2"
          using Suc.prems(1) asm0 safeNoneE(3) Suc.prems(2) \<open>Some H = Some h2 \<oplus> Some hf1\<close> by blast

        moreover have "safe n (None :: ('i, 'a, nat) cont) C1 (s, h1) S1"
          by (meson Suc.prems(1) Suc_leD le_Suc_eq safe_smaller)

        then have "safe n (None :: ('i, 'a, nat) cont) C1 (s', h1) S1"
        proof (rule safe_free_vars_None)
          show "agrees (fvC C1 \<union> vars1) s s'"
            using Suc.prems(4) agrees_comm asm1 fst_eqD red_properties(1) disjoint_def[of "fvC C1 \<union> vars1" "wrC C2"]
              agrees_minusD by (metis inf_commute)
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
        qed

        moreover obtain h'' where "Some h'' = Some h2' \<oplus> Some h1"
          by (metis \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> calculation(4) not_Some_eq plus.simps(1) plus_asso)
        have "safe n (None :: ('i, 'a, nat) cont) (Cpar C1 C2') (s', h'') (add_states S1 S2)"
        proof (rule Suc.hyps)
          show "safe n (None :: ('i, 'a, nat) cont) C1 (s', h1) S1"
            using calculation(6) by blast
          show "safe n (None :: ('i, 'a, nat) cont) C2' (s', h2') S2"
            using calculation(5) by auto
          show "Some h'' = Some h1 \<oplus> Some h2'"
            by (simp add: \<open>Some h'' = Some h2' \<oplus> Some h1\<close> plus_comm)
          show "disjoint (fvC C2' \<union> vars2) (wrC C1)"
            using Suc.prems(5) asm1 disjoint_def[of "fvC C2 \<union> vars2" "wrC C1"] disjoint_def[of "fvC C2' \<union> vars2" "wrC C1"]
              inf_shunt inf_sup_aci(5) red_properties(1) subset_Un_eq sup.idem sup_assoc
            by fast
          show "disjoint (fvC C1 \<union> vars1) (wrC C2')"
            by (metis (no_types, lifting) Suc.prems(4) asm1 disjoint_def inf_commute inf_shunt red_properties(1) subset_Un_eq sup_assoc)
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
        qed

        ultimately show "\<exists>h'' H'.
              full_ownership (get_fh H') \<and>
              no_guard H' \<and>
              h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S1 S2)"
          by (metis \<open>Some h'' = Some h2' \<oplus> Some h1\<close> \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> asm1 plus_asso)
      qed
    qed
  qed
qed (simp)

lemma parallel_comp_some:
  assumes "safe n (Some \<Gamma>) C1 (s, h1) S1"
      and "safe n (Some \<Gamma>) C2 (s, h2) S2"
      and "Some h = Some h1 \<oplus> Some h2"

      and "disjoint (fvC C1 \<union> vars1) (wrC C2)"
      and "disjoint (fvC C2 \<union> vars2) (wrC C1)"

      and "upper_fvs S1 vars1"
      and "upper_fvs S2 vars2"

      and "disjoint (fvA (invariant \<Gamma>)) (wrC C2)"
      and "disjoint (fvA (invariant \<Gamma>)) (wrC C1)"

  shows "safe n (Some \<Gamma>) (Cpar C1 C2) (s, h) (add_states S1 S2)"
  using assms
proof (induct n arbitrary: C1 h1 C2 h2 s h S1 S2)
  case (Suc n)  
  show ?case
  proof (rule safeSomeI)
    show "Cpar C1 C2 = Cskip \<Longrightarrow> (s, h) \<in> add_states S1 S2"
      by simp
    show "no_abort (Some \<Gamma>) (Cpar C1 C2) s h"
    proof (rule no_abort_par)
      show "no_abort (Some \<Gamma>) C1 s h"
        using Suc.prems(1) Suc.prems(3) larger_def no_abort_larger safe.simps(3) by blast
      have "h \<succeq> h2"
        by (metis Suc.prems(3) larger_def plus_comm)
      then show "no_abort (Some \<Gamma>) C2 s h"
        using Suc.prems(2) no_abort_larger safeSomeE(2) by blast
    qed
    fix H hf C' s' h' hj v0
    assume asm0: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and>
       semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cpar C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"


    obtain hf1 where "Some hf1 = Some h1 \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) Suc.prems(3) asm0 plus.simps(1) plus.simps(3) plus_asso plus_comm)
    then have "Some H = Some h2 \<oplus> Some hf1 \<oplus> Some hj"
      by (metis (no_types, lifting) Suc.prems(3) asm0 plus_asso plus_comm)
    then have "Some H = Some h2 \<oplus> Some hj \<oplus> Some hf1"
      by (metis plus_asso plus_comm)
    obtain hf2 where "Some hf2 = Some h2 \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) \<open>Some H = Some h2 \<oplus> Some hf1 \<oplus> Some hj\<close> \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> not_Some_eq plus.simps(1) plus_asso plus_comm)
    then have "Some H = Some h1 \<oplus> Some hf2 \<oplus> Some hj"
      by (metis (no_types, opaque_lifting) \<open>Some H = Some h2 \<oplus> Some hf1 \<oplus> Some hj\<close> \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> plus_asso plus_comm)
    then have "Some H = Some h1 \<oplus> Some hj \<oplus> Some hf2"
      by (metis plus_asso plus_comm)

    let ?H = "normalize (get_fh H)"

    show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s' hj' \<Gamma> \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
    proof (rule par_cases)
      show "red (Cpar C1 C2) (s, ?H) C' (s', h')"
        using asm0 by blast

      show "C1 = Cskip \<and> C2 = Cskip \<and> C' = Cskip \<and> (s, FractionalHeap.normalize (get_fh H)) = (s', h') \<Longrightarrow>
    \<exists>h'' H' hj'. full_ownership (get_fh H') \<and>
       semi_consistent \<Gamma> v0 H' \<and>
       sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
      proof -
        assume asm1: "C1 = Cskip \<and> C2 = Cskip \<and> C' = Cskip \<and> (s, FractionalHeap.normalize (get_fh H)) = (s', h')"
        then have "(s, h1) \<in> S1 \<and> (s, h2) \<in> S2"
          using Suc.prems(1) Suc.prems(2) safe.simps(3) by blast
        moreover have "(s, h) \<in> add_states S1 S2"
          by (metis (mono_tags, lifting) Suc.prems(3) add_states_def calculation mem_Collect_eq)
        ultimately show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and>
       semi_consistent \<Gamma> v0 H' \<and>
       sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
          by (metis asm0 asm1 old.prod.inject safe_skip)
      qed

      show "\<And>C1'. C' = Cpar C1' C2 \<and> red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h') \<Longrightarrow>
           \<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and>
              sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
      proof -
        fix C1'
        assume asm1: "C' = Cpar C1' C2 \<and> red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')"
        then obtain h1' H' hj' where asm2: "full_ownership (get_fh H')" "h' = FractionalHeap.normalize (get_fh H')"
          "semi_consistent \<Gamma> v0 H'" "sat_inv s' hj' \<Gamma>" "Some H' = Some h1' \<oplus> Some hj' \<oplus> Some hf2" "safe n (Some \<Gamma>) C1' (s', h1') S1"
          using safeSomeE(3)[of n \<Gamma> C1 s h1 S1 H hj hf2 v0 C1' s' h'] Suc.prems(1) asm0
          using \<open>Some H = Some h1 \<oplus> Some hj \<oplus> Some hf2\<close> by blast

        moreover have "safe n (Some \<Gamma>) C2 (s, h2) S2"
          by (meson Suc.prems(2) Suc_leD le_Suc_eq safe_smaller)

        then have "safe n (Some \<Gamma>) C2 (s', h2) S2"
        proof (rule safe_free_vars_Some)
          show "agrees (fvC C2 \<union> vars2 \<union> fvA (invariant \<Gamma>)) s s'"
            using Suc.prems(5) Suc.prems(9) agrees_minusD agrees_comm asm1 disjoint_def fst_eqD red_properties(1)
            by (metis agrees_union inf_commute)
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
        qed

        moreover have "h1' ## h2"
          by (metis (no_types, opaque_lifting) \<open>Some hf2 = Some h2 \<oplus> Some hf\<close> calculation(5) compatible_eq option.discI plus.simps(1) plus_asso plus_comm)
        then obtain h'' where "Some h'' = Some h1' \<oplus> Some h2" by simp

        have "safe n (Some \<Gamma>) (Cpar C1' C2) (s', h'') (add_states S1 S2)"
        proof (rule Suc.hyps)
          show "safe n (Some \<Gamma>) C1' (s', h1') S1"
            using calculation(6) by blast
          show "safe n (Some \<Gamma>) C2 (s', h2) S2"
            using calculation(7) by auto
          show "Some h'' = Some h1' \<oplus> Some h2"
            using \<open>Some h'' = Some h1' \<oplus> Some h2\<close> by blast
          show "disjoint (fvC C1' \<union> vars1) (wrC C2)"
            by (metis (no_types, opaque_lifting) Suc.prems(4) asm1 disjnt_Un1 disjnt_def disjoint_def red_properties(1) sup.orderE)
          show "disjoint (fvC C2 \<union> vars2) (wrC C1')"
            by (metis (no_types, lifting) Suc.prems(5) asm1 disjoint_def inf_commute inf_shunt red_properties(1) subset_Un_eq sup_assoc)
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
          show "disjoint (fvA (invariant \<Gamma>)) (wrC C2)"
            by (simp add: Suc.prems(8))
          show "disjoint (fvA (invariant \<Gamma>)) (wrC C1')"
            by (metis (no_types, lifting) Suc.prems(9) asm1 disjoint_def inf_commute inf_shunt red_properties(1) subset_Un_eq sup_assoc)
        qed
        moreover have "Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf"
          by (metis (no_types, opaque_lifting) \<open>Some h'' = Some h1' \<oplus> Some h2\<close> \<open>Some hf2 = Some h2 \<oplus> Some hf\<close> calculation(5) plus_asso plus_comm)


        ultimately show "\<exists>h'' H' hj'.
              full_ownership (get_fh H') \<and>
              semi_consistent \<Gamma> v0 H' \<and>
              sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
          using asm1 by blast

      qed

      show "\<And>C2'. C' = Cpar C1 C2' \<and> red C2 (s, FractionalHeap.normalize (get_fh H)) C2' (s', h') \<Longrightarrow>
           \<exists>h'' H' hj'.
              full_ownership (get_fh H') \<and>
              semi_consistent \<Gamma> v0 H' \<and>
              sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
      proof -
        fix C2'
        assume asm1: "C' = Cpar C1 C2' \<and> red C2 (s, FractionalHeap.normalize (get_fh H)) C2' (s', h')"
        then obtain h2' H' hj' where asm2: "full_ownership (get_fh H')" "h' = FractionalHeap.normalize (get_fh H')"
          "semi_consistent \<Gamma> v0 H'" "sat_inv s' hj' \<Gamma>" "Some H' = Some h2' \<oplus> Some hj' \<oplus> Some hf1" "safe n (Some \<Gamma>) C2' (s', h2') S2"
          using safeSomeE(3)[of n \<Gamma> C2 s h2 S2 H hj hf1 v0 C2' s' h'] Suc.prems(2) Suc.prems(3)
          using \<open>Some H = Some h2 \<oplus> Some hj \<oplus> Some hf1\<close> asm0 by blast
        moreover have "safe n (Some \<Gamma>) C1 (s, h1) S1"
          by (meson Suc.prems(1) Suc_leD le_Suc_eq safe_smaller)

        then have "safe n (Some \<Gamma>) C1 (s', h1) S1"
        proof (rule safe_free_vars_Some)
          show "agrees (fvC C1 \<union> vars1 \<union> fvA (invariant \<Gamma>)) s s'"
            using Suc.prems(4) Suc.prems(8) agrees_minusD agrees_comm asm1 fst_eqD red_properties(1)
            by (metis agrees_union disjoint_def inf_commute)
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
        qed

        moreover have "h1 ## h2'"
          by (metis (no_types, opaque_lifting) \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> calculation(5) compatible_eq option.distinct(1) plus.simps(1) plus_asso plus_comm)
        then obtain h'' where "Some h'' = Some h1 \<oplus> Some h2'" by simp

        have "safe n (Some \<Gamma>) (Cpar C1 C2') (s', h'') (add_states S1 S2)"
        proof (rule Suc.hyps)
          show "safe n (Some \<Gamma>) C1 (s', h1) S1"
            using calculation(7) by blast
          show "safe n (Some \<Gamma>) C2' (s', h2') S2"
            using calculation(6) by auto
          show "Some h'' = Some h1 \<oplus> Some h2'"
            using \<open>Some h'' = Some h1 \<oplus> Some h2'\<close> by blast
          show "disjoint (fvC C1 \<union> vars1) (wrC C2')"
            by (metis (no_types, lifting) Suc.prems(4) asm1 disjoint_def inf_commute inf_shunt red_properties(1) subset_Un_eq sup_assoc)
          show "disjoint (fvC C2' \<union> vars2) (wrC C1)"
            using Suc.prems(5) asm1 red_properties(1)
            by (metis (no_types, lifting) Un_subset_iff disjoint_def inf_shunt subset_Un_eq)
          show "disjoint (fvA (invariant \<Gamma>)) (wrC C2')"
            using Suc.prems(8) asm1 red_properties(1)
            by (metis (no_types, lifting) Un_subset_iff disjoint_def inf_commute inf_shunt subset_Un_eq)
          show "disjoint (fvA (invariant \<Gamma>)) (wrC C1)"
            by (simp add: Suc.prems(9))
          show "upper_fvs S1 vars1"
            by (simp add: Suc.prems(6))
          show "upper_fvs S2 vars2"
            by (simp add: Suc.prems(7))
        qed
        moreover have "Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf"
          by (metis \<open>Some h'' = Some h1 \<oplus> Some h2'\<close> \<open>Some hf1 = Some h1 \<oplus> Some hf\<close> calculation(5) plus_comm simpler_asso)
        ultimately show "\<exists>h'' H' hj'.
              full_ownership (get_fh H') \<and>
              semi_consistent \<Gamma> v0 H' \<and>
              sat_inv s' hj' \<Gamma> \<and>
              h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S1 S2)"
          using asm1 by blast
      qed
    qed
  qed
qed (simp)


lemma parallel_comp:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C1 (s, h1) S1"
      and "safe n \<Delta> C2 (s, h2) S2"
      and "Some h = Some h1 \<oplus> Some h2"
      and "disjoint (fvC C1 \<union> vars1) (wrC C2)"
      and "disjoint (fvC C2 \<union> vars2) (wrC C1)"
      and "upper_fvs S1 vars1"
      and "upper_fvs S2 vars2"

      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C2)"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C1)"

  shows "safe n \<Delta> (Cpar C1 C2) (s, h) (add_states S1 S2)"
proof (cases \<Delta>)
  case None
  then show ?thesis
    using assms parallel_comp_none by blast
next
  case (Some \<Gamma>)
  then show ?thesis
    using assms parallel_comp_some by blast
qed


theorem rule_par:
  fixes \<Delta> :: "('i, 'a, nat) cont"

  assumes "hoare_triple_valid \<Delta> P1 C1 Q1"
      and "hoare_triple_valid \<Delta> P2 C2 Q2"
      and "disjoint (fvA P1 \<union> fvC C1 \<union> fvA Q1) (wrC C2)"
      and "disjoint (fvA P2 \<union> fvC C2 \<union> fvA Q2) (wrC C1)"

      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C2)"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C1)"

      and "precise P1 \<or> precise P2"

    shows "hoare_triple_valid \<Delta> (Star P1 P2) (Cpar C1 C2) (Star Q1 Q2)"
proof -
  obtain \<Sigma>1 where r1: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P1 \<Longrightarrow> safe n \<Delta> C1 \<sigma> (\<Sigma>1 \<sigma>)" "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P1 \<Longrightarrow> pair_sat (\<Sigma>1 \<sigma>) (\<Sigma>1 \<sigma>') Q1"
    using assms(1) hoare_triple_validE by blast
  obtain \<Sigma>2 where r2: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P2 \<Longrightarrow> safe n \<Delta> C2 \<sigma> (\<Sigma>2 \<sigma>)" "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P2 \<Longrightarrow> pair_sat (\<Sigma>2 \<sigma>) (\<Sigma>2 \<sigma>') Q2"
    using assms(2) hoare_triple_validE by blast

  define pairs where "pairs = (\<lambda>(s, h). { ((s, h1), (s, h2)) |h1 h2. Some h = Some h1 \<oplus> Some h2 \<and> (s, h1), (s, h1) \<Turnstile> P1 \<and> (s, h2), (s, h2) \<Turnstile> P2 })"
  define \<Sigma> where "\<Sigma> = (\<lambda>\<sigma>. \<Union>(\<sigma>1, \<sigma>2) \<in> pairs \<sigma>. add_states (upperize (\<Sigma>1 \<sigma>1) (fvA Q1)) (upperize (\<Sigma>2 \<sigma>2) (fvA Q2)))"


  show ?thesis
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> Star P1 P2 \<Longrightarrow> safe n \<Delta> (Cpar C1 C2) (s, h) (\<Sigma> (s, h))"
    proof -
      fix s h n assume "(s, h), (s, h) \<Turnstile> Star P1 P2"
      then obtain h1 h2 where asm0: "Some h = Some h1 \<oplus> Some h2" "(s, h1), (s, h1) \<Turnstile> P1"
        "(s, h2), (s, h2) \<Turnstile> P2"
        using always_sat_refl hyper_sat.simps(4) by blast
      then have "((s, h1), (s, h2)) \<in> pairs (s, h)"
        using pairs_def by blast
      then have "add_states (upperize (\<Sigma>1 (s, h1)) (fvA Q1)) (upperize (\<Sigma>2 (s, h2)) (fvA Q2)) \<subseteq> \<Sigma> (s, h)"
        using \<Sigma>_def by blast
      moreover have "safe n \<Delta> (Cpar C1 C2) (s, h) (add_states (upperize (\<Sigma>1 (s, h1)) (fvA Q1)) (upperize (\<Sigma>2 (s, h2)) (fvA Q2)))"
      proof (rule parallel_comp)
        show "safe n \<Delta> C1 (s, h1) (upperize (\<Sigma>1 (s, h1)) (fvA Q1))"
          by (meson asm0(2) r1(1) safe_larger_set upperize_larger)
        show "safe n \<Delta> C2 (s, h2) (upperize (\<Sigma>2 (s, h2)) (fvA Q2))"
          by (meson asm0(3) r2(1) safe_larger_set upperize_larger)
        show "Some h = Some h1 \<oplus> Some h2" using asm0 by simp
        show "disjoint (fvC C1 \<union> fvA Q1) (wrC C2)"
          by (metis Un_subset_iff assms(3) disjoint_def inf_shunt)
        show "disjoint (fvC C2 \<union> fvA Q2) (wrC C1)"
          by (metis Un_subset_iff assms(4) disjoint_def inf_shunt)
        show "upper_fvs (upperize (\<Sigma>1 (s, h1)) (fvA Q1)) (fvA Q1)"
          by (simp add: upper_fvs_upperize)
        show "upper_fvs (upperize (\<Sigma>2 (s, h2)) (fvA Q2)) (fvA Q2)"
          using upper_fvs_upperize by auto
        show "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C2)"
          using assms(5) by auto
        show "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> disjoint (fvA (invariant \<Gamma>)) (wrC C1)"
          using assms(6) by blast
      qed
      ultimately show "safe n \<Delta> (Cpar C1 C2) (s, h) (\<Sigma> (s, h))"
        using safe_larger_set by blast
    qed

    fix s h s' h'
    assume "(s, h), (s', h') \<Turnstile> Star P1 P2"
    then obtain h1 h2 h1' h2' where asm0: "Some h = Some h1 \<oplus> Some h2" "Some h' = Some h1' \<oplus> Some h2'"
      "(s, h1), (s', h1') \<Turnstile> P1" "(s, h2), (s', h2') \<Turnstile> P2"
      by auto

    show "pair_sat (\<Sigma> (s, h)) (\<Sigma> (s', h')) (Star Q1 Q2)"
    proof (rule pair_satI)
      fix ss hh ss' hh' assume asm1: "(ss, hh) \<in> \<Sigma> (s, h) \<and> (ss', hh') \<in> \<Sigma> (s', h')"

      then obtain \<sigma>1 \<sigma>2 \<sigma>1' \<sigma>2' where "(\<sigma>1, \<sigma>2) \<in> pairs (s, h)" "(\<sigma>1', \<sigma>2') \<in> pairs (s', h')"
        "(ss, hh) \<in> add_states (upperize (\<Sigma>1 \<sigma>1) (fvA Q1)) (upperize (\<Sigma>2 \<sigma>2) (fvA Q2))"
        "(ss', hh') \<in> add_states (upperize (\<Sigma>1 \<sigma>1') (fvA Q1)) (upperize (\<Sigma>2 \<sigma>2') (fvA Q2))"
        using \<Sigma>_def by blast
      then obtain "fst \<sigma>1 = s" "fst \<sigma>2 = s" "fst \<sigma>1' = s'" "fst \<sigma>2' = s'" "Some h = Some (snd \<sigma>1) \<oplus> Some (snd \<sigma>2)"
        "Some h' = Some (snd \<sigma>1') \<oplus> Some (snd \<sigma>2')"
        "(s, snd \<sigma>1), (s, snd \<sigma>1) \<Turnstile> P1 \<and> (s, snd \<sigma>2), (s, snd \<sigma>2) \<Turnstile> P2"
        "(s', snd \<sigma>1'), (s', snd \<sigma>1') \<Turnstile> P1 \<and> (s', snd \<sigma>2'), (s', snd \<sigma>2') \<Turnstile> P2"
        using case_prod_conv pairs_def by auto

      moreover have "snd \<sigma>1 = h1 \<and> snd \<sigma>2 = h2 \<and> snd \<sigma>1' = h1' \<and> snd \<sigma>2' = h2'"
      proof (cases "precise P1")
        case True
        then have "snd \<sigma>1 = h1 \<and> snd \<sigma>1' = h1'"
        proof (rule preciseE)
          show "h \<succeq> h1 \<and> h \<succeq> snd \<sigma>1 \<and> h' \<succeq> h1' \<and> h' \<succeq> snd \<sigma>1'"
            using asm0(1) asm0(2) calculation(5) calculation(6) larger_def by blast
          show "(s, h1), (s', h1') \<Turnstile> P1 \<and> (s, snd \<sigma>1), (s', snd \<sigma>1') \<Turnstile> P1"
            by (metis True \<open>h \<succeq> h1 \<and> h \<succeq> snd \<sigma>1 \<and> h' \<succeq> h1' \<and> h' \<succeq> snd \<sigma>1'\<close> always_sat_refl asm0(3) calculation(7) calculation(8) preciseE sat_comm)
        qed
        then show ?thesis
          by (metis addition_cancellative asm0(1) asm0(2) calculation(5) calculation(6) plus_comm)
      next
        case False
        then have "precise P2"
          using assms(7) by blast
        then have "snd \<sigma>2 = h2 \<and> snd \<sigma>2' = h2'"
        proof (rule preciseE)
          show "h \<succeq> h2 \<and> h \<succeq> snd \<sigma>2 \<and> h' \<succeq> h2' \<and> h' \<succeq> snd \<sigma>2'"
            by (metis asm0(1) asm0(2) calculation(5) calculation(6) larger_def plus_comm)
          show "(s, h2), (s', h2') \<Turnstile> P2 \<and> (s, snd \<sigma>2), (s', snd \<sigma>2') \<Turnstile> P2"
            by (metis \<open>h \<succeq> h2 \<and> h \<succeq> snd \<sigma>2 \<and> h' \<succeq> h2' \<and> h' \<succeq> snd \<sigma>2'\<close> \<open>precise P2\<close> always_sat_refl asm0(4) calculation(7) calculation(8) preciseE sat_comm)
        qed
        then show ?thesis
          using addition_cancellative asm0(1) asm0(2) calculation(5) calculation(6) by blast
      qed
      ultimately have "pair_sat (\<Sigma>1 \<sigma>1) (\<Sigma>1 \<sigma>1') Q1 \<and> pair_sat (\<Sigma>2 \<sigma>2) (\<Sigma>2 \<sigma>2') Q2"
        by (metis asm0(3) asm0(4) prod.exhaust_sel r1(2) r2(2))
      then show "(ss, hh), (ss', hh') \<Turnstile> Star Q1 Q2"
        by (metis (no_types, opaque_lifting) \<open>(ss', hh') \<in> add_states (upperize (\<Sigma>1 \<sigma>1') (fvA Q1)) (upperize (\<Sigma>2 \<sigma>2') (fvA Q2))\<close> \<open>(ss, hh) \<in> add_states (upperize (\<Sigma>1 \<sigma>1) (fvA Q1)) (upperize (\<Sigma>2 \<sigma>2) (fvA Q2))\<close> add_states_sat_star pair_sat_comm pair_sat_def pair_sat_upperize)
    qed
  qed
qed

subsubsection \<open>If\<close>

lemma if_cases:
  assumes "red (Cif b C1 C2) (s, h) C' (s', h')"
      and "C' = C1 \<Longrightarrow> s = s' \<and> h = h' \<Longrightarrow> bdenot b s \<Longrightarrow> P"
      and "C' = C2 \<Longrightarrow> s = s' \<and> h = h' \<Longrightarrow> \<not> bdenot b s \<Longrightarrow> P"
    shows P
  using assms(1)
  apply (rule red.cases)
  apply blast+
  using assms(2) apply fastforce
  using assms(3) apply fastforce
  apply blast+
  done

lemma if_safe_None:
  fixes \<Delta> :: "('i, 'a, nat) cont"

  assumes "bdenot b s \<Longrightarrow> safe n \<Delta> C1 (s, h) S"
      and "\<not> bdenot b s \<Longrightarrow> safe n \<Delta> C2 (s, h) S"
      and "\<Delta> = None"
    shows "safe (Suc n) (None :: ('i, 'a, nat) cont) (Cif b C1 C2) (s, h) S"
proof (rule safeNoneI)
  show "Cif b C1 C2 = Cskip \<Longrightarrow> (s, h) \<in> S" by simp
  show "no_abort (None :: ('i, 'a, nat) cont) (Cif b C1 C2) s h"
  proof (rule no_abortNoneI)
    fix hf H assume "Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H"
    show "\<not> aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))"
    proof (rule ccontr)
      assume "\<not> \<not> aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))"
      then have "aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))" by simp
      then show False
        by (rule aborts.cases) auto
    qed
  qed
  fix H hf C' s' h'
  assume asm0: "Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H
  \<and> red (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
  show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S"
    by (metis asm0 assms(1) assms(2) assms(3) if_cases)
qed

lemma if_safe_Some:
  assumes "bdenot b s \<Longrightarrow> safe n (Some \<Gamma>) C1 (s, h) S"
      and "\<not> bdenot b s \<Longrightarrow> safe n (Some \<Gamma>) C2 (s, h) S"
    shows "safe (Suc n) (Some \<Gamma>) (Cif b C1 C2) (s, h) S"
proof (rule safeSomeI)
  show "Cif b C1 C2 = Cskip \<Longrightarrow> (s, h) \<in> S" by simp
  show "no_abort (Some \<Gamma>) (Cif b C1 C2) s h"
  proof (rule no_abortSomeI)
    fix H hf hj v0
    assume asm0: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma>"
    show "\<not> aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))"
    proof (rule ccontr)
      assume "\<not> \<not> aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))"
      then have "aborts (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H))" by simp
      then show False
        by (rule aborts.cases) auto
    qed
  qed
  fix H hf C' s' h' hj v0
  assume asm0: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H
  \<and> sat_inv s hj \<Gamma> \<and> red (Cif b C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
  show "\<exists>h'' H' hj'.
          full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S"
    by (metis asm0 assms(1) assms(2) if_cases)
qed

lemma if_safe:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "bdenot b s \<Longrightarrow> safe n \<Delta> C1 (s, h) S"
      and "\<not> bdenot b s \<Longrightarrow> safe n \<Delta> C2 (s, h) S"
    shows "safe (Suc n) \<Delta> (Cif b C1 C2) (s, h) S"
  apply (cases \<Delta>) 
  using assms(1) assms(2) if_safe_None apply blast
  using assms(1) assms(2) if_safe_Some by blast


theorem if1_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> (And P (Bool b)) C1 Q"
      and "hoare_triple_valid \<Delta> (And P (Bool (Bnot b))) C2 Q"
  shows "hoare_triple_valid \<Delta> (And P (Low b)) (Cif b C1 C2) Q"
proof -

  obtain \<Sigma>t where safe_t: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> And P (Bool b) \<Longrightarrow> safe n \<Delta> C1 \<sigma> (\<Sigma>t \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And P (Bool b) \<Longrightarrow> pair_sat (\<Sigma>t \<sigma>) (\<Sigma>t \<sigma>') Q"
    using assms(1) hoare_triple_validE by blast
  obtain \<Sigma>f where safe_f: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> And P (Bool (Bnot b)) \<Longrightarrow> safe n \<Delta> C2 \<sigma> (\<Sigma>f \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And P (Bool (Bnot b)) \<Longrightarrow> pair_sat (\<Sigma>f \<sigma>) (\<Sigma>f \<sigma>') Q"
    using assms(2) hoare_triple_validE by blast

  define \<Sigma> where "\<Sigma> = (\<lambda>\<sigma>. if bdenot b (fst \<sigma>) then \<Sigma>t \<sigma> else \<Sigma>f \<sigma>)"

  show ?thesis
  proof (rule hoare_triple_valid_smallerI)

    show "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> And P (Low b) \<Longrightarrow> safe n \<Delta> (Cif b C1 C2) \<sigma> (\<Sigma> \<sigma>)"
    proof -
      fix \<sigma> n
      assume asm0: "\<sigma>, \<sigma> \<Turnstile> And P (Low b)"
      show "safe n \<Delta> (Cif b C1 C2) \<sigma> (\<Sigma> \<sigma>)"
      proof (cases "bdenot b (fst \<sigma>)")
        case True
        then have "safe n \<Delta> C1 \<sigma> (\<Sigma> \<sigma>)"
          by (metis \<Sigma>_def asm0 hyper_sat.simps(1) hyper_sat.simps(3) prod.exhaust_sel safe_t(1))
        then show ?thesis
          by (metis (no_types, lifting) Suc_n_not_le_n True if_safe nat_le_linear prod.exhaust_sel safe_smaller)
      next
        case False
        then have "safe n \<Delta> C2 \<sigma> (\<Sigma> \<sigma>)"
          by (metis \<Sigma>_def asm0 bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) prod.exhaust_sel safe_f(1))
        then show ?thesis
          by (metis (mono_tags) False Suc_n_not_le_n if_safe nat_le_linear prod.exhaust_sel safe_smaller)
      qed
    qed
    fix \<sigma> \<sigma>' assume asm0: "\<sigma>, \<sigma>' \<Turnstile> And P (Low b)"
    show "pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q"
    proof (cases "bdenot b (fst \<sigma>)")
      case True
      then show ?thesis
        by (metis (no_types, lifting) \<Sigma>_def asm0 hyper_sat.simps(1) hyper_sat.simps(3) hyper_sat.simps(5) prod.exhaust_sel safe_t(2))
    next
      case False
      then show ?thesis
        by (metis (no_types, lifting) \<Sigma>_def asm0 bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) hyper_sat.simps(5) prod.exhaust_sel safe_f(2))
    qed
  qed
qed

theorem if2_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> (And P (Bool b)) C1 Q"
      and "hoare_triple_valid \<Delta> (And P (Bool (Bnot b))) C2 Q"
      and "unary Q"
    shows "hoare_triple_valid \<Delta> P (Cif b C1 C2) Q"
proof -
  obtain \<Sigma>t where safe_t: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> And P (Bool b) \<Longrightarrow> safe n \<Delta> C1 \<sigma> (\<Sigma>t \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And P (Bool b) \<Longrightarrow> pair_sat (\<Sigma>t \<sigma>) (\<Sigma>t \<sigma>') Q"
    using assms(1) hoare_triple_validE by blast
  obtain \<Sigma>f where safe_f: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> And P (Bool (Bnot b)) \<Longrightarrow> safe n \<Delta> C2 \<sigma> (\<Sigma>f \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And P (Bool (Bnot b)) \<Longrightarrow> pair_sat (\<Sigma>f \<sigma>) (\<Sigma>f \<sigma>') Q"
    using assms(2) hoare_triple_validE by blast

  define \<Sigma> where "\<Sigma> = (\<lambda>\<sigma>. if bdenot b (fst \<sigma>) then \<Sigma>t \<sigma> else \<Sigma>f \<sigma>)"

  show ?thesis
  proof (rule hoare_triple_valid_smallerI)

    show "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Delta> (Cif b C1 C2) \<sigma> (\<Sigma> \<sigma>)"
    proof -
      fix \<sigma> n
      assume asm0: "\<sigma>, \<sigma> \<Turnstile> P"
      show "safe n \<Delta> (Cif b C1 C2) \<sigma> (\<Sigma> \<sigma>)"
      proof (cases "bdenot b (fst \<sigma>)")
        case True
        then have "safe n \<Delta> C1 \<sigma> (\<Sigma> \<sigma>)"
          by (metis \<Sigma>_def asm0 hyper_sat.simps(1) hyper_sat.simps(3) prod.exhaust_sel safe_t(1))
        then show ?thesis
          by (metis (no_types, lifting) Suc_n_not_le_n True if_safe nat_le_linear prod.exhaust_sel safe_smaller)
      next
        case False
        then have "safe n \<Delta> C2 \<sigma> (\<Sigma> \<sigma>)"
          by (metis \<Sigma>_def asm0 bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) prod.exhaust_sel safe_f(1))
        then show ?thesis
          by (metis (mono_tags) False Suc_n_not_le_n if_safe nat_le_linear prod.exhaust_sel safe_smaller)
      qed
    qed
    fix \<sigma>1 \<sigma>2 assume asm0: "\<sigma>1, \<sigma>2 \<Turnstile> P"
    then have asm0_bis: "\<sigma>2, \<sigma>1 \<Turnstile> P"
      by (simp add: sat_comm)
    show "pair_sat (\<Sigma> \<sigma>1) (\<Sigma> \<sigma>2) Q"
    proof (rule pair_sat_smallerI)
      fix \<sigma>1' \<sigma>2'
      assume asm1: "\<sigma>1' \<in> \<Sigma> \<sigma>1 \<and> \<sigma>2' \<in> \<Sigma> \<sigma>2"
      then have "\<sigma>1', \<sigma>1' \<Turnstile> Q"
        apply (cases "bdenot b (fst \<sigma>1)")
         apply (metis (no_types, lifting) \<Sigma>_def always_sat_refl asm0 hyper_sat.simps(1) hyper_sat.simps(3) pair_sat_def safe_t(2) surjective_pairing)
        by (metis (no_types, lifting) \<Sigma>_def always_sat_refl asm0 bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) pair_satE prod.collapse safe_f(2))
      moreover have "\<sigma>2', \<sigma>2' \<Turnstile> Q"
        apply (cases "bdenot b (fst \<sigma>2)")
         apply (metis (mono_tags) \<Sigma>_def always_sat_refl asm0_bis asm1 entailsI entails_def fst_conv hyper_sat.simps(1) hyper_sat.simps(3) old.prod.exhaust pair_sat_def safe_t(2))
        using \<Sigma>_def always_sat_refl asm0_bis bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) pair_satE prod.collapse safe_f(2)
        by (metis (no_types, lifting) asm1)
      ultimately show "\<sigma>1', \<sigma>2' \<Turnstile> Q"
        by (metis assms(3) eq_fst_iff unaryE)
    qed
  qed
qed


subsubsection \<open>Sequential composition\<close>

inductive_cases red_seq_cases: "red (Cseq C1 C2) \<sigma> C' \<sigma>'"

lemma aborts_seq_aborts_C1:
  assumes "aborts (Cseq C1 C2) \<sigma>"
  shows "aborts C1 \<sigma>"
  using aborts.simps assms cmd.inject(6) by blast


lemma safe_seq_None:
  assumes "safe n (None :: ('i, 'a, nat) cont) C1 (s, h) S1"
      and "\<And>m s' h'. m \<le> n \<and> (s', h') \<in> S1 \<Longrightarrow> safe m (None :: ('i, 'a, nat) cont) C2 (s', h') S2"
    shows "safe n (None :: ('i, 'a, nat) cont) (Cseq C1 C2) (s, h) S2"
  using assms
proof (induct n arbitrary: C1 s h)
  case (Suc n)
  show ?case
  proof (rule safeNoneI)
    show "no_abort (None :: ('i, 'a, nat) cont) (Cseq C1 C2) s h"
      by (meson Suc.prems(1) aborts_seq_aborts_C1 no_abort.simps(1) safeNoneE_bis(2))
    fix H hf C' s' h'
    assume asm0: "Some H = Some h \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> no_guard H \<and> red (Cseq C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S2"
    proof (rule red_seq_cases)
      show "red (Cseq C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      show "C1 = Cskip \<Longrightarrow>
    C' = C2 \<Longrightarrow>
    (s', h') = (s, FractionalHeap.normalize (get_fh H)) \<Longrightarrow>
    \<exists>h'' H'. full_ownership (get_fh H') \<and>
       no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S2"
        using Suc.prems(1) Suc.prems(2) asm0 order_refl prod.inject safeNoneE_bis(1)
        by (metis le_SucI)
      fix C1' assume "C' = Cseq C1' C2" "red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')"
      obtain H' h'' where asm1: "full_ownership (get_fh H')" "no_guard H'" "h' = FractionalHeap.normalize (get_fh H')"
        "Some H' = Some h'' \<oplus> Some hf" "safe n (None :: ('i, 'a, nat) cont) C1' (s', h'') S1"
      using Suc(2) safeNoneE(3)[of n C1 s h S1 H hf C1' s' h']
      using \<open>red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')\<close> asm0 by blast
    moreover have "safe n (None :: ('i, 'a, nat) cont) (Cseq C1' C2) (s', h'') S2"
      using Suc.hyps Suc.prems(2) calculation(5)
      using le_Suc_eq by presburger
    ultimately show ?thesis
      using \<open>C' = Cseq C1' C2\<close> by blast
  qed
  qed (simp)
qed (simp)

lemma safe_seq_Some:
  assumes "safe n (Some \<Gamma>) C1 (s, h) S1"
      and "\<And>m s' h'. m \<le> n \<and> (s', h') \<in> S1 \<Longrightarrow> safe m (Some \<Gamma>) C2 (s', h') S2"
    shows "safe n (Some \<Gamma>) (Cseq C1 C2) (s, h) S2"
  using assms
proof (induct n arbitrary: C1 s h)
  case (Suc n)
  show ?case
  proof (rule safeSomeI)
    show "no_abort (Some \<Gamma>) (Cseq C1 C2) s h"
      by (meson Suc.prems(1) aborts_seq_aborts_C1 no_abort.simps(2) safeSomeE(2))
    fix H hf C' s' h' hj v0
    assume asm0: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cseq C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S2"
    proof (rule red_seq_cases)
      show "red (Cseq C1 C2) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by blast
      show "C1 = Cskip \<Longrightarrow>
    C' = C2 \<Longrightarrow>
    (s', h') = (s, FractionalHeap.normalize (get_fh H)) \<Longrightarrow> \<exists>h'' H' hj'. full_ownership (get_fh H') \<and>
       semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H')
    \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S2"
        using Pair_inject Suc.prems(1) Suc_n_not_le_n asm0 assms(2) not_less_eq_eq safeSomeE(1)
        by (metis (no_types, lifting) Suc.prems(2) nat_le_linear)
      fix C1' assume "C' = Cseq C1' C2" "red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')"
      obtain H' h'' hj' where asm1: "full_ownership (get_fh H') \<and>
   semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C1' (s', h'') S1"
        using Suc(2) safeSomeE(3)[of n \<Gamma> C1 s h S1 H hj hf v0 C1' s' h']
        using \<open>red C1 (s, FractionalHeap.normalize (get_fh H)) C1' (s', h')\<close> asm0 by blast
      moreover have "safe n (Some \<Gamma>) (Cseq C1' C2) (s', h'') S2"
        by (simp add: Suc.hyps Suc.prems(2) calculation)
      ultimately show ?thesis
        using \<open>C' = Cseq C1' C2\<close> by blast
    qed
  qed (simp)
qed (simp)

lemma seq_safe:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C1 (s, h) S1"
      and "\<And>m s' h'. m \<le> n \<and> (s', h') \<in> S1 \<Longrightarrow> safe m \<Delta> C2 (s', h') S2"
    shows "safe n \<Delta> (Cseq C1 C2) (s, h) S2"
  apply (cases \<Delta>) 
  using assms(1) assms(2) safe_seq_None apply blast
  using assms(1) assms(2) safe_seq_Some by blast

theorem seq_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> P C1 R"
      and "hoare_triple_valid \<Delta> R C2 Q"
    shows "hoare_triple_valid \<Delta> P (Cseq C1 C2) Q"
proof -
  obtain \<Sigma>1 where safe_1: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Delta> C1 \<sigma> (\<Sigma>1 \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma>1 \<sigma>) (\<Sigma>1 \<sigma>') R"
    using assms(1) hoare_triple_validE by blast
  obtain \<Sigma>2 where safe_2: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> R \<Longrightarrow> safe n \<Delta> C2 \<sigma> (\<Sigma>2 \<sigma>)"
    "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> R \<Longrightarrow> pair_sat (\<Sigma>2 \<sigma>) (\<Sigma>2 \<sigma>') Q"
    using assms(2) hoare_triple_validE by blast

  define \<Sigma> where "\<Sigma> = (\<lambda>\<sigma>. (\<Union>\<sigma>' \<in> \<Sigma>1 \<sigma>. \<Sigma>2 \<sigma>'))"

  show ?thesis
  proof (rule hoare_triple_valid_smallerI)
    show "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Delta> (Cseq C1 C2) \<sigma> (\<Sigma> \<sigma>)"
    proof -
      fix \<sigma> n assume asm0: "\<sigma>, \<sigma> \<Turnstile> P"
      then have "pair_sat (\<Sigma>1 \<sigma>) (\<Sigma>1 \<sigma>) R"
        using safe_1(2) by blast

      have "safe n \<Delta> (Cseq C1 C2) (fst \<sigma>, snd \<sigma>) (\<Sigma> \<sigma>)"
      proof (rule seq_safe)
        show "safe n \<Delta> C1 (fst \<sigma>, snd \<sigma>) (\<Sigma>1 \<sigma>)"
          by (simp add: asm0 safe_1(1))
        fix m s' h'
        assume "m \<le> n \<and> (s', h') \<in> \<Sigma>1 \<sigma>"
        then show "safe m \<Delta> C2 (s', h') (\<Sigma> \<sigma>)"
          by (metis (no_types, opaque_lifting) Sup_upper \<open>\<Sigma> \<equiv> \<lambda>\<sigma>. \<Union> (\<Sigma>2 ` \<Sigma>1 \<sigma>)\<close> \<open>pair_sat (\<Sigma>1 \<sigma>) (\<Sigma>1 \<sigma>) R\<close> image_iff pair_sat_def safe_2(1) safe_larger_set)
      qed
      then show "safe n \<Delta> (Cseq C1 C2) \<sigma> (\<Sigma> \<sigma>)" by auto
    qed
    fix \<sigma>1 \<sigma>2
    assume asm0: "\<sigma>1, \<sigma>2 \<Turnstile> P"
    show "pair_sat (\<Sigma> \<sigma>1) (\<Sigma> \<sigma>2) Q"
    proof (rule pair_sat_smallerI)
      fix \<sigma>1'' \<sigma>2''
      assume asm1: "\<sigma>1'' \<in> \<Sigma> \<sigma>1 \<and> \<sigma>2'' \<in> \<Sigma> \<sigma>2"
      then obtain \<sigma>1' \<sigma>2' where "\<sigma>1'' \<in> \<Sigma>2 \<sigma>1'" "\<sigma>1' \<in> \<Sigma>1 \<sigma>1" "\<sigma>2'' \<in> \<Sigma>2 \<sigma>2'" "\<sigma>2' \<in> \<Sigma>1 \<sigma>2"
        using \<open>\<Sigma> \<equiv> \<lambda>\<sigma>. \<Union> (\<Sigma>2 ` \<Sigma>1 \<sigma>)\<close> by blast
      then show "\<sigma>1'', \<sigma>2'' \<Turnstile> Q"
        by (meson asm0 pair_sat_def safe_1(2) safe_2(2))
    qed
  qed
qed


subsubsection \<open>Frame rule\<close>

lemma safe_frame_None:
  assumes "safe n (None :: ('i, 'a, nat) cont) C (s, h) S"
      and "Some H = Some h \<oplus> Some hf0"
    shows "safe n (None :: ('i, 'a, nat) cont) C (s, H) (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''})"
  using assms
proof (induct n arbitrary: s h H C)
  case (Suc n)
  show "safe (Suc n) (None :: ('i, 'a, nat) cont) C (s, H) (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''} )"
  proof (rule safeNoneI)
    show "C = Cskip \<Longrightarrow> (s, H) \<in> add_states S {(s', hf0) |s'. agrees (- wrC C) s s'}"
      using CollectI Suc.prems(1) Suc.prems(2) add_states_def agrees_def[of "- wrC C" s] safeNoneE(1)[of n C s h S]
      by fast
    show "no_abort (None :: ('i, 'a, nat) cont) C s H"
      using Suc.prems(1) Suc.prems(2) larger_def no_abort_larger safeNoneE(2) by blast
    fix H1 hf1 C' s' h'
    assume asm0: "Some H1 = Some H \<oplus> Some hf1 \<and> full_ownership (get_fh H1) \<and> no_guard H1 \<and> red C (s, FractionalHeap.normalize (get_fh H1)) C' (s', h')"
    then obtain hf where "Some hf = Some hf0 \<oplus> Some hf1"
      by (metis (no_types, opaque_lifting) Suc.prems(2) option.collapse plus.simps(1) plus_asso plus_comm)
    then have "Some H1 = Some h \<oplus> Some hf"
      by (metis Suc.prems(2) asm0 plus_asso)
    then obtain h'' H' where r: "full_ownership (get_fh H')"
      "no_guard H'" "h' = FractionalHeap.normalize (get_fh H')" "Some H' = Some h'' \<oplus> Some hf" "safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S"
      using safeNoneE(3)[of n C s h S H1 hf C' s'] Suc.prems(1) asm0 by blast
    then obtain h''' where "Some h''' = Some h'' \<oplus> Some hf0"
      by (metis \<open>Some hf = Some hf0 \<oplus> Some hf1\<close> not_Some_eq plus.simps(1) plus_asso)
    then have "Some H' = Some h''' \<oplus> Some hf1"
      by (metis \<open>Some hf = Some hf0 \<oplus> Some hf1\<close> plus_asso r(4))
    moreover have "safe n (None :: ('i, 'a, nat) cont) C' (s', h''') (add_states S {(s'', hf0) |s''. agrees (- wrC C') s' s''})"
    proof (rule Suc.hyps)
      show "safe n (None :: ('i, 'a, nat) cont) C' (s', h'') S"
        using r by simp
      show "Some h''' = Some h'' \<oplus> Some hf0"
        by (simp add: \<open>Some h''' = Some h'' \<oplus> Some hf0\<close>)
    qed
    moreover have "add_states S {(s'', hf0) |s''. agrees (- wrC C') s' s''} \<subseteq> add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''}"
    proof -
      have "wrC C' \<subseteq> wrC C"
        using asm0 red_properties(1) by blast
      have "{(s'', hf0) |s''. agrees (- wrC C') s' s''} \<subseteq> {(s'', hf0) |s''. agrees (- wrC C) s s''}"
      proof
        fix x assume "x \<in> {(s'', hf0) |s''. agrees (- wrC C') s' s''}"
        then have "agrees (- wrC C') s' (fst x) \<and> snd x = hf0" by force
        moreover have "fvC C' \<subseteq> fvC C \<and> wrC C' \<subseteq> wrC C \<and> agrees (- wrC C) s' s"
          using asm0 red_properties(1) by force

        moreover have "agrees (- wrC C) s (fst x)"
        proof (rule agreesI)
          fix y assume "y \<in> - wrC C"
          show "s y = fst x y"
            by (metis (no_types, lifting) Compl_subset_Compl_iff \<open>y \<in> - wrC C\<close> agrees_def calculation(1) calculation(2) in_mono)
        qed
        then show "x \<in> {(s'', hf0) |s''. agrees (- wrC C) s s''}"
          using \<open>agrees (- wrC C') s' (fst x) \<and> snd x = hf0\<close> by force
      qed
      then show ?thesis
        by (metis (no_types, lifting) add_states_comm add_states_subset)
    qed
    ultimately have "safe n (None :: ('i, 'a, nat) cont) C' (s', h''') (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''})"
      using safe_larger_set by blast
    then show "\<exists>h'' H'.
          full_ownership (get_fh H') \<and>
          no_guard H' \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf1 \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''})"
      using \<open>Some H' = Some h''' \<oplus> Some hf1\<close> r(1) r(2) r(3) by blast
  qed
qed (simp)

lemma safe_frame_Some:
  assumes "safe n (Some \<Gamma>) C (s, h) S"
      and "Some H = Some h \<oplus> Some hf0"
    shows "safe n (Some \<Gamma>) C (s, H) (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''})"
  using assms
proof (induct n arbitrary: s h H C)
  case (Suc n)
  let ?R = "{(s'', hf0) |s''. agrees (- wrC C) s s''}"
  show "safe (Suc n) (Some \<Gamma>) C (s, H) (add_states S ?R)"
  proof (rule safeSomeI)
    show "C = Cskip \<Longrightarrow> (s, H) \<in> add_states S ?R"
      using CollectI Suc.prems(1) Suc.prems(2) add_states_def[of S ?R] agrees_def[of "- wrC C" s]
        safeSomeE(1)[of n \<Gamma> C s h S] by fast
    show "no_abort (Some \<Gamma>) C s H"
      using Suc.prems(1) Suc.prems(2) larger_def no_abort_larger safeSomeE(2) by blast
    fix H1 hf1 C' s' h' hj v0
    assume asm0: "Some H1 = Some H \<oplus> Some hj \<oplus> Some hf1 \<and>
       full_ownership (get_fh H1) \<and> semi_consistent \<Gamma> v0 H1 \<and> sat_inv s hj \<Gamma> \<and> red C (s, FractionalHeap.normalize (get_fh H1)) C' (s', h')"
    then obtain hf where "Some hf = Some hf0 \<oplus> Some hf1"
      by (metis (no_types, opaque_lifting) Suc.prems(2) option.collapse plus.simps(1) plus_asso plus_comm)
    then have "Some H1 = Some h \<oplus> Some hj \<oplus> Some hf"
      by (metis (no_types, opaque_lifting) Suc.prems(2) asm0 plus_asso plus_comm)

    then obtain h'' H' hj' where r: "full_ownership (get_fh H') \<and>
   semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') S"
      using safeSomeE(3)[of n \<Gamma> C s h S H1 hj hf v0 C' s' h'] Suc.prems(1) asm0 by blast


    then obtain h''' where "Some h''' = Some h'' \<oplus> Some hf0"
      by (metis (no_types, lifting) \<open>Some hf = Some hf0 \<oplus> Some hf1\<close> plus.simps(2) plus.simps(3) plus_asso plus_comm)
    then have "Some H' = Some h''' \<oplus> Some hj' \<oplus> Some hf1"
      by (metis (no_types, lifting) \<open>Some hf = Some hf0 \<oplus> Some hf1\<close> plus_asso plus_comm r)
    moreover have "safe n (Some \<Gamma>) C' (s', h''') (add_states S {(s'', hf0) |s''. agrees (- wrC C') s' s''})"
    proof (rule Suc.hyps)
      show "safe n (Some \<Gamma>) C' (s', h'') S"
        using r by simp
      show "Some h''' = Some h'' \<oplus> Some hf0"
        by (simp add: \<open>Some h''' = Some h'' \<oplus> Some hf0\<close>)
    qed
    moreover have "add_states S {(s'', hf0) |s''. agrees (- wrC C') s' s''} \<subseteq> add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''}"
    proof -
      have "wrC C' \<subseteq> wrC C"
        using asm0 red_properties(1) by blast
      have "{(s'', hf0) |s''. agrees (- wrC C') s' s''} \<subseteq> {(s'', hf0) |s''. agrees (- wrC C) s s''}"
      proof
        fix x assume "x \<in> {(s'', hf0) |s''. agrees (- wrC C') s' s''}"
        then have "agrees (- wrC C') s' (fst x) \<and> snd x = hf0" by force
        moreover have "fvC C' \<subseteq> fvC C \<and> wrC C' \<subseteq> wrC C \<and> agrees (- wrC C) s' s"
          using asm0 red_properties(1) by force
        moreover have "agrees (- wrC C) s (fst x)"
        proof (rule agreesI)
          fix y assume "y \<in> - wrC C"
          then show "s y = fst x y"
            by (metis (mono_tags, opaque_lifting) Compl_iff agrees_def calculation(1) calculation(2) in_mono)
        qed
        then show "x \<in> {(s'', hf0) |s''. agrees (- wrC C) s s''}"
          using \<open>agrees (- wrC C') s' (fst x) \<and> snd x = hf0\<close> by force
      qed
      then show ?thesis
        by (metis (no_types, lifting) add_states_comm add_states_subset)
    qed
    ultimately have "safe n (Some \<Gamma>) C' (s', h''') (add_states S ?R)"
      using safe_larger_set by blast
    then show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and>
          semi_consistent \<Gamma> v0 H' \<and>
          sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf1 \<and> safe n (Some \<Gamma>) C' (s', h'') (add_states S ?R)"
      using \<open>Some H' = Some h''' \<oplus> Some hj' \<oplus> Some hf1\<close> r by blast
    qed
qed (simp)

lemma safe_frame:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "safe n \<Delta> C (s, h) S"
      and "Some H = Some h \<oplus> Some hf0"
    shows "safe n \<Delta> C (s, H) (add_states S {(s'', hf0) |s''. agrees (- wrC C) s s''})"
  apply (cases \<Delta>)
  using assms(1) assms(2) safe_frame_None apply blast
  using assms(1) assms(2) safe_frame_Some by blast

theorem frame_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> P C Q"
      and "disjoint (fvA R) (wrC C)"
      and "precise P \<or> precise R"
    shows "hoare_triple_valid \<Delta> (Star P R) C (Star Q R)"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)" "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q"
    using assms(1) hoare_triple_validE by blast

  define pairs where "pairs = (\<lambda>\<sigma>. { (p, r) |p r. Some (snd \<sigma>) = Some p \<oplus> Some r \<and> (fst \<sigma>, p), (fst \<sigma>, p) \<Turnstile> P
    \<and> (fst \<sigma>, r), (fst \<sigma>, r) \<Turnstile> R })"

  define \<Sigma>' where "\<Sigma>' = (\<lambda>\<sigma>. (\<Union>(p, r) \<in> pairs \<sigma>. add_states (\<Sigma> (fst \<sigma>, p)) {(s'', r) |s''. agrees (- wrC C) (fst \<sigma>) s''}))"

  show ?thesis
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> Star P R \<Longrightarrow> safe n \<Delta> C (s, h) (\<Sigma>' (s, h))"
    proof -
      fix s h n assume asm1: "(s, h), (s, h) \<Turnstile> Star P R"
      then obtain p r where "Some h = Some p \<oplus> Some r" "(s, p), (s, p) \<Turnstile> P" "(s, r), (s, r) \<Turnstile> R"
        using always_sat_refl hyper_sat.simps(4) by blast
      then have "safe n \<Delta> C (s, p) (\<Sigma> (s, p))"
        using asm0(1) by blast
      then have "safe n \<Delta> C (s, h) (add_states (\<Sigma> (s, p)) {(s'', r) |s''. agrees (- wrC C) s s''})"
        using safe_frame[of n \<Delta> C s p "\<Sigma> (s, p)" h r] \<open>Some h = Some p \<oplus> Some r\<close> by blast
      moreover have "(add_states (\<Sigma> (s, p)) {(s'', r) |s''. agrees (- wrC C) s s''}) \<subseteq> \<Sigma>' (s, h)"
      proof -
        have "(p, r) \<in> pairs (s, h)"
          using \<open>(s, p), (s, p) \<Turnstile> P\<close> \<open>(s, r), (s, r) \<Turnstile> R\<close> \<open>Some h = Some p \<oplus> Some r\<close> pairs_def by force
        then show ?thesis
          using \<Sigma>'_def by auto
      qed
      ultimately show "safe n \<Delta> C (s, h) (\<Sigma>' (s, h))"
        using safe_larger_set by blast
    qed

    fix s1 h1 s2 h2
    assume asm1: "(s1, h1), (s2, h2) \<Turnstile> Star P R"
    then obtain p1 p2 r1 r2 where "Some h1 = Some p1 \<oplus> Some r1" "Some h2 = Some p2 \<oplus> Some r2"
      "(s1, p1), (s2, p2) \<Turnstile> P" "(s1, r1), (s2, r2) \<Turnstile> R"
      by auto
    then have "(s1, p1), (s1, p1) \<Turnstile> P \<and> (s1, r1), (s1, r1) \<Turnstile> R \<and> (s2, p2), (s2, p2) \<Turnstile> P \<and> (s2, r2), (s2, r2) \<Turnstile> R"
      using always_sat_refl sat_comm by blast


    show "pair_sat (\<Sigma>' (s1, h1)) (\<Sigma>' (s2, h2)) (Star Q R)"
    proof (rule pair_satI)
      fix s1' h1' s2' h2'
      assume asm2: "(s1', h1') \<in> \<Sigma>' (s1, h1) \<and> (s2', h2') \<in> \<Sigma>' (s2, h2)"
      then obtain p1' r1' p2' r2' where "(p1', r1') \<in> pairs (s1, h1)" "(p2', r2') \<in> pairs (s2, h2)"
        "(s1', h1') \<in> add_states (\<Sigma> (s1, p1')) {(s'', r1') |s''. agrees (- wrC C) s1 s''}"
        "(s2', h2') \<in> add_states (\<Sigma> (s2, p2')) {(s'', r2') |s''. agrees (- wrC C) s2 s''}"
        using \<Sigma>'_def by force

      moreover obtain "(s1, p1'), (s1, p1') \<Turnstile> P" "(s1, r1'), (s1, r1') \<Turnstile> R" "(s2, p2'), (s2, p2') \<Turnstile> P" "(s2, r2'), (s2, r2') \<Turnstile> R"
        "Some h1 = Some p1' \<oplus> Some r1'" "Some h2 = Some p2' \<oplus> Some r2'"
        using calculation(1) calculation(2) pairs_def by auto
      ultimately have "p1 = p1' \<and> p2 = p2' \<and> r1 = r1' \<and> r2 = r2'"
      proof (cases "precise P")
        case True
        then have "p1 = p1' \<and> p2 = p2'" using preciseE
          by (metis \<open>(s1, p1), (s1, p1) \<Turnstile> P \<and> (s1, r1), (s1, r1) \<Turnstile> R \<and> (s2, p2), (s2, p2) \<Turnstile> P \<and> (s2, r2), (s2, r2) \<Turnstile> R\<close> \<open>Some h1 = Some p1 \<oplus> Some r1\<close> \<open>Some h2 = Some p2 \<oplus> Some r2\<close> \<open>\<And>thesis. (\<lbrakk>(s1, p1'), (s1, p1') \<Turnstile> P; (s1, r1'), (s1, r1') \<Turnstile> R; (s2, p2'), (s2, p2') \<Turnstile> P; (s2, r2'), (s2, r2') \<Turnstile> R; Some h1 = Some p1' \<oplus> Some r1'; Some h2 = Some p2' \<oplus> Some r2'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> larger_def)
        then show ?thesis
          by (metis \<open>Some h1 = Some p1 \<oplus> Some r1\<close> \<open>Some h1 = Some p1' \<oplus> Some r1'\<close> \<open>Some h2 = Some p2 \<oplus> Some r2\<close> \<open>Some h2 = Some p2' \<oplus> Some r2'\<close> addition_cancellative plus_comm)
      next
        case False
        then have "precise R"
          using assms(3) by auto
        then show ?thesis
          by (metis (no_types, opaque_lifting) \<open>(s1, p1), (s1, p1) \<Turnstile> P \<and> (s1, r1), (s1, r1) \<Turnstile> R \<and> (s2, p2), (s2, p2) \<Turnstile> P \<and> (s2, r2), (s2, r2) \<Turnstile> R\<close> \<open>Some h1 = Some p1 \<oplus> Some r1\<close> \<open>Some h2 = Some p2 \<oplus> Some r2\<close> \<open>\<And>thesis. (\<lbrakk>(s1, p1'), (s1, p1') \<Turnstile> P; (s1, r1'), (s1, r1') \<Turnstile> R; (s2, p2'), (s2, p2') \<Turnstile> P; (s2, r2'), (s2, r2') \<Turnstile> R; Some h1 = Some p1' \<oplus> Some r1'; Some h2 = Some p2' \<oplus> Some r2'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> addition_cancellative larger_def plus_comm preciseE)
      qed
      then have "pair_sat (\<Sigma> (s1, p1')) (\<Sigma> (s2, p2')) Q"
        using \<open>(s1, p1), (s2, p2) \<Turnstile> P\<close> asm0(2) by blast
      moreover have "pair_sat {(s'', r1') |s''. agrees (- wrC C) s1 s''} {(s'', r2') |s''. agrees (- wrC C) s2 s''} R"
        (is "pair_sat ?R1 ?R2 R")
      proof (rule pair_satI)
        fix s1'' r1'' s2'' r2'' assume "(s1'', r1'') \<in> {(s'', r1') |s''. agrees (- wrC C) s1 s''} \<and> (s2'', r2'') \<in> {(s'', r2') |s''. agrees (- wrC C) s2 s''}"
        then obtain "r1'' = r1'" "r2'' = r2'" "agrees (- wrC C) s1 s1''" "agrees (- wrC C) s2 s2''"
          by fastforce
        then show "(s1'', r1''), (s2'', r2'') \<Turnstile> R"
          using \<open>(s1, r1), (s2, r2) \<Turnstile> R\<close> \<open>p1 = p1' \<and> p2 = p2' \<and> r1 = r1' \<and> r2 = r2'\<close> agrees_minusD agrees_same
            assms(2) sat_comm
          by (metis (no_types, opaque_lifting) disjoint_def inf_commute)
      qed
      ultimately have "pair_sat (add_states (\<Sigma> (s1, p1')) ?R1) (add_states (\<Sigma> (s2, p2')) ?R2) (Star Q R)"
        using add_states_sat_star by blast
      then show "(s1', h1'), (s2', h2') \<Turnstile> Star Q R"
        using \<open>(s1', h1') \<in> add_states (\<Sigma> (s1, p1')) {(s'', r1') |s''. agrees (- wrC C) s1 s''}\<close> \<open>(s2', h2') \<in> add_states (\<Sigma> (s2, p2')) {(s'', r2') |s''. agrees (- wrC C) s2 s''}\<close> pair_sat_def by blast
    qed
  qed
qed

subsubsection \<open>Consequence\<close>

theorem consequence_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> P' C Q'"
      and "entails P P'"
      and "entails Q' Q"
    shows "hoare_triple_valid \<Delta> P C Q"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P' \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)" "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P' \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q'"
    using assms(1) hoare_triple_validE by blast

  show ?thesis
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> P \<Longrightarrow> safe n \<Delta> C (s, h) (\<Sigma> (s, h))"
      using asm0(1) assms(2) entails_def by blast
    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> (s, h)) (\<Sigma> (s', h')) Q"
      by (meson asm0(2) assms(2) assms(3) entails_def pair_sat_def)
  qed
qed

subsubsection \<open>Existential\<close>

theorem existential_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> P C Q"
      and "x \<notin> fvC C"
      and "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> x \<notin> fvA (invariant \<Gamma>)"
      and "unambiguous P x"
    shows "hoare_triple_valid \<Delta> (Exists x P) C (Exists x Q)"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)" "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q"
    using assms(1) hoare_triple_validE by blast

  define \<Sigma>' where "\<Sigma>' = (\<lambda>\<sigma>. \<Union>v \<in> { v |v. ((fst \<sigma>)(x := v), snd \<sigma>), ((fst \<sigma>)(x := v), snd \<sigma>) \<Turnstile> P }. upperize (\<Sigma> ((fst \<sigma>)(x := v), snd \<sigma>)) (fvA Q - {x}))"

  show ?thesis
  proof (rule hoare_triple_validI)
    show "\<And>s h n. (s, h), (s, h) \<Turnstile> Exists x P \<Longrightarrow> safe n \<Delta> C (s, h) (\<Sigma>' (s, h))"
    proof -
      fix s h n assume "(s, h), (s, h) \<Turnstile> Exists x P"
      then obtain v where "(s(x := v), h), (s(x := v), h) \<Turnstile> P"
        using always_sat_refl hyper_sat.simps(7) by blast
      then have "\<Sigma> (s(x := v), h) \<subseteq> \<Sigma>' (s, h)"
        using upperize_larger SUP_upper2 \<Sigma>'_def by fastforce

      moreover have "safe n \<Delta> C (s(x := v), h) (\<Sigma> (s(x := v), h))"
        by (simp add: \<open>(s(x := v), h), (s(x := v), h) \<Turnstile> P\<close> asm0(1))
      ultimately have "safe n \<Delta> C (s(x := v), h) (\<Sigma>' (s, h))"
        using safe_larger_set by blast
      then have "safe n \<Delta> C (s, h) (\<Sigma>' (s, h))"
      proof (rule safe_free_vars)
        show "\<And>\<Gamma>. \<Delta> = Some \<Gamma> \<Longrightarrow> agrees (fvA (invariant \<Gamma>)) (s(x := v)) s"
          by (meson agrees_comm agrees_update assms(3))
        show "agrees (fvC C \<union> (fvA Q - {x})) (s(x := v)) s"
          by (simp add: agrees_def assms(2))
        show "upper_fvs (\<Sigma>' (s, h)) (fvA Q - {x})"
        proof (rule upper_fvsI)
          fix sa s' ha
          assume asm0: "(sa, ha) \<in> \<Sigma>' (s, h) \<and> agrees (fvA Q - {x}) sa s'"
          then obtain v where "(s(x := v), h), (s(x := v), h) \<Turnstile> P" "(sa, ha) \<in> upperize (\<Sigma> (s(x := v), h)) (fvA Q - {x})"
            using \<Sigma>'_def by force
          then have "(s', ha) \<in> upperize (\<Sigma> (s(x := v), h)) (fvA Q - {x})"
            using asm0 upper_fvs_def upper_fvs_upperize by blast
          then show "(s', ha) \<in> \<Sigma>' (s, h)"
            using \<open>(s(x := v), h), (s(x := v), h) \<Turnstile> P\<close> \<Sigma>'_def by force
        qed
      qed
      then show "safe n \<Delta> C (s, h) (\<Sigma>' (s, h))"
        by auto
    qed
    fix s1 h1 s2 h2
    assume asm1: "(s1, h1), (s2, h2) \<Turnstile> Exists x P"
    then obtain v1' v2' where "(s1(x := v1'), h1), (s2(x := v2'), h2) \<Turnstile> P" by auto
    show "pair_sat (\<Sigma>' (s1, h1)) (\<Sigma>' (s2, h2)) (Exists x Q)"
    proof (rule pair_satI)
      fix s1' h1' s2' h2'
      assume asm2: "(s1', h1') \<in> \<Sigma>' (s1, h1) \<and> (s2', h2') \<in> \<Sigma>' (s2, h2)"

      then obtain v1 v2 where
        r: "(s1(x := v1), h1), (s1(x := v1), h1) \<Turnstile> P" "(s1', h1') \<in> upperize (\<Sigma> (s1(x := v1), h1)) (fvA Q - {x})"
        "(s2(x := v2), h2), (s2(x := v2), h2) \<Turnstile> P" "(s2', h2') \<in> upperize (\<Sigma> (s2(x := v2), h2)) (fvA Q - {x})"
        using \<Sigma>'_def by auto

      then obtain s1'' s2'' where "agrees (fvA Q - {x}) s1'' s1'" "(s1'', h1') \<in> \<Sigma> (s1(x := v1), h1)"
        "agrees (fvA Q - {x}) s2'' s2'" "(s2'', h2') \<in> \<Sigma> (s2(x := v2), h2)"
        using in_upperize by (metis (no_types, lifting))

      moreover have "(s1(x := v1), h1), (s2(x := v2), h2) \<Turnstile> P"
\<comment>\<open>Unambiguity needed here\<close>
      proof -
        have "v1 = v1'"
          using \<open>(s1(x := v1'), h1), (s2(x := v2'), h2) \<Turnstile> P\<close> always_sat_refl assms(4) r(1) unambiguous_def by blast
        moreover have "v2 = v2'"
          using \<open>(s1(x := v1'), h1), (s2(x := v2'), h2) \<Turnstile> P\<close> always_sat_refl assms(4) r(3) sat_comm_aux unambiguous_def by blast
        ultimately show ?thesis
          by (simp add: \<open>(s1(x := v1'), h1), (s2(x := v2'), h2) \<Turnstile> P\<close>)
      qed
      then have "pair_sat (\<Sigma> (s1(x := v1), h1)) (\<Sigma> (s2(x := v2), h2)) Q"
        using asm0 by simp
      then have "(s1'', h1'), (s2'', h2') \<Turnstile> Q"
        using calculation(2) calculation(4) pair_sat_def by blast
      moreover have "agrees (fvA Q) s1'' (s1'(x := s1'' x))"
      proof (rule agreesI)
        fix y assume "y \<in> fvA Q"
        then show "s1'' y = (s1'(x := s1'' x)) y"
          apply (cases "x = y")
           apply auto[1]
          by (metis (mono_tags, lifting) DiffI agrees_def calculation(1) fun_upd_other singleton_iff)
      qed
      moreover have "agrees (fvA Q) s2'' (s2'(x := s2'' x))"
      proof (rule agreesI)
        fix y assume "y \<in> fvA Q"
        then show "s2'' y = (s2'(x := s2'' x)) y"
          apply (cases "x = y")
           apply auto[1]
          by (metis (mono_tags, lifting) DiffI agrees_def calculation(3) fun_upd_other singleton_iff)
      qed
      ultimately have "(s1'(x := s1'' x), h1'), (s2'(x := s2'' x), h2') \<Turnstile> Q"
        by (meson agrees_same sat_comm)
      then show "(s1', h1'), (s2', h2') \<Turnstile> Exists x Q"
        using hyper_sat.simps(7) by blast
    qed
  qed
qed


subsubsection \<open>While loops\<close>



inductive leads_to_loop where
  "leads_to_loop b I \<Sigma> \<sigma> \<sigma>"
| "\<lbrakk> leads_to_loop b I \<Sigma> \<sigma> \<sigma>' ; bdenot b (fst \<sigma>') ; \<sigma>'' \<in> \<Sigma> \<sigma>' \<rbrakk> \<Longrightarrow> leads_to_loop b I \<Sigma> \<sigma> \<sigma>''"


definition leads_to_loop_set where
  "leads_to_loop_set b I \<Sigma> \<sigma> = { \<sigma>' |\<sigma>'. leads_to_loop b I \<Sigma> \<sigma> \<sigma>'}"

definition trans_\<Sigma> where
  "trans_\<Sigma> b I \<Sigma> \<sigma> = Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (leads_to_loop_set b I \<Sigma> \<sigma>)"

inductive_cases red_while_cases: "red (Cwhile b s) \<sigma> C' \<sigma>'"
inductive_cases abort_while_cases: "aborts (Cwhile b s) \<sigma>"

lemma safe_while_None:
  assumes "\<And>\<sigma> m. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
      and "(s, h), (s, h) \<Turnstile> I"
      and "leads_to_loop b I \<Sigma> \<sigma> (s, h)"
    shows "safe n (None :: ('i, 'a, nat) cont) (Cwhile b C) (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
  using assms
proof (induct n arbitrary: s h)
  let ?S = "trans_\<Sigma> b I \<Sigma> \<sigma>"
  case (Suc n)
  show ?case
  proof (rule safeNoneI)
    show "no_abort (None :: ('i, 'a, nat) cont) (Cwhile b C) s h"
      using abort_while_cases no_abortNoneI by blast
    fix H hf C' s' h'
    assume asm0: "Some H = Some h \<oplus> Some hf \<and> full_ownership (get_fh H) \<and> no_guard H \<and> red (Cwhile b C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    show "\<exists>h'' H'. full_ownership (get_fh H') \<and> no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H')
  \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n (None :: ('i, 'a, nat) cont) C' (s', h'') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
    proof (rule red_while_cases)
      show "red (Cwhile b C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by linarith
      assume asm1: "C' = Cif b (Cseq C (Cwhile b C)) Cskip" "(s', h') = (s, FractionalHeap.normalize (get_fh H))"
      have "safe n (None :: ('i, 'a, nat) cont) C' (s, h) ?S"
      proof (cases n)
        case (Suc k)
        have "safe (Suc k) (None :: ('i, 'a, nat) cont) (Cif b (Cseq C (Cwhile b C)) Cskip) (s, h) ?S"
        proof (rule if_safe)
          have "\<not> bdenot b s \<Longrightarrow> (s, h) \<in> ?S"
            by (metis CollectI Suc.prems(4) asm1(2) fst_eqD leads_to_loop_set_def member_filter trans_\<Sigma>_def)
          then show "\<not> bdenot b s \<Longrightarrow> safe k (None :: ('i, 'a, nat) cont) Cskip (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
            by (metis Pair_inject asm1(2) safe_skip)
          assume asm2: "bdenot b s"
          then have "(s, h), (s, h) \<Turnstile> And I (Bool b)"
            by (simp add: Suc.prems(3))
          then have r: "safe (Suc n) (None :: ('i, 'a, nat) cont) C (s, h) (\<Sigma> (s, h))"
            using Suc.prems(1) by blast
          show "safe k (None :: ('i, 'a, nat) cont) (Cseq C (Cwhile b C)) (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
          proof (rule seq_safe)
            show "safe k (None :: ('i, 'a, nat) cont) C (s, h) (\<Sigma> (s, h))"
              by (metis Suc Suc_n_not_le_n nat_le_linear r safe_smaller)
            fix m s' h' assume asm3: "m \<le> k \<and> (s', h') \<in> \<Sigma> (s, h)"
            have "safe n (None :: ('i, 'a, nat) cont) (Cwhile b C) (s', h') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
            proof (rule Suc.hyps)
              show "leads_to_loop b I \<Sigma> \<sigma> (s', h')"
                by (metis Suc.prems(4) asm2 asm3 fst_conv leads_to_loop.intros(2))
              show "(s', h'), (s', h') \<Turnstile> I"
                using \<open>(s, h), (s, h) \<Turnstile> And I (Bool b)\<close> asm3 assms(2) pair_satE by blast
              show "\<And>\<sigma>. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C \<sigma> (\<Sigma> \<sigma>)"
                by (meson Suc.prems(1) Suc_n_not_le_n nat_le_linear safe_smaller)
            qed (auto simp add: assms)
            then show "safe m (None :: ('i, 'a, nat) cont) (Cwhile b C) (s', h') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
              using Suc asm3 le_SucI safe_smaller by blast
          qed
        qed
        then show ?thesis
          using Suc asm1(1) by blast
      qed (simp)
      then show "\<exists>h'' H'. full_ownership (get_fh H') \<and>
       no_guard H' \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hf \<and> safe n None C' (s', h'') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
        using asm0 asm1(2) by blast
    qed
  qed (simp)
qed (simp)


lemma safe_while_Some:
  assumes "\<And>\<sigma> m. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n (Some \<Gamma>) C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
      and "(s, h), (s, h) \<Turnstile> I"
      and "leads_to_loop b I \<Sigma> \<sigma> (s, h)"
    shows "safe n (Some \<Gamma>) (Cwhile b C) (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
  using assms
proof (induct n arbitrary: s h)
  let ?S = "trans_\<Sigma> b I \<Sigma> \<sigma>"
  case (Suc n)
  show ?case
  proof (rule safeSomeI)
    show "no_abort (Some \<Gamma>) (Cwhile b C) s h"
      using abort_while_cases no_abortSomeI by blast
    fix H hf C' s' h' hj v0
    assume asm0: "Some H = Some h \<oplus> Some hj \<oplus> Some hf \<and>
       full_ownership (get_fh H) \<and> semi_consistent \<Gamma> v0 H \<and> sat_inv s hj \<Gamma> \<and> red (Cwhile b C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
    show "\<exists>h'' H' hj'. full_ownership (get_fh H') \<and> semi_consistent \<Gamma> v0 H' \<and> sat_inv s' hj' \<Gamma> \<and>
          h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
    proof (rule red_while_cases)
      show "red (Cwhile b C) (s, FractionalHeap.normalize (get_fh H)) C' (s', h')"
        using asm0 by linarith
      assume asm1: "C' = Cif b (Cseq C (Cwhile b C)) Cskip" "(s', h') = (s, FractionalHeap.normalize (get_fh H))"
      have "safe n (Some \<Gamma>) C' (s, h) ?S"
      proof (cases n)
        case (Suc k)
        have "safe (Suc k) (Some \<Gamma>) (Cif b (Cseq C (Cwhile b C)) Cskip) (s, h) ?S"
        proof (rule if_safe)
          have "\<not> bdenot b s \<Longrightarrow> (s, h) \<in> ?S"
            by (metis CollectI Suc.prems(4) asm1(2) fst_eqD leads_to_loop_set_def member_filter trans_\<Sigma>_def)
          then show "\<not> bdenot b s \<Longrightarrow> safe k (Some \<Gamma>) Cskip (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
            by (metis Pair_inject asm1(2) safe_skip)
          assume asm2: "bdenot b s"
          then have "(s, h), (s, h) \<Turnstile> And I (Bool b)"
            by (simp add: Suc.prems(3))
          then have r: "safe (Suc n) (Some \<Gamma>) C (s, h) (\<Sigma> (s, h))"
            using Suc.prems(1) by blast
          show "safe k (Some \<Gamma>) (Cseq C (Cwhile b C)) (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
          proof (rule seq_safe)
            show "safe k (Some \<Gamma>) C (s, h) (\<Sigma> (s, h))"
              by (metis Suc Suc_n_not_le_n nat_le_linear r safe_smaller)
            fix m s' h' assume asm3: "m \<le> k \<and> (s', h') \<in> \<Sigma> (s, h)"
            have "safe n (Some \<Gamma>) (Cwhile b C) (s', h') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
            proof (rule Suc.hyps)
              show "leads_to_loop b I \<Sigma> \<sigma> (s', h')"
                by (metis Suc.prems(4) asm2 asm3 fst_conv leads_to_loop.intros(2))
              show "(s', h'), (s', h') \<Turnstile> I"
                using \<open>(s, h), (s, h) \<Turnstile> And I (Bool b)\<close> asm3 assms(2) pair_satE by blast
              show "\<And>\<sigma>. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n (Some \<Gamma>) C \<sigma> (\<Sigma> \<sigma>)"
                by (meson Suc.prems(1) Suc_n_not_le_n nat_le_linear safe_smaller)
            qed (auto simp add: assms)
            then show "safe m (Some \<Gamma>) (Cwhile b C) (s', h') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
              using Suc asm3 le_SucI safe_smaller by blast
          qed
        qed
        then show ?thesis
          using Suc asm1(1) by blast
      qed (simp)
      then show "\<exists>h'' H' hj'.
       full_ownership (get_fh H') \<and>
       semi_consistent \<Gamma> v0 H' \<and>
       sat_inv s' hj' \<Gamma> \<and> h' = FractionalHeap.normalize (get_fh H') \<and> Some H' = Some h'' \<oplus> Some hj' \<oplus> Some hf \<and> safe n (Some \<Gamma>) C' (s', h'') (trans_\<Sigma> b I \<Sigma> \<sigma>)"
        using asm0 asm1(2) by blast
    qed
  qed (simp)
qed (simp)

lemma safe_while:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "\<And>\<sigma> m. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
      and "(s, h), (s, h) \<Turnstile> I"
      and "leads_to_loop b I \<Sigma> \<sigma> (s, h)"
    shows "safe n \<Delta> (Cwhile b C) (s, h) (trans_\<Sigma> b I \<Sigma> \<sigma>)"
  apply (cases \<Delta>)
  using assms safe_while_None apply blast
  using assms safe_while_Some by blast

lemma leads_to_sat_inv_unary:
  assumes "leads_to_loop b I \<Sigma> \<sigma> \<sigma>'"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
      and "\<sigma>, \<sigma> \<Turnstile> I"
    shows "\<sigma>', \<sigma>' \<Turnstile> I"
  using assms
proof (induct arbitrary: rule: leads_to_loop.induct)
  case (2 b I \<Sigma> \<sigma>0 \<sigma>1 \<sigma>2)
  then have "pair_sat (\<Sigma> \<sigma>1) (\<Sigma> \<sigma>1) I"
    by (metis hyper_sat.simps(1) hyper_sat.simps(3) prod.collapse)
  then show ?case
    using "2.hyps"(4) pair_sat_def by blast
qed (simp)

theorem while_rule2:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "unary I"
      and "hoare_triple_valid \<Delta> (And I (Bool b)) C I"
    shows "hoare_triple_valid \<Delta> I (Cwhile b C) (And I (Bool (Bnot b)))"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> (And I (Bool b)) \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
    using assms(2) hoare_triple_validE by blast
  let ?\<Sigma> = "trans_\<Sigma> b I \<Sigma>"
  show ?thesis
  proof (rule hoare_triple_validI)

    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> I \<Longrightarrow> pair_sat (?\<Sigma> (s, h)) (?\<Sigma> (s', h')) (And I (Bool (Bnot b)))"
    proof -
      fix s1 h1 s2 h2 assume asm0: "(s1, h1), (s2, h2) \<Turnstile> I"
      show "pair_sat (trans_\<Sigma> b I \<Sigma> (s1, h1)) (trans_\<Sigma> b I \<Sigma> (s2, h2)) (And I (Bool (Bnot b)))"
      proof (rule pair_satI)
        fix s1' h1' s2' h2'
        assume asm1: "(s1', h1') \<in> trans_\<Sigma> b I \<Sigma> (s1, h1) \<and> (s2', h2') \<in> trans_\<Sigma> b I \<Sigma> (s2, h2)"
        then obtain "leads_to_loop b I \<Sigma> (s1, h1) (s1', h1')" "\<not> bdenot b s1'"
           "leads_to_loop b I \<Sigma> (s2, h2) (s2', h2')" "\<not> bdenot b s2'"
          using trans_\<Sigma>_def leads_to_loop_set_def
          by (metis fst_conv mem_Collect_eq member_filter)
        then have "(s1', h1'), (s1', h1') \<Turnstile> I \<and> (s2', h2'), (s2', h2') \<Turnstile> I"
          by (meson \<open>\<And>\<sigma>' \<sigma>. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I\<close> always_sat_refl asm0 leads_to_sat_inv_unary sat_comm_aux)
        then show "(s1', h1'), (s2', h2') \<Turnstile> And I (Bool (Bnot b))"
          by (metis \<open>\<not> bdenot b s1'\<close> \<open>\<not> bdenot b s2'\<close> assms(1) bdenot.simps(3) hyper_sat.simps(1) hyper_sat.simps(3) unaryE)
      qed
    qed
    fix s h n
    assume asm1: "(s, h), (s, h) \<Turnstile> I"

    show "safe n \<Delta> (Cwhile b C) (s, h) (trans_\<Sigma> b I \<Sigma> (s, h))"
    proof (rule safe_while)
      show "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
        by (simp add: \<open>\<And>\<sigma>' \<sigma>. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I\<close>)
      show "(s, h), (s, h) \<Turnstile> I"
        using asm1 by auto
      show "leads_to_loop b I \<Sigma> (s, h) (s, h)"
        by (simp add: leads_to_loop.intros(1))
      show "\<And>\<sigma> m. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)"
        by (simp add: asm0)
    qed
  qed
qed

fun iterate_sigma :: "nat \<Rightarrow> bexp \<Rightarrow> ('i, 'a, nat) assertion \<Rightarrow> ((store \<times> ('i, 'a) heap) \<Rightarrow> (store \<times> ('i, 'a) heap) set) \<Rightarrow> (store \<times> ('i, 'a) heap) \<Rightarrow> (store \<times> ('i, 'a) heap) set"
  where
  "iterate_sigma 0 b I \<Sigma> \<sigma> = {\<sigma>}"
| "iterate_sigma (Suc n) b I \<Sigma> \<sigma> = (\<Union>\<sigma>' \<in> Set.filter (\<lambda>\<sigma>. bdenot b (fst \<sigma>)) (iterate_sigma n b I \<Sigma> \<sigma>). \<Sigma> \<sigma>')"


lemma union_of_iterate_sigma_is_leads_to_loop_set:
  assumes "leads_to_loop b I \<Sigma> \<sigma> \<sigma>'"
  shows "\<sigma>' \<in> (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
  using assms
proof (induct rule: leads_to_loop.induct)
  case (1 b I \<Sigma> \<sigma>)
  have "\<sigma> \<in> iterate_sigma 0 b I \<Sigma> \<sigma>"
    by simp
  then show ?case
    by blast
next
  case (2 b I \<Sigma> \<sigma> \<sigma>' \<sigma>'')
  then obtain n where "\<sigma>' \<in> iterate_sigma n b I \<Sigma> \<sigma>" by blast
  then have "\<sigma>'' \<in> iterate_sigma (Suc n) b I \<Sigma> \<sigma>" using 2 by auto
  then show ?case by blast
qed

lemma trans_included:
  "trans_\<Sigma> b I \<Sigma> \<sigma> \<subseteq> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
proof
  fix x assume "x \<in> trans_\<Sigma> b I \<Sigma> \<sigma>"
  then have "\<not> bdenot b (fst x) \<and> leads_to_loop b I \<Sigma> \<sigma> x"
    by (simp add: leads_to_loop_set_def trans_\<Sigma>_def)
  then show "x \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
    by (metis member_filter union_of_iterate_sigma_is_leads_to_loop_set)
qed


lemma iterate_sigma_low_all_sat_I_and_low:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
      and "\<sigma>1, \<sigma>2 \<Turnstile> I"
      and "bdenot b (fst \<sigma>1) = bdenot b (fst \<sigma>2)"
    shows "pair_sat (iterate_sigma n b I \<Sigma> \<sigma>1) (iterate_sigma n b I \<Sigma> \<sigma>2) (And I (Low b))"
  using assms
proof (induct n)
  case 0
  then show ?case
    by (metis (mono_tags, lifting) hyper_sat.simps(3) hyper_sat.simps(5) iterate_sigma.simps(1) pair_satI prod.exhaust_sel singletonD)
next
  case (Suc n)
  show ?case
  proof (rule pair_satI)
    fix s1 h1 s2 h2
    assume asm0: "(s1, h1) \<in> iterate_sigma (Suc n) b I \<Sigma> \<sigma>1 \<and> (s2, h2) \<in> iterate_sigma (Suc n) b I \<Sigma> \<sigma>2"
    then obtain \<sigma>1' \<sigma>2' where "bdenot b (fst \<sigma>1')" "bdenot b (fst \<sigma>2')"
      "\<sigma>1' \<in> iterate_sigma n b I \<Sigma> \<sigma>1" "\<sigma>2' \<in> iterate_sigma n b I \<Sigma> \<sigma>2"
      "(s1, h1) \<in> \<Sigma> \<sigma>1'" "(s2, h2) \<in> \<Sigma> \<sigma>2'"
      by auto
    then have "pair_sat (iterate_sigma n b I \<Sigma> \<sigma>1) (iterate_sigma n b I \<Sigma> \<sigma>2) (And I (Low b))"
      using Suc.hyps
      using Suc.prems(3) assms(1) assms(2) by blast
    moreover have "pair_sat (\<Sigma> \<sigma>1') (\<Sigma> \<sigma>2') (And I (Low b))"
    proof (rule Suc.prems)
      show "\<sigma>1', \<sigma>2' \<Turnstile> And I (Bool b)"
        by (metis \<open>\<sigma>1' \<in> iterate_sigma n b I \<Sigma> \<sigma>1\<close> \<open>\<sigma>2' \<in> iterate_sigma n b I \<Sigma> \<sigma>2\<close> \<open>bdenot b (fst \<sigma>1')\<close> \<open>bdenot b (fst \<sigma>2')\<close> calculation hyper_sat.simps(1) hyper_sat.simps(3) pair_sat_def prod.exhaust_sel)
    qed
    ultimately show "(s1, h1), (s2, h2) \<Turnstile> And I (Low b)"
      using \<open>(s1, h1) \<in> \<Sigma> \<sigma>1'\<close> \<open>(s2, h2) \<in> \<Sigma> \<sigma>2'\<close> pair_sat_def by blast
  qed
qed

lemma iterate_empty_later_empty:
  assumes "iterate_sigma n b I \<Sigma> \<sigma> = {}"
      and "m \<ge> n"
    shows "iterate_sigma m b I \<Sigma> \<sigma> = {}"
  using assms
proof (induct "m - n" arbitrary: n m)
  case (Suc k)
  then obtain mm where "m = Suc mm"
    by (metis iterate_sigma.elims zero_diff)
  then have "iterate_sigma mm b I \<Sigma> \<sigma> = {}"
    by (metis Suc.hyps(1) Suc.hyps(2) Suc.prems(1) Suc.prems(2) Suc_le_mono diff_Suc_Suc diff_diff_cancel diff_le_self)
  then show ?case
    using \<open>m = Suc mm\<close> by force
qed (simp)

lemma all_same:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
      and "\<sigma>1, \<sigma>2 \<Turnstile> I"
      and "bdenot b (fst \<sigma>1) = bdenot b (fst \<sigma>2)"
      and "x1 \<in> iterate_sigma n b I \<Sigma> \<sigma>1"
      and "x2 \<in> iterate_sigma n b I \<Sigma> \<sigma>2"
    shows "bdenot b (fst x1) = bdenot b (fst x2)"
proof -
  have "x1, x2 \<Turnstile> (And I (Low b))"
    using assms(1) assms(2) assms(3) assms(4) assms(5) iterate_sigma_low_all_sat_I_and_low pair_sat_def by blast
  then show ?thesis
    by (metis (no_types, lifting) hyper_sat.simps(3) hyper_sat.simps(5) surjective_pairing)
qed

lemma non_empty_at_most_once:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
      and "\<sigma>, \<sigma> \<Turnstile> I"
      and "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma n1 b I \<Sigma> \<sigma>) \<noteq> {}"
      and "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma n2 b I \<Sigma> \<sigma>) \<noteq> {}"
    shows "n1 = n2"
proof -
  let ?n = "min n1 n2"
  obtain \<sigma>' where "\<sigma>' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma ?n b I \<Sigma> \<sigma>)"
    by (metis assms(3) assms(4) equals0I min.orderE min_def)
  then have "\<not> bdenot b (fst \<sigma>')"
    by fastforce
  moreover have "pair_sat (iterate_sigma ?n b I \<Sigma> \<sigma>) (iterate_sigma ?n b I \<Sigma> \<sigma>) (And I (Low b))"
    using assms(1) assms(2) assms(3) iterate_sigma_low_all_sat_I_and_low by blast
  then have r: "\<And>x. x \<in> iterate_sigma ?n b I \<Sigma> \<sigma> \<Longrightarrow> \<not> bdenot b (fst x)"
    by (metis \<open>\<sigma>' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma (min n1 n2) b I \<Sigma> \<sigma>)\<close> all_same assms(1) assms(2) member_filter)
  then have "iterate_sigma (Suc ?n) b I \<Sigma> \<sigma> = {}" by auto
  then have "\<not> (n1 > ?n) \<and> \<not> (n2 > ?n)" using iterate_empty_later_empty[of "Suc ?n" b I \<Sigma> \<sigma>]
      assms by (metis (no_types, lifting) Set.filter_def empty_Collect_eq empty_def le_simps(3) mem_Collect_eq)
  then show ?thesis by linarith
qed

lemma one_non_empty_union:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
      and "\<sigma>, \<sigma> \<Turnstile> I"
      and "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k b I \<Sigma> \<sigma>) \<noteq> {}"
    shows "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>) = Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k b I \<Sigma> \<sigma>)"
proof
  show "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k b I \<Sigma> \<sigma>) \<subseteq> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
    by auto
  show "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>) \<subseteq> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k b I \<Sigma> \<sigma>)"
  proof
    fix x assume "x \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
    then obtain k' where "x \<in> iterate_sigma k' b I \<Sigma> \<sigma>" "\<not> bdenot b (fst x)"
      by auto
    then have "x \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k' b I \<Sigma> \<sigma>)"
      by fastforce
    then have "k = k'"
      using non_empty_at_most_once assms(1) assms(2) assms(3) by blast
    then show "x \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k b I \<Sigma> \<sigma>)"
      using \<open>x \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k' b I \<Sigma> \<sigma>)\<close> by blast
  qed
qed

definition not_set where
  "not_set b S = Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) S"

lemma union_exists_at_some_point_exactly:
  assumes "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
      and "\<sigma>1, \<sigma>2 \<Turnstile> I"
      and "bdenot b (fst \<sigma>1) = bdenot b (fst \<sigma>2)"
      and "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>1) \<noteq> {}"
      and "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>2) \<noteq> {}"
    shows "\<exists>k. not_set b (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>1) = not_set b (iterate_sigma k b I \<Sigma> \<sigma>1) \<and> not_set b (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>2) = not_set b (iterate_sigma k b I \<Sigma> \<sigma>2)"
proof -
  obtain k1 where "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<noteq> {}"
    using assms(4) by fastforce
  moreover obtain k2 where "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k2 b I \<Sigma> \<sigma>2) \<noteq> {}"
    using assms(5) by fastforce

  show ?thesis
  proof (cases "k1 \<le> k2")
    case True
    then have "iterate_sigma k1 b I \<Sigma> \<sigma>2 \<noteq> {}"
      by (metis (no_types, lifting) Collect_cong Set.filter_def \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k2 b I \<Sigma> \<sigma>2) \<noteq> {}\<close> empty_def iterate_empty_later_empty mem_Collect_eq)
    then obtain \<sigma>1' \<sigma>2' where "\<sigma>1' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<and> \<sigma>2' \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2"
      using calculation by blast
    then have "\<not> bdenot b (fst \<sigma>1')"
      by fastforce
    moreover have "pair_sat (iterate_sigma k1 b I \<Sigma> \<sigma>1) (iterate_sigma k1 b I \<Sigma> \<sigma>2) (And I (Low b))"
      using assms(1) assms(2) assms(3) iterate_sigma_low_all_sat_I_and_low by blast
    then have r: "\<And>x1 x2. x1 \<in> iterate_sigma k1 b I \<Sigma> \<sigma>1 \<and> x2 \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2 \<Longrightarrow> bdenot b (fst x1) \<longleftrightarrow> bdenot b (fst x2)"
      by (metis (no_types, opaque_lifting) eq_fst_iff hyper_sat.simps(3) hyper_sat.simps(5) pair_sat_def)
    then have "\<not> bdenot b (fst \<sigma>2')"
      by (metis \<open>\<sigma>1' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<and> \<sigma>2' \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2\<close> member_filter)
    then have "\<And>x1. x1 \<in> iterate_sigma k1 b I \<Sigma> \<sigma>1 \<Longrightarrow> \<not> bdenot b (fst x1)"
      using \<open>\<sigma>1' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<and> \<sigma>2' \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2\<close> r by blast
    then have "iterate_sigma (Suc k1) b I \<Sigma> \<sigma>1 = {}" by auto
    moreover have "\<And>x2. x2 \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2 \<Longrightarrow> \<not> bdenot b (fst x2)"
      by (metis \<open>\<sigma>1' \<in> Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<and> \<sigma>2' \<in> iterate_sigma k1 b I \<Sigma> \<sigma>2\<close> member_filter r)
    then have "iterate_sigma (Suc k1) b I \<Sigma> \<sigma>2 = {}" by auto
    then have "k1 = k2"
      using True \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k2 b I \<Sigma> \<sigma>2) \<noteq> {}\<close> dual_order.antisym[of k1 k2]
          ex_in_conv iterate_empty_later_empty[of _ b I \<Sigma> \<sigma>2] member_filter not_less_eq_eq
      by metis
    moreover have "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>1) = Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1)"
      using one_non_empty_union[of I b \<Sigma> \<sigma>1]
      using \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<noteq> {}\<close> always_sat_refl assms(1) assms(2) by blast
    moreover have "Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>2) = Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>2)"
      using one_non_empty_union[of I b \<Sigma> \<sigma>2]
      using \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k2 b I \<Sigma> \<sigma>2) \<noteq> {}\<close> always_sat_refl assms(1) assms(2) calculation(3) sat_comm by blast
    ultimately show ?thesis
      by (metis not_set_def)
  next
    case False
    then have "iterate_sigma k2 b I \<Sigma> \<sigma>1 \<noteq> {}"
      by (metis (no_types, lifting) Collect_cong Set.filter_def calculation empty_def iterate_empty_later_empty linorder_le_cases mem_Collect_eq)
    then obtain \<sigma>1' \<sigma>2' where "\<sigma>1' \<in> iterate_sigma k2 b I \<Sigma> \<sigma>1 \<and> \<sigma>2' \<in> not_set b (iterate_sigma k2 b I \<Sigma> \<sigma>2)"
      by (metis \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k2 b I \<Sigma> \<sigma>2) \<noteq> {}\<close> ex_in_conv not_set_def)
    then have "\<not> bdenot b (fst \<sigma>2')"
      using not_set_def by fastforce
    then have "\<not> bdenot b (fst \<sigma>1')"
      by (metis \<open>\<sigma>1' \<in> iterate_sigma k2 b I \<Sigma> \<sigma>1 \<and> \<sigma>2' \<in> not_set b (iterate_sigma k2 b I \<Sigma> \<sigma>2)\<close> all_same assms(1) assms(2) assms(3) member_filter not_set_def)
    then have "\<And>x1. x1 \<in> iterate_sigma k2 b I \<Sigma> \<sigma>1 \<Longrightarrow> \<not> bdenot b (fst x1)"
      using \<open>\<sigma>1' \<in> iterate_sigma k2 b I \<Sigma> \<sigma>1 \<and> \<sigma>2' \<in> not_set b (iterate_sigma k2 b I \<Sigma> \<sigma>2)\<close> all_same always_sat_refl assms(1) assms(2) by blast
    then have "iterate_sigma (Suc k2) b I \<Sigma> \<sigma>1 = {}" by auto
    moreover have "\<And>x2. x2 \<in> iterate_sigma k2 b I \<Sigma> \<sigma>2 \<Longrightarrow> \<not> bdenot b (fst x2)"
      using \<open>\<not> bdenot b (fst \<sigma>1')\<close> \<open>\<sigma>1' \<in> iterate_sigma k2 b I \<Sigma> \<sigma>1 \<and> \<sigma>2' \<in> not_set b (iterate_sigma k2 b I \<Sigma> \<sigma>2)\<close> all_same assms(1) assms(2) assms(3) by blast
    then have "iterate_sigma (Suc k2) b I \<Sigma> \<sigma>2 = {}" by auto
    then show ?thesis
      by (metis (no_types, lifting) Collect_empty_eq False Set.filter_def \<open>Set.filter (\<lambda>\<sigma>. \<not> bdenot b (fst \<sigma>)) (iterate_sigma k1 b I \<Sigma> \<sigma>1) \<noteq> {}\<close> calculation empty_iff iterate_empty_later_empty not_less_eq_eq)
  qed
qed


theorem while_rule1:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "hoare_triple_valid \<Delta> (And I (Bool b)) C (And I (Low b))"
    shows "hoare_triple_valid \<Delta> (And I (Low b)) (Cwhile b C) (And I (Bool (Bnot b)))"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> (And I (Bool b)) \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)"
      and "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> (And I (Bool b)) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))"
    using assms(1) hoare_triple_validE by blast
  let ?\<Sigma> = "\<lambda>\<sigma>. not_set b (\<Union>n. iterate_sigma n b I \<Sigma> \<sigma>)"
  show ?thesis
  proof (rule hoare_triple_validI)

    show "\<And>s h s' h'. (s, h), (s', h') \<Turnstile> And I (Low b) \<Longrightarrow> pair_sat (?\<Sigma> (s, h)) (?\<Sigma> (s', h')) (And I (Bool (Bnot b)))"
    proof -
      fix s1 h1 s2 h2 assume asm0: "(s1, h1), (s2, h2) \<Turnstile> And I (Low b)"
      then have asm0_bis: "(s1, h1), (s2, h2) \<Turnstile> I \<and> bdenot b (fst (s1, h1)) = bdenot b (fst (s2, h2))" by auto

      show "pair_sat (not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s1, h1))) (not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s2, h2))) (And I (Bool (Bnot b)))"
      proof (rule pair_satI)
        fix s1' h1' s2' h2'
        assume asm1: "(s1', h1') \<in> not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s1, h1)) \<and> (s2', h2') \<in> not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s2, h2))"
        then obtain k where "not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s1, h1)) = not_set b (iterate_sigma k b I \<Sigma> (s1, h1))"
          "not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s2, h2)) = not_set b (iterate_sigma k b I \<Sigma> (s2, h2))"
          using union_exists_at_some_point_exactly[of I b \<Sigma> "(s1, h1)" "(s2, h2)"] asm0_bis not_set_def
          using \<open>\<And>\<sigma>' \<sigma>. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))\<close> by blast
        moreover have "pair_sat (iterate_sigma k b I \<Sigma> (s1, h1)) (iterate_sigma k b I \<Sigma> (s2, h2)) (And I (Low b))"
          using \<open>\<And>\<sigma>' \<sigma>. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))\<close> asm0_bis iterate_sigma_low_all_sat_I_and_low by blast
        ultimately show "(s1', h1'), (s2', h2') \<Turnstile> And I (Bool (Bnot b))"
          by (metis (no_types, lifting) asm1 bdenot.simps(3) fst_conv hyper_sat.simps(1) hyper_sat.simps(3) member_filter not_set_def pair_satE)
      qed
    qed

    fix s h n
    assume asm1: "(s, h), (s, h) \<Turnstile> And I (Low b)"

    have "safe n \<Delta> (Cwhile b C) (s, h) (trans_\<Sigma> b I \<Sigma> (s, h))"
    proof (rule safe_while)
      show "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') I"
        by (meson \<open>\<And>\<sigma>' \<sigma>. \<sigma>, \<sigma>' \<Turnstile> And I (Bool b) \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') (And I (Low b))\<close> hyper_sat.simps(3) pair_sat_def)
      show "(s, h), (s, h) \<Turnstile> I"
        using asm1 by auto
      show "leads_to_loop b I \<Sigma> (s, h) (s, h)"
        by (simp add: leads_to_loop.intros(1))
      show "\<And>\<sigma> m. \<sigma>, \<sigma> \<Turnstile> And I (Bool b) \<Longrightarrow> safe n \<Delta> C \<sigma> (\<Sigma> \<sigma>)"
        by (simp add: asm0)
    qed
    then show "safe n \<Delta> (Cwhile b C) (s, h) (not_set b (\<Union>n. iterate_sigma n b I \<Sigma> (s, h)))"
      by (simp add: not_set_def safe_larger_set trans_included)
  qed
qed


lemma entails_smallerI:
  assumes "\<And>s1 h1 s2 h2. (s1, h1), (s2, h2) \<Turnstile> A \<Longrightarrow> (s1, h1), (s2, h2) \<Turnstile> B"
  shows "entails A B"
  by (simp add: assms entails_def)


corollary while_rule:
  fixes \<Delta> :: "('i, 'a, nat) cont"
  assumes "entails P (Star P' R)"
      and "unary P'"
      and "fvA R \<inter> wrC C = {}"
      and "hoare_triple_valid \<Delta> (And P' (Bool e)) C P'"
      and "hoare_triple_valid \<Delta> (And P (Bool (Band e e'))) C (And P (Low (Band e e')))"
      and "precise P' \<or> precise R"
    shows "hoare_triple_valid \<Delta> (And P (Low (Band e e'))) (Cseq (Cwhile (Band e e') C) (Cwhile e C)) (And (Star P' R) (Bool (Bnot e)))"
proof (rule seq_rule)

  show "hoare_triple_valid \<Delta> (And P (Low (Band e e'))) (Cwhile (Band e e') C) (And P (Bool (Bnot (Band e e'))))"
  proof (rule while_rule1)
    show "hoare_triple_valid \<Delta> (And P (Bool (Band e e'))) C (And P (Low (Band e e')))"
      by (simp add: assms(5))
  qed

  show "hoare_triple_valid \<Delta> (And P (Bool (Bnot (Band e e')))) (Cwhile e C) (And (Star P' R) (Bool (Bnot e)))"
  proof (rule consequence_rule)
    show "hoare_triple_valid \<Delta> (Star P' R) (Cwhile e C) (Star (And P' (Bool (Bnot e))) R)"
    proof (rule frame_rule)
      show "precise P' \<or> precise R"
        by (simp add: assms(6))
      show "disjoint (fvA R) (wrC (Cwhile e C))"
        by (simp add: assms(3) disjoint_def)
      show "hoare_triple_valid \<Delta> P' (Cwhile e C) (And P' (Bool (Bnot e)))"
      proof (rule while_rule2)
        show "hoare_triple_valid \<Delta> (And P' (Bool e)) C P'"
          by (simp add: assms(4))
        show "unary P'" using assms(2) by auto
      qed
    qed
    show "entails (And P (Bool (Bnot (Band e e')))) (Star P' R)"
      using assms(1) entails_def hyper_sat.simps(3) by blast
    show "entails (Star (And P' (Bool (Bnot e))) R) (And (Star P' R) (Bool (Bnot e)))"
    proof (rule entails_smallerI)
      fix s1 h1 s2 h2
      assume asm0: "(s1, h1), (s2, h2) \<Turnstile> Star (And P' (Bool (Bnot e))) R"
      then obtain hp1 hr1 hp2 hr2 where "Some h1 = Some hp1 \<oplus> Some hr1" "Some h2 = Some hp2 \<oplus> Some hr2"
        "(s1, hp1), (s2, hp2) \<Turnstile> And P' (Bool (Bnot e))" "(s1, hr1), (s2, hr2) \<Turnstile> R"
        using hyper_sat.simps(4) by blast
      then show "(s1, h1), (s2, h2) \<Turnstile> And (Star P' R) (Bool (Bnot e))"
        by fastforce
    qed
  qed
qed

subsubsection \<open>CommCSL is sound\<close>

theorem soundness:
  assumes "\<Delta> \<turnstile> {P} C {Q}"
  shows "\<Delta> \<Turnstile> {P} C {Q}"
  using assms
proof (induct rule: CommCSL.induct)
  case (RuleAtomicShared \<Gamma> f \<alpha> sact uact J P Q x C map_to_arg sarg ms map_to_multiset \<pi>)
  then show ?case using atomic_rule_shared by blast
qed (simp_all add: rule_skip  assign_rule new_rule write_rule read_rule share_rule atomic_rule_unique
    rule_par if1_rule if2_rule seq_rule frame_rule consequence_rule existential_rule while_rule1 while_rule2)

subsection \<open>Corollaries\<close>

theorem safety:
  assumes "hoare_triple_valid (None :: ('i, 'a, nat) cont) P C Q"
      and "(s1, h1), (s2, h2) \<Turnstile> P"

      and "Some H1 = Some h1 \<oplus> Some hf1 \<and> full_ownership (get_fh H1) \<and> no_guard H1"
\<comment>\<open>extend h1 to a normal state H1 without guards\<close>

      and "Some H2 = Some h2 \<oplus> Some hf2 \<and> full_ownership (get_fh H2) \<and> no_guard H2"
\<comment>\<open>extend h2 to a normal state H2 without guards\<close>

    shows "\<And>\<sigma>' C'. red_rtrans C (s1, normalize (get_fh H1)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
      and "\<And>\<sigma>' C'. red_rtrans C (s2, normalize (get_fh H2)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
      and "\<And>\<sigma>1' \<sigma>2'. red_rtrans C (s1, normalize (get_fh H1)) Cskip \<sigma>1'
  \<Longrightarrow> red_rtrans C (s2, normalize (get_fh H2)) Cskip \<sigma>2'
  \<Longrightarrow> (\<exists>h1' h2' H1' H2'. no_guard H1' \<and> full_ownership (get_fh H1') \<and> snd \<sigma>1' = normalize (get_fh H1') \<and> Some H1' = Some h1' \<oplus> Some hf1
      \<and> no_guard H2' \<and> full_ownership (get_fh H2') \<and> snd \<sigma>2' = normalize (get_fh H2') \<and> Some H2' = Some h2' \<oplus> Some hf2
      \<and> (fst \<sigma>1', h1'), (fst \<sigma>2', h2') \<Turnstile> Q)"
proof -
  obtain \<Sigma> where asm0: "\<And>\<sigma> n. \<sigma>, \<sigma> \<Turnstile> P \<Longrightarrow> safe n (None :: ('i, 'a, nat) cont) C \<sigma> (\<Sigma> \<sigma>)"
        "\<And>\<sigma> \<sigma>'. \<sigma>, \<sigma>' \<Turnstile> P \<Longrightarrow> pair_sat (\<Sigma> \<sigma>) (\<Sigma> \<sigma>') Q"
    using assms(1) hoare_triple_validE by blast
  then have "pair_sat (\<Sigma> (s1, h1)) (\<Sigma> (s2, h2)) Q"
    using assms(2) by blast
  moreover have "\<And>n. safe n (None :: ('i, 'a, nat) cont) C (s1, h1) (\<Sigma> (s1, h1))"
    using always_sat_refl asm0(1) assms(2) by blast
  then show "\<And>\<sigma>' C'. red_rtrans C (s1, FractionalHeap.normalize (get_fh H1)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
  proof -
    fix \<sigma>' C'
    assume "red_rtrans C (s1, FractionalHeap.normalize (get_fh H1)) C' \<sigma>'"
    then show "\<not> aborts C' \<sigma>'"
      using safe_atomic[of C "(s1, FractionalHeap.normalize (get_fh H1))" C' \<sigma>' s1 "FractionalHeap.normalize (get_fh H1)" "fst \<sigma>'" "snd \<sigma>'"]
      by (metis \<open>\<And>n. safe n None C (s1, h1) (\<Sigma> (s1, h1))\<close> assms(3) denormalize_properties(4) prod.exhaust_sel)
  qed
  moreover have "\<And>n. safe n (None :: ('i, 'a, nat) cont) C (s2, h2) (\<Sigma> (s2, h2))"
    using always_sat_refl asm0(1) assms(2) sat_comm_aux by blast
  then show "\<And>\<sigma>' C'. red_rtrans C (s2, FractionalHeap.normalize (get_fh H2)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
  proof -
    fix \<sigma>' C'
    assume "red_rtrans C (s2, FractionalHeap.normalize (get_fh H2)) C' \<sigma>'"
    then show "\<not> aborts C' \<sigma>'"
      using safe_atomic[of C "(s2, FractionalHeap.normalize (get_fh H2))" C' \<sigma>' s2 "FractionalHeap.normalize (get_fh H2)" "fst \<sigma>'" "snd \<sigma>'"]
      by (metis \<open>\<And>n. safe n None C (s2, h2) (\<Sigma> (s2, h2))\<close> assms(4) denormalize_properties(4) prod.exhaust_sel)
  qed
  fix \<sigma>1'
  assume "red_rtrans C (s1, FractionalHeap.normalize (get_fh H1)) Cskip \<sigma>1'"
  then obtain h1' H1' where r1: "Some H1' = Some h1' \<oplus> Some hf1" "snd \<sigma>1' = FractionalHeap.normalize (get_fh H1')"
   "no_guard H1' \<and> full_ownership (get_fh H1')" "(fst \<sigma>1', h1') \<in> \<Sigma> (s1, h1)"
    using safe_atomic[of C "(s1, FractionalHeap.normalize (get_fh H1))" Cskip \<sigma>1' s1 _ "fst \<sigma>1'" "snd \<sigma>1'" h1 "\<Sigma> (s1, h1)" H1 hf1]
    by (metis \<open>\<And>n. safe n None C (s1, h1) (\<Sigma> (s1, h1))\<close> assms(3) denormalize_properties(4) surjective_pairing)
  fix \<sigma>2'
  assume "red_rtrans C (s2, FractionalHeap.normalize (get_fh H2)) Cskip \<sigma>2'"
  then obtain h2' H2' where r2: "Some H2' = Some h2' \<oplus> Some hf2" "snd \<sigma>2' = FractionalHeap.normalize (get_fh H2')"
   "no_guard H2' \<and> full_ownership (get_fh H2')" "(fst \<sigma>2', h2') \<in> \<Sigma> (s2, h2)"
    using safe_atomic[of C "(s2, FractionalHeap.normalize (get_fh H2))" Cskip \<sigma>2' s2 _ "fst \<sigma>2'" "snd \<sigma>2'" h2 "\<Sigma> (s2, h2)" H2 hf2]
    by (metis \<open>\<And>n. safe n None C (s2, h2) (\<Sigma> (s2, h2))\<close> assms(4) denormalize_properties(4) surjective_pairing)
  then have "(fst \<sigma>1', h1'), (fst \<sigma>2', h2') \<Turnstile> Q"
    using calculation(1) pair_satE r1(4) by blast
  then show "\<exists>h1' h2' H1' H2'.
          no_guard H1' \<and>
          full_ownership (get_fh H1') \<and>
          snd \<sigma>1' = FractionalHeap.normalize (get_fh H1') \<and>
          Some H1' = Some h1' \<oplus> Some hf1 \<and>
          no_guard H2' \<and>
          full_ownership (get_fh H2') \<and> snd \<sigma>2' = FractionalHeap.normalize (get_fh H2') \<and> Some H2' = Some h2' \<oplus> Some hf2 \<and> (fst \<sigma>1', h1'), (fst \<sigma>2', h2') \<Turnstile> Q"
    using r1 r2 by blast
qed

lemma neutral_add:
  "Some h = Some h \<oplus> Some (Map.empty, None, (\<lambda>_. None))"
proof -
  have "h ## (Map.empty, None, (\<lambda>_. None))"
    by (metis compatibleI compatible_fract_heapsI empty_heap_def fst_conv get_fh.elims get_gs.simps get_gu.simps option.distinct(1) snd_conv)
  then obtain x where "Some x = Some h \<oplus> Some (Map.empty, None, (\<lambda>_. None))"
    by simp
  moreover have "x = h"
    by (metis (no_types, lifting) addition_cancellative calculation decompose_guard_remove_easy fst_eqD get_gs.simps get_gu.simps no_guard_def no_guards_remove prod.sel(2) simpler_asso)
  ultimately show ?thesis by blast
qed

corollary safety_no_frame:
  assumes "hoare_triple_valid (None :: ('i, 'a, nat) cont) P C Q"
      and "(s1, H1), (s2, H2) \<Turnstile> P"

      and "full_ownership (get_fh H1) \<and> no_guard H1"
      and "full_ownership (get_fh H2) \<and> no_guard H2"

    shows "\<And>\<sigma>' C'. red_rtrans C (s1, normalize (get_fh H1)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
      and "\<And>\<sigma>' C'. red_rtrans C (s2, normalize (get_fh H2)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
      and "\<And>\<sigma>1' \<sigma>2'. red_rtrans C (s1, normalize (get_fh H1)) Cskip \<sigma>1'
  \<Longrightarrow> red_rtrans C (s2, normalize (get_fh H2)) Cskip \<sigma>2'
  \<Longrightarrow> (\<exists>H1' H2'. no_guard H1' \<and> full_ownership (get_fh H1') \<and> snd \<sigma>1' = normalize (get_fh H1')
      \<and> no_guard H2' \<and> full_ownership (get_fh H2') \<and> snd \<sigma>2' = normalize (get_fh H2')
      \<and> (fst \<sigma>1', H1'), (fst \<sigma>2', H2') \<Turnstile> Q)"
proof -
  have "Some H1 = Some H1 \<oplus> Some (Map.empty, None, (\<lambda>_. None))"
    using neutral_add by blast
  moreover have "Some H2 = Some H2 \<oplus> Some (Map.empty, None, (\<lambda>_. None))"
    using neutral_add by blast
  show "\<And>\<sigma>' C'. red_rtrans C (s1, FractionalHeap.normalize (get_fh H1)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
    using always_sat_refl_aux assms(1) assms(2) assms(3) calculation safety(2) by blast
  show "\<And>\<sigma>' C'. red_rtrans C (s2, FractionalHeap.normalize (get_fh H2)) C' \<sigma>' \<Longrightarrow> \<not> aborts C' \<sigma>'"
    using \<open>Some H2 = Some H2 \<oplus> Some (Map.empty, None, (\<lambda>_. None))\<close> assms(1) assms(2) assms(3) assms(4) calculation safety(2) by blast
  fix \<sigma>1' \<sigma>2'
  assume "red_rtrans C (s1, FractionalHeap.normalize (get_fh H1)) Cskip \<sigma>1'"
       "red_rtrans C (s2, FractionalHeap.normalize (get_fh H2)) Cskip \<sigma>2'"

  then obtain h1' h2' H1' H2' where asm0: "no_guard H1' \<and> full_ownership (get_fh H1') \<and> snd \<sigma>1' = normalize (get_fh H1') \<and> Some H1' = Some h1' \<oplus> Some (Map.empty, None, (\<lambda>_. None))
      \<and> no_guard H2' \<and> full_ownership (get_fh H2') \<and> snd \<sigma>2' = normalize (get_fh H2') \<and> Some H2' = Some h2' \<oplus> Some (Map.empty, None, (\<lambda>_. None))
      \<and> (fst \<sigma>1', h1'), (fst \<sigma>2', h2') \<Turnstile> Q"
    using  safety[of P C Q s1 H1 s2 H2 H1 "(Map.empty, None, (\<lambda>_. None))" H2 "(Map.empty, None, (\<lambda>_. None))"] assms
    by (metis (no_types, lifting) \<open>Some H2 = Some H2 \<oplus> Some (Map.empty, None, (\<lambda>_. None))\<close> calculation)
  then have "H1' = h1'"
    using addition_cancellative decompose_guard_remove_easy denormalize_properties(4) denormalize_properties(5)
    by (metis denormalize_def get_gs.simps get_gu.simps prod.exhaust_sel snd_conv)
  moreover have "H2' = h2'"
    by (metis asm0 denormalize_properties(4) denormalize_properties(5) fst_eqD get_fh.elims no_guard_and_no_heap no_guard_then_smaller_same)

  ultimately show "\<exists>H1' H2'.
          no_guard H1' \<and>
          full_ownership (get_fh H1') \<and>
          snd \<sigma>1' = FractionalHeap.normalize (get_fh H1') \<and>
          no_guard H2' \<and> full_ownership (get_fh H2') \<and> snd \<sigma>2' = FractionalHeap.normalize (get_fh H2') \<and> (fst \<sigma>1', H1'), (fst \<sigma>2', H2') \<Turnstile> Q"
    using asm0 by blast
qed

end
