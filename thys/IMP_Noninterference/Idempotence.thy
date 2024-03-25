(*  Title:       Information Flow Control via Stateful Intransitive Noninterference in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Idempotence of the auxiliary type system meant for loop bodies"

theory Idempotence
  imports Definitions
begin

text \<open>
\null

The purpose of this section is to prove that the auxiliary type system @{const [names_short]
noninterf.ctyping1} used to simulate the execution of loop bodies is idempotent, namely that if its
output for a given input is the pair composed of @{typ "state set"} @{term B} and @{typ "vname set"}
@{term Y}, then the same output is returned if @{term B} and @{term Y} are fed back into the type
system (lemma @{text ctyping1_idem}).
\<close>


subsection "Global context proofs"

lemma remdups_filter_last:
 "last [x\<leftarrow>remdups xs. P x] = last [x\<leftarrow>xs. P x]"
by (induction xs, auto simp: filter_empty_conv)

lemma remdups_append:
 "set xs \<subseteq> set ys \<Longrightarrow> remdups (xs @ ys) = remdups ys"
by (induction xs, simp_all)

lemma remdups_concat_1:
 "remdups (concat (remdups [])) = remdups (concat [])"
by simp

lemma remdups_concat_2:
 "remdups (concat (remdups xs)) = remdups (concat xs) \<Longrightarrow>
    remdups (concat (remdups (x # xs))) = remdups (concat (x # xs))"
by (simp, subst (2 3) remdups_append2 [symmetric], clarsimp,
 subst remdups_append, auto)

lemma remdups_concat:
 "remdups (concat (remdups xs)) = remdups (concat xs)"
by (induction xs, rule remdups_concat_1, rule remdups_concat_2)


subsection "Local context proofs"

context noninterf
begin


lemma ctyping1_seq_last:
 "foldl (;;) S xs = (\<lambda>x. let xs' = [T\<leftarrow>xs. T x \<noteq> None] in
    if xs' = [] then S x else last xs' x)"
by (rule ext, induction xs rule: rev_induct, auto simp: ctyping1_seq_def)

lemma ctyping1_seq_remdups:
 "foldl (;;) S (remdups xs) = foldl (;;) S xs"
by (simp add: Let_def ctyping1_seq_last, subst remdups_filter_last,
 simp add: remdups_filter [symmetric])

lemma ctyping1_seq_remdups_concat:
 "foldl (;;) S (concat (remdups xs)) = foldl (;;) S (concat xs)"
by (subst (1 2) ctyping1_seq_remdups [symmetric], simp add: remdups_concat)

lemma ctyping1_seq_eq:
  assumes A: "foldl (;;) (\<lambda>x. None) xs = foldl (;;) (\<lambda>x. None) ys"
  shows "foldl (;;) S xs = foldl (;;) S ys"
proof -
  have "\<forall>x. ([T\<leftarrow>xs. T x \<noteq> None] = [] \<longleftrightarrow> [T\<leftarrow>ys. T x \<noteq> None] = []) \<and>
    last [T\<leftarrow>xs. T x \<noteq> None] x = last [T\<leftarrow>ys. T x \<noteq> None] x"
    (is "\<forall>x. (?xs' x = [] \<longleftrightarrow> ?ys' x = []) \<and> _")
  proof
    fix x
    from A have "(if ?xs' x = [] then None else last (?xs' x) x) =
      (if ?ys' x = [] then None else last (?ys' x) x)"
      by (drule_tac fun_cong [where x = x], auto simp: ctyping1_seq_last)
    moreover have "?xs' x \<noteq> [] \<Longrightarrow> last (?xs' x) x \<noteq> None"
      by (drule last_in_set, simp)
    moreover have "?ys' x \<noteq> [] \<Longrightarrow> last (?ys' x) x \<noteq> None"
      by (drule last_in_set, simp)
    ultimately show "(?xs' x = [] \<longleftrightarrow> ?ys' x = []) \<and>
      last (?xs' x) x = last (?ys' x) x"
      by (auto split: if_split_asm)
  qed
  thus ?thesis
    by (auto simp: ctyping1_seq_last)
qed


lemma ctyping1_merge_aux_butlast:
 "\<lbrakk>ws \<in> A \<Squnion> B; butlast ws \<noteq> []\<rbrakk> \<Longrightarrow>
    snd (last (butlast ws)) = (\<not> snd (last ws))"
by (erule ctyping1_merge_aux.cases, simp_all)

lemma ctyping1_merge_aux_distinct:
 "ws \<in> A \<Squnion> B \<Longrightarrow> distinct ws"
by (induction rule: ctyping1_merge_aux.induct, simp_all)

lemma ctyping1_merge_aux_nonempty:
 "ws \<in> A \<Squnion> B \<Longrightarrow> ws \<noteq> []"
by (induction rule: ctyping1_merge_aux.induct, simp_all)

lemma ctyping1_merge_aux_item:
 "\<lbrakk>ws \<in> A \<Squnion> B; w \<in> set ws\<rbrakk> \<Longrightarrow> fst w \<in> (if snd w then A else B)"
by (induction rule: ctyping1_merge_aux.induct, auto)

lemma ctyping1_merge_aux_take_1 [elim]:
 "\<lbrakk>take n ws \<in> A \<Squnion> B; \<not> snd (last ws); xs \<in> A; (xs, True) \<notin> set ws\<rbrakk> \<Longrightarrow>
    take n ws @ take (n - length ws) [(xs, True)] \<in> A \<Squnion> B"
by (cases "n \<le> length ws", auto)

lemma ctyping1_merge_aux_take_2 [elim]:
 "\<lbrakk>take n ws \<in> A \<Squnion> B; snd (last ws); ys \<in> B; (ys, False) \<notin> set ws\<rbrakk> \<Longrightarrow>
    take n ws @ take (n - length ws) [(ys, False)] \<in> A \<Squnion> B"
by (cases "n \<le> length ws", auto)

lemma ctyping1_merge_aux_take:
 "\<lbrakk>ws \<in> A \<Squnion> B; 0 < n\<rbrakk> \<Longrightarrow> take n ws \<in> A \<Squnion> B"
by (induction rule: ctyping1_merge_aux.induct, auto)


lemma ctyping1_merge_aux_drop_1 [elim]:
  assumes
    A: "xs \<in> A" and
    B: "ys \<in> B"
  shows "drop n [(xs, True)] @ [(ys, False)] \<in> A \<Squnion> B"
proof -
  from A have "[(xs, True)] \<in> A \<Squnion> B" ..
  with B have "[(xs, True)] @ [(ys, False)] \<in> A \<Squnion> B"
    by fastforce
  with B show ?thesis
    by (cases n, auto)
qed

lemma ctyping1_merge_aux_drop_2 [elim]:
  assumes
    A: "xs \<in> A" and
    B: "ys \<in> B"
  shows "drop n [(ys, False)] @ [(xs, True)] \<in> A \<Squnion> B"
proof -
  from B have "[(ys, False)] \<in> A \<Squnion> B" ..
  with A have "[(ys, False)] @ [(xs, True)] \<in> A \<Squnion> B"
    by fastforce
  with A show ?thesis
    by (cases n, auto)
qed

lemma ctyping1_merge_aux_drop_3:
  assumes
    A: "\<And>xs v. (xs, True) \<notin> set (drop n ws) \<Longrightarrow>
      xs \<in> A \<Longrightarrow> v \<Longrightarrow> drop n ws @ [(xs, True)] \<in> A \<Squnion> B" and
    B: "xs \<in> A" and
    C: "ys \<in> B" and
    D: "(xs, True) \<notin> set ws" and
    E: "(ys, False) \<notin> set (drop n ws)"
  shows "drop n ws @ drop (n - length ws) [(xs, True)] @
    [(ys, False)] \<in> A \<Squnion> B"
proof -
  have "set (drop n ws) \<subseteq> set ws"
    by (rule set_drop_subset)
  hence "drop n ws @ [(xs, True)] \<in> A \<Squnion> B"
    using A and B and D by blast
  hence "(drop n ws @ [(xs, True)]) @ [(ys, False)] \<in> A \<Squnion> B"
    using C and E by fastforce
  thus ?thesis
    using C by (cases "n \<le> length ws", auto)
qed

lemma ctyping1_merge_aux_drop_4:
  assumes
    A: "\<And>ys v. (ys, False) \<notin> set (drop n ws) \<Longrightarrow>
      ys \<in> B \<Longrightarrow> \<not> v \<Longrightarrow> drop n ws @ [(ys, False)] \<in> A \<Squnion> B" and
    B: "ys \<in> B" and
    C: "xs \<in> A" and
    D: "(ys, False) \<notin> set ws" and
    E: "(xs, True) \<notin> set (drop n ws)"
  shows "drop n ws @ drop (n - length ws) [(ys, False)] @
    [(xs, True)] \<in> A \<Squnion> B"
proof -
  have "set (drop n ws) \<subseteq> set ws"
    by (rule set_drop_subset)
  hence "drop n ws @ [(ys, False)] \<in> A \<Squnion> B"
    using A and B and D by blast
  hence "(drop n ws @ [(ys, False)]) @ [(xs, True)] \<in> A \<Squnion> B"
    using C and E by fastforce
  thus ?thesis
    using C by (cases "n \<le> length ws", auto)
qed

lemma ctyping1_merge_aux_drop:
 "\<lbrakk>ws \<in> A \<Squnion> B; w \<notin> set (drop n ws);
    fst w \<in> (if snd w then A else B); snd w = (\<not> snd (last ws))\<rbrakk> \<Longrightarrow>
  drop n ws @ [w] \<in> A \<Squnion> B"
proof (induction arbitrary: w rule: ctyping1_merge_aux.induct)
  fix xs ws w
  show
   "\<lbrakk>ws \<in> A \<Squnion> B;
    \<And>w. w \<notin> set (drop n ws) \<Longrightarrow>
      fst w \<in> (if snd w then A else B) \<Longrightarrow>
      snd w = (\<not> snd (last ws)) \<Longrightarrow>
      drop n ws @ [w] \<in> A \<Squnion> B;
    \<not> snd (last ws);
    xs \<in> A;
    (xs, True) \<notin> set ws;
    w \<notin> set (drop n (ws @ [(xs, True)]));
    fst w \<in> (if snd w then A else B);
    snd w = (\<not> snd (last (ws @ [(xs, True)])))\<rbrakk> \<Longrightarrow>
      drop n (ws @ [(xs, True)]) @ [w] \<in> A \<Squnion> B"
    by (cases w, auto intro: ctyping1_merge_aux_drop_3)
next
  fix ys ws w
  show
   "\<lbrakk>ws \<in> A \<Squnion> B;
    \<And>w. w \<notin> set (drop n ws) \<Longrightarrow>
      fst w \<in> (if snd w then A else B) \<Longrightarrow>
      snd w = (\<not> snd (last ws)) \<Longrightarrow>
      drop n ws @ [w] \<in> A \<Squnion> B;
    snd (last ws);
    ys \<in> B;
    (ys, False) \<notin> set ws;
    w \<notin> set (drop n (ws @ [(ys, False)]));
    fst w \<in> (if snd w then A else B);
    snd w = (\<not> snd (last (ws @ [(ys, False)])))\<rbrakk> \<Longrightarrow>
      drop n (ws @ [(ys, False)]) @ [w] \<in> A \<Squnion> B"
    by (cases w, auto intro: ctyping1_merge_aux_drop_4)
qed auto


lemma ctyping1_merge_aux_closed_1:
  assumes
    A: "\<forall>vs. length vs \<le> length us \<longrightarrow>
      (\<forall>ls rs. vs = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
        (\<exists>ws \<in> A \<Squnion> B. foldl (;;) (\<lambda>x. None) (concat (map fst ws)) =
          foldl (;;) (\<lambda>x. None) (concat (map fst (ls @ rs))) \<and>
        length ws \<le> length (ls @ rs) \<and> snd (last ws) = snd (last rs)))"
      (is "\<forall>_. _ \<longrightarrow> (\<forall>ls rs. _ \<longrightarrow> _ \<longrightarrow> _ \<longrightarrow> (\<exists>ws \<in> _. ?P ws ls rs))") and
    B: "us \<in> A \<Squnion> B" and
    C: "fst v \<in> (if snd v then A else B)" and
    D: "snd v = (\<not> snd (last us))"
  shows "\<exists>ws \<in> A \<Squnion> B. foldl (;;) (\<lambda>x. None) (concat (map fst ws)) =
    foldl (;;) (\<lambda>x. None) (concat (map fst (us @ [v]))) \<and>
    length ws \<le> Suc (length us) \<and> snd (last ws) = snd v"
proof (cases "v \<in> set us", cases "hd us = v")
  assume E: "hd us = v"
  moreover have "distinct us"
    using B by (rule ctyping1_merge_aux_distinct)
  ultimately have "v \<notin> set (drop (Suc 0) us)"
    by (cases us, simp_all)
  with B have "drop (Suc 0) us @ [v] \<in> A \<Squnion> B"
    (is "?ws \<in> _")
    using C and D by (rule ctyping1_merge_aux_drop)
  moreover have "foldl (;;) (\<lambda>x. None) (concat (map fst ?ws)) =
    foldl (;;) (\<lambda>x. None) (concat (map fst (us @ [v])))"
    using E by (cases us, simp, subst (1 2) ctyping1_seq_remdups_concat
     [symmetric], simp)
  ultimately show ?thesis
    by fastforce
next
  assume "v \<in> set us"
  then obtain ls and rs where E: "us = ls @ v # rs \<and> v \<notin> set rs"
    by (blast dest: split_list_last)
  moreover assume "hd us \<noteq> v"
  ultimately have "ls \<noteq> []"
    by (cases ls, simp_all)
  hence "take (length ls) us \<in> A \<Squnion> B"
    by (simp add: ctyping1_merge_aux_take B)
  moreover have "v \<notin> set (drop (Suc (length ls)) us)"
    using E by simp
  with B have "drop (Suc (length ls)) us @ [v] \<in> A \<Squnion> B"
    using C and D by (rule ctyping1_merge_aux_drop)
  ultimately have "\<exists>ws \<in> A \<Squnion> B. ?P ws ls (rs @ [v])"
    using A and E by (drule_tac spec [of _ "ls @ rs @ [v]"],
     simp, drule_tac spec [of _ ls], simp)
  moreover have "foldl (;;) (\<lambda>x. None) (concat (map fst (ls @ rs @ [v]))) =
    foldl (;;) (\<lambda>x. None) (concat (map fst (us @ [v])))"
    using E by (subst (1 2) ctyping1_seq_remdups_concat [symmetric],
     simp, subst (1 2) remdups_append2 [symmetric], simp)
  ultimately show ?thesis
    using E by auto
next
  assume E: "v \<notin> set us"
  show ?thesis
  proof (rule bexI [of _ "us @ [v]"])
    show "foldl (;;) (\<lambda>x. None) (concat (map fst (us @ [v]))) =
      foldl (;;) (\<lambda>x. None) (concat (map fst (us @ [v]))) \<and>
      length (us @ [v]) \<le> Suc (length us) \<and>
      snd (last (us @ [v])) = snd v"
      by simp
  next
    from B and C and D and E show "us @ [v] \<in> A \<Squnion> B"
      by (cases v, cases "snd (last us)", auto)
  qed
qed

lemma ctyping1_merge_aux_closed:
  assumes
    A: "\<forall>xs \<in> A. \<forall>ys \<in> A. \<exists>zs \<in> A.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)" and
    B: "\<forall>xs \<in> B. \<forall>ys \<in> B. \<exists>zs \<in> B.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)"
  shows "\<lbrakk>us \<in> A \<Squnion> B; vs \<in> A \<Squnion> B\<rbrakk> \<Longrightarrow>
    \<exists>ws \<in> A \<Squnion> B. foldl (;;) (\<lambda>x. None) (concat (map fst ws)) =
      foldl (;;) (\<lambda>x. None) (concat (map fst (us @ vs))) \<and>
    length ws \<le> length (us @ vs) \<and> snd (last ws) = snd (last vs)"
    (is "\<lbrakk>_; _\<rbrakk> \<Longrightarrow> \<exists>ws \<in> _. ?P ws us vs")
proof (induction "us @ vs" arbitrary: us vs rule: length_induct)
  fix us vs
  let ?f = "foldl (;;) (\<lambda>x. None)"
  assume
    C: "\<forall>ts. length ts < length (us @ vs) \<longrightarrow>
      (\<forall>ls rs. ts = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
        (\<exists>ws \<in> A \<Squnion> B. ?f (concat (map fst ws)) =
          ?f (concat (map fst (ls @ rs))) \<and>
        length ws \<le> length (ls @ rs) \<and> snd (last ws) = snd (last rs)))"
      (is "\<forall>_. _ \<longrightarrow> (\<forall>ls rs. _ \<longrightarrow> _ \<longrightarrow> _ \<longrightarrow> (\<exists>ws \<in> _. ?Q ws ls rs))") and
    D: "us \<in> A \<Squnion> B" and
    E: "vs \<in> A \<Squnion> B"
  {
    fix vs' v
    assume F: "vs = vs' @ [v]"
    have "\<exists>ws \<in> A \<Squnion> B. ?f (concat (map fst ws)) =
      ?f (concat (map fst (us @ vs' @ [v]))) \<and>
      length ws \<le> Suc (length us + length vs') \<and> snd (last ws) = snd v"
    proof (cases vs', cases "(\<not> snd (last us)) = snd v")
      assume "vs' = []" and "(\<not> snd (last us)) = snd v"
      thus ?thesis
        using ctyping1_merge_aux_closed_1 [OF _ D] and
         ctyping1_merge_aux_item [OF E] and C and F
         by (auto simp: less_Suc_eq_le)
    next
      have G: "us \<noteq> []"
        using D by (rule ctyping1_merge_aux_nonempty)
      hence "fst (last us) \<in> (if snd (last us) then A else B)"
        using ctyping1_merge_aux_item and D by auto
      moreover assume H: "(\<not> snd (last us)) \<noteq> snd v"
      ultimately have "fst (last us) \<in> (if snd v then A else B)"
        by simp
      moreover have "fst v \<in> (if snd v then A else B)"
        using ctyping1_merge_aux_item and E and F by auto
      ultimately have "\<exists>zs \<in> if snd v
        then A else B. ?f zs = ?f (concat (map fst [last us, v]))"
        (is "\<exists>zs \<in> _. ?R zs")
        using A and B by auto
      then obtain zs where
        I: "zs \<in> (if snd v then A else B)" and J: "?R zs" ..
      let ?w = "(zs, snd v)"
      assume K: "vs' = []"
      {
        fix us' u
        assume Cons: "butlast us = u # us'"
        hence L: "snd v = (\<not> snd (last (butlast us)))"
          using D and H by (drule_tac ctyping1_merge_aux_butlast, simp_all)
        let ?S = "?f (concat (map fst (butlast us)))"
        have "take (length (butlast us)) us \<in> A \<Squnion> B"
          using Cons by (auto intro: ctyping1_merge_aux_take [OF D])
        hence M: "butlast us \<in> A \<Squnion> B"
          by (subst (asm) (2) append_butlast_last_id [OF G, symmetric], simp)
        have N: "\<forall>ts. length ts < length (butlast us @ [last us, v]) \<longrightarrow>
          (\<forall>ls rs. ts = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
            (\<exists>ws \<in> A \<Squnion> B. ?Q ws ls rs))"
          using C and F and K by (subst (asm) append_butlast_last_id
           [OF G, symmetric], simp)
        have "\<exists>ws \<in> A \<Squnion> B. ?f (concat (map fst ws)) =
          ?f (concat (map fst (butlast us @ [?w]))) \<and>
          length ws \<le> Suc (length (butlast us)) \<and> snd (last ws) = snd ?w"
        proof (rule ctyping1_merge_aux_closed_1)
          show "\<forall>ts. length ts \<le> length (butlast us) \<longrightarrow>
            (\<forall>ls rs. ts = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
              (\<exists>ws \<in> A \<Squnion> B. ?Q ws ls rs))"
            using N by force
        next
          from M show "butlast us \<in> A \<Squnion> B" .
        next
          show "fst (zs, snd v) \<in> (if snd (zs, snd v) then A else B)"
            using I by simp
        next
          show "snd (zs, snd v) = (\<not> snd (last (butlast us)))"
            using L by simp
        qed
        moreover have "foldl (;;) ?S zs =
          foldl (;;) ?S (concat (map fst [last us, v]))"
          using J by (rule ctyping1_seq_eq)
        ultimately have "\<exists>ws \<in> A \<Squnion> B. ?f (concat (map fst ws)) =
          ?f (concat (map fst ((butlast us @ [last us]) @ [v]))) \<and>
          length ws \<le> Suc (length us) \<and> snd (last ws) = snd v"
          by auto
      }
      with K and I and J show ?thesis
        by (simp, subst append_butlast_last_id [OF G, symmetric],
         cases "butlast us", (force split: if_split_asm)+)
    next
      case Cons
      hence "take (length vs') vs \<in> A \<Squnion> B"
        by (auto intro: ctyping1_merge_aux_take [OF E])
      hence "vs' \<in> A \<Squnion> B"
        using F by simp
      then obtain ws where G: "ws \<in> A \<Squnion> B" and H: "?Q ws us vs'"
        using C and D and F by force
      have I: "\<forall>ts. length ts \<le> length ws \<longrightarrow>
          (\<forall>ls rs. ts = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
            (\<exists>ws \<in> A \<Squnion> B. ?Q ws ls rs))"
      proof (rule allI, rule impI)
        fix ts :: "(state_upd list \<times> bool) list"
        assume J: "length ts \<le> length ws"
        show "\<forall>ls rs. ts = ls @ rs \<longrightarrow> ls \<in> A \<Squnion> B \<longrightarrow> rs \<in> A \<Squnion> B \<longrightarrow>
          (\<exists>ws \<in> A \<Squnion> B. ?Q ws ls rs)"
        proof (rule spec [OF C, THEN mp])
          show "length ts < length (us @ vs)"
            using F and H and J by simp
        qed
      qed
      hence J: "snd (last (butlast vs)) = (\<not> snd (last vs))"
        by (metis E F Cons butlast_snoc ctyping1_merge_aux_butlast
         list.distinct(1))
      have "\<exists>ws' \<in> A \<Squnion> B. ?f (concat (map fst ws')) =
        ?f (concat (map fst (ws @ [v]))) \<and>
        length ws' \<le> Suc (length ws) \<and> snd (last ws') = snd v"
      proof (rule ctyping1_merge_aux_closed_1 [OF I G])
        show "fst v \<in> (if snd v then A else B)"
          by (rule ctyping1_merge_aux_item [OF E], simp add: F)
      next
        show "snd v = (\<not> snd (last ws))"
          using F and H and J by simp
      qed
      thus ?thesis
        using H by auto
    qed
  }
  note F = this
  show "\<exists>ws \<in> A \<Squnion> B. ?P ws us vs"
  proof (rule rev_cases [of vs])
    assume "vs = []"
    thus ?thesis
      by (simp add: ctyping1_merge_aux_nonempty [OF E])
  next
    fix vs' v
    assume "vs = vs' @ [v]"
    thus ?thesis
      using F by simp
  qed
qed


lemma ctyping1_merge_closed:
  assumes
    A: "\<forall>xs \<in> A. \<forall>ys \<in> A. \<exists>zs \<in> A.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)" and
    B: "\<forall>xs \<in> B. \<forall>ys \<in> B. \<exists>zs \<in> B.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)" and
    C: "xs \<in> A \<squnion> B" and
    D: "ys \<in> A \<squnion> B"
  shows "\<exists>zs \<in> A \<squnion> B. foldl (;;) (\<lambda>x. None) zs =
    foldl (;;) (\<lambda>x. None) (xs @ ys)"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  obtain us where "us \<in> A \<Squnion> B" and
    E: "xs = concat (map fst us)"
    using C by (auto simp: ctyping1_merge_def)
  moreover obtain vs where "vs \<in> A \<Squnion> B" and
    F: "ys = concat (map fst vs)"
    using D by (auto simp: ctyping1_merge_def)
  ultimately have "\<exists>ws \<in> A \<Squnion> B. ?f (concat (map fst ws)) =
    ?f (concat (map fst (us @ vs))) \<and>
    length ws \<le> length (us @ vs) \<and> snd (last ws) = snd (last vs)"
    using A and B by (blast intro: ctyping1_merge_aux_closed)
  then obtain ws where "ws \<in> A \<Squnion> B" and
   "?f (concat (map fst ws)) = ?f (xs @ ys)"
    using E and F by auto
  thus ?thesis
    by (auto simp: ctyping1_merge_def)
qed

lemma ctyping1_merge_append_closed:
  assumes
    A: "\<forall>xs \<in> A. \<forall>ys \<in> A. \<exists>zs \<in> A.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)" and
    B: "\<forall>xs \<in> B. \<forall>ys \<in> B. \<exists>zs \<in> B.
      foldl (;;) (\<lambda>x. None) zs = foldl (;;) (\<lambda>x. None) (xs @ ys)" and
    C: "xs \<in> A \<squnion>\<^sub>@ B" and
    D: "ys \<in> A \<squnion>\<^sub>@ B"
  shows "\<exists>zs \<in> A \<squnion>\<^sub>@ B. foldl (;;) (\<lambda>x. None) zs =
    foldl (;;) (\<lambda>x. None) (xs @ ys)"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  {
    assume E: "card B = Suc 0"
    moreover from C and this obtain as bs where
     "xs = as @ bs \<and> as \<in> A \<and> bs \<in> B"
      by (auto simp: ctyping1_append_def ctyping1_merge_append_def)
    moreover from D and E obtain as' bs' where
     "ys = as' @ bs' \<and> as' \<in> A \<and> bs' \<in> B"
      by (auto simp: ctyping1_append_def ctyping1_merge_append_def)
    ultimately have F: "xs @ ys = as @ bs @ as' @ bs \<and>
      {as, as'} \<subseteq> A \<and> bs \<in> B"
      by (auto simp: card_1_singleton_iff)
    hence "?f (xs @ ys) = ?f (remdups (as @ remdups (bs @ as' @ bs)))"
      by (simp add: ctyping1_seq_remdups)
    also have "\<dots> = ?f (remdups (as @ remdups (as' @ bs)))"
      by (simp add: remdups_append)
    finally have G: "?f (xs @ ys) = ?f (as @ as' @ bs)"
      by (simp add: ctyping1_seq_remdups)
    obtain as'' where H: "as'' \<in> A" and I: "?f as'' = ?f (as @ as')"
      using A and F by auto
    have "\<exists>zs \<in> A @ B. ?f zs = ?f (xs @ ys)"
    proof (rule bexI [of _ "as'' @ bs"])
      show "foldl (;;) (\<lambda>x. None) (as'' @ bs) =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using G and I by simp
    next
      show "as'' @ bs \<in> A @ B"
        using F and H by (auto simp: ctyping1_append_def)
    qed
  }
  moreover {
    fix n
    assume E: "card B \<noteq> Suc 0"
    moreover from C and this obtain ws bs where
     "xs = ws @ bs \<and> ws \<in> A \<squnion> B \<and> bs \<in> B"
      by (auto simp: ctyping1_append_def ctyping1_merge_append_def)
    moreover from D and E obtain ws' bs' where
     "ys = ws' @ bs' \<and> ws' \<in> A \<squnion> B \<and> bs' \<in> B"
      by (auto simp: ctyping1_append_def ctyping1_merge_append_def)
    ultimately have F: "xs @ ys = ws @ bs @ ws' @ bs' \<and>
      {ws, ws'} \<subseteq> A \<squnion> B \<and> {bs, bs'} \<subseteq> B"
      by simp
    hence "[(bs, False)] \<in> A \<Squnion> B"
      by blast
    hence G: "bs \<in> A \<squnion> B"
      by (force simp: ctyping1_merge_def)
    have "\<exists>vs \<in> A \<squnion> B. ?f vs = ?f (ws @ bs)"
      (is "\<exists>vs \<in> _. ?P vs ws bs")
    proof (rule ctyping1_merge_closed)
      show "\<forall>xs \<in> A. \<forall>ys \<in> A. \<exists>zs \<in> A. foldl (;;) (\<lambda>x. None) zs =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using A by simp
    next
      show "\<forall>xs \<in> B. \<forall>ys \<in> B. \<exists>zs \<in> B. foldl (;;) (\<lambda>x. None) zs =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using B by simp
    next
      show "ws \<in> A \<squnion> B"
        using F by simp
    next
      from G show "bs \<in> A \<squnion> B" .
    qed
    then obtain vs where H: "vs \<in> A \<squnion> B" and I: "?P vs ws bs" ..
    have "\<exists>vs' \<in> A \<squnion> B. ?P vs' vs ws'"
    proof (rule ctyping1_merge_closed)
      show "\<forall>xs \<in> A. \<forall>ys \<in> A. \<exists>zs \<in> A. foldl (;;) (\<lambda>x. None) zs =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using A by simp
    next
      show "\<forall>xs \<in> B. \<forall>ys \<in> B. \<exists>zs \<in> B. foldl (;;) (\<lambda>x. None) zs =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using B by simp
    next
      from H show "vs \<in> A \<squnion> B" .
    next
      show "ws' \<in> A \<squnion> B"
        using F by simp
    qed
    then obtain vs' where J: "vs' \<in> A \<squnion> B" and K: "?P vs' vs ws'" ..
    have "\<exists>zs \<in> A \<squnion> B @ B. ?f zs = ?f (xs @ ys)"
    proof (rule bexI [of _ "vs' @ bs'"])
      show "foldl (;;) (\<lambda>x. None) (vs' @ bs') =
        foldl (;;) (\<lambda>x. None) (xs @ ys)"
        using F and I and K by simp
    next
      show "vs' @ bs' \<in> A \<squnion> B @ B"
        using F and J by (auto simp: ctyping1_append_def)
    qed
  }
  ultimately show ?thesis
    using A and B and C and D by (auto simp: ctyping1_merge_append_def)
qed

lemma ctyping1_aux_closed:
 "\<lbrakk>xs \<in> \<turnstile> c; ys \<in> \<turnstile> c\<rbrakk> \<Longrightarrow> \<exists>zs \<in> \<turnstile> c. foldl (;;) (\<lambda>x. None) zs =
    foldl (;;) (\<lambda>x. None) (xs @ ys)"
by (induction c arbitrary: xs ys, auto
 intro: ctyping1_merge_closed ctyping1_merge_append_closed
 simp: Let_def ctyping1_seq_def simp del: foldl_append)


lemma ctyping1_idem_1:
  assumes
    A: "s \<in> A" and
    B: "xs \<in> \<turnstile> c" and
    C: "ys \<in> \<turnstile> c"
  shows "\<exists>f r.
    (\<exists>t.
      (\<lambda>x. case foldl (;;) (\<lambda>x. None) ys x of
        None \<Rightarrow> case foldl (;;) (\<lambda>x. None) xs x of
          None \<Rightarrow> s x | Some None \<Rightarrow> t' x | Some (Some i) \<Rightarrow> i |
        Some None \<Rightarrow> t'' x | Some (Some i) \<Rightarrow> i) =
      (\<lambda>x. case f x of
        None \<Rightarrow> r x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>zs. f = foldl (;;) (\<lambda>x. None) zs \<and> zs \<in> \<turnstile> c) \<and>
    r \<in> A"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?t = "\<lambda>x. case ?f ys x of
    None \<Rightarrow> case ?f xs x of Some None \<Rightarrow> t' x | _ \<Rightarrow> (0 :: val) |
    Some None \<Rightarrow> t'' x | _ \<Rightarrow> 0"
  have "\<exists>zs \<in> \<turnstile> c. ?f zs = ?f (xs @ ys)"
    using B and C by (rule ctyping1_aux_closed)
  then obtain zs where "zs \<in> \<turnstile> c" and "?f zs = ?f (xs @ ys)" ..
  with A show ?thesis
    by (rule_tac exI [of _ "?f zs"], rule_tac exI [of _ s],
     rule_tac conjI, rule_tac exI [of _ ?t], fastforce dest: last_in_set
     simp: Let_def ctyping1_seq_last split: option.split, blast)
qed

lemma ctyping1_idem_2:
  assumes
    A: "s \<in> A" and
    B: "xs \<in> \<turnstile> c"
  shows "\<exists>f r.
    (\<exists>t.
      (\<lambda>x. case foldl (;;) (\<lambda>x. None) xs x of
        None \<Rightarrow> s x | Some None \<Rightarrow> t' x | Some (Some i) \<Rightarrow> i) =
      (\<lambda>x. case f x of
        None \<Rightarrow> r x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
    (\<exists>xs. f = foldl (;;) (\<lambda>x. None) xs \<and> xs \<in> \<turnstile> c) \<and>
    (\<exists>f s.
      (\<exists>t. r = (\<lambda>x. case f x of
        None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i)) \<and>
      (\<exists>xs. f = foldl (;;) (\<lambda>x. None) xs \<and> xs \<in> \<turnstile> c) \<and>
      s \<in> A)"
proof -
  let ?f = "foldl (;;) (\<lambda>x. None)"
  let ?g = "\<lambda>f s t x. case f x of
    None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i"
  show ?thesis
    by (rule exI [of _ "?f xs"], rule exI [of _ "?g (?f xs) s t'"],
     (fastforce simp: A B split: option.split)+)
qed

lemma ctyping1_idem:
 "\<turnstile> c (\<subseteq> A, X) = (B, Y) \<Longrightarrow> \<turnstile> c (\<subseteq> B, Y) = (B, Y)"
by (cases "A = {}", auto simp: ctyping1_def
 intro: ctyping1_idem_1 ctyping1_idem_2)

end

end
