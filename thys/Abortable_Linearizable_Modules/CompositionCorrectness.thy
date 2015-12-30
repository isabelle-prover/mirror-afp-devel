(*Author: Giuliano Losa *)

section {* Proof that the composition of two instances of the ALM automaton behaves like a single instance of the ALM automaton*}

theory CompositionCorrectness
imports ALM
begin

declare  split_if_asm [split]
declare  Let_def [simp]

subsection {*A case split useful in the proofs*}

definition  in_trans_cases_fun :: "nat => nat => (ALM_state * ALM_state) => (ALM_state * ALM_state) => bool" 
  -- {*Helper function used to decompose proofs*}
  where 
"in_trans_cases_fun == % id1 id2 s t . 
  (EX ca ra. (fst s, Invoke ca ra, fst t) : ALM_trans 0 id1 & (snd s, Invoke ca ra, snd t) : ALM_trans id1 id2)
  | (EX ca h ra. (fst s, Switch ca id1 h ra, fst t) : ALM_trans 0 id1 & (snd s, Switch ca id1 h ra, snd t) : ALM_trans id1 id2)
  | (EX c id' h. fst t = fst s & (snd s, Commit c id' h, snd t) : ALM_trans id1 id2 & id1 <= id' & id' < id2)
  | (EX c h r. fst t = fst s & (snd s, Switch c id2 h r, snd t) : ALM_trans id1 id2)
  | (EX h . fst t = fst s & (snd s, Linearize id1 h, snd t) : ALM_trans id1 id2)
  | (fst t = fst s & (snd s, Abort id1, snd t) : ALM_trans id1 id2)
  | (EX h. fst t = fst s & (snd s, Initialize id1 h, snd t) : ALM_trans id1 id2)
  | (EX ca ta ra. (fst s, Switch ca 0 ta ra, fst t) : ALM_trans 0 id1 & snd t = snd s)
  | (EX ca id' h. (fst s, Commit ca id' h, fst t) : ALM_trans 0 id1 & snd t = snd s & id' < id1)
  | (EX h . (fst s, Linearize 0 h, fst t) : ALM_trans 0 id1 & snd t = snd s)
  | (EX h. (fst s, Initialize 0 h, fst t) : ALM_trans 0 id1 & snd t = snd s)
  | ((fst s, Abort 0, fst t) : ALM_trans 0 id1 & snd t = snd s)"

lemma  composeALMsE:
  -- {*A rule for decomposing proofs*}
  assumes "id1 ~= 0" and "id1 < id2" and in_trans_comp:"s \<midarrow>(a::ALM_action)\<midarrow>composeALMs id1 id2\<rightarrow> t"
  shows decomp: "in_trans_cases_fun id1 id2 s t"
proof -
  from in_trans_comp and `id1 ~= 0` and `id1 < id2`
  have "a : {act . EX c r h id' . 0 <= id' & id' < id2 & (
      act = Invoke c r 
      | act : {Switch c 0 h r, Switch c id1 h r, Switch c id2 h r}
      | act : {Linearize 0 h, Linearize id1 h}
      | act : {Initialize 0 h, Initialize id1 h}
      | act : {Abort 0, Abort id1}
      | act : {Commit c id' h}
     )}" by (auto simp add: composeALMs_def trans_of_def hide_def ALM_ioa_def par_def actions_def asig_inputs_def asig_outputs_def asig_internals_def asig_of_def ALM_asig_def)
  with this obtain c r h id' where "0 <= id' & id' < id2 & a : { act . 
      act = Invoke c r 
      | act : {Switch c 0 h r, Switch c id1 h r, Switch c id2 h r}
      | act : {Linearize 0 h, Linearize id1 h}
      | act : {Initialize 0 h, Initialize id1 h}
      | act : {Abort 0, Abort id1}
      | act : {Commit c id' h}
     }" by auto
  moreover from in_trans_comp and `id1 ~= 0` and `id1 < id2` 
  have
    "(a = Linearize 0 h | a = Abort 0 | a = Initialize 0 h | a = Switch c 0 h r | (a = Commit c id' h & id' < id1)) \<Longrightarrow> ((fst s, a, fst t) : ALM_trans 0 id1 & snd s = snd t)"
    and
    "(a = Linearize id1 h | a = Abort id1 | a = Initialize id1 h | a = Switch c id2 h r | (a = Commit c id' h & id1 <= id' & id' < id2)) \<Longrightarrow> (fst s = fst t & (snd s, a, snd t) : ALM_trans id1 id2)"
    and 
    "(a = Switch c id1 h r | a = Invoke c r) \<Longrightarrow> ((fst s, a, fst t) : ALM_trans 0 id1 & (snd s, a, snd t) : ALM_trans id1 id2)" 
    by (auto simp add: composeALMs_def trans_of_def hide_def ALM_ioa_def par_def actions_def asig_inputs_def asig_outputs_def asig_internals_def asig_of_def ALM_asig_def)
  ultimately show ?thesis unfolding in_trans_cases_fun_def apply simp by(metis linorder_not_less)
qed

lemma  my_rule:"[|id1 \<noteq> 0; id1 < id2; s \<midarrow>a\<midarrow>composeALMs id1 id2\<rightarrow> t; [|in_trans_cases_fun id1 id2 s t|] ==> P|]  ==> P"  by (auto intro: composeALMsE[where s="s" and t="t" and a="a"])
lemma  my_rule2:"[|0 < id1; id1 < id2; s \<midarrow>a\<midarrow>composeALMs id1 id2\<rightarrow> t; [|in_trans_cases_fun id1 id2 s t|] ==> P|]  ==> P"  by (auto intro: composeALMsE[where s="s" and t="t" and a="a"])

subsection {*Invariants of a single ALM instance*}

definition P1a :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*In ALM 1, a pending request of client c has client c as sender*}
  "P1a == % s . let s1 = fst s; s2 = snd s in
               ALL c . phase s1 c \<in> {Pending, Aborted} --> request_snd (pending s1 c) = c"

definition P1b :: "(ALM_state * ALM_state) \<Rightarrow> bool"
  where
  -- {*In ALM 2, a pending request of client c has client c as sender*}
  "P1b == % s . let s1 = fst s; s2 = snd s in
               ALL c . phase s2 c \<noteq> Sleep --> request_snd (pending s2 c) = c"

definition P2 :: "(ALM_state * ALM_state) \<Rightarrow> bool" where
  "P2 == % s . let s1 = fst s; s2 = snd s in
       (\<forall> c . phase s2 c = Sleep) \<longrightarrow> (\<not> initialized s2 \<and> hist s2 = [])"

definition P3 :: "(ALM_state * ALM_state) \<Rightarrow> bool" where
  "P3 == % s . let s1 = fst s; s2 = snd s in
        \<forall> c . (phase s2 c = Ready \<longrightarrow> initialized s2)"

definition P4 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*The set of init histories of ALM 2 is empty when no client ever invoked anything*}
  "P4 == % s . let s1 = fst s; s2 = snd s in
      (\<forall> c . phase s2 c = Sleep) = (initHists s2 = {})"

definition P5 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*In ALM 1 a client never sleeps*}
  where
  "P5 == % s . let s1 = fst s; s2 = snd s in
       \<forall> c . phase s1 c \<noteq> Sleep"

subsection {*Invariants of the composition of two ALM instances*}

definition P6 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*Non-interference accross instances*}
  where
  "P6 == % s . let s1 = fst s; s2 = snd s in 
                (~ aborted s1 --> (ALL c . phase s2 c = Sleep)) & (ALL c . phase s1 c ~= Aborted = (phase s2 c = Sleep))"

definition P7 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*Before initialization of the ALM 2, pending requests are the same as in ALM 1 and no new requests may be accepted (phase is not Ready)*}
  where
  "P7 == % s . let s1 = fst s; s2 = snd s in
               ALL c . phase s1 c = Aborted \<and> \<not> initialized s2 \<longrightarrow> (pending s2 c = pending s1 c \<and> phase s2 c \<in> {Pending, Aborted})"

definition P8 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*Init histories of ALM 2 are built from the history of ALM 1 plus pending requests of ALM 1*}
  where
  "P8 == % s . let s1 = fst s; s2 = snd s in
               \<forall> h \<in> initHists s2 . h \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))"

definition P9 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*ALM 2 does not abort before ALM 1 aborts*}
  where
  "P9 == % s . let s1 = fst s; s2 = snd s in
              aborted s2 \<longrightarrow> aborted s1"

definition P10 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  -- {*ALM 1 is always initialized and when ALM 2 is not initialized its history is empty*}
  where
  "P10 == % s . let s1 = fst s; s2 = snd s in
              initialized s1 \<and> (\<not> initialized s2 \<longrightarrow> (hist s2 = []))"

definition P11 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*After ALM 2 has been invoked and before it is initialized, any request found in init histories after their longest common prefix is pending in ALM 1*}
  "P11 == % s . let s1 = fst s; s2 = snd s in
       ((\<exists> c . phase s2 c \<noteq> Sleep) \<and> \<not> initialized s2) \<longrightarrow> initValidReqs s2 \<subseteq> pendingReqs s1"

definition P12:: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*After ALM 2 has been invoked and before it is initialized, the longest common prefix of the init histories of ALM 2 is buit from appending a set of request pending in ALM 1 to the history of ALM 1*}
  "P12 == % s . let s1 = fst s; s2 = snd s in
       (\<exists> c . phase s2 c \<noteq> Sleep) \<longrightarrow> (\<exists> rs . l_c_p (initHists s2) = rs @ (hist s1) \<and> set rs \<subseteq> pendingReqs s1 \<and> distinct rs)"

definition P13 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*After ALM 2 has been invoked and before it is initialized, any history that may be chosen at initialization is a valid linearization of the concurrent history of ALM 1*}
  "P13 == % s . let s1 = fst s; s2 = snd s in
       ((\<exists> c . phase s2 c \<noteq> Sleep) \<and> \<not> initialized s2) \<longrightarrow> postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2)) \<subseteq> postfix_all (hist s1) (linearizations (pendingReqs s1))"

definition P14 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*The history of ALM 1 is a postfix of the history of ALM 2 and requests appearing in ALM 2 after the history of ALM 1 are not in the history of ALM 1*}
  "P14 == % s . let s1 = fst s; s2 = snd s in
       (hist s2 \<noteq> [] \<or> initialized s2) \<longrightarrow> (\<exists> rs . 
          hist s2 = rs @ (hist s1) 
          \<and> set rs \<inter> set (hist s1) = {})"

definition P15 :: "(ALM_state * ALM_state) \<Rightarrow> bool" 
  where
  -- {*A client that hasn't yet invoked ALM 2 has no request commited in ALM 2 except for its pending request*}
  "P15 == % s . let s1 = fst s; s2 = snd s in
       \<forall> r . let c = request_snd r in phase s2 c = Sleep \<and> r \<in> set (hist s2) \<longrightarrow> (r \<in> set (hist s1) \<or> r \<in> pendingReqs s1)"

subsection {*Proofs of invariance*}

lemma invariant_imp: "\<lbrakk>invariant ioa P; \<forall> s . P s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow> invariant ioa Q"
by (simp add:invariant_def)

declare  phase.split [split]
declare  phase.split_asm [split]
declare  ALM_action.split [split]
declare  ALM_action.split_asm [split]

lemma dropWhile_lemma: "\<forall> ys . xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys \<longrightarrow> dropWhile (\<lambda> x' . x' \<noteq> x) xs = zs"
  -- {*A useful lemma about truncating histories*}
proof  (induct xs, force)
  fix a xs
  assume "\<forall> ys . xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys \<longrightarrow> dropWhile (\<lambda>x'. x' \<noteq> x) xs = zs"
  show "\<forall> ys . a # xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys \<longrightarrow> dropWhile (\<lambda>x'. x' \<noteq> x) (a # xs) = zs"
  proof (rule allI, rule impI, cases "a = x")
    fix ys
    assume "a # xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys" and "a = x"
    hence "x # xs = ys @ zs" and "x \<notin> set ys" and "hd zs = x" and "zs \<noteq> []" by auto
    from `x # xs = ys @ zs` and `x \<notin> set ys` have "ys = []"   by (metis list.sel(1) hd_append hd_in_set)
    with `a = x` and `x # xs = ys @ zs` show "dropWhile (\<lambda>x'. x' \<noteq> x) (a # xs) = zs" by auto
  next
    fix ys
    assume "a # xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys" and "a \<noteq> x"
    hence "a # xs = ys @ zs" and "hd zs = x" and "zs \<noteq> []" and "x \<notin> set ys" by auto
    obtain ys' where "xs = ys' @ zs" and "x \<notin> set ys'"
    proof -
      from `a # xs = ys @ zs` and `hd zs = x` and `a \<noteq> x` obtain ys' where "ys = a # ys'" apply clarify by (metis Cons_eq_append_conv list.sel(1))
      moreover with `x \<notin> set ys` have "x \<notin> set ys'" by auto
      moreover from `ys = a # ys'` and `a # xs = ys @ zs` have "xs = ys' @ zs" by auto
      ultimately show "(\<And>ys'. \<lbrakk>xs = ys' @ zs; x \<notin> set ys'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis" by auto
    qed
    with `\<forall> ys . xs = ys @ zs \<and> hd zs = x \<and> zs \<noteq> [] \<and> x \<notin> set ys \<longrightarrow> dropWhile (\<lambda>x'. x' \<noteq> x) xs = zs` and `hd zs = x` and `zs \<noteq> []` have "dropWhile (\<lambda>x'. x' \<noteq> x) xs = zs" by auto
    with `a \<noteq> x` show "dropWhile (\<lambda>x'. x' \<noteq> x) (a # xs) = zs" by auto
  qed
qed

lemma P2_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P2"
proof  (rule invariantI, auto)
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P2 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P2_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P2 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P2 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P2 (s1', s2')" using `P2 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P2_def) done
  qed
qed

lemma P5_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P5"
proof  (rule invariantI, auto)
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P5 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P5_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P5 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P5 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P5 (s1', s2')" using `P5 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P5_def) done
  qed
qed

lemma  P6_invariant: "[|id1 \<noteq> 0 ; id1 < id2|] ==> invariant (composeALMs id1 id2) P6"
proof  (rule invariantI, rule_tac [2] impI) 
  fix s
  assume "s : starts_of (composeALMs id1 id2)" and "id1 \<noteq> 0"
  thus "P6 s" by (simp add: starts_of_def composeALMs_def hide_def  ALM_ioa_def par_def ALM_start_def P6_def)
next
  fix s t a
  assume "P6 s"
  assume "id1 \<noteq> 0" and "id1 < id2" and "s \<midarrow>a\<midarrow>composeALMs id1 id2\<rightarrow> t"
  thus "P6 t" 
  proof (rule my_rule)
    assume "in_trans_cases_fun id1 id2 s t"
    thus "P6 t" using `P6 s` and `id1 \<noteq> 0` and `id1 < id2`  apply(auto simp add: in_trans_cases_fun_def) apply (simp_all add: ALM_trans_def P6_def) apply (metis phase.simps(12) phase.simps(4) phase.simps(5)) apply (metis phase.simps(12) phase.simps(5)) apply (force simp add: ALM_trans_def P6_def) apply (force simp add: ALM_trans_def P6_def) apply (force simp add: ALM_trans_def P6_def)  apply (force simp add: ALM_trans_def P6_def) apply (force simp add: ALM_trans_def P6_def) apply (force simp add: ALM_trans_def P6_def) done
  qed
qed

lemma  P9_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P9"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)"
  thus "P9 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P9_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P9 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P6 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P6_invariant show "P6 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P9 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P9 (s1', s2')" using `P9 (s1, s2)` and `P6 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P9_def P6_def) done
  qed
qed

lemma  P10_invariant: "[|id1 < id2; id1 ~= 0|] ==> invariant (composeALMs id1 id2) P10"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P10 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P10_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P10 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P10 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P10 (s1', s2')" using `P10 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P10_def) done
  qed
qed

lemma P3_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P3"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P3 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P3_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P3 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P10 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P10_invariant show "P10 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P3 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P3 (s1', s2')" using `P3 (s1, s2)` and `P10 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P3_def P10_def) done
  qed
qed

lemma  P7_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P7"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P7 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P7_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P7 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P6 (s1, s2)" and "P10 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P6_invariant and P10_invariant show "P6 (s1, s2)" and "P10 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P7 (s1', s2')"  
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P7 (s1', s2')" using `P7 (s1, s2)` and `P6 (s1, s2)` and `0 < id1` and `id1 < id2`
    proof (auto simp add: in_trans_cases_fun_def)
      fix ca ra
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Invoke ca ra, s1') \<in> ALM_trans 0 id1" and "(s2, Invoke ca ra, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1', s2')"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix ca h ra
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca id1 h ra, s1') \<in> ALM_trans 0 id1" and "(s2, Switch ca id1 h ra, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1', s2')"  by (auto simp add: ALM_trans_def P7_def P6_def)
    next
      fix c id' h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "(s2, Commit c id' h, s2') \<in> ALM_trans id1 id2" and "id1 \<le> id'" and "id' < id2"
      thus " P7 (s1, s2')" using `P10 (s1, s2)` by (auto simp add: ALM_trans_def P7_def P10_def)
    next
      fix c h r
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Switch c id2 h r, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1, s2')"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Linearize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1, s2')" by (simp add: ALM_trans_def P7_def) 
    next
      fix h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Initialize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1, s2')"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix ca ta ra
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca 0 ta ra, s1') \<in> ALM_trans 0 id1"
      thus " P7 (s1', s2)"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix ca id' h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "id1 < id2" and "(s1, Commit ca id' h, s1') \<in> ALM_trans 0 id1" and "id' < id1"
      thus " P7 (s1', s2)"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Linearize 0 h, s1') \<in> ALM_trans 0 id1"
      thus " P7 (s1', s2)"  by (auto simp add: ALM_trans_def P7_def)
    next
      fix h
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Initialize 0 h, s1') \<in> ALM_trans 0 id1"
      thus " P7 (s1', s2)"  by (auto simp add: ALM_trans_def P7_def)
    next
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Abort id1, s2') \<in> ALM_trans id1 id2"
      thus " P7 (s1, s2')"  by (auto simp add: ALM_trans_def P7_def)
    next
      assume "P7 (s1, s2)" and "P6 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Abort 0, s1') \<in> ALM_trans 0 id1"
      thus " P7 (s1', s2)"  by (auto simp add: ALM_trans_def P7_def)
    qed
  qed
qed

lemma  P4_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P4"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P4 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P4_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P4 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P6 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P6_invariant show "P6 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P4 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P4 (s1', s2')" using `P4 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P4_def) done
  qed
qed

lemma  P8_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P8"
proof  (rule invariantI, auto) 
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P8 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P8_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P6 (s1, s2)" and "P10 (s1, s2)" and "P5 (s1, s2)" and "P4 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P6_invariant and P10_invariant and P5_invariant and P4_invariant show "P6 (s1, s2)" and "P10 (s1, s2)" and "P5 (s1, s2)" and "P4 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P8 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P8 (s1', s2')" using `P8 (s1, s2)` and `0 < id1` and `id1 < id2` 
    proof (auto simp add: in_trans_cases_fun_def) 
      fix ca ra
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and in_invoke_1:"(s1, Invoke ca ra, s1') \<in> ALM_trans 0 id1" and in_invoke_2:"(s2, Invoke ca ra, s2') \<in> ALM_trans id1 id2"
      show "P8 (s1', s2')"
      proof (cases "s1' = s1")
        assume "s1' = s1"
        with in_invoke_2 and `P8 (s1, s2)` show ?thesis by (auto simp add: ALM_trans_def P8_def)
      next
        assume "s1' \<noteq> s1"
        with in_invoke_1 have "pendingReqs s1 \<subseteq> pendingReqs s1'" by (force simp add:pendingReqs_def ALM_trans_def)
        moreover from in_invoke_1 have "hist s1' = hist s1" by (auto simp add:ALM_trans_def)
        moreover from in_invoke_2 have "initHists s2' = initHists s2" by (auto simp add:ALM_trans_def)
        moreover note `P8 (s1, s2)` 
        ultimately show ?thesis by (auto simp add: ALM_trans_def P8_def linearizations_def postfix_all_def)
      qed
    next
      fix ca h ra
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and in_switch_1:"(s1, Switch ca id1 h ra, s1') \<in> ALM_trans 0 id1" and in_switch_2:"(s2, Switch ca id1 h ra, s2') \<in> ALM_trans id1 id2"
      show "P8 (s1', s2')" 
      proof (auto simp add:P8_def)
        fix h1
        assume "h1 \<in> initHists s2'"
        show "h1 \<in> postfix_all (hist s1') (linearizations (pendingReqs s1'))"
        proof (cases "h1 \<in> initHists s2")
          assume "h1 \<in> initHists s2"
          moreover from in_switch_1 and `0 < id1` have "hist s1' = hist s1" and "pendingReqs s1' = pendingReqs s1" by (auto simp add:ALM_trans_def pendingReqs_def) 
          moreover note `P8 (s1, s2)`
          ultimately show "h1 \<in> postfix_all (hist s1') (linearizations (pendingReqs s1'))" by (auto simp add:P8_def)
        next
          assume "h1 \<notin> initHists s2"
          with `h1 \<in> initHists s2'` and in_switch_2 have "h1 = h" by (auto simp add:ALM_trans_def)
          with in_switch_1 and `0 < id1` and `P10 (s1, s2)` have "h1 \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))" by (auto simp add:ALM_trans_def P10_def)
          moreover from in_switch_1 and `0 < id1` have "hist s1' = hist s1" and "pendingReqs s1' = pendingReqs s1" by (auto simp add:ALM_trans_def pendingReqs_def)
          ultimately show ?thesis by auto
        qed
      qed
    next
      fix c id' h
      assume "P8 (s1, s2)" and "0 < id1" and "(s2, Commit c id' h, s2') \<in> ALM_trans id1 id2" and "id1 \<le> id'" and "id' < id2"
      thus " P8 (s1, s2')"  by (auto simp add: ALM_trans_def P8_def)
    next
      fix c h r
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Switch c id2 h r, s2') \<in> ALM_trans id1 id2"
      thus " P8 (s1, s2')"  by (auto simp add: ALM_trans_def P8_def)
    next
      fix h
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Linearize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P8 (s1, s2')"  by (auto simp add: ALM_trans_def P8_def)
    next
      fix h
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Initialize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P8 (s1, s2')"  by (auto simp add: ALM_trans_def P8_def)
    next
      fix ca ta ra
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca 0 ta ra, s1') \<in> ALM_trans 0 id1"
      thus " P8 (s1', s2)" using `P5 (s1, s2)` by (auto simp add: ALM_trans_def P8_def P5_def)
    next
      fix ca id' h
      assume "P8 (s1, s2)" and in_commit_1:"(s1, Commit ca id' h, s1') \<in> ALM_trans 0 id1"
      from in_commit_1 have "pendingReqs s1' = pendingReqs s1" and "hist s1' = hist s1" by (auto simp add:pendingReqs_def ALM_trans_def)
      with `P8 (s1, s2)` show "P8 (s1', s2)" by (auto simp add: ALM_trans_def P8_def pendingReqs_def)
    next
      fix h
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Linearize 0 h, s1') \<in> ALM_trans 0 id1"
      thus "P8 (s1', s2)" using `P6 (s1, s2)` and `P4 (s1, s2)` by (auto simp add: ALM_trans_def P8_def P6_def P4_def)
    next
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Abort id1, s2') \<in> ALM_trans id1 id2"
      thus " P8 (s1, s2')"  by (auto simp add: ALM_trans_def P8_def)
    next
      fix h
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Initialize 0 h, s1') \<in> ALM_trans 0 id1"
      thus " P8 (s1', s2)" using `P10 (s1, s2)` by (auto simp add: ALM_trans_def P8_def P10_def)
    next
      assume "P8 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Abort 0, s1') \<in> ALM_trans 0 id1"
      thus " P8 (s1', s2)" by (auto simp add: ALM_trans_def P8_def pendingReqs_def)
    qed
  qed
qed

lemma  P12_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P12"
proof  clarify 
  assume "id1 < id2" and "0 < id1"
  with P8_invariant and P4_invariant have "invariant (composeALMs id1 id2) (\<lambda> (s1, s2) . P8 (s1, s2) \<and> P4 (s1, s2))" by (auto simp add:invariant_def)
  moreover have "\<forall> s . P8 s \<and> P4 s\<longrightarrow> P12 s"
  proof auto
    fix s1 s2
    assume "P8 (s1, s2)" and "P4 (s1, s2)"
    hence initHists_prop:"\<forall> h \<in> initHists s2 . (\<exists> h' . h = h' @ (hist s1) \<and> set h' \<subseteq> pendingReqs s1 \<and> distinct h')" by (auto simp add:P8_def postfix_all_def linearizations_def)
    show "P12 (s1, s2)"
    proof (simp add:P12_def, rule impI)
      assume "\<exists> c . phase s2 c \<noteq> Sleep"
      with `P4 (s1, s2)` have "initHists s2 \<noteq> {}" by (auto simp add:P4_def)
      with l_c_p_lemma[of "initHists s2" "hist s1"] and initHists_prop 
      obtain rs where "l_c_p (initHists s2) = rs @ hist s1" by (auto simp add: suffixeq_def)
      moreover have "set rs \<subseteq> pendingReqs s1"
      proof -
        from `initHists s2 \<noteq> {}` obtain h where "h \<in> initHists s2" by auto
        with initHists_prop obtain h' where "h = h' @ (hist s1) \<and> set h' \<subseteq> pendingReqs s1" by auto
        moreover from l_c_p_common_postfix[of "initHists s2"] and `h \<in> initHists s2` obtain h'' where "h = h'' @ (l_c_p (initHists s2))" by (auto simp add:common_postfix_p_def suffixeq_def)
        moreover note `l_c_p (initHists s2) = rs @ hist s1`
        ultimately show ?thesis by auto
      qed
      moreover have "distinct rs"
      proof -
        from `initHists s2 \<noteq> {}` obtain h where "h \<in> initHists s2" by auto
        with initHists_prop obtain h' where "h = h' @ (hist s1)" and "distinct h'" by auto
        with l_c_p_common_postfix[of "initHists s2"] and `h \<in> initHists s2` and `l_c_p (initHists s2) = rs @ hist s1` obtain h'' where "h' = h'' @ rs" apply (auto simp add:common_postfix_p_def suffixeq_def) by (metis `h = h' @ hist s1` append_assoc append_same_eq)
        with `distinct h'` show ?thesis by auto
      qed
      ultimately show "\<exists>rs. l_c_p (initHists s2) = rs @ hist s1 \<and> set rs \<subseteq> pendingReqs s1 \<and> distinct rs" by auto
    qed
  qed
  ultimately show ?thesis by (auto intro:invariant_imp)
qed

lemma  P11_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P11"
proof clarify  
  assume "id1 < id2" and "0 < id1"
  with P8_invariant and P12_invariant and P6_invariant and P7_invariant have "invariant (composeALMs id1 id2) (\<lambda> (s1, s2) . P8 (s1, s2) \<and> P12 (s1, s2) \<and> P6 (s1, s2) \<and> P7 (s1, s2))" by (auto simp add:invariant_def)
  moreover have "\<forall> s . P8 s \<and> P12 s \<and> P6 s \<and> P7 s \<longrightarrow> P11 s"
  proof auto
    fix s1 s2
    assume "P8 (s1, s2)" and "P12 (s1, s2)" and "P6 (s1, s2)" and "P7 (s1, s2)"
    show "P11 (s1, s2)"
    proof (simp add:P11_def initValidReqs_def, auto)
      fix x c h
      assume "phase s2 c \<noteq> Sleep"
      with `P12 (s1, s2)` and `P8 (s1, s2)` have  initHists_prop:"\<forall> h \<in> initHists s2 . (\<exists> h' . h = h' @ (hist s1) \<and> set h' \<subseteq> pendingReqs s1)" and lcp_prop:"\<exists> rs . l_c_p (initHists s2) = rs @ (hist s1)" by (auto simp add:P12_def P8_def postfix_all_def linearizations_def)
      assume "x \<notin> set (l_c_p (initHists s2))" and "h \<in> initHists s2" and "x \<in> set h"
      from initHists_prop and `h \<in> initHists s2` obtain h' where "h = h' @ (hist s1)" and "set h' \<subseteq> pendingReqs s1" by auto
      moreover from lcp_prop obtain rs where "l_c_p (initHists s2) = rs @ (hist s1)" by auto
      moreover note `x \<notin> set (l_c_p (initHists s2))` and `x \<in> set h`
      ultimately have "x \<in> set h'" by auto
      with `set h' \<subseteq> pendingReqs s1` show "x \<in> pendingReqs s1" by auto
    next
      fix x c h
      assume "phase s2 c \<noteq> Sleep" and "\<not> initialized s2"
      with `P12 (s1, s2)` have  lcp_prop:"\<exists> rs . l_c_p (initHists s2) = rs @ (hist s1)" by (auto simp add:P12_def P8_def postfix_all_def linearizations_def)
      assume "x \<notin> set (l_c_p (initHists s2))" and "x \<in> pendingReqs s2"
      from `x \<notin> set (l_c_p (initHists s2))` and lcp_prop have "x \<notin> set (hist s1)" by auto
      moreover obtain c' where "phase s1 c' = Aborted" and "x = pending s1 c'"
      proof -
        from `x \<in> pendingReqs s2` and `P6 (s1, s2)` obtain c' where "phase s1 c' = Aborted" and "x = pending s2 c'" by (force simp add:pendingReqs_def P6_def)
        moreover with `\<not> initialized s2` and  `P7 (s1, s2)` have "x = pending s1 c'" by (auto simp add:P7_def)
        ultimately show "(\<And>c'. \<lbrakk>phase s1 c' = Aborted; x = pending s1 c'\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis" by auto
      qed
      ultimately show "x \<in> pendingReqs s1" by (auto simp add:pendingReqs_def)
    qed
  qed
  ultimately show ?thesis by (auto intro:invariant_imp)
qed

lemma  P1a_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P1a"
proof (rule invariantI, auto)  
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P1a (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P1a_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P1a (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P5 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P5_invariant show "P5 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P1a (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P1a (s1', s2')" using `P1a (s1, s2)` and `P5 (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P1a_def P5_def) done
  qed
qed

lemma  P1b_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P1b"
proof (rule invariantI, auto)  
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P1b (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P1b_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P1b (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P1a (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P1a_invariant show "P1a (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P1b (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P1b (s1', s2')" using `P1b (s1, s2)` and `P1a (s1, s2)` and `0 < id1` and `id1 < id2` apply(auto simp add: in_trans_cases_fun_def) apply (auto simp add: ALM_trans_def P1b_def P1a_def) done
  qed
qed

lemma  P13_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P13"
proof clarify  
  assume "id1 < id2" and "0 < id1"
  with P11_invariant and P12_invariant have "invariant (composeALMs id1 id2) (\<lambda> (s1, s2) . P11 (s1, s2) \<and> P12 (s1, s2))" by (auto simp add:invariant_def)
  moreover have "\<forall> s . P11 s \<and> P12 s \<longrightarrow> P13 s"
  proof auto
    fix s1 s2
    assume "P11 (s1, s2)" and "P12 (s1, s2)"
    show "P13 (s1, s2)"
    proof (simp add:P13_def, rule impI)
      assume "(\<exists> c . phase s2 c \<noteq> Sleep) \<and> \<not> initialized s2"
      with `P12 (s1, s2)` and `P11 (s1, s2)` obtain rs where initValidReqs_prop:"initValidReqs s2 \<subseteq> pendingReqs s1" and "l_c_p (initHists s2) = rs @ (hist s1)" and "set rs \<subseteq> pendingReqs s1" and "distinct rs" by (auto simp add:P12_def P11_def postfix_all_def linearizations_def)
      moreover from `l_c_p (initHists s2) = rs @ (hist s1)` have "initValidReqs s2 \<inter> set rs = {}" by (auto simp add:initValidReqs_def)
      ultimately show "postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2)) \<subseteq> postfix_all (hist s1) (linearizations (pendingReqs s1))" by (force simp add: postfix_all_def linearizations_def)
    qed
  qed
  ultimately show ?thesis by (auto intro:invariant_imp)
qed

lemma  P14_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P14"
proof (rule invariantI, auto)  
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P14 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P14_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P6 (s1, s2)" and "P13 (s1, s2)" and "P10 (s1, s2)" and "P2 (s1, s2)" and "P4 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P6_invariant and P13_invariant and P10_invariant  and P4_invariant and P2_invariant show "P6 (s1, s2)" and "P13 (s1, s2)" and "P10 (s1, s2)" and "P2 (s1, s2)" and "P4 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P14 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P14 (s1', s2')" using `P14 (s1, s2)` and `0 < id1` and `id1 < id2` 
    proof (auto simp add: in_trans_cases_fun_def) 
      fix ca ra
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Invoke ca ra, s1') \<in> ALM_trans 0 id1" and "(s2, Invoke ca ra, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1', s2')"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix ca h ra
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca id1 h ra, s1') \<in> ALM_trans 0 id1" and "(s2, Switch ca id1 h ra, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1', s2')"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix c id' h
      assume "P14 (s1, s2)" and "0 < id1" and "(s2, Commit c id' h, s2') \<in> ALM_trans id1 id2" and "id1 \<le> id'" and "id' < id2"
      thus " P14 (s1, s2')"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix c h r
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Switch c id2 h r, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1, s2')"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix h
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Linearize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1, s2')" by (auto simp add: ALM_trans_def P14_def linearizations_def postfix_all_def pendingReqs_def)
    next
      fix h
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Initialize id1 h, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1, s2')" using `P13 (s1, s2)` apply (auto simp add: ALM_trans_def P14_def P13_def linearizations_def postfix_all_def pendingReqs_def) prefer 2 apply force apply blast done
    next
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Abort id1, s2') \<in> ALM_trans id1 id2"
      thus " P14 (s1, s2')"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix ca ta ra
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca 0 ta ra, s1') \<in> ALM_trans 0 id1"
      thus " P14 (s1', s2)"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix ca id' h
      assume "P14 (s1, s2)" and "id1 < id2" and "(s1, Commit ca id' h, s1') \<in> ALM_trans 0 id1" and "id' < id1"
      thus " P14 (s1', s2)"  by (auto simp add: ALM_trans_def P14_def)
    next
      fix h
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and in_lin:"(s1, Linearize 0 h, s1') \<in> ALM_trans 0 id1"
      from in_lin have "\<not> initialized s2" and "hist s2 = []" using `P6 (s1, s2)` and `P2 (s1, s2)` and `P10 (s1, s2)` and `P2 (s1, s2)` by (auto simp add: ALM_trans_def P14_def P6_def P10_def P2_def P2_def)
      thus " P14 (s1', s2)" by (auto simp add:P14_def)
    next
      fix h
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Initialize 0 h, s1') \<in> ALM_trans 0 id1"
      thus " P14 (s1', s2)" using `P10 (s1, s2)`by (auto simp add: ALM_trans_def P14_def P10_def) 
    next
      assume "P14 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Abort 0, s1') \<in> ALM_trans 0 id1"
      thus " P14 (s1', s2)"  by (auto simp add: ALM_trans_def P14_def)
    qed
  qed
qed

lemma  P15_invariant: "[|id1 < id2; id1 \<noteq> 0|] ==> invariant (composeALMs id1 id2) P15"
proof (rule invariantI, auto)  
  fix s1 s2
  assume "(s1, s2) : starts_of (composeALMs id1 id2)" and "0 < id1"
  thus "P15 (s1, s2)" by (simp add: starts_of_def composeALMs_def hide_def ALM_ioa_def par_def ALM_start_def P15_def)
next
  fix s1 s2 s1' s2' act
  assume "reachable (composeALMs id1 id2) (s1, s2)" and "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
  have "P13 (s1, s2)" and "P1b (s1, s2)" and "P6 (s1, s2)" and "P1a (s1, s2)" and "P5 (s1, s2)" and "P10 (s1, s2)"
  proof -
    from in_trans_comp and `reachable (composeALMs id1 id2) (s1, s2)` have "reachable (composeALMs id1 id2) (s1', s2')" by (auto intro: reachable.reachable_n)
    with `reachable (composeALMs id1 id2) (s1, s2)` and `0 < id1` and `id1 < id2` and P13_invariant and P1b_invariant and P1a_invariant and P6_invariant and P5_invariant and P10_invariant  show "P13 (s1, s2)" and "P1b (s1, s2)" and "P6 (s1, s2)" and "P1a (s1, s2)"  and "P5 (s1, s2)" and "P10 (s1, s2)" unfolding invariant_def by auto
  qed
  from `0 < id1` and `id1 < id2` and in_trans_comp show "P15 (s1', s2')" 
  proof (rule my_rule2) 
    assume "in_trans_cases_fun id1 id2 (s1, s2) (s1', s2')"
    thus "P15 (s1', s2')" using  `P15 (s1, s2)` and `0 < id1` and `id1 < id2` 
    proof (auto simp add: in_trans_cases_fun_def) 
      fix ca ra
      assume "P15 (s1, s2)" and in_invoke1:"(s1, Invoke ca ra, s1') \<in> ALM_trans 0 id1" and in_invoke2:"(s2, Invoke ca ra, s2') \<in> ALM_trans id1 id2"
      show "P15 (s1', s2')" 
      proof -
        { assume "s1' = s1"
          with `P15 (s1, s2)` and in_invoke1 and in_invoke2 and `0 < id1` and `id1 < id2`
          have ?thesis by (auto simp add:ALM_trans_def P15_def)
        } note case1 = this
        { assume "s1' \<noteq> s1"
          with in_invoke1 and in_invoke2 and `P6 (s1, s2)` have "s2' = s2" apply (auto simp add:ALM_trans_def P6_def) by (metis phase.simps(12) phase.simps(4))
          with `s1' \<noteq> s1` and `P15 (s1, s2)` and in_invoke1 have ?thesis by (force simp add:P15_def ALM_trans_def pendingReqs_def) (*TODO: why is it working?*)
        } note case2 = this
        from case1 and case2 show ?thesis by auto
      qed
    next
      fix ca h ra
      assume "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Switch ca id1 h ra, s1') \<in> ALM_trans 0 id1" and "(s2, Switch ca id1 h ra, s2') \<in> ALM_trans id1 id2"
      thus " P15 (s1', s2')" by (auto simp add: ALM_trans_def P15_def pendingReqs_def)
    next
      fix c id' h
      assume "P15 (s1, s2)" and "0 < id1" and "(s2, Commit c id' h, s2') \<in> ALM_trans id1 id2" and "id1 \<le> id'" and "id' < id2"
      thus " P15 (s1, s2')"  by (auto simp add: ALM_trans_def P15_def)
    next
      fix c h r
      assume "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Switch c id2 h r, s2') \<in> ALM_trans id1 id2"
      thus " P15 (s1, s2')"  by (auto simp add: ALM_trans_def P15_def)
    next
      fix h
      assume in_lin:"(s2, Linearize id1 h, s2') \<in> ALM_trans id1 id2"
      show "P15 (s1, s2')"
      proof (auto simp add:P15_def)
        fix r
        assume "phase s2' (request_snd r) = Sleep" and "r \<in> set (hist s2')" and "r \<notin> pendingReqs s1"
        show "r \<in> set (hist s1)"
        proof -
          from `phase s2' (request_snd r) = Sleep` and in_lin have "phase s2 (request_snd r) = Sleep" by (auto simp add:ALM_trans_def)
          with `P1b (s1, s2)` have "r \<notin> pendingReqs s2" by (auto simp add:pendingReqs_def P1b_def)
          with in_lin and `r \<in> set (hist s2')` have "r \<in> set (hist s2)" by (auto simp add:ALM_trans_def postfix_all_def linearizations_def)
          with `phase s2 (request_snd r) = Sleep` and `P15 (s1, s2)` and `r \<notin> pendingReqs s1` show ?thesis by (auto simp add:P15_def)
        qed
      qed
    next
      assume "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s2, Abort id1, s2') \<in> ALM_trans id1 id2"
      thus " P15 (s1, s2')"  by (auto simp add: ALM_trans_def P15_def)
    next
      fix h
      assume in_init:"(s2, Initialize id1 h, s2') \<in> ALM_trans id1 id2"
      show " P15 (s1, s2')" 
      proof (auto simp add:P15_def)
        fix r
        assume "phase s2' (request_snd r) = Sleep" and "r \<in> set (hist s2')" and "r \<notin> pendingReqs s1"
        show "r \<in> set (hist s1)"
        proof -
          from in_init and `P13 (s1, s2)`
          have "hist s2' \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))" by (auto simp add:ALM_trans_def P13_def)
          with `r \<in> set (hist s2')` have "r \<in> set (hist s1) \<or> r \<in> pendingReqs s1" by (auto simp add: postfix_all_def linearizations_def)
          with `r \<notin> pendingReqs s1` show ?thesis by auto
        qed
      qed
    next
      fix ca ta ra
      assume "(s1, Switch ca 0 ta ra, s1') \<in> ALM_trans 0 id1"
      hence "s1' = s1" using `P5 (s1, s2)` by (auto simp add: ALM_trans_def P5_def)
      thus "P15 (s1', s2)" using `P15 (s1, s2)` by auto
    next
      fix ca id' h
      assume "P15 (s1, s2)" and "id1 < id2" and "(s1, Commit ca id' h, s1') \<in> ALM_trans 0 id1" and "id' < id1"
      thus " P15 (s1', s2)" by (auto simp add: ALM_trans_def P15_def pendingReqs_def)
    next
      fix h
      assume "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Linearize 0 h, s1') \<in> ALM_trans 0 id1"
      thus "P15 (s1', s2)" by (auto simp add: ALM_trans_def P15_def pendingReqs_def postfix_all_def)
    next
      fix h
      assume "(s1, Initialize 0 h, s1') \<in> ALM_trans 0 id1"
      hence "s1' = s1" using `P10 (s1, s2)` by (auto simp add: ALM_trans_def P10_def)
      thus "P15 (s1', s2)" using `P15 (s1, s2)` by auto
    next
      assume "P15 (s1, s2)" and "0 < id1" and "id1 < id2" and "(s1, Abort 0, s1') \<in> ALM_trans 0 id1"
      thus " P15 (s1', s2)"  by (auto simp add: ALM_trans_def P15_def pendingReqs_def)
    qed
  qed
qed

subsection {*The refinement proof*}

definition ref_mapping :: "(ALM_state * ALM_state) => ALM_state" 
  -- {*The refinement mapping between the composition of two ALMs and a single ALM*}
  where
  "ref_mapping \<equiv> \<lambda> (s1, s2) .
     \<lparr>pending = \<lambda>c. (if phase s1 c \<noteq> Aborted then pending s1 c else pending s2 c),
      initHists = {},
      phase = \<lambda>c. (if phase s1 c \<noteq> Aborted then phase s1 c else phase s2 c),
      hist = (if hist s2 = [] then hist s1 else hist s2),
      aborted = aborted s2,
      initialized = True\<rparr>"

theorem composition: "[|id1 \<noteq> 0; id1 < id2|] ==> ((composeALMs id1 id2) =<| (ALM_ioa 0 id2))"
  -- {*The composition theorem*}
proof -
  assume "id1 \<noteq> 0" and "id1 < id2"
  show "composeALMs id1 id2 =<| ALM_ioa 0 id2"
  proof  (simp add: ioa_implements_def, rule conjI, rule_tac[2] conjI) 
    show same_input_sig:"inp (composeALMs id1 id2) = inp (ALM_ioa 0 id2)" 
    -- {*First we show that both automata have the same input and output signature*}
      using  `id1 \<noteq> 0` and `id1 < id2` by  (simp add: composeALMs_def hide_def hide_asig_def  ALM_ioa_def asig_inputs_def asig_outputs_def asig_of_def ALM_asig_def par_def asig_comp_def, auto)
    from `id1 \<noteq> 0` and `id1 < id2` 
    show same_output_sig:"out (composeALMs id1 id2) = out (ALM_ioa 0 id2)" 
      -- {*Then we show that output signatures match*}
      by  (simp add:  asig_inputs_def asig_outputs_def asig_of_def composeALMs_def hide_def hide_asig_def ALM_ioa_def ALM_asig_def par_def asig_comp_def, auto)
    show "traces (composeALMs id1 id2) <= traces (ALM_ioa 0 id2)"
      -- {*Finally we show trace inclusion*}
    proof  (rule trace_inclusion[where f=ref_mapping]) 
      -- {*We use the mapping @{text ref_mapping}, defined before*}
      from  same_input_sig and same_output_sig show "ext (composeALMs id1 id2) = ext (ALM_ioa 0 id2)" 
        -- {*First we show that they have the same external signature*}
        by  (simp add: externals_def)
    next
      show "is_ref_map ref_mapping (composeALMs id1 id2) (ALM_ioa 0 id2)"
        -- {*Then we show that @{text ref_mapping_comp} is a refinement mapping*}
         apply (simp add: is_ref_map_def, auto, rename_tac s1 s2) prefer 2 apply (rename_tac s1 s2 s1' s2' act) 
      proof -
        -- {*First we show that start states correspond*}
        fix s1 s2
        assume "(s1, s2) : starts_of (composeALMs id1 id2)"
        thus "ref_mapping (s1, s2) : starts_of (ALM_ioa 0 id2)" using  `id1 \<noteq> 0` and `id1 < id2` by  (simp add:  ALM_ioa_def ALM_start_def starts_of_def composeALMs_def hide_def par_def ref_mapping_def)
      next
          -- {*Then we show the main property of a refinement mapping*}
        fix s1 s2 s1' s2' act
        assume reachable:"reachable (composeALMs id1 id2) (s1, s2)" and in_trans_comp:"(s1, s2) \<midarrow>act\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
        txt  {*We make the invariants available for later use*}
        have "P6 (s1, s2)" and "P6 (s1', s2')" and "P9 (s1, s2)" and "P7 (s1, s2)" and "P10 (s1, s2)" and "P4 (s1, s2)" and "P5 (s1, s2)" and "P13 (s1, s2)" and "P1a (s1, s2)" and "P14 (s1, s2)" and "P14 (s1', s2')" and "P15 (s1, s2)" and "P2 (s1, s2)" and "P3 (s1, s2)"
        proof  -
          from reachable and in_trans_comp have "reachable (composeALMs id1 id2) (s1', s2')" by (rule reachable.reachable_n)
          with P6_invariant and P9_invariant and P2_invariant and P7_invariant and P10_invariant and P4_invariant and P5_invariant and P13_invariant  and P1a_invariant and P14_invariant and P15_invariant  and P3_invariant `id1 \<noteq> 0` and `id1 < id2` and reachable
          show "P6 (s1, s2)" and "P6 (s1', s2')" and "P9 (s1, s2)" and "P7 (s1, s2)" and "P10 (s1, s2)" and "P4 (s1, s2)" and "P5 (s1, s2)" and "P13 (s1, s2)" and "P1a (s1, s2)" and "P14 (s1, s2)"  and "P14 (s1', s2')"  and "P15 (s1, s2)"  and "P2 (s1, s2)" and "P3 (s1, s2)" by (auto simp add: invariant_def)
        qed
        let ?t = "ref_mapping (s1, s2)"
        let ?t' = "ref_mapping (s1', s2')"
        show "EX ex. move (ALM_ioa 0 id2) ex ?t act ?t'"
          -- {* the main part of the proof *}
        proof  (simp add: move_def, auto) 
          assume "act : ext (ALM_ioa 0 id2)"
          hence "act : {act . EX c r . act = Invoke c r | (EX t . act = Switch c 0 t r)} Un {act . EX c tr . (EX id' . 0 <= id' & id' < id2 & act = Commit c id' tr) | (EX r . act = Switch c id2 tr r)}" by  (auto simp add: ALM_ioa_def ALM_asig_def externals_def asig_inputs_def asig_outputs_def asig_of_def)
          with in_trans_comp show "EX ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) & Finite ex & laststate (?t, ex) = ?t' & mk_trace (ALM_ioa 0 id2)$ex = [act!]" 
            -- {*If act is an external action of the composition, then there must be an execution of the spec with matching states and forming trace "act"*}
             apply auto 
          proof -
            fix c r
            assume in_invoke:"(s1, s2) \<midarrow>Invoke c r\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*If the current action is Invoke*}
            show "EX ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) & Finite ex & laststate (?t, ex) = ?t' & mk_trace (ALM_ioa 0 id2)$ex = [Invoke c r!]"
            proof  -
              let ?ex = "[(Invoke c r, ?t')!]"
                (*First a bunch of trivial things*)
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)$(?ex) = [Invoke c r!]" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
                (*Proof that ?ex relates the mappings*)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)" (*CAN actually go automatically if you wait long enough: using in_invoke and `id1 \<noteq> 0` and `id1 < id2` and `P6 (s1, s2)` apply (auto simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(force simp add:ALM_trans_def fun_eq_iff P6_def ref_mapping_def)*)
              proof -
                {
                  assume "s1' \<noteq> s1 & s2' \<noteq> s2" 
                    -- {*contradiction*}
                  with in_invoke and `id1 \<noteq> 0` and `id1 < id2` and `P6 (s1', s2')` have ?thesis apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(auto simp add:ALM_trans_def P6_def) done
                }
                moreover
                {
                  assume "s1' = s1" and "s2' = s2"
                  with in_invoke have pre_s1:"~(phase s1 c = Ready & request_snd r = c & r \<notin> set (hist s1))"  and pre_s2:"~(phase s2 c = Ready & request_snd r = c & r \<notin> set (hist s2))" using [[hypsubst_thin]] apply (auto simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp_all add:ALM_trans_def) apply (drule_tac[!] arg_cong[where f = "phase"]) apply simp_all apply (metis phase.simps(8) fun_upd_idem_iff) apply (metis phase.simps(8) fun_upd_idem_iff) apply (metis phase.simps(8) fun_upd_idem_iff) apply (metis phase.simps(8) fun_upd_idem_iff) done (*TODO: how to deal with records automatically?*)
                  hence  "~(phase ?t c = Ready & request_snd r = c & r \<notin> set (hist ?t))" using `P14 (s1, s2)` by (auto simp add:ref_mapping_def P14_def)
                  hence ?thesis using `id1 \<noteq> 0`  and `s1' = s1` and `s2' = s2` apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp_all add:ALM_trans_def) apply force done 
                }
                moreover
                {
                  assume "s1' \<noteq> s1" and "s2' = s2"
                  with in_invoke have pre_s1:"phase s1 c = Ready & request_snd r = c & r \<notin> set (hist s1)" and trans_s1: "s1' = s1\<lparr>pending :=  (pending s1)(c := r), phase := (phase s1)(c := Pending)\<rparr>" apply (simp_all add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp_all add:ALM_trans_def ref_mapping_def) done
                  have pre_t: "phase ?t c = Ready & request_snd r = c & r \<notin> set (hist ?t)"
                  proof -
                    from pre_s1 have "phase ?t c = Ready & request_snd r = c" by (auto simp add:ref_mapping_def)
                    moreover have "r \<notin> set (hist ?t)"
                    proof (cases "hist s2 = []")
                      assume "hist s2 = []"
                      with pre_s1 show ?thesis by (auto simp add:ref_mapping_def)
                    next
                      assume "hist s2 \<noteq> []"
                      show "r \<notin> set (hist ?t)"
                      proof auto
                        assume "r \<in> set (hist ?t)"
                        with `hist s2 \<noteq> []` have "r \<in> set (hist s2)" by (auto simp add:ref_mapping_def)
                        moreover from pre_s1 and `P6 (s1, s2)` have "phase s2 (request_snd r) = Sleep" by (force simp add:P6_def)
                        moreover note `P15 (s1, s2)`
                        ultimately have "r \<in> set (hist s1) \<or> r \<in> pendingReqs s1" by (auto simp add:P15_def) 
                        with pre_s1 have "r \<in> pendingReqs s1" by auto
                        with `P1a (s1, s2)` and pre_s1 show False by (auto simp add:pendingReqs_def P1a_def)
                      qed
                    qed
                    ultimately show ?thesis by auto
                  qed
                  moreover from pre_s1 and trans_s1 and `s2' = s2` have trans_t:"?t' = ?t\<lparr>pending :=  (pending ?t)(c := r), phase := (phase ?t)(c := Pending)\<rparr>" by (auto simp add:ref_mapping_def  fun_eq_iff)
                  ultimately have ?thesis apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done 
                }
                moreover
                {
                  assume "s1' = s1" and "s2' \<noteq> s2"
                    (*CAN go automatically: with in_invoke and `id1 \<noteq> 0` and `P6 (s1, s2)` have ?thesis apply (auto simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(force simp add:ALM_trans_def fun_eq_iff P6_def ref_mapping_def)*)
                  with in_invoke and `id1 \<noteq> 0` have pre_s2: "phase s2 c = Ready & request_snd r = c & r \<notin> set (hist s2)" and trans_s2: "s2' = s2\<lparr>pending :=  (pending s2)(c := r), phase := (phase s2)(c := Pending)\<rparr>" apply (simp_all add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp_all add:ALM_trans_def ref_mapping_def) done
                  from pre_s2 and `P6 (s1, s2)`  have aborted_s1_c:"phase s1 c = Aborted" by (auto simp add: P6_def) 
                  with pre_s2 and `P3 (s1, s2)` and `P14 (s1, s2)` have pre_t:"phase ?t c = Ready & request_snd r = c & r \<notin> set (hist ?t)" apply (auto simp add: fun_eq_iff ref_mapping_def P3_def P14_def) done
                  moreover have trans_t:"?t' = ?t\<lparr>pending :=  (pending ?t)(c := r), phase := (phase ?t)(c := Pending)\<rparr>" using aborted_s1_c and `s1' = s1` and trans_s2 apply(force simp add: fun_eq_iff ref_mapping_def) done
                  ultimately have ?thesis apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done 
                }
                ultimately show ?thesis by auto
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          next
            fix c r h
            assume in_switch:"(s1, s2) \<midarrow>Switch c 0 h r\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*If we get a switch 0 input (nothing happens)*}
            show "EX ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) & Finite ex & laststate (?t, ex) = ?t' & mk_trace (ALM_ioa 0 id2)$ex = [Switch c 0 h r!]"
            proof  -
              let ?ex = "[(Switch c 0 h r, ?t')!]"
                (*First a bunch of trivial things*)
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)$(?ex) = [Switch c 0 h r!]" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
                (*Proof that ?ex relates the mappings*)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
              proof -
                from in_switch and `id1 \<noteq> 0` and `id1 < id2` and `P5 (s1, s2)` have "s1' = s1" and "s2' = s2" and "\<And> c . phase s1 c \<noteq> Sleep" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(simp_all add: ALM_trans_def P5_def) done
                hence "?t = ?t'" and "\<And> c . phase ?t c \<noteq> Sleep" using `P6 (s1, s2)` by (auto simp add:ref_mapping_def P6_def)
                thus ?thesis by (simp add:is_exec_frag_def  ALM_ioa_def trans_of_def ALM_trans_def)
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          next
            fix c h r
            assume in_switch:"(s1, s2) \<midarrow>Switch c id2 h r\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*The case when the system switches to a third, new, instance*}
            show "EX ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) &
              Finite ex & laststate (?t, ex) = ?t' & mk_trace (ALM_ioa 0 id2)$ex = [Switch c id2 h r!]"
            proof  -
              let ?ex = "[(Switch c id2 h r, ?t')!]"
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)$(?ex) = [Switch c id2 h r!]" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
                (*Proof that ?ex relates the mappings*)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
              proof -
                from in_switch and `id1 < id2` have "s1' = s1" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) done
                from `id1 \<noteq> 0` and `id1 < id2` in_switch have pre_s2:"aborted s2 & phase s2 c = Pending & r = pending s2 c & (if initialized s2 then (h \<in> postfix_all (hist s2) (linearizations (pendingReqs s2))) else (h : postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2))))" and trans_s2: "s2' = s2\<lparr>phase := (phase s2)(c := Aborted)\<rparr>" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
                from pre_s2 have s1_aborted:"phase s1 c = Aborted" using `P6 (s1, s2)` apply(auto simp add: P6_def) done
                have pre_t:"aborted ?t & phase ?t c = Pending & initialized ?t & h : postfix_all (hist ?t) (linearizations (pendingReqs ?t)) & r = pending ?t c" 
                proof -
                  from s1_aborted and pre_s2 have "aborted ?t & pending ?t c = r" and "phase ?t c = Pending" and "initialized ?t" by (auto simp add: ref_mapping_def fun_eq_iff)
                  moreover have "h : postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                  proof -
                    from pre_s2 have "(if initialized s2 then (h : postfix_all (hist s2) (linearizations (pendingReqs s2))) else (h : postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2))))" by auto
                    thus ?thesis
                    proof auto
                      assume case1_1:"initialized s2" and case1_2:"h : postfix_all (hist s2) (linearizations (pendingReqs s2))"
                      hence "suffixeq (hist s1) (hist s2)" using `P14 (s1, s2)` by (auto simp add:P14_def suffixeq_def)
                      show "h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                      proof -
                        have "hist ?t = hist s2"
                        proof (cases "hist s2 = []")
                          assume "hist s2 = []"
                          show "hist ?t = hist s2"
                          proof -
                            from `hist s2 = []` and `suffixeq (hist s1) (hist s2)` have "hist s1 = []" by (auto simp add:suffixeq_def)
                            with `hist s2 = []` show  "hist ?t = hist s2" by (auto simp add: ref_mapping_def)
                          qed
                        next
                          assume "hist s2 \<noteq> []"
                          thus "hist ?t = hist s2" by (simp add:ref_mapping_def)
                        qed
                        moreover have "pendingReqs s2 <= pendingReqs ?t"
                        proof (simp add: pendingReqs_def, clarify) 
                          fix c
                          assume "pending s2 c \<notin> set (hist s2)" and "phase s2 c = Pending \<or> phase s2 c = Aborted"
                          moreover with `P6 (s1, s2)` have "phase s1 c = Aborted" by (auto simp add:P6_def)
                          moreover note `suffixeq (hist s1) (hist s2)`
                          ultimately show "\<exists>ca. pending s2 c = pending ?t ca \<and> pending s2 c \<notin> set (hist ?t) \<and> (phase ?t ca = Pending \<or> phase ?t ca = Aborted)" apply (simp add:ref_mapping_def suffixeq_def) by (metis prefixeq_Nil prefixeq_def self_append_conv2)
                        qed
                        moreover note  case1_2
                        ultimately show ?thesis by (auto simp add: linearizations_def postfix_all_def)
                      qed
                    next
                      assume case2_1:"\<not> initialized s2" and case2_2:"h : postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2))"
                      from case2_1 and `P10 (s1, s2)` have "hist s2 = []" by (auto simp add:P10_def)
                      have "h : postfix_all (hist s1) (linearizations (pendingReqs s1))"
                      proof -
                        from pre_s2 have "phase s2 c \<noteq> Sleep" by auto
                        moreover note `P13 (s1, s2)` and case2_1 and case2_2
                        ultimately  show ?thesis by (auto simp add:P13_def)
                      qed
                      moreover from `hist s2 = []` have "hist ?t = hist s1" by (auto simp add:P10_def ref_mapping_def)
                      moreover have "pendingReqs ?t = pendingReqs s1"
                      proof auto
                        fix r
                        assume "r \<in> pendingReqs ?t"
                        with this obtain c' where "r = pending ?t c'" and "r \<notin> set (hist ?t)" and "phase ?t c' \<in> {Pending, Aborted}" by (auto simp add:pendingReqs_def)
                        show "r \<in> pendingReqs s1"
                        proof (cases "phase s1 c' = Aborted")
                          assume "phase s1 c' = Aborted"
                          with `phase ?t c' \<in> {Pending, Aborted}` and `r = pending ?t c'` have "phase s2 c' \<in> {Pending, Aborted}" and "r = pending s2 c'" by (auto simp add:ref_mapping_def)
                          with `P6 (s1, s2)` and case2_1 and `P7 (s1, s2)` and `hist ?t = hist s1` and `r \<notin> set (hist ?t)` have "phase s1 c' = Aborted" and "r = pending s1 c'" and "r \<notin> set (hist s1)" apply (auto simp add: P6_def P7_def) apply force apply force done
                          thus ?thesis by (auto simp add:pendingReqs_def)
                        next
                          assume "phase s1 c' \<noteq> Aborted"
                          with `r = pending ?t c'` and `r \<notin> set (hist ?t)` and `phase ?t c' \<in> {Pending, Aborted}` and `hist ?t = hist s1` show ?thesis by (auto simp add:ref_mapping_def pendingReqs_def)
                        qed
                      next
                        fix r
                        assume "r \<in> pendingReqs s1"
                        with this obtain c where "r = pending s1 c" and "phase s1 c \<in> {Pending, Aborted}" and "r \<notin> set (hist s1)" by (auto simp add:pendingReqs_def)
                        with `hist s2 = []` and `\<not> initialized s2` and `P7 (s1, s2)` show "r \<in> pendingReqs ?t" by (auto simp add:ref_mapping_def pendingReqs_def P7_def)
                      qed
                      ultimately show ?thesis by (auto simp add: postfix_all_def linearizations_def)
                    qed
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have trans_t:"?t' = ?t\<lparr>phase := (phase ?t)(c := Aborted)\<rparr>" using s1_aborted and `s1' = s1` and trans_s2 by (auto simp add:ref_mapping_def fun_eq_iff)
                ultimately show ?thesis using `id1 < id2` apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          next
            fix c h id'
            assume in_commit:"(s1, s2) \<midarrow>Commit c id' h\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')" and "id' <  id2"
              -- {*Case when the composition commits a request*}
            show "\<exists>ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) \<and> Finite ex \<and> laststate (?t, ex) = ?t' \<and> mk_trace (ALM_ioa 0 id2)\<cdot>ex = [Commit c id' h!]"
            proof  -
              let ?ex = "[(Commit c id' h, ?t')!]"
                (*First a bunch of trivial things*)
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)$(?ex) = [Commit c id' h!]" using `id' < id2` by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
                (*Proof that ?ex relates the mappings*)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
              proof -
                {
                  assume "id' < id1"
                  with in_commit have "s2' = s2" and pre_s1:"phase s1 c = Pending \<and> pending s1 c \<in> set (hist s1) \<and> h = dropWhile (\<lambda> r . r \<noteq> pending s1 c) (hist s1)" and trans_s1:"s1' = s1 \<lparr>phase := (phase s1)(c := Ready)\<rparr>" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
                  from pre_s1 have s1_not_aborted_c:"phase s1 c \<noteq> Aborted" by auto
                  have pre_t:"phase ?t c = Pending & pending ?t c \<in> set (hist ?t) \<and> h = dropWhile (\<lambda> r . r \<noteq> pending ?t c) (hist ?t)"
                  proof (cases "hist s2 = []")
                    assume "hist s2 = []"
                    with pre_s1 and `phase s1 c \<noteq> Aborted` show ?thesis by (auto simp add: ref_mapping_def)
                  next
                    assume "hist s2 \<noteq> []"
                    hence "initialized s2" using `P10 (s1, s2)` by (auto simp add:P10_def)
                    from pre_s1 and `phase s1 c \<noteq> Aborted` have "phase ?t c = Pending" and "pending ?t c = pending s1 c" and "pending s1 c \<in> set (hist s1)" by (auto simp add:ref_mapping_def)
                    moreover have "pending ?t c \<in> set (hist ?t)"
                    proof -
                      from `initialized s2` and `P14 (s1, s2)` obtain rs3 where "hist s2 = rs3 @ (hist s1)" by (auto simp add:P14_def)
                      with `pending s1 c \<in> set (hist s1)` and `hist s2 = rs3 @ (hist s1)` and `pending ?t c = pending s1 c` show "pending ?t c \<in> set (hist ?t)" by (auto simp add:ref_mapping_def suffixeq_def)
                    qed
                    moreover have "h = dropWhile (\<lambda> r . r \<noteq> pending ?t c) (hist ?t)"
                    proof -
                      from `pending s1 c \<in> set (hist s1)` obtain rs1 rs2 where "hist s1 = rs2 @ rs1" and "hd rs1 = pending s1 c" and "rs1 \<noteq> []" and "pending s1 c \<notin> set rs2"  by (metis list.sel(1) in_set_conv_decomp_first list.simps(3))
                      with `pending ?t c = pending s1 c` and dropWhile_lemma[of "hist s1" rs1 "pending s1 c"] and pre_s1 have "h = rs1" by auto
                      moreover have "dropWhile (\<lambda> r . r \<noteq> pending ?t c) (hist ?t) = rs1"
                      proof -
                        from `initialized s2` and `P14 (s1, s2)` obtain rs3 where "hist s2 = rs3 @ (hist s1)" and "set rs3 \<inter> set (hist s1) = {}" by (auto simp add:P14_def)
                        with `pending s1 c \<in> set (hist s1)` and `hist s1 = rs2 @ rs1` have "hist s2 = rs3 @ rs2 @ rs1" and "pending s1 c \<notin> set rs3" by auto
                        with `pending s1 c \<notin> set rs2` obtain rs4 where "hist s2 = rs4 @ rs1" and "pending s1 c \<notin> set rs4" by auto
                        with `hd rs1 = pending s1 c` and `rs1 \<noteq> []` and dropWhile_lemma[of "hist s2" rs1 "pending s1 c"] have "dropWhile (\<lambda> r . r \<noteq> pending s1 c) (hist s2) = rs1" by auto
                        thus ?thesis using `hist s2 \<noteq> []` and `pending ?t c = pending s1 c` by (auto simp add:ref_mapping_def)
                      qed
                      ultimately show ?thesis by auto
                    qed
                    ultimately show ?thesis by auto
                  qed
                  moreover from `s2' = s2` and s1_not_aborted_c and trans_s1 have trans_t:"?t' = ?t \<lparr>phase := (phase ?t)(c := Ready)\<rparr>" by (simp add:fun_eq_iff ref_mapping_def)
                  ultimately have ?thesis using `id1 < id2` apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done
                }
                moreover 
                {
                  assume "id1 \<le> id'"
                  with in_commit have "s1' = s1" and pre_s2:"phase s2 c = Pending \<and> pending s2 c \<in> set (hist s2) \<and> h = dropWhile (\<lambda> r . r \<noteq> pending s2 c) (hist s2)" and trans_s2:"s2' = s2 \<lparr>phase := (phase s2)(c := Ready)\<rparr>" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
                  from pre_s2 and `P6 (s1, s2)` have facts:"aborted s1 & phase s1 c = Aborted & hist s2 \<noteq> []" by (force simp add:P6_def)
                  with pre_s2 have pre_t:"phase ?t c = Pending \<and> pending ?t c \<in> set (hist ?t) \<and> h = dropWhile (\<lambda> r . r \<noteq> pending ?t c) (hist ?t)" by (auto simp add:ref_mapping_def)
                  moreover from `s1' = s1` and facts and trans_s2 have trans_t:"?t' = ?t \<lparr>phase := (phase ?t)(c := Ready)\<rparr>" by (auto simp add:fun_eq_iff ref_mapping_def)
                  ultimately have ?thesis using `id1 < id2` apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done
                }
                ultimately show ?thesis using `id' < id2` by force
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          qed
              -- {*We finished the case when the composition takes an action that is in the external signature of the spec*}
        next
          assume "act \<notin> ext (ALM_ioa 0 id2)"
            -- {*Now the case when the composition takes an action that is not in the external signature of the spec*}
          with in_trans_comp and `id1 < id2` and `id1 \<noteq> 0` have "act : {act . act = Abort 0 | act = Abort id1 | (EX c r h . act = Linearize 0 h | act = Linearize id1 h | act = Switch c id1 h r | act = Initialize 0 h | act = Initialize id1 h)}" by  (auto simp add: composeALMs_def hide_def hide_asig_def ALM_ioa_def ALM_asig_def externals_def asig_inputs_def asig_outputs_def asig_internals_def asig_of_def trans_of_def par_def actions_def)
          with in_trans_comp show "\<exists>ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) \<and> Finite ex \<and> laststate (?t, ex) = ?t' \<and> mk_trace (ALM_ioa 0 id2)\<cdot>ex = nil" 
          proof  auto 
            assume in_abort:"(s1, s2) \<midarrow>Abort 0\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*The case where the first Abastract aborts*}
            moreover  with `id1 \<noteq> 0` and `id1 < id2` and `P6 (s1, s2)` and `P2 (s1, s2)` have "\<forall> c . phase s1 c \<noteq> Aborted" and "hist s2 = []" and "\<forall> c . phase s2 c = Sleep" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:fun_eq_iff ALM_trans_def ref_mapping_def P6_def P2_def) done
            moreover  note `id1 \<noteq> 0`
             ultimately  have "?t' = ?t"  apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:fun_eq_iff ALM_trans_def ref_mapping_def) done 
            thus ?thesis
            proof  simp
              let ?ex = "nil"
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" using `id1 < id2` by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)" by (auto simp add:is_exec_frag_def)
              ultimately show "\<exists>ex. is_exec_frag (ALM_ioa 0 id2) (?t, ex) \<and> Finite ex \<and> laststate (?t, ex) = ?t \<and> mk_trace (ALM_ioa 0 id2)\<cdot>ex = nil" by (auto intro: exI[where x="?ex"])
            qed
          next
            assume in_abort:"(s1, s2) \<midarrow>Abort id1\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*The case where the second ALM aborts*}
            show ?thesis
            proof  -
              let ?ex = "[(Abort 0, ?t')!]"
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
              proof -
                from in_abort and `id1 \<noteq> 0` have "s1' = s1" and pre_s2:"~ aborted s2 & (\<exists> c . phase s2 c \<noteq> Sleep)" and trans_s2:"s2' = s2\<lparr>aborted:= True\<rparr>" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
                from pre_s2 and `P6 (s1, s2)` have pre_t:"~ aborted ?t  & (\<exists> c . phase ?t c \<noteq> Sleep)" apply (force simp add:ref_mapping_def P6_def) done
                moreover from trans_s2 and `s1' = s1` have trans_t:"?t' = ?t\<lparr>aborted:= True\<rparr>" by (auto simp add: fun_eq_iff ref_mapping_def)
                ultimately show ?thesis  apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(simp add:ALM_trans_def) done
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          next
            fix h
            assume in_lin:"(s1, s2) \<midarrow>Linearize 0 h\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*If the composition executes Linearize 0*}
            show ?thesis
            proof  -
              let ?ex = "[(Linearize 0 h, ?t')!]"
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
              proof -
                from in_lin and `id1 \<noteq> 0` have "s2' = s2" and pre_s1:"initialized s1 & ~ aborted s1 & h \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))" and trans_s1:"s1' = s1\<lparr>hist := h, initialized := True\<rparr>"  apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
                have pre_t:"initialized ?t & ~ aborted ?t & h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                proof -
                  from  pre_s1 have "~ aborted s1" by auto
                  with `P9 (s1, s2)` have "~ aborted ?t" and "initialized ?t" by (auto simp add:ref_mapping_def P9_def)
                  moreover have "h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                  proof -
                    from `\<not> aborted s1` have "hist ?t = hist s1" using `P6 (s1, s2)` and `P2 (s1, s2)`  by (auto simp add:P6_def P2_def ref_mapping_def)
                    moreover have "pendingReqs s1 \<subseteq> pendingReqs ?t" 
                    proof auto
                      fix x
                      assume "x \<in> pendingReqs s1"
                      moreover note `\<not> aborted s1` and `P6 (s1 ,s2)`
                      ultimately obtain c where "x = pending s1 c" and "phase s1 c = Pending" and "pending s1 c \<notin> set (hist s1)" by (auto simp add:pendingReqs_def P6_def)
                      thus "x \<in> pendingReqs ?t" using `hist ?t = hist s1` by (force simp add:ref_mapping_def pendingReqs_def)
                    qed
                    moreover from pre_s1 have "h \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))" by auto
                    ultimately show ?thesis by (auto simp add: postfix_all_def linearizations_def)
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have trans_t: "?t' = ?t\<lparr>hist := h, initialized := True\<rparr>"
                proof -
                  have "hist ?t' = hist s1'"
                  proof -
                    from pre_s1 have "~ aborted s1" by auto
                    with  `P6 (s1, s2)` and `P2 (s1, s2)` have "hist s2 = []" by (auto simp add:P6_def P2_def)
                    with `s2' = s2` show ?thesis by (auto simp add:ref_mapping_def)
                  qed
                  with trans_s1 have "hist ?t' = h" by auto
                  thus ?thesis using `s2' = s2` and trans_s1 by (auto simp add:ref_mapping_def fun_eq_iff)
                qed
                ultimately show ?thesis  apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(auto simp add:ALM_trans_def) done
              qed
              ultimately show ?thesis by (auto intro: exI[where x="?ex"])
            qed
          next
            fix h
            assume in_lin:"(s1, s2) \<midarrow>Linearize id1 h\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*If the composition executes Linearize id1*}
            let ?ex = "[(Linearize id1 h, ?t')!]"
            have "Finite ?ex" by auto
            moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
            moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
            moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
            proof -
              from in_lin and `id1 \<noteq> 0` have "s1' = s1" and pre_s2: "initialized s2 \<and> \<not> aborted s2 \<and> h \<in> postfix_all (hist s2) (linearizations (pendingReqs s2))" and trans_s2: "s2' = s2\<lparr>hist := h\<rparr>"  apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
              have pre_t:"initialized ?t \<and> \<not> aborted ?t \<and> h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
              proof -
                have  "\<not> aborted ?t" and "initialized ?t" using pre_s2 by (auto simp add:ref_mapping_def)
                moreover have "h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                proof -
                  from pre_s2 have "initialized s2" by auto
                  hence "suffixeq (hist s1) (hist s2)" using `P14 (s1, s2)` by (auto simp add:P14_def suffixeq_def)
                  hence "hist ?t = hist s2"  by (auto simp add:ref_mapping_def)
                  moreover have "pendingReqs s2 \<subseteq> pendingReqs ?t"
                  proof auto
                    fix x
                    assume "x \<in> pendingReqs s2"
                    from this obtain c where "x = pending s2 c" and "phase s2 c \<in> {Pending, Aborted}" and "pending s2 c \<notin> set (hist s2)" by (auto simp add:pendingReqs_def)
                    with `P6 (s1, s2)` and `hist ?t = hist s2` show "x \<in> pendingReqs ?t" by (force simp add:ref_mapping_def P6_def pendingReqs_def)
                  qed
                  moreover from pre_s2 have "h \<in> postfix_all (hist s2) (linearizations (pendingReqs s2))" by auto
                  ultimately show ?thesis by (auto simp add:postfix_all_def linearizations_def)
                qed
                ultimately show ?thesis by auto
              qed
              moreover have trans_t: "?t' = ?t\<lparr>hist := h\<rparr>"
              proof -
                from pre_s2 and trans_s2 have "initialized s2'" by auto
                hence "suffixeq (hist s1') (hist s2')"  using `P14 (s1', s2')` by (auto simp add:P14_def suffixeq_def)
                hence "hist ?t' = hist s2'" by (auto simp add:ref_mapping_def)
                with trans_s2 and `s1' = s1` show ?thesis by (auto simp add:ref_mapping_def fun_eq_iff)
              qed
              ultimately show ?thesis  apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(auto simp add:ALM_trans_def) done
            qed
            
            ultimately show ?thesis by  (auto intro: exI[where x="?ex"])
          next
            fix c r h
            assume in_switch:"(s1, s2) \<midarrow>Switch c id1 h r\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
              -- {*If the composition switches internally*}
            show ?thesis
            proof -
              let ?ex = "nil"
              have "Finite ?ex" by auto
              moreover have "laststate (?t, ?ex) = ?t" by (simp add: laststate_def)
              moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
              moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)" by (auto simp add:is_exec_frag_def)
              moreover have "?t' = ?t"
              proof -
                from in_switch and `id1 \<noteq> 0` have pre_s1:"aborted s1 \<and> phase s1 c = Pending \<and> r = pending s1 c \<and> (if initialized s1 then (h \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))) else (h : postfix_all (l_c_p (initHists s1)) (linearizations (initValidReqs s1))))" and trans_s1: "s1' = s1\<lparr>phase := (phase s1)(c := Aborted)\<rparr>" apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done 
                have pre_s2:"phase s2 c = Sleep" and trans_s2: "s2' = s2 \<lparr>initHists := {h} \<union> (initHists s2), phase := (phase s2)(c := Pending), pending := (pending s2)(c := r)\<rparr>"
                proof -
                  from pre_s1 have "phase s1 c = Pending" by auto
                  with `P6 (s1, s2)` have "phase s2 c = Sleep" apply (simp add:P6_def) by (metis phase.simps(10))
                  with in_switch and `id1 \<noteq> 0` and `id1 < id2` show "phase s2 c = Sleep" and  "s2' = s2 \<lparr>initHists := {h} \<union> (initHists s2), phase := (phase s2)(c := Pending), pending := (pending s2)(c := r)\<rparr>"  apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def P6_def) done
                qed
                from pre_s1 and pre_s2 and trans_s1 and trans_s2 and `P1a (s1, s2)` have "pending ?t c = pending ?t' c & initHists ?t = initHists ?t' & hist ?t = hist ?t' & aborted ?t = aborted ?t' \<and> phase ?t' c = phase ?t c" by (simp add:ref_mapping_def fun_eq_iff P1a_def)
                moreover note pre_s1 and pre_s2 and trans_s1 and trans_s2
                ultimately show ?thesis by (force simp add:ref_mapping_def fun_eq_iff)
              qed
              ultimately show ?thesis  by (auto intro: exI[where x="?ex"])
            qed
          next
            fix h
            assume in_initialize:"(s1, s2) \<midarrow>Initialize 0 h\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
            hence False  using `P10 (s1, s2)` apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def P10_def) done 
            thus ?thesis by  auto
          next
            fix h
            assume in_initialize:"(s1, s2) \<midarrow>Initialize id1 h\<midarrow>composeALMs id1 id2\<rightarrow> (s1', s2')"
            -- {*If the second ALM of the composition initializes*}
            let ?ex = "[(Linearize id1 h, ?t')!]"
            have "Finite ?ex" by auto
            moreover have "laststate (?t, ?ex) = ?t'" by (simp add: laststate_def)
            moreover have "mk_trace (ALM_ioa 0 id2)\<cdot>?ex = nil" by (simp add: mk_trace_def externals_def asig_inputs_def asig_outputs_def asig_of_def ALM_ioa_def ALM_asig_def)
            moreover have "is_exec_frag (ALM_ioa 0 id2) (?t, ?ex)"
            proof -
              from in_initialize and `id1 \<noteq> 0` have "s1' = s1" and pre_s2:"(\<exists> c . phase s2 c \<noteq> Sleep) \<and> \<not> aborted s2 \<and> \<not> initialized s2 \<and> h \<in> postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2))" and trans_s2:"s2' = s2\<lparr>hist := h, initialized := True\<rparr>"  apply (simp_all add: composeALMs_def trans_of_def hide_def  par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def ALM_ioa_def ALM_asig_def) apply(auto simp add:ALM_trans_def) done
              have pre_t:"initialized ?t \<and> \<not> aborted ?t \<and> h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
              proof -
                from pre_s2 have "initialized ?t \<and> \<not> aborted ?t" by (auto simp add:ref_mapping_def)
                moreover have "h \<in> postfix_all (hist ?t) (linearizations (pendingReqs ?t))"
                proof -
                  from pre_s2 have "h \<in> postfix_all (l_c_p (initHists s2)) (linearizations (initValidReqs s2))" and "\<not> initialized s2" and "\<exists> c . phase s2 c \<noteq> Sleep" by auto
                  with `P13 (s1, s2)` have "h \<in> postfix_all (hist s1) (linearizations (pendingReqs s1))" by (auto simp add:P13_def)
                  moreover from `\<not> initialized s2` and `P10 (s1, s2)` have "hist ?t = hist s1" by (auto simp add:ref_mapping_def P10_def)
                  moreover have "pendingReqs s1 \<subseteq> pendingReqs ?t"
                  proof auto
                    fix x
                    assume "x \<in> pendingReqs s1"
                    from this obtain c where "x = pending s1 c" and "phase s1 c \<in> {Pending, Aborted}" and "pending s1 c \<notin> set (hist s1)" by (auto simp add:pendingReqs_def)
                    show "x \<in> pendingReqs ?t"
                    proof (cases "phase s1 c = Pending")
                      assume "phase s1 c = Pending"
                      with `x = pending s1 c` and `pending s1 c \<notin> set (hist s1)` and `hist ?t = hist s1` show ?thesis by (force simp add:ref_mapping_def pendingReqs_def)
                    next
                      assume "phase s1 c \<noteq> Pending"
                      with `phase s1 c \<in> {Pending, Aborted}` have "phase s1 c = Aborted" by auto
                      with `\<not> initialized s2` and `P6 (s1, s2)` and `P7 (s1, s2)` have "pending s2 c = pending s1 c" and "phase s2 c \<in> {Pending, Aborted}" by (auto simp add:P6_def P7_def)
                      with `x = pending s1 c` and `pending s1 c \<notin> set (hist s1)` and `hist ?t = hist s1` and `P6 (s1, s2)` show ?thesis by (auto simp add:ref_mapping_def pendingReqs_def P6_def) 
                    qed
                  qed
                  ultimately show ?thesis by (auto simp add:postfix_all_def linearizations_def)
                qed
                ultimately show ?thesis by auto
              qed
              moreover have trans_t:"?t' = ?t\<lparr>hist := h\<rparr>"
              proof -
                from pre_s2 have "\<exists> c . phase s2 c \<noteq> Sleep" by auto
                with trans_s2 have "initialized s2'" and "\<exists> c . phase s2' c \<noteq> Sleep" by auto
                hence "suffixeq (hist s1') (hist s2')" using `P14 (s1', s2')` by (auto simp add:P14_def suffixeq_def)
                hence "hist ?t' = hist s2'" by (auto simp add:ref_mapping_def)
                with trans_s2 and `s1' = s1` show ?thesis by (auto simp add:ref_mapping_def fun_eq_iff)
              qed
              ultimately show ?thesis  apply (simp add: is_exec_frag_def composeALMs_def trans_of_def hide_def  ALM_ioa_def ALM_asig_def par_def actions_def asig_outputs_def asig_inputs_def asig_internals_def asig_of_def) apply(auto simp add:ALM_trans_def) done
            qed
            ultimately show ?thesis by (auto intro: exI[where x="?ex"])
          qed 
        qed
      qed
    qed
  qed
qed

end
