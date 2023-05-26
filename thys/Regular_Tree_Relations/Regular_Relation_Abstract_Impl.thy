theory Regular_Relation_Abstract_Impl
  imports Pair_Automaton
    GTT_Transitive_Closure
    RR2_Infinite_Q_infinity
    Horn_Fset
begin

abbreviation TA_of_lists where
  "TA_of_lists \<Delta> \<Delta>\<^sub>E \<equiv> TA (fset_of_list \<Delta>) (fset_of_list \<Delta>\<^sub>E)"

section \<open>Computing the epsilon transitions for the composition of GTT's\<close>

definition \<Delta>\<^sub>\<epsilon>_rules :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) horn set" where
  "\<Delta>\<^sub>\<epsilon>_rules A B =
    {zip ps qs \<rightarrow>\<^sub>h (p, q) |f ps p qs q. f ps \<rightarrow> p |\<in>| rules A \<and> f qs \<rightarrow> q |\<in>| rules B \<and> length ps = length qs} \<union>
    {[(p, q)] \<rightarrow>\<^sub>h (p', q) |p p' q. (p, p') |\<in>| eps A} \<union>
    {[(p, q)] \<rightarrow>\<^sub>h (p, q') |p q q'. (q, q') |\<in>| eps B}"

locale \<Delta>\<^sub>\<epsilon>_horn =
  fixes A :: "('q, 'f) ta" and B :: "('q, 'f) ta"
begin

sublocale horn "\<Delta>\<^sub>\<epsilon>_rules A B" .

lemma \<Delta>\<^sub>\<epsilon>_infer0:
  "infer0 = {(p, q) |f p q. f [] \<rightarrow> p |\<in>| rules A \<and> f [] \<rightarrow> q |\<in>| rules B}"
  unfolding horn.infer0_def \<Delta>\<^sub>\<epsilon>_rules_def
  using zip_Nil[of "[]"]
  by auto (metis length_greater_0_conv zip_eq_Nil_iff)+

lemma \<Delta>\<^sub>\<epsilon>_infer1:
  "infer1 pq X = {(p, q) |f ps p qs q. f ps \<rightarrow> p |\<in>| rules A \<and> f qs \<rightarrow> q |\<in>| rules B \<and> length ps = length qs \<and>
    (fst pq, snd pq) \<in> set (zip ps qs) \<and> set (zip ps qs) \<subseteq> insert pq X} \<union>
    {(p', snd pq) |p p'. (p, p') |\<in>| eps A \<and> p = fst pq} \<union>
    {(fst pq, q') |q q'. (q, q') |\<in>| eps B \<and> q = snd pq}"
  unfolding \<Delta>\<^sub>\<epsilon>_rules_def horn_infer1_union
  apply (intro arg_cong2[of _ _ _ _ "(\<union>)"])
    by (auto simp: horn.infer1_def simp flip: ex_simps(1)) force+

lemma \<Delta>\<^sub>\<epsilon>_sound:
  "\<Delta>\<^sub>\<epsilon>_set A B = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using lr unfolding x
  proof (induct)
    case (\<Delta>\<^sub>\<epsilon>_set_cong f ps p qs q) show ?case
      apply (intro infer[of "zip ps qs" "(p, q)"])
      subgoal using \<Delta>\<^sub>\<epsilon>_set_cong(1-3) by (auto simp: \<Delta>\<^sub>\<epsilon>_rules_def)
      subgoal using \<Delta>\<^sub>\<epsilon>_set_cong(3,5) by (auto simp: zip_nth_conv)
      done
  next
    case (\<Delta>\<^sub>\<epsilon>_set_eps1 p p' q) then show ?case
      by (intro infer[of "[(p, q)]" "(p', q)"]) (auto simp: \<Delta>\<^sub>\<epsilon>_rules_def)
  next
    case (\<Delta>\<^sub>\<epsilon>_set_eps2 q q' p) then show ?case
      by (intro infer[of "[(p, q)]" "(p, q')"]) (auto simp: \<Delta>\<^sub>\<epsilon>_rules_def)
  qed
next
  case (rl x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using rl unfolding x
  proof (induct)
    case (infer as a) then show ?case
      using \<Delta>\<^sub>\<epsilon>_set_cong[of _ "map fst as" "fst a" A "map snd as" "snd a" B]
        \<Delta>\<^sub>\<epsilon>_set_eps1[of _ "fst a" A "snd a" B] \<Delta>\<^sub>\<epsilon>_set_eps2[of _ "snd a" B "fst a" A]
      by (auto simp: \<Delta>\<^sub>\<epsilon>_rules_def)
  qed
qed

end

section \<open>Computing the epsilon transitions for the transitive closure of GTT's\<close>

definition \<Delta>_trancl_rules :: "('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) horn set" where
  "\<Delta>_trancl_rules A B =
    \<Delta>\<^sub>\<epsilon>_rules A B \<union> {[(p, q), (q, r)] \<rightarrow>\<^sub>h (p, r) |p q r. True}"

locale \<Delta>_trancl_horn =
  fixes A :: "('q, 'f) ta" and B :: "('q, 'f) ta"
begin

sublocale horn "\<Delta>_trancl_rules A B" .

lemma \<Delta>_trancl_infer0:
  "infer0 = horn.infer0 (\<Delta>\<^sub>\<epsilon>_rules A B)"
  by (auto simp: \<Delta>\<^sub>\<epsilon>_rules_def \<Delta>_trancl_rules_def horn.infer0_def)

lemma \<Delta>_trancl_infer1:
  "infer1 pq X = horn.infer1 (\<Delta>\<^sub>\<epsilon>_rules A B) pq X \<union>
   {(r, snd pq) |r p'. (r, p') \<in> X \<and> p' = fst pq} \<union>
   {(fst pq, r) |q' r. (q', r) \<in> (insert pq X) \<and> q' = snd pq}"
  unfolding \<Delta>_trancl_rules_def horn_infer1_union Un_assoc
  apply (intro arg_cong2[of _ _ _ _ "(\<union>)"] HOL.refl)
  by (auto simp: horn.infer1_def simp flip: ex_simps(1)) force+

lemma \<Delta>_trancl_sound:
  "\<Delta>_trancl_set A B = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using lr unfolding x
  proof (induct)
    case (\<Delta>_set_cong f ps p qs q) show ?case
      apply (intro infer[of "zip ps qs" "(p, q)"])
      subgoal using \<Delta>_set_cong(1-3) by (auto simp: \<Delta>_trancl_rules_def \<Delta>\<^sub>\<epsilon>_rules_def)
      subgoal using \<Delta>_set_cong(3,5) by (auto simp: zip_nth_conv)
      done
  next
    case (\<Delta>_set_eps1 p p' q) then show ?case
      by (intro infer[of "[(p, q)]" "(p', q)"]) (auto simp: \<Delta>_trancl_rules_def \<Delta>\<^sub>\<epsilon>_rules_def)
  next
    case (\<Delta>_set_eps2 q q' p) then show ?case
      by (intro infer[of "[(p, q)]" "(p, q')"]) (auto simp: \<Delta>_trancl_rules_def \<Delta>\<^sub>\<epsilon>_rules_def)
  next
    case (\<Delta>_set_trans p q r) then show ?case
      by (intro infer[of "[(p,q), (q,r)]" "(p, r)"]) (auto simp: \<Delta>_trancl_rules_def \<Delta>\<^sub>\<epsilon>_rules_def)
  qed
next
  case (rl x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using rl unfolding x
  proof (induct)
    case (infer as a) then show ?case
      using \<Delta>_set_cong[of _ "map fst as" "fst a" A "map snd as" "snd a" B]
        \<Delta>_set_eps1[of _ "fst a" A "snd a" B] \<Delta>_set_eps2[of _ "snd a" B "fst a" A]
        \<Delta>_set_trans[of "fst a" "snd (hd as)" A B "snd a"]
      by (auto simp: \<Delta>_trancl_rules_def \<Delta>\<^sub>\<epsilon>_rules_def)
  qed
qed

end

section \<open>Computing the epsilon transitions for the transitive closure of pair automata\<close>

definition \<Delta>_Atr_rules :: "('q \<times> 'q) fset \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q, 'f) ta \<Rightarrow> ('q \<times> 'q) horn set" where
  "\<Delta>_Atr_rules Q A B =
    {[] \<rightarrow>\<^sub>h (p, q) | p q. (p , q) |\<in>| Q} \<union>
    {[(p, q),(r, v)] \<rightarrow>\<^sub>h (p, v) |p q r v. (q, r) |\<in>| \<Delta>\<^sub>\<epsilon> B A}"

locale \<Delta>_Atr_horn =
  fixes Q :: "('q \<times> 'q) fset" and A :: "('q, 'f) ta" and B :: "('q, 'f) ta"
begin

sublocale horn "\<Delta>_Atr_rules Q A B" .

lemma \<Delta>_Atr_infer0: "infer0 = fset Q"
  by (auto simp: horn.infer0_def \<Delta>_Atr_rules_def)
  
lemma \<Delta>_Atr_infer1:
  "infer1 pq X = {(p, snd pq) | p q. (p, q) \<in> X \<and> (q, fst pq) |\<in>| \<Delta>\<^sub>\<epsilon> B A} \<union>
   {(fst pq, v) | q r v. (snd pq, r) |\<in>| \<Delta>\<^sub>\<epsilon> B A \<and> (r, v) \<in> X} \<union>
   {(fst pq, snd pq) | q . (snd pq, fst pq) |\<in>| \<Delta>\<^sub>\<epsilon> B A}"
  unfolding \<Delta>_Atr_rules_def horn_infer1_union
  by (auto simp: horn.infer1_def simp flip: ex_simps(1)) force+

lemma \<Delta>_Atr_sound:
  "\<Delta>_Atrans_set Q A B = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using lr unfolding x
  proof (induct)
    case (base p q)
    then show ?case
      by (intro infer[of "[]" "(p, q)"]) (auto simp: \<Delta>_Atr_rules_def)
  next
    case (step p q r v)
    then show ?case
      by (intro infer[of "[(p, q), (r, v)]" "(p, v)"]) (auto simp: \<Delta>_Atr_rules_def)
  qed
next
  case (rl x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using rl unfolding x
  proof (induct)
    case (infer as a) then show ?case
      using base[of "fst a" "snd a" Q A B]
      using \<Delta>_Atrans_set.step[of "fst a" _ Q A B "snd a"]
      by (auto simp: \<Delta>_Atr_rules_def) blast
  qed
qed

end

section \<open>Computing the Q infinity set for the infinity predicate automaton\<close>

definition Q_inf_rules :: "('q, 'f option \<times> 'g option) ta \<Rightarrow> ('q \<times> 'q) horn set" where
  "Q_inf_rules A =
    {[] \<rightarrow>\<^sub>h (ps ! i, p) |f ps p i. (None, Some f) ps \<rightarrow> p |\<in>| rules A \<and> i < length ps} \<union>
    {[(p, q)] \<rightarrow>\<^sub>h (p, r) |p q r. (q, r) |\<in>| eps A} \<union>
    {[(p, q), (q, r)] \<rightarrow>\<^sub>h (p, r) |p q r. True}"

locale Q_horn =
  fixes A :: "('q, 'f option \<times> 'g option) ta"
begin

sublocale horn "Q_inf_rules A" .

lemma Q_infer0:
  "infer0 = {(ps ! i, p) |f ps p i. (None, Some f) ps \<rightarrow> p |\<in>| rules A \<and> i < length ps}"
  unfolding horn.infer0_def Q_inf_rules_def by auto

lemma Q_infer1:
  "infer1 pq X = {(fst pq, r) | q r. (q, r) |\<in>| eps A \<and> q = snd pq} \<union>
    {(r, snd pq) |r p'. (r, p') \<in> X \<and> p' = fst pq} \<union>
    {(fst pq, r) |q' r. (q', r) \<in> (insert pq X) \<and> q' = snd pq}"
  unfolding Q_inf_rules_def horn_infer1_union
  by (auto simp: horn.infer1_def simp flip: ex_simps(1)) force+

lemma Q_sound:
  "Q_inf A = saturate"
proof (intro set_eqI iffI, goal_cases lr rl)
  case (lr x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using lr unfolding x
  proof (induct)
    case (trans p q r)
    then show ?case
      by (intro infer[of "[(p,q), (q,r)]" "(p, r)"])
        (auto simp: Q_inf_rules_def)
  next
    case (rule f qs q i)
    then show ?case
      by (intro infer[of "[]" "(qs ! i, q)"])
        (auto simp: Q_inf_rules_def)
  next
    case (eps p q r)
    then show ?case
      by (intro infer[of "[(p, q)]" "(p, r)"])
        (auto simp: Q_inf_rules_def)
  qed
next
  case (rl x) obtain p q where x: "x = (p, q)" by (cases x)
  show ?case using rl unfolding x
  proof (induct)
    case (infer as a) then show ?case
      using Q_inf.eps[of "fst a" _ A "snd a"]
      using Q_inf.trans[of "fst a" "snd (hd as)" A "snd a"]
      by (auto simp: Q_inf_rules_def intro: Q_inf.rule)
  qed
qed

end


end