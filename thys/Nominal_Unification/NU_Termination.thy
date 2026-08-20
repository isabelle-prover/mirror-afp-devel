(*<*)
theory NU_Termination
imports NU_Mgu
begin
(*>*)

section \<open>Termination\<close>

text \<open>
  Defines a lexicographic termination measure and proves that all the unification
  reductions decrease this measure.  
\<close>


lemma apply_subst_equivalence: 
  shows "apply_subst s P = (apply_subst_eprobs s (fst P), apply_subst_fprobs s (snd P))"
  unfolding apply_subst_def apply_subst_eprobs_def apply_subst_fprobs_def by simp


fun size_trm :: "trm \<Rightarrow> nat"
  where
  "size_trm (Unit)      = 1" |
  "size_trm (Atom a)    = 1" |
  "size_trm (Susp pi X) = 1" |
  "size_trm (Abst a t)  = 1 + size_trm t" |
  "size_trm (Func F t)  = 1 + size_trm t" |
  "size_trm (Paar t t') = 1 + (size_trm t) + (size_trm t')"

fun size_fprobs :: "fprobs \<Rightarrow> nat"
  where 
    "size_fprobs [] = 0" |
    "size_fprobs (x#xs) = (size_trm (snd x))+(size_fprobs xs)"

fun size_eprobs :: "eprobs \<Rightarrow> nat"
  where
 "size_eprobs [] = 0" | 
  "size_eprobs (x#xs) = (size_trm (fst x))+(size_trm (snd x))+(size_eprobs xs)"


lemma size_swap [simp]: "size_trm (swap pi t) = size_trm t"
  by (induct t) auto

definition rank_r
  where
  "rank_r = measures [\<lambda>(eprobs, fprobs). card (vars_eprobs eprobs),
                      \<lambda>(eprobs, fprobs). size_eprobs eprobs, 
                      \<lambda>(eprobs, fprobs). size_fprobs fprobs]"


lemma vars_term_finite [simp]: "finite (vars_trm t)"
  by (induct t) auto


lemma vars_eprobs_finite [simp]: "finite (vars_eprobs P)"
  by (induct P) auto


lemma not_occurs_trm: "\<not>occurs X t \<longrightarrow> X\<notin> vars_trm t"
  by (induct t) auto

lemma not_occurs_subst: "\<not>occurs X t1\<longrightarrow> X\<notin> vars_trm (subst [(X,swap pi2 t1)] t2)" 
  using subst_susp not_occurs_trm by (induct t2) (auto simp add: vars_swap)

lemma not_occurs_list: "\<not> occurs X t \<longrightarrow>
  X \<notin> vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs)"
  using not_occurs_subst apply_subst_eprobs_def by (induct xs) auto


lemma vars_equ: 
  assumes "\<not>occurs X t1" and "occurs X t2"
  shows "vars_trm (subst [(X, swap pi t1)] t2) = (vars_trm t1 \<union> vars_trm t2)-{X}"
  using assms
proof(induct t2)
  case (Susp pi' Y)
  hence eq: "X=Y" 
    unfolding occurs.simps(3) by argo
  have subst_i: "subst [(X, swap pi t1)] (Susp pi' Y) = swap pi'(look_up X [(X, swap pi t1)])"
    using eq subst_susp by simp
  also have "... = swap pi'(swap pi t1)" by simp
  hence "vars_trm (subst [(X, swap pi t1)] (Susp pi' Y)) =  vars_trm t1"
    using subst_i swap_append vars_swap by simp
  thus
    "vars_trm (subst [(X, swap pi t1)] (Susp pi' Y)) = 
    vars_trm t1 \<union> vars_trm (Susp pi' Y) - {X}"
    using eq assms(1) not_occurs_subst[of X t1 pi \<open>Susp pi' Y\<close>] by auto
next
  case (Paar t21 t22)
  hence "occurs X t21 \<or> occurs X t22"
    unfolding occurs.simps(5) by argo
  then show ?case
  proof
    assume "occurs X t21" 
    hence "vars_trm (subst [(X, swap pi t1)] t21) = vars_trm t1 \<union> vars_trm t21 - {X}"
      using assms(1) Paar by auto 
    hence "vars_trm (subst [(X, swap pi t1)] (Paar t21 t22)) =
    (vars_trm t1 \<union> vars_trm t21 - {X}) \<union> (vars_trm t1 \<union> vars_trm t22 - {X})"
      using Paar.hyps(2) assms(1) subst_not_occurs[of X t22 \<open>swap pi t1\<close>] not_occurs_trm
      by (cases "occurs X t22") auto
    thus "vars_trm (subst [(X, swap pi t1)] (Paar t21 t22)) =
    vars_trm t1 \<union> vars_trm (Paar t21 t22) - {X}" by auto
  next
    assume "occurs X t22"
     hence "vars_trm (subst [(X, swap pi t1)] t22) = vars_trm t1 \<union> vars_trm t22 - {X}"
       using assms(1) Paar by auto
     hence "vars_trm (subst [(X, swap pi t1)] (Paar t21 t22)) =
    (vars_trm t1 \<union> vars_trm t21 - {X}) \<union> (vars_trm t1 \<union> vars_trm t22 - {X})"
      using Paar.hyps(1) assms(1) subst_not_occurs[of X t21 \<open>swap pi t1\<close>] not_occurs_trm
      by (cases "occurs X t21") auto
    thus "vars_trm (subst [(X, swap pi t1)] (Paar t21 t22)) =
    vars_trm t1 \<union> vars_trm (Paar t21 t22) - {X}" by auto
  qed
qed (simp_all)


lemma vars_subseteq:
  assumes "\<not>occurs X t "
  shows "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> (vars_trm t \<union> vars_eprobs xs)"
  using assms
proof(induct xs)
  case Nil
  have "apply_subst_eprobs [(X, swap pi t)] [] = []"
    unfolding apply_subst_eprobs_def by simp
  hence "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] []) = {}"
    by simp
  thus "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] []) \<subseteq> vars_trm t \<union> vars_eprobs []"
    by simp
next
  case (Cons a xs)
  have "apply_subst_eprobs [(X, swap pi t)] (a # xs) = 
  (subst [(X, swap pi t)] (fst a), subst [(X, swap pi t)] (snd a)) # (apply_subst_eprobs[(X, swap pi t)] xs)"
    unfolding apply_subst_eprobs_def case_prod_beta by simp
  hence A: "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] (a # xs)) = 
    (vars_trm (subst [(X, swap pi t)] (snd a)))\<union>(vars_trm (subst [(X, swap pi t)] (fst a)))
    \<union>(vars_eprobs (apply_subst_eprobs[(X, swap pi t)] xs))"
    by auto
  then show "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] (a # xs))
    \<subseteq> vars_trm t \<union> vars_eprobs (a # xs)"
  proof(cases "occurs X (fst a)")
    case True
    have X_in_fst: 
      "occurs X (fst a)" by fact
    hence vars_fst:
      "vars_trm (subst [(X, swap pi t)] (fst a)) = (vars_trm t \<union> vars_trm (fst a))-{X}"
      using vars_equ[OF assms X_in_fst] by simp
    then show "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] (a # xs))
    \<subseteq> vars_trm t \<union> vars_eprobs (a # xs)"
    proof(cases "occurs X (snd a)")
      case True
      have X_in_snd: "occurs X (snd a)" by fact
      hence vars_snd:
        "vars_trm (subst [(X, swap pi t)] (snd a)) = (vars_trm t \<union> vars_trm (snd a))-{X}"
        using vars_equ[OF assms X_in_snd] by simp
      with vars_fst
      have "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a))  = 
      vars_trm t \<union> vars_trm (snd a) \<union> vars_trm (fst a) - {X}"
        by auto
      hence "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a)) \<subseteq> 
      vars_trm t \<union> vars_eprobs (a # xs)" by auto
      thus ?thesis using A Cons by auto
    next
      case False
      hence vars_snd: "vars_trm (subst [(X, swap pi t)] (snd a)) = vars_trm (snd a)"
        using subst_not_occurs by auto
      with vars_fst
      have "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a))  = 
      vars_trm t \<union> vars_trm (snd a) \<union> vars_trm (fst a) - {X}"
        using False not_occurs_trm by auto
      hence "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a)) \<subseteq> 
      vars_trm t \<union> vars_eprobs (a # xs)" by auto
      thus ?thesis using A Cons by auto
    qed
  next
    case False
    hence vars_fst:
      "vars_trm (subst [(X, swap pi t)] (fst a)) = vars_trm (fst a)"
      using subst_not_occurs by simp
    then show "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] (a # xs))
    \<subseteq> vars_trm t \<union> vars_eprobs (a # xs)"
    proof(cases "occurs X (snd a)")
      case True
      have X_in_snd: "occurs X (snd a)" by fact
      hence vars_snd:
        "vars_trm (subst [(X, swap pi t)] (snd a)) = (vars_trm t \<union> vars_trm (snd a))-{X}"
        using vars_equ[OF assms X_in_snd] by simp
       with vars_fst
      have "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a))  = 
      vars_trm t \<union> vars_trm (snd a) \<union> vars_trm (fst a) - {X}"
        using False not_occurs_trm by auto
      hence "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a)) \<subseteq> 
      vars_trm t \<union> vars_eprobs (a # xs)" by auto
      thus ?thesis using A Cons by auto
    next
      case False
      hence vars_snd: "vars_trm (subst [(X, swap pi t)] (snd a)) = vars_trm (snd a)"
        using subst_not_occurs by auto
      with vars_fst
      have "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a))  = 
       vars_trm (snd a) \<union> vars_trm (fst a)"
        by simp
      hence "vars_trm (subst [(X, swap pi t)] (snd a)) \<union> vars_trm (subst [(X, swap pi t)] (fst a)) \<subseteq> 
      vars_trm t \<union> vars_eprobs (a # xs)" by auto
      thus ?thesis using A Cons by auto
    qed
  qed
qed


lemma vars_decrease: 
  assumes "\<not>occurs X t"
  shows "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 < card (insert X (vars_trm t \<union> vars_eprobs xs))"
  using assms
proof(cases "X \<in> (vars_trm t \<union> vars_eprobs xs)")
  case True
  hence "insert X (vars_trm t \<union> vars_eprobs xs) = vars_trm t \<union> vars_eprobs xs"
    using  insert_absorb by auto
  moreover have subset:
    "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> vars_trm t \<union> vars_eprobs xs"
    using assms vars_subseteq by simp
  hence
    "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> vars_trm t \<union> vars_eprobs xs - {X}"
    using not_occurs_list assms subset_Diff_insert by auto
  ultimately have 
  "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 \<le> card (vars_trm t \<union> vars_eprobs xs - {X})"    
    using Finite_Set.card_mono
    by (metis finite_Diff finite_Un vars_eprobs_finite vars_term_finite)
  thus "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 < card (insert X (vars_trm t \<union> vars_eprobs xs))"
    by (simp add: card.insert_remove)
next
  case False
  hence "card (vars_trm t \<union> vars_eprobs xs) < card (insert X (vars_trm t \<union> vars_eprobs xs))"
    by auto
  moreover have subset:
    "vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs) \<subseteq> vars_trm t \<union> vars_eprobs xs"
    using assms vars_subseteq by simp
  hence "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
                 \<le> card (vars_trm t \<union> vars_eprobs xs)"
    using Finite_Set.card_mono
    by (metis finite_Un vars_eprobs_finite vars_term_finite)
  ultimately show 
    "card (vars_eprobs (apply_subst_eprobs [(X, swap pi t)] xs))
    < card (insert X (vars_trm t \<union> vars_eprobs xs))"
    by simp
qed


lemma rank_r_cred: 
  assumes "P1\<turnstile>(nabla)\<rightarrow>P2" 
  shows "(P2, P1) \<in> rank_r"
  unfolding rank_r_def by (cases rule: c_red.cases[OF \<open>P1 \<turnstile> nabla \<rightarrow> P2\<close>], simp_all)

lemma rank_r_sred:
  assumes "P1 \<turnstile>  s \<leadsto>P2"
  shows "(P2,P1) \<in> rank_r"
proof(cases rule: s_red.cases[OF \<open>P1\<turnstile> s \<leadsto>P2\<close>])
  case (2 t1 t2 s1 s2 xs ys)
   case (2 t1 t2 s1 s2 xs ys)
  let ?union = "vars_trm s1 \<union> vars_trm s2 \<union> vars_trm t1 \<union> vars_trm t2 \<union> vars_eprobs xs"
    and ?size = "size_trm t1 + size_trm t2 + size_trm s1 + size_trm s2 + size_eprobs xs"
  from 2 have "vars_eprobs ((Paar t1 t2, Paar s1 s2) # xs) = ?union"
    unfolding vars_eprobs.simps vars_trm.simps by auto
  moreover from 2 have
    "size_eprobs ((Paar t1 t2, Paar s1 s2) # xs) = 2 + ?size"
    unfolding size_eprobs.simps using size_trm.simps(6) by auto
  from 2 have
  "vars_eprobs ((t1, s1) # (t2, s2) # xs) = ?union"
    unfolding vars_eprobs.simps by auto
  moreover from 2 have 
    "size_eprobs ((t1, s1) # (t2, s2) # xs) = ?size"
    unfolding size_eprobs.simps by simp
  ultimately have 
    "size_eprobs ((t1, s1) # (t2, s2) # xs) < size_eprobs ((Paar t1 t2, Paar s1 s2) # xs)"
    "card (vars_eprobs ((t1, s1) # (t2, s2) # xs)) = card (vars_eprobs ((Paar t1 t2, Paar s1 s2) # xs))"
    by simp+
  with 2 show "(P2, P1) \<in> rank_r" 
    unfolding rank_r_def by simp
next
  case (7 pi1 X pi2 xs ys)
  let ?mapds = "map (\<lambda>a. (a, Susp [] X)) (ds_list pi1 pi2) @ ys"
  let ?union = "{X} \<union> vars_eprobs xs"
  from 7 have 
  vars: "vars_eprobs ((Susp pi1 X, Susp pi2 X) # xs) = ?union" and
  size: "size_eprobs ((Susp pi1 X, Susp pi2 X) # xs) = 2 + size_eprobs xs"
    unfolding vars_eprobs.simps size_eprobs.simps by simp+
  then show "(P2, P1) \<in> rank_r"
     proof(cases "X \<in> vars_eprobs xs")
    case True
   hence "card ?union = card (vars_eprobs xs)"
     by (simp add: insert_absorb)
   with 7 show "(P2, P1) \<in> rank_r" 
      unfolding rank_r_def by simp
  next
    case False
    hence "card ?union = 1 + card (vars_eprobs xs)"
      by auto
    with 7 show "(P2, P1) \<in> rank_r" 
      unfolding rank_r_def by simp
  qed
next
  case (8 X t pi xs ys)
   let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
    and ?size = "size_trm t + size_eprobs xs"
   from 8 have 
     vars: "vars_eprobs ((Susp pi X, t) # xs) = ?union" and
     size: "size_eprobs ((Susp pi X, t) # xs) = 1 + ?size"
    unfolding vars_eprobs.simps size_eprobs.simps by simp+
   moreover from 8 have
    "P2 = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
     using apply_subst_equivalence by auto
   ultimately show ?thesis  
    using 8 vars_decrease[OF 8(4)] unfolding rank_r_def by simp
next
  case (9 X t pi xs ys)
   let ?union = "insert X (vars_trm t \<union> vars_eprobs xs)"
    and ?size = "size_trm t + size_eprobs xs"
  from 9 have 
     vars: "vars_eprobs ((t, Susp pi X) # xs) = ?union" and
     size: "size_eprobs ((t, Susp pi X) # xs) = 1 + ?size"
    unfolding vars_eprobs.simps size_eprobs.simps by simp+
  moreover from 9 have
    "P2 = (apply_subst_eprobs [(X, swap (rev pi) t)] xs, 
    apply_subst_fprobs [(X, swap (rev pi) t)] ys)"
     using apply_subst_equivalence by auto
   ultimately show ?thesis  
    using 9 vars_decrease[OF 9(4)] unfolding rank_r_def by simp
qed (unfold rank_r_def, auto simp add: vars_swap)

lemma rank_r_trans: "\<lbrakk>(P1,P2) \<in> rank_r; (P2,P3) \<in> rank_r\<rbrakk>\<Longrightarrow> (P1,P3)\<in> rank_r"
  unfolding rank_r_def by auto

lemma rank_r_red_plus: 
  assumes "P1\<Turnstile> (s,nabla)\<Rightarrow>P2" 
  shows "(P2, P1) \<in> rank_r"
  using assms 
by(induct rule: red_plus.induct)(auto dest: rank_r_sred rank_r_cred rank_r_trans)

lemma wf_rank_r: 
  shows "wf (rank_r)"
  unfolding rank_r_def by simp

(*<*)
end
(*>*)
