(*
Author:  Christian Sternagel
Author:  René Thiemann
*)
section \<open>Positions (of terms, contexts, etc.)\<close>

text \<open>Positions are just list of natural numbers, and here we define
  standard notions such as the prefix-relation, parallel positions, left-of, etc.
  Note that we also instantiate lists in certain ways, such that 
  we can write $p^n$ for the n-fold concatenation of the position $p$.\<close>

theory Position
  imports
    "HOL-Library.Infinite_Set"
    "HOL-Library.Sublist"
    Show.Shows_Literal
begin

type_synonym pos = "nat list"

definition less_eq_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infix "\<le>\<^sub>p" 50) where
  "p \<le>\<^sub>p q \<longleftrightarrow> (\<exists>r. p @ r = q)"

definition less_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infix "<\<^sub>p" 50) where
  "p <\<^sub>p q \<longleftrightarrow> p \<le>\<^sub>p q \<and> p \<noteq> q"

lemma less_eq_pos_eq_prefix: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "less_eq_pos = Sublist.prefix"
  unfolding less_eq_pos_def Sublist.prefix_def by metis

lemma less_pos_eq_strict_prefix: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "less_pos = Sublist.strict_prefix"
  unfolding less_pos_def less_eq_pos_def Sublist.strict_prefix_def Sublist.prefix_def by metis

interpretation order_pos: order less_eq_pos less_pos
  by (standard) (auto simp: less_eq_pos_def less_pos_def)

lemma Nil_least [intro!, simp]:
  "[] \<le>\<^sub>p p"
  by (auto simp: less_eq_pos_def)

lemma less_eq_pos_simps [simp]:
  "p \<le>\<^sub>p p @ q" 
  "p @ q1 \<le>\<^sub>p p @ q2 \<longleftrightarrow> q1 \<le>\<^sub>p q2"
  "i # q1 \<le>\<^sub>p [] \<longleftrightarrow> False"
  "i # q1 \<le>\<^sub>p j # q2 \<longleftrightarrow> i = j \<and> q1 \<le>\<^sub>p q2"
  "p @ q \<le>\<^sub>p p \<longleftrightarrow> q = []"
  "p \<le>\<^sub>p [] \<longleftrightarrow> p = []"
  by (auto simp: less_eq_pos_def)

lemma less_eq_pos_code [code]:
  "([] :: pos) \<le>\<^sub>p p = True" 
  "(i # q1 \<le>\<^sub>p []) = False"
  "(i # q1 \<le>\<^sub>p j # q2) = (i = j \<and> q1 \<le>\<^sub>p q2)"
  by auto

lemma less_pos_simps[simp]: 
  "(p <\<^sub>p p @ q) = (q \<noteq> [])" 
  "(p @ q1 <\<^sub>p p @ q2) = (q1 <\<^sub>p q2)" 
  "(p <\<^sub>p []) = False"
  "(i # q1 <\<^sub>p j # q2) = (i = j \<and> q1 <\<^sub>p q2)"
  "(p @ q <\<^sub>p p) = False"
  by (auto simp: less_pos_def)

lemma prefix_smaller [simp]:
  assumes "p <\<^sub>p q" shows "size p < size q"
  using assms by (auto simp: less_pos_def less_eq_pos_def)

instantiation list :: (type) one
begin
  definition one_list_def [simp]: "1 = []"
  instance by (intro_classes)
end

instantiation list :: (type) times
begin
  definition times_list_def [simp]: "times p q = p @ q"
  instance by (intro_classes)
end

instantiation list :: (type) semigroup_mult
begin
  instance by (intro_classes) simp
end

instantiation list :: (type) power
begin
  instance by (intro_classes)
end

lemma power_append_distr:
  "p ^ (m + n) = p ^ m @ p ^ n"
  by (induct m) auto

lemma power_pos_Suc: "p ^ Suc n = p ^ n @ p"
proof -
  have "p ^ Suc n = p ^ (n + Suc 0)" by simp
  also have "... = p ^ n @ p" unfolding power_append_distr by auto 
  finally show ?thesis .
qed

lemma power_subtract_less_eq:
  "p ^ (n - m) \<le>\<^sub>p p ^ n"
proof (cases "m \<ge> n")
  case False
  then have "(n - m) + m = n" by auto
  then show ?thesis unfolding less_eq_pos_def using power_append_distr by metis
qed simp

lemma power_size: fixes p :: "pos" shows "size (p ^ n) = size p * n" 
 by (induct n, simp, auto)

fun remove_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list option"
  where
    "remove_prefix [] ys = Some ys"
  | "remove_prefix (x#xs) (y#ys) = (if x = y then remove_prefix xs ys else None)"
  | "remove_prefix xs ys = None"

lemma remove_prefix [simp]:
  "remove_prefix (x # xs) ys =
    (case ys of
      [] \<Rightarrow> None
    | z # zs \<Rightarrow> if x = z then remove_prefix xs zs else None)"
  by (cases ys) auto

lemma remove_prefix_Some [simp]:
  "remove_prefix xs ys = Some zs \<longleftrightarrow> ys = xs @ zs"
  by (induct xs ys rule: remove_prefix.induct) (auto)

lemma remove_prefix_append [simp]:
  "remove_prefix xs (xs @ ys) = Some ys"
  by simp

lemma less_eq_pos_remove_prefix:
  assumes "p \<le>\<^sub>p q"
  obtains r where "q = p @ r" and "remove_prefix p q = Some r"
  using assms by (induct p arbitrary: q) (auto simp: less_eq_pos_def)

lemma suffix_exists:
  assumes "p \<le>\<^sub>p q"
  shows "\<exists>r. p @ r = q \<and> remove_prefix p q = Some r"
  using assms by (elim less_eq_pos_remove_prefix) auto

fun remove_suffix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list option"
  where
    "remove_suffix p q =
      (case remove_prefix (rev p) (rev q) of
        None \<Rightarrow> None
      | Some r \<Rightarrow> Some (rev r))"

lemma remove_suffix_Some [simp]:
  "remove_suffix xs ys = Some zs \<longleftrightarrow> ys = zs @ xs"
  by (auto split: option.splits) (metis rev_append rev_rev_ident)

lemma Nil_power [simp]: "[] ^ n = []" by (induct n) auto

fun parallel_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" (infixr "\<bottom>" 64)
  where
    "[] \<bottom> _ \<longleftrightarrow> False"
  | "_ \<bottom> [] \<longleftrightarrow> False"
  | "i # p \<bottom> j # q \<longleftrightarrow> i \<noteq> j \<or> p \<bottom> q"

lemma parallel_pos_eq_parallel: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "parallel_pos = Sublist.parallel"
proof (intro ext)
  fix xs ys
  show "xs \<bottom> ys \<longleftrightarrow> xs \<parallel> ys"
  proof (induction xs ys rule: parallel_pos.induct)
    case (1 uu)
    thus ?case
      by simp
  next
    case (2 v va)
    thus ?case
      by simp
  next
    case (3 i p j q)
    thus ?case
      by fastforce
  qed
qed

lemma parallel_pos: "p \<bottom> q = (\<not> p \<le>\<^sub>p q \<and> \<not> q \<le>\<^sub>p p)"
  by (induct p q rule: parallel_pos.induct) auto

lemma parallel_remove_prefix: "p1 \<bottom> p2 \<Longrightarrow>
  \<exists> p i j q1 q2. p1 = p @ i # q1 \<and> p2 = p @ j # q2 \<and> i \<noteq> j"
proof (induct p1 p2 rule: parallel_pos.induct)
  case (3 i p j q)
  then show ?case by simp (metis Cons_eq_append_conv)
qed auto

lemma pos_cases: "p \<le>\<^sub>p q \<or> q <\<^sub>p p \<or> p \<bottom> q"
  by (induct p q rule: parallel_pos.induct)
    (auto simp: less_pos_def)

lemma parallel_pos_sym: "p1 \<bottom> p2 \<Longrightarrow> p2 \<bottom> p1"
  unfolding parallel_pos by auto

lemma less_pos_def': "(p <\<^sub>p q) = (\<exists> r. q = p @ r \<and> r \<noteq> [])" (is "?l = ?r")
  by (auto simp: less_pos_def less_eq_pos_def)

lemma pos_append_cases: 
  "p1 @ p2 = q1 @ q2 \<Longrightarrow>
    (\<exists> q3. p1 = q1 @ q3 \<and> q2 = q3 @ p2) \<or> 
    (\<exists> p3. q1 = p1 @ p3 \<and> p2 = p3 @ q2)"
proof (induct p1 arbitrary: q1)
  case Nil
  then show ?case by auto
next
  case (Cons i p1' q1) note IH = this
  show ?case 
  proof (cases q1)
    case Nil
    then show ?thesis using IH(2) by auto
  next
    case (Cons j q1')
    with IH(2) have id: "p1' @ p2 = q1' @ q2" and ij: "i = j" by auto
    from IH(1)[OF id]
    show ?thesis unfolding Cons ij by auto
  qed
qed

lemma pos_less_eq_append_not_parallel:
 assumes "q \<le>\<^sub>p p @ q'"
 shows "\<not> (q \<bottom> p)"
proof-
  from assms obtain r where "q @ r = p @ q'" unfolding less_eq_pos_def ..  
  then have dec:"(\<exists> q3. q = p @ q3 \<and> q' = q3 @ r) \<or> 
   (\<exists> p3. p = q @ p3 \<and> r = p3 @ q')" (is "?a \<or> ?b") by (rule pos_append_cases)
  then have "p \<le>\<^sub>p q \<or> q \<le>\<^sub>p p" unfolding less_eq_pos_def by blast
  then show ?thesis unfolding parallel_pos by auto
qed

lemma less_pos_power_split: "q <\<^sub>p p ^ m \<Longrightarrow> \<exists> p' k. q = p ^ k @ p' \<and> p' <\<^sub>p p \<and> k < m"
proof (induct m arbitrary: q)
  case 0
  then show ?case by auto
next
  case (Suc n q)
  show ?case
  proof (cases "q <\<^sub>p p")
    case True
    show ?thesis
      by (rule exI[of _ q], rule exI[of _ 0], insert True, auto)
  next
    case False
    from Suc(2) obtain r where pn: "p @ p^n = q @ r" unfolding less_pos_def' by auto
    from pos_append_cases[OF this]
    have "\<exists> r. q = p @ r"
    proof
      assume "\<exists> s. p = q @ s \<and> r = s @ p ^ n"
      then obtain s where p: "p = q @ s" by auto
      with False show ?thesis by auto
    qed auto
    then obtain r where q: "q = p @ r" by auto
    with Suc(2) have "r <\<^sub>p p ^ n" by simp
    from Suc(1)[OF this] obtain p' k where r: "r = p ^ k @ p'" "p' <\<^sub>p p" "k < n" by auto
    show ?thesis unfolding q
      by (rule exI[of _ p'], rule exI[of _ "Suc k"], insert r, auto)
  qed
qed

definition showsl_pos :: "pos \<Rightarrow> showsl" where
  "showsl_pos = showsl_list_gen (\<lambda> i. showsl (Suc i)) (STR ''empty'') (STR '''') (STR ''.'') (STR '''')" 

fun proper_prefix_list :: "pos \<Rightarrow> pos list"
  where
    "proper_prefix_list [] = []" |
    "proper_prefix_list (i # p) = [] # map (Cons i) (proper_prefix_list p)"

lemma proper_prefix_list [simp]: "set (proper_prefix_list p) = {q. q <\<^sub>p p}"
proof (induction p)
  case (Cons i p)
  note IH = this
  show ?case (is "?l = ?r")
  proof (rule set_eqI)
    fix q
    show "q \<in> ?l = (q \<in> ?r)"
    proof (cases q)
      case Nil
      have less: "[] <\<^sub>p i # p" unfolding less_pos_def by auto
      show ?thesis unfolding Nil using less by auto
    next
      case (Cons j q')
      show ?thesis unfolding Cons by (auto simp: IH)
    qed
  qed
qed simp

definition prefix_list :: "pos \<Rightarrow> pos list"
  where
    "prefix_list p = p # proper_prefix_list p"

lemma proper_prefix_list_append_self_eq_prefixes: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "proper_prefix_list xs @ [xs] = Sublist.prefixes xs"
proof (induction xs)
  case Nil
  show ?case
    by simp
next
  case (Cons a xs)
  thus ?case
    by (metis (no_types, lifting) append_Cons list.simps(8) list.simps(9) map_append
        prefixes.simps(2) proper_prefix_list.simps(2))
qed

lemma rotate1_prefix_list_eq_prefixes: \<^marker>\<open>contributor \<open>Martin Desharnais\<close>\<close>
  "rotate1 (prefix_list xs) = Sublist.prefixes xs"
  unfolding prefix_list_def rotate1.simps
  using proper_prefix_list_append_self_eq_prefixes .

lemma prefix_list [simp]: "set (prefix_list p) = { q. q \<le>\<^sub>p p}"
  by (auto simp: prefix_list_def)

definition bounded_postfixes :: "pos \<Rightarrow> pos list \<Rightarrow> pos list"
  where
    "bounded_postfixes p ps = map the [opt\<leftarrow>map (remove_prefix p) ps . opt \<noteq> None]"

lemma bounded_postfixes [simp]:
  "set (bounded_postfixes p ps) = { r. p @ r \<in> set ps}" (is "?l = ?r")
  by (auto simp: bounded_postfixes_def)
    (metis (mono_tags, lifting) image_eqI mem_Collect_eq option.sel remove_prefix_append)

definition left_of_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool" 
  where
    "left_of_pos p q = (\<exists>r i j. r @ [i] \<le>\<^sub>p p \<and> r @ [j] \<le>\<^sub>p q \<and> i < j)"

lemma left_of_pos_append:
  "left_of_pos p q \<Longrightarrow> left_of_pos (p @ p') (q @ q')"
  apply (simp add: left_of_pos_def)
  using less_eq_pos_simps(1) order_pos.order.trans by blast

lemma append_left_of_pos:
  "left_of_pos p q = left_of_pos (p' @ p) (p' @ q)"
proof (rule iffI)
  assume "left_of_pos p q"
  then show "left_of_pos (p' @ p) (p' @ q)"
    unfolding left_of_pos_def by (metis less_eq_pos_simps(2) append_assoc)
next
  assume "left_of_pos (p' @ p) (p' @ q)"
  then show "left_of_pos p q"
  proof (induct p' arbitrary: p q rule:rev_induct)
    case (snoc a p')
    then have IH:"left_of_pos (p' @ p) (p' @ q) \<Longrightarrow> left_of_pos p q" and 
      left:"left_of_pos ((p' @ [a]) @ p) ((p' @ [a]) @ q)" by auto
    from left[unfolded left_of_pos_def] have "left_of_pos (p' @ (a # p)) (p' @ (a # q))"
      by (metis append_assoc append_Cons append.left_neutral snoc.prems)
    with IH have "left_of_pos (a # p) (a # q)" unfolding left_of_pos_def by (metis left_of_pos_def snoc.hyps) 
    then obtain r i j r' r'' where x:"r @ [i] @ r' = a # p" and y:"(r @ [j]) @ r'' = a # q" 
      and ij:"i < j" unfolding left_of_pos_def less_eq_pos_def by auto
    then have "[] <\<^sub>p r" unfolding less_pos_def'
      by (metis append_Nil append_Cons not_less_iff_gr_or_eq list.inject)
    with x obtain rr where "r = a # rr" using list.exhaust[of r]
      by (metis less_eq_pos_simps(1) less_eq_pos_simps(4) less_pos_simps(1) append.left_neutral)
    with x y have "rr @ [i] @ r' = p" and y:"(rr @ [j]) @ r'' = q" by auto
    with ij show ?case unfolding left_of_pos_def less_eq_pos_def by auto
  qed simp
qed

lemma left_pos_parallel: "left_of_pos p q \<Longrightarrow> q \<bottom> p" unfolding left_of_pos_def
proof -
  assume "\<exists>r i j. r @ [i] \<le>\<^sub>p p \<and> r @ [j] \<le>\<^sub>p q \<and> i < j"
  then obtain r i j where rp:"r @ [i] \<le>\<^sub>p p" and rq:"r @ [j] \<le>\<^sub>p q" and ij:"i < j" by auto
  from rp obtain p' where rp:"p = r @ i #  p'" unfolding less_eq_pos_def by auto
  from rq obtain q' where rq:"q = (r @ (j # q'))" unfolding less_eq_pos_def by auto
  from rp rq ij have pq:"\<not> p \<le>\<^sub>p q" by force
  from rp rq ij have "\<not> q \<le>\<^sub>p p" by force 
  with pq show ?thesis using parallel_pos by auto
qed

lemma left_of_append_cases:" left_of_pos (p0 @ p1) q \<Longrightarrow> p0 <\<^sub>p q \<or> left_of_pos p0 q"
proof -
  assume "left_of_pos (p0 @ p1) q"
  then obtain r i j where rp:"r @ [i] \<le>\<^sub>p (p0 @ p1)" and rq:"r @ [j] \<le>\<^sub>p q" and ij:"i < j" 
    unfolding left_of_pos_def by auto
  show ?thesis proof(cases "p0 \<le>\<^sub>p r")
    case True
    with rq have "p0 <\<^sub>p q"
      by (metis less_eq_pos_simps(1) less_eq_pos_simps(5) less_pos_def list.simps(3) order_pos.order.trans)
    then show ?thesis by auto
  next
    case False
    then have aux:"\<not> (\<exists> r'. p0 @ r' = r)" unfolding less_eq_pos_def by auto
    from rp have par:"\<not> (r @ [i] \<bottom> p0)" using pos_less_eq_append_not_parallel by auto
    from aux have a:"\<not> (p0 \<le>\<^sub>p r)" unfolding less_eq_pos_def by auto
    from rp have "\<not> (p0 \<bottom> r)"
      using less_eq_pos_simps(1) order_pos.order.trans parallel_pos pos_less_eq_append_not_parallel by blast
    with a have "r <\<^sub>p p0" using pos_cases by auto
    then obtain oo where p0:"p0 = r @ oo" and "[] <\<^sub>p oo" unfolding less_pos_def less_eq_pos_def by auto 
    have "\<not> (p0 <\<^sub>p r @ [i])" unfolding less_pos_def less_eq_pos_def
      by (metis aux butlast_append butlast_snoc self_append_conv)
    with par have "r @ [i] \<le>\<^sub>p p0" using pos_cases by auto
    with ij this[unfolded less_eq_pos_def] have "left_of_pos p0 q" unfolding left_of_pos_def using rq by auto
    then show ?thesis by auto
  qed
qed

lemma append_left_of_cases:
  assumes left: "left_of_pos q (p0 @ p1)"
  shows "p0 <\<^sub>p q \<or> left_of_pos q p0"
proof -
  from left obtain r i j where rp:"r @ [i] \<le>\<^sub>p q" and rq:"r @ [j] \<le>\<^sub>p (p0 @ p1)" and ij:"i < j"
    unfolding left_of_pos_def by auto
  show ?thesis proof(cases "p0 \<le>\<^sub>p r")
    case True
    with rp have "p0 <\<^sub>p q" unfolding less_pos_def
      by (meson less_eq_pos_simps(1) less_eq_pos_simps(5) list.simps(3) order_pos.order.trans)
    then show ?thesis by auto
  next
    case False
    then have aux:"\<not> (\<exists> r'. p0 @ r' = r)" unfolding less_eq_pos_def by auto
    from rp rq have par:"\<not> (r @ [j] \<bottom> p0)" using pos_less_eq_append_not_parallel by auto
    from aux have a:"\<not> (p0 \<le>\<^sub>p r)" unfolding less_eq_pos_def by auto
    from rq have "\<not> (p0 \<bottom> r)"
      using less_eq_pos_simps(1) order_pos.order.trans parallel_pos pos_less_eq_append_not_parallel by blast
    with a have "r <\<^sub>p p0" using pos_cases by auto
    then obtain oo where p0:"p0 = r @ oo" and "[] <\<^sub>p oo" unfolding less_pos_def less_eq_pos_def by auto 
    have "\<not> (p0 <\<^sub>p r @ [j])" unfolding less_pos_def less_eq_pos_def using p0 a list.exhaust[of p0]
      by (metis append_Nil2 aux butlast_append butlast_snoc)
    with par have "r @ [j] \<le>\<^sub>p p0" using pos_cases by auto
    with ij this[unfolded less_eq_pos_def] have "left_of_pos q p0" unfolding left_of_pos_def using rp by auto
    then show ?thesis by auto
  qed
qed

lemma parallel_imp_right_or_left_of:
  assumes par:"p \<bottom> q" shows "left_of_pos p q \<or> left_of_pos q p"
proof -
  from parallel_remove_prefix[OF par] obtain r i j p' q' where "p = r @ i# p'" and "q = r @ j # q'" 
    and ij:"i \<noteq> j" by blast
  then have "r @ [i] \<le>\<^sub>p p \<and> r @ [j] \<le>\<^sub>p q" by simp
  then show ?thesis unfolding left_of_pos_def using ij less_linear by blast
qed

lemma left_of_imp_not_right_of:
  assumes l:"left_of_pos p q" shows "\<not> left_of_pos q p"
proof
  assume l':"left_of_pos q p"
  from l obtain r i j where "r @ [i] \<le>\<^sub>p p" and ij:"i < j" and "r @ [j] \<le>\<^sub>p q" unfolding left_of_pos_def by blast
  then obtain p0 q0 where p:"p = (r @ [i]) @ p0" and q:"q = (r @ [j]) @ q0" unfolding less_eq_pos_def by auto
  from l' obtain r' i' j' where "r' @ [j'] \<le>\<^sub>p p" and ij':"i' < j'" and "r' @ [i'] \<le>\<^sub>p q" unfolding left_of_pos_def by blast
  then obtain p0' q0' where p':"p = (r' @ [j']) @ p0'" and q':"q = (r' @ [i']) @ q0'" unfolding less_eq_pos_def by auto
  from p p' have p:"r @ (i # p0) = r' @ (j' # p0')"  by auto
  from q q' have q:"r @ (j # q0) = r' @ (i' # q0')"  by auto
  with p ij ij' have ne:"r \<noteq> r'" using same_append_eq[of r] by (metis less_imp_not_less list.inject)
  have nlt:"\<not> r <\<^sub>p r'" proof
    assume "r <\<^sub>p r'"
    then obtain r2 where r1:"r' = r @ r2" and r2:"r2 \<noteq> []" unfolding less_pos_def less_eq_pos_def by auto
    from p have p':"i # p0 = r2 @ j' # p0'" unfolding r1 append_assoc using less_eq_pos_simps(2) by auto
    from q have q':"j # q0 = r2 @ i' # q0'" unfolding r1 append_assoc using less_eq_pos_simps(2) by auto
    from r2 obtain k rr where r2:"r2 = k# rr" by (cases r2, auto)
    from p' q' ij list.inject show False unfolding r2 by simp
  qed
  have "\<not> r' <\<^sub>p r" proof
    assume "r' <\<^sub>p r"
    then obtain r2 where r1:"r = r' @ r2" and r2:"r2 \<noteq> []" unfolding less_pos_def less_eq_pos_def by auto
    from p have p':"r2 @ i # p0 = j' # p0'" unfolding r1 append_assoc using less_eq_pos_simps(2) by auto
    from q have q':"r2 @ j # q0 = i' # q0'" unfolding r1 append_assoc using less_eq_pos_simps(2) by auto
    from r2 obtain k rr where r2:"r2 = k# rr" by (cases r2, auto)
    from p' q' ij' list.inject show False unfolding r2 by simp
  qed
  with nlt ne have "r \<bottom> r'" by (auto simp: parallel_pos less_pos_def)
  with p q show False by (metis less_eq_pos_simps(1) pos_less_eq_append_not_parallel)
qed

primrec is_left_of :: "pos \<Rightarrow> pos \<Rightarrow> bool"
  where
    left_Nil: "is_left_of [] q = False"
  | left_Cons: "is_left_of (i # p) q =
      (case q of 
        [] \<Rightarrow> False 
      | j # q' \<Rightarrow> if i < j then True else if i > j then False else is_left_of p q')" 

lemma is_left_of: "is_left_of p q = left_of_pos p q"
proof
  assume l:"is_left_of p q"
  then show "left_of_pos p q" 
  proof (induct p arbitrary:q)
    case Nil
    with left_Nil show ?case by auto
  next
    case (Cons i p) note IH = this
    assume l:"is_left_of (i # p) q"
    show ?case
    proof (cases q)
      case Nil 
      with l show ?thesis unfolding left_Cons by auto
    next
      case (Cons j q') 
      show ?thesis
      proof (cases "\<not> (i < j)", cases "j < i")
        case True
        with l Cons show ?thesis unfolding left_Cons by auto
      next
        assume "\<not> j < i" and "\<not> i < j"
        then have ij:"i = j" by auto
        with Cons l have "is_left_of p q'" unfolding left_Cons by auto
        with IH have "left_of_pos p q'" by blast
        with ij show "left_of_pos (i # p) q" unfolding Cons left_of_pos_def 
          by (metis append_Cons less_eq_pos_simps(4))
      next
        assume ij:"\<not> \<not> (i < j)"
        then have "[] @ [i] \<le>\<^sub>p (i # p) \<and> [] @ [j] \<le>\<^sub>p (j # q')" unfolding less_eq_pos_def by auto
        with Cons ij show ?thesis unfolding left_of_pos_def by blast
      qed
    qed
  qed
next
  assume l:"left_of_pos p q"
  from this[unfolded left_of_pos_def] obtain r i j where "r @[i] \<le>\<^sub>p p" and "r @ [j] \<le>\<^sub>p q" 
    and ij:"i < j" by blast
  then obtain p' q' where "p = (r @[i]) @ p'" and "q = (r @[j]) @ q'" unfolding less_eq_pos_def 
    by auto
  then show "is_left_of p q"
  proof (induct r arbitrary: p q p' q')
    case Nil
    assume p:"p = ([] @ [i]) @ p'" and q:"q = ([] @ [j]) @ q'"
    with l[unfolded p q append_Nil] show ?case using left_Cons ij by force
  next
    case (Cons k r') note IH = this
    assume p:"p = ((k # r') @ [i]) @ p'" and q:"q = ((k # r') @ [j]) @ q'"
    from ij have "left_of_pos ((r' @ [i]) @ p') (( r' @ [j]) @ q')" unfolding left_of_pos_def
      by (metis less_eq_pos_def)
    with IH have "is_left_of ((r' @ [i]) @ p') (( r' @ [j]) @ q')" by auto
    then show "is_left_of p q" unfolding p q  using left_Cons by force
  qed
qed

abbreviation right_of_pos :: "pos \<Rightarrow> pos \<Rightarrow> bool"
where
  "right_of_pos p q \<equiv> left_of_pos q p"

lemma remove_prefix_same [simp]:
  "remove_prefix p p = Some []"
  by (induct p) simp_all

definition "pos_diff p q = the (remove_prefix q p)"

lemma prefix_pos_diff [simp]:
  assumes "p \<le>\<^sub>p q"
  shows "p @ pos_diff q p = q"
  using suffix_exists [OF assms] by (auto simp: pos_diff_def)

lemma pos_diff_Nil2 [simp]:
  "pos_diff p [] = p"
  by (auto simp: pos_diff_def)

lemma inj_nat_to_pos: "inj (rec_nat [] Cons)" (is "inj ?f")
  unfolding inj_on_def
proof (intro ballI impI)
  fix x y
  show "?f x = ?f y \<Longrightarrow> x = y"
  proof (induct x arbitrary: y)
    case 0
    then show ?case by (cases y, auto)
  next
    case (Suc x sy)
    then obtain y where sy: "sy = Suc y" by (cases sy, auto)
    from Suc(2)[unfolded sy] have id: "?f x = ?f y" by auto
    from Suc(1)[OF this] sy show ?case by simp
  qed
qed

lemma infinite_UNIV_pos[simp]: "infinite (UNIV :: pos set)"
proof
  assume "finite (UNIV :: pos set)"
  from finite_subset[OF _ this, of "range (rec_nat [] Cons)"]
    range_inj_infinite[OF inj_nat_to_pos]
  show False by blast
qed

lemma less_pos_right_mono:
  "p @ q <\<^sub>p r @ q \<Longrightarrow> p <\<^sub>p r" 
proof (induct q rule: rev_induct)
  case (snoc x xs)
  thus ?case 
    by (simp add: less_pos_def less_eq_pos_def)
      (metis append_is_Nil_conv butlast_append butlast_snoc list.simps(3))
qed auto

lemma less_pos_left_mono:
  "p @ q <\<^sub>p p @ r \<Longrightarrow> q <\<^sub>p r"
  by auto

end