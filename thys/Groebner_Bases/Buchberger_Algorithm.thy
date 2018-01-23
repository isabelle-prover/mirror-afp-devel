(* Author: Fabian Immler, Alexander Maletzky *)

section \<open>Buchberger's Algorithm\<close>

theory Buchberger_Algorithm
imports Groebner_Bases General
begin

text \<open>This theory implements Buchberger's algorithm for computing Gr\"obner bases, and proves it
  totally correct. The implementation incorporates Buchberger's chain- and product criterion for
  avoiding useless pairs.\<close>

type_synonym ('a, 'b) apT = "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list"
type_synonym ('a, 'b) critT = "(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"

subsection \<open>The @{emph \<open>add_pairs\<close>} Parameter\<close>

context gd_powerprod
begin

definition add_pairs_set :: "('a, 'b::zero) apT \<Rightarrow> bool"
  where "add_pairs_set apf \<longleftrightarrow> (\<forall>bs rs h. set (apf rs bs h) = set rs \<union> Pair h ` set bs)"

lemma add_pairs_setI:
  assumes "\<And>bs rs h. set (apf rs bs h) = set rs \<union> Pair h ` set bs"
  shows "add_pairs_set apf"
  using assms by (auto simp add: add_pairs_set_def)

lemma add_pairs_setD:
  assumes "add_pairs_set apf"
  shows "set (apf rs bs h) = set rs \<union> Pair h ` set bs"
  using assms by (auto simp add: add_pairs_set_def)

lemma add_pairs_setD2:
  assumes "add_pairs_set apf" and "(a, b) \<in> set (apf ps bs h)"
  shows "(a, b) \<in> set ps \<or> (a = h \<and> b \<in> set bs)"
proof -
  from assms(2) have "(a, b) \<in> set ps \<union> Pair h ` set bs" by (simp only: add_pairs_setD[OF assms(1)])
  thus "(a, b) \<in> set ps \<or> (a = h \<and> b \<in> set bs)" by auto
qed

lemma add_pairs_setD3:
  assumes "add_pairs_set apf" and "set ps \<subseteq> (set bs) \<times> (set bs)"
  shows "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)"
proof
  fix x y
  assume "(x, y) \<in> set (apf ps bs h)"
  with assms(1) have "(x, y) \<in> set ps \<or> (x = h \<and> y \<in> set bs)" by (rule add_pairs_setD2)
  thus "(x, y) \<in> set (h # bs) \<times> set (h # bs)"
  proof
    assume "(x, y) \<in> set ps"
    from this assms(2) have "(x, y) \<in> (set bs) \<times> (set bs)" ..
    thus ?thesis by simp
  next
    assume "x = h \<and> y \<in> set bs"
    thus ?thesis by simp
  qed
qed

lemma add_pairs_set_inI1:
  assumes "add_pairs_set apf" and "p \<in> set ps"
  shows "p \<in> set (apf ps bs h)"
  using assms by (simp add: add_pairs_setD)

lemma add_pairs_set_inI2:
  assumes "add_pairs_set apf" and "p \<in> set bs"
  shows "(h, p) \<in> set (apf ps bs h)"
  using assms by (simp add: add_pairs_setD)

lemma fst_add_pairs_subset:
  assumes "add_pairs_set apf"
  shows "fst ` set (apf rs bs h) \<subseteq> insert h (fst ` set rs)"
proof -
  from assms have "set (apf rs bs h) = set rs \<union> Pair h ` set bs" by (rule add_pairs_setD)
  hence "fst ` set (apf rs bs h) = fst ` (set rs \<union> Pair h ` set bs)" by simp
  thus ?thesis by auto
qed

lemma snd_add_pairs_subset:
  assumes "add_pairs_set apf"
  shows "snd ` set (apf rs bs h) \<subseteq> (snd ` set rs) \<union> set bs"
proof -
  from assms have "set (apf rs bs h) = set rs \<union> Pair h ` set bs" by (rule add_pairs_setD)
  hence "snd ` set (apf rs bs h) = snd ` (set rs \<union> Pair h ` set bs)" by simp
  thus ?thesis by auto
qed

definition add_pairs_naive :: "('a, 'b) apT"
  where "add_pairs_naive ps bs h \<equiv> ps @ (map (Pair h) bs)"

lemma add_pairs_set_add_pairs_naive: "add_pairs_set add_pairs_naive"
  by (simp add: add_pairs_set_def add_pairs_naive_def)

primrec add_pairs_sorted :: "('a, 'b::zero) apT" where
  "add_pairs_sorted ps [] _ = ps"|
  "add_pairs_sorted ps (b # bs) h =
    add_pairs_sorted (insort_wrt (\<lambda>_ y. lcs (lp h) (lp b) \<preceq> lcs (lp (fst y)) (lp (snd y))) (h, b) ps) bs h"

lemma add_pairs_set_add_pairs_sorted: "add_pairs_set add_pairs_sorted"
  unfolding add_pairs_set_def
proof (intro allI)
  fix bs ps and h::"'a \<Rightarrow>\<^sub>0 'b"
  show "set (add_pairs_sorted ps bs h) = set ps \<union> Pair h ` set bs"
    by (induct bs arbitrary: ps, simp_all)
qed

(* Could be defined tail-recursively, but is usually only called on "small" arguments anyway. *)
primrec pairs :: "('a, 'b) apT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list" where
  "pairs _ [] = []"|
  "pairs apf (x # xs) = apf (pairs apf xs) xs x"

lemma pairsD1:
  assumes "add_pairs_set apf" and "(p, q) \<in> set (pairs apf bs)"
  shows "p \<in> set bs"
  using assms(2)
proof (induct bs)
  assume "(p, q) \<in> set (pairs apf [])"
  thus "p \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs apf xs) \<Longrightarrow> p \<in> set xs"
    and a: "(p, q) \<in> set (pairs apf (x # xs))"
  from a have "(p, q) \<in> set (apf (pairs apf xs) xs x)" by simp
  with assms(1) have "(p, q) \<in> set (pairs apf xs) \<or> (p = x \<and> q \<in> set xs)"
    by (rule add_pairs_setD2)
  thus "p \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (pairs apf xs)"
    hence "p \<in> set xs" by (rule IH)
    thus ?thesis by simp
  next
    assume "p = x \<and> q \<in> set xs"
    thus ?thesis by simp
  qed
qed

lemma pairsD2:
  assumes "add_pairs_set apf" and "(p, q) \<in> set (pairs apf bs)"
  shows "q \<in> set bs"
  using assms(2)
proof (induct bs)
  assume "(p, q) \<in> set (pairs apf [])"
  thus "q \<in> set []" by simp
next
  fix x xs
  assume IH: "(p, q) \<in> set (pairs apf xs) \<Longrightarrow> q \<in> set xs"
    and a: "(p, q) \<in> set (pairs apf (x # xs))"
  from a have "(p, q) \<in> set (apf (pairs apf xs) xs x)" by simp
  with assms(1) have "(p, q) \<in> set (pairs apf xs) \<or> (p = x \<and> q \<in> set xs)"
    by (rule add_pairs_setD2)
  thus "q \<in> set (x # xs)"
  proof
    assume "(p, q) \<in> set (pairs apf xs)"
    hence "q \<in> set xs" by (rule IH)
    thus ?thesis by simp
  next
    assume "p = x \<and> q \<in> set xs"
    thus ?thesis by simp
  qed
qed

corollary pairs_subset:
  assumes "add_pairs_set apf"
  shows "set (pairs apf bs) \<subseteq> set bs \<times> set bs"
  by (rule, rule, rule, erule pairsD1[OF assms], erule pairsD2[OF assms])

lemma in_pairsI:
  assumes "add_pairs_set apf" and "p \<noteq> q" and "p \<in> set bs" and "q \<in> set bs"
  shows "(p, q) \<in> set (pairs apf bs) \<or> (q, p) \<in> set (pairs apf bs)"
  using assms(3, 4)
proof (induct bs)
  case Nil
  thus ?case by simp
next
  case (Cons b bs)
  from Cons(3) have d: "q = b \<or> q \<in> set bs" by simp
  from Cons(2) have "p = b \<or> p \<in> set bs" by simp
  thus ?case
  proof
    assume "p = b"
    with assms(2) have "q \<noteq> b" by simp
    with d have "q \<in> set bs" by simp
    with assms(1) have "(p, q) \<in> set (pairs apf (b # bs))" unfolding \<open>p = b\<close> pairs.simps
      by (rule add_pairs_set_inI2)
    thus ?thesis ..
  next
    assume "p \<in> set bs"
    from d show ?thesis
    proof
      assume "q = b"
      from assms(1) \<open>p \<in> set bs\<close> have "(q, p) \<in> set (pairs apf (b # bs))"
        unfolding \<open>q = b\<close> pairs.simps by (rule add_pairs_set_inI2)
      thus ?thesis ..
    next
      assume "q \<in> set bs"
      with \<open>p \<in> set bs\<close> have "(p, q) \<in> set (pairs apf bs) \<or> (q, p) \<in> set (pairs apf bs)"
        by (rule Cons(1))
      thus ?thesis
      proof
        assume "(p, q) \<in> set (pairs apf bs)"
        with assms(1) have "(p, q) \<in> set (pairs apf (b # bs))"
          unfolding pairs.simps by (rule add_pairs_set_inI1)
        thus ?thesis ..
      next
        assume "(q, p) \<in> set (pairs apf bs)"
        with assms(1) have "(q, p) \<in> set (pairs apf (b # bs))"
          unfolding pairs.simps by (rule add_pairs_set_inI1)
        thus ?thesis ..
      qed
    qed
  qed
qed

subsection \<open>@{term processed}\<close>

definition processed::"(('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> bool"
  where "processed p bs ps \<longleftrightarrow> fst p \<in> set bs \<and> snd p \<in> set bs \<and> p \<notin> set ps \<and> (snd p, fst p) \<notin> set ps"

lemma processed_alt:
  "processed (a, b) bs ps \<longleftrightarrow> ((a \<in> set bs) \<and> (b \<in> set bs) \<and> (a, b) \<notin> set ps \<and> (b, a) \<notin> set ps)"
  unfolding processed_def by auto

lemma processedI:
  assumes "f \<in> set bs" and "g \<in> set bs" and "(f, g) \<notin> set ps" and "(g, f) \<notin> set ps"
  shows "processed (f, g) bs ps"
  unfolding processed_alt using assms by simp

lemma processedD1:
  assumes "processed (f, g) bs ps"
  shows "f \<in> set bs"
  using assms by (simp add: processed_alt)

lemma processedD2:
  assumes "processed (f, g) bs ps"
  shows "g \<in> set bs"
  using assms by (simp add: processed_alt)

lemma processedD3:
  assumes "processed (f, g) bs ps"
  shows "(f, g) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processedD4:
  assumes "processed (f, g) bs ps"
  shows "(g, f) \<notin> set ps"
  using assms by (simp add: processed_alt)

lemma processed_Nil: "processed (f, g) bs [] \<longleftrightarrow> (f \<in> set bs \<and> g \<in> set bs)"
  by (simp add: processed_alt)

lemma processed_Cons:
  assumes "processed (f, g) bs ps"
    and a1: "f = p \<Longrightarrow> g = q \<Longrightarrow> thesis"
    and a2: "f = q \<Longrightarrow> g = p \<Longrightarrow> thesis"
    and a3: "processed (f, g) bs ((p, q) # ps) \<Longrightarrow> thesis"
  shows thesis
proof -
  from assms(1) have "f \<in> set bs" and "g \<in> set bs" and "(f, g) \<notin> set ps" and "(g, f) \<notin> set ps"
    by (simp_all add: processed_alt)
  show ?thesis
  proof (cases "(f, g) = (p, q)")
    case True
    hence "f = p" and "g = q" by simp_all
    thus ?thesis by (rule a1)
  next
    case False
    with \<open>(f, g) \<notin> set ps\<close> have *: "(f, g) \<notin> set ((p, q) # ps)" by auto
    show ?thesis
    proof (cases "(g, f) = (p, q)")
      case True
      hence "f = q" and "g = p" by simp_all
      thus ?thesis by (rule a2)
    next
      case False
      with \<open>(g, f) \<notin> set ps\<close> have "(g, f) \<notin> set ((p, q) # ps)" by auto
      with \<open>f \<in> set bs\<close> \<open>g \<in> set bs\<close> * have "processed (f, g) bs ((p, q) # ps)" by (rule processedI)
      thus ?thesis by (rule a3)
    qed
  qed
qed

lemma processed_pairs:
  assumes "add_pairs_set apf" and "f \<noteq> g" and "f \<in> set bs" and "g \<in> set bs"
  shows "\<not> processed (f, g) bs (pairs apf bs)"
proof
  assume "processed (f, g) bs (pairs apf bs)"
  hence "(f, g) \<notin> set (pairs apf bs)" and "(g, f) \<notin> set (pairs apf bs)"
    by (rule processedD3, rule processedD4)
  moreover from assms have "(f, g) \<in> set (pairs apf bs) \<or> (g, f) \<in> set (pairs apf bs)"
    by (rule in_pairsI)
  ultimately show False by simp
qed

lemma processed_add_pairs:
  assumes "add_pairs_set apf" and "processed (f, g) (h # bs) (apf ps bs h)"
  shows "processed (f, g) bs ps \<or> (f = h \<and> g = h)"
proof -
  from assms(2) have d1: "f = h \<or> f \<in> set bs" and d2: "g = h \<or> g \<in> set bs"
    and a: "(f, g) \<notin> set (apf ps bs h)" and b: "(g, f) \<notin> set (apf ps bs h)" by (simp_all add: processed_def)
  from d1 show ?thesis
  proof
    assume "f = h"
    from d2 show ?thesis
    proof
      assume "g = h"
      with \<open>f = h\<close> show ?thesis by simp
    next
      assume "g \<in> set bs"
      with assms(1) have "(f, g) \<in> set (apf ps bs h)" unfolding \<open>f = h\<close> by (rule add_pairs_set_inI2)
      with a show ?thesis ..
    qed
  next
    assume "f \<in> set bs"
    from d2 show ?thesis
    proof
      assume "g = h"
      from assms(1) \<open>f \<in> set bs\<close> have "(g, f) \<in> set (apf ps bs h)" unfolding \<open>g = h\<close> by (rule add_pairs_set_inI2)
      with b show ?thesis ..
    next
      assume "g \<in> set bs"
      from \<open>f \<in> set bs\<close> this have "processed (f, g) bs ps"
      proof (rule processedI)
        show "(f, g) \<notin> set ps"
        proof
          assume "(f, g) \<in> set ps"
          with assms(1) have "(f, g) \<in> set (apf ps bs h)" by (rule add_pairs_set_inI1)
          with a show False ..
        qed
      next
        show "(g, f) \<notin> set ps"
        proof
          assume "(g, f) \<in> set ps"
          with assms(1) have "(g, f) \<in> set (apf ps bs h)" by (rule add_pairs_set_inI1)
          with b show False ..
        qed
      qed
      thus ?thesis ..
    qed
  qed
qed

subsection \<open>The @{emph \<open>crit\<close>} Parameter\<close>

definition crit_conn :: "('a, 'b::field) critT \<Rightarrow> bool"
  where "crit_conn cf \<longleftrightarrow> (\<forall>d m bs ps p q. dickson_grading (+) d \<longrightarrow> set bs \<subseteq> dgrad_p_set d m \<longrightarrow>
                                set ps \<subseteq> set bs \<times> set bs \<longrightarrow>
                                (\<forall>p' q'. processed (p', q') bs ps \<longrightarrow> p' \<noteq> 0 \<longrightarrow> q' \<noteq> 0 \<longrightarrow>
                                    (p' \<noteq> p \<or> q' \<noteq> q) \<longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<longrightarrow>
                                    crit_pair_cbelow_on d m (set bs) p' q') \<longrightarrow>
                                p \<in> set bs \<longrightarrow> q \<in> set bs \<longrightarrow> p \<noteq> 0 \<longrightarrow> q \<noteq> 0 \<longrightarrow> cf ps bs p q \<longrightarrow>
                                crit_pair_cbelow_on d m (set bs) p q)"

lemma crit_connI:
  assumes "\<And>d m bs ps p q.
        dickson_grading (+) d \<Longrightarrow> set bs \<subseteq> dgrad_p_set d m \<Longrightarrow> set ps \<subseteq> set bs \<times> set bs \<Longrightarrow>
        (\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
                  (p' \<noteq> p \<or> q' \<noteq> q) \<Longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<Longrightarrow>
                  crit_pair_cbelow_on d m (set bs) p' q') \<Longrightarrow>
        p \<in> set bs \<Longrightarrow> q \<in> set bs \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> cf ps bs p q \<Longrightarrow>
        crit_pair_cbelow_on d m (set bs) p q"
  shows "crit_conn cf"
  using assms unfolding crit_conn_def by (metis (no_types, lifting))

lemma crit_connD:
  assumes "crit_conn cf" and 1: "dickson_grading (+) d"
    and 2: "set bs \<subseteq> dgrad_p_set d m" and 3: "set ps \<subseteq> set bs \<times> set bs"
    and 4: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
                  (p' \<noteq> p \<or> q' \<noteq> q) \<Longrightarrow> (p' \<noteq> q \<or> q' \<noteq> p) \<Longrightarrow>
                  crit_pair_cbelow_on d m (set bs) p' q'"
    and 5: "p \<in> set bs" and 6: "q \<in> set bs" and 7: "p \<noteq> 0" and 8: "q \<noteq> 0" and 9: "cf ps bs p q"
  shows "crit_pair_cbelow_on d m (set bs) p q"
  using assms unfolding crit_conn_def by blast

definition product_crit :: "('a, 'b::zero) critT"
  where "product_crit ps bs p q \<longleftrightarrow> (gcs (lp p) (lp q) = 0)"

lemma crit_conn_product_crit: "crit_conn product_crit"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume "product_crit ps bs p q"
  hence *: "gcs (lp p) (lp q) = 0" by (simp only: product_crit_def)
  assume "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m"
    and "p \<in> set bs" and "q \<in> set bs" and "p \<noteq> 0" and "q \<noteq> 0"
  from this * show "crit_pair_cbelow_on d m (set bs) p q" by (rule product_criterion)
qed

definition chain_crit :: "('a, 'b::zero) critT"
  where "chain_crit ps bs p q \<longleftrightarrow> (\<exists>r \<in> set bs. r \<noteq> 0 \<and> r \<noteq> p \<and> r \<noteq> q \<and> lp r adds lcs (lp p) (lp q) \<and>
                                    (p, r) \<notin> set ps \<and> (r, p) \<notin> set ps \<and> (q, r) \<notin> set ps \<and> (r, q) \<notin> set ps)"

lemma chain_critE:
  assumes "chain_crit ps bs p q" and "p \<in> set bs" and "q \<in> set bs"
  obtains r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q" and "lp r adds lcs (lp p) (lp q)"
    and "processed (p, r) bs ps" and "processed (r, q) bs ps"
proof -
  from assms(1) obtain r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q"
    and "lp r adds lcs (lp p) (lp q)" and "(p, r) \<notin> set ps" and "(r, p) \<notin> set ps"
    and "(q, r) \<notin> set ps" and "(r, q) \<notin> set ps" unfolding chain_crit_def by blast
  from this(1, 2, 3, 4, 5) show ?thesis
  proof
    from assms(2) \<open>r \<in> set bs\<close> \<open>(p, r) \<notin> set ps\<close> \<open>(r, p) \<notin> set ps\<close> show "processed (p, r) bs ps"
      by (rule processedI)
  next
    from \<open>r \<in> set bs\<close> assms(3) \<open>(r, q) \<notin> set ps\<close> \<open>(q, r) \<notin> set ps\<close> show "processed (r, q) bs ps"
      by (rule processedI)
  qed
qed

lemma crit_conn_chain_crit: "crit_conn chain_crit"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m"
    and *: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
           p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow>  p' \<noteq> q \<or> q' \<noteq> p \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p' q'"
    and "p \<noteq> 0" and "q \<noteq> 0"
  assume "chain_crit ps bs p q" and "p \<in> set bs" and "q \<in> set bs"
  then obtain r where "r \<in> set bs" and "r \<noteq> 0" and "r \<noteq> p" and "r \<noteq> q" and "lp r adds lcs (lp p) (lp q)"
    and "processed (p, r) bs ps" and "processed (r, q) bs ps" by (rule chain_critE)
  from \<open>dickson_grading (+) d\<close> \<open>set bs \<subseteq> dgrad_p_set d m\<close> \<open>p \<in> set bs\<close> \<open>q \<in> set bs\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close>
    \<open>lp r adds lcs (lp p) (lp q)\<close> show "crit_pair_cbelow_on d m (set bs) p q"
  proof (rule chain_criterion)
    from \<open>processed (p, r) bs ps\<close> \<open>p \<noteq> 0\<close> \<open>r \<noteq> 0\<close> show "crit_pair_cbelow_on d m (set bs) p r"
    proof (rule *)
      from \<open>r \<noteq> q\<close> show "p \<noteq> p \<or> r \<noteq> q" by simp
    next
      from \<open>r \<noteq> p\<close> show "p \<noteq> q \<or> r \<noteq> p" by simp
    qed
  next
    from \<open>processed (r, q) bs ps\<close> \<open>r \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show "crit_pair_cbelow_on d m (set bs) r q"
    proof (rule *)
      from \<open>r \<noteq> p\<close> show "r \<noteq> p \<or> q \<noteq> q" by simp
    next
      from \<open>r \<noteq> q\<close> show "r \<noteq> q \<or> q \<noteq> p" by simp
    qed
  qed
qed

definition comb_crit :: "('a, 'b::zero) critT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a, 'b) critT"
  where "comb_crit c1 c2 ps bs p q \<longleftrightarrow> (c1 ps bs p q \<or> c2 ps bs p q)"

lemma crit_conn_comb_crit:
  assumes "crit_conn c1" and "crit_conn c2"
  shows "crit_conn (comb_crit c1 c2)"
proof (rule crit_connI)
  fix d m bs ps p and q::"'a \<Rightarrow>\<^sub>0 'b"
  assume 1: "dickson_grading (+) d" and 2: "set bs \<subseteq> dgrad_p_set d m" and 3: "set ps \<subseteq> set bs \<times> set bs"
    and 4: "\<And>p' q'. processed (p', q') bs ps \<Longrightarrow> p' \<noteq> 0 \<Longrightarrow> q' \<noteq> 0 \<Longrightarrow>
           p' \<noteq> p \<or> q' \<noteq> q \<Longrightarrow>  p' \<noteq> q \<or> q' \<noteq> p \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p' q'"
    and 5: "p \<in> set bs" and 6: "q \<in> set bs" and 7: "p \<noteq> 0" and 8: "q \<noteq> 0"
  assume "comb_crit c1 c2 ps bs p q"
  hence "c1 ps bs p q \<or> c2 ps bs p q" by (simp only: comb_crit_def)
  thus "crit_pair_cbelow_on d m (set bs) p q"
  proof
    assume "c1 ps bs p q"
    with assms(1) 1 2 3 4 5 6 7 8 show ?thesis by (rule crit_connD)
  next
    assume "c2 ps bs p q"
    with assms(2) 1 2 3 4 5 6 7 8 show ?thesis by (rule crit_connD)
  qed
qed

definition pc_crit :: "('a, 'b::zero) critT"
  where "pc_crit = comb_crit product_crit chain_crit"

corollary crit_conn_pc_crit: "crit_conn pc_crit"
  by (simp only: pc_crit_def, rule crit_conn_comb_crit, fact crit_conn_product_crit, fact crit_conn_chain_crit)

subsection \<open>Function @{term gb}\<close>

definition trdsp::"('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)"
  where "trdsp bs p q \<equiv> trd bs (spoly p q)"

lemma trdsp_in_pideal:
  assumes "p \<in> set bs" and "q \<in> set bs"
  shows "trdsp bs p q \<in> pideal (set bs)"
  unfolding trdsp_def spoly_def
  apply (rule pideal_closed_trd)
    subgoal apply (rule pideal_closed_minus)
      subgoal by (rule monom_mult_in_pideal, fact)
      subgoal by (rule monom_mult_in_pideal, fact)
      done
    subgoal by (fact generator_subset_pideal)
  done

lemma trdsp_eq_zero_imp_cbelow_on:
  assumes "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m" and "p \<noteq> 0" and "q \<noteq> 0" and "trdsp bs p q = 0" and "set bs \<subseteq> F"
  shows "crit_pair_cbelow_on d m F p q"
proof -
  from assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) have "crit_pair_cbelow_on d m (set bs) p q"
  proof (rule spoly_red_zero_imp_crit_pair_cbelow_on)
    from assms(7) trd_red_rtrancl[of bs "spoly p q"] show "(red (set bs))\<^sup>*\<^sup>* (spoly p q) 0"
      by (simp add: trdsp_def)
  qed
  from this assms(8) show ?thesis by (rule crit_pair_cbelow_mono)
qed

lemma dgrad_p_set_le_trdsp:
  assumes "dickson_grading (+) d"
  shows "dgrad_p_set_le d {trdsp bs p q} (insert p (insert q (set bs)))"
proof -
  let ?h = "trdsp bs p q"
  have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) ?h" unfolding trdsp_def by (rule trd_red_rtrancl)
  with assms have "dgrad_p_set_le d {?h} (insert (spoly p q) (set bs))"
    by (rule dgrad_p_set_le_red_rtrancl)
  also have "dgrad_p_set_le d ... ({p, q} \<union> set bs)"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d (set bs) ({p, q} \<union> set bs)" by (rule dgrad_p_set_le_subset, blast)
  next
    from assms have "dgrad_p_set_le d {spoly p q} {p, q}" by (rule dgrad_p_set_le_spoly)
    also have "dgrad_p_set_le d ... ({p, q} \<union> set bs)"
      by (rule dgrad_p_set_le_subset, blast)
    finally show "dgrad_p_set_le d {spoly p q} ({p, q} \<union> set bs)" .
  qed
  finally show ?thesis by simp
qed

corollary dgrad_p_set_closed_trdsp:
  assumes "dickson_grading (+) d" and "set bs \<subseteq> dgrad_p_set d m" and "p \<in> dgrad_p_set d m"
    and "q \<in> dgrad_p_set d m"
  shows "trdsp bs p q \<in> dgrad_p_set d m"
proof -
  have "{trdsp bs p q} \<subseteq> dgrad_p_set d m"
  proof (rule dgrad_p_set_le_dgrad_p_set)
    from assms(1) show "dgrad_p_set_le d {trdsp bs p q} (insert p (insert q (set bs)))"
      by (rule dgrad_p_set_le_trdsp)
  next
    show "(insert p (insert q (set bs))) \<subseteq> dgrad_p_set d m" by (intro insert_subsetI, fact+)
  qed
  thus ?thesis by simp
qed

text \<open>Proving termination of Buchberger's algorithm is a bit involved; we need a couple more
  definitions and lemmas. Actually, the fact that we want to prove termination in context
  @{locale gd_powerprod} rather than @{locale od_powerprod} complicates matters even more
  (in particular the definition of the well-founded termination relation).\<close>

definition pair_to_set :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) set"
  where "pair_to_set x = set (fst x) \<union> fst ` set (snd x) \<union> snd ` set (snd x)"

definition gbaux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)) set"
  where "gbaux_term1 d = {(a, b::('a \<Rightarrow>\<^sub>0 'b) list). (set a) \<sqsupset>p (set b)} <*lex*> (measure length)"

definition gbaux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('a \<Rightarrow>\<^sub>0 'b::field) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list) \<times>
                                                (('a \<Rightarrow>\<^sub>0 'b) list \<times> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)) set"
  where "gbaux_term2 d = {(a, b). dgrad_p_set_le d (pair_to_set a) (pair_to_set b)}"

definition gbaux_term where "gbaux_term d = gbaux_term1 d \<inter> gbaux_term2 d"

text \<open>@{const gbaux_term} is need for proving termination of function @{term gbaux}.\<close>

lemma gbaux_term1_wf_on:
  assumes "dickson_grading (+) d"
  shows "wfP_on {x. pair_to_set x \<subseteq> dgrad_p_set d m} (\<lambda>x y. (x, y) \<in> gbaux_term1 d)"
proof (rule wfP_onI_min)
  let ?B = "dgrad_p_set d m"
  let ?A = "{x::(('a \<Rightarrow>\<^sub>0 'b) list) \<times> ((('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list). pair_to_set x \<subseteq> ?B}"
  have A_sub_Pow: "set ` fst ` ?A \<subseteq> Pow ?B" by (auto simp add: pair_to_set_def)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  have Q_sub_A: "set ` fst ` Q \<subseteq> set ` fst ` ?A" by (rule image_mono, rule image_mono, fact)
  from assms have "wfP_on (Pow ?B) (\<sqsupset>p)" by (rule red_supset_wf_on)
  moreover have "set (fst x) \<in> set ` fst ` Q" by (rule, rule refl, rule, rule refl, fact)
  moreover from Q_sub_A A_sub_Pow have "set ` fst ` Q \<subseteq> Pow ?B" by (rule subset_trans)
  ultimately obtain z0 where "z0 \<in> set ` fst ` Q"
    and *: "\<And>y. y \<sqsupset>p z0 \<Longrightarrow> y \<notin> set ` fst ` Q" by (rule wfP_onE_min, blast)
  from this(1) obtain z1 where "z1 \<in> Q" and z0: "z0 = set (fst z1)" by auto

  let ?Q = "{q \<in> Q. set (fst q) = z0}"
  have "snd z1 \<in> snd ` ?Q" by (rule, rule refl, simp add: \<open>z1 \<in> Q\<close> z0)
  with wf_measure obtain z2 where "z2 \<in> snd ` ?Q" and **: "\<And>y. (y, z2) \<in> measure length \<Longrightarrow> y \<notin> snd ` ?Q"
    by (rule wfE_min, blast)
  from this(1) obtain z where "z \<in> ?Q" and z2: "z2 = snd z" ..
  from this(1) have "z \<in> Q" and eq: "set (fst z) = z0" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y\<in>?A. (y, z) \<in> gbaux_term1 d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y\<in>?A. (y, z) \<in> gbaux_term1 d \<longrightarrow> y \<notin> Q"
    proof (intro ballI impI)
      fix y
      assume "y \<in> ?A"
      assume "(y, z) \<in> gbaux_term1 d"
      hence "set (fst y) \<sqsupset>p z0 \<or> (fst y = fst z \<and> (snd y, z2) \<in> measure length)"
        by (simp add: gbaux_term1_def eq[symmetric] z2 in_lex_prod_alt)
      thus "y \<notin> Q"
      proof
        assume "set (fst y) \<sqsupset>p z0"
        hence "set (fst y) \<notin> set ` fst ` Q" by (rule *)
        thus ?thesis by auto
      next
        assume "fst y = fst z \<and> (snd y, z2) \<in> measure length"
        hence "fst y = fst z" and "(snd y, z2) \<in> measure length" by simp_all
        from this(2) have "snd y \<notin> snd ` ?Q" by (rule **)
        hence "y \<notin> ?Q" by auto
        thus ?thesis by (simp add: \<open>fst y = fst z\<close> eq)
      qed
    qed
  qed
qed

lemma gbaux_term_wf:
  assumes "dickson_grading (+) d"
  shows "wf (gbaux_term d)"
proof (rule wfI_min)
  fix x::"(('a \<Rightarrow>\<^sub>0 'b) list) \<times> ((('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list)" and Q
  assume "x \<in> Q"
  let ?A = "pair_to_set x"
  have "finite ?A" by (simp add: pair_to_set_def)
  then obtain m where A: "?A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  let ?B = "dgrad_p_set d m"
  let ?Q = "{q \<in> Q. pair_to_set q \<subseteq> ?B}"
  from assms have "wfP_on {x. pair_to_set x \<subseteq> ?B} (\<lambda>x y. (x, y) \<in> gbaux_term1 d)"
    by (rule gbaux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. pair_to_set x \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> gbaux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfP_onE_min, blast)
  from this(1) have "z \<in> Q" and a: "pair_to_set z \<subseteq> ?B" by simp_all
  from this(1) show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> gbaux_term d \<longrightarrow> y \<notin> Q"
  proof
    show "\<forall>y. (y, z) \<in> gbaux_term d \<longrightarrow> y \<notin> Q"
    proof (intro allI impI)
      fix y
      assume "(y, z) \<in> gbaux_term d"
      hence "(y, z) \<in> gbaux_term1 d" and "(y, z) \<in> gbaux_term2 d" by (simp_all add: gbaux_term_def)
      from this(2) have "dgrad_p_set_le d (pair_to_set y) (pair_to_set z)" by (simp add: gbaux_term2_def)
      from this \<open>pair_to_set z \<subseteq> ?B\<close> have "pair_to_set y \<subseteq> ?B" by (rule dgrad_p_set_le_dgrad_p_set)
      moreover from \<open>(y, z) \<in> gbaux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
      ultimately show "y \<notin> Q" by simp
    qed
  qed
qed

lemma dgrad_p_set_le_pair_to_set_trdsp:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (pair_to_set ((trdsp bs p q) # bs, apf rs bs (trdsp bs p q))) (pair_to_set (bs, (p, q) # rs))"
proof -
  let ?h = "trdsp bs p q"
  from fst_add_pairs_subset[OF assms(2), of rs bs "trdsp bs p q"] snd_add_pairs_subset[OF assms(2), of rs bs]
  have "pair_to_set (?h # bs, apf rs bs ?h) \<subseteq> insert ?h (pair_to_set (bs, rs))"
    by (simp only: pair_to_set_def, auto)
  hence "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (insert ?h (pair_to_set (bs, rs)))"
    by (rule dgrad_p_set_le_subset)
  also have "dgrad_p_set_le d ... (insert p (insert q (pair_to_set (bs, rs))))"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d (pair_to_set (bs, rs)) (insert p (insert q (pair_to_set (bs, rs))))"
      by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
  next
    from assms(1) have "dgrad_p_set_le d {trdsp bs p q} (insert p (insert q (set bs)))"
      by (rule dgrad_p_set_le_trdsp)
    also have "dgrad_p_set_le d ... (insert p (insert q (pair_to_set (bs, rs))))"
      by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
    finally show "dgrad_p_set_le d {?h} (insert p (insert q (pair_to_set (bs, rs))))" .
  qed
  also have "... = pair_to_set (bs, (p, q) # rs)"
    by (auto simp add: pair_to_set_def)
  finally show ?thesis .
qed

text \<open>Functions @{term gb} and @{term gbaux} implement Buchberger's algorithm for computing
  Gr\"obner bases, incorporating Buchberger's two criteria for avoiding useless S-polynomials.\<close>

function (domintros) gbaux::"('a, 'b) apT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow>
    (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list" where
  gbaux_base: "gbaux _ _ bs [] = bs"|
  gbaux_rec: "gbaux apf cf bs ((p, q) # rs) =
    (if cf rs bs p q then
      gbaux apf cf bs rs
    else
      (let h = trdsp bs p q in
        (if h = 0 then
          gbaux apf cf bs rs
        else
          gbaux apf cf (h # bs) (apf rs bs h)
        )
      )
    )"
  by pat_completeness auto

text \<open>Note that we could parameterize @{const gbaux} over a binary (order) relation @{term R} instead
  of the ``add-pairs function'' @{term apf}. Then, @{term R} could be used to determine the order of
  the pairs in @{term rs}, and @{const gbaux} would terminate unconditionally. However, @{term apf} is
  more powerful, since it has a ``global'' view of the list of pairs and therefore has the potential
  of arranging the elements in a more clever way than by just comparing pairs of elements to each
  other, as @{term R} would do.\<close>

lemma gbaux_domI:
  assumes "add_pairs_set apf"
  shows "gbaux_dom (apf, cf, args)"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gbaux_term d"
  from dg have "wf ?R" by (rule gbaux_term_wf)
  thus ?thesis
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> gbaux_term d \<Longrightarrow> gbaux_dom (apf, cf, y)"
    obtain bs rs0 where x: "x = (bs, rs0)" by force
    show "gbaux_dom (apf, cf, x)" unfolding x
    proof (cases rs0)
      case Nil
      show "gbaux_dom (apf, cf, bs, rs0)" unfolding Nil by (rule gbaux.domintros)
    next
      case (Cons pq rs)
      obtain p q where "pq = (p, q)" by force
      from IH' have IH: "\<And>bs' rs'. ((bs', rs'), (bs, (p, q) # rs)) \<in> gbaux_term d \<Longrightarrow> gbaux_dom (apf, cf, bs', rs')"
        unfolding Cons x \<open>pq = (p, q)\<close> by blast
      have *: "gbaux_dom (apf, cf, bs, rs)"
      proof (rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
        show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
          by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
      qed
      show "gbaux_dom (apf, cf, bs, rs0)" unfolding Cons \<open>pq = (p, q)\<close>
      proof (rule gbaux.domintros)
        assume "trdsp bs p q \<noteq> 0"
        let ?h = "trdsp bs p q"
        show "gbaux_dom (apf, cf, ?h # bs, apf rs bs ?h)"
        proof (rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def, rule)
          show "insert ?h (set bs) \<sqsupset>p set bs"
          proof (rule red_supset_insertI[OF \<open>?h \<noteq> 0\<close>, of "set bs"])
            from trd_irred[of bs "(spoly p q)"] show "\<not> is_red (set bs) ?h" by (simp add: trdsp_def)
          qed
        next
          from dg assms show "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (pair_to_set (bs, (p, q) # rs))"
            by (rule dgrad_p_set_le_pair_to_set_trdsp)
        qed
      qed (rule *, rule*)
    qed
  qed
qed

lemma gbaux_simp_1 [simp]: "gbaux apf cf bs [] = bs"
  by (rule gbaux.psimps(1), rule gbaux.domintros)

lemma gbaux_simp_2:
  assumes "add_pairs_set apf"
  shows "gbaux apf cf bs ((p, q) # rs) =
      (if cf rs bs p q then
        gbaux apf cf bs rs
      else
        (let h = trdsp bs p q in if h = 0 then gbaux apf cf bs rs else gbaux apf cf (h # bs) (apf rs bs h))
      )"
  by (rule gbaux.psimps(2), rule gbaux_domI, fact)

lemma gbaux_simp_2_1:
  assumes "add_pairs_set apf" and "cf rs bs p q"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf bs rs"
  using assms(2) by (simp add: gbaux_simp_2[OF assms(1)])

lemma gbaux_simp_2_2:
  assumes "add_pairs_set apf" and "trdsp bs p q = 0"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf bs rs"
  using assms(2) by (simp add: gbaux_simp_2[OF assms(1)])

lemma gbaux_simp_2_3:
  assumes "add_pairs_set apf" and "\<not> cf rs bs p q" and "trdsp bs p q \<noteq> 0"
  shows "gbaux apf cf bs ((p, q) # rs) = gbaux apf cf ((trdsp bs p q) # bs) (apf rs bs (trdsp bs p q))"
  using assms(2) assms(3) by (simp add: gbaux_simp_2[OF assms(1)] Let_def)

text \<open>In order to prove the following lemma we again have to employ well-founded induction, since
  @{thm gbaux.pinduct} does not treat the first arguments of @{const gbaux} (i.\,e. @{term apf} and
  @{term cf}) in the proper way.\<close>
lemma gbaux_induct [consumes 1, case_names base ind1 ind2]:
  assumes "add_pairs_set apf"
  assumes base: "\<And>bs. P bs [] bs"
    and ind1: "\<And>bs ps p q. cf ps bs p q \<or> trdsp bs p q = 0 \<Longrightarrow> P bs ps (gbaux apf cf bs ps) \<Longrightarrow>
                P bs ((p, q) # ps) (gbaux apf cf bs ps)"
    and ind2: "\<And>bs ps p q h. \<not> cf ps bs p q \<Longrightarrow> h = trdsp bs p q \<Longrightarrow> h \<noteq> 0 \<Longrightarrow>
                P (h # bs) (apf ps bs h) (gbaux apf cf (h # bs) (apf ps bs h)) \<Longrightarrow>
                P bs ((p, q) # ps) (gbaux apf cf (h # bs) (apf ps bs h))"
  shows "P bs ps (gbaux apf cf bs ps)"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  let ?R = "gbaux_term d"
  from dg have "wf ?R" by (rule gbaux_term_wf)
  hence "P (fst (bs, ps)) (snd (bs, ps)) (gbaux apf cf (fst (bs, ps)) (snd (bs, ps)))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> gbaux_term d \<Longrightarrow> P (fst y) (snd y) (gbaux apf cf (fst y) (snd y))"
    obtain bs rs0 where x: "x = (bs, rs0)" by force
    show "P (fst x) (snd x) (gbaux apf cf (fst x) (snd x))"
    proof (simp add: x, cases rs0)
      case Nil
      from base show "P bs rs0 (gbaux apf cf bs rs0)" by (simp add: Nil)
    next
      case (Cons pq rs)
      obtain p q where "pq = (p, q)" by force
      from IH' have IH: "\<And>bs' rs'. ((bs', rs'), (bs, (p, q) # rs)) \<in> gbaux_term d \<Longrightarrow> P bs' rs' (gbaux apf cf bs' rs')"
        unfolding Cons x \<open>pq = (p, q)\<close> by auto
      show "P bs rs0 (gbaux apf cf bs rs0)" unfolding Cons \<open>pq = (p, q)\<close>
      proof (cases "cf rs bs p q")
        case True
        show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
          unfolding gbaux_simp_2_1[of _ cf, OF assms(1) True]
        proof (rule ind1, rule disjI1, fact, rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
          show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
            by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
        qed
      next
        case False
        show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
        proof (cases "trdsp bs p q = 0")
          case True
          show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))" unfolding gbaux_simp_2_2[OF assms(1) True]
          proof (rule ind1, rule disjI2, fact, rule IH, simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def)
            show "dgrad_p_set_le d (pair_to_set (bs, rs)) (pair_to_set (bs, (p, q) # rs))"
              by (rule dgrad_p_set_le_subset, auto simp add: pair_to_set_def)
          qed
        next
          case False
          let ?h = "trdsp bs p q"
          show "P bs ((p, q) # rs) (gbaux apf cf bs ((p, q) # rs))"
            unfolding gbaux_simp_2_3[of _ cf, OF assms(1) \<open>\<not> cf rs bs p q\<close> False]
          proof (rule ind2, fact, fact refl, fact, rule IH,
                  simp add: gbaux_term_def gbaux_term1_def gbaux_term2_def, rule)
          show "insert ?h (set bs) \<sqsupset>p set bs"
            proof (rule red_supset_insertI[OF \<open>?h \<noteq> 0\<close>, of "set bs"])
              from trd_irred[of bs "(spoly p q)"] show "\<not> is_red (set bs) ?h" by (simp add: trdsp_def)
            qed
          next
            from dg assms(1) show "dgrad_p_set_le d (pair_to_set (?h # bs, apf rs bs ?h)) (pair_to_set (bs, (p, q) # rs))"
              by (rule dgrad_p_set_le_pair_to_set_trdsp)
          qed
        qed
      qed
    qed
  qed
  thus ?thesis by simp
qed

lemma gbaux_sublist:
  assumes "add_pairs_set apf"
  obtains cs::"('a \<Rightarrow>\<^sub>0 'b::field) list" where "gbaux apf cf bs ps = cs @ bs"
  using assms
proof (induct rule: gbaux_induct)
  case (base bs)
  show ?case by (rule base[of "[]"], simp)
next
  case (ind1 bs ps p q)
  show ?case by (rule ind1(2), fact)
next
  case (ind2 bs ps p q h)
  show ?case
  proof (rule ind2(4), rule ind2(5))
    fix cs
    assume "gbaux apf cf (h # bs) (apf ps bs h) = cs @ h # bs"
    thus "gbaux apf cf (h # bs) (apf ps bs h) = (cs @ [h]) @ bs" by simp
  qed
qed

lemma gbaux_subset:
  assumes "add_pairs_set apf"
  shows "set bs \<subseteq> set (gbaux apf cf bs ps)"
proof -
  from assms obtain cs where "gbaux apf cf bs ps = cs @ bs" by (rule gbaux_sublist)
  thus ?thesis by simp
qed

lemma gbaux_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (set (gbaux apf cf bs ps)) (pair_to_set (bs, ps))"
  using assms(2)
proof (induct rule: gbaux_induct)
  case (base bs)
  thus ?case by (simp add: pair_to_set_def, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (ind1 bs ps p q)
  have "pair_to_set (bs, ps) \<subseteq> pair_to_set (bs, (p, q) # ps)" by (auto simp add: pair_to_set_def)
  hence "dgrad_p_set_le d (pair_to_set (bs, ps)) (pair_to_set (bs, (p, q) # ps))"
    by (rule dgrad_p_set_le_subset)
  with ind1(2) show ?case by (rule dgrad_p_set_le_trans)
next
  case (ind2 bs ps p q h)
  from assms have "dgrad_p_set_le d (pair_to_set (h # bs, apf ps bs h)) (pair_to_set (bs, (p, q) # ps))"
    unfolding ind2(2) by (rule dgrad_p_set_le_pair_to_set_trdsp)
  with ind2(4) show ?case by (rule dgrad_p_set_le_trans)
qed

corollary gbaux_dgrad_p_set:
  assumes "dickson_grading (+) d" and "add_pairs_set apf" and "set bs \<subseteq> dgrad_p_set d m"
    and "fst ` (set ps) \<subseteq> dgrad_p_set d m" and "snd ` (set ps) \<subseteq> dgrad_p_set d m"
  shows "set (gbaux apf cf bs ps) \<subseteq> dgrad_p_set d m"
proof (rule dgrad_p_set_le_dgrad_p_set)
  from assms(1, 2) show "dgrad_p_set_le d (set (gbaux apf cf bs ps)) (pair_to_set (bs, ps))"
    by (rule gbaux_dgrad_p_set_le)
next
  from assms(3, 4, 5) show "pair_to_set (bs, ps) \<subseteq> dgrad_p_set d m" by (simp add: pair_to_set_def)
qed

lemma gbaux_connectible:
  assumes "add_pairs_set apf" and "crit_conn cf" and "dickson_grading (+) d"
    and "set bs \<subseteq> dgrad_p_set d m"
    and "set ps \<subseteq> (set bs) \<times> (set bs)"
    and "\<And>p q. processed (p, q) bs ps \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p q"
  assumes "f \<in> set (gbaux apf cf bs ps)" and "g \<in> set (gbaux apf cf bs ps)"
    and "f \<noteq> 0" and "g \<noteq> 0"
  shows "crit_pair_cbelow_on d m (set (gbaux apf cf bs ps)) f g"
  using assms(1, 4, 5, 6, 7, 8)
proof (induct rule: gbaux_induct)
  case (base bs)
  from base(4, 5) have "processed (f, g) bs []" by (simp only: processed_Nil)
  from this \<open>f \<noteq> 0\<close> \<open>g \<noteq> 0\<close> show ?case by (rule base(3))
next
  case (ind1 bs ps p q)

  from ind1(4) have "(p, q) \<in> (set bs) \<times> (set bs)" by simp
  hence "p \<in> set bs" and "q \<in> set bs" by simp_all
  from \<open>p \<in> set bs\<close> ind1(3) have p_in: "p \<in> dgrad_p_set d m" ..
  from \<open>q \<in> set bs\<close> ind1(3) have q_in: "q \<in> dgrad_p_set d m" ..
  from ind1(4) have ps_sub: "set ps \<subseteq> (set bs) \<times> (set bs)" by simp

  have cpq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set bs) p q"
  proof -
    assume "p \<noteq> 0" and "q \<noteq> 0"
    from ind1(1) show "crit_pair_cbelow_on d m (set bs) p q"
    proof
      assume "cf ps bs p q"
      with assms(2, 3) ind1(3) ps_sub _ \<open>p \<in> set bs\<close> \<open>q \<in> set bs\<close> \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> show ?thesis
      proof (rule crit_connD)
        fix p' q'
        assume "processed (p', q') bs ps" and "p' \<noteq> 0" and "q' \<noteq> 0"
          and d1: "p' \<noteq> p \<or> q' \<noteq> q" and d2: "p' \<noteq> q \<or> q' \<noteq> p"
        from this(1) show "crit_pair_cbelow_on d m (set bs) p' q'"
        proof (rule processed_Cons)
          assume "p' = p" and "q' = q"
          with d1 show ?thesis by simp
        next
          assume "p' = q" and "q' = p"
          with d2 show ?thesis by simp
        next
          assume "processed (p', q') bs ((p, q) # ps)"
          from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis by (rule ind1(5))
        qed
      qed
    next
      assume "trdsp bs p q = 0"
      from assms(3) ind1(3) p_in q_in \<open>p \<noteq> 0\<close> \<open>q \<noteq> 0\<close> this subset_refl show ?thesis
        by (rule trdsp_eq_zero_imp_cbelow_on)
    qed
  qed

  note ind1(3) ps_sub
  moreover {
    fix p' q'
    assume "processed (p', q') bs ps" and "p' \<noteq> 0" and "q' \<noteq> 0"
    from this(1) have "crit_pair_cbelow_on d m (set bs) p' q'"
    proof (rule processed_Cons)
      assume "p' = p" and "q' = q"
      from \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis unfolding \<open>p' = p\<close> \<open>q' = q\<close> by (rule cpq)
    next
      assume "p' = q" and "q' = p"
      from \<open>q' \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set bs) q' p'"
        unfolding \<open>p' = q\<close> \<open>q' = p\<close> by (rule cpq)
      thus ?thesis by (rule crit_pair_cbelow_sym)
    next
      assume "processed (p', q') bs ((p, q) # ps)"
      from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis by (rule ind1(5))
    qed
  }
  ultimately show "crit_pair_cbelow_on d m (set (gbaux apf cf bs ps)) f g"
    using ind1(6, 7) by (rule ind1(2))
next
  case (ind2 bs ps p q h)

  from ind2(6) have "(p, q) \<in> (set bs) \<times> (set bs)" by simp
  hence "p \<in> set bs" and "q \<in> set bs" by simp_all
  from \<open>p \<in> set bs\<close> ind2(5) have p_in: "p \<in> dgrad_p_set d m" ..
  from \<open>q \<in> set bs\<close> ind2(5) have q_in: "q \<in> dgrad_p_set d m" ..
  from assms(3) ind2(5) p_in q_in have h_in: "h \<in> dgrad_p_set d m"
    unfolding ind2(2) by (rule dgrad_p_set_closed_trdsp)
  with ind2(5) have hbs_sub: "set (h # bs) \<subseteq> dgrad_p_set d m" by simp
  have "set bs \<subseteq> set (h # bs)" by auto

  from ind2(6) have ps_sub': "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
  with assms(1) have apf_sub: "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)" by (rule add_pairs_setD3)

  have cpq: "p \<noteq> 0 \<Longrightarrow> q \<noteq> 0 \<Longrightarrow> crit_pair_cbelow_on d m (set (h # bs)) p q"
  proof -
    assume "p \<noteq> 0" and "q \<noteq> 0"
    have "{h} \<subseteq> set (h # bs)" by simp
    have "(red (set bs))\<^sup>*\<^sup>* (spoly p q) h" unfolding ind2(2) trdsp_def by (rule trd_red_rtrancl)
    from this \<open>set bs \<subseteq> set (h # bs)\<close> have r1: "(red (set (h # bs)))\<^sup>*\<^sup>* (spoly p q) h"
      by (rule red_rtrancl_subset)
    from red_self[OF \<open>h \<noteq> 0\<close>] have "(red {h})\<^sup>*\<^sup>* h 0" ..
    from this \<open>{h} \<subseteq> set (h # bs)\<close> have "(red (set (h # bs)))\<^sup>*\<^sup>* h 0" by (rule red_rtrancl_subset)
    with r1 have "(red (set (h # bs)))\<^sup>*\<^sup>* (spoly p q) 0" by (rule rtranclp_trans)
    show "crit_pair_cbelow_on d m (set (h # bs)) p q"
      by (rule spoly_red_zero_imp_crit_pair_cbelow_on, fact+)
  qed

  from hbs_sub apf_sub _ ind2(8, 9) show ?case
  proof (rule ind2(4))
    fix p' q'
    assume "processed (p', q') (h # bs) (apf ps bs h)" and "p' \<noteq> 0" and "q' \<noteq> 0"
    from processed_add_pairs[OF assms(1) this(1)]
    show "crit_pair_cbelow_on d m (set (h # bs)) p' q'"
    proof
      assume "processed (p', q') bs ps"
      thus ?thesis
      proof (rule processed_Cons)
        assume "p' = p" and "q' = q"
        from \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> show ?thesis unfolding \<open>p' = p\<close> \<open>q' = q\<close> by (rule cpq)
      next
        assume "p' = q" and "q' = p"
        from \<open>q' \<noteq> 0\<close> \<open>p' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set (h # bs)) q' p'"
          unfolding \<open>p' = q\<close> \<open>q' = p\<close> by (rule cpq)
        thus ?thesis by (rule crit_pair_cbelow_sym)
      next
        assume "processed (p', q') bs ((p, q) # ps)"
        from this \<open>p' \<noteq> 0\<close> \<open>q' \<noteq> 0\<close> have "crit_pair_cbelow_on d m (set bs) p' q'" by (rule ind2(7))
        from this \<open>set bs \<subseteq> set (h # bs)\<close> show ?thesis by (rule crit_pair_cbelow_mono)
      qed
    next
      assume "p' = h \<and> q' = h"
      hence "p' = h" and "q' = h" by simp_all
      from assms(3) h_in show ?thesis unfolding \<open>p' = h\<close> \<open>q' = h\<close> by (rule crit_pair_cbelow_same)
    qed
  qed
qed

lemma gbaux_pideal:
  assumes "add_pairs_set apf" and "set ps \<subseteq> (set bs) \<times> (set bs)"
  shows "pideal (set (gbaux apf cf bs ps)) = pideal (set bs)"
  using assms
proof (induction rule: gbaux_induct)
  case (base bs)
  show ?case ..
next
  case (ind1 bs ps p q)
  from ind1(3) have "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
  thus ?case by (rule ind1(2))
next
  case (ind2 bs ps p q h)
  from ind2(5) have "p \<in> set bs" and "q \<in> set bs" by simp_all
  have "pideal (set (gbaux apf cf (h # bs) (apf ps bs h))) = pideal (set (h # bs))"
  proof (rule ind2(4))
    from assms(1) show "set (apf ps bs h) \<subseteq> set (h # bs) \<times> set (h # bs)"
    proof (rule add_pairs_setD3)
      from ind2(5) show "set ps \<subseteq> (set bs) \<times> (set bs)" by simp
    qed
  qed
  also have "... = pideal (set bs)"
    by (simp add: ind2(2), rule pideal_insert, rule trdsp_in_pideal, fact+)
  finally show "pideal (set (gbaux apf cf (h # bs) (apf ps bs h))) = pideal (set bs)" .
qed

definition gb_param :: "('a, 'b) apT \<Rightarrow> ('a, 'b) critT \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "gb_param apf cf bs = gbaux apf cf bs (pairs apf bs)"

theorem gb_param_dgrad_p_set_le:
  assumes "dickson_grading (+) d" and "add_pairs_set apf"
  shows "dgrad_p_set_le d (set (gb_param apf cf bs)) (set bs)"
proof -
  from assms have "dgrad_p_set_le d (set (gbaux apf cf bs (pairs apf bs))) (pair_to_set (bs, pairs apf bs))"
    by (rule gbaux_dgrad_p_set_le)
  also from assms(2) have "... = set bs" by (auto simp add: pair_to_set_def dest: pairsD1 pairsD2)
  finally show ?thesis unfolding gb_param_def .
qed

corollary gb_param_dgrad_p_set:
  assumes "dickson_grading (+) d" and "add_pairs_set apf" and "set bs \<subseteq> dgrad_p_set d m"
  shows "set (gb_param apf cf bs) \<subseteq> dgrad_p_set d m"
  by (rule dgrad_p_set_le_dgrad_p_set, rule gb_param_dgrad_p_set_le, fact+)

theorem gb_param_isGB:
  assumes "add_pairs_set apf" and "crit_conn cf"
  shows "is_Groebner_basis (set (gb_param apf cf bs))"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading (+) d" ..
  obtain m where "set bs \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust, rule finite_set)
  with dg assms(1) have "set (gb_param apf cf bs) \<subseteq> dgrad_p_set d m" by (rule gb_param_dgrad_p_set)
  with dg show ?thesis
  proof (rule crit_pair_cbelow_imp_GB_dgrad_p_set)
    fix p q
    assume p_in: "p \<in> set (gb_param apf cf bs)" and q_in: "q \<in> set (gb_param apf cf bs)"
    assume "p \<noteq> 0" and "q \<noteq> 0"
    with assms dg \<open>set bs \<subseteq> dgrad_p_set d m\<close> _ _ _ _
    show "crit_pair_cbelow_on d m (set (gb_param apf cf bs)) p q" unfolding gb_param_def
    proof (rule gbaux_connectible)
      from assms(1) show "set (pairs apf bs) \<subseteq> set bs \<times> set bs" by (rule pairs_subset)
    next
      fix p' q'
      assume proc: "processed (p', q') bs (pairs apf bs)"
      hence "p' \<in> set bs" and "q' \<in> set bs" by (rule processedD1, rule processedD2)
      show "crit_pair_cbelow_on d m (set bs) p' q'"
      proof (cases "p' = q'")
        case True
        from dg show ?thesis unfolding True
        proof (rule crit_pair_cbelow_same)
          from \<open>q' \<in> set bs\<close> \<open>set bs \<subseteq> dgrad_p_set d m\<close> show "q' \<in> dgrad_p_set d m" ..
        qed
      next
        case False
        from assms(1) this \<open>p' \<in> set bs\<close> \<open>q' \<in> set bs\<close> have "\<not> processed (p', q') bs (pairs apf bs)"
          by (rule processed_pairs)
        from this proc show ?thesis ..
      qed
    next
      from p_in show "p \<in> set (gbaux apf cf bs (pairs apf bs))" by (simp only: gb_param_def)
    next
      from q_in show "q \<in> set (gbaux apf cf bs (pairs apf bs))" by (simp only: gb_param_def)
    qed
  qed
qed

theorem gb_param_pideal:
  assumes "add_pairs_set apf"
  shows "pideal (set (gb_param apf cf bs)) = pideal (set bs)"
  unfolding gb_param_def using assms
proof (rule gbaux_pideal)
  from assms show "set (pairs apf bs) \<subseteq> set bs \<times> set bs" by (auto dest: pairsD1 pairsD2)
qed

definition gb_aux :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> (('a \<Rightarrow>\<^sub>0 'b) \<times> ('a \<Rightarrow>\<^sub>0 'b)) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "gb_aux = gbaux add_pairs_sorted pc_crit"

lemmas gb_aux_simps [code] =
  gbaux_simp_1[of add_pairs_sorted pc_crit, folded gb_aux_def]
  gbaux_simp_2[OF add_pairs_set_add_pairs_sorted, of pc_crit, folded gb_aux_def]

definition gb :: "('a \<Rightarrow>\<^sub>0 'b::field) list \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b) list"
  where "gb = gb_param add_pairs_sorted pc_crit"

lemmas gb_simps [code] = gb_param_def[of add_pairs_sorted pc_crit, folded gb_def gb_aux_def]
lemmas gb_isGB = gb_param_isGB[OF add_pairs_set_add_pairs_sorted crit_conn_pc_crit, folded gb_def]
lemmas gb_pideal = gb_param_pideal[OF add_pairs_set_add_pairs_sorted, of pc_crit, folded gb_def]

text \<open>The following theorem yields a criterion for deciding whether a given polynomial belongs to
  the ideal generated by a given list of polynomials. Note again that @{term "pideal (set bs)"}
  coincides with the ideal (in @{typ "('a, 'b) poly_mapping"}) generated by @{term "set bs"}!\<close>

theorem in_pideal_gb: "p \<in> pideal (set bs) \<longleftrightarrow> (trd (gb bs) p) = 0"
proof
  assume "p \<in> pideal (set bs)"
  hence p_in: "p \<in> pideal (set (gb bs))" using gb_pideal[of bs] by simp
  from gb_isGB[of bs] have cr: "relation.is_ChurchRosser (red (set (gb bs)))"
    unfolding is_Groebner_basis_def .
  hence a: "\<forall>a b. relation.srtc (red (set (gb bs))) a b \<longrightarrow> relation.cs (red (set (gb bs))) a b"
    unfolding relation.is_ChurchRosser_def .
  from a[rule_format, OF in_pideal_srtc[OF p_in]] obtain s
    where r1: "(red (set (gb bs)))\<^sup>*\<^sup>* p s" and r2: "(red (set (gb bs)))\<^sup>*\<^sup>* 0 s"
      unfolding relation.cs_def by auto
  from r1 rtrancl_0[OF r2] have r0: "(red (set (gb bs)))\<^sup>*\<^sup>* p 0" by simp
  from irred_0[of "set (gb bs)"] have fin_0: "relation.is_final (red (set (gb bs))) 0"
    unfolding is_red_def by simp
  from trd_irred[of "gb bs" p] have fin_trd: "relation.is_final (red (set (gb bs))) (trd (gb bs) p)"
    unfolding is_red_def by simp
  from relation.ChurchRosser_unique_final[OF cr trd_red_rtrancl[of "gb bs" p] r0 fin_trd fin_0]
    show "trd (gb bs) p = 0" .
next
  assume "trd (gb bs) p = 0"
  from this trd_in_pideal[of p "gb bs"] have "p \<in> pideal (set (gb bs))" by simp
  thus "p \<in> pideal (set bs)" using gb_pideal[of bs] by simp
qed

end (* gd_powerprod *)

end (* theory *)
