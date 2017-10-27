section {* Relations on Büchi Automata *}

theory BA_Refine
imports
  "BA"
  "../Transition_Systems/Transition_System_Refine"
begin

  definition ba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow> ('more\<^sub>1 \<times> 'more\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1, 'more\<^sub>1) ba_scheme \<times> ('label\<^sub>2, 'state\<^sub>2, 'more\<^sub>2) ba_scheme) set" where
    [to_relAPP]: "ba_rel L S M \<equiv> {(A\<^sub>1, A\<^sub>2).
      (succ A\<^sub>1, succ A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel \<and>
      (initial A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (accepting A\<^sub>1, accepting A\<^sub>2) \<in> S \<rightarrow> bool_rel \<and>
      (ba.more A\<^sub>1, ba.more A\<^sub>2) \<in> M}"

  lemma ba_param[param]:
    "(ba_ext, ba_ext) \<in> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel) \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> (S \<rightarrow> bool_rel) \<rightarrow> M \<rightarrow> \<langle>L, S, M\<rangle> ba_rel"
    "(succ, succ) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
    "(initial, initial) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(accepting, accepting) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> S \<rightarrow> bool_rel"
    "(ba.more, ba.more) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> M"
    unfolding ba_rel_def fun_rel_def by auto

  lemma ba_rel_id[simp]: "\<langle>Id, Id, Id\<rangle> ba_rel = Id" unfolding ba_rel_def by auto
  lemma ba_rel_converse[simp]: "(\<langle>L, S, M\<rangle> ba_rel)\<inverse> = \<langle>L\<inverse>, S\<inverse>, M\<inverse>\<rangle> ba_rel"
  proof -
    have 1: "L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel = (L\<inverse> \<rightarrow> S\<inverse> \<rightarrow> \<langle>S\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 2: "\<langle>S\<rangle> set_rel = (\<langle>S\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 3: "S \<rightarrow> bool_rel = (S\<inverse> \<rightarrow> bool_rel)\<inverse>" by simp
    show ?thesis unfolding ba_rel_def unfolding 1 unfolding 2 unfolding 3 by fastforce
  qed

  lemma run_param_1:
    assumes "(A, B) \<in> \<langle>L, S, M\<rangle> ba_rel"
    assumes "(u, v) \<in> \<langle>L\<rangle> stream_rel"
    assumes "(p, q) \<in> S" "run A (u ||| r) p"
    obtains s
    where "(r, s) \<in> \<langle>S\<rangle> stream_rel" "run B (v ||| s) q"
  proof -
    define P :: "'a stream \<times> 'd stream \<times> 'b stream \<times> 'b \<times> 'e \<Rightarrow> bool" where
      "P \<equiv> \<lambda> (u, v, r, p, q). (u, v) \<in> \<langle>L\<rangle> stream_rel \<and> (p, q) \<in> S \<and> run A (u ||| r) p"
    define Q :: "'a stream \<times> 'd stream \<times> 'b stream \<times> 'b \<times> 'e \<Rightarrow> 'e \<Rightarrow> bool" where
      "Q \<equiv> \<lambda> (u, v, r, p, q) q'. q' \<in> succ B (shd v) q \<and> (shd r, q') \<in> S"
    have 1: "P (u, v, r, p, q)" using assms(2, 3, 4) unfolding P_def by auto
    have "\<exists> q'. Q x q'" if "P x" for x
    proof -
      obtain a u b v p' r p q where x: "x = (a ## u, b ## v, p' ## r, p, q)"
        using prod.exhaust stream.exhaust by metis
      note succE = ba_param(2)[param_fo, OF assms(1), THEN set_relE1]
      show ?thesis using succE that unfolding x P_def Q_def by force
    qed
    then obtain f where 2: "\<And> x. P x \<Longrightarrow> Q x (f x)" by metis
    define g where "g \<equiv> \<lambda> (u, v, r, p, q). (stl u, stl v, stl r, shd r, f (u, v, r, p, q))"
    have 3: "P (g x)" if "P x" for x
    proof -
      obtain a u b v p' r p q where x: "x = (a ## u, b ## v, p' ## r, p, q)"
        using prod.exhaust stream.exhaust by metis
      show ?thesis using 2[OF that] that unfolding x P_def Q_def g_def by auto
    qed
    show ?thesis
    proof
      show "run B (v ||| smap f (siterate g (u, v, r, p, q))) q"
        using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: u v r p q) (fastforce)
      show "(r, smap f (siterate g (u, v, r, p, q))) \<in> \<langle>S\<rangle> stream_rel"
        using 1 2 3 unfolding Q_def g_def by (coinduction arbitrary: u v r p q) (fastforce)
    qed
  qed
  lemma run_param_2:
    assumes "(A, B) \<in> \<langle>L, S, M\<rangle> ba_rel"
    assumes "(u, v) \<in> \<langle>L\<rangle> stream_rel"
    assumes "(p, q) \<in> S" "run B (v ||| s) q"
    obtains r
    where "(r, s) \<in> \<langle>S\<rangle> stream_rel" "run A (u ||| r) p"
  proof -
    have 1: "(B, A) \<in> \<langle>L\<inverse>, S\<inverse>, M\<inverse>\<rangle> ba_rel" using assms(1) ba_rel_converse by blast
    have 2: "(v, u) \<in> \<langle>L\<inverse>\<rangle> stream_rel" using assms(2) by simp
    have 3: "(q, p) \<in> S\<inverse>" using assms(3) by simp
    show ?thesis using run_param_1 1 2 3 assms(4) that by force
  qed

  lemma language_param[param]:
    assumes "Domain L = UNIV" "Range L = UNIV"
    shows "(language, language) \<in> \<langle>L, S, M\<rangle> ba_rel \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
  proof
    fix A B
    assume 1[param]: "(A, B) \<in> \<langle>L, S, M\<rangle> ba_rel"
    define runsa where "runsa w p \<equiv> {r. run A (w ||| r) p}" for w p
    define runsb where "runsb w p \<equiv> {r. run B (w ||| r) p}" for w p
    have 2[param]: "(runsa, runsb) \<in> \<langle>L\<rangle> stream_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>S\<rangle> stream_rel\<rangle> set_rel"
      unfolding runsa_def runsb_def using 1 by (fast intro: set_relI elim: run_param_1 run_param_2)
    have 3:
      "language A = {w. \<exists> p \<in> initial A. \<exists> r \<in> runsa w p. infs (accepting A) (trace (w ||| r) p)}"
      "language B = {w. \<exists> p \<in> initial B. \<exists> r \<in> runsb w p. infs (accepting B) (trace (w ||| r) p)}"
      unfolding language_def runsa_def runsb_def by (auto iff: split_szip_ex)
    show "(language A, language B) \<in> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
      unfolding 3 using assms by parametricity auto
  qed

end
