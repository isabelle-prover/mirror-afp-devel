section\<open>The Axiom of Replacement in $M[G]$\<close>
theory Replacement_Axiom
  imports
    Separation_Axiom
begin

context forcing_data1
begin

bundle sharp_simps1 = snd_abs[simp] fst_abs[simp] fst_closed[simp del, simplified, simp]
  snd_closed[simp del, simplified, simp] M_inhabited[simplified, simp]
  pair_in_M_iff[simp del, simplified, simp]

lemma sats_body_ground_repl_fm:
  includes sharp_simps1
  assumes
    "\<exists>t p. x=\<langle>t,p\<rangle>" "[x,\<alpha>,m,P,leq,\<one>] @ nenv \<in>list(M)"
    "\<phi>\<in>formula"
  shows
    "(\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. (##M)(a),\<alpha>,V) \<and> \<tau> \<in> V \<and> (snd(x) \<tturnstile> \<phi> ([fst(x),\<tau>]@nenv)))
    \<longleftrightarrow> M, [\<alpha>, x, m, P, leq, \<one>] @ nenv \<Turnstile> body_ground_repl_fm(\<phi>)"
  unfolding body_ground_repl_fm_def rename_split_fm_def
  by ((insert assms,rule iff_sats | simp add:nonempty[simplified])+,
      insert sats_incr_bv_iff[where bvs="[_,_,_,_,_,_]", simplified],auto del: iffI)

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

context G_generic1
begin

lemma Replace_sats_in_MG:
  assumes
    "c\<in>M[G]" "env \<in> list(M[G])"
    "\<phi> \<in> formula" "arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(env)"
    "univalent(##M[G], c, \<lambda>x v. (M[G] , [x,v]@env \<Turnstile> \<phi>) )"
    and
    ground_replacement:
    "\<And>nenv. ground_replacement_assm(M,[P,leq,\<one>] @ nenv, \<phi>)"
  shows
    "{v. x\<in>c, v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)} \<in> M[G]"
proof -
  let ?R = "\<lambda> x v . v\<in>M[G] \<and> (M[G] , [x,v]@env \<Turnstile> \<phi>)"
  from \<open>c\<in>M[G]\<close>
  obtain \<pi>' where "val(G, \<pi>') = c" "\<pi>' \<in> M"
    using GenExt_def by auto
  then
  have "domain(\<pi>')\<times>P\<in>M" (is "?\<pi>\<in>M")
    using cartprod_closed domain_closed by simp
  from \<open>val(G, \<pi>') = c\<close>
  have "c \<subseteq> val(G,?\<pi>)"
    using def_val[of G ?\<pi>] elem_of_val[of _ G \<pi>'] one_in_G
       domain_of_prod[OF one_in_P, of "domain(\<pi>')"]
    by (force del:M_genericD)
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)"
    using map_val by auto
  then
  have "length(nenv) = length(env)" by simp
  with \<open>arity(\<phi>) \<le> _\<close>
  have "arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(nenv)" by simp
  define f where "f(\<rho>p) \<equiv> \<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<tau> \<in> Vset(\<alpha>) \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv)))" (is "_ \<equiv> \<mu> \<alpha>. ?P(\<rho>p,\<alpha>)") for \<rho>p
  have "f(\<rho>p) = (\<mu> \<alpha>. \<alpha>\<in>M \<and> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(##M,\<alpha>,V) \<and> \<tau>\<in>V \<and>
        (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))))" (is "_ = (\<mu> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>))") for \<rho>p
    unfolding f_def using Vset_abs Vset_closed Ord_Least_cong[of "?P(\<rho>p)" "\<lambda> \<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)"]
    by (simp, simp del:setclass_iff)
  moreover
  note inM = \<open>nenv\<in>list(M)\<close> \<open>?\<pi>\<in>M\<close>
  moreover
  have "f(\<rho>p) \<in> M" "Ord(f(\<rho>p))" for \<rho>p
    unfolding f_def using Least_closed'[of "?P(\<rho>p)"] by simp_all
  ultimately
  have 1:"least(##M,\<lambda>\<alpha>. ?Q(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    using least_abs'[of "\<lambda>\<alpha>. \<alpha>\<in>M \<and> ?Q(\<rho>p,\<alpha>)" "f(\<rho>p)"] least_conj
    by (simp flip: setclass_iff)
  define QQ where "QQ\<equiv>?Q"
  from 1
  have "least(##M,\<lambda>\<alpha>. QQ(\<rho>p,\<alpha>),f(\<rho>p))" for \<rho>p
    unfolding QQ_def .
  have body:"(M, [\<rho>p,m,P,leq,\<one>] @ nenv \<Turnstile> ground_repl_fm(\<phi>)) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
    if "\<rho>p\<in>M" "\<rho>p\<in>?\<pi>" "m\<in>M" for \<rho>p m
  proof -
    note inM that
    moreover from this assms 1
    have "(M , [\<alpha>,\<rho>p,m,P,leq,\<one>] @ nenv \<Turnstile> body_ground_repl_fm(\<phi>)) \<longleftrightarrow> ?Q(\<rho>p,\<alpha>)" if "\<alpha>\<in>M" for \<alpha>
      using that sats_body_ground_repl_fm[of \<rho>p \<alpha> m nenv \<phi>]
      by auto
    moreover from calculation
    have body:"\<And>\<alpha>. \<alpha> \<in> M \<Longrightarrow> (\<exists>\<tau>\<in>M. \<exists>V\<in>M. is_Vset(\<lambda>a. a\<in>M, \<alpha>, V) \<and> \<tau> \<in> V \<and>
          (snd(\<rho>p) \<tturnstile> \<phi> ([fst(\<rho>p),\<tau>] @ nenv))) \<longleftrightarrow>
          M, Cons(\<alpha>, [\<rho>p, m, P, leq, \<one>] @ nenv) \<Turnstile> body_ground_repl_fm(\<phi>)"
      by simp
    ultimately
    show "(M , [\<rho>p,m,P,leq,\<one>] @ nenv \<Turnstile> ground_repl_fm(\<phi>)) \<longleftrightarrow> least(##M, QQ(\<rho>p), m)"
      using sats_least_fm[OF body,of 1] unfolding QQ_def ground_repl_fm_def
      by (simp, simp flip: setclass_iff)
  qed
  then
  have "univalent(##M, ?\<pi>, \<lambda>\<rho>p m. M , [\<rho>p,m] @ ([P,leq,\<one>] @ nenv) \<Turnstile> ground_repl_fm(\<phi>))"
    unfolding univalent_def by (auto intro:unique_least)
  moreover from \<open>length(_) = _\<close> \<open>env \<in> _\<close>
  have "length([P,leq,\<one>] @ nenv) = 3 +\<^sub>\<omega> length(env)" by simp
  moreover from \<open>arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(nenv)\<close>
    \<open>length(_) = length(_)\<close>[symmetric] \<open>nenv\<in>_\<close> \<open>\<phi>\<in>_\<close>
  have "arity(ground_repl_fm(\<phi>)) \<le> 5 +\<^sub>\<omega> length(env)"
    using arity_ground_repl_fm[of \<phi>] le_trans Un_le by auto
  moreover from \<open>\<phi>\<in>formula\<close>
  have "ground_repl_fm(\<phi>)\<in>formula" by simp
  moreover
  note \<open>length(nenv) = length(env)\<close> inM
  ultimately
  obtain Y where "Y\<in>M"
    "\<forall>m\<in>M. m \<in> Y \<longleftrightarrow> (\<exists>\<rho>p\<in>M. \<rho>p \<in> ?\<pi> \<and> (M, [\<rho>p,m] @ ([P,leq,\<one>] @ nenv) \<Turnstile> ground_repl_fm(\<phi>)))"
    using ground_replacement[of nenv]
    unfolding strong_replacement_def ground_replacement_assm_def replacement_assm_def by auto
  with \<open>least(_,QQ(_),f(_))\<close> \<open>f(_) \<in> M\<close> \<open>?\<pi>\<in>M\<close> body
  have "f(\<rho>p)\<in>Y" if "\<rho>p\<in>?\<pi>" for \<rho>p
    using that transitivity[OF _ \<open>?\<pi>\<in>M\<close>]
    by (clarsimp,rename_tac \<rho> p \<rho>p, rule_tac x="\<langle>\<rho>,p\<rangle>" in bexI, auto)
  from \<open>Y\<in>M\<close>
  have "\<Union> {y\<in>Y. Ord(y)} \<in> M" (is "?sup \<in> M")
    using separation_Ord separation_closed Union_closed by simp
  then
  have "{x\<in>Vset(?sup). x \<in> M} \<times> {\<one>} \<in> M" (is "?big_name \<in> M")
    using Vset_closed cartprod_closed singleton_closed by simp
  then
  have "val(G,?big_name) \<in> M[G]"
    by (blast intro:GenExtI)
  have "{v. x\<in>c, ?R(x,v)} \<subseteq> val(G,?big_name)" (is "?repl\<subseteq>?big")
  proof(intro subsetI)
    fix v
    assume "v\<in>?repl"
    moreover from this
    obtain x where "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "v\<in>M[G]"
      by auto
    moreover
    note \<open>val(G,\<pi>')=c\<close> \<open>\<pi>'\<in>M\<close>
    moreover
    from calculation
    obtain \<rho> p where "\<langle>\<rho>,p\<rangle>\<in>\<pi>'" "val(G,\<rho>) = x" "p\<in>G" "\<rho>\<in>M"
      using elem_of_val_pair' by blast
    moreover from this \<open>v\<in>M[G]\<close>
    obtain \<sigma> where "val(G,\<sigma>) = v" "\<sigma>\<in>M"
      using GenExtD by (force del:M_genericD)
    moreover
    note \<open>\<phi>\<in>_\<close> \<open>nenv\<in>_\<close> \<open>env = _\<close> \<open>arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(env)\<close>
    ultimately
    obtain q where "q\<in>G" "q \<tturnstile> \<phi> ([\<rho>,\<sigma>]@nenv)" "q\<in>P"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close>,of "[\<rho>,\<sigma>] @ nenv"]
      by auto
    with \<open>\<langle>\<rho>,p\<rangle>\<in>\<pi>'\<close> \<open>\<langle>\<rho>,q\<rangle>\<in>?\<pi> \<Longrightarrow> f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "f(\<langle>\<rho>,q\<rangle>)\<in>Y"
      using generic unfolding M_generic_def filter_def by blast
    let ?\<alpha>="succ(rank(\<sigma>))"
    note \<open>\<sigma>\<in>M\<close>
    moreover from this
    have "?\<alpha> \<in> M" "\<sigma> \<in> Vset(?\<alpha>)"
      using rank_closed cons_closed Vset_Ord_rank_iff
      by (simp_all flip: setclass_iff)
    moreover
    note \<open>q \<tturnstile> \<phi> ([\<rho>,\<sigma>] @ nenv)\<close>
    ultimately
    have "?P(\<langle>\<rho>,q\<rangle>,?\<alpha>)" by (auto simp del: Vset_rank_iff)
    moreover
    have "(\<mu> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)) = f(\<langle>\<rho>,q\<rangle>)"
      unfolding f_def by simp
    ultimately
    obtain \<tau> where "\<tau>\<in>M" "\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))" "q \<tturnstile> \<phi> ([\<rho>,\<tau>] @ nenv)"
      using LeastI[of "\<lambda> \<alpha>. ?P(\<langle>\<rho>,q\<rangle>,\<alpha>)" ?\<alpha>] by auto
    with \<open>q\<in>G\<close> \<open>\<rho>\<in>M\<close> \<open>nenv\<in>_\<close> \<open>arity(\<phi>)\<le> 2 +\<^sub>\<omega> length(nenv)\<close>
    have "M[G], map(val(G),[\<rho>,\<tau>] @ nenv) \<Turnstile> \<phi>"
      using truth_lemma[OF \<open>\<phi>\<in>_\<close>, of "[\<rho>,\<tau>] @ nenv"] by auto
    moreover from \<open>x\<in>c\<close> \<open>c\<in>M[G]\<close>
    have "x\<in>M[G]" using transitivity_MG by simp
    moreover
    note \<open>M[G],[x,v] @ env\<Turnstile> \<phi>\<close> \<open>env = map(val(G),nenv)\<close> \<open>\<tau>\<in>M\<close> \<open>val(G,\<rho>)=x\<close>
      \<open>univalent(##M[G],_,_)\<close> \<open>x\<in>c\<close> \<open>v\<in>M[G]\<close>
    ultimately
    have "v=val(G,\<tau>)"
      using GenExtI[of \<tau> G] unfolding univalent_def by (auto)
    from \<open>\<tau> \<in> Vset(f(\<langle>\<rho>,q\<rangle>))\<close> \<open>Ord(f(_))\<close>  \<open>f(\<langle>\<rho>,q\<rangle>)\<in>Y\<close>
    have "\<tau> \<in> Vset(?sup)"
      using Vset_Ord_rank_iff lt_Union_iff[of _ "rank(\<tau>)"] by auto
    with \<open>\<tau>\<in>M\<close>
    have "val(G,\<tau>) \<in> val(G,?big_name)"
      using domain_of_prod[of \<one> "{\<one>}" "{x\<in>Vset(?sup). x \<in> M}" ] def_val[of G ?big_name]
        one_in_G one_in_P  by (auto simp del: Vset_rank_iff)
    with \<open>v=val(G,\<tau>)\<close>
    show "v \<in> val(G,?big_name)"
      by simp
  qed
  from \<open>?big_name\<in>M\<close>
  have "?repl = {v\<in>?big. \<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile>  \<phi>}" (is "_ = ?rhs")
  proof(intro equalityI subsetI)
    fix v
    assume "v\<in>?repl"
    with \<open>?repl\<subseteq>?big\<close>
    obtain x where "x\<in>c" "M[G], [x, v] @ env \<Turnstile> \<phi>" "v\<in>?big"
      using subsetD by auto
    with \<open>univalent(##M[G],_,_)\<close> \<open>c\<in>M[G]\<close>
    show "v \<in> ?rhs"
      unfolding univalent_def
      using transitivity_MG ReplaceI[of "\<lambda> x v. \<exists>x\<in>c. M[G], [x, v] @ env \<Turnstile> \<phi>"] by blast
  next
    fix v
    assume "v\<in>?rhs"
    then
    obtain x where
      "v\<in>val(G, ?big_name)" "M[G], [x, v] @ env \<Turnstile> \<phi>" "x\<in>c"
      by blast
    moreover from this \<open>c\<in>M[G]\<close>
    have "v\<in>M[G]" "x\<in>M[G]"
      using transitivity_MG GenExtI[OF \<open>?big_name\<in>_\<close>,of G] by auto
    moreover from calculation \<open>univalent(##M[G],_,_)\<close>
    have "?R(x,y) \<Longrightarrow> y = v" for y
      unfolding univalent_def by auto
    ultimately
    show "v\<in>?repl"
      using ReplaceI[of ?R x v c]
      by blast
  qed
  moreover
  let ?\<psi> = "(\<cdot>\<exists>\<cdot>\<cdot>0 \<in> 2 +\<^sub>\<omega> length(env) \<cdot> \<and> \<phi>\<cdot>\<cdot>)"
  from \<open>\<phi>\<in>_\<close>
  have "?\<psi>\<in>formula" "arity(?\<psi>) \<le> 2 +\<^sub>\<omega> length(env)"
    using pred_mono[OF _ \<open>arity(\<phi>)\<le>2+\<^sub>\<omega>length(env)\<close>] lt_trans[OF _ le_refl]
    by (auto simp add:ord_simp_union arity)
  moreover
  from \<open>\<phi>\<in>_\<close> \<open>arity(\<phi>)\<le>2+\<^sub>\<omega>length(env)\<close> \<open>c\<in>M[G]\<close> \<open>env\<in>_\<close>
  have "(\<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>) \<longleftrightarrow> M[G], [v] @ env @ [c] \<Turnstile> ?\<psi>" if "v\<in>M[G]" for v
    using that nth_concat transitivity_MG[OF _ \<open>c\<in>M[G]\<close>] arity_sats_iff[of \<phi> "[c]" _ "[_,v]@env"]
    by auto
  moreover from this
  have "{v\<in>?big. \<exists>x\<in>c. M[G], [x,v] @ env \<Turnstile> \<phi>} = {v\<in>?big. M[G], [v] @ env @ [c] \<Turnstile>  ?\<psi>}"
    using transitivity_MG[OF _ GenExtI, OF _ \<open>?big_name\<in>M\<close>]
    by simp
  moreover from calculation and \<open>env\<in>_\<close> \<open>c\<in>_\<close> \<open>?big\<in>M[G]\<close>
  have "{v\<in>?big. M[G] , [v] @ env @ [c] \<Turnstile> ?\<psi>} \<in> M[G]"
    using Collect_sats_in_MG by auto
  ultimately
  show ?thesis by simp
qed

theorem strong_replacement_in_MG:
  assumes
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 2 +\<^sub>\<omega> length(env)" "env \<in> list(M[G])"
    and
    ground_replacement:
    "\<And>nenv. ground_replacement_assm(M,[P,leq,\<one>] @ nenv, \<phi>)"
  shows
    "strong_replacement(##M[G],\<lambda>x v. M[G],[x,v] @ env \<Turnstile> \<phi>)"
proof -
  let ?R="\<lambda>x y . M[G], [x, y] @ env \<Turnstile> \<phi>"
  {
    fix A
    let ?Y="{v . x \<in> A, v\<in>M[G] \<and> ?R(x,v)}"
    assume 1: "(##M[G])(A)" "univalent(##M[G], A, ?R)"
    with assms
    have "(##M[G])(?Y)"
      using Replace_sats_in_MG ground_replacement 1
      unfolding ground_replacement_assm_def by auto
    have "b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))" if "(##M[G])(b)" for b
    proof(rule)
      from \<open>(##M[G])(A)\<close>
      show "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)" if "b \<in> ?Y"
        using that transitivity_MG by auto
    next
      show "b \<in> ?Y" if "\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)"
      proof -
        from \<open>(##M[G])(b)\<close>
        have "b\<in>M[G]" by simp
        with that
        obtain x where "(##M[G])(x)" "x\<in>A" "b\<in>M[G] \<and> ?R(x,b)"
          by blast
        moreover from this 1 \<open>(##M[G])(b)\<close>
        have "x\<in>M[G]" "z\<in>M[G] \<and> ?R(x,z) \<Longrightarrow> b = z" for z
          unfolding univalent_def
          by auto
        ultimately
        show ?thesis
          using ReplaceI[of "\<lambda> x y. y\<in>M[G] \<and> ?R(x,y)"] by blast
      qed
    qed
    then
    have "\<forall>b[##M[G]]. b \<in> ?Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b))"
      by simp
    with \<open>(##M[G])(?Y)\<close>
    have " (\<exists>Y[##M[G]]. \<forall>b[##M[G]]. b \<in> Y \<longleftrightarrow> (\<exists>x[##M[G]]. x \<in> A \<and> ?R(x,b)))"
      by auto
  }
  then show ?thesis unfolding strong_replacement_def
    by simp
qed

lemma replacement_assm_MG:
  assumes
    ground_replacement:
    "\<And>nenv. ground_replacement_assm(M,[P,leq,\<one>] @ nenv, \<phi>)"
  shows
    "replacement_assm(M[G],env,\<phi>)"
  using assms strong_replacement_in_MG
  unfolding replacement_assm_def by simp

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end