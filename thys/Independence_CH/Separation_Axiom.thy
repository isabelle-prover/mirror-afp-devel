section\<open>The Axiom of Separation in $M[G]$\<close>
theory Separation_Axiom
  imports Forcing_Theorems Separation_Rename
begin

context G_generic1
begin

lemma map_val :
  assumes "env\<in>list(M[G])"
  shows "\<exists>nenv\<in>list(M). env = map(val(G),nenv)"
  using assms
proof(induct env)
  case Nil
  have "map(val(G),Nil) = Nil" by simp
  then show ?case by force
next
  case (Cons a l)
  then obtain a' l' where
    "l' \<in> list(M)" "l=map(val(G),l')" "a = val(G,a')"
    "Cons(a,l) = map(val(G),Cons(a',l'))" "Cons(a',l') \<in> list(M)"
    using GenExtD
    by force
  then show ?case by force
qed

lemma Collect_sats_in_MG :
  assumes
    "A\<in>M[G]"
    "\<phi> \<in> formula" "env\<in>list(M[G])" "arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)"
  shows
    "{x \<in> A . (M[G], [x] @ env \<Turnstile> \<phi>)} \<in> M[G]"
proof -
  from \<open>A\<in>M[G]\<close>
  obtain \<pi> where "\<pi> \<in> M" "val(G, \<pi>) = A"
    using GenExt_def by auto
  then
  have "domain(\<pi>)\<in>M" "domain(\<pi>) \<times> P \<in> M"
    using cartprod_closed[of _ P,simplified]
    by (simp_all flip:setclass_iff)
  let ?\<chi>="\<cdot>\<cdot> 0 \<in> (1 +\<^sub>\<omega> length(env)) \<cdot> \<and> \<phi> \<cdot>"
  let ?new_form="sep_ren(length(env),forces(?\<chi>))"
  let ?\<psi>="(\<cdot>\<exists>(\<cdot>\<exists>\<cdot>\<cdot>\<langle>0,1\<rangle> is 2 \<cdot> \<and> ?new_form \<cdot> \<cdot>)\<cdot>)"
  note phi = \<open>\<phi>\<in>formula\<close> \<open>arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)\<close>
  then
  have "?\<chi>\<in>formula" "forces(?\<chi>) \<in> formula" "arity(\<phi>) \<le> 2+\<^sub>\<omega> length(env)"
    using definability le_trans[OF \<open>arity(\<phi>)\<le>_\<close>] add_le_mono[of 1 2,OF _ le_refl]
    by simp_all
  with \<open>env\<in>_\<close> phi
  have "arity(?\<chi>) \<le> 2+\<^sub>\<omega>length(env)"
    using ord_simp_union leI FOL_arities by simp
  with \<open>env\<in>list(_)\<close> phi
  have "arity(forces(?\<chi>)) \<le> 6 +\<^sub>\<omega> length(env)"
    using  arity_forces_le by simp
  then
  have "arity(forces(?\<chi>)) \<le> 7 +\<^sub>\<omega> length(env)"
    using ord_simp_union arity_forces leI by simp
  with \<open>arity(forces(?\<chi>)) \<le>7 +\<^sub>\<omega> _\<close> \<open>env \<in> _\<close> \<open>\<phi> \<in> formula\<close>
  have "arity(?new_form) \<le> 7 +\<^sub>\<omega> length(env)" "?new_form \<in> formula" "?\<psi>\<in>formula"
    using arity_rensep[OF definability[of "?\<chi>"]]
    by auto
  then
  have "arity(?\<psi>) \<le> 5 +\<^sub>\<omega> length(env)"
    using ord_simp_union arity_forces pred_mono[OF _ pred_mono[OF _ \<open>arity(?new_form) \<le> _\<close>]]
    by (auto simp:arity)
  from \<open>env \<in> _\<close>
  obtain nenv where "nenv\<in>list(M)" "env = map(val(G),nenv)" "length(nenv) = length(env)"
    using map_val by auto
  from phi \<open>nenv\<in>_\<close> \<open>env\<in>_\<close> \<open>\<pi>\<in>M\<close> \<open>\<phi>\<in>_\<close> \<open>length(nenv) = length(env)\<close>
  have "arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])" for \<theta>
    using union_abs2[OF \<open>arity(\<phi>) \<le> 2+\<^sub>\<omega> _\<close>] ord_simp_union FOL_arities
    by simp
  note in_M = \<open>\<pi>\<in>M\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>
  have Equivalence: "
       (M, [u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>) \<longleftrightarrow>
         (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and>
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> M[F],  map(val(F), [\<theta>] @ nenv @[\<pi>]) \<Turnstile>  ?\<chi>))"
    if "u \<in> domain(\<pi>) \<times> P"
    for u
  proof -
    from \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>domain(\<pi>) \<times> P \<in> M\<close>
    have "u\<in>M" by (simp add:transitivity)
    have "(M, [\<theta>,p,u,P,leq,\<one>,\<pi>]@nenv \<Turnstile> ?new_form) \<longleftrightarrow>
          (\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow> (M[F],  map(val(F), [\<theta>] @ nenv@[\<pi>]) \<Turnstile>  ?\<chi>))"
      if "\<theta>\<in>M" "p\<in>P"
      for \<theta> p
    proof -
      from \<open>p\<in>P\<close>
      have "p\<in>M" by (simp add: transitivity)
      let ?env="[p,P,leq,\<one>,\<theta>] @ nenv @ [\<pi>,u]"
      let ?new_env=" [\<theta>,p,u,P,leq,\<one>,\<pi>] @ nenv"
      note types = in_M \<open>\<theta> \<in> M\<close> \<open>p\<in>M\<close> \<open>u \<in> domain(\<pi>) \<times> P\<close> \<open>u \<in> M\<close> \<open>nenv\<in>_\<close>
      then
      have tyenv:"?env \<in> list(M)" "?new_env \<in> list(M)"
        by simp_all
      from types
      have eq_env:"[p, P, leq, \<one>] @ ([\<theta>] @ nenv @ [\<pi>,u]) = 
                  ([p, P, leq, \<one>] @ ([\<theta>] @ nenv @ [\<pi>])) @ [u]"
        using app_assoc by simp
      then
      have "(M, [\<theta>,p,u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?new_form) \<longleftrightarrow> (M, ?new_env \<Turnstile> ?new_form)"
        by simp
      from tyenv \<open>length(nenv) = length(env)\<close> \<open>arity(forces(?\<chi>)) \<le> 7 +\<^sub>\<omega> length(env)\<close> \<open>forces(?\<chi>) \<in> formula\<close>
      have "... \<longleftrightarrow> p \<tturnstile> ?\<chi> ([\<theta>] @ nenv @ [\<pi>,u])"
        using sepren_action[of "forces(?\<chi>)"  "nenv",OF _ _ \<open>nenv\<in>list(M)\<close>]
        by simp
      also from types phi \<open>env\<in>_\<close> \<open>length(nenv) = length(env)\<close> \<open>arity(forces(?\<chi>)) \<le> 6 +\<^sub>\<omega> length(env)\<close>
      have "... \<longleftrightarrow> p \<tturnstile> ?\<chi>  ([\<theta>] @ nenv @ [\<pi>])"
        by (subst eq_env,rule_tac arity_sats_iff,auto)
      also from types phi \<open>p\<in>P\<close> \<open>arity(forces(?\<chi>)) \<le> 6 +\<^sub>\<omega> length(env)\<close> \<open>arity(?\<chi>) \<le> length([\<theta>] @ nenv @ [\<pi>])\<close>
      have " ... \<longleftrightarrow> (\<forall>F . M_generic(F) \<and> p \<in> F \<longrightarrow>
                           M[F],  map(val(F), [\<theta>] @ nenv @ [\<pi>]) \<Turnstile>  ?\<chi>)"
        using definition_of_forcing[where \<phi>="\<cdot>\<cdot> 0 \<in> (1 +\<^sub>\<omega> length(env)) \<cdot> \<and> \<phi> \<cdot>"]
        by auto
      finally
      show ?thesis
        by simp
    qed
    with in_M \<open>?new_form \<in> formula\<close> \<open>?\<psi>\<in>formula\<close> \<open>nenv \<in> _\<close> \<open>u \<in> domain(\<pi>)\<times>P\<close>
    show ?thesis
      by (auto simp add: transitivity)
  qed
  moreover from \<open>env = _\<close> \<open>\<pi>\<in>M\<close> \<open>nenv\<in>list(M)\<close>
  have map_nenv:"map(val(G), nenv @ [\<pi>]) = env @ [val(G,\<pi>)]"
    using map_app_distrib append1_eq_iff by auto
  ultimately
  have aux:"(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> M[G], [val(G,\<theta>)] @ env @ [val(G,\<pi>)] \<Turnstile> ?\<chi>))"
    (is "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. _ ( _ \<longrightarrow> M[G] , ?vals(\<theta>) \<Turnstile> _))")
    if "u \<in> domain(\<pi>) \<times> P" "M, [u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>" for u
    using Equivalence[THEN iffD1, OF that] generic by force
  moreover
  have "[val(G, \<theta>)] @ env @ [val(G, \<pi>)] \<in> list(M[G])" if "\<theta>\<in>M" for \<theta>
    using \<open>\<pi>\<in>M\<close> \<open>env \<in> list(M[G])\<close> GenExtI that by force
  ultimately
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u=\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> val(G,\<theta>)\<in>nth(1 +\<^sub>\<omega> length(env),[val(G, \<theta>)] @ env @ [val(G, \<pi>)])
        \<and> (M[G], ?vals(\<theta>) \<Turnstile> \<phi>)))"
    if "u \<in> domain(\<pi>) \<times> P" "M, [u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>" for u
    using aux[OF that] by simp
  moreover from \<open>env \<in> _\<close> \<open>\<pi>\<in>M\<close>
  have nth:"nth(1 +\<^sub>\<omega> length(env),[val(G, \<theta>)] @ env @ [val(G, \<pi>)]) = val(G,\<pi>)"
    if "\<theta>\<in>M" for \<theta>
    using nth_concat[of "val(G,\<theta>)" "val(G,\<pi>)" "M[G]"] that GenExtI by simp
  ultimately
  have "(\<exists>\<theta>\<in>M. \<exists>p\<in>P. u=\<langle>\<theta>,p\<rangle> \<and> (p\<in>G \<longrightarrow> val(G,\<theta>)\<in>val(G,\<pi>) \<and> (M[G],?vals(\<theta>) \<Turnstile>  \<phi>)))"
    if "u \<in> domain(\<pi>) \<times> P" "M, [u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>" for u
    using that \<open>\<pi>\<in>M\<close> \<open>env \<in> _\<close> by simp
  with \<open>domain(\<pi>)\<times>P\<in>M\<close>
  have "\<forall>u\<in>domain(\<pi>)\<times>P . (M, [u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>) \<longrightarrow> (\<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and>
        (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> (M[G],?vals(\<theta>) \<Turnstile>  \<phi>)))"
    by (simp add:transitivity)
  then
  have "{u\<in>domain(\<pi>)\<times>P . (M,[u,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>) } \<subseteq>
     {u\<in>domain(\<pi>)\<times>P . \<exists>\<theta>\<in>M. \<exists>p\<in>P. u =\<langle>\<theta>,p\<rangle> \<and>
       (p \<in> G \<longrightarrow> val(G, \<theta>)\<in>val(G, \<pi>) \<and> (M[G], ?vals(\<theta>) \<Turnstile> \<phi>))}"
    (is "?n\<subseteq>?m")
    by auto
  then
  have first_incl: "val(G,?n) \<subseteq> val(G,?m)"
    using val_mono by simp
  note  \<open>val(G,\<pi>) = A\<close> (* from the assumptions *)
  with \<open>?\<psi>\<in>formula\<close>  \<open>arity(?\<psi>) \<le> _\<close> in_M \<open>nenv \<in> _\<close> \<open>env \<in> _\<close> \<open>length(nenv) = _\<close>
  have "?n\<in>M"
    using separation_ax leI separation_iff by auto
  from generic
  have "filter(G)" "G\<subseteq>P"
    by auto
  from \<open>val(G,\<pi>) = A\<close>
  have "val(G,?m) =
               {z . t\<in>domain(\<pi>) , (\<exists>q\<in>P .
                    (\<exists>\<theta>\<in>M. \<exists>p\<in>P. \<langle>t,q\<rangle> = \<langle>\<theta>, p\<rangle> \<and>
            (p \<in> G \<longrightarrow> val(G, \<theta>) \<in> A \<and> (M[G],  [val(G, \<theta>)] @ env @ [A] \<Turnstile>  \<phi>)) \<and> q \<in> G)) \<and>
           z=val(G,t)}"
    using val_of_name by auto
  also
  have "... =  {z . t\<in>domain(\<pi>) , (\<exists>q\<in>P.
                   val(G, t) \<in> A \<and> (M[G],  [val(G, t)] @ env @ [A] \<Turnstile>  \<phi>) \<and> q \<in> G) \<and> z=val(G,t)}"
    using \<open>domain(\<pi>)\<in>M\<close> by (auto simp add:transitivity)
  also
  have "... =  {x\<in>A . \<exists>q\<in>P. x \<in> A \<and> (M[G],  [x] @ env @ [A] \<Turnstile>  \<phi>) \<and> q \<in> G}"
  proof(intro equalityI, auto)
    (* Now we show the other inclusion:
      {x .. x \<in> A , \<exists>q\<in>P. x \<in> A \<and> (M[G],  [x, w, c] \<Turnstile>  \<phi>) \<and> q \<in> G}
      \<subseteq>
      {val(G,t)..t\<in>domain(\<pi>),\<exists>q\<in>P.val(G,t)\<in> A\<and>(M[G], [val(G,t),w] \<Turnstile> \<phi>)\<and>q\<in>G}
    *)
    {
      fix x q
      assume "M[G], Cons(x, env @ [A]) \<Turnstile> \<phi>" "x\<in>A" "q \<in> P" "q \<in> G"
      from this \<open>val(G,\<pi>) = A\<close>
      show "x \<in> {y . x \<in> domain(\<pi>), val(G, x) \<in> A \<and> (M[G], Cons(val(G, x), env @ [A]) \<Turnstile> \<phi>) \<and> (\<exists>q\<in>P. q \<in> G) \<and> y = val(G, x)}"
        using elem_of_val by force
    }
  qed
  also
  have " ... = {x \<in> A. (M[G], [x] @ env @ [A] \<Turnstile> \<phi>)}"
    using \<open>G\<subseteq>P\<close> G_nonempty by force
  finally
  have val_m: "val(G,?m) = {x \<in> A. (M[G], [x] @ env @ [A] \<Turnstile> \<phi>)}" by simp
  have "val(G,?m) \<subseteq> val(G,?n)"
  proof
    fix x
    assume "x \<in> val(G,?m)"
    with val_m
    have "x \<in> {x \<in> A. (M[G], [x] @ env @ [A] \<Turnstile> \<phi>)}" by simp
    with \<open>val(G,\<pi>) = A\<close>
    have "x \<in> val(G,\<pi>)" by simp
    then
    obtain \<theta> q where "\<langle>\<theta>,q\<rangle>\<in>\<pi>" "q\<in>G" "val(G,\<theta>)=x" "\<theta>\<in>M"
      using elem_of_val_pair domain_trans[OF trans_M \<open>\<pi>\<in>_\<close>]
      by force
    with \<open>\<pi>\<in>M\<close> \<open>nenv \<in> _\<close> \<open>env = _\<close>
    have "[val(G,\<theta>), val(G,\<pi>)] @ env \<in> list(M[G])" "[\<theta>] @ nenv @ [\<pi>]\<in>list(M)"
      using GenExt_def by auto
    with \<open>val(G,\<theta>)=x\<close> \<open>val(G,\<pi>) = A\<close> \<open>x \<in> val(G,\<pi>)\<close> nth \<open>\<theta>\<in>M\<close> \<open>x\<in> {x \<in> A . _}\<close>
    have "M[G],  [val(G,\<theta>)] @ env @ [val(G,\<pi>)] \<Turnstile> \<cdot>\<cdot> 0 \<in> (1 +\<^sub>\<omega> length(env)) \<cdot> \<and> \<phi> \<cdot>"
      by auto
        \<comment> \<open>Recall \<^term>\<open>?\<chi> = And(Member(0,1 +\<^sub>\<omega> length(env)),\<phi>)\<close>\<close>
    with \<open>[_] @ nenv @ [_] \<in> _ \<close> map_nenv \<open>arity(?\<chi>) \<le> length(_)\<close> \<open>length(nenv) = _\<close>
    obtain r where "r\<in>G" "r \<tturnstile> ?\<chi> ([\<theta>] @ nenv @ [\<pi>])"
      using truth_lemma[OF \<open>?\<chi>\<in>_\<close>,of "[\<theta>] @ nenv @ [\<pi>]"]
      by auto
    with \<open>filter(G)\<close> and \<open>q\<in>G\<close>
    obtain p where "p\<in>G" "p\<preceq>q" "p\<preceq>r"
      unfolding filter_def compat_in_def by force
    with \<open>r\<in>G\<close> \<open>q\<in>G\<close> \<open>G\<subseteq>P\<close>
    have "p\<in>P" "r\<in>P" "q\<in>P" "p\<in>M"
      using transitivity[OF _ P_in_M] subsetD
      by simp_all
    with \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>p\<preceq>r\<close> \<open>nenv \<in> _\<close> \<open>arity(?\<chi>) \<le> length(_)\<close> \<open>r \<tturnstile> ?\<chi> _\<close> \<open>env\<in>_\<close>
    have "p \<tturnstile> ?\<chi> ([\<theta>] @ nenv @ [\<pi>])"
      using strengthening_lemma
      by simp
    with \<open>p\<in>P\<close> \<open>\<phi>\<in>formula\<close> \<open>\<theta>\<in>M\<close> \<open>\<pi>\<in>M\<close> \<open>nenv \<in> _\<close> \<open>arity(?\<chi>) \<le> length(_)\<close>
    have "\<forall>F. M_generic(F) \<and> p \<in> F \<longrightarrow>
                 M[F],   map(val(F), [\<theta>] @ nenv @ [\<pi>]) \<Turnstile>  ?\<chi>"
      using definition_of_forcing[where \<phi>="\<cdot>\<cdot> 0 \<in> (1 +\<^sub>\<omega> length(env)) \<cdot> \<and> \<phi> \<cdot>"]
      by simp
    with \<open>p\<in>P\<close> \<open>\<theta>\<in>M\<close>
    have Eq6: "\<exists>\<theta>'\<in>M. \<exists>p'\<in>P.  \<langle>\<theta>,p\<rangle> = \<langle>\<theta>',p'\<rangle> \<and> (\<forall>F. M_generic(F) \<and> p' \<in> F \<longrightarrow>
                 M[F],   map(val(F), [\<theta>'] @ nenv @ [\<pi>]) \<Turnstile>  ?\<chi>)" by auto
    from \<open>\<pi>\<in>M\<close> \<open>\<langle>\<theta>,q\<rangle>\<in>\<pi>\<close> \<open>\<theta>\<in>M\<close> \<open>p\<in>P\<close> \<open>p\<in>M\<close>
    have "\<langle>\<theta>,q\<rangle> \<in> M" "\<langle>\<theta>,p\<rangle>\<in>M" "\<langle>\<theta>,p\<rangle>\<in>domain(\<pi>)\<times>P"
      using pair_in_M_iff transitivity
      by auto
    with \<open>\<theta>\<in>M\<close> Eq6 \<open>p\<in>P\<close>
    have "M, [\<langle>\<theta>,p\<rangle>,P,leq,\<one>,\<pi>] @ nenv \<Turnstile> ?\<psi>"
      using Equivalence by auto
    with \<open>\<langle>\<theta>,p\<rangle>\<in>domain(\<pi>)\<times>P\<close>
    have "\<langle>\<theta>,p\<rangle>\<in>?n" by simp
    with \<open>p\<in>G\<close> \<open>p\<in>P\<close>
    have "val(G,\<theta>)\<in>val(G,?n)"
      using val_of_elem[of \<theta> p] by simp
    with \<open>val(G,\<theta>)=x\<close>
    show "x\<in>val(G,?n)" by simp
  qed (* proof of "val(G,?m) \<subseteq> val(G,?n)" *)
  with val_m first_incl
  have "val(G,?n) = {x \<in> A. (M[G], [x] @ env @ [A] \<Turnstile> \<phi>)}" by auto
  also from \<open>A\<in>_\<close> phi \<open>env \<in> _\<close>
  have " ... = {x \<in> A. (M[G], [x] @ env \<Turnstile> \<phi>)}"
    using arity_sats_iff[where env="[_]@env"] transitivity_MG
    by auto
  finally
  show "{x \<in> A. (M[G], [x] @ env \<Turnstile> \<phi>)}\<in> M[G]"
    using \<open>?n\<in>M\<close> GenExt_def by force
qed

theorem separation_in_MG:
  assumes
    "\<phi>\<in>formula" and "arity(\<phi>) \<le> 1 +\<^sub>\<omega> length(env)" and "env\<in>list(M[G])"
  shows
    "separation(##M[G],\<lambda>x. (M[G], [x] @ env \<Turnstile> \<phi>))"
proof -
  {
    fix A
    assume "A\<in>M[G]"
    moreover from \<open>env \<in> _\<close>
    obtain nenv where "nenv\<in>list(M)""env = map(val(G),nenv)" "length(env) = length(nenv)"
      using GenExt_def map_val[of env] by auto
    moreover note \<open>\<phi> \<in> _\<close> \<open>arity(\<phi>) \<le> _\<close> \<open>env \<in> _\<close>
    ultimately
    have "{x \<in> A . (M[G], [x] @ env \<Turnstile> \<phi>)} \<in> M[G]"
      using Collect_sats_in_MG by auto
  }
  then
  show ?thesis
    using separation_iff rev_bexI unfolding is_Collect_def by force
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

end