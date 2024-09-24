(*<*)
theory Constructions
imports
  Safety_Logic
begin

(*>*)
section\<open> Constructions in the \<^emph>\<open>('a, 's, 'v) spec\<close> lattice\label{sec:constructions} \<close>


subsection\<open> Constrains-at-most \label{sec:cam} \<close>

text\<open>

\<^citet>\<open>\<open>\S3.1\<close> in "AbadiPlotkin:1993"\<close>
require that processes to be composed in parallel
\<^emph>\<open>constrain at most\<close> (CAM) distinct sets of agents:
intuitively each process cannot block other processes from taking
steps after any of its transitions. We model this as a closure.

See \S\ref{sec:abadi_plotkin} for a discussion of their composition rules.

Observations:
 \<^item> the sense of the relation \<open>r\<close> here is inverted wrt Abadi/Plotkin
 \<^item> this is a key ingredient in interference closure (\S\ref{sec:interference_closure})
 \<^item> this closure is antimatroidal

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "cam"\<close>

definition cl :: "('a, 's) steps \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "cl r P = P \<squnion> spec.term.none (spec.term.all P \<bind> (\<lambda>_::unit. spec.rel r :: (_, _, unit) spec))"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none.cam"\<close>

lemma cl:
  shows "spec.term.none (spec.cam.cl r P) = spec.cam.cl r (spec.term.none P)"
by (simp add: spec.cam.cl_def spec.bind.supL spec.bind.bind spec.term.all.bind ac_simps
        flip: spec.bind.botR bot_fun_def)

lemma cl_rel_wind:
  fixes P :: "('a, 's, 'v) spec"
  shows "spec.cam.cl r P \<then> spec.term.none (spec.rel r :: ('a, 's, 'w) spec)
       = spec.term.none (spec.cam.cl r P)"
by (simp add: spec.cam.cl_def spec.term.none.sup spec.term.none.bind spec.bind.supL spec.bind.bind
              bot_fun_def sup.absorb2
              spec.vmap.unitL[where f=P] spec.vmap.unitL[where f="spec.term.all P"]
              spec.vmap.unitL[where f="spec.rel r :: ('a, 's, 'w) spec"]
              spec.term.all.vmap_unit  spec.vmap.unit_rel spec.bind.mono spec.term.all.expansive
        flip: spec.bind.botR)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all.cam"\<close>

lemma cl_le: \<comment>\<open> Converse does not hold \<close>
  shows "spec.cam.cl r (spec.term.all P) \<le> spec.term.all (spec.cam.cl r P)"
by (simp add: spec.term.none.cam.cl flip: spec.term.galois) (simp flip: spec.term.none.cam.cl)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

interpretation cam: closure_complete_distrib_lattice_distributive_class "spec.cam.cl r" for r :: "('a, 's) steps"
proof standard
  show "P \<le> spec.cam.cl r Q \<longleftrightarrow> spec.cam.cl r P \<le> spec.cam.cl r Q" (is "?lhs \<longleftrightarrow> ?rhs") for P Q :: "('a, 's, 'v) spec"
  proof(rule iffI)
    assume ?lhs show ?rhs
      apply (subst spec.cam.cl_def)
      apply (strengthen ord_to_strengthen(1)[OF \<open>?lhs\<close>])
      apply (simp add: spec.cam.cl_def spec.term.galois spec.term.all.sup spec.term.all.bind
                       spec.bind.supL spec.term.all.rel spec.bind.bind spec.rel.wind_bind)
      done
next
    show "?rhs \<Longrightarrow> ?lhs"
      by (simp add: spec.cam.cl_def)
  qed
  show "spec.cam.cl r (\<Squnion>P) \<le> \<Squnion>(spec.cam.cl r ` P) \<squnion> spec.cam.cl r \<bottom>" for P :: "('a, 's, 'v) spec set"
    by (simp add: spec.cam.cl_def spec.term.none.bind spec.term.all.Sup spec.bind.SupL
                  spec.term.none.Sup SUP_upper2)
qed

setup \<open>Sign.mandatory_path "cam"\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

lemma bot[simp]:
  shows "spec.cam.cl r \<bottom> = \<bottom>"
by (simp add: spec.cam.cl_def)

lemma mono:
  fixes r :: "('a, 's) steps"
  assumes "r \<subseteq> r'"
  assumes "P \<le> P'"
  shows "spec.cam.cl r P \<le> spec.cam.cl r' P'"
unfolding spec.cam.cl_def
apply (strengthen ord_to_strengthen(1)[OF \<open>r \<le> r'\<close>])
apply (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>])
apply blast
done

declare spec.cam.strengthen_cl[strg del]

lemma strengthen[strg]:
  assumes "st_ord F r r'"
  assumes "st_ord F P P'"
  shows "st_ord F (spec.cam.cl r P) (spec.cam.cl r' P')"
using assms by (cases F; simp add: spec.cam.cl.mono)

lemma Sup:
  shows "spec.cam.cl r (\<Squnion>X) = (\<Squnion>P\<in>X. spec.cam.cl r P)"
by (simp add: spec.cam.cl_Sup)

lemmas sup = spec.cam.cl.Sup[where X="{P, Q}" for P Q, simplified]

lemma rel_empty:
  shows "spec.cam.cl {} P = P"
by (simp add: spec.cam.cl_def spec.rel.empty sup.absorb1 UNIV_unit)

lemma rel_reflcl:
  shows "spec.cam.cl (r \<union> A \<times> Id) P = spec.cam.cl r P"
    and "spec.cam.cl (A \<times> Id \<union> r) P = spec.cam.cl r P"
by (simp_all add: spec.cam.cl_def spec.rel.reflcl)

lemma rel_minus_Id:
  shows "spec.cam.cl (r - UNIV \<times> Id) P = spec.cam.cl r P"
by (metis Un_Diff_cancel2 spec.cam.cl.rel_reflcl(1))

lemma Inf:
  shows "spec.cam.cl r (\<Sqinter>X) = \<Sqinter>(spec.cam.cl r ` X)" (is "?lhs = ?rhs")
proof(rule antisym[OF spec.cam.cl_Inf_le spec.singleton_le_extI])
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
  proof (cases "trace.term \<sigma>")
    case None
    have "\<lblot>\<sigma>\<rblot> \<le> \<Sqinter> (spec.term.all ` X) \<bind> (\<lambda>v. spec.term.none (spec.rel r))"
      if "x \<in> X" and "\<not> \<lblot>\<sigma>\<rblot> \<le> x"
     for x
    proof -
      from \<open>\<lblot>\<sigma>\<rblot> \<le> ?rhs\<close> that
      have "\<lblot>\<sigma>\<rblot> \<le> spec.term.all x \<bind> (\<lambda>_::unit. spec.term.none (spec.rel r :: (_, _, unit) spec))"
        by (auto simp: spec.cam.cl_def le_Inf_iff spec.term.none.bind)
      then show ?thesis
      proof(induct rule: spec.singleton.bind_le)
        case incomplete with \<open>\<not> \<lblot>\<sigma>\<rblot> \<le> x\<close> show ?case
          using order_trans by auto
      next
        case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f)
        from None obtain xs ys
          where *: "\<forall>xs' zs. trace.rest \<sigma> = xs' @ zs \<and> trace.steps' (trace.final' (trace.init \<sigma>) xs') zs \<subseteq> r
                         \<longrightarrow> length xs \<le> length xs'"
                   "xs @ ys = trace.rest \<sigma>"
                   "trace.steps' (trace.final' (trace.init \<sigma>) xs) ys \<subseteq> r"
          using ex_has_least_nat[where P="\<lambda>xs. \<exists>ys. trace.rest \<sigma> = xs @ ys
                                             \<and> trace.steps' (trace.final' (trace.init \<sigma>) xs) ys \<subseteq> r"
                                   and k="trace.rest \<sigma>"
                                   and m=length]
          by clarsimp
        show ?case
        proof(induct rule: spec.bind.continueI[where s="trace.init \<sigma>" and xs=xs and ys=ys
                                                 and v=undefined and w="trace.term \<sigma>",
                                               simplified \<open>xs @ ys = trace.rest \<sigma>\<close> trace.t.collapse,
                                               case_names f g])
          case f
          have "\<lblot>trace.init \<sigma>, xs, None\<rblot> \<le> x"
            if "x \<in> X"
           and "\<lblot>\<sigma>\<rblot> \<le> spec.cam.cl r x"
           for x
            using that(2)[unfolded spec.cam.cl_def, simplified]
          proof(induct rule: disjE[consumes 1, case_names expansive cam])
            case expansive with \<open>xs @ ys = trace.rest \<sigma>\<close> show ?case
              by (cases \<sigma>)
                 (fastforce elim: order.trans[rotated]
                            simp: spec.singleton.mono trace.less_eq_same_append_conv)

          next
            case cam from cam[unfolded spec.term.none.bind] show ?case
            proof(induct rule: spec.singleton.bind_le)
              case incomplete with \<open>xs @ ys = trace.rest \<sigma>\<close> show ?case
                by clarsimp
                   (metis prefixI spec.singleton.mono spec.singleton_le_ext_conv
                          spec.term.none.contractive trace.less_eq_None(2))
            next
              case (continue \<sigma>\<^sub>f \<sigma>\<^sub>g v\<^sub>f) with *(1,2) show ?case
                by (clarsimp simp: spec.singleton.le_conv trace.less_eq_None
                            elim!: order.trans[rotated]
                           intro!: spec.singleton.mono)
                   (metis prefixI prefix_length_prefix)
            qed
          qed
          with \<open>\<lblot>\<sigma>\<rblot> \<le> ?rhs\<close> show ?case
            by (simp add: le_Inf_iff spec.singleton.le_conv exI[where x=None])
        next
          case g with None *(3) show ?case
            by (simp add: spec.singleton.le_conv)
        qed
    qed
  qed
  then show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    by (auto simp: spec.cam.cl_def spec.term.none.bind spec.term.all.Inf le_Inf_iff)
  next
    case Some with \<open>\<lblot>\<sigma>\<rblot> \<le> ?rhs\<close> show ?thesis
      by (simp add: le_Inf_iff spec.cam.cl_def spec.singleton.term.none_le_conv)
  qed
qed

lemmas inf = spec.cam.cl.Inf[where X="{P, Q}" for P Q, simplified]

lemma idle:
  shows "spec.cam.cl r spec.idle = spec.term.none (spec.rel r :: (_, _, unit) spec)"
by (simp add: spec.cam.cl_def spec.term.all.idle UNIV_unit spec.bind.returnL
              spec.idle_le sup_absorb2)

lemma bind:
  shows "spec.cam.cl r (f \<bind> g) = spec.cam.cl r f \<bind> (\<lambda>v. spec.cam.cl r (g v))"
by (simp add: spec.cam.cl_def spec.bind.supL spec.bind.supR spec.bind.bind ac_simps spec.term.all.bind
        flip: spec.bind.botR bot_fun_def)

lemma action:
  fixes r :: "('a, 's) steps"
  fixes F :: "('v \<times> 'a \<times> 's \<times> 's) set"
  shows "spec.cam.cl r (spec.action F)
       = spec.action F
      \<squnion> spec.term.none (spec.action F \<then> (spec.rel r :: (_, _, unit) spec))
      \<squnion> spec.term.none (spec.rel r :: (_, _, unit) spec)"
by (simp add: spec.cam.cl_def spec.term.all.action spec.term.none.bind spec.term.none.sup
              spec.bind.botR spec.bind.supL spec.bind.returnL spec.idle_le
              spec.vmap.unitL[where f="spec.action F"] spec.map.surj_sf_action
              UNIV_unit map_prod_const_image ac_simps
        flip: spec.return_def)

lemma return:
  shows "spec.cam.cl r (spec.return v) = spec.return v \<squnion> spec.term.none (spec.rel r :: (_, _, unit) spec)"
unfolding spec.return_def spec.cam.cl.action
by (simp add: spec.bind.returnL spec.idle_le bot_fun_def
        flip: spec.return_def bot_fun_def)

lemma rel_le:
  assumes "r \<subseteq> r' \<or> r' \<subseteq> r"
  shows "spec.cam.cl r (spec.rel r') \<le> spec.rel (r \<union> r')"
using assms
by (auto simp: spec.cam.cl_def spec.rel.mono spec.term.all.rel
               spec.rel.wind_bind_leading spec.rel.wind_bind_trailing spec.term.galois)

lemma rel:
  assumes "r \<subseteq> r'"
  shows "spec.cam.cl r (spec.rel r') = spec.rel r'"
by (simp add: assms spec.eq_iff spec.cam.expansive
              order.trans[OF spec.cam.cl.rel_le[OF disjI1] spec.rel.mono])

lemma inf_rel:
  fixes r :: "('a, 's) steps"
  fixes s :: "('a, 's) steps"
  fixes P :: "('a, 's, 'v) spec"
  shows "spec.rel r \<sqinter> spec.cam.cl r' P = spec.cam.cl (r \<inter> r') (spec.rel r \<sqinter> P)" (is ?thesis1)
    and "spec.cam.cl r' P \<sqinter> spec.rel r = spec.cam.cl (r \<inter> r') (spec.rel r \<sqinter> P)" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: spec.cam.cl_def ac_simps inf_sup_distrib
                  spec.term.none.bind spec.term.all.inf spec.term.all.rel
                  spec.bind.inf_rel spec.rel.inf spec.term.none.inf spec.term.none.inf_none_rel(1))
  then show ?thesis2
    by (rule inf_commute_conv)
qed

lemma bind_return:
  shows "spec.cam.cl r (f \<then> spec.return v) = spec.cam.cl r f \<then> spec.return v"
by (simp add: spec.cam.cl.bind spec.cam.cl.return spec.bind.supR sup.absorb1 spec.term.none.cam.cl_rel_wind)

lemma heyting_le:
  shows "spec.cam.cl r (P \<^bold>\<longrightarrow>\<^sub>H Q) \<le> P \<^bold>\<longrightarrow>\<^sub>H spec.cam.cl r Q"
by (force intro!: SupI
            dest: spec.cam.mono_cl[where r=r]
            elim: order.trans[rotated]
            simp: heyting_def spec.cam.cl.Sup spec.cam.cl.inf le_infI1 spec.cam.expansive)

lemma pre:
  shows "spec.cam.cl r (spec.pre P) = spec.pre P"
by (simp add: spec.cam.cl_def spec.term.none.bind spec.term.all.pre sup_iff_le spec.bind.inf_pre
        flip: inf_iff_le)

lemma post:
  shows "spec.cam.cl r (spec.post Q) = spec.post Q"
by (simp add: spec.cam.cl_def spec.term.none.post_le sup_iff_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "closed"\<close>

lemma empty:
  shows "spec.cam.closed {} = UNIV"
by (simp add: order.eq_iff spec.cam.cl.rel_empty spec.cam.closed_clI subsetI)

lemma antimonotone:
  shows "antimono spec.cam.closed"
by (rule monotoneI) (auto intro: spec.cam.closed_clI elim: spec.cam.le_closedE[OF spec.cam.cl.mono])

lemmas strengthen[strg] = st_ord_antimono[OF spec.cam.closed.antimonotone]
lemmas antimono = antimonoD[OF spec.cam.closed.antimonotone, of r r' for r r']

lemma reflcl:
  shows "spec.cam.closed (r \<union> A \<times> Id) = spec.cam.closed r"
by (simp add: spec.cam.cl.rel_reflcl(1) spec.cam.closed_def)

setup \<open>Sign.mandatory_path "term"\<close>

lemma none:
  assumes "P \<in> spec.cam.closed r"
  shows "spec.term.none P \<in> spec.cam.closed r"
by (simp add: assms spec.cam.closed_clI flip: spec.term.none.cam.cl spec.cam.closed_conv[OF assms])

setup \<open>Sign.parent_path\<close>

lemma bind:
  fixes f :: "('a, 's, 'v) spec"
  fixes g :: "'v \<Rightarrow> ('a, 's, 'w) spec"
  assumes "f \<in> spec.cam.closed r"
  assumes "\<And>x. g x \<in> spec.cam.closed r"
  shows "f \<bind> g \<in> spec.cam.closed r"
by (simp add: assms spec.cam.closed_clI spec.cam.least spec.cam.cl.bind spec.bind.mono)

lemma rel[intro]:
  assumes "r \<subseteq> r'"
  shows "spec.rel r' \<in> spec.cam.closed r"
by (simp add: assms spec.cam.closed_clI spec.cam.cl.rel)

lemma pre[intro]:
  shows "spec.pre P \<in> spec.cam.closed r"
by (simp add: spec.cam.closed_clI spec.cam.cl.pre)

lemma post[intro]:
  shows "spec.post Q \<in> spec.cam.closed r"
by (simp add: spec.cam.closed_clI spec.cam.cl.post)

lemma heyting[intro]:
  assumes "Q \<in> spec.cam.closed r"
  shows "P \<^bold>\<longrightarrow>\<^sub>H Q \<in> spec.cam.closed r"
by (rule spec.cam.closed_clI)
   (simp add: assms order.trans[OF spec.cam.cl.heyting_le] flip: spec.cam.closed_conv)

lemma snoc_conv:
  fixes P :: "('a, 's, 'v) spec"
  assumes "P \<in> spec.cam.closed r"
  assumes "(fst x, trace.final' s xs, snd x) \<in> r \<union> UNIV \<times> Id"
  shows "\<lblot>s, xs @ [x], None\<rblot> \<le> P \<longleftrightarrow> \<lblot>s, xs, None\<rblot> \<le> P" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    by (erule order.trans[rotated]) (simp add: spec.singleton.mono trace.less_eq_same_append_conv)
  from assms(2) show "?rhs \<Longrightarrow> ?lhs"
    by (subst spec.cam.closed_conv[OF \<open>P \<in> spec.cam.closed r\<close>])
       (auto simp: spec.cam.cl_def spec.singleton.term.none_le_conv
                   spec.term.none.singleton spec.steps.singleton
        simp flip: spec.rel.galois spec.term.galois
            intro: spec.bind.continueI)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap.cam"\<close>

lemma cl:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes r :: "('b, 't) steps"
  fixes P :: "('b, 't, 'w) spec"
  shows "spec.invmap af sf vf (spec.cam.cl r P)
       = spec.cam.cl (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)) (spec.invmap af sf vf P)"
by (simp add: spec.cam.cl_def spec.invmap.sup spec.invmap.bind spec.invmap.rel spec.term.all.invmap
        flip: spec.term.none.invmap_gen[where vf=id])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map.cam"\<close>

lemma cl_le:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes r :: "('a, 's) steps"
  fixes P :: "('a, 's, 'v) spec"
  shows "spec.map af sf vf (spec.cam.cl r P)
      \<le> spec.cam.cl (map_prod af (map_prod sf sf) ` r) (spec.map af sf vf P)"
by (simp add: spec.map_invmap.galois spec.map_invmap.upper_lower_expansive
              spec.invmap.cam.cl spec.cam.cl.mono subset_vimage_iff le_supI1)

lemma cl_inj_sf:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes r :: "('a, 's) steps"
  fixes P :: "('a, 's, 'v) spec"
  assumes "inj sf"
  shows "spec.map af sf vf (spec.cam.cl r P)
       = spec.cam.cl (map_prod af (map_prod sf sf) ` r) (spec.map af sf vf P)"
apply (simp add: spec.cam.cl_def spec.map.sup spec.map.bind_inj_sf[OF \<open>inj sf\<close>] spec.term.all.map
           flip: spec.term.none.map_gen[where vf=id])
apply (subst spec.map.rel, blast dest: injD[OF \<open>inj sf\<close>])
apply (simp add: inf.absorb1 spec.map_invmap.galois spec.invmap.post flip: spec.bind_post_pre)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Abadi and Plotkin's composition principle\label{sec:abadi_plotkin} \<close>

text\<open>

\<^citet>\<open>"AbadiPlotkin:1991" and "AbadiPlotkin:1993"\<close>
develop a theory of circular reasoning about Heyting implication for
safety properties under the mild condition that each is CAM-closed with respect to the other.

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

abbreviation ap_cam_cl :: "'a set \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "ap_cam_cl as \<equiv> spec.cam.cl ((-as) \<times> UNIV)"

abbreviation (input) ap_cam_closed :: "'a set \<Rightarrow> ('a, 's, 'v) spec set" where
  "ap_cam_closed as \<equiv> spec.cam.closed ((-as) \<times> UNIV)"

lemma composition_principle_1:
  fixes P :: "('a, 's, 'v) spec"
  assumes "P \<in> spec.ap_cam_closed as"
  assumes "P \<in> spec.term.closed _"
  assumes "spec.idle \<le> P"
  shows "spec.ap_cam_cl (-as) P \<^bold>\<longrightarrow>\<^sub>H P \<le> P" (is "?lhs \<le> ?rhs")
proof(rule spec.term.closed.singleton_le_extI)
  show "\<lblot>s, xs, None\<rblot> \<le> ?rhs" if "\<lblot>s, xs, None\<rblot> \<le> ?lhs" for s xs
    using that
  proof(induct xs rule: rev_induct)
    case Nil
    from \<open>spec.idle \<le> P\<close> show ?case
      by (simp add: order.trans[OF spec.idle.minimal_le])
  next
    case (snoc x xs)
    from snoc.prems have "\<lblot>s, xs, None\<rblot> \<le> spec.ap_cam_cl (- as) P \<^bold>\<longrightarrow>\<^sub>H P"
      by (simp add: order.trans[OF spec.singleton.mono, rotated] trace.less_eq_None)
    with snoc.hyps have "\<lblot>s, xs, None\<rblot> \<le> P" by blast
    show ?case
    proof(cases "fst x \<in> as")
      case True
      with \<open>\<lblot>s, xs, None\<rblot> \<le> P\<close> have "\<lblot>s, xs @ [x], None\<rblot> \<le> spec.ap_cam_cl (-as) P"
        by (subst spec.cam.closed.snoc_conv) (auto simp: order.trans[OF _ spec.cam.expansive])
      with snoc.prems show ?thesis by (blast intro: heyting.mp)
    next
      case False with \<open>P \<in> spec.ap_cam_closed as\<close> \<open>\<lblot>s, xs, None\<rblot> \<le> P\<close> show ?thesis
        by (simp add: spec.cam.closed.snoc_conv)
    qed
  qed
qed fact

lemma composition_principle_half: \<comment>\<open> \<^citet>\<open>\<open>\S3.1(4)\<close> in "AbadiPlotkin:1993"\<close> -- cleaner than in \<^citet>\<open>\<open>\S3.1\<close> in "AbadiPlotkin:1991"\<close> \<close>
  assumes "M\<^sub>1 \<in> spec.ap_cam_closed a\<^sub>1"
  assumes "M\<^sub>2 \<in> spec.ap_cam_closed a\<^sub>2"
  assumes "M\<^sub>1 \<in> spec.term.closed _"
  assumes "spec.idle \<le> M\<^sub>1"
  assumes "a\<^sub>1 \<inter> a\<^sub>2 = {}"
  shows "(M\<^sub>1 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>2) \<sqinter> (M\<^sub>2 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>1) \<le> M\<^sub>1"
proof -
  have "(M\<^sub>1 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>2) \<sqinter> (M\<^sub>2 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>1) \<le> (spec.ap_cam_cl (-a\<^sub>1) M\<^sub>1 \<^bold>\<longrightarrow>\<^sub>H spec.ap_cam_cl (-a\<^sub>1) M\<^sub>2) \<sqinter> (M\<^sub>2 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>1)"
    by (rule inf_mono[OF heyting.closure_imp_distrib_le[OF closure.axioms(2)[OF spec.cam.closure_axioms]] order.refl])
       (simp add: spec.cam.cl.inf)
  also have "\<dots> \<le> spec.ap_cam_cl (-a\<^sub>1) M\<^sub>1 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>1"
  proof -
    from \<open>M\<^sub>2 \<in> spec.ap_cam_closed a\<^sub>2\<close> \<open>a\<^sub>1 \<inter> a\<^sub>2 = {}\<close> have "spec.ap_cam_cl (-a\<^sub>1) M\<^sub>2 \<le> M\<^sub>2"
      by (fastforce intro: spec.cam.least elim: subsetD[OF spec.cam.closed.antimono, rotated])
    then show ?thesis
      by (simp add: heyting.trans order_antisym_conv spec.cam.expansive)
  qed
  also have "\<dots> \<le> M\<^sub>1"
    by (rule spec.composition_principle_1[OF \<open>M\<^sub>1 \<in> spec.ap_cam_closed a\<^sub>1\<close> \<open>M\<^sub>1 \<in> spec.term.closed _\<close> \<open>spec.idle \<le> M\<^sub>1\<close>])
  finally show ?thesis .
qed

theorem composition_principle: \<comment> \<open> \<^citet>\<open>\<open>\S3.1(3)\<close> in "AbadiPlotkin:1993"\<close> \<close>
  assumes "M\<^sub>1 \<in> spec.ap_cam_closed a\<^sub>1"
  assumes "M\<^sub>2 \<in> spec.ap_cam_closed a\<^sub>2"
  assumes "M\<^sub>1 \<in> spec.term.closed _"
  assumes "M\<^sub>2 \<in> spec.term.closed _"
  assumes "spec.idle \<le> M\<^sub>1"
  assumes "spec.idle \<le> M\<^sub>2"
  assumes "a\<^sub>1 \<inter> a\<^sub>2 = {}"
  shows "(M\<^sub>1 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>2) \<sqinter> (M\<^sub>2 \<^bold>\<longrightarrow>\<^sub>H M\<^sub>1) \<le> M\<^sub>1 \<sqinter> M\<^sub>2"
using assms by (metis spec.composition_principle_half inf.bounded_iff inf.commute)

text\<open>

An infinitary variant can be established in essentially the same way
as @{thm [source] "spec.composition_principle_1"}.

\<close>

lemma ag_circular:
  fixes Ps :: "'a \<Rightarrow> ('a, 's, 'v) spec"
  assumes cam_closed: "\<And>a. a \<in> as \<Longrightarrow> Ps a \<in> spec.ap_cam_closed {a}"
  assumes term_closed: "\<And>a. a \<in> as \<Longrightarrow> Ps a \<in> spec.term.closed _"
  assumes idle: "\<And>a. a \<in> as \<Longrightarrow> spec.idle \<le> Ps a"
  shows "(\<Sqinter>a\<in>as. (\<Sqinter>a'\<in>as-{a}. Ps a') \<^bold>\<longrightarrow>\<^sub>H Ps a) \<le> (\<Sqinter>a\<in>as. Ps a)" (is "?lhs \<le> ?rhs")
proof(rule spec.term.closed.singleton_le_extI)
  show "\<lblot>s, xs, None\<rblot> \<le> ?rhs" if "\<lblot>s, xs, None\<rblot> \<le> ?lhs" for s xs
    using that
  proof(induct xs rule: rev_induct)
    case Nil from idle show ?case
      by (simp add: le_INF_iff order.trans[OF spec.idle.minimal_le])
  next
    case (snoc x xs)
    have *: "\<lblot>s, xs, None\<rblot> \<le> ?rhs"
      by (simp add: snoc(1) order.trans[OF spec.singleton.mono snoc(2)] trace.less_eq_same_append_conv)
    have "\<lblot>s, xs @ [x], None\<rblot> \<le> Ps a" if "a \<in> as" for a
    proof(cases "fst x = a")
      case True
      with cam_closed * have "\<lblot>s, xs @ [x], None\<rblot> \<le> \<Sqinter>(Ps ` (as - {a}))"
        by (subst spec.cam.closed.snoc_conv[where r="\<Sqinter>a'\<in>as-{a}. (- {a'}) \<times> UNIV"])
           (auto simp: le_INF_iff intro: subsetD[OF spec.cam.closed.antimono, rotated])
      with snoc.prems(1) \<open>a \<in> as\<close> show ?thesis
        by (meson heyting.mp le_INF_iff)
    next
      case False with cam_closed * \<open>a \<in> as\<close> show ?thesis
        by (fastforce simp: spec.cam.closed.snoc_conv le_INF_iff)
    qed
    then show ?case by (blast intro: INFI)
  qed
  from term_closed show "?rhs \<in> spec.term.closed _"
    by (fastforce simp: spec.term.all.monomorphic)
qed

setup \<open>Sign.parent_path\<close>


subsection\<open> Interference closure\label{sec:interference_closure} \<close>

text\<open>

We add environment interference to the beginnings and ends of behaviors for two reasons:
 \<^item> it ensures the wellformedness of parallel composition as conjunction (see \S\ref{sec:constructions-parallel_composition})
 \<^item> it guarantees the monad laws hold (see \S\ref{sec:programs-laws})
  \<^item> \<^const>\<open>spec.cam.cl\<close> by itself is too weak to justify these

We use this closure to build the program sublattice of the \<^typ>\<open>('a, 's, 'v) spec\<close> lattice (see \S\ref{sec:programs}).

Observations:
 \<^item> if processes are made out of actions then it is not necessary to apply \<^const>\<open>spec.cam.cl\<close>

\<close>

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

definition cl :: "('a, 's) steps \<Rightarrow> ('a, 's, 'v) spec \<Rightarrow> ('a, 's, 'v) spec" where
  "cl r P = spec.rel r \<bind> (\<lambda>_::unit. spec.cam.cl r P) \<bind> (\<lambda>v. spec.rel r \<bind> (\<lambda>_::unit. spec.return v))"

setup \<open>Sign.parent_path\<close>

interpretation interference: closure_complete_distrib_lattice_distributive_class "spec.interference.cl r"
           for r :: "('a, 's) steps"
proof
  show "P \<le> spec.interference.cl r Q \<longleftrightarrow> spec.interference.cl r P \<le> spec.interference.cl r Q" (is "?lhs \<longleftrightarrow> ?rhs")
   for P Q :: "('a, 's, 'v) spec"
  proof(rule iffI)
    assume ?lhs show ?rhs
      apply (subst spec.interference.cl_def)
      apply (strengthen ord_to_strengthen(1)[OF \<open>?lhs\<close>])
      apply (simp add: spec.interference.cl_def spec.cam.cl.bind spec.cam.cl.return spec.cam.cl.rel
                       spec.bind.bind spec.bind.supL spec.bind.supR
                       spec.bind.returnL spec.idle_le
                 flip: bot_fun_def spec.bind.botR)
      apply (simp add: spec.rel.wind_bind flip: spec.bind.bind)
      apply (simp add: spec.bind.bind spec.bind.mono)
      done
  next
    assume ?rhs show ?lhs
      apply (strengthen ord_to_strengthen(2)[OF \<open>?rhs\<close>])
      apply (simp add: spec.interference.cl_def spec.bind.bind)
      apply (strengthen ord_to_strengthen(2)[OF spec.cam.expansive])
      apply (strengthen ord_to_strengthen(2)[OF spec.return.rel_le])
      apply (auto simp: spec.bind.return intro: spec.bind.returnL_le)
      done
  qed
  show "spec.interference.cl r (\<Squnion>P) \<le> \<Squnion>(spec.interference.cl r ` P) \<squnion> spec.interference.cl r \<bottom>"
   for P :: "('a, 's, 'v) spec set"
    by (simp add: spec.interference.cl_def spec.cam.cl.Sup image_image
                  spec.bind.SupL spec.bind.supL spec.bind.SUPR
            flip: bot_fun_def)
qed

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

lemma cl:
  shows "spec.term.none (spec.interference.cl r P) = spec.interference.cl r (spec.term.none P)"
by (simp add: spec.interference.cl_def spec.term.none.bind spec.term.none.return
              spec.bind.bind spec.bind.idleR spec.bind.botR spec.term.none.cam.cl_rel_wind
        flip: spec.term.none.cam.cl)

setup \<open>Sign.mandatory_path "closed"\<close>

lemma rel_le:
  assumes "P \<in> spec.interference.closed r"
  shows "spec.term.none (spec.rel r) \<le> P"
by (subst spec.interference.closed_conv[OF assms])
   (simp add: spec.interference.cl_def spec.term.galois spec.term.all.bind spec.term.all.rel ac_simps)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma cl_le: \<comment>\<open> Converse does not hold \<close>
  shows "spec.interference.cl r (spec.term.all P) \<le> spec.term.all (spec.interference.cl r P)"
by (simp add: spec.interference.cl_def spec.bind.bind spec.bind.idleR spec.bind.botR
              spec.term.none.bind spec.term.none.return
              spec.term.none.cam.cl_rel_wind spec.term.none.cam.cl
        flip: spec.term.galois)
   (simp add: spec.bind.mono flip: spec.term.none.cam.cl)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "cam.closed.interference"\<close>

lemma cl:
  shows "spec.interference.cl r P \<in> spec.cam.closed r"
by (metis spec.cam.closed_clI spec.interference.cl_def spec.interference.expansive
          spec.interference.idempotent(1) spec.cam.idempotent(1))

lemma closed_subseteq:
  shows "spec.interference.closed r \<subseteq> spec.cam.closed r"
by (metis spec.cam.closed.interference.cl spec.interference.closed_conv subsetI)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference"\<close>

setup \<open>Sign.mandatory_path "cl"\<close>

lemma mono:
  assumes "r \<subseteq> r'"
  assumes "P \<le> P'"
  shows "spec.interference.cl r P \<le> spec.interference.cl r' P'"
unfolding spec.interference.cl_def
apply (strengthen ord_to_strengthen(1)[OF \<open>r \<subseteq> r'\<close>])
apply (strengthen ord_to_strengthen(1)[OF \<open>P \<le> P'\<close>])
apply simp
done

declare spec.interference.strengthen_cl[strg del]

lemma strengthen[strg]:
  assumes "st_ord F r r'"
  assumes "st_ord F P P'"
  shows "st_ord F (spec.interference.cl r P) (spec.interference.cl r' P')"
using assms by (cases F; simp add: spec.interference.cl.mono)

lemma bot:
  shows "spec.interference.cl r \<bottom> = spec.term.none (spec.rel r :: (_, _, unit) spec)"
by (simp add: spec.interference.cl_def spec.bind.bind flip: bot_fun_def spec.bind.botR)

lemmas Sup = spec.interference.cl_Sup
lemmas sup = spec.interference.cl_sup

lemma idle:
  shows "spec.interference.cl r spec.idle = spec.term.none (spec.rel r :: (_, _, unit) spec)"
by (simp add: spec.interference.cl_def spec.cam.cl.idle spec.bind.bind spec.rel.wind_bind
        flip: spec.term.none.bind)

lemma rel_empty:
  assumes "spec.idle \<le> P"
  shows "spec.interference.cl {} P = P"
by (simp add: spec.interference.cl_def spec.rel.empty spec.cam.cl.rel_empty spec.bind.return
              spec.bind.returnL assms UNIV_unit)

lemma rel_reflcl:
  shows "spec.interference.cl (r \<union> A \<times> Id) P = spec.interference.cl r P"
    and "spec.interference.cl (A \<times> Id \<union> r) P = spec.interference.cl r P"
by (simp_all add: spec.interference.cl_def spec.cam.cl.rel_reflcl spec.rel.reflcl)

lemma rel_minus_Id:
  shows "spec.interference.cl (r - UNIV \<times> Id) P = spec.interference.cl r P"
by (metis Un_Diff_cancel2 spec.interference.cl.rel_reflcl(1))

(* Inf *)

lemma inf_rel:
  shows "spec.interference.cl s P \<sqinter> spec.rel r = spec.interference.cl (r \<inter> s) (spec.rel r \<sqinter> P)"
    and "spec.rel r \<sqinter> spec.interference.cl s P = spec.interference.cl (r \<inter> s) (spec.rel r \<sqinter> P)"
by (simp_all add: spec.interference.cl_def spec.bind.inf_rel spec.return.inf_rel spec.cam.cl.inf_rel
            flip: spec.rel.inf)

lemma bindL:
  assumes "f \<in> spec.interference.closed r"
  shows "spec.interference.cl r (f \<bind> g) = f \<bind> (\<lambda>v. spec.interference.cl r (g v))"
apply (subst (1 2) spec.interference.closed_conv[OF assms])
apply (simp add: spec.interference.cl_def spec.bind.bind spec.cam.cl.bind spec.cam.cl.rel
                 spec.cam.cl.return spec.bind.supL spec.bind.return)
apply (simp add: spec.rel.wind_bind flip: spec.bind.bind)
done

lemma bindR:
  assumes "\<And>v. g v \<in> spec.interference.closed r"
  shows "spec.interference.cl r (f \<bind> g) = spec.interference.cl r f \<bind> g" (is "?lhs = ?rhs")
proof -
  from assms have "?lhs = spec.interference.cl r (f \<bind> (\<lambda>v. spec.interference.cl r (g v)))"
    by (meson spec.interference.closed_conv)
  also have "\<dots> = spec.interference.cl r f \<bind> (\<lambda>v. spec.interference.cl r (g v))"
    apply (simp add: spec.interference.cl_def spec.bind.bind spec.cam.cl.bind spec.cam.cl.rel
                     spec.cam.cl.return spec.bind.supL spec.bind.supR spec.bind.return
                     sup.absorb1 spec.bind.mono
               flip: spec.bind.botR)
    apply (simp add: spec.rel.wind_bind flip: spec.bind.bind)
    done
  also from assms have "\<dots> = ?rhs"
    by (simp flip: spec.interference.closed_conv)
  finally show ?thesis .
qed

lemma bind_conv:
  assumes "f \<in> spec.interference.closed r"
  assumes "\<forall>x. g x \<in> spec.interference.closed r"
  shows "spec.interference.cl r (f \<bind> g) = f \<bind> g"
using assms by (simp add: spec.interference.cl.bindR flip: spec.interference.closed_conv)

lemma action:
  shows "spec.interference.cl r (spec.action F)
       = spec.rel r \<bind> (\<lambda>_::unit. spec.action F \<bind> (\<lambda>v. spec.rel r \<bind> (\<lambda>_::unit. spec.return v)))"
by (simp add: spec.interference.cl_def spec.cam.cl.action spec.bind.supL spec.bind.supR
        flip: spec.bind.botR spec.bind.bind spec.rel.unwind_bind)
   (simp add: spec.bind.bind sup.absorb1 spec.bind.mono)

lemma return:
  shows "spec.interference.cl r (spec.return v) = spec.rel r \<bind> (\<lambda>_::unit. spec.return v)"
by (simp add: spec.return_def spec.interference.cl.action spec.bind.bind)
   (simp add: spec.bind.return spec.rel.wind_bind flip: spec.return_def spec.bind.bind)

lemma bind_return:
  shows "spec.interference.cl r (f \<then> spec.return v) = spec.interference.cl r f \<then> spec.return v"
by (simp add: spec.interference.cl_def spec.bind.bind spec.bind.return spec.cam.cl.bind_return)

lemma rel: \<comment>\<open> complicated by polymorphic \<^const>\<open>spec.rel\<close> \<close>
  assumes "r \<subseteq> r' \<or> r' \<subseteq> r"
  shows "spec.interference.cl r (spec.rel r') = spec.rel (r \<union> r')" (is "?lhs = ?rhs")
using assms
proof
  show ?thesis if "r \<subseteq> r'"
    apply (simp add: \<open>r \<subseteq> r'\<close> sup.absorb2 spec.eq_iff spec.interference.expansive)
    apply (strengthen ord_to_strengthen(1)[OF \<open>r \<subseteq> r'\<close>])
    apply (metis spec.interference.cl.bot spec.interference.idempotent(1) spec.term.all.rel
                 spec.term.all_none spec.term.none.interference.all.cl_le)
    done
  show ?thesis if "r' \<subseteq> r"
  proof(rule antisym)
    from \<open>r' \<subseteq> r\<close> show "?lhs \<le> ?rhs"
      by (simp add: inf.absorb_iff1 spec.interference.cl.inf_rel flip: spec.rel.inf)
    from \<open>r' \<subseteq> r\<close> show "?rhs \<le> ?lhs"
      by (simp add: sup.absorb1 spec.interference.cl_def spec.cam.cl_def
            spec.rel.wind_bind_trailing le_supI1  spec.bind.supR spec.bind.return
            order.trans[OF _ spec.bind.mono[OF order.refl spec.bind.mono[OF spec.return.rel_le order.refl]]])
  qed
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle.interference"\<close>

lemma cl_le[spec.idle_le]:
  shows "spec.idle \<le> spec.interference.cl r P"
by (simp add: spec.interference.cl_def spec.idle_le)

lemma closed_le[spec.idle_le]:
  assumes "P \<in> spec.interference.closed r"
  shows "spec.idle \<le> P"
by (subst spec.interference.closed_conv[OF assms]) (simp add: spec.idle.interference.cl_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map.interference"\<close>

lemma cl_sf_id:
  shows "spec.map af id vf (spec.interference.cl r P)
       = spec.interference.cl (map_prod af id ` r) (spec.map af id vf P)"
apply (simp add: spec.interference.cl_def spec.map.return
                 spec.map.bind_inj_sf[OF inj_on_id] spec.map.cam.cl_inj_sf[OF inj_on_id])
apply (subst (1 2) spec.map.rel, force, force)
apply (simp add: spec.vmap.eq_return(2) spec.bind.bind
                 spec.bind.returnL spec.idle_le
           flip: spec.map.cam.cl_inj_sf[where af=id and sf=id and vf=vf and P="spec.amap af P",
                                        simplified spec.map.comp, simplified, folded id_def])
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap.interference"\<close>

lemma cl:
  fixes as :: "'b set"
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  fixes r :: "('b, 't) steps"
  fixes P :: "('b, 't, 'w) spec"
  shows "spec.invmap af sf vf (spec.interference.cl r P)
       = spec.interference.cl (map_prod af (map_prod sf sf) -` (r \<union> UNIV \<times> Id)) (spec.invmap af sf vf P)"
apply (simp add: spec.interference.cl_def map_prod_vimage_Times spec.rel.wind_bind_trailing
                 spec.invmap.bind spec.invmap.cam.cl spec.invmap.rel spec.invmap.return
           flip: spec.bind.bind)
apply (subst (2) spec.invmap.split_vinvmap)
apply (simp add: spec.cam.cl.bind spec.cam.cl.return spec.cam.cl.Sup spec.term.none.cam.cl_rel_wind
                 spec.bind.mono spec.bind.bind spec.bind.SupL spec.bind.supL
                 spec.bind.SUPR spec.bind.supR spec.bind.returnL spec.idle_le spec.bind.botR
                 image_image sup.absorb1)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference.closed"\<close>

lemma antimonotone:
  shows "antimono spec.interference.closed"
proof(rule antimonoI)
  show "spec.interference.closed r' \<subseteq> spec.interference.closed r" if "r \<subseteq> r'" for r r' :: "('a, 's) steps"
    unfolding spec.interference.closed_def by (strengthen ord_to_strengthen(2)[OF \<open>r \<subseteq> r'\<close>]) simp
qed

lemmas strengthen[strg] = st_ord_antimono[OF spec.interference.closed.antimonotone]
lemmas antimono = antimonoD[OF spec.interference.closed.antimonotone]

lemma Sup':
  assumes "X \<subseteq> spec.interference.closed r"
  shows "\<Squnion>X \<squnion> spec.term.none (spec.rel r :: (_, _, unit) spec) \<in> spec.interference.closed r"
by (metis assms spec.interference.cl.bot spec.interference.closed_Sup)

lemma Sup_not_empty:
  assumes "X \<subseteq> spec.interference.closed r"
  assumes "X \<noteq> {}"
  shows "\<Squnion>X \<in> spec.interference.closed r"
using spec.interference.closed_Sup[OF assms(1)] assms
by (simp add: assms spec.interference.closed_Sup[OF assms(1)] less_eq_Sup spec.interference.least
              subsetD sup.absorb1)

lemma rel:
  assumes "r' \<subseteq> r"
  shows "spec.rel r \<in> spec.interference.closed r'"
by (metis assms spec.eq_iff inf.absorb_iff2 spec.interference.cl.inf_rel(2) spec.interference.closed_clI)

lemma bind_relL:
  fixes P :: "('a, 's, 'v) spec"
  assumes "P \<in> spec.interference.closed r"
  shows "spec.rel r \<bind> (\<lambda>_::unit. P) = P"
by (subst (1 2) spec.interference.closed_conv[OF assms])
   (simp add: spec.interference.cl_def spec.rel.wind_bind flip: spec.bind.bind)

lemma bind_relR:
  assumes "P \<in> spec.interference.closed r"
  shows "P \<bind> (\<lambda>v. spec.rel r \<bind> (\<lambda>_::unit. Q v)) = P \<bind> Q"
by (subst (1 2) spec.interference.closed_conv[OF assms])
   (simp add: spec.interference.cl_def spec.bind.bind spec.bind.return;
    simp add: spec.rel.wind_bind flip: spec.bind.bind)

lemma bind_rel_unitR:
  assumes "P \<in> spec.interference.closed r"
  shows "P \<then> (spec.rel r :: (_, _, unit) spec) = P"
by (subst (1 2) spec.interference.closed_conv[OF assms])
   (simp add: spec.interference.cl_def spec.bind.bind spec.rel.wind_bind)

lemma bind_rel_botR:
  assumes "P \<in> spec.interference.closed r"
  shows "P \<bind> (\<lambda>v. spec.rel r \<bind> (\<lambda>_::unit. \<bottom>)) = P \<bind> \<bottom>"
by (subst (1 2) spec.interference.closed_conv[OF assms])
   (simp add: spec.interference.cl_def spec.bind.bind spec.bind.return;
    simp add: spec.rel.wind_bind flip: spec.bind.bind)

lemma bind[intro]:
  fixes f :: "('a, 's, 'v) spec"
  fixes g :: "'v \<Rightarrow> ('a, 's, 'w) spec"
  assumes "f \<in> spec.interference.closed r"
  assumes "\<And>x. g x \<in> spec.interference.closed r"
  shows "(f \<bind> g) \<in> spec.interference.closed r"
using assms by (simp add: spec.interference.closed_clI spec.interference.cl.bindL
                    flip: spec.interference.closed_conv)

lemma kleene_star:
  assumes "P \<in> spec.interference.closed r"
  assumes "spec.return () \<le> P"
  shows "spec.kleene.star P \<in> spec.interference.closed r"
proof(rule spec.interference.closed_clI,
      induct rule: spec.kleene.star.fixp_induct[where P="\<lambda>R. spec.interference.cl r (R P) \<le> spec.kleene.star P ", case_names adm bot step])
  case bot from \<open>P \<in> spec.interference.closed r\<close> show ?case
    by (simp add: order.trans[OF _ spec.kleene.expansive_star] spec.interference.cl.bot
                  spec.term.none.interference.closed.rel_le)
next
  case (step R) show ?case
    apply (simp add: spec.interference.cl_sup spec.interference.cl.bindL[OF assms(1)])
    apply (strengthen ord_to_strengthen(1)[OF step])
    apply (strengthen ord_to_strengthen(1)[OF \<open>spec.return () \<le> P\<close>])
    apply (simp add: spec.kleene.fold_starL spec.kleene.expansive_star
               flip: spec.interference.closed_conv[OF assms(1)])
    done
qed simp_all

lemma map_sf_id:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes vf :: "'v \<Rightarrow> 'w"
  assumes "P \<in> spec.interference.closed r"
  shows "spec.map af id vf P \<in> spec.interference.closed (map_prod af id ` r)"
by (rule spec.interference.closed_clI)
   (subst (2) spec.interference.closed_conv[OF assms];
    simp add: spec.map.interference.cl_sf_id map_prod_image_Times)

lemma invmap:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  assumes "P \<in> spec.interference.closed r"
  shows "spec.invmap af sf vf P \<in> spec.interference.closed (map_prod af (map_prod sf sf) -` r)"
by (rule spec.interference.closed_clI)
   (subst (2) spec.interference.closed_conv[OF assms];
    fastforce simp: spec.invmap.interference.cl intro: spec.interference.cl.mono)

setup \<open>Sign.mandatory_path "term"\<close>

lemma none:
  assumes "P \<in> spec.interference.closed r"
  shows "spec.term.none P \<in> spec.interference.closed r"
by (rule spec.interference.closed_clI)
   (subst (2) spec.interference.closed_conv[OF assms];
    simp add: spec.term.none.interference.cl)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> The \<^emph>\<open>'a agent\<close> datatype \<close>

text\<open>

For compositionality we often wish to designate a specific agent as the environment.

\<close>

datatype 'a agent = proc (the_agent: 'a) | env
type_synonym sequential = "unit agent" \<comment>\<open> Sequential programs (\S\ref{sec:programs}) \<close>
abbreviation self :: sequential where "self \<equiv> proc ()"

declare agent.map_id[simp]
declare agent.map_id0[simp]
declare agent.map_id0[unfolded id_def, simp]
declare agent.map_comp[unfolded comp_def, simp]

lemma env_not_in_range_proc[iff]:
  shows "env \<notin> range proc"
by fastforce

lemma range_proc_conv[simp]:
  shows "x \<in> range proc \<longleftrightarrow> x \<noteq> env"
by (cases x) simp_all

lemma inj_proc[iff]:
  shows "inj proc"
by (simp add: inj_def)

lemma surj_the_inv_proc[iff]:
  shows "surj (the_inv proc)"
by (meson inj_proc surjI the_inv_f_f)

lemma the_inv_proc[simp]:
  shows "the_inv proc (proc a) = a"
by (simp add: the_inv_f_f)

lemma uminus_env_range_proc[simp]:
  shows "-{env} = range proc"
by (auto intro: agent.exhaust)

lemma env_range_proc_UNIV[simp]:
  shows "insert env (range proc) = UNIV"
by (auto intro: agent.exhaust)

setup \<open>Sign.mandatory_path "sequential"\<close>

lemma not_conv[simp]:
  shows "a \<noteq> env \<longleftrightarrow> a = self"
    and "a \<noteq> self \<longleftrightarrow> a = env"
by (cases a; simp)+

lemma range_proc_self[simp]:
  shows "range proc = {self}"
by fastforce

lemma UNIV:
  shows "UNIV = {env, self}"
by fastforce

lemma rev_UNIV[simp]:
  shows "{env, self} = UNIV"
    and "{self, env} = UNIV"
by fastforce+

lemma uminus_self_env[simp]:
  shows "-{self} = {env}"
by fastforce

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "map_agent"\<close>

lemma eq_conv:
  shows "map_agent f x = env \<longleftrightarrow> x = env"
    and "env = map_agent f x \<longleftrightarrow> x = env"
    and "map_agent f x = proc a \<longleftrightarrow> (\<exists>a'. x = proc a' \<and> a = f a')"
    and "proc a = map_agent f x \<longleftrightarrow> (\<exists>a'. x = proc a' \<and> a = f a')"
by (cases x; auto)+

lemma surj:
  fixes \<pi> :: "'a \<Rightarrow> 'b"
  assumes "surj \<pi>"
  shows "surj (map_agent \<pi>)"
  by (metis assms surj_def agent.exhaust agent.map(1,2))

lemma bij:
  fixes \<pi> :: "'a \<Rightarrow> 'b"
  assumes "bij \<pi>"
  shows "bij (map_agent \<pi>)"
by (rule bijI[OF agent.inj_map[OF bij_is_inj[OF assms]] map_agent.surj[OF bij_is_surj[OF assms]]])

setup \<open>Sign.parent_path\<close>

definition swap_env_self_fn :: "sequential \<Rightarrow> sequential" where
  "swap_env_self_fn a = (case a of proc () \<Rightarrow> env | env \<Rightarrow> self)"

lemma swap_env_self_fn_simps:
  shows "swap_env_self_fn self = env"
        "swap_env_self_fn env = self"
unfolding swap_env_self_fn_def by simp_all

lemma bij_swap_env_self_fn:
  shows "bij swap_env_self_fn"
unfolding swap_env_self_fn_def bij_def inj_def surj_def by (auto split: agent.split)

lemma swap_env_self_fn_vimage_singleton:
  shows "swap_env_self_fn -` {env} = {self}"
    and "swap_env_self_fn -` {self} = {env}"
unfolding swap_env_self_fn_def by (auto split: agent.splits)

setup \<open>Sign.mandatory_path "spec"\<close>

abbreviation swap_env_self :: "(sequential, 's, 'v) spec \<Rightarrow> (sequential, 's, 'v) spec" where
  "swap_env_self \<equiv> spec.amap swap_env_self_fn"

setup \<open>Sign.parent_path\<close>


subsection\<open> Parallel composition\label{sec:constructions-parallel_composition} \<close>

text\<open>

We compose a collection of programs \<^typ>\<open>(sequential, 's, 'v) spec\<close> in parallel by mapping
these into the \<^typ>\<open>('a agent, 's, 'v) spec\<close> lattice, taking the infimum, and mapping back.

\<close>

definition toConcurrent_fn :: "'a \<Rightarrow> 'a \<Rightarrow> sequential" where
  "toConcurrent_fn = (\<lambda>a a'. if a' = a then self else env)"

definition toSequential_fn :: "'a agent \<Rightarrow> sequential" where
  "toSequential_fn = map_agent \<langle>()\<rangle>"

lemma toSequential_fn_alt_def:
  shows "toSequential_fn = (\<lambda>x. case x of proc x \<Rightarrow> self | env \<Rightarrow> env)"
by (simp add: toSequential_fn_def fun_eq_iff split: agent.split)

setup \<open>Sign.mandatory_path "spec"\<close>

abbreviation toConcurrent :: "'a \<Rightarrow> (sequential, 's, 'v) spec \<Rightarrow> ('a agent, 's, 'v) spec" where
  "toConcurrent a \<equiv> spec.ainvmap (toConcurrent_fn (proc a))"

abbreviation toSequential :: "('a agent, 's, 'v) spec \<Rightarrow> (sequential, 's, 'v) spec" where
  "toSequential \<equiv> spec.amap toSequential_fn"

definition Parallel :: "'a set \<Rightarrow> ('a \<Rightarrow> (sequential, 's, unit) spec) \<Rightarrow> (sequential, 's, unit) spec" where
  "Parallel as Ps = spec.toSequential (spec.rel (insert env (proc ` as) \<times> UNIV) \<sqinter> (\<Sqinter>a\<in>as. spec.toConcurrent a (Ps a)))"

definition parallel :: "(sequential, 's, unit) spec \<Rightarrow> (sequential, 's, unit) spec \<Rightarrow> (sequential, 's, unit) spec" where
  "parallel P Q = spec.Parallel UNIV (\<lambda>a::bool. if a then P else Q)"

adhoc_overloading
  Parallel spec.Parallel
adhoc_overloading
  parallel spec.parallel

lemma parallel_alt_def:
  shows "spec.parallel P Q = spec.toSequential (spec.toConcurrent True P \<sqinter> spec.toConcurrent False Q)"
by (simp add: spec.parallel_def spec.Parallel_def INF_UNIV_bool_expand spec.rel.UNIV)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "toConcurrent_fn"\<close>

lemma simps[simp]:
  shows "toConcurrent_fn (proc a) (proc a) = self"
    and "toConcurrent_fn (proc a) env = env"
    and "toConcurrent_fn a' a'' = self \<longleftrightarrow> a'' = a'"
    and "self = toConcurrent_fn a' a'' \<longleftrightarrow> a'' = a'"
    and "toConcurrent_fn a' a'' = env \<longleftrightarrow> a'' \<noteq> a'"
    and "env = toConcurrent_fn a' a'' \<longleftrightarrow> a'' \<noteq> a'"
    and "toConcurrent_fn (proc a) (map_agent \<langle>a\<rangle> x) = map_agent \<langle>()\<rangle> x"
by (auto simp: toConcurrent_fn_def map_agent.eq_conv intro: agent.exhaust)

lemma inj_map_agent:
  assumes "inj_on f (insert x (set_agent a))"
  shows "toConcurrent_fn (proc (f x)) (map_agent f a) = toConcurrent_fn (proc x) a"
by (cases a) (auto simp: toConcurrent_fn_def intro: inj_onD[OF assms])

lemma inv_into_map_agent:
  fixes f :: "'a \<Rightarrow> 'b"
  fixes a :: "'b agent"
  fixes x :: "'a"
  assumes "inj_on f as"
  assumes "x \<in> as"
  assumes "a \<in> insert env ((\<lambda>x. proc (f x)) ` as)"
  shows "toConcurrent_fn (proc x) (map_agent (inv_into as f) a) = toConcurrent_fn (proc (f x)) a"
using assms by (auto simp: toConcurrent_fn_def)

lemma vimage_sequential[simp]:
  shows "toConcurrent_fn (proc a) -` {self} = {proc a}"
    and "toConcurrent_fn (proc a) -` {env} = -{proc a}"
by (auto simp: toConcurrent_fn_def split: if_splits)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "toSequential_fn"\<close>

lemma simps[simp]:
  shows "toSequential_fn env = env"
    and "toSequential_fn (proc x) = self"
    and "toSequential_fn (map_agent f a) = toSequential_fn a"
    and "trace.map toSequential_fn id id \<sigma> = \<sigma>"
    and "trace.map toSequential_fn (\<lambda>x. x) (\<lambda>x. x) \<sigma> = \<sigma>"
    and "(\<lambda>x. if x = self then self else env) = id"
by (simp_all add: toSequential_fn_def fun_unit_id[where f="\<lambda>x. ()"] fun_eq_iff flip: id_def)

lemma eq_conv:
  shows "toSequential_fn x = env \<longleftrightarrow> x = env"
    and "toSequential_fn x = self \<longleftrightarrow> (\<exists>a. x = proc a)"
by (simp_all add: toSequential_fn_def map_agent.eq_conv)

lemma surj:
  shows "surj toSequential_fn"
proof -
  have "x \<in> range toSequential_fn" for x
    by (cases x)
       (simp_all add: toSequential_fn_def range_eqI[where x="proc undefined"] range_eqI[where x="env"])
  then show ?thesis by blast
qed

lemma image[simp]:
  assumes "as \<noteq> {}"
  shows "toSequential_fn ` proc ` as = {self}"
using assms by (auto simp: toSequential_fn_def image_image)

lemma vimage_sequential[simp]:
  shows "toSequential_fn -` {env} = {env}"
    and "toSequential_fn -` {self} = range proc"
by (auto simp: toSequential_fn_def map_agent.eq_conv)

setup \<open>Sign.parent_path\<close>

lemma toSequential_fn_eq_toConcurrent_fn_conv:
  shows "toSequential_fn a = toConcurrent_fn a' a'' \<longleftrightarrow> (case a of env \<Rightarrow> a'' \<noteq> a' | proc _ \<Rightarrow> a'' = a')"
    and "toConcurrent_fn a' a'' = toSequential_fn a \<longleftrightarrow> (case a of env \<Rightarrow> a'' \<noteq> a' | proc _ \<Rightarrow> a'' = a')"
by (simp_all split: agent.split)

setup \<open>Sign.mandatory_path "spec"\<close>

setup \<open>Sign.mandatory_path "toSequential"\<close>

lemma interference:
  shows "spec.toSequential (spec.rel ({env} \<times> r)) = spec.rel ({env} \<times> r)"
by (simp add: spec.map.rel map_prod_image_Times)

lemma interference_inf_toConcurrent:
  fixes a :: "'a"
  fixes P :: "(sequential, 's, 'v) spec"
  shows "spec.toSequential (spec.rel ({env, proc a} \<times> UNIV) \<sqinter> spec.toConcurrent a P) = P" (is "?lhs = ?rhs")
    and "spec.toSequential (spec.toConcurrent a P \<sqinter> spec.rel ({env, proc a} \<times> UNIV)) = P" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(rule spec.singleton.antisym)
    have *: "trace.natural' s (map (map_prod toSequential_fn id) xs)
           = trace.natural' s (map (map_prod (toConcurrent_fn (proc a)) id) xs)"
         if "trace.steps' s xs \<subseteq> {env, proc a} \<times> UNIV"
        for s and xs :: "('a agent \<times> 's) list"
      using that by (induct xs arbitrary: s) auto
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
      using that
      by (force simp: spec.singleton.le_conv spec.singleton_le_conv trace.natural_def *
                elim: order.trans[rotated])
    show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
      using that
      by (clarsimp intro!: exI[where x="trace.map (map_agent \<langle>a\<rangle>) id id \<sigma>"]
                     simp: spec.singleton.le_conv trace.steps'.map map_agent.eq_conv
                           fun_unit_id[where f="\<lambda>_::unit. ()"]
                simp flip: id_def)
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "toConcurrent"\<close>

lemma interference:
  shows "spec.toConcurrent a (spec.rel ({env} \<times> UNIV)) = spec.rel ((- {proc a}) \<times> UNIV)"
by (simp add: spec.invmap.rel map_prod_vimage_Times spec.rel.reflcl)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma Parallel_le[spec.idle_le]:
  assumes "\<And>a. a \<in> as \<Longrightarrow> spec.idle \<le> Ps a"
  shows "spec.idle \<le> spec.Parallel as Ps"
apply (simp add: spec.Parallel_def)
apply (strengthen ord_to_strengthen(2)[OF assms], assumption)
apply (strengthen ord_to_strengthen(2)[OF spec.idle.invmap_le[OF order.refl]])
apply (simp add: le_INF_iff spec.idle_le)
done

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "Parallel"\<close>

lemma cong:
  assumes "as = as'"
  assumes "\<And>a. a \<in> as' \<Longrightarrow> Ps a = Ps' a"
  shows "spec.Parallel as Ps = spec.Parallel as' Ps'"
unfolding spec.Parallel_def using assms by simp

lemma no_agents:
  shows "spec.Parallel {} Ps = spec.rel ({env} \<times> UNIV)"
by (simp add: spec.Parallel_def spec.toSequential.interference)

lemma singleton_agents:
  shows "spec.Parallel {a} Ps = Ps a"
by (simp add: spec.Parallel_def spec.toSequential.interference_inf_toConcurrent)

lemma bot:
  assumes "Ps a = \<bottom>"
  assumes "a \<in> as"
  shows "spec.Parallel as Ps = \<bottom>"
by (simp add: spec.Parallel_def assms INF_unwind_index[of a] spec.invmap.bot spec.map.bot)

lemma top:
  shows "spec.Parallel as \<top> = (if as = {} then spec.rel ({env} \<times> UNIV) else \<top>)"
proof -
  have "spec.toSequential (spec.rel (insert env (proc ` as) \<times> UNIV)) = \<top>" if "as \<noteq> {}"
    using that by (subst spec.map.rel, force, simp add: map_prod_image_Times flip: spec.rel.UNIV)
  then show ?thesis
    by (simp add: spec.Parallel.no_agents) (auto simp: spec.Parallel_def spec.invmap.top)
qed

lemma mono:
  assumes "\<And>a. a \<in> as \<Longrightarrow> Ps a \<le> Ps' a"
  shows "spec.Parallel as Ps \<le> spec.Parallel as Ps'"
unfolding spec.Parallel_def by (strengthen ord_to_strengthen(1)[OF assms(1)]; simp)

lemma strengthen[strg]:
  assumes "\<And>a. a \<in> as \<Longrightarrow> st_ord F (Ps a) (Ps' a)"
  shows "st_ord F (spec.Parallel as Ps) (spec.Parallel as Ps')"
using assms by (cases F) (auto simp: spec.Parallel.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  fixes Ps :: "'a \<Rightarrow> 'b \<Rightarrow> (sequential, 's, unit) spec"
  assumes "\<And>a. a \<in> as \<Longrightarrow> monotone orda (\<le>) (Ps a)"
  shows "monotone orda (\<le>) (\<lambda>x::'b. spec.Parallel as (\<lambda>a. Ps a x))"
using spec.Parallel.mono assms unfolding monotone_def by meson

(* Sup, mcont *)

lemma invmap: \<comment>\<open> \<open>af = id\<close> in \<open>spec.invmap\<close> \<close>
  shows "spec.invmap id sf vf (spec.Parallel UNIV Ps) = spec.Parallel UNIV (spec.invmap id sf vf \<circ> Ps)"
by (simp add: spec.Parallel_def image_image spec.invmap.inf spec.invmap.Inf spec.invmap.comp spec.rel.UNIV
        flip: spec.amap.surj_invmap[OF toSequential_fn.surj])

lemma discard_interference:
  assumes "\<And>a. a \<in> bs \<Longrightarrow> Ps a = spec.rel ({env} \<times> UNIV)"
  shows "spec.Parallel as Ps = spec.Parallel (as - bs) Ps"
proof -
  have *: "as = (as - bs) \<union> (as \<inter> bs)" by blast
  have **: "(insert env (proc ` as) \<inter> - proc ` (as \<inter> bs)) = insert env (proc ` (as - bs))" by blast
  from assms have ***: "(\<Sqinter>a\<in>as \<inter> bs. spec.toConcurrent a (Ps a))
                      = spec.rel ((- proc ` (as \<inter> bs)) \<times> UNIV)"
    by (force simp: assms spec.toConcurrent.interference le_Inf_iff
         simp flip: spec.rel.INF
             intro: spec.rel.mono antisym)
  show ?thesis
    apply (simp add: spec.Parallel_def)
    apply (subst (2) *)
    apply (simp add: image_Un Inf_union_distrib ac_simps ** *** Times_Int_Times
               flip: spec.rel.inf inf.assoc)
    done
qed

lemma rename_UNIV_aux:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "inj_on f as"
  shows "spec.toSequential (spec.rel (insert env (proc ` as) \<times> UNIV)
           \<sqinter> (\<Sqinter>a\<in>as. spec.toConcurrent a (Ps a)))
       = spec.toSequential (spec.rel (insert env (proc ` f ` as) \<times> UNIV)
           \<sqinter> (\<Sqinter>a\<in>as. spec.toConcurrent (f a) (Ps a)))" (is "?lhs = ?rhs")
proof(rule spec.singleton.antisym)
  show "\<lblot>\<sigma>\<rblot> \<le> ?rhs" if "\<lblot>\<sigma>\<rblot> \<le> ?lhs" for \<sigma>
    using that assms
    apply (clarsimp simp: spec.singleton.le_conv le_Inf_iff)
    apply (rule exI[where x="trace.map (map_agent f) id id \<sigma>" for \<sigma>])
    apply (intro conjI)
      apply (fastforce simp: trace.steps'.map)
     apply (fastforce intro: ord_eq_le_trans[OF spec.singleton.map_cong[OF toConcurrent_fn.inj_map_agent refl refl refl]]
                       dest: inj_onD trace.steps'.asetD
                  simp flip: id_def)
    apply (fastforce simp flip: id_def)
    done
  show "\<lblot>\<sigma>\<rblot> \<le> ?lhs" if "\<lblot>\<sigma>\<rblot> \<le> ?rhs" for \<sigma>
    using that assms
    apply (clarsimp simp: spec.singleton.le_conv le_Inf_iff image_image)
    apply (rule exI[where x="trace.map (map_agent (inv_into as f)) id id \<sigma>" for \<sigma>])
    apply (auto 4 2 dest: trace.steps'.asetD
                simp: spec.singleton.map_cong[OF toConcurrent_fn.inv_into_map_agent refl refl refl]
                      comp_def trace.steps'.map
           simp flip: id_def)
    done
qed

lemma rename_UNIV: \<comment>\<open> expand the set of agents to \<open>UNIV\<close> \<close>
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "inj_on f as"
  shows "spec.Parallel as Ps
       = spec.Parallel (UNIV :: 'b set)
                       (\<lambda>b. if b \<in> f ` as then Ps (inv_into as f b) else spec.rel ({env} \<times> UNIV))"
(is "?lhs = spec.Parallel _ ?f")
proof -
  have *: "(\<Sqinter>x. spec.toConcurrent x (?f x))
         = spec.rel (insert env (proc ` f ` as) \<times> UNIV)
            \<sqinter> (\<Sqinter>x\<in>f ` as. spec.toConcurrent x (Ps (inv_into as f x)))"
  proof -
    have *: "(\<Inter>x\<in>- f ` as. (- {proc x}) \<times> UNIV) = insert env (proc ` f ` as) \<times> UNIV"
      by (auto intro: agent.exhaust)
    have "(\<Sqinter>x. spec.toConcurrent x (?f x))
        = (\<Sqinter>x\<in>f ` as. spec.toConcurrent x (?f x)) \<sqinter> (\<Sqinter>x\<in>-f ` as. spec.toConcurrent x (?f x))"
      by (subst INF_union[symmetric]) simp
    also have "\<dots> = spec.rel (insert env (proc ` f ` as) \<times> UNIV)
                    \<sqinter> (\<Sqinter>x\<in>f ` as. spec.toConcurrent x (Ps (inv_into as f x)))"
      by (simp add: ac_simps spec.invmap.rel map_prod_vimage_Times spec.rel.reflcl *
              flip: spec.rel.upper_INF)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp add: spec.Parallel_def * inv_into_f_f[OF assms] spec.rel.UNIV
                  INF_rename_bij[OF inj_on_imp_bij_betw[OF assms],
                             where F="\<lambda>_ x. spec.toConcurrent x (Ps (inv_into as f x))"]
                  spec.Parallel.rename_UNIV_aux[OF assms])
qed

lemma rename:
  fixes \<pi> :: "'a \<Rightarrow> 'b"
  fixes Ps :: "'b \<Rightarrow> (sequential, 's, unit) spec"
  assumes "bij_betw \<pi> as bs"
  shows "spec.Parallel as (Ps \<circ> \<pi>) = spec.Parallel bs Ps"
proof -
  define \<pi>' where "\<pi>' = (\<lambda>x::'a+'b. case x of
                  Inl a \<Rightarrow> if a \<in> as then Inr (\<pi> a) else Inl a
                | Inr b \<Rightarrow> if b \<in> bs then Inl (inv_into as \<pi> b) else Inr b)"
  from assms have "inj \<pi>'"
    by (force intro: injI
               simp: \<pi>'_def bij_betw_apply bij_betw_imp_surj_on inv_into_into
              split: sum.split_asm if_split_asm
               dest: bij_betw_inv_into_left[rotated] bij_betw_inv_into_right[rotated])
  have simps: "\<And>a. \<pi>' (Inl a) = (if a \<in> as then Inr (\<pi> a) else Inl a)"
              "\<And>b. \<pi>' (Inr b) = (if b \<in> bs then Inl (inv_into as \<pi> b) else Inr b)"
    by (simp_all add: \<pi>'_def)
  have inv_simps: "\<And>a. a \<in> as \<Longrightarrow> inv \<pi>' (Inl a) = Inr (\<pi> a)"
    by (simp add: inv_f_eq[OF \<open>inj \<pi>'\<close>] bij_betw_inv_into_left[OF assms] bij_betw_apply[OF assms] simps(2))
  show ?thesis
    apply (simp add: spec.Parallel.rename_UNIV[where as=as and f="Inl :: 'a \<Rightarrow> 'a + 'b"]
                     spec.Parallel.rename_UNIV[where as=bs and f="Inr :: 'b \<Rightarrow> 'a + 'b"] comp_def)
    apply (subst (2) spec.Parallel.rename_UNIV[where as=UNIV, OF \<open>inj \<pi>'\<close>])
    apply (fastforce intro: arg_cong[where f="spec.Parallel UNIV"]
                      simp: fun_eq_iff split_sum_all image_iff simps inv_simps
                      inv_f_f[OF \<open>inj \<pi>'\<close>]  bij_betw_apply[OF bij_betw_inv_into[OF assms]]
                      bij_betw_apply[OF assms] bij_betw_inv_into_left[OF assms])
    done
qed

lemma rename_cong:
  fixes \<pi> :: "'a \<Rightarrow> 'b"
  fixes Ps :: "'a \<Rightarrow> (_, _, _) spec"
  fixes Ps' :: "'b \<Rightarrow> (_, _, _) spec"
  assumes "bij_betw \<pi> as bs"
  assumes "\<And>a. a \<in> as \<Longrightarrow> Ps a = Ps' (\<pi> a)"
  shows "spec.Parallel as Ps = spec.Parallel bs Ps'"
by (simp add: assms(2) flip: spec.Parallel.rename[OF assms(1)] cong: spec.Parallel.cong)

lemma inf_pre:
  assumes "as \<noteq> {}"
  shows "spec.Parallel as Ps \<sqinter> spec.pre P = (\<Parallel>i\<in>as. Ps i \<sqinter> spec.pre P)" (is ?thesis1)
    and "spec.pre P \<sqinter> spec.Parallel as Ps = (\<Parallel>i\<in>as. spec.pre P \<sqinter> Ps i)" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: spec.Parallel_def assms spec.invmap.inf spec.invmap.pre spec.map.inf_distr
                  inf.assoc INF_inf_const2)
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma inf_post:
  assumes "as \<noteq> {}"
  shows "spec.Parallel as Ps \<sqinter> spec.post Q = spec.Parallel as (\<lambda>i. Ps i \<sqinter> spec.post Q)" (is ?thesis1)
    and "spec.post Q \<sqinter> spec.Parallel as Ps = spec.Parallel as (\<lambda>i. spec.post Q \<sqinter> Ps i)" (is ?thesis2)
proof -
  show ?thesis1
    by (simp add: spec.Parallel_def assms spec.invmap.inf spec.invmap.post spec.map.inf_distr
                  inf.assoc INF_inf_const2)
  then show ?thesis2
    by (simp add: ac_simps)
qed

lemma unwind:
    \<comment>\<open> All other processes begin with interference \<close>
  assumes b: "\<And>b. b \<in> as - {a} \<Longrightarrow> spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. Ps b) \<le> Ps b"
  assumes a: "f \<bind> g \<le> Ps a" \<comment>\<open> The selected process starts with \<open>f\<close> \<close>
  assumes "a \<in> as"
  shows "f \<bind> (\<lambda>v. spec.Parallel as (Ps(a := g v))) \<le> spec.Parallel as Ps"
proof -
  have *: "spec.toConcurrent a f \<sqinter> spec.rel (\<Inter>x\<in>as - {a}. (- {proc x}) \<times> UNIV)
            \<bind> (\<lambda>v. \<Sqinter>b\<in>as. spec.toConcurrent b ((Ps(a:=g v)) b))
        \<le> (\<Sqinter>a\<in>as. spec.toConcurrent a (Ps a))" (is "?lhs \<le> ?rhs")
  proof -
    from \<open>a \<in> as\<close>
    have "?lhs = spec.toConcurrent a f \<sqinter> spec.rel (\<Inter>x\<in>as - {a}. (- {proc x}) \<times> UNIV)
                    \<bind> (\<lambda>v. spec.toConcurrent a (g v) \<sqinter> (\<Sqinter>b\<in>as - {a}. spec.toConcurrent b (Ps b)))"
      by (simp add: INF_unwind_index)
    also have "\<dots> \<le> (spec.toConcurrent a f \<bind> (\<lambda>x. spec.toConcurrent a (g x)))
                        \<sqinter> (spec.rel (\<Inter>x\<in>as - {a}. (- {proc x}) \<times> UNIV)
                             \<bind> (\<lambda>_::unit. \<Sqinter>b\<in>as - {a}. spec.toConcurrent b (Ps b)))"
      by (strengthen ord_to_strengthen(2)[OF spec.bind.inf_rel_distr_le]) simp
    also have "\<dots> = (spec.toConcurrent a f \<bind> (\<lambda>x. spec.toConcurrent a (g x)))
                        \<sqinter> ((\<Sqinter>b\<in>as - {a}. spec.toConcurrent b (spec.rel ({env} \<times> UNIV)))
                             \<bind> (\<lambda>_::unit. \<Sqinter>b\<in>as - {a}. spec.toConcurrent b (Ps b)))"
      by (simp add: spec.invmap.rel map_prod_vimage_Times spec.rel.reflcl flip: spec.rel.INF)
    also have "\<dots> \<le> (spec.toConcurrent a f \<bind> (\<lambda>x. spec.toConcurrent a (g x)))
                        \<sqinter> (\<Sqinter>b\<in>as - {a}. spec.toConcurrent b (spec.rel ({env} \<times> UNIV))
                             \<bind> (\<lambda>_::unit. spec.toConcurrent b (Ps b)))"
      by (strengthen ord_to_strengthen(2)[OF spec.bind.Inf_le]) simp
    also have "\<dots> = spec.toConcurrent a (f \<bind> g)
                        \<sqinter> (\<Sqinter>b\<in>as - {a}. spec.toConcurrent b (spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. Ps b)))"
      by (simp add: spec.invmap.bind)
    also have "\<dots> \<le> spec.toConcurrent a (Ps a) \<sqinter> (\<Sqinter>b\<in>as - {a}. spec.toConcurrent b (Ps b))"
      by (strengthen ord_to_strengthen(2)[OF a], strengthen ord_to_strengthen(2)[OF b], assumption, rule order.refl)
    also from \<open>a \<in> as\<close> have "\<dots> = ?rhs" by (simp add: INF_unwind_index)
    finally show ?thesis .
  qed
  from \<open>a \<in> as\<close>
  have **: "(insert env (proc ` as) \<times> UNIV \<inter> (\<Inter>x\<in>as - {a}. (- {proc x}) \<times> UNIV)) = {env, proc a} \<times> UNIV"
    by blast
  show ?thesis
    unfolding spec.Parallel_def
    by (strengthen ord_to_strengthen(2)[OF *])
       (simp add: ac_simps spec.bind.inf_rel spec.map.bind_inj_sf **
                  spec.toSequential.interference_inf_toConcurrent
            flip: spec.rel.inf)
qed

lemma inf_rel:
  fixes as :: "'a set"
  fixes r :: "'s rel"
  shows "spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> spec.Parallel as Ps
       = spec.Parallel as (\<lambda>a. spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> Ps a)" (is "?lhs = ?rhs")
    and "spec.Parallel as Ps \<sqinter> spec.rel ({env} \<times> UNIV \<union> {self} \<times> r)
       = spec.Parallel as (\<lambda>a. Ps a \<sqinter> spec.rel ({env} \<times> UNIV \<union> {self} \<times> r))" (is ?thesis1)
proof -
  show "?lhs = ?rhs"
  proof(cases "as = {}")
    case True then show ?thesis
      by (simp add: spec.Parallel.no_agents flip: spec.rel.inf)
  next
    case False show ?thesis
  proof(rule antisym)
    have *: "insert env (proc ` as) \<times> UNIV \<inter> map_prod toSequential_fn id -` (UNIV \<times> Id \<union> ({env} \<times> UNIV \<union> {self} \<times> r))
          \<subseteq> insert env (proc ` as) \<times> UNIV \<inter> map_prod (toConcurrent_fn (proc a)) id -` (UNIV \<times> Id \<union> (({env} \<times> UNIV) \<union> {self} \<times> r))" for a
      by auto
    from False
    show "?lhs \<le> ?rhs"
      apply (simp add: spec.Parallel_def ac_simps spec.map.inf_rel
                 flip: spec.rel.inf spec.invmap.inf_rel INF_inf_const1 INF_inf_const2
                  del: vimage_Un)
      apply (strengthen ord_to_strengthen(1)[OF *])
      apply (rule order.refl)
      done
    have "spec.toSequential (\<Sqinter>x\<in>as. spec.toConcurrent x (Ps x) \<sqinter> spec.rel (insert env (proc ` as) \<times> UNIV \<inter> map_prod (toConcurrent_fn (proc x)) id -` (UNIV \<times> Id \<union> ({env} \<times> UNIV \<union> {self} \<times> r))))
       \<le> spec.toSequential (\<Sqinter>x\<in>as. spec.toConcurrent x (Ps x) \<sqinter> spec.rel (insert env (proc ` as) \<times> UNIV \<inter> map_prod toSequential_fn id -` (UNIV \<times> Id \<union> ({env} \<times> UNIV \<union> {self} \<times> r))))"
      apply (rule spec.singleton_le_extI)
      apply (clarsimp simp: spec.singleton.le_conv le_INF_iff)
      apply (rename_tac \<sigma> \<sigma>')
      apply (rule_tac x=\<sigma>' in exI)
      apply (clarsimp simp: toConcurrent_fn_def toSequential_fn_def trace.split_all)
      apply (rename_tac \<sigma> \<sigma>' a s s' a')
      apply (case_tac a)
       apply (case_tac "the_agent a \<in> as"; force)
      apply simp
      done
    with False
    show "?rhs \<le> ?lhs"
      by (simp add: spec.Parallel_def ac_simps spec.map.inf_rel
           flip: INF_inf_const1 INF_inf_const2 spec.invmap.inf_rel spec.rel.inf)
    qed
  qed
  then show ?thesis1
    by (simp add: ac_simps)
qed

lemma flatten:
  fixes as :: "'a set"
  fixes a :: "'a"
  fixes bs :: "'b set"
  fixes Ps :: "'a \<Rightarrow> (sequential, 's, unit) spec"
  fixes Ps' :: "'b \<Rightarrow> (sequential, 's, unit) spec"
  assumes "Ps a = spec.Parallel bs Ps'"
  assumes "a \<in> as"
  shows "spec.Parallel as Ps = spec.Parallel ((as - {a}) <+> bs) (case_sum Ps Ps')" (is "?lhs = ?rhs")
proof(rule spec.singleton.antisym)
  have simps:
    "\<And>a'. a' \<noteq> a \<Longrightarrow> (\<lambda>x::('a + 'b) agent. toConcurrent_fn (proc a') (case x of proc (Inl a) \<Rightarrow> proc a | proc (Inr _) \<Rightarrow> proc a | env \<Rightarrow> env)) = toConcurrent_fn (proc (Inl a'))"
    "\<And>a'.            (\<lambda>x::('a + 'b) agent. toConcurrent_fn (proc a') (case x of proc (Inl _) \<Rightarrow> env | proc (Inr a) \<Rightarrow> proc a | env \<Rightarrow> env)) = toConcurrent_fn (proc (Inr a'))"
    by (auto simp: fun_eq_iff toConcurrent_fn_def split: agent.split sum.split)
  have *:
    "\<exists>\<sigma>''' :: (('a + 'b) agent, 's, unit) trace.t.
          \<lblot>\<sigma>'\<rblot> = \<lblot>trace.map (case_agent (case_sum proc \<langle>proc a\<rangle>) env) id id \<sigma>'''\<rblot>
        \<and> \<lblot>trace.map (case_agent (case_sum \<langle>env\<rangle> proc) env) id id \<sigma>'''\<rblot> \<le> \<lblot>\<sigma>''\<rblot>
        \<and> proc (Inl a) \<notin> trace.aset (\<natural>\<sigma>''')"
      if "\<lblot>trace.map (toConcurrent_fn (proc a)) id id \<sigma>'\<rblot> \<le> \<lblot>trace.map toSequential_fn id id \<sigma>''\<rblot>"
     for \<sigma>'  :: "('a agent, 's, unit) trace.t"
     and \<sigma>'' :: "('b agent, 's, unit) trace.t"
  proof(cases "trace.term \<sigma>'")
    case None
    have "\<exists>zs :: (('a + 'b) agent \<times> 's) list.
               xs = map (map_prod (case_agent (case_sum proc (\<lambda>s. proc a)) env) id) zs
             \<and> prefix (map (map_prod (case_agent (case_sum (\<lambda>s. env) proc) env) id) zs) ys
             \<and> (proc (Inl a) \<notin> fst ` set zs)" (is "\<exists>zs. ?goal xs zs")
      if "prefix (map (map_prod (toConcurrent_fn (proc a)) id) xs) (map (map_prod toSequential_fn id) ys)"
     for xs :: "('a agent \<times> 's) list" and ys :: "('b agent \<times> 's) list"
      using that
    proof(induct xs rule: rev_induct)
      case (snoc x xs)
      then obtain zs where "?goal xs zs" by (auto dest: append_prefixD)
      with snoc.prems show ?case
        apply (clarsimp simp: map_prod.comp map_prod_conv simp flip: id_def elim!: prefixE)
        subgoal for a\<^sub>y
          by (rule exI[where x="zs @ [(if fst x = proc a then map_agent Inr a\<^sub>y else map_agent Inl (fst x), (snd x))]"])
             (auto simp: toSequential_fn.eq_conv map_agent.eq_conv simp flip: all_simps split: agent.split)
        done
    qed simp
    from this[of "(trace.natural' (trace.init \<sigma>') (trace.rest \<sigma>'))"
                 "trace.natural' (trace.init \<sigma>') (trace.rest \<sigma>'')"] that None
    show ?thesis
      apply (simp add: spec.singleton_le_conv trace.natural.map_inj_on_sf)
      apply (clarsimp simp: trace.natural_def trace.aset.simps trace.split_Ex image_iff trace.less_eq_None)
      subgoal for zs
        by (clarsimp dest!: trace.natural'.amap_noop intro!: exI[where x=zs])
      done
  next
    case (Some v)
    have *: "\<exists>zs :: (('a + 'b) agent \<times> 's) list.
               xs = map (map_prod (case_agent (case_sum proc (\<lambda>s. proc a)) env) id) zs
             \<and> ys = map (map_prod (case_agent (case_sum (\<lambda>s. env) proc) env) id) zs
             \<and> (proc (Inl a) \<notin> fst ` set zs)"
      if "map (map_prod (toConcurrent_fn (proc a)) id) xs = map (map_prod toSequential_fn id) ys"
     for xs :: "('a agent \<times> 's) list" and ys :: "('b agent \<times> 's) list"
    proof -
      from that have "length xs = length ys"
        using map_eq_imp_length_eq by blast
      from this that show ?thesis
      proof(induct rule: list_induct2)
        case (Cons x xs y ys) then show ?case
          by (cases x, cases y, cases "fst x")
             (auto 8 0 simp: Cons_eq_map_conv comp_def toSequential_fn_eq_toConcurrent_fn_conv
                  simp flip: id_def ex_simps
                      split: if_splits agent.splits sum.split)
      qed simp
    qed
    from that Some
         *[where xs="trace.natural' (trace.init \<sigma>') (trace.rest \<sigma>')"
             and ys="trace.natural' (trace.init \<sigma>') (trace.rest \<sigma>'')"]
    show ?thesis
      apply (simp add: spec.singleton_le_conv trace.natural.map_inj_on_sf)
      apply (clarsimp simp: trace.natural_def)
      subgoal for zs
        by (clarsimp simp: trace.split_Ex trace.aset.simps
                    dest!: trace.natural'.amap_noop
                   intro!: exI[where x=zs])
      done
  qed
  {
    fix \<sigma>
    assume "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    then obtain \<sigma>\<^sub>a \<sigma>\<^sub>b \<sigma>\<^sub>c
      where 1: "trace.steps' (trace.init \<sigma>\<^sub>a) (trace.rest \<sigma>\<^sub>a) \<subseteq> insert env (proc ` as) \<times> UNIV"
        and 2: "\<forall>x\<in>as. \<lblot>trace.map (toConcurrent_fn (proc x)) id id \<sigma>\<^sub>a\<rblot> \<le> Ps x"
        and 3: "\<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map toSequential_fn id id \<sigma>\<^sub>a\<rblot>"
        and 4: "trace.steps' (trace.init \<sigma>\<^sub>b) (trace.rest \<sigma>\<^sub>b) \<subseteq> insert env (proc ` bs) \<times> UNIV"
        and 5: "\<forall>x\<in>bs. \<lblot>trace.map (toConcurrent_fn (proc x)) id id \<sigma>\<^sub>b\<rblot> \<le> Ps' x"
        and 6: "\<sigma>\<^sub>a \<simeq>\<^sub>S trace.map (case_agent (case_sum proc \<langle>proc a\<rangle>) env) id id \<sigma>\<^sub>c"
        and 7: "\<lblot>trace.map (case_agent (case_sum \<langle>env\<rangle> proc) env) id id \<sigma>\<^sub>c\<rblot> \<le> \<lblot>\<sigma>\<^sub>b\<rblot>"
        and 8: "proc (Inl a) \<notin> trace.aset (\<natural>\<sigma>\<^sub>c)"
      apply (clarsimp simp: spec.Parallel_def spec.singleton.le_conv le_Inf_iff)
      apply (frule bspec[OF _ \<open>a \<in> as\<close>])
      apply (clarsimp simp: assms(1) spec.Parallel_def spec.singleton.le_conv le_Inf_iff dest!: *)
      done
    show "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
      unfolding spec.Parallel_def spec.singleton.le_conv inf.bounded_iff le_Inf_iff ball_simps
    proof(intro exI[where x=\<sigma>\<^sub>c] conjI ballI)
      show "trace.steps' (trace.init \<sigma>\<^sub>c) (trace.rest \<sigma>\<^sub>c)
         \<subseteq> insert env (proc ` ((as - {a}) <+> bs)) \<times> UNIV" (is "?lhs \<subseteq> ?rhs")
      proof(rule subsetI, unfold split_paired_all)
        show "(x, s, s') \<in> ?rhs" if "(x, s, s') \<in> ?lhs" for x s s'
        proof(cases x)
          case (proc y) then show ?thesis
          proof(cases y)
            case (Inl a)
            with that proc 1 arg_cong[OF 6, where f=trace.steps] 8
            show ?thesis
              by (fastforce simp: trace.steps'.natural' trace.steps'.map trace.aset.natural_conv)
          next
            case (Inr b)
            with that proc 4 spec.steps.mono[OF 7]
            show ?thesis
              by (fastforce simp: trace.steps'.natural' trace.steps'.map spec.steps.singleton)
          qed
        qed simp
      qed
      show "\<lblot>trace.map (toConcurrent_fn (proc x)) id id \<sigma>\<^sub>c\<rblot> \<le> (case x of Inl x \<Rightarrow> Ps x | Inr x \<Rightarrow> Ps' x)"
        if "x \<in> (as - {a}) <+> bs"
       for x
      proof(cases x)
        case (Inl l) with 2 6 that show ?thesis
          by (force dest: trace.stuttering.equiv.map[where af="toConcurrent_fn (proc l)" and sf=id and vf=id]
                    simp: sum_In_conv simps fun_unit_id[where f="\<lambda>_::unit. ()"]
               simp flip: id_def
                    cong: spec.singleton_cong)
      next
        case (Inr r) with 2 5 6 7 that show ?thesis
          by (fastforce dest: spec.singleton.map_le[where af="toConcurrent_fn (proc r)" and sf=id and vf=id]
                        simp: simps fun_unit_id[where f="\<lambda>_::unit. ()"]
                   simp flip: id_def
                        cong: spec.singleton_cong)
      qed
      from 3 6
      show "\<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map toSequential_fn id id \<sigma>\<^sub>c\<rblot>"
        by (fastforce dest: trace.stuttering.equiv.map[where af="toSequential_fn" and sf=id and vf=id]
                      simp: spec.singleton_le_conv id_def agent.case_distrib sum.case_distrib
                 simp flip: toSequential_fn_alt_def
                      cong: agent.case_cong sum.case_cong)
    qed
  }
  {
    fix \<sigma>
    assume "\<lblot>\<sigma>\<rblot> \<le> ?rhs"
    then obtain \<sigma>'
      where 1: "trace.steps' (trace.init \<sigma>') (trace.rest \<sigma>') \<subseteq> insert env (proc ` ((as - {a}) <+> bs)) \<times> UNIV"
        and 2: "\<forall>x\<in>(as - {a}) <+> bs. \<lblot>trace.map (toConcurrent_fn (proc x)) id id \<sigma>'\<rblot> \<le> (case x of Inl x \<Rightarrow> Ps x | Inr x \<Rightarrow> Ps' x)"
        and 3: "\<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map toSequential_fn id id \<sigma>'\<rblot>"
      by (clarsimp simp: spec.Parallel_def spec.singleton.le_conv le_Inf_iff)
    show "\<lblot>\<sigma>\<rblot> \<le> ?lhs"
    proof -
      from \<open>a \<in> as\<close> 1
      have "trace.steps' (trace.init \<sigma>') (map (map_prod (case_agent (case_sum proc \<langle>proc a\<rangle>) env) id) (trace.rest \<sigma>'))
         \<subseteq> insert env (proc ` as) \<times> UNIV"
        by (auto simp: trace.steps'.map)
      moreover
      have "\<lblot>trace.map (\<lambda>y. toConcurrent_fn (proc x) (case y of proc (Inl a) \<Rightarrow> proc a | proc (Inr b) \<Rightarrow> proc a | env \<Rightarrow> env)) id id \<sigma>'\<rblot> \<le> Ps x"
        if "x \<in> as"
       for x
      proof(cases "x = a")
        case True show ?thesis
        proof -
          from \<open>a \<in> as\<close> 1
          have "trace.steps' (trace.init \<sigma>') (map (map_prod (case_agent (case_sum \<langle>env\<rangle> proc) env) id) (trace.rest \<sigma>'))
             \<subseteq> insert env (proc ` bs) \<times> UNIV"
            by (auto simp: trace.steps'.map)
          moreover
          from 2
          have "\<lblot>trace.map (\<lambda>y. toConcurrent_fn (proc b) (case y of proc (Inl a) \<Rightarrow> env | proc (Inr b) \<Rightarrow> proc b | env \<Rightarrow> env)) id id \<sigma>'\<rblot> \<le> Ps' b"
            if "b \<in> bs"
           for b
            using that by (fastforce simp: simps dest: bspec[where x="Inr b"])
          moreover
          from 1
          have "\<lblot>trace.map (\<lambda>y. toConcurrent_fn (proc a) (case y of proc (Inl a) \<Rightarrow> proc a | proc (Inr b) \<Rightarrow> proc a | env \<Rightarrow> env)) id id \<sigma>'\<rblot>
             \<le> \<lblot>trace.map (\<lambda>y. toSequential_fn (case y of proc (Inl a) \<Rightarrow> env | proc (Inr b) \<Rightarrow> proc b | env \<Rightarrow> env)) id id \<sigma>'\<rblot>"
            by (subst spec.singleton.map_cong[where af'="\<lambda>y. toSequential_fn (case y of proc (Inl s) \<Rightarrow> env | proc (Inr b) \<Rightarrow> proc b | env \<Rightarrow> env)", OF _ refl refl refl];
                fastforce simp: trace.aset.natural_conv split: agent.split sum.split)
          ultimately show ?thesis
            apply (simp add: \<open>x = a\<close> assms(1) spec.Parallel_def spec.singleton.le_conv le_Inf_iff)
            apply (rule exI[where x="trace.map (case_agent (case_sum \<langle>env\<rangle> proc) env) id id \<sigma>'"])
            apply (intro conjI ballI)
            apply (simp_all add: fun_unit_id[where f="\<lambda>_::unit. ()"] flip: id_def)
            done
        qed
      next
        case False with 2 that show ?thesis
          by (fastforce simp: simps dest: bspec[where x="Inl x"])
      qed
      moreover
      from 3
      have "\<lblot>\<sigma>\<rblot> \<le> \<lblot>trace.map (\<lambda>x. toSequential_fn (case x of proc (Inl a) \<Rightarrow> proc a | proc (Inr b) \<Rightarrow> proc a | env \<Rightarrow> env)) id id \<sigma>'\<rblot>"
        by (simp add: agent.case_distrib sum.case_distrib
                flip: toSequential_fn_alt_def
                cong: agent.case_cong sum.case_cong)
      ultimately show ?thesis
        apply (simp add: spec.Parallel_def spec.singleton.le_conv le_Inf_iff)
        apply (rule exI[where x="trace.map (case_agent (case_sum proc \<langle>proc a\<rangle>) env) id id \<sigma>'"] conjI ballI)
        apply (simp add: fun_unit_id[where f="\<lambda>_::unit. ()"] flip: id_def)
        done
    qed
  }
qed

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term"\<close>

setup \<open>Sign.mandatory_path "none"\<close>

lemma Parallel_some_agents:
  assumes "\<And>a. a \<in> bs \<Longrightarrow> Ps a = spec.term.none (Ps' a)"
  assumes "as \<inter> bs \<noteq> {}"
  shows "spec.Parallel as Ps = spec.term.none (\<Parallel>a\<in>as. if a \<in> as \<inter> bs then Ps' a else Ps a)"
using assms(1)[symmetric] assms(2)
      INF_union[where A="as - bs" and B="as \<inter> bs"
                  and M="\<lambda>a. spec.toConcurrent a (if a \<in> bs then Ps' a else Ps a)"]
by (simp add: spec.Parallel_def Un_Diff_Int inf_assoc image_image
              spec.term.none.map spec.term.none.invmap spec.term.none.inf_unit(2) spec.term.none.Inf_not_empty
        flip: INF_union)

lemma Parallel_not_empty:
  assumes "as \<noteq> {}"
  shows "spec.term.none (Parallel as Ps) = Parallel as (spec.term.none \<circ> Ps)"
using assms spec.term.none.Parallel_some_agents[where as=as and bs=as and Ps="spec.term.none \<circ> Ps" and Ps'=Ps]
by (simp cong: spec.Parallel.cong)

lemma parallel:
  shows "spec.term.none (P \<parallel> Q) = spec.term.none P \<parallel> spec.term.none Q"
by (simp add: spec.parallel_def spec.term.none.Parallel_not_empty comp_def if_distrib)

lemma
  shows parallelL: "spec.term.none P \<parallel> Q = spec.term.none (P \<parallel> Q)"
    and parallelR: "P \<parallel> spec.term.none Q = spec.term.none (P \<parallel> Q)"
using
  spec.term.none.Parallel_some_agents[where
    as=UNIV and bs="{True}"
            and Ps="\<lambda>a. if a then spec.term.none P else Q" and Ps'="\<lambda>a. if a then P else Q"]
  spec.term.none.Parallel_some_agents[where
    as=UNIV and bs="{False}"
            and Ps="\<lambda>a. if a then P else spec.term.none Q" and Ps'="\<lambda>a. if a then P else Q"]
by (simp_all add: spec.parallel_def cong: if_cong)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "all"\<close>

lemma Parallel:
  shows "spec.term.all (spec.Parallel as Ps) = spec.Parallel as (spec.term.all \<circ> Ps)"
by (simp add: spec.Parallel_def image_image
              spec.term.all.Inf spec.term.all.inf spec.term.all.invmap spec.term.all.map spec.term.all.rel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "idle"\<close>

lemma parallel_le:
  assumes "spec.idle \<le> P"
  assumes "spec.idle \<le> Q"
  shows "spec.idle \<le> P \<parallel> Q"
by (simp add: assms spec.parallel_def spec.idle_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "invmap"\<close>

lemma parallel: \<comment>\<open> \<open>af = id\<close> in \<open>spec.invmap\<close> \<close>
  shows "spec.invmap id sf vf (spec.parallel P Q)
       = spec.parallel (spec.invmap id sf vf P) (spec.invmap id sf vf Q)"
by (simp add: spec.parallel_def spec.Parallel.invmap comp_def if_distrib)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "parallel"\<close>

lemma bot:
  shows botL: "spec.parallel \<bottom> P = \<bottom>"
    and botR: "spec.parallel P \<bottom> = \<bottom>"
by (simp_all add: spec.parallel_def spec.Parallel.bot[where a="False"] spec.Parallel.bot[where a="True"])

lemma commute:
  shows "spec.parallel P Q = spec.parallel Q P"
unfolding spec.parallel_def by (subst spec.Parallel.rename[symmetric, OF bij_Not]) (simp add: comp_def)

lemma mono:
  assumes "P \<le> P'"
  assumes "Q \<le> Q'"
  shows "spec.parallel P Q \<le> spec.parallel P' Q'"
by (simp add: assms spec.parallel_def spec.Parallel.mono)

lemma strengthen[strg]:
  assumes "st_ord F P P'"
  assumes "st_ord F Q Q'"
  shows "st_ord F (spec.parallel P Q) (spec.parallel P' Q')"
using assms by (cases F; simp add: spec.parallel.mono)

lemma mono2mono[cont_intro, partial_function_mono]:
  assumes "monotone orda (\<le>) F"
  assumes "monotone orda (\<le>) G"
  shows "monotone orda (\<le>) (\<lambda>f. spec.parallel (F f) (G f))"
using assms by (simp add: spec.parallel_def spec.Parallel.mono2mono)

lemma Sup:
  fixes Ps :: "(sequential, 's, unit) spec set"
  shows SupL: "\<Squnion>Ps \<parallel> Q = (\<Squnion>P\<in>Ps. P \<parallel> Q)"
    and SupR: "Q \<parallel> \<Squnion>Ps = (\<Squnion>P\<in>Ps. Q \<parallel> P)"
by (simp_all add: spec.parallel_alt_def spec.invmap.Sup spec.map.Sup heyting.inf_SUP_distrib image_image)

lemma sup:
  fixes P :: "(sequential, 's, unit) spec"
  shows supL: "(P \<squnion> Q) \<parallel> R = (P \<parallel> R) \<squnion> (Q \<parallel> R)"
    and supR: "P \<parallel> (Q \<squnion> R) = (P \<parallel> Q) \<squnion> (P \<parallel> R)"
using spec.parallel.Sup[where Ps="{P, Q}" for P Q, simplified] by fast+

text\<open>

We can residuate \<^const>\<open>spec.parallel\<close> but not \<open>prog.parallel\<close> (see \S\ref{sec:programs-language})
as the latter is not strict. Intuitively any realistic modelling of parallel composition will be
non-strict as the divergence of one process should not block the progress of others, and
incorporating such interference may preclude the implementation of a specification via this residuation.

References:
 \<^item> \<^citet>\<open>\<open>Law 23\<close> in "Hayes:2016"\<close>: residuate parallel
 \<^item> \<^citet>\<open>\<open>Lemma~6\<close> in "vanStaden:2015"\<close> who cites \<^citet>\<open>"ArmstrongGomesStruth:2014"\<close>

\<close>

definition res :: "(sequential, 's, unit) spec \<Rightarrow> (sequential, 's, unit) spec \<Rightarrow> (sequential, 's, unit) spec" where
  "res S i = \<Squnion>{P. P \<parallel> i \<le> S}"

interpretation res: galois.complete_lattice_class "\<lambda>S. spec.parallel S i" "\<lambda>S. spec.parallel.res S i" for i  \<comment>\<open> \<^citet>\<open>\<open>Law 23 (rely refinement)\<close> in "Hayes:2016"\<close> \<close>
proof
  have *: "spec.parallel.res S i \<parallel> i \<le> S" for S \<comment>\<open> \<^citet>\<open>\<open>Law 22 (rely quotient)\<close> in "Hayes:2016"\<close> \<close>
    by (simp add: spec.parallel.res_def spec.parallel.SupL)
  show "x \<parallel> i \<le> S \<longleftrightarrow> x \<le> spec.parallel.res S i" for x S
    by (fastforce simp: spec.parallel.res_def Sup_upper spec.parallel.mono intro: order.trans[OF _ *])
qed

lemma mcont2mcont[cont_intro]:
  assumes "mcont luba orda Sup (\<le>) P"
  assumes "mcont luba orda Sup (\<le>) Q"
  shows "mcont luba orda Sup (\<le>) (\<lambda>x. spec.parallel (P x) (Q x))"
proof(rule ccpo.mcont2mcont'[OF complete_lattice_ccpo _ _ assms(1)])
  show "mcont Sup (\<le>) Sup (\<le>) (\<lambda>y. spec.parallel y (Q x))" for x
    by (intro mcontI contI monotoneI) (simp_all add: spec.parallel.mono spec.parallel.SupL)
  show "mcont luba orda Sup (\<le>) (\<lambda>x. spec.parallel y (Q x))" for y
    by (simp add: mcontI monotoneI contI mcont_monoD[OF assms(2)] spec.parallel.mono mcont_contD[OF assms(2)] spec.parallel.SupR image_image)
qed

lemma inf_rel:
  shows "spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> (P \<parallel> Q)
      = (spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> P) \<parallel> (spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> Q)"
    and "(P \<parallel> Q) \<sqinter> spec.rel ({env} \<times> UNIV \<union> {self} \<times> r)
      = (spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> P) \<parallel> (spec.rel ({env} \<times> UNIV \<union> {self} \<times> r) \<sqinter> Q)"
by (simp_all add: ac_simps spec.parallel_def spec.Parallel.inf_rel if_distrib[where f="\<lambda>x. x \<sqinter> y" for y])

lemma assoc:
  shows "spec.parallel P (spec.parallel Q R) = spec.parallel (spec.parallel P Q) R" (is "?lhs = ?rhs")
by (auto simp: spec.parallel_def bij_betw_def Plus_def UNIV_bool
               spec.Parallel.flatten[where a=False] spec.Parallel.flatten[where a=True]
       intro!: spec.Parallel.rename_cong[where \<pi>="case_sum (\<lambda>a. if a then Inr True else undefined)
                                                           (\<lambda>a. if a then Inr False else Inl False)"])

lemma bind_botR:
  shows "spec.parallel (P \<bind> \<bottom>) Q  = spec.parallel P Q \<bind> \<bottom>"
    and "spec.parallel P (Q \<bind> \<bottom>)  = spec.parallel P Q \<bind> \<bottom>"
by (simp_all add: spec.bind.botR spec.term.none.parallelL spec.term.none.parallelR)

lemma interference:
  shows interferenceL: "spec.rel ({env} \<times> UNIV) \<parallel> c = c"
    and interferenceR: "c \<parallel> spec.rel ({env} \<times> UNIV) = c"
by (simp_all add: spec.parallel_def spec.Parallel.singleton_agents
  flip: spec.Parallel.rename_UNIV[where as="{False}" and f="id" and Ps="\<langle>c\<rangle>", simplified]
        spec.Parallel.rename_UNIV[where as="{True}" and f="id" and Ps="\<langle>c\<rangle>", simplified])

lemma unwindL:
  assumes "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. Q) \<le> Q" \<comment>\<open> All other processes begin with interference \<close>
  assumes "f \<bind> g \<le> P" \<comment>\<open> The selected process starts with action \<open>f\<close> \<close>
  shows "f \<bind> (\<lambda>v. g v \<parallel> Q) \<le> P \<parallel> Q"
unfolding spec.parallel_def
by (strengthen ord_to_strengthen[OF spec.Parallel.unwind[where a=True]])
   (auto simp: spec.Parallel.mono spec.bind.mono intro: assms)

lemma unwindR:
  assumes "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. P) \<le> P" \<comment>\<open> All other processes begin with interference \<close>
  assumes "f \<bind> g \<le> Q" \<comment>\<open> The selected process starts with action \<open>f\<close> \<close>
  shows "f \<bind> (\<lambda>v. P \<parallel> g v) \<le> P \<parallel> Q"
by (subst (1 2) spec.parallel.commute) (rule spec.parallel.unwindL[OF assms])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "interference.closed"\<close>

lemma toConcurrent_gen:
  fixes P :: "(sequential, 's, 'v) spec"
  fixes a :: "'a"
  assumes P: "P \<in> spec.interference.closed ({env} \<times> r)"
  shows "spec.toConcurrent a P \<in> spec.interference.closed ((-{proc a}) \<times> r)"
proof -
  have *: "map_prod (toConcurrent_fn (proc a)) id -` ({env} \<times> r) = (-{proc a}) \<times> r"
    by (force simp: toConcurrent_fn_def)
  show ?thesis
    apply (rule spec.interference.closed_clI)
    apply (subst (2) spec.interference.closed_conv[OF P])
    apply (force intro: spec.interference.cl.mono simp: * spec.invmap.interference.cl)
    done
qed

lemma toConcurrent:
  fixes P :: "(sequential, 's, 'v) spec"
  fixes a :: "'a"
  assumes P: "P \<in> spec.interference.closed ({env} \<times> r)"
  shows "spec.toConcurrent a P \<in> spec.interference.closed ({env} \<times> r)"
by (blast intro: subsetD[OF spec.interference.closed.antimono
                            spec.interference.closed.toConcurrent_gen[OF assms]])

lemma toSequential:
  fixes P :: "('a agent, 's, 'v) spec"
  assumes "P \<in> spec.interference.closed ({env} \<times> r)"
  shows "spec.toSequential P \<in> spec.interference.closed ({env} \<times> r)"
proof -
  have *: "map_prod toSequential_fn id ` ({env} \<times> r) = {env} \<times> r"
    by (force simp: toSequential_fn_def)
  show ?thesis
    apply (rule spec.interference.closed_clI)
    apply (subst (2) spec.interference.closed_conv[OF assms])
    apply (simp add: * spec.map.interference.cl_sf_id)
    done
qed

lemma Parallel:
  assumes "\<And>a. Ps a \<in> spec.interference.closed ({env} \<times> UNIV)"
  shows "spec.Parallel as Ps \<in> spec.interference.closed ({env} \<times> UNIV)"
unfolding spec.Parallel_def
by (fastforce intro: spec.interference.closed.rel spec.interference.closed_Inf spec.interference.closed.toSequential
               simp: assms image_subset_iff spec.interference.closed.toConcurrent)

lemma parallel:
  assumes "P \<in> spec.interference.closed ({env} \<times> UNIV)"
  assumes "Q \<in> spec.interference.closed ({env} \<times> UNIV)"
  shows "P \<parallel> Q \<in> spec.interference.closed ({env} \<times> UNIV)"
by (simp add: assms spec.parallel_def spec.interference.closed.Parallel)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>


subsection\<open> Specification Inhabitation\label{sec:inhabitation} \<close>

text\<open>

Given that \<open>\<bottom>\<close> satisfies any specification \<^term>\<open>S::('a, 's, 'v) spec\<close>, we may wish to show that
a specific trace \<open>\<sigma>\<close> is allowed by \<open>S\<close>.

The strategy is to compute the allowed transitions from a given
initial state and possibly a return value. We almost always discard the
closures we've added for various kinds of compositionality.

References:
 \<^item> Similar to how \<^citet>\<open>\<open>\S3.3\<close> in "vanStaden:2014"\<close> models a small-step operational semantics.
  \<^item> i.e., we can (semantically) define something like an LTS, which is compositional wrt parallel
  \<^item> a bit like a resumption or a residual
 \<^item> Similar to \<^citet>\<open>"HoareHeSampaio:2000"\<close>

TODO:
 \<^item> often want transitive variants of these rules
 \<^item> automate: only stop when there's a scheduling decision to be made

\<close>

definition inhabits :: "('a, 's, 'w) spec \<Rightarrow> 's \<Rightarrow> ('a \<times> 's) list \<Rightarrow> ('a, 's, 'w) spec \<Rightarrow> bool" (\<open>_/ -_, _\<rightarrow>/ _\<close> [50, 0, 0, 50] 50) where
  "S -s, xs\<rightarrow> T \<longleftrightarrow> \<lblot>s, xs, Some ()\<rblot> \<then> T \<le> S"

setup \<open>Sign.mandatory_path "inhabits"\<close>

lemma incomplete:
  assumes "S -s, xs\<rightarrow> S'"
  shows "\<lblot>s, xs, None\<rblot> \<le> S"
by (strengthen ord_to_strengthen[OF assms[unfolded inhabits_def]])
   (simp add: spec.bind.incompleteI)

lemma complete:
  assumes "S -s, xs\<rightarrow> spec.return v"
  shows "\<lblot>s, xs, Some v\<rblot> \<le> S"
by (strengthen ord_to_strengthen[OF assms[unfolded inhabits_def]])
   (simp add: spec.bind.continueI[where ys="[]", simplified] spec.singleton.le_conv)

lemmas I = inhabits.complete inhabits.incomplete

lemma mono:
  assumes "S \<le> S'"
  assumes "T' \<le> T"
  assumes "S -s, xs\<rightarrow> T"
  shows "S' -s, xs\<rightarrow> T'"
unfolding inhabits_def
apply (strengthen ord_to_strengthen[OF assms(1)])
apply (strengthen ord_to_strengthen[OF assms(2)])
apply (rule assms(3)[unfolded inhabits_def])
done

lemma strengthen[strg]:
  assumes "st_ord F S S'"
  assumes "st_ord (\<not>F) T T'"
  shows "st F (\<longrightarrow>) (S -s, xs\<rightarrow> T) (S' -s, xs\<rightarrow> T')"
using assms by (cases F; simp add: inhabits.mono)

lemma pre:
  assumes "S -s, xs'\<rightarrow> T"
  assumes "T' \<le> T"
  assumes "xs = xs'"
  shows "S -s, xs\<rightarrow> T'"
using assms by (blast intro: inhabits.mono[OF order.refl assms(2)])

lemma tau:
  assumes "spec.idle \<le> S"
  shows "S -s, []\<rightarrow> S"
unfolding inhabits_def
by (strengthen ord_to_strengthen[OF spec.action.stutterI[where F="{()} \<times> UNIV \<times> Id"]])
   (simp_all add: assms spec.bind.returnL flip: spec.return_def)

lemma trans:
  assumes "R -s, xs\<rightarrow> S"
  assumes "S -trace.final' s xs, ys\<rightarrow> T"
  shows "R -s, xs @ ys\<rightarrow> T"
unfolding inhabits_def
apply (strengthen ord_to_strengthen(2)[OF assms(1)[unfolded inhabits_def]])
apply (strengthen ord_to_strengthen(2)[OF assms(2)[unfolded inhabits_def]])
apply (simp add: spec.bind.continueI spec.bind.mono flip: spec.bind.bind)
done

lemma Sup:
  assumes "P -s, xs\<rightarrow> P'"
  assumes "P \<in> X"
  shows "\<Squnion>X -s, xs\<rightarrow> P'"
using assms by (simp add: inhabits_def Sup_upper2)

lemma supL:
  assumes "P -s, xs\<rightarrow> P'"
  shows "P \<squnion> Q -s, xs\<rightarrow> P'"
using assms by (simp add: inhabits_def le_supI1)

lemma supR:
  assumes "Q -s, xs\<rightarrow> Q'"
  shows "P \<squnion> Q -s, xs\<rightarrow> Q'"
using assms by (simp add: inhabits_def le_supI2)

lemma inf:
  assumes "P -s, xs\<rightarrow> P'"
  assumes "Q -s, xs\<rightarrow> Q'"
  shows "P \<sqinter> Q -s, xs\<rightarrow> P' \<sqinter> Q'"
using assms by (meson inf.cobounded1 inf.cobounded2 le_inf_iff inhabits.pre inhabits_def)

lemma infL:
  assumes "P -s, xs\<rightarrow> R"
  assumes "Q -s, xs\<rightarrow> R"
  shows "P \<sqinter> Q -s, xs\<rightarrow> R"
using assms by (meson le_inf_iff inhabits_def)

setup \<open>Sign.mandatory_path "spec"\<close>

lemma bind:
  assumes "f -s, xs\<rightarrow> f'"
  shows "f \<bind> g -s, xs\<rightarrow> f' \<bind> g"
using assms by (simp add: inhabits_def spec.bind.mono flip: spec.bind.bind)

lemmas bind' = inhabits.trans[OF inhabits.spec.bind]

lemma parallelL:
  assumes "P -s, xs\<rightarrow> P'"
  assumes "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. Q) \<le> Q"
  shows "P \<parallel> Q -s, xs\<rightarrow> P' \<parallel> Q"
by (rule inhabits.mono[OF spec.parallel.unwindL[OF assms(2) assms(1)[unfolded inhabits_def]]
                          order.refl])
   (simp add: inhabits_def)

lemma parallelR:
  assumes "Q -s, xs\<rightarrow> Q'"
  assumes "spec.rel ({env} \<times> UNIV) \<bind> (\<lambda>_::unit. P) \<le> P"
  shows "P \<parallel> Q -s, xs\<rightarrow> P \<parallel> Q'"
by (subst (1 2) spec.parallel.commute) (rule inhabits.spec.parallelL assms)+

lemmas parallelL' = inhabits.trans[OF inhabits.spec.parallelL]
lemmas parallelR' = inhabits.trans[OF inhabits.spec.parallelR]

setup \<open>Sign.mandatory_path "action"\<close>

lemma step:
  assumes "(v, a, s, s') \<in> F"
  shows "spec.action F -s, [(a, s')]\<rightarrow> spec.return v"
by (clarsimp simp: inhabits_def trace.split_all spec.bind.singletonL spec.term.none.singleton
                   spec.singleton.le_conv spec.action.stepI[OF assms]
           intro!: ord_eq_le_trans[OF spec.singleton.Cons spec.action.stepI[OF assms]])

lemma stutter:
  assumes "(v, a, s, s) \<in> F"
  shows "spec.action F -s, []\<rightarrow> spec.return v"
using inhabits.spec.action.step[OF assms] by (simp add: inhabits_def)

setup \<open>Sign.parent_path\<close>

lemma map:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  assumes "P -s, xs \<rightarrow> spec.return v"
  shows "spec.map af sf vf P -sf s, map (map_prod af sf) xs\<rightarrow> spec.return (vf v)"
proof -
  have "\<lblot>sf s, map (map_prod af sf) xs, Some ()\<rblot> \<then> spec.return (vf v)
     \<le> spec.map af sf vf (\<lblot>s, xs, Some ()\<rblot> \<then> spec.return v)"
    by (subst (1) spec.bind.singletonL)
       (fastforce intro: spec.bind.incompleteI
                         spec.bind.continueI[where ys="[]" and w="Some v", simplified]
                   simp: spec.singleton.le_conv spec.term.none.singleton
                  split: option.split_asm)
  then show ?thesis
    using assms by (auto simp: inhabits_def dest: spec.map.mono[where af=af and sf=sf and vf=vf])
qed

lemma invmap:
  fixes af :: "'a \<Rightarrow> 'b"
  fixes sf :: "'s \<Rightarrow> 't"
  fixes vf :: "'v \<Rightarrow> 'w"
  assumes "P -sf s, map (map_prod af sf) xs \<rightarrow> P'"
  shows "spec.invmap af sf vf P -s, xs\<rightarrow> spec.invmap af sf vf P'"
by (strengthen ord_to_strengthen(2)[OF assms(1)[unfolded inhabits_def]])
   (simp add: inhabits_def spec.invmap.bind spec.map.singleton spec.bind.mono
        flip: spec.map_invmap.galois)

setup \<open>Sign.mandatory_path "term.none"\<close>

lemma step:
  assumes "P -s, xs\<rightarrow> P'"
  shows "spec.term.none P -s, xs\<rightarrow> spec.term.none P'"
by (simp add: inhabits.spec.bind[OF assms] flip: spec.bind.botR)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "term.all"\<close>

lemma step:
  assumes "P -s, xs\<rightarrow> P'"
  shows "spec.term.all P -s, xs\<rightarrow> spec.term.all P'"
by (strengthen ord_to_strengthen(2)[OF assms(1)[unfolded inhabits_def]])
   (simp add: inhabits_def spec.term.all.bind)

lemma "term":
  assumes "spec.idle \<le> P"
  shows "spec.term.all P -s, []\<rightarrow> spec.return v"
by (strengthen ord_to_strengthen(2)[OF assms(1)])
   (auto simp: spec.term.all.idle intro: spec.idle_le inhabits.tau inhabits.Sup)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "kleene.star"\<close>

lemma step:
  assumes "P -s, xs\<rightarrow> P'"
  shows "spec.kleene.star P -s, xs\<rightarrow> P' \<then> spec.kleene.star P"
by (subst spec.kleene.star.simps) (simp add: assms inhabits.supL inhabits.spec.bind)

lemma "term":
  shows "spec.kleene.star P -s, []\<rightarrow> spec.return ()"
by (metis inhabits.tau inhabits.supR spec.kleene.star.simps spec.idle.return_le)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "rel"\<close>

lemma rel:
  assumes "trace.steps' s xs \<subseteq> r"
  shows "spec.rel r -s, xs\<rightarrow> spec.rel r"
proof -
  from assms
  have "\<lblot>s, xs, Some ()\<rblot> \<then> spec.rel r \<le> spec.rel r \<bind> (\<lambda>_::unit. spec.rel r)"
    by (simp add: spec.bind.mono spec.singleton.le_conv)
  then show ?thesis
    by (simp add: inhabits_def spec.rel.wind_bind)
qed

lemma rel_term:
  assumes "trace.steps' s xs \<subseteq> r"
  shows "spec.rel r -s, xs\<rightarrow> spec.return v"
by (rule inhabits.pre[OF inhabits.spec.rel.rel[OF assms] spec.return.rel_le refl])

lemma step:
  assumes "(a, s, s') \<in> r"
  shows "spec.rel r -s, [(a, s')]\<rightarrow> spec.rel r"
by (rule inhabits.pre)
   (auto intro: assms inhabits.spec.action.step[where s'=s'] inhabits.spec.kleene.star.step
                      inhabits.spec.term.all.step
          simp: spec.rel_def spec.rel.act_def spec.bind.returnL spec.idle_le)

lemma "term":
  shows "spec.rel r -s, []\<rightarrow> spec.return v"
by (simp add: inhabits.pre[OF inhabits.tau[OF spec.idle.rel_le] spec.return.rel_le])

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>
(*<*)

end
(*>*)
