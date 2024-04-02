theory Bisim_Struct_Cong
  imports Bisim_Pres Sim_Struct_Cong "Psi_Calculi.Structural_Congruence"
begin

text \<open>This file is a (heavily modified) variant of the theory {\it Psi\_Calculi.Bisim\_Struct\_Cong}
from~\cite{DBLP:journals/afp/Bengtson12}.\<close>

context env begin

lemma bisimParComm:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> P \<parallel> Q \<sim> Q \<parallel> P"
proof -
  let ?X = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q), \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)) | xvec \<Psi> P Q. xvec \<sharp>* \<Psi>}"

  have "eqvt ?X"
    by(force simp add: eqvt_def pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)

  have "(\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
    using resChain.base by(smt (verit) freshSets(1) mem_Collect_eq)
  then show ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> PQ QP)
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)" and "xvec \<sharp>* \<Psi>"
      by auto

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q"
      by(rule freshFrame[where C="(\<Psi>, Q)"]) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(rule freshFrame[where C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P)"]) auto
    from FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" by(force dest: extractFrameFreshChain)
    have "\<langle>(xvec@A\<^sub>P@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>(xvec@A\<^sub>Q@A\<^sub>P), \<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P\<rangle>"
      by(simp add: frameChainAppend)
        (metis frameResChainPres frameResChainComm frameNilStatEq compositionSym Associativity Commutativity FrameStatEqTrans)
    with FrP FrQ PFrQ QFrP \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
    show ?case by(auto simp add: frameChainAppend)
  next
    case(cSim \<Psi> PQ QP)
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
      and "xvec \<sharp>* \<Psi>"
      by auto
    moreover have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<leadsto>[?X] \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
    proof -
      have "\<Psi> \<rhd> P \<parallel> Q \<leadsto>[?X] Q \<parallel> P"
      proof -
        note \<open>eqvt ?X\<close>
        moreover have "\<And>\<Psi> P Q. (\<Psi>, P \<parallel> Q, Q \<parallel> P) \<in> ?X"
          using resChain.base by(smt (verit) freshSets(1) mem_Collect_eq)
        moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X"
        proof (induct xvec)
          case Nil
          then show ?case
            by (smt (verit, ccfv_threshold) Pair_inject freshChainAppend mem_Collect_eq resChainAppend)
        next
          case (Cons a xvec)
          then show ?case
            by blast
        qed
        ultimately show ?thesis by(rule simParComm)
      qed
      moreover note \<open>eqvt ?X\<close> \<open>xvec \<sharp>* \<Psi>\<close>
      moreover have "\<And>\<Psi> P Q xvec. \<lbrakk>(\<Psi>, P, Q) \<in> ?X; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*xvec\<rparr>Q) \<in> ?X"
        using resChainAppend[symmetric] freshChainAppend by blast
      ultimately show ?thesis
        by(rule resChainPres)
    qed
    ultimately show ?case by simp
  next
    case(cExt \<Psi> PQ QP \<Psi>')
    from \<open>(\<Psi>, PQ, QP) \<in> ?X\<close>
    obtain xvec P Q where PFrQ: "PQ = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)" and QFrP: "QP = \<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P)"
      and "xvec \<sharp>* \<Psi>"
      by auto

    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>"
      and "(p \<bullet> xvec) \<sharp>* P"
      and "(p \<bullet> xvec) \<sharp>* Q"
      and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
      and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule name_list_avoiding[where c="(\<Psi>, P, Q, \<Psi>')"]) auto

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (P \<parallel> Q))"
      by(subst resChainAlpha) auto
    then have PQAlpha: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q))"
      by(simp add: eqvts)

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> (Q \<parallel> P))"
      by(subst resChainAlpha) auto
    then have QPAlpha: "\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> P) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))"
      by(simp add: eqvts)

    from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> (p \<bullet> Q)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> Q) \<parallel> (p \<bullet> P))) \<in> ?X"
      by auto
    with PFrQ QFrP PQAlpha QPAlpha show ?case by simp
  next
    case(cSym \<Psi> PR QR)
    then show ?case by blast
  qed
qed

inductive_set resCommRel :: "('b \<times> ('a,'b,'c) psi \<times> ('a,'b,'c) psi) set"
  where
    resCommRel_refl : "(\<Psi>,P,P) \<in> resCommRel"
  | resCommRel_swap : "\<lbrakk>a \<sharp> \<Psi>; b \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>,\<lparr>\<nu>a\<rparr>(\<lparr>\<nu>b\<rparr>P),\<lparr>\<nu>b\<rparr>(\<lparr>\<nu>a\<rparr>P)) \<in> resCommRel"
  | resCommRel_res : "\<lbrakk>(\<Psi>,P,Q) \<in> resCommRel; a \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>,\<lparr>\<nu>a\<rparr>P,\<lparr>\<nu>a\<rparr>Q) \<in> resCommRel"

lemma eqvtResCommRel: "eqvt resCommRel"
proof -
  {
    fix \<Psi> P Q
      and p::"name prm"
    assume "(\<Psi>,P,Q) \<in> resCommRel"
    then have "(p\<bullet>\<Psi>,p\<bullet>P,p\<bullet>Q) \<in> resCommRel"
    proof(induct rule: resCommRel.inducts)
      case resCommRel_refl then show ?case by(rule resCommRel.intros)
    next
      case(resCommRel_swap a \<Psi> b P)
      then have "(p\<bullet>a) \<sharp> p\<bullet>\<Psi>" and "(p\<bullet>b) \<sharp> p\<bullet>\<Psi>"
         apply -
        by(subst (asm) (1 2) perm_bool[where pi=p,symmetric], simp add: eqvts)+
      then show ?case unfolding eqvts
        by(rule resCommRel.intros)
    next
      case(resCommRel_res \<Psi> P Q a)
      from \<open>a \<sharp> \<Psi>\<close> have "(p\<bullet>a) \<sharp> p\<bullet>\<Psi>"
        apply -
        by(subst (asm) perm_bool[where pi=p,symmetric], simp add: eqvts)
      then show ?case using \<open>(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> resCommRel\<close>
        unfolding eqvts
        by(intro resCommRel.intros)
    qed
  }
  then show ?thesis unfolding eqvt_def
    by auto
qed

lemma resCommRelStarRes:
  assumes "(\<Psi>,P,Q) \<in> resCommRel\<^sup>\<star>"
    and   "a \<sharp> \<Psi>"
  shows   "(\<Psi>,\<lparr>\<nu>a\<rparr>P,\<lparr>\<nu>a\<rparr>Q) \<in> resCommRel\<^sup>\<star>"
  using assms
proof(induct rule: rel_trancl.induct)
  case r_into_rel_trancl then show ?case by(auto intro: resCommRel_res)
next
  case(rel_trancl_into_rel_trancl \<Psi> P Q R)
  then show ?case
    by(auto dest: resCommRel_res intro: rel_trancl.intros)
qed

lemma resCommRelStarResChain:
  assumes "(\<Psi>,P,Q) \<in> resCommRel\<^sup>\<star>"
    and   "xvec \<sharp>* \<Psi>"
  shows   "(\<Psi>,\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*xvec\<rparr>Q) \<in> resCommRel\<^sup>\<star>"
  using assms
  by(induct xvec) (auto simp add: resCommRelStarRes)

lemma length_induct1[consumes 0, case_names Nil Cons]:
  assumes b: "P []"
    and   s: "\<And> x xvec. \<lbrakk>\<And> yvec. length xvec=length yvec\<Longrightarrow>P yvec\<rbrakk> \<Longrightarrow> P(x#xvec)"
  shows   "P xvec"
proof(induct xvec rule: length_induct)
  case(1 xvec)
  then show ?case
  proof(cases xvec)
    case Nil then show ?thesis by(simp add: b)
  next
    case(Cons y yvec)
    with \<open>\<forall>ys. length ys < length xvec \<longrightarrow> P ys\<close> have "\<forall>ys. length ys = length yvec \<longrightarrow> P ys" by simp
    then show ?thesis unfolding Cons
      using s by auto
  qed
qed

lemma oneStepPerm_in_rel:
  assumes "xvec \<sharp>* \<Psi>"
  shows "(\<Psi>,\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*(rotate1 xvec)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  using assms
proof(induct xvec rule: length_induct1)
  case Nil then show ?case by(auto intro: resCommRel_refl)
next
  case(Cons x xvec)
  note Cons1 = this
  show ?case
  proof(cases xvec)
    case Nil then show ?thesis
      by(auto intro: resCommRel_refl)
  next
    case(Cons y yvec)
    then have "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" using \<open>(x # xvec) \<sharp>* \<Psi>\<close>
      by simp+
    have "(\<Psi>, \<lparr>\<nu>*(x#y#yvec)\<rparr>P, \<lparr>\<nu>*(y#x#yvec)\<rparr>P) \<in> resCommRel\<^sup>\<star>" using \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close>
      by(auto intro: resCommRel_swap)
    moreover have "(\<Psi>, \<lparr>\<nu>*(y#x#yvec)\<rparr>P, \<lparr>\<nu>*(y#rotate1(x#yvec))\<rparr>P) \<in> resCommRel\<^sup>\<star>"
    proof -
      have "(\<Psi>, \<lparr>\<nu>*(x#yvec)\<rparr>P, \<lparr>\<nu>*rotate1(x#yvec)\<rparr>P) \<in> resCommRel\<^sup>\<star>" using \<open>xvec \<sharp>* \<Psi>\<close> Cons \<open>x \<sharp> \<Psi>\<close>
        by(intro Cons1) auto
      then show ?thesis using \<open>y \<sharp> \<Psi>\<close>
        unfolding resChain.simps
        by(rule resCommRelStarRes)
    qed
    ultimately show ?thesis unfolding Cons
      by(auto intro: rel_trancl_transitive)
  qed
qed

lemma fresh_same_multiset:
  fixes xvec::"name list"
    and yvec::"name list"
  assumes "mset xvec = mset yvec"
    and   "xvec \<sharp>* X"
  shows   "yvec \<sharp>* X"
proof -
  from \<open>mset xvec = mset yvec\<close> have "set xvec = set yvec"
    using mset_eq_setD by blast
  then show ?thesis using \<open>xvec \<sharp>* X\<close>
    unfolding fresh_def fresh_star_def name_list_supp
    by auto
qed

lemma nStepPerm_in_rel:
  assumes "xvec \<sharp>* \<Psi>"
  shows "(\<Psi>,\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*(rotate n xvec)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  using assms
proof(induct n)
  case 0 then show ?case by(auto intro: resCommRel_refl)
next
  case(Suc n)
  then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*rotate n xvec\<rparr>P) \<in> resCommRel\<^sup>\<star>"
    by simp
  moreover have "(\<Psi>, \<lparr>\<nu>*rotate n xvec\<rparr>P,\<lparr>\<nu>*rotate (Suc n) xvec\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  proof -
    {
      fix xvec::"name list"
      assume "xvec \<sharp>* \<Psi>"
      have "rotate1 xvec \<sharp>* \<Psi>" using \<open>xvec \<sharp>* \<Psi>\<close>
      proof(induct xvec)
        case Nil then show ?case by simp
      next
        case Cons then show ?case by simp
      qed
    }
    note f1 = this
    have "rotate n xvec \<sharp>* \<Psi>" using \<open>xvec \<sharp>* \<Psi>\<close>
      by(induct n) (auto simp add: f1)
    then show ?thesis
      by(auto simp add: oneStepPerm_in_rel)
  qed
  ultimately show ?case
    by(rule rel_trancl_transitive)
qed

lemma any_perm_in_rel:
  assumes "xvec \<sharp>* \<Psi>"
    and   "mset xvec = mset yvec"
  shows "(\<Psi>,\<lparr>\<nu>*xvec\<rparr>P,\<lparr>\<nu>*yvec\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  using assms
proof(induct xvec arbitrary: yvec rule: length_induct1)
  case Nil then show ?case by(auto intro: resCommRel.intros)
next
  case(Cons x xvec)
  obtain yvec1 yvec2 where yveceq: "yvec=yvec1@x#yvec2"
  proof -
    assume 1: "\<And>yvec1 yvec2. yvec = yvec1 @ x # yvec2 \<Longrightarrow> thesis"
    {
      note \<open>mset (x # xvec) = mset yvec\<close>
      then have "\<exists> yvec1 yvec2. yvec=yvec1@x#yvec2"
      proof(induct xvec arbitrary: yvec rule: length_induct1)
        case Nil
        from \<open>mset [x] = mset yvec\<close> have "yvec = [x]"
          apply(induct yvec)
           apply simp
          apply(simp add: single_is_union)
          done
        then show ?case by blast
      next
        case(Cons x' xvec)
        have less: "{#x'#} \<subseteq># mset yvec" unfolding \<open>mset (x # x' # xvec) = mset yvec\<close>[symmetric]
          by simp
        from \<open>mset (x # x' # xvec) = mset yvec\<close>
        have "mset (x # xvec) = mset (remove1 x' yvec)"
          by (metis mset_remove1 remove1.simps(2))
        then have "\<exists>yvec1 yvec2. (remove1 x' yvec) = yvec1 @ x # yvec2"
          by(intro Cons) simp+
        then obtain yvec1 yvec2 where "(remove1 x' yvec) = yvec1 @ x # yvec2"
          by blast
        then show ?case
        proof(induct yvec arbitrary: yvec1 yvec2)
          case Nil then show ?case by simp
        next
          case(Cons y yvec) then show ?case
          proof(cases "x'=y")
            case True
            with \<open>remove1 x' (y # yvec) = yvec1 @ x # yvec2\<close>
            have "yvec = yvec1 @ x # yvec2"
              by simp
            then show ?thesis
              by (metis append_Cons)
          next
            case False
            then have "remove1 x' (y#yvec) = y # remove1 x' (yvec)"
              by simp
            note Cons2=Cons
            show ?thesis
            proof(cases yvec1)
              case Nil
              then show ?thesis using Cons2 False
                by auto
            next
              case(Cons y1 yvec1a)
              from \<open>remove1 x' (y # yvec) = yvec1 @ x # yvec2\<close> \<open>yvec1 = y1 # yvec1a\<close> False have "y1=y"
                by simp
              from \<open>remove1 x' (y # yvec) = yvec1 @ x # yvec2\<close>
              have "remove1 x' yvec = yvec1a @ x # yvec2" unfolding Cons \<open>y1=y\<close> using False
                by simp
              then have "\<exists>yvec1 yvec2. yvec = yvec1 @ x # yvec2"
                by(rule Cons2)
              then obtain yvec1 yvec2 where "yvec = yvec1 @ x # yvec2"
                by blast
              then show ?thesis
                by (metis append_Cons)
            qed
          qed
        qed
      qed
    }
    then show ?thesis using 1
      by blast
  qed
  from \<open>(x # xvec) \<sharp>* \<Psi>\<close> have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by auto
  have "mset (x # xvec) = mset(yvec1 @ x # yvec2)"
    unfolding yveceq[symmetric] by fact
  then have "mset (xvec) = mset(yvec1 @ yvec2)"
    by(subst add_right_cancel[symmetric,where a="{#x#}"]) (simp add: add.assoc)
  then have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*(yvec1@yvec2)\<rparr>P) \<in> resCommRel\<^sup>\<star>" using \<open>xvec \<sharp>* \<Psi>\<close>
    by(intro Cons) auto
  moreover have "(\<Psi>, \<lparr>\<nu>*(yvec1@yvec2)\<rparr>P, \<lparr>\<nu>*(yvec2@yvec1)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  proof -
    have e: "yvec2 @ yvec1 = rotate (length yvec1) (yvec1@yvec2)"
      apply(cases yvec2)
       apply simp
      apply(simp add: rotate_drop_take)
      done
    have "(yvec1@yvec2) \<sharp>* \<Psi>" using \<open>mset (xvec) = mset(yvec1 @ yvec2)\<close> \<open>xvec \<sharp>* \<Psi>\<close>
      by(rule fresh_same_multiset)
    then show ?thesis unfolding e
      by(rule nStepPerm_in_rel)
  qed
  ultimately have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>P, \<lparr>\<nu>*(yvec2 @ yvec1)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
    by(rule rel_trancl_transitive)
  then have "(\<Psi>, \<lparr>\<nu>*(x#xvec)\<rparr>P, \<lparr>\<nu>*(x # yvec2 @ yvec1)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
    unfolding resChain.simps using \<open>x \<sharp> \<Psi>\<close>
    by(rule resCommRelStarRes)
  moreover have "(\<Psi>, \<lparr>\<nu>*(x # yvec2 @ yvec1)\<rparr>P, \<lparr>\<nu>*(yvec1 @ x # yvec2)\<rparr>P) \<in> resCommRel\<^sup>\<star>"
  proof -
    have e: "yvec1 @ x # yvec2 = rotate (1+length yvec2) (x#yvec2@yvec1)"
      apply(simp add: rotate_drop_take)
      apply(cases yvec1)
      by simp+
    have "(yvec1 @ x # yvec2) \<sharp>* \<Psi>" using \<open>mset (x # xvec) = mset(yvec1 @ x # yvec2)\<close> \<open>(x#xvec) \<sharp>* \<Psi>\<close>
      by(rule fresh_same_multiset)
    then have "(x # yvec2 @ yvec1) \<sharp>* \<Psi>" by simp
    then show ?thesis unfolding e
      by(rule nStepPerm_in_rel)
  qed
  ultimately show ?case unfolding yveceq
    by(rule rel_trancl_transitive)
qed

lemma bisimResComm:
  fixes x :: name
    and \<Psi> :: 'b
    and y :: name
    and P :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
proof(cases "x=y")
  case True
  then show ?thesis by(blast intro: bisimReflexive)
next
  case False
  {
    fix x::name and y::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "y \<sharp> \<Psi>"
    let ?X = resCommRel
    from \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)) \<in> ?X"
      by(rule resCommRel_swap)
    then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)" using eqvtResCommRel
    proof(coinduct rule: bisimStarWeakCoinduct)
      case(cStatEq \<Psi> R S)
      then show ?case
      proof(induct rule: resCommRel.induct)
        case resCommRel_refl then show ?case by(rule FrameStatEqRefl)
      next
        case(resCommRel_swap x \<Psi> y P)
        moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "x \<sharp> A\<^sub>P" and "y \<sharp> A\<^sub>P"
          by(rule freshFrame[where C="(x, y, \<Psi>)"]) auto
        ultimately show ?case by(force intro: frameResComm FrameStatEqTrans)
      next
        case(resCommRel_res \<Psi> P Q a)
        then show ?case by(auto intro: frameResPres)
      qed
    next
      case(cSim \<Psi> R S)
      have "eqvt(resCommRel\<^sup>\<star>)"
        by(rule rel_trancl_eqvt) (rule eqvtResCommRel)
      from cSim show ?case
      proof(induct rule: resCommRel.induct)
        case(resCommRel_refl \<Psi> P)
        then show ?case
          by(rule simI[OF \<open>eqvt(resCommRel\<^sup>\<star>)\<close>]) (blast intro: resCommRel.intros)
      next
        case(resCommRel_swap a \<Psi> b P)
        show ?case
          by(rule resComm) (fact|auto intro: resCommRel.intros any_perm_in_rel)+
      next
        case(resCommRel_res \<Psi> P Q a)
        show ?case
          by(rule resPres[where Rel="resCommRel\<^sup>\<star>"]) (fact|simp add: resCommRelStarResChain)+
      qed
    next
      case(cExt \<Psi> R S \<Psi>') then show ?case
      proof(induct arbitrary: \<Psi>' rule: resCommRel.induct)
        case resCommRel_refl then show ?case by(rule resCommRel_refl)
      next
        case(resCommRel_swap a \<Psi> b P)
        then show ?case
        proof(cases "a=b")
          case True show ?thesis unfolding \<open>a=b\<close> by(rule resCommRel_refl)
        next
          case False
          obtain x::name and y::name where "x\<noteq>y" and "x \<sharp> \<Psi>" and "x \<sharp> \<Psi>'" and "x \<sharp> P" and "x \<noteq> a" and "x\<noteq>b" and "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> P" and "y \<noteq> a" and "y\<noteq>b"
            apply(generate_fresh "name")
            apply(generate_fresh "name")
            by force
          then show ?thesis using False
            apply(subst (1 2) alphaRes[where x=a and y=x])
              apply assumption
             apply(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp])
            apply(subst (1 2) alphaRes[where x=b and y=y])
              apply(simp add: fresh_abs_fun_iff[OF pt_name_inst, OF at_name_inst, OF fin_supp] fresh_left)
             apply assumption
            unfolding eqvts
            apply(subst (1) cp1[OF cp_pt_inst, OF pt_name_inst, OF at_name_inst])
            by(auto simp add: eqvts swap_simps intro: resCommRel.intros)
        qed
      next
        case(resCommRel_res \<Psi> P Q a)
        obtain b::name where "b \<sharp> \<Psi>" and "b \<noteq> a" and "b \<sharp> P" and "b \<sharp> Q" and "b \<sharp> \<Psi>'"
          by(generate_fresh "name") auto
        have "(\<Psi> \<otimes> ([(a,b)]\<bullet>\<Psi>'), P, Q) \<in> resCommRel" by fact
        moreover from \<open>b \<sharp> \<Psi>'\<close> have "a \<sharp> ([(a, b)] \<bullet> \<Psi>')" by(simp add: fresh_left swap_simps)
        with \<open>a \<sharp> \<Psi>\<close> have "a \<sharp> \<Psi> \<otimes> ([(a,b)]\<bullet>\<Psi>')" by force
        ultimately have "(\<Psi> \<otimes> ([(a,b)]\<bullet>\<Psi>'), \<lparr>\<nu>a\<rparr>P, \<lparr>\<nu>a\<rparr>Q) \<in> resCommRel"
          by(rule resCommRel.intros)
        then have "([(a,b)]\<bullet>(\<Psi> \<otimes> ([(a,b)]\<bullet>\<Psi>'), \<lparr>\<nu>a\<rparr>P, \<lparr>\<nu>a\<rparr>Q)) \<in> resCommRel" using eqvtResCommRel
          by(intro eqvtI)
        then have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>b\<rparr>([(a,b)]\<bullet>P), \<lparr>\<nu>b\<rparr>([(a,b)]\<bullet>Q)) \<in> resCommRel" using \<open>a \<sharp> \<Psi>\<close> \<open>b \<sharp> \<Psi>\<close>
          by(simp add: eqvts swap_simps)
        then show ?case using \<open>b \<sharp> Q\<close> \<open>b \<sharp> P\<close>
          apply(subst (1 2) alphaRes[where x=a and y=b])
          by(assumption|simp only: eqvts)+
      qed
    next
      case(cSym \<Psi> R S) then show ?case
        by(induct rule: resCommRel.inducts) (auto intro: resCommRel.intros)
    qed
  }
  moreover obtain x'::name where "x' \<sharp> \<Psi>" and "x' \<sharp> P" and "x' \<noteq> x" and "x' \<noteq> y"
    by(generate_fresh "name") auto
  moreover obtain y'::name where "y' \<sharp> \<Psi>" and "y' \<sharp> P" and "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y'), (x, x')] \<bullet> P)) \<sim> \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y'), (x, x')] \<bullet> P))" by auto
  then show ?thesis using \<open>x' \<sharp> P\<close> \<open>x' \<noteq> x\<close> \<open>x' \<noteq> y\<close> \<open>y' \<sharp> P\<close> \<open>y' \<noteq> x\<close> \<open>y' \<noteq> y\<close> \<open>y' \<noteq> x'\<close> \<open>x \<noteq> y\<close>
    apply(subst alphaRes[where x=x and y=x' and P=P], auto)
    apply(subst alphaRes[where x=y and y=y' and P=P], auto)
    apply(subst alphaRes[where x=x and y=x' and P="\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    apply(subst alphaRes[where x=y and y=y' and P="\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> P)"], auto simp add: abs_fresh fresh_left)
    by(subst perm_compose) (simp add: eqvts calc_atm)
qed

lemma bisimResComm':
  fixes x    :: name
    and \<Psi>   :: 'b
    and xvec :: "name list"
    and P    :: "('a, 'b, 'c) psi"

assumes "x \<sharp> \<Psi>"
  and   "xvec \<sharp>* \<Psi>"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<sim> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)"
  using assms
  by(induct xvec) (auto intro: bisimResComm bisimReflexive bisimResPres bisimTransitive)

lemma bisimParPresSym:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim> Q"

shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
  using assms
  by(metis bisimParComm bisimParPres bisimTransitive)

lemma bisimScopeExt:
  fixes x :: name
    and \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "x \<sharp> P"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
proof -
  {
    fix x::name and Q :: "('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> P"
    let ?X1 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> Q)), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))) | \<Psi> xvec yvec P Q. yvec \<sharp>* \<Psi> \<and> yvec \<sharp>* P \<and> xvec \<sharp>* \<Psi>}"
    let ?X2 = "{((\<Psi>::'b), \<lparr>\<nu>*xvec\<rparr>((P::('a, 'b, 'c) psi) \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q)), \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))) | \<Psi> xvec yvec P Q. yvec \<sharp>* \<Psi> \<and> yvec \<sharp>* P \<and> xvec \<sharp>* \<Psi>}"
    let ?X = "?X1 \<union> ?X2"
    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<in> ?X"
    proof -
      from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> P\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(P \<parallel> Q), P \<parallel> \<lparr>\<nu>x\<rparr>Q) \<in> ?X1"
        by (smt (verit, del_insts) mem_Collect_eq freshSets(1) freshSets(5) resChain.base resChain.step)
      then show ?thesis by auto
    qed
    moreover have "eqvt ?X"
      by (rule eqvtUnion) (clarsimp simp add: eqvt_def eqvts, metis fresh_star_bij(2))+
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
    proof(coinduct rule: transitiveStarCoinduct)
      case(cStatEq \<Psi> R T)
      then have "(\<Psi>, R, T) \<in> ?X1 \<or> (\<Psi>, R, T) \<in> ?X2"
        by blast
      then show ?case
      proof(rule disjE)
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec yvec P Q where "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "yvec \<sharp>* A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
          by(rule freshFrame[where C="(\<Psi>, yvec, Q)"]) auto
        moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "yvec \<sharp>* A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
          by(rule freshFrame[where C="(\<Psi>, yvec, A\<^sub>P, \<Psi>\<^sub>P)"]) auto
        moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
          by(auto dest: extractFrameFreshChain)
        moreover from \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* A\<^sub>P\<close> FrP have "yvec \<sharp>* \<Psi>\<^sub>P"
          by(drule_tac extractFrameFreshChain) auto
        ultimately show ?case
          by(auto simp add: frameChainAppend[symmetric] freshChainAppend) (auto simp add: frameChainAppend intro: frameResChainPres frameResChainComm)
      next
        assume "(\<Psi>, R, T) \<in> ?X2"
        then obtain xvec yvec P Q where "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "yvec \<sharp>* A\<^sub>P" and "A\<^sub>P \<sharp>* Q"
          by(rule freshFrame[where C="(\<Psi>, yvec, Q)"]) auto
        moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "yvec \<sharp>* A\<^sub>Q" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
          by(rule freshFrame[where C="(\<Psi>, yvec, A\<^sub>P, \<Psi>\<^sub>P)"]) auto
        moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
          by(auto dest: extractFrameFreshChain)
        moreover from \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* A\<^sub>P\<close> FrP have "yvec \<sharp>* \<Psi>\<^sub>P"
          by(drule_tac extractFrameFreshChain) auto
        ultimately show ?case
          by(auto simp add: frameChainAppend[symmetric] freshChainAppend) (auto simp add: frameChainAppend intro: frameResChainPres frameResChainComm)
      qed
    next
      case(cSim \<Psi> R T)
      let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> ?X \<or> \<Psi> \<rhd> P' \<sim> Q') \<and> \<Psi> \<rhd> Q' \<sim> Q}"
      from \<open>eqvt ?X\<close> have "eqvt ?Y" by blast
      have C1: "\<And>\<Psi> R T y. \<lbrakk>(\<Psi>, R, T) \<in> ?Y; (y::name) \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
      proof -
        fix \<Psi> R T y
        assume "(\<Psi>, R, T) \<in> ?Y"
        then obtain R' T' where "\<Psi> \<rhd> R \<sim> R'" and "(\<Psi>, R', T') \<in> (?X \<union> bisim)" and "\<Psi> \<rhd> T' \<sim> T" by force
        assume "(y::name) \<sharp> \<Psi>"
        show "(\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y"
        proof(cases "(\<Psi>, R', T') \<in> ?X")
          assume "(\<Psi>, R', T') \<in> ?X"
          show ?thesis
          proof(cases "(\<Psi>, R', T') \<in> ?X1")
            assume "(\<Psi>, R', T') \<in> ?X1"
            then obtain xvec yvec P Q where R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))"
              and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
              by auto
            from \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisimResPres)
            moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q), \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))) \<in> ?X1"
              by(force simp del: resChain.simps)
            with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
            moreover from \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisimResPres)
            ultimately show ?thesis by blast
          next
            assume "(\<Psi>, R', T') \<notin> ?X1"
            with \<open>(\<Psi>, R', T') \<in> ?X\<close> have "(\<Psi>, R', T') \<in> ?X2" by blast
            then obtain xvec yvec P Q where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and R'eq: "R' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
              by auto
            from \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>R \<sim> \<lparr>\<nu>y\<rparr>R'" by(rule bisimResPres)
            moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(y#xvec)\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q)), \<lparr>\<nu>*(y#xvec)\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))) \<in> ?X2"
              by(force simp del: resChain.simps)
            with R'eq T'eq have "(\<Psi>, \<lparr>\<nu>y\<rparr>R', \<lparr>\<nu>y\<rparr>T') \<in> ?X \<union> bisim" by simp
            moreover from \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>T' \<sim> \<lparr>\<nu>y\<rparr>T" by(rule bisimResPres)
            ultimately show ?thesis by blast
          qed
        next
          assume "(\<Psi>, R', T') \<notin> ?X"
          with \<open>(\<Psi>, R', T') \<in> ?X \<union> bisim\<close> have "\<Psi> \<rhd> R' \<sim> T'" by blast
          with \<open>\<Psi> \<rhd> R \<sim> R'\<close> \<open>\<Psi> \<rhd> T' \<sim> T\<close> \<open>y \<sharp> \<Psi>\<close> show ?thesis
            by(blast dest: bisimResPres)
        qed
      qed
      have C1': "\<And>\<Psi> R T y. \<lbrakk>(\<Psi>, R, T) \<in> ?Y\<^sup>\<star>; (y::name) \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y\<^sup>\<star>"
      proof -
        fix \<Psi> R
          and T::"('a,'b,'c) psi"
          and y::name
        assume "(\<Psi>, R, T) \<in> ?Y\<^sup>\<star>"
          and  "y \<sharp> \<Psi>"
        then show "(\<Psi>, \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>T) \<in> ?Y\<^sup>\<star>"
        proof(induct rule: rel_trancl.induct)
          case(r_into_rel_trancl \<Psi> P Q)
          then show ?case
            by (intro rel_trancl.intros(1)) (rule C1)
        next
          case(rel_trancl_into_rel_trancl \<Psi> P Q R)
          then show ?case
            using rel_trancl.intros(2) C1 by meson
        qed
      qed
      have C1'': "\<And>\<Psi> R T yvec. \<lbrakk>(\<Psi>, R, T) \<in> ?Y\<^sup>\<star>; (yvec::name list) \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*yvec\<rparr>R, \<lparr>\<nu>*yvec\<rparr>T) \<in> ?Y\<^sup>\<star>"
      proof -
        fix \<Psi> R T
          and yvec::"name list"
        assume "(\<Psi>, R, T) \<in> ?Y\<^sup>\<star>"
          and  "yvec \<sharp>* \<Psi>"
        then show "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>R, \<lparr>\<nu>*yvec\<rparr>T) \<in> ?Y\<^sup>\<star>"
          apply(induct yvec)
           apply simp
          unfolding resChain.simps
          by(rule C1') simp+
      qed
      have C2: "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> ?Y\<^sup>\<star>"
      proof -
        fix   y::name
          and \<Psi>::'b
          and R::"('a,'b,'c) psi"
          and S::"('a,'b,'c) psi"
          and zvec::"name list"
        assume "y \<sharp> \<Psi>"
          and  "y \<sharp> R"
          and  "zvec \<sharp>* \<Psi>"
        have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)) \<sim> (\<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>(R \<parallel> S)))"
          by(rule bisimResComm') fact+
        moreover have "(\<Psi>, (\<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>(R \<parallel> S))), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> ?X" using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> R\<close> \<open>zvec \<sharp>* \<Psi>\<close>
          apply clarsimp
          apply(rule exI[where x=zvec])
          apply(rule exI[where x="[y]"])
          by auto
        moreover have "\<Psi> \<rhd> \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S) \<sim> \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)"
          by(rule bisimReflexive)
        ultimately show "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)) \<in> ?Y\<^sup>\<star>"
          by blast
      qed
      have C2': "\<And>y \<Psi>' R S zvec. \<lbrakk>y \<sharp> \<Psi>'; y \<sharp> R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> ?Y\<^sup>\<star>"
      proof -
        fix   y::name
          and \<Psi>::'b
          and R::"('a,'b,'c) psi"
          and S::"('a,'b,'c) psi"
          and zvec::"name list"
        assume "y \<sharp> \<Psi>"
          and  "y \<sharp> R"
          and  "zvec \<sharp>* \<Psi>"
        have "\<Psi> \<rhd> (\<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>(R \<parallel> S))) \<sim> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))"
          by(rule bisimSymmetric[OF bisimResComm']) fact+
        moreover have "(\<Psi>, \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), (\<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>(R \<parallel> S)))) \<in> ?X" using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> R\<close> \<open>zvec \<sharp>* \<Psi>\<close>
          apply(intro UnI2)
          apply clarsimp
          apply(rule exI[where x=zvec])
          apply(rule exI[where x="[y]"])
          by auto
        moreover have "\<Psi> \<rhd> \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S) \<sim> \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S)"
          by(rule bisimReflexive)
        ultimately show "(\<Psi>, \<lparr>\<nu>*zvec\<rparr>(R \<parallel> \<lparr>\<nu>y\<rparr>S), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> ?Y\<^sup>\<star>"
          by blast
      qed
      have C3: "\<And>\<Psi>' zvec R y. \<lbrakk>y \<sharp> \<Psi>'; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> ?Y\<^sup>\<star>"
      proof -
        fix   y::name
          and \<Psi>::'b
          and R::"('a,'b,'c) psi"
          and zvec::"name list"
        assume "y \<sharp> \<Psi>"
          and  "zvec \<sharp>* \<Psi>"
        then have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R) \<sim> \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)"
          by(rule bisimResComm')
        then show "(\<Psi>, \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*zvec\<rparr>R), \<lparr>\<nu>*zvec\<rparr>(\<lparr>\<nu>y\<rparr>R)) \<in> ?Y\<^sup>\<star>"
          by(blast intro: bisimReflexive)
      qed
      have C4: "\<And>\<Psi>' R S zvec. \<lbrakk>zvec \<sharp>* R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S))) \<in> ?Y\<^sup>\<star>"
      proof -
        fix   \<Psi>::'b
          and R::"('a,'b,'c) psi"
          and S::"('a,'b,'c) psi"
          and zvec::"name list"
        assume "zvec \<sharp>* R"
          and  "zvec \<sharp>* \<Psi>"
        then have "(\<Psi>, (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S))) \<in> ?X"
          apply clarsimp
          apply(rule exI[where x="[]"])
          apply(rule exI[where x=zvec])
          by auto
        then show "(\<Psi>, (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S)), (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S))) \<in> ?Y\<^sup>\<star>"
          by(blast intro: bisimReflexive)
      qed
      have C4': "\<And>\<Psi>' R S zvec. \<lbrakk>zvec \<sharp>* R; zvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S)), (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> ?Y\<^sup>\<star>"
      proof -
        fix   \<Psi>::'b
          and R::"('a,'b,'c) psi"
          and S::"('a,'b,'c) psi"
          and zvec::"name list"
        assume "zvec \<sharp>* R"
          and  "zvec \<sharp>* \<Psi>"
        then have "(\<Psi>, (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S)), (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> ?X"
          apply(intro UnI2)
          apply clarsimp
          apply(rule exI[where x="[]"])
          apply(rule exI[where x=zvec])
          by auto
        then show "(\<Psi>, (R \<parallel> (\<lparr>\<nu>*zvec\<rparr>S)), (\<lparr>\<nu>*zvec\<rparr>(R \<parallel> S))) \<in> ?Y\<^sup>\<star>"
          by(blast intro: bisimReflexive)
      qed
      {
        fix \<Psi> P Q R
        assume "\<Psi> \<rhd> P \<leadsto>[?Y\<^sup>\<star>] Q"
          and  "\<Psi> \<rhd> Q \<leadsto>[?Y\<^sup>\<star>] R"
        moreover note rel_trancl_eqvt[OF \<open>eqvt ?Y\<close>]
        moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> ?Y\<^sup>\<star> \<and> (\<Psi>, Q, R) \<in> ?Y\<^sup>\<star>} \<subseteq> ?Y\<^sup>\<star>"
          by(auto intro: rel_trancl_transitive)
        ultimately have  "\<Psi> \<rhd> P \<leadsto>[?Y\<^sup>\<star>] R"
          by(rule transitive)
      }
      note trans = this

      show ?case
      proof(cases "(\<Psi>, R, T) \<in> ?X1")
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec yvec P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))"
        proof -
          have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q)" using \<open>yvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close>
          proof(induct yvec arbitrary: Q)
            case Nil show ?case
              unfolding resChain.simps
              by(rule monotonic[where A="?Y"]) (blast intro: reflexive bisimReflexive)+
          next
            case(Cons y yvec)
            then have "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" and "y \<sharp> P"
              by simp+
            have "\<Psi> \<rhd> \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q))"
            proof -
              have "\<Psi> \<rhd> \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q \<leadsto>[bisim] \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q))"
                unfolding resChain.simps
                apply(rule bisimE)
                apply(rule bisimResComm')
                by fact+
              then have "\<Psi> \<rhd> \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q \<leadsto>[?Y] \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q))"
                apply -
                apply(drule monotonic[where B="?Y"])
                by auto (blast intro: bisimTransitive bisimReflexive)
              then show ?thesis
                apply -
                apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                by blast
            qed
            moreover have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>(P \<parallel> \<lparr>\<nu>y\<rparr>Q)"
            proof -
              have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> Q) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> \<lparr>\<nu>y\<rparr>Q"
                apply(rule scopeExtLeft)
                      apply fact
                     apply fact
                    apply(rule rel_trancl_eqvt)
                    apply fact
                   apply(blast intro: bisimReflexive)
                by fact+
              then show ?thesis using \<open>yvec \<sharp>* \<Psi>\<close>
              proof(induct yvec)
                case Nil then show ?case by simp
              next
                case(Cons y' yvec)
                then show ?case
                  unfolding resChain.simps
                  apply -
                  apply(rule resPres[where Rel="?Y\<^sup>\<star>" and Rel'="?Y\<^sup>\<star>"])
                      apply simp
                     apply(rule rel_trancl_eqvt[OF \<open>eqvt ?Y\<close>])
                    apply simp
                   apply simp
                  by(rule C1'')
              qed
            qed
            moreover have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(P \<parallel> \<lparr>\<nu>y\<rparr>Q) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
              by(rule Cons) fact+
            moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q)"
            proof -
              have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[bisim] P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q)"
                unfolding resChain.simps
                apply(rule bisimE)
                apply(rule bisimParPresSym)
                apply(rule bisimSymmetric[OF bisimResComm'])
                by fact+
              then have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y] P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q)"
                apply -
                apply(drule monotonic[where B="?Y"])
                by auto (blast intro: bisimTransitive bisimReflexive)
              then show ?thesis
                apply -
                apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                by blast
            qed
            moreover have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>P \<parallel> \<lparr>\<nu>y\<rparr>Q \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
              by(rule Cons) fact+
            moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q)"
            proof -
              have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[bisim] P \<parallel> (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>Q))"
                apply(rule bisimE)
                apply(rule bisimParPresSym)
                apply(rule bisimSymmetric[OF bisimResComm'])
                by fact+
              then have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y] P \<parallel> (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>Q))"
                apply -
                apply(drule monotonic[where B="?Y"])
                by auto (blast intro: bisimTransitive bisimReflexive)
              then show ?thesis
                unfolding resChain.simps
                apply -
                apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                by blast
            qed
            ultimately show ?case
              by(blast dest: trans)
          qed
          then show ?thesis using \<open>xvec \<sharp>* \<Psi>\<close>
            apply(induct xvec)
             apply simp
            unfolding resChain.simps
            apply(rule resPres)
                apply simp
               apply(rule rel_trancl_eqvt[OF \<open>eqvt ?Y\<close>])
              apply simp
             apply simp
            apply(rule C1'')
             apply simp
            by assumption
        qed
        then show ?case unfolding Req Teq
          by -
      next
        assume "(\<Psi>, R, T) \<notin> ?X1"
        then have "(\<Psi>, R, T) \<in> ?X2" using \<open>(\<Psi>, R, T) \<in> ?X\<close> by blast
        then obtain xvec yvec P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))"
        proof -
          have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q)" using \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* \<Psi>\<close>
          proof(induct yvec arbitrary: Q)
            case Nil show ?case
              unfolding resChain.simps
              by(rule monotonic[where A="?Y"]) (blast intro: reflexive bisimReflexive)+
          next
            case(Cons y yvec)
            then have "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" and "y \<sharp> P"
              by simp+
            have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q"
            proof -
              have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q)) \<leadsto>[bisim] \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q"
                unfolding resChain.simps
                apply(rule bisimE)
                apply(rule bisimSymmetric[OF bisimResComm'])
                by fact+
              then have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q)) \<leadsto>[?Y] \<lparr>\<nu>*(y#yvec)\<rparr>P \<parallel> Q"
                apply -
                apply(drule monotonic[where B="?Y"])
                by auto (blast intro: bisimTransitive bisimReflexive)
              then show ?thesis
                apply -
                apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                by blast
            qed
            moreover have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>(P \<parallel> \<lparr>\<nu>y\<rparr>Q) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>(P \<parallel> Q))"
            proof -
              have "\<Psi> \<rhd> P \<parallel> \<lparr>\<nu>y\<rparr>Q \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>y\<rparr>(P \<parallel> Q)"
                apply(rule scopeExtRight)
                     apply fact
                    apply fact
                   apply(rule rel_trancl_eqvt)
                   apply fact
                  apply(blast intro: bisimReflexive)
                by fact+
              then show ?thesis using \<open>yvec \<sharp>* \<Psi>\<close>
              proof(induct yvec)
                case Nil then show ?case by simp
              next
                case(Cons y' yvec)
                then show ?case
                  unfolding resChain.simps
                  apply -
                  apply(rule resPres[where Rel="?Y\<^sup>\<star>" and Rel'="?Y\<^sup>\<star>"])
                      apply simp
                     apply(rule rel_trancl_eqvt[OF \<open>eqvt ?Y\<close>])
                    apply simp
                   apply simp
                  by(rule C1'')
              qed
              moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>(P \<parallel> \<lparr>\<nu>y\<rparr>Q)"
                by(rule Cons) fact+
              moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
              proof -
                have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q) \<leadsto>[bisim] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
                  unfolding resChain.simps
                  apply(rule bisimE)
                  apply(rule bisimParPresSym)
                  apply(rule bisimResComm')
                  by fact+
                then have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q) \<leadsto>[?Y] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
                  apply -
                  apply(drule monotonic[where B="?Y"])
                  by auto (blast intro: bisimTransitive bisimReflexive)
                then show ?thesis
                  apply -
                  apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                  by blast
              qed
            qed
            moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q)) \<leadsto>[?Y\<^sup>\<star>] \<lparr>\<nu>*yvec\<rparr>P \<parallel> \<lparr>\<nu>y\<rparr>Q"
              by(rule Cons) fact+
            moreover have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>*(y#yvec)\<rparr>Q) \<leadsto>[?Y\<^sup>\<star>] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
            proof -
              have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>Q)) \<leadsto>[bisim] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
                apply(rule bisimE)
                apply(rule bisimParPresSym)
                apply(rule bisimResComm')
                by fact+
              then have "\<Psi> \<rhd> P \<parallel> (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>Q)) \<leadsto>[?Y] P \<parallel> (\<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>Q))"
                apply -
                apply(drule monotonic[where B="?Y"])
                by auto (blast intro: bisimTransitive bisimReflexive)
              then show ?thesis
                unfolding resChain.simps
                apply -
                apply(drule monotonic[where B="?Y\<^sup>\<star>"])
                by blast
            qed
            ultimately show ?case
              by(blast dest: trans)
          qed
          then show ?thesis using \<open>xvec \<sharp>* \<Psi>\<close>
            apply(induct xvec)
             apply simp
            unfolding resChain.simps
            apply(rule resPres)
                apply simp
               apply(rule rel_trancl_eqvt[OF \<open>eqvt ?Y\<close>])
              apply simp
             apply simp
            apply(rule C1'')
             apply simp
            by assumption
        qed
        then show ?case unfolding Req Teq
          by -
      qed
    next
      case(cExt \<Psi> R T \<Psi>')
      show ?case
      proof(cases "(\<Psi>, R, T) \<in> ?X1")
        assume "(\<Psi>, R, T) \<in> ?X1"
        then obtain xvec yvec P Q where Req: "R = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and Teq: "T = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        obtain p where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P" and "(p \<bullet> yvec) \<sharp>* Q" and "(p \<bullet> yvec) \<sharp>* \<Psi>'" and "(p \<bullet> yvec) \<sharp>* xvec"
          and S: "(set p) \<subseteq> (set yvec) \<times> (set(p \<bullet> yvec))" and "distinctPerm p"
          by(rule name_list_avoiding[where c="(\<Psi>, P, Q, xvec, \<Psi>')"]) auto
        obtain q where "(q \<bullet> xvec) \<sharp>* \<Psi>" and "(q \<bullet> xvec) \<sharp>* \<Psi>'" and "(q \<bullet> xvec) \<sharp>* P"  and "(q \<bullet> xvec) \<sharp>* yvec" and "(q \<bullet> xvec) \<sharp>* Q" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>P)" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)" and "distinctPerm q" and T: "(set q) \<subseteq> (set xvec) \<times> (set(q\<bullet>xvec))" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)"
          by(rule name_list_avoiding[where c="(\<Psi>, P, Q, yvec, p\<bullet>yvec, \<Psi>',p\<bullet>P,p\<bullet>Q)"]) auto
        note \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)\<close>
        moreover have "(p \<bullet> yvec) \<sharp>* (P \<parallel> Q)" using \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close>
          by simp
        moreover have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q, \<lparr>\<nu>*xvec\<rparr>P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q)) \<in> ?X"
        proof -
          have Pdef: "(p \<bullet> P) = P" using \<open>set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)\<close> \<open>yvec \<sharp>* P\<close> \<open>(p\<bullet>yvec) \<sharp>* P\<close>
            by simp
          have yvecdef: "(q \<bullet> p \<bullet> yvec) = (p\<bullet> yvec)" using \<open>set q \<subseteq> set xvec \<times> set(q\<bullet>xvec)\<close> \<open>(p\<bullet>yvec) \<sharp>* xvec\<close> \<open>(q\<bullet>xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          have "(q \<bullet> xvec) \<sharp>* (P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q))" using \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          moreover have "(q \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q)"
            unfolding eqvts Pdef
            using \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          moreover note \<open>set q \<subseteq> set xvec \<times> set (q \<bullet> xvec)\<close>
          moreover have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*q \<bullet> xvec\<rparr>q \<bullet> \<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q,
            \<lparr>\<nu>*q \<bullet> xvec\<rparr>q \<bullet> P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q)) \<in> ?X"
          proof -
            have "(p\<bullet>yvec) \<sharp>* (\<Psi>\<otimes>\<Psi>')" using \<open>(p\<bullet>yvec) \<sharp>* \<Psi>\<close> \<open>(p\<bullet>yvec) \<sharp>* \<Psi>'\<close>
              by auto
            moreover have "(p\<bullet>yvec) \<sharp>* (q\<bullet>P)" using \<open>(p\<bullet>yvec) \<sharp>* P\<close>
              apply(subst yvecdef[symmetric])
              by(subst fresh_star_bij)
            moreover have "(q\<bullet>xvec) \<sharp>* (\<Psi>\<otimes>\<Psi>')" using \<open>(q\<bullet>xvec) \<sharp>* \<Psi>\<close> \<open>(q\<bullet>xvec) \<sharp>* \<Psi>'\<close>
              by auto
            ultimately show ?thesis
              unfolding Pdef eqvts yvecdef
              by blast
          qed
          ultimately show ?thesis
            by(subst (1 2) resChainAlpha[where p=q and xvec=xvec])
        qed
        ultimately show ?case unfolding Req Teq
          apply(intro disjI1)
          by(subst (1 2) resChainAlpha[where p=p and xvec=yvec])
      next
        assume "(\<Psi>, R, T) \<notin> ?X1"
        then have "(\<Psi>, R, T) \<in> ?X2" using \<open>(\<Psi>,R,T) \<in> ?X\<close>
          by blast
        then obtain xvec yvec P Q where Teq: "T = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>(P \<parallel> Q))" and Req: "R = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (\<lparr>\<nu>*yvec\<rparr>Q))" and "xvec \<sharp>* \<Psi>" and "yvec \<sharp>* P" and "yvec \<sharp>* \<Psi>"
          by auto
        obtain p where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P" and "(p \<bullet> yvec) \<sharp>* Q" and "(p \<bullet> yvec) \<sharp>* \<Psi>'" and "(p \<bullet> yvec) \<sharp>* xvec"
          and S: "(set p) \<subseteq> (set yvec) \<times> (set(p \<bullet> yvec))" and "distinctPerm p"
          by(rule name_list_avoiding[where c="(\<Psi>, P, Q, xvec, \<Psi>')"]) auto
        obtain q where "(q \<bullet> xvec) \<sharp>* \<Psi>" and "(q \<bullet> xvec) \<sharp>* \<Psi>'" and "(q \<bullet> xvec) \<sharp>* P"  and "(q \<bullet> xvec) \<sharp>* yvec" and "(q \<bullet> xvec) \<sharp>* Q" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>P)" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)" and "distinctPerm q" and T: "(set q) \<subseteq> (set xvec) \<times> (set(q\<bullet>xvec))" and "(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)"
          by(rule name_list_avoiding[where c="(\<Psi>, P, Q, yvec, p\<bullet>yvec, \<Psi>',p\<bullet>P,p\<bullet>Q)"]) auto
        note \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>set p \<subseteq> set yvec \<times> set (p \<bullet> yvec)\<close>
        moreover have "(p \<bullet> yvec) \<sharp>* (P \<parallel> Q)" using \<open>(p \<bullet> yvec) \<sharp>* Q\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close>
          by simp
        moreover have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*xvec\<rparr>P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q), \<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q) \<in> ?X"
        proof -
          have Pdef: "(p \<bullet> P) = P" using \<open>set p \<subseteq> set yvec \<times> set(p\<bullet>yvec)\<close> \<open>yvec \<sharp>* P\<close> \<open>(p\<bullet>yvec) \<sharp>* P\<close>
            by simp
          have yvecdef: "(q \<bullet> p \<bullet> yvec) = (p\<bullet> yvec)" using \<open>set q \<subseteq> set xvec \<times> set(q\<bullet>xvec)\<close> \<open>(p\<bullet>yvec) \<sharp>* xvec\<close> \<open>(q\<bullet>xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          have "(q \<bullet> xvec) \<sharp>* (P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q))" using \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          moreover have "(q \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q)"
            unfolding eqvts Pdef
            using \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>Q)\<close> \<open>(q \<bullet> xvec) \<sharp>* (p\<bullet>yvec)\<close>
            by simp
          moreover note \<open>set q \<subseteq> set xvec \<times> set (q \<bullet> xvec)\<close>
          moreover have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*q \<bullet> xvec\<rparr>q \<bullet> P \<parallel> (\<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> Q), \<lparr>\<nu>*q \<bullet> xvec\<rparr>q \<bullet> \<lparr>\<nu>*p \<bullet> yvec\<rparr>p \<bullet> P \<parallel> Q) \<in> ?X"
          proof -
            have "(p\<bullet>yvec) \<sharp>* (\<Psi>\<otimes>\<Psi>')" using \<open>(p\<bullet>yvec) \<sharp>* \<Psi>\<close> \<open>(p\<bullet>yvec) \<sharp>* \<Psi>'\<close>
              by auto
            moreover have "(p\<bullet>yvec) \<sharp>* (q\<bullet>P)" using \<open>(p\<bullet>yvec) \<sharp>* P\<close>
              apply(subst yvecdef[symmetric])
              by(subst fresh_star_bij)
            moreover have "(q\<bullet>xvec) \<sharp>* (\<Psi>\<otimes>\<Psi>')" using \<open>(q\<bullet>xvec) \<sharp>* \<Psi>\<close> \<open>(q\<bullet>xvec) \<sharp>* \<Psi>'\<close>
              by auto
            ultimately show ?thesis
              unfolding Pdef eqvts yvecdef
              by blast
          qed
          ultimately show ?thesis
            by(subst (1 2) resChainAlpha[where p=q and xvec=xvec])
        qed
        ultimately show ?case unfolding Req Teq
          apply(intro disjI1)
          by(subst (1 2) resChainAlpha[where p=p and xvec=yvec])
      qed
    next
      case(cSym \<Psi> P Q)
      then show ?case
        by(blast dest: bisimE)
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" "y \<sharp> Q"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(P \<parallel> ([(x, y)] \<bullet> Q)) \<sim> P \<parallel> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by auto
  then show ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close>
    apply(subst alphaRes[where x=x and y=y and P=Q], auto)
    by(subst alphaRes[where x=x and y=y and P="P \<parallel> Q"]) auto
qed

lemma bisimScopeExtChain:
  fixes xvec :: "name list"
    and \<Psi>    :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "xvec \<sharp>* \<Psi>"
  and   "xvec \<sharp>* P"

shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>Q)"
  using assms
  by(induct xvec) (auto intro: bisimScopeExt bisimReflexive bisimTransitive bisimResPres)

lemma bisimParAssoc:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<sim> P \<parallel> (Q \<parallel> R)"
proof -
  let ?X = "{(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) | \<Psi> xvec P Q R. xvec \<sharp>* \<Psi>}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  have "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
    by(clarsimp, rule exI[where x="[]"]) auto
  moreover have "eqvt ?X" by(force simp add: eqvt_def simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] eqvts)
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct')
    case(cStatEq \<Psi> PQR PQR')
    from \<open>(\<Psi>, PQR, PQR') \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and "PQR = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and "PQR' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* R"
      by(rule freshFrame[where C="(\<Psi>, Q, R)"]) auto
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q \<sharp>* R"
      by(rule freshFrame[where C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, R)"]) auto
    moreover obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
      by(rule freshFrame[where C="(\<Psi>, A\<^sub>P, \<Psi>\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>Q)"]) auto
    moreover from FrQ \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
      by(auto dest: extractFrameFreshChain)
    moreover from FrR \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(auto dest: extractFrameFreshChain)
    moreover from FrR \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(auto dest: extractFrameFreshChain)
    ultimately show ?case using freshCompChain
      by auto (metis frameChainAppend compositionSym Associativity frameNilStatEq frameResChainPres)
  next
    case(cSim \<Psi> T S)
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      and SEq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    from \<open>eqvt ?X\<close>have "eqvt ?Y" by blast
    have C1: "\<And>\<Psi> T S yvec. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; yvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y"
    proof -
      fix \<Psi> T S yvec
      assume "(\<Psi>, T, S) \<in> ?Y"
      then obtain T' S' where "\<Psi> \<rhd> T \<sim> T'" and "(\<Psi>, T', S') \<in> ?X" and "\<Psi> \<rhd> S' \<sim> S" by force
      assume "(yvec::name list) \<sharp>* \<Psi>"
      from \<open>(\<Psi>, T', S') \<in> ?X\<close> obtain xvec P Q R where T'eq: "T' = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)" and S'eq: "S' = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
        and "xvec \<sharp>* \<Psi>"
        by auto
      from \<open>\<Psi> \<rhd> T \<sim> T'\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>T \<sim> \<lparr>\<nu>*yvec\<rparr>T'" by(rule bisimResChainPres)
      moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*(yvec@xvec)\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*(yvec@xvec)\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X"
        by force
      with T'eq S'eq have "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T', \<lparr>\<nu>*yvec\<rparr>S') \<in> ?X" by(simp add: resChainAppend)
      moreover from \<open>\<Psi> \<rhd> S' \<sim> S\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*yvec\<rparr>S' \<sim> \<lparr>\<nu>*yvec\<rparr>S" by(rule bisimResChainPres)
      ultimately show "(\<Psi>, \<lparr>\<nu>*yvec\<rparr>T, \<lparr>\<nu>*yvec\<rparr>S) \<in> ?Y" by blast
    qed

    {
      fix y
      have "\<And>\<Psi> T S. \<lbrakk>(\<Psi>, T, S) \<in> ?Y; y \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>y\<rparr>T, \<lparr>\<nu>y\<rparr>S) \<in> ?Y"
        by(drule C1[where yvec2="[y]"]) auto
    }
    note C2 = this

    have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R) \<leadsto>[?Y] \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
    proof -
      have "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<leadsto>[?Y] P \<parallel> (Q \<parallel> R)"
      proof -
        note \<open>eqvt ?Y\<close>
        moreover have "\<And>\<Psi> P Q R. (\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
        proof -
          fix \<Psi> P Q R
          have "(\<Psi>::'b, ((P::('a, 'b, 'c) psi) \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?X"
            by(clarsimp, rule exI[where x="[]"]) auto
          then show "(\<Psi>, (P \<parallel> Q) \<parallel> R, P \<parallel> (Q \<parallel> R)) \<in> ?Y"
            by(blast intro: bisimReflexive)
        qed
        moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
        proof -
          fix xvec \<Psi> P Q R
          assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (P::('a, 'b, 'c) psi)"
          from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))"
            by(rule bisimScopeExtChain)
          ultimately show "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), P \<parallel> (\<lparr>\<nu>*xvec\<rparr>(Q \<parallel> R))) \<in> ?Y"
            by(blast intro: bisimReflexive)
        qed
        moreover have "\<And>xvec \<Psi> P Q R. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* R\<rbrakk> \<Longrightarrow> (\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"
        proof -
          fix xvec \<Psi> P Q R
          assume "(xvec::name list) \<sharp>* (\<Psi>::'b)" and "xvec \<sharp>* (R::('a, 'b, 'c) psi)"
          have "\<Psi> \<rhd> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisimParComm)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q))" by(rule bisimScopeExtChain)
          then have "\<Psi> \<rhd> R \<parallel> (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q))" by(rule bisimE)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (P \<parallel> Q)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
            by(metis bisimResChainPres bisimParComm)
          moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R), \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?X" by blast
          ultimately show "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) \<parallel> R, \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))) \<in> ?Y"  by(blast dest: bisimTransitive intro: bisimReflexive)
        qed
        ultimately show ?thesis using C1
          by(rule parAssocLeft)
      qed
      then show ?thesis using \<open>eqvt ?Y\<close> \<open>xvec \<sharp>* \<Psi>\<close> C1
        by(rule resChainPres)
    qed
    with TEq SEq show ?case by simp
  next
    case(cExt \<Psi> T S \<Psi>')
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      and SEq: "S = \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R))"
      by auto
    obtain p where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* R" and "(p \<bullet> xvec) \<sharp>* \<Psi>'"
      and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
      by(rule name_list_avoiding[where c="(\<Psi>, P, Q, R, \<Psi>')"]) auto

    from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R)), \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))) \<in> ?X"
      by auto
    moreover from TEq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "T = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(((p \<bullet> P) \<parallel> (p \<bullet> Q)) \<parallel> (p \<bullet> R))"
      apply clarsimp by(subst resChainAlpha[of p]) auto
    moreover from SEq \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "S = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> P) \<parallel> ((p \<bullet> Q) \<parallel> (p \<bullet> R)))"
      apply clarsimp by(subst resChainAlpha[of p]) auto
    ultimately show ?case by simp
  next
    case(cSym \<Psi> T S)
    from \<open>(\<Psi>, T, S) \<in> ?X\<close> obtain xvec P Q R where "xvec \<sharp>* \<Psi>" and TEq: "T = \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      and SEq: "\<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) = S"
      by auto

    from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> (Q \<parallel> R)) \<sim> \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P)"
      by(metis bisimParComm bisimParPres bisimTransitive bisimResChainPres)
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R \<parallel> Q) \<parallel> P), \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P))) \<in> ?X" by blast
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R \<parallel> (Q \<parallel> P)) \<sim> \<lparr>\<nu>*xvec\<rparr>((P \<parallel> Q) \<parallel> R)"
      by(metis bisimParComm bisimParPres bisimTransitive bisimResChainPres)
    ultimately show ?case using TEq SEq by(blast dest: bisimTransitive)
  qed
qed

lemma bisimParNil:
  fixes P :: "('a, 'b, 'c) psi"

shows "\<Psi> \<rhd> P \<parallel> \<zero> \<sim> P"
proof -
  let ?X1 = "{(\<Psi>, P \<parallel> \<zero>, P) | \<Psi> P. True}"
  let ?X2 = "{(\<Psi>, P, P \<parallel> \<zero>) | \<Psi> P. True}"
  let ?X = "?X1 \<union> ?X2"
  have "eqvt ?X" by(auto simp add: eqvt_def)
  have "(\<Psi>, P \<parallel> \<zero>, P) \<in> ?X" by simp
  then show ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> Q R)
    show ?case
    proof(cases "(\<Psi>, Q, R) \<in> ?X1")
      assume "(\<Psi>, Q, R) \<in> ?X1"
      then obtain P where "Q = P \<parallel> \<zero>" and "R = P" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
        by(rule freshFrame)
      ultimately show ?case
        apply clarsimp by(metis frameResChainPres frameNilStatEq Identity Associativity AssertionStatEqTrans Commutativity)
    next
      assume "(\<Psi>, Q, R) \<notin> ?X1"
      with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
      then obtain P where "Q = P" and "R = P \<parallel> \<zero>" by auto
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>"
        by(rule freshFrame)
      ultimately show ?case
        apply clarsimp by(metis frameResChainPres frameNilStatEq Identity Associativity AssertionStatEqTrans AssertionStatEqSym Commutativity)
    qed
  next
    case(cSim \<Psi> Q R)
    then show ?case using \<open>eqvt ?X\<close>
      by(auto intro: parNilLeft parNilRight)
  next
    case(cExt \<Psi> Q R \<Psi>')
    then show ?case by auto
  next
    case(cSym \<Psi> Q R)
    then show ?case by auto
  qed
qed

lemma bisimResNil:
  fixes x :: name
    and \<Psi> :: 'b

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
proof -
  {
    fix x::name
    assume "x \<sharp> \<Psi>"
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<sim> \<zero>"
    proof -
      let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X2 = "{(\<Psi>, \<zero>, \<lparr>\<nu>x\<rparr>\<zero>) | \<Psi> x. x \<sharp> \<Psi>}"
      let ?X = "?X1 \<union> ?X2"

      from \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>\<zero>, \<zero>) \<in> ?X" by auto
      then show ?thesis
      proof(coinduct rule: bisimWeakCoinduct)
        case(cStatEq \<Psi> P Q)
        then show ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
      next
        case(cSim \<Psi> P Q)
        then show ?case
          by(force intro: resNilLeft resNilRight)
      next
        case(cExt \<Psi> P Q \<Psi>')
        obtain y where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<noteq> x"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        show ?case
        proof(cases "(\<Psi>, P, Q) \<in> ?X1")
          assume "(\<Psi>, P, Q) \<in> ?X1"
          then obtain x where "P = \<lparr>\<nu>x\<rparr>\<zero>" and "Q = \<zero>" by auto
          moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alphaRes) auto
          ultimately show ?case using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> by auto
        next
          assume "(\<Psi>, P, Q) \<notin> ?X1"
          with \<open>(\<Psi>, P, Q) \<in> ?X\<close> have "(\<Psi>, P, Q) \<in> ?X2" by auto
          then obtain x where "Q = \<lparr>\<nu>x\<rparr>\<zero>" and "P = \<zero>" by auto
          moreover have "\<lparr>\<nu>x\<rparr>\<zero> = \<lparr>\<nu>y\<rparr> \<zero>" by(subst alphaRes) auto
          ultimately show ?case using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> by auto
        qed
      next
        case(cSym \<Psi> P Q)
        then show ?case by auto
      qed
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>\<zero> \<sim> \<zero>" by auto
  then show ?thesis by(subst alphaRes[where x=x and y=y]) auto
qed

lemma bisimOutputPushRes:
  fixes x :: name
    and \<Psi> :: 'b
    and M :: 'a
    and N :: 'a
    and P :: "('a, 'b, 'c) psi"

assumes "x \<sharp> M"
  and   "x \<sharp> N"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)) | \<Psi> x M N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"

    have "eqvt ?X"
      by(rule eqvtUnion) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+
    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> N\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P), M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P) \<in> ?X"
      by auto
    then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      then show ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      then show ?case using \<open>eqvt ?X\<close>
        by(auto intro!: outputPushResLeft outputPushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(cases "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x M N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Req: "R = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
          by(generate_fresh "name") (auto simp add: fresh_prod)

        moreover then have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
        moreover from Qeq \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "Q = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Req \<open>y \<sharp> P\<close> have "R = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x M N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P)" and Qeq: "Q = M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P"
          by(generate_fresh "name") (auto simp add: fresh_prod)

        moreover then have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)), M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by auto
        moreover from Req \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "R = \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Qeq \<open>y \<sharp> P\<close> have "Q = M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      then show ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" "y \<sharp> P"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<langle>N\<rangle>.([(x, y)] \<bullet> P)) \<sim> M\<langle>N\<rangle>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  then show ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close>
    apply(subst alphaRes[where x=x and y=y and P=P], auto)
    by(subst alphaRes[where x=x and y=y and P="M\<langle>N\<rangle>.P"]) auto
qed

lemma bisimInputPushRes:
  fixes x    :: name
    and \<Psi>    :: 'b
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a
    and P    :: "('a, 'b, 'c) psi"

assumes "x \<sharp> M"
  and   "x \<sharp> xvec"
  and   "x \<sharp> N"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
proof -
  {
    fix x::name and P::"('a, 'b, 'c) psi"
    assume "x \<sharp> \<Psi>" and "x \<sharp> M" and "x \<sharp> N" and "x \<sharp> xvec"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X2 = "{(\<Psi>, M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)) | \<Psi> x M xvec N P. x \<sharp> \<Psi> \<and> x \<sharp> M \<and> x \<sharp> xvec \<and> x \<sharp> N}"
    let ?X = "?X1 \<union> ?X2"

    have "eqvt ?X"
      by(rule eqvtUnion) (force simp add: eqvt_def pt_fresh_bij[OF pt_name_inst, OF at_name_inst] eqvts)+

    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> N\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P) \<in> ?X"
      by blast
    then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      then show ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      then show ?case using \<open>eqvt ?X\<close>
        by(auto intro!: inputPushResLeft inputPushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(cases "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x M xvec N P where Qeq: "Q = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Req: "R = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
          and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
          by(generate_fresh "name") (auto simp add: fresh_prod)

        moreover then have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by force
        moreover from Qeq \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "Q = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts inputChainFresh)
        moreover from Req \<open>y \<sharp> P\<close> have "R = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x M xvec N P where Req: "R = \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P)" and Qeq: "Q = M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<Psi>"
          and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> N" by auto
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
          by(generate_fresh "name") (auto simp add: fresh_prod)

        moreover then have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)), M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)) \<in> ?X" by force
        moreover from Req \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> N\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> P\<close> have "R = \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts inputChainFresh)
        moreover from Qeq \<open>y \<sharp> P\<close> have "Q = M\<lparr>\<lambda>*xvec N \<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      then show ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> P" and "y \<sharp> xvec"
    by(generate_fresh "name") auto
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.([(x, y)] \<bullet> P)) \<sim> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by auto
  then show ?thesis using assms \<open>y \<sharp> P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> N\<close> \<open>y \<sharp> xvec\<close>
    apply(subst alphaRes[where x=x and y=y and P=P], auto)
    by(subst alphaRes[where x=x and y=y and P="M\<lparr>\<lambda>*xvec N\<rparr>.P"]) (auto simp add: inputChainFresh eqvts)
qed

lemma bisimCasePushRes:
  fixes x  :: name
    and \<Psi>  :: 'b
    and Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

assumes "x \<sharp> (map fst Cs)"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
proof -
  {
    fix x::name and Cs::"('c \<times> ('a, 'b, 'c) psi) list"
    assume "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)"
    let ?X1 = "{(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X2 = "{(\<Psi>, Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs), \<lparr>\<nu>x\<rparr>(Cases Cs)) | \<Psi> x Cs. x \<sharp> \<Psi> \<and> x \<sharp> (map fst Cs)}"
    let ?X = "?X1 \<union> ?X2"

    have "eqvt ?X"
    proof
      show "eqvt ?X1"
        apply(clarsimp simp add: eqvt_def eqvts)
        apply (rule exI)
        apply (rule exI)
        apply (rule conjI)
         apply (rule refl)
        apply(perm_extend_simp)
          apply(clarsimp simp add: eqvts)
         apply (simp add: fresh_bij)
        apply(drule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
        apply(drule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
       apply(simp add: eqvts)
        apply(perm_extend_simp)
        apply(simp add: eqvts)
        done
    next
      show "eqvt ?X2"
        apply(clarsimp simp add: eqvt_def eqvts)
        apply (rule exI)
        apply (rule exI)
        apply (subst conj_commute)
        apply (rule conjI)
        apply (rule conjI)
          apply (rule refl)
         apply(perm_extend_simp)
          apply (simp add: fresh_bij)
         apply(drule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
         apply(drule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
         apply(simp add: eqvts)
         apply(perm_extend_simp)
         apply(simp add: eqvts)
        apply(perm_extend_simp)
        apply(clarsimp simp add: eqvts)
        done
    qed

    from \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> map fst Cs\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>(Cases Cs), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)) \<in> ?X" by auto
    then have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    proof(coinduct rule: bisimCoinduct)
      case(cStatEq \<Psi> Q R)
      then show ?case using freshComp by(force intro: frameResFresh FrameStatEqSym)
    next
      case(cSim \<Psi> Q R)
      then show ?case using \<open>eqvt ?X\<close>
        by(auto intro!: casePushResLeft casePushResRight bisimReflexive)
    next
      case(cExt \<Psi> Q R \<Psi>')
      show ?case
      proof(cases "(\<Psi>, Q, R) \<in> ?X1")
        assume "(\<Psi>, Q, R) \<in> ?X1"
        then obtain x Cs where Qeq: "Q = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Req: "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        from \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)

        moreover with \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
          by auto
        moreover from Qeq \<open>y \<sharp> Cs\<close> have "Q = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Req \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "R = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))"
          by(induct Cs arbitrary: R) (auto simp add: fresh_list_cons fresh_prod alphaRes)
        ultimately show ?case by blast
      next
        assume "(\<Psi>, Q, R) \<notin> ?X1"
        with \<open>(\<Psi>, Q, R) \<in> ?X\<close> have "(\<Psi>, Q, R) \<in> ?X2" by blast
        then obtain x Cs where Req: "R = \<lparr>\<nu>x\<rparr>(Cases Cs)" and Qeq: "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
          and "x \<sharp> \<Psi>" and "x \<sharp> (map fst Cs)" by blast
        obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> \<Psi>'" and "y \<sharp> Cs"
          by(generate_fresh "name") (auto simp add: fresh_prod)
        from \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "y \<sharp> map fst ([(x, y)] \<bullet> Cs)" by(induct Cs) (auto simp add: fresh_list_cons fresh_list_nil)

        moreover with \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>'\<close> have "(\<Psi> \<otimes> \<Psi>', \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)), Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))) \<in> ?X"
          by auto
        moreover from Req \<open>y \<sharp> Cs\<close> have "R = \<lparr>\<nu>y\<rparr>(Cases([(x, y)] \<bullet> Cs))"
          apply clarsimp by(subst alphaRes[of y]) (auto simp add: eqvts)
        moreover from Qeq \<open>y \<sharp> Cs\<close> \<open>x \<sharp> (map fst Cs)\<close> have "Q = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))"
          by(induct Cs arbitrary: Q) (auto simp add: fresh_list_cons fresh_prod alphaRes)
        ultimately show ?case by blast
      qed
    next
      case(cSym \<Psi> R Q)
      then show ?case by blast
    qed
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> Cs" by(generate_fresh "name") auto
  moreover from \<open>x \<sharp> map fst Cs\<close> have "y \<sharp> map fst([(x, y)] \<bullet> Cs)"
    by(induct Cs) (auto simp add: fresh_left calc_atm)
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) \<sim> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs))"
    by auto
  moreover from \<open>y \<sharp> Cs\<close> have "\<lparr>\<nu>y\<rparr>(Cases ([(x, y)] \<bullet> Cs)) =  \<lparr>\<nu>x\<rparr>(Cases Cs)"
    by(simp add: alphaRes eqvts)
  moreover from \<open>x \<sharp> map fst Cs\<close> \<open>y \<sharp> Cs\<close> have "Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>y\<rparr>P)) ([(x, y)] \<bullet> Cs)) = Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
    by(induct Cs) (auto simp add: alphaRes)
  ultimately show ?thesis by auto
qed

lemma bangExt:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"

assumes "guarded P"

shows "\<Psi> \<rhd> !P \<sim> P \<parallel> !P"
proof -
  let ?X = "{(\<Psi>, !P, P \<parallel> !P) | \<Psi> P. guarded P} \<union> {(\<Psi>, P \<parallel> !P, !P) | \<Psi> P. guarded P}"
  from \<open>guarded P\<close> have "(\<Psi>, !P, P \<parallel> !P) \<in> ?X" by auto
  then show ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> Q R)
    from \<open>(\<Psi>, Q, R) \<in> ?X\<close> obtain P where Eq: "(Q = !P \<and> R = P \<parallel> !P) \<or> (Q = P \<parallel> !P \<and> R = !P)" and "guarded P"
      by auto
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
    from FrP \<open>guarded P\<close> have "\<Psi>\<^sub>P \<simeq> SBottom'" by(blast dest: guardedStatEq)
    from \<open>\<Psi>\<^sub>P \<simeq> SBottom'\<close> have "\<Psi> \<otimes> SBottom' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> SBottom'" by(metis Identity Composition AssertionStatEqTrans Commutativity AssertionStatEqSym)
    then have "\<langle>A\<^sub>P, \<Psi> \<otimes> SBottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> SBottom'\<rangle>"
      by(force intro: frameResChainPres)
    moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "\<langle>\<epsilon>, \<Psi> \<otimes> SBottom'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> SBottom'\<rangle>"
      apply -
      by(rule FrameStatEqSym) (simp add: frameResFreshChain freshCompChain(1))
    ultimately show ?case using Eq \<open>A\<^sub>P \<sharp>* \<Psi>\<close> FrP
      by auto (blast dest: FrameStatEqTrans FrameStatEqSym)+
  next
    case(cSim \<Psi> Q R)
    then show ?case by(auto intro: bangExtLeft bangExtRight bisimReflexive)
  next
    case(cExt \<Psi> Q R)
    then show ?case by auto
  next
    case(cSym \<Psi> Q R)
    then show ?case by auto
  qed
qed

lemma bisimScopeExtSym:
  fixes x :: name
    and Q :: "('a, 'b, 'c) psi"
    and P :: "('a, 'b, 'c) psi"

assumes "x \<sharp> \<Psi>"
  and   "x \<sharp> Q"

shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>x\<rparr>P) \<parallel> Q"
  using assms
  by(metis bisimScopeExt bisimTransitive bisimParComm bisimSymmetric bisimResPres)

lemma bisimScopeExtChainSym:
  fixes xvec :: "name list"
    and Q    :: "('a, 'b, 'c) psi"
    and P    :: "('a, 'b, 'c) psi"

assumes "xvec \<sharp>* \<Psi>"
  and   "xvec \<sharp>* Q"

shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<sim> (\<lparr>\<nu>*xvec\<rparr>P) \<parallel> Q"
  using assms
  by(induct xvec) (auto intro: bisimScopeExtSym bisimReflexive bisimTransitive bisimResPres)

lemma bisimParPresAuxSym:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"
    and R :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<sim> Q"
  and   "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and   "A\<^sub>R \<sharp>* \<Psi>"
  and   "A\<^sub>R \<sharp>* P"
  and   "A\<^sub>R \<sharp>* Q"

shows "\<Psi> \<rhd> R \<parallel> P \<sim> R \<parallel> Q"
  using assms
  by(metis bisimParComm bisimParPresAux bisimTransitive)

lemma bangDerivative:
  fixes \<Psi>   :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and P'   :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
  and   "\<Psi> \<rhd> P \<sim> Q"
  and   "bn \<alpha> \<sharp>* \<Psi>"
  and   "bn \<alpha> \<sharp>* P"
  and   "bn \<alpha> \<sharp>* Q"
  and   "bn \<alpha> \<sharp>* subject \<alpha>"
  and   "guarded Q"

obtains Q' R T where "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
  and "((supp R)::name set) \<subseteq> supp P'" and "((supp T)::name set) \<subseteq> supp Q'"
proof -
  from \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> have "guarded P"
    apply -
    by(ind_cases "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: psi.inject)
  assume "\<And>Q' R T. \<lbrakk>\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'; \<Psi> \<rhd> P' \<sim> R \<parallel> !P; \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q; \<Psi> \<rhd> R \<sim> T; ((supp R)::name set) \<subseteq> supp P';
                    ((supp T)::name set) \<subseteq> supp Q'\<rbrakk> \<Longrightarrow> thesis"
  moreover from \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>guarded Q\<close>
  have "\<exists>Q' T R . \<Psi> \<rhd> !Q \<longmapsto>\<alpha>  \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and> \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and> \<Psi> \<rhd> R \<sim> T \<and>
                  ((supp R)::name set) \<subseteq> supp P' \<and> ((supp T)::name set) \<subseteq> supp Q'"
  proof(nominal_induct avoiding: Q rule: bangInduct')
    case(cAlpha \<alpha> P' p Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from QTrans have "distinct(bn \<alpha>)"
      by(rule boundOutputDistinct)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"
      by fact
    from QTrans \<open>bn(p \<bullet> \<alpha>) \<sharp>* Q\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "bn(p \<bullet> \<alpha>) \<sharp>* Q'"
      by(drule_tac freeFreshChainDerivative) simp+
    with QTrans \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> S \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "\<Psi> \<rhd> !Q \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> Q')"
      by(force simp add: residualAlpha)
    moreover from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P') \<sim> (p \<bullet> (R \<parallel> (P \<parallel> !P)))"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* P\<close> S have "\<Psi> \<rhd> (p \<bullet> P') \<sim> (p \<bullet> R) \<parallel> (P \<parallel> !P)"
      by(simp add: eqvts)
    moreover from \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> (T \<parallel> !Q))"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* Q\<close> S have "\<Psi> \<rhd> (p \<bullet> Q') \<sim> (p \<bullet> T) \<parallel> !Q"
      by(simp add: eqvts)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(rule bisimClosed)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> S have "\<Psi> \<rhd> (p \<bullet> R) \<sim> (p \<bullet> T)"
      by(simp add: eqvts)
    moreover from suppR have "((supp(p \<bullet> R))::name set) \<subseteq> supp(p \<bullet> P')"
      apply(erule_tac rev_mp)
      by(subst subsetClosed[of p, symmetric]) (simp add: eqvts)
    moreover from suppT have "((supp(p \<bullet> T))::name set) \<subseteq> supp(p \<bullet> Q')"
      apply(erule_tac rev_mp)
      by(subst subsetClosed[of p, symmetric]) (simp add: eqvts)
    ultimately show ?case by blast
  next
    case(cPar1 \<alpha> P' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close>
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(blast dest: bisimE simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
      by(metis statEqTransition Identity AssertionStatEqSym)
    then have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<alpha> \<prec> (Q' \<parallel> !Q)"
      using \<open>bn \<alpha> \<sharp>* Q\<close> by(intro Par1) (assumption | simp)+
    then have "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> (Q' \<parallel> !Q)"
      using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>guarded P\<close> have "\<Psi> \<rhd> P' \<parallel> !P \<sim> P' \<parallel> (P \<parallel> !P)"
      by(metis bangExt bisimParPresSym)
    moreover have "\<Psi> \<rhd> Q' \<parallel> !Q \<sim> Q' \<parallel> !Q"
      by(rule bisimReflexive)
    ultimately show ?case using \<open>\<Psi> \<rhd> P' \<sim> Q'\<close>
      by(force simp add: psi.supp)
  next
    case(cPar2 \<alpha> P' Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q"
      and "\<Psi> \<rhd> R \<sim> T" and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    note QTrans
    from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> !P\<close> have "\<Psi> \<rhd> P \<parallel> P' \<sim> R \<parallel> (P \<parallel> !P)"
      by(metis bisimParPresSym bisimParComm bisimTransitive bisimParAssoc)
    with QTrans show ?case using \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> \<open>\<Psi> \<rhd> R \<sim> T\<close> suppR suppT
      by(force simp add: psi.supp)
  next
    case(cComm1 M N P' K xvec P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> Q \<leadsto>[bisim] P"
      by(metis bisimE)
    with \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      by(force dest: simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"
      by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M"
      by(rule freshFrame[where C="(\<Psi>, Q, M)"]) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'"
      by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''\<close> \<open>xvec \<sharp>* K\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>guarded Q\<close>
    obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''"
      using cComm1 by force
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''"
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> SBottom' \<turnstile> M \<leftrightarrow> K"
      by(metis statEqEnt Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close>
      by(intro Comm1) (assumption | simp)+
    then have "\<Psi> \<rhd> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))"
      using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisimScopeExtChainSym bisimTransitive psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres bisimScopeExtChainSym psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> Q' \<sim> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisimParPresSym bisimTransitive bisimResChainPres bisimParComm bisimE(4))
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  next
    case(cComm2 M xvec N P' K P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close>
    obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> Q'"
      by(metis bisimE simE bn.simps)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M"
      by(rule freshFrame[where C="(\<Psi>, Q, M)"]) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'"
      by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>guarded Q\<close>
    obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''" using cComm2
      by force
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q''"
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> SBottom' \<turnstile> M \<leftrightarrow> K"
      by(metis statEqEnt Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close>
      by(intro Comm2) (assumption | simp)+
    then have "\<Psi> \<rhd> !Q \<longmapsto>\<tau> \<prec> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q''))" using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> \<lparr>\<nu>*xvec\<rparr>((P' \<parallel> R) \<parallel> (P \<parallel> !P))"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)) \<parallel> (P \<parallel> !P)"
      by(metis bisimScopeExtChainSym bisimTransitive psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'') \<sim> (\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric bisimResChainPres bisimScopeExtChainSym psiFreshVec)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> P' \<sim> Q'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R) \<sim> \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)"
      by(metis bisimParPresSym bisimTransitive bisimResChainPres bisimParComm)
    moreover from suppR have "((supp(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'')))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> T)))::name set) \<subseteq>  supp((\<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> Q'')))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  next
    case(cBang \<alpha> P' Q)
    then obtain Q' T R where QTrans: "\<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and "\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)" and "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T"
      and suppR: "((supp R)::name set) \<subseteq> supp P'" and suppT: "((supp T)::name set) \<subseteq> supp Q'"
      by blast
    from \<open>\<Psi> \<rhd> P' \<sim> R \<parallel> (P \<parallel> !P)\<close> \<open>guarded P\<close> have "\<Psi> \<rhd> P' \<sim> R \<parallel> !P"
      by(metis bangExt bisimParPresSym bisimTransitive bisimSymmetric)
    with QTrans show ?case using \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close> \<open>\<Psi> \<rhd> R \<sim> T\<close> suppR suppT
      by blast
  next
    case(cBrMerge M N P' P'' Q)
    then obtain Q' T R where "\<Psi> \<rhd> !Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'" and
      p''eq: "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and
      "\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q" and "\<Psi> \<rhd> R \<sim> T" and
      "supp R \<subseteq> (supp P''::name set)" and
      "supp T \<subseteq> (supp Q'::name set)"
      by blast
    obtain Q'' where "\<Psi> \<rhd> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q''" and "\<Psi> \<rhd> Q'' \<sim> P'"
    proof -
      assume g: "(\<And>Q''. \<lbrakk>\<Psi> \<rhd> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q''; \<Psi> \<rhd> Q'' \<sim> P'\<rbrakk> \<Longrightarrow> thesis)"
      have "\<exists>Q'. \<Psi> \<rhd> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q' \<and> (\<Psi>, Q', P') \<in> bisim"
        apply(rule simE)
           apply(rule bisimE)
           apply(rule bisimSymmetric)
        by fact+
      then show thesis
        using g by blast
    qed
    have "\<Psi> \<otimes> \<one> \<rhd> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q''" using \<open>\<Psi> \<rhd> Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q''\<close>
      by(rule statEqTransition) (rule AssertionStatEqSym[OF Identity])
    obtain A\<^sub>Q \<Psi>\<^sub>Q where "extractFrame Q = \<langle>A\<^sub>Q,\<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M"
      by(rule freshFrame[where C="(\<Psi>,Q,M)"]) force
    then have "\<Psi>\<^sub>Q \<simeq> \<one>" using \<open>guarded Q\<close>
      by(auto dest: guardedStatEq)
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'" using \<open>\<Psi> \<rhd> !Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'\<close>
      by(rule statEqTransition) (metis \<open>\<Psi>\<^sub>Q \<simeq> \<one>\<close> AssertionStatEqTrans AssertionStatEqSym Identity compositionSym)
    have "\<Psi> \<rhd> !Q \<longmapsto> \<questiondown>M\<lparr>N\<rparr> \<prec> Q'' \<parallel> Q'"
      by(rule Bang) (rule BrMerge|fact|simp)+
    moreover have "\<Psi> \<rhd> P' \<parallel> P'' \<sim> (P' \<parallel> R) \<parallel> (P \<parallel> !P)"
      apply(rule bisimTransitive[OF bisimParPresSym, OF p''eq])
      apply(rule bisimTransitive[OF bisimSymmetric, OF bisimParAssoc])
      apply(rule bisimParPresSym)
      apply(rule bangExt[OF \<open>guarded P\<close>])
      done
    moreover have "\<Psi> \<rhd> Q'' \<parallel> Q' \<sim> Q'' \<parallel> T \<parallel> !Q" using \<open>\<Psi> \<rhd> Q' \<sim> T \<parallel> !Q\<close>
      by(metis bisimTransitive bisimParAssoc bisimParComm bisimParPres bisimSymmetric)
    moreover have "\<Psi> \<rhd> (P' \<parallel> R) \<sim> Q'' \<parallel> T" using \<open>\<Psi> \<rhd> R \<sim> T\<close> and \<open>\<Psi> \<rhd> Q'' \<sim> P'\<close>
      apply -
      apply(erule bisimTransitive[OF bisimParPres, OF bisimSymmetric])
      apply(erule bisimTransitive[OF bisimParPresSym])
      by(rule bisimReflexive)
    moreover have "supp(P' \<parallel> R) \<subseteq> (supp(P'\<parallel>P'')::name set)"
      using \<open>supp R \<subseteq> (supp P''::name set)\<close> by(auto simp add: psi.supp)
    moreover have "supp(Q'' \<parallel> T) \<subseteq> (supp(Q'' \<parallel> Q')::name set)"
      using \<open>supp T \<subseteq> (supp Q'::name set)\<close> by(auto simp add: psi.supp)
    ultimately show ?case
      by blast
  next
    case(cBrComm1 M N P' xvec P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> Q \<leadsto>[bisim] P" by(metis bisimE)
    with \<open>\<Psi> \<rhd> P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P'\<close> obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      by(force dest: simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q'"
      by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M"
      by(rule freshFrame[where C="(\<Psi>, Q, M)"]) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'"
      by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>guarded Q\<close>
    obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q"
      and "\<Psi> \<rhd> R \<sim> T" and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''"
      using cBrComm1 by force
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q''"
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q' \<parallel> Q''"
      using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close> by(intro BrComm1) (assumption | simp)+
    then have "\<Psi> \<rhd> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q' \<parallel> Q''"
      using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> P' \<parallel> P'' \<sim> (P' \<parallel> R) \<parallel> (P \<parallel> !P)"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> Q' \<parallel> Q'' \<sim> (Q' \<parallel> T) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> Q' \<sim> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> P' \<parallel> R \<sim> Q' \<parallel> T"
      by(metis bisimParPresSym bisimTransitive bisimParComm bisimE(4))
    moreover from suppR have "((supp(P' \<parallel> R))::name set) \<subseteq>  supp((P' \<parallel> P''))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(Q' \<parallel> T))::name set) \<subseteq>  supp((Q' \<parallel> Q''))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  next
    case(cBrComm2 M N P' xvec P'' Q)
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> Q \<leadsto>[bisim] P" by(metis bisimE)
    with \<open>\<Psi> \<rhd> P \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> P'"
      using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> by(auto dest: simE)
    from QTrans have "\<Psi> \<otimes> SBottom' \<rhd> Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
      by(metis statEqTransition Identity AssertionStatEqSym)
    moreover obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* M"
      by(rule freshFrame[where C="(\<Psi>, Q, M)"]) auto
    note FrQ
    moreover from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> SBottom'" by(blast dest: guardedStatEq)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> P''\<close> \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>guarded Q\<close>
    obtain Q'' T R where QTrans': "\<Psi> \<rhd> !Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q''" and "\<Psi> \<rhd> P'' \<sim> R \<parallel> !P" and "\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q"
      and "\<Psi> \<rhd> R \<sim> T" and suppR: "((supp R)::name set) \<subseteq> supp P''" and suppT: "((supp T)::name set) \<subseteq> supp Q''"
      using cBrComm2 by force
    from QTrans' \<open>\<Psi>\<^sub>Q \<simeq> SBottom'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> !Q \<longmapsto>\<questiondown>M\<lparr>N\<rparr> \<prec> Q''"
      by(metis statEqTransition Identity compositionSym AssertionStatEqSym)
    ultimately have "\<Psi> \<rhd> Q \<parallel> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q' \<parallel> Q''"
      using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close> by(intro BrComm2) (assumption | simp)+
    then have "\<Psi> \<rhd> !Q \<longmapsto>\<exclamdown>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q' \<parallel> Q''"
      using \<open>guarded Q\<close> by(rule Bang)
    moreover from \<open>\<Psi> \<rhd> P'' \<sim> R \<parallel> !P\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> P' \<parallel> P'' \<sim> (P' \<parallel> R) \<parallel> (P \<parallel> !P)"
      by(metis bisimParPresSym bangExt bisimTransitive bisimParAssoc bisimSymmetric)
    moreover from \<open>\<Psi> \<rhd> Q'' \<sim> T \<parallel> !Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> have "\<Psi> \<rhd> Q' \<parallel> Q'' \<sim> (Q' \<parallel> T) \<parallel> !Q"
      by(metis bisimParPresSym bisimTransitive bisimParAssoc bisimSymmetric)
    moreover from \<open>\<Psi> \<rhd> R \<sim> T\<close> \<open>\<Psi> \<rhd> Q' \<sim> P'\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> P' \<parallel> R \<sim> Q' \<parallel> T"
      by(metis bisimParPresSym bisimTransitive bisimParComm bisimE(4))
    moreover from suppR have "((supp(P' \<parallel> R))::name set) \<subseteq>  supp((P' \<parallel> P''))"
      by(auto simp add: psi.supp resChainSupp)
    moreover from suppT have "((supp(Q' \<parallel> T))::name set) \<subseteq>  supp((Q' \<parallel> Q''))"
      by(auto simp add: psi.supp resChainSupp)
    ultimately show ?case by blast
  qed
  ultimately show ?thesis by blast
qed

lemma structCongBisim:
  fixes P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "P \<equiv>\<^sub>s Q"

shows "P \<sim> Q"
  using assms
  by(induct rule: structCong.induct)
    (auto intro: bisimReflexive bisimSymmetric bisimTransitive bisimParComm bisimParAssoc bisimParNil bisimResNil bisimResComm bisimScopeExt bisimCasePushRes bisimInputPushRes bisimOutputPushRes bangExt)

lemma bisimBangPres:
  fixes \<Psi> :: 'b
    and P :: "('a, 'b, 'c) psi"
    and Q :: "('a, 'b, 'c) psi"

assumes "\<Psi> \<rhd> P \<sim> Q"
  and   "guarded P"
  and   "guarded Q"

shows "\<Psi> \<rhd> !P \<sim> !Q"
proof -
  let ?X = "{(\<Psi>, R \<parallel> !P, R \<parallel> !Q) | \<Psi> P Q R. \<Psi> \<rhd> P \<sim> Q \<and> guarded P \<and> guarded Q}"
  let ?Y = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> ?X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from assms have "(\<Psi>, \<zero> \<parallel> !P, \<zero> \<parallel> !Q) \<in> ?X" by(blast intro: bisimReflexive)

  moreover have "eqvt ?X"
    apply(clarsimp simp add: eqvt_def)
    apply(drule bisimClosed)
    by force
  ultimately have "\<Psi> \<rhd> \<zero> \<parallel> !P \<sim> \<zero> \<parallel> !Q"
  proof(coinduct rule: weakTransitiveCoinduct)
    case(cStatEq \<Psi> P Q)
    then show ?case by auto
  next
    case(cSim \<Psi> RP RQ)
    from \<open>(\<Psi>, RP, RQ) \<in> ?X\<close> obtain P Q R where "\<Psi> \<rhd> P \<sim> Q" and "guarded P" and "guarded Q"
      and "RP = R \<parallel> !P" and "RQ = R \<parallel> !Q"
      by auto
    note \<open>\<Psi> \<rhd> P \<sim> Q\<close>
    moreover from \<open>eqvt ?X\<close> have "eqvt ?Y" by blast
    moreover note \<open>guarded P\<close> \<open>guarded Q\<close> bisimE(2) bisimE(3) bisimE(4) statEqBisim bisimClosed bisimParAssoc[THEN bisimSymmetric]
      bisimParPres bisimParPresAuxSym bisimResChainPres bisimScopeExtChainSym bisimTransitive
    moreover have "\<And>\<Psi> P Q R T. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> ?Y; \<Psi> \<rhd> R \<sim> T\<rbrakk> \<Longrightarrow> (\<Psi>, P, T) \<in> ?Y"
      by auto (metis bisimTransitive)
    moreover have "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; guarded P; guarded Q\<rbrakk> \<Longrightarrow> (\<Psi>, R \<parallel> !P, R \<parallel> !Q) \<in> ?Y" by(blast intro: bisimReflexive)
    moreover have "\<And>\<Psi> P \<alpha> P' Q. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; \<Psi> \<rhd> P \<sim> Q; bn \<alpha> \<sharp>* \<Psi>;  bn \<alpha> \<sharp>* P;  bn \<alpha> \<sharp>* Q; guarded Q; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                         \<exists>Q' R T.  \<Psi> \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q' \<and> \<Psi> \<rhd> P' \<sim> R \<parallel> !P \<and>  \<Psi> \<rhd> Q' \<sim> T \<parallel> !Q \<and>
                                                   \<Psi> \<rhd> R \<sim> T \<and> ((supp R)::name set) \<subseteq> supp P' \<and>
                                                   ((supp T)::name set) \<subseteq> supp Q'"
      by(blast elim: bangDerivative)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[?Y] R \<parallel> !Q"
      by(rule bangPres)
    with \<open>RP = R \<parallel> !P\<close> \<open>RQ = R \<parallel> !Q\<close> show ?case
      by blast
  next
    case(cExt \<Psi> RP RQ \<Psi>')
    then show ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> RP RQ)
    then show ?case by(blast dest: bisimE)
  qed
  then show ?thesis
    by(metis bisimTransitive bisimParNil bisimSymmetric bisimParComm)
qed

end

end
