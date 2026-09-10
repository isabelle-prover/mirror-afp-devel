theory AlphabetReduction_ForwardAdvance
  imports AlphabetReduction_ForwardWrite
begin

subsection \<open>Advance phase\<close>

text \<open>Relation-generic advance left-walk loop scaffold.  The
  chain over \<open>R'\<close> is built natively by
  \<open>relpow_invariant_chain\<close> from the per-step leaf contract
  supplied as the \<open>leaf\<close> hypothesis; the union-relation
  \<open>ar_advance_walk_loop\<close> and the sub-relation
  \<open>ar_advance_walk_loop_in_sub\<close> are both thin instantiations,
  discharging \<open>leaf\<close> by \<open>ar_advance_walk_step\<close> and
  \<open>ar_advance_walk_step_in_sub\<close> respectively.  No
  \<open>stays\<close> side-condition arises: the chain is native to
  \<open>R'\<close> rather than lifted from the union relation, so the
  leaf-parametric scaffold applies
  where a union-to-sub chain lift would not.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

lemma ar_advance_walk_loop_gen:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf:
        "\<And>cc i. \<lbrakk> valid_mttm M;
                   mt_state cc = (q, AR_SimAdvance, tk, i, buf, dvec, posk);
                   q \<in> Q_tm M;
                   mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                   Suc i < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk);
                   ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk);
                   \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                   ar_stage_bounded (bl_tm M) (k_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk) \<rbrakk>
                 \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                          \<and> mt_state c'' = (q, AR_SimAdvance, tk, Suc i, buf, dvec, posk)
                          \<and> mt_tape c'' = mt_tape cc
                          \<and> mt_pos c'' = (mt_pos cc)(tk := mt_pos cc tk - 1)"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and ndisp: "n < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>j. j < n \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - j) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> R' ^^ n
              \<and> mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
              \<and> mt_pos c' tk = mt_pos c0 tk - n
              \<and> mt_tape c' = mt_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k')"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "mt_pos c0 tk"
  have kpos: "0 < ?k" using block_width_pos[of "\<Gamma>_tm M"] by simp
  let ?P = "\<lambda>j c.
       mt_state c = (q, AR_SimAdvance, tk, j, buf, dvec, posk)
     \<and> mt_pos c tk = ?start - j
     \<and> mt_tape c = mt_tape c0
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c k' = mt_pos c0 k')"
  have mybase: "?P 0 c0" using stg by simp
  have mystep:
      "\<And>j cc. \<lbrakk> j < n; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < n" and Pj: "?P j cc"
    from Pj have st_cc:
        "mt_state cc = (q, AR_SimAdvance, tk, j, buf, dvec, posk)"
      and pos_cc: "mt_pos cc tk = ?start - j"
      and tape_cc: "mt_tape cc = mt_tape c0"
      and other_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos cc k' = mt_pos c0 k'"
      by simp_all
    have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cc: "\<forall>j' \<ge> k_tm M. mt_tape cc j' (mt_pos cc j') = BLANK4"
    proof (intro allI impI)
      fix j' assume jge: "k_tm M \<le> j'"
      have jne: "j' \<noteq> tk" using jge tk_lt by simp
      have "mt_tape cc j' (mt_pos cc j') = mt_tape c0 j' (mt_pos c0 j')"
        using tape_cc other_cc jne by simp
      thus "mt_tape cc j' (mt_pos cc j') = BLANK4" using pad0 jge by simp
    qed
    have src_cc: "ar_stage_bounded (bl_tm M) (k_tm M)
                    (AR_SimAdvance, tk, j, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have sucj_lt: "Suc j < ?D" using jlt ndisp by linarith
    have j_lt2k: "j < 2 * ?k"
      using sucj_lt ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrc_cc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, j, buf, dvec, posk)"
      using j_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have notLE_cc: "mt_tape cc tk (mt_pos cc tk) \<noteq> LE4"
      using tape_cc pos_cc notLE[OF jlt] by simp
    obtain c'' where
        bstep: "(cc, c'') \<in> R'"
      and bst_state: "mt_state c'' = (q, AR_SimAdvance, tk, Suc j, buf, dvec, posk)"
      and bst_tape: "mt_tape c'' = mt_tape cc"
      and bst_pos: "mt_pos c'' = (mt_pos cc)(tk := mt_pos cc tk - 1)"
      using leaf[OF vM st_cc qQ notLE_cc sucj_lt vsrc_cc pad_cc src_cc] by blast
    have pos_eq: "mt_pos c'' tk = ?start - Suc j"
      using bst_pos pos_cc by simp
    have tape_eq: "mt_tape c'' = mt_tape c0" using bst_tape tape_cc by simp
    have other_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c'' k' = mt_pos c0 k'"
      using bst_pos other_cc by simp
    show "\<exists>c''. (cc, c'') \<in> R'
                \<and> ?P (Suc j) c''"
      using bstep bst_state pos_eq tape_eq other_eq by blast
  qed
  have loop:
      "\<exists>c'. (c0, c') \<in> R' ^^ n
            \<and> ?P n c'"
    by (rule relpow_invariant_chain
          [where P = ?P and n = n, OF mystep mybase])
  obtain c' where
      chain: "(c0, c') \<in> R' ^^ n"
    and Pfin: "?P n c'"
    using loop by blast
  show ?thesis
  proof (intro exI[where x = c'] conjI)
    show "(c0, c') \<in> R' ^^ n" by (rule chain)
    show "mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)"
      using Pfin by simp
    show "mt_pos c' tk = ?start - n" using Pfin by simp
    show "mt_tape c' = mt_tape c0" using Pfin by simp
    show "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k'" using Pfin by simp
  qed
qed

text \<open>The advance left-walk loop, proper tape.  From an
  \<open>AR_SimAdvance\<close> stage at bit-counter \<open>0\<close> with the head
  at \<open>start\<close>, \<open>n\<close> \<open>M'\<close>-steps walk the head
  \<open>n\<close> cells \<open>L\<close> (counter \<open>0 \<rightarrow> n\<close>), the tape
  and all other heads unchanged.  Each \<open>ar_advance_walk_step\<close>'s
  \<open>\<noteq> LE4\<close> guard reads the current cell
  \<open>start - j\<close>, supplied \<open>\<noteq> LE4\<close> by \<open>notLE\<close>;
  the per-step displacement bound \<open>Suc j < D\<close> follows from
  \<open>n < D\<close> by \<open>linarith\<close>.  Unlike the write loops this loop
  does not mutate the tape (advance only moves heads), so the invariant
  keeps \<open>mt_tape c = mt_tape c0\<close> constant.  Chain length
  \<open>n\<close>.\<close>

lemma ar_advance_walk_loop:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and ndisp: "n < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>j. j < n \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - j) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (alphabet_reduce_delta M)) ^^ n
              \<and> mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
              \<and> mt_pos c' tk = mt_pos c0 tk - n
              \<and> mt_tape c' = mt_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0 k')"
  by (rule ar_advance_walk_loop_gen
        [OF ar_advance_walk_step vM qQ stg buf_valid ndisp notLE
            pad0 src0])

text \<open>Relation-generic unified single-tape advance scaffold
  (non-last tape).  Both helper references of the dispatch ---
  the walk loop and the boundary step --- are abstracted as the
  \<open>leaf_loop\<close> and \<open>leaf_boundary\<close> hypotheses, so the
  union-relation \<open>ar_advance_tape_step\<close> and the sub-relation
  \<open>ar_advance_tape_step_in_sub\<close> are both thin instantiations
  (discharging the two leaves by the union- resp. sub-relation
  helper lemmas).  Multi-leaf instance of the leaf-parametric
  scaffold; no \<open>stays\<close>
  side-condition since both leaves' chains are native to \<open>R'\<close>.\<close>

lemma ar_advance_tape_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_loop:
        "\<And>c0' n. \<lbrakk> valid_mttm M;
                    q \<in> Q_tm M;
                    mt_state c0' = (q, AR_SimAdvance, tk, 0, buf, dvec, posk);
                    \<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M};
                    n < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk);
                    \<And>j. j < n \<Longrightarrow> mt_tape c0' tk (mt_pos c0' tk - j) \<noteq> LE4;
                    \<forall>j \<ge> k_tm M. mt_tape c0' j (mt_pos c0' j) = BLANK4;
                    ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimAdvance, tk, 0, buf, dvec, posk) \<rbrakk>
                  \<Longrightarrow> \<exists>c'. (c0', c') \<in> R' ^^ n
                          \<and> mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
                          \<and> mt_pos c' tk = mt_pos c0' tk - n
                          \<and> mt_tape c' = mt_tape c0'
                          \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0' k')"
      and leaf_boundary:
        "\<And>cc i. \<lbrakk> valid_mttm M;
                   mt_state cc = (q, AR_SimAdvance, tk, i, buf, dvec, posk);
                   q \<in> Q_tm M;
                   \<not> is_last_k M tk;
                   (dvec tk = dir.R \<and> i = 0)
                     \<or> (dvec tk \<noteq> dir.R
                         \<and> mt_tape cc tk (mt_pos cc tk) \<noteq> LE4
                         \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk));
                   ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk);
                   \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                   ar_stage_bounded (bl_tm M) (k_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk) \<rbrakk>
                 \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                          \<and> mt_state c'' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                              posk(tk := ar_newpos (dvec tk) (posk tk)))
                          \<and> mt_tape c'' = mt_tape cc
                          \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos cc
                                          else (mt_pos cc)(tk := mt_pos cc tk - 1))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> R'
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?R = R'
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "mt_pos c0 tk"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "dvec tk = dir.R")
    case True
    have vsrc0: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
      using kpos buf_valid by (simp add: ar_valid_stage_def)
    have fire: "(dvec tk = dir.R \<and> (0::nat) = 0)
                \<or> (dvec tk \<noteq> dir.R \<and> mt_tape c0 tk (mt_pos c0 tk) \<noteq> LE4
                    \<and> Suc 0 = ?D)"
      using True by simp
    obtain c' where
        step: "(c0, c') \<in> ?R"
      and st: "mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and tp: "mt_tape c' = mt_tape c0"
      and ps: "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                  else (mt_pos c0)(tk := mt_pos c0 tk - 1))"
      using leaf_boundary[OF vM stg qQ notlast fire vsrc0 pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = dir.R then 1 else ?D)"
        using step True by simp
      show "mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule st)
      show "mt_tape c' = mt_tape c0" by (rule tp)
      show "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
              else (mt_pos c0)(tk := mt_pos c0 tk - ?D))"
        using ps True by simp
    qed
  next
    case False
    have Dpos: "0 < ?D" using dge1[OF False] by simp
    obtain DD where DD: "?D = Suc DD" using Dpos by (cases ?D) auto
    have ndisp: "DD < ?D" using DD by simp
    have notLE_loop: "\<And>j. j < DD \<Longrightarrow> mt_tape c0 tk (?start - j) \<noteq> LE4"
    proof -
      fix j assume "j < DD"
      hence "j < ?D" using DD by simp
      thus "mt_tape c0 tk (?start - j) \<noteq> LE4" by (rule notLE)
    qed
    obtain cmid where
        lstep: "(c0, cmid) \<in> ?R ^^ DD"
      and lst: "mt_state cmid = (q, AR_SimAdvance, tk, DD, buf, dvec, posk)"
      and lpos: "mt_pos cmid tk = ?start - DD"
      and ltape: "mt_tape cmid = mt_tape c0"
      and lother: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos cmid k' = mt_pos c0 k'"
      using leaf_loop[OF vM qQ stg buf_valid ndisp notLE_loop pad0 src0] by blast
    have DD_lt2k: "DD < 2 * ?k"
      using DD ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrcmid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using DD_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cmid: "\<forall>j \<ge> k_tm M. mt_tape cmid j (mt_pos cmid j) = BLANK4"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have jne: "j \<noteq> tk" using jge tk_lt by simp
      have "mt_tape cmid j (mt_pos cmid j) = mt_tape c0 j (mt_pos c0 j)"
        using ltape lother jne by simp
      thus "mt_tape cmid j (mt_pos cmid j) = BLANK4" using pad0 jge by simp
    qed
    have src_cmid: "ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have notLE_b: "mt_tape cmid tk (mt_pos cmid tk) \<noteq> LE4"
      using ltape lpos notLE[OF ndisp] by simp
    have fire: "(dvec tk = dir.R \<and> DD = 0)
                \<or> (dvec tk \<noteq> dir.R
                    \<and> mt_tape cmid tk (mt_pos cmid tk) \<noteq> LE4
                    \<and> Suc DD = ?D)"
      using False notLE_b DD by simp
    obtain c' where
        bstep: "(cmid, c') \<in> ?R"
      and bst: "mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and btp: "mt_tape c' = mt_tape cmid"
      and bps: "mt_pos c' = (if dvec tk = dir.R then mt_pos cmid
                  else (mt_pos cmid)(tk := mt_pos cmid tk - 1))"
      using leaf_boundary[OF vM lst qQ notlast fire vsrcmid pad_cmid src_cmid] by blast
    have bps_ne: "mt_pos c' = (mt_pos cmid)(tk := mt_pos cmid tk - 1)"
      using bps False by simp
    have chainD: "(c0, c') \<in> ?R ^^ ?D"
    proof -
      have "(c0, c') \<in> ?R ^^ Suc DD" by (rule relpow_Suc_I[OF lstep bstep])
      thus ?thesis using DD by simp
    qed
    have ps_final: "mt_pos c' = (mt_pos c0)(tk := ?start - ?D)"
    proof (rule ext)
      fix k'
      show "mt_pos c' k' = ((mt_pos c0)(tk := ?start - ?D)) k'"
      proof (cases "k' = tk")
        case True
        have "mt_pos c' tk = mt_pos cmid tk - 1" using bps_ne by simp
        also have "\<dots> = (?start - DD) - 1" using lpos by simp
        also have "\<dots> = ?start - ?D" using DD by simp
        finally show ?thesis using True by simp
      next
        case False
        have "mt_pos c' k' = mt_pos cmid k'" using bps_ne False by simp
        also have "\<dots> = mt_pos c0 k'" using lother False by simp
        finally show ?thesis using False by simp
      qed
    qed
    have tp_final: "mt_tape c' = mt_tape c0" using btp ltape by simp
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = dir.R then 1 else ?D)"
        using chainD False by simp
      show "mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule bst)
      show "mt_tape c' = mt_tape c0" by (rule tp_final)
      show "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
              else (mt_pos c0)(tk := mt_pos c0 tk - ?D))"
        using ps_final False by simp
    qed
  qed
qed

text \<open>The unified single-tape advance, non-last tape: the
  \<open>R\<close>/non-\<open>R\<close> dispatch, the advance analogue of
  \<open>ar_write_tape_step\<close>.  From an \<open>AR_SimAdvance\<close> stage at
  bit-counter \<open>0\<close>, tape \<open>tk\<close>'s head is repositioned to
  \<open>M\<close>'s new cell and the hand-off goes to the next tape
  \<open>k_succ tk\<close> (counter \<open>0\<close>, \<open>posk tk\<close> updated by
  \<open>ar_newpos\<close>).  An \<open>R\<close>-move needs no head motion (the
  head already sits at \<open>sim_pos (p + 1)\<close>): a single boundary
  step, cost \<open>1\<close>.  A non-\<open>R\<close>-move walks the head
  \<open>D = ar_disp\<close> cells \<open>L\<close>: the \<open>D - 1\<close>-step
  \<open>ar_advance_walk_loop\<close> followed by the final boundary
  \<open>L\<close>-move, cost \<open>D\<close>, landing the head at
  \<open>start - D\<close>.  The \<open>dge1\<close> hypothesis rules out the
  forbidden \<open>L\<close>-from-\<open>AR_AtLE\<close> (zero displacement) so that
  \<open>D \<ge> 1\<close>; \<open>notLE\<close> covers every cell the walk reads
  (\<open>start - m\<close>, \<open>m < D\<close>).  The tape is unchanged; only
  the head on \<open>tk\<close> moves.\<close>

lemma ar_advance_tape_step:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (alphabet_reduce_delta M))
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
  by (rule ar_advance_tape_step_gen
        [OF ar_advance_walk_loop ar_advance_boundary_step
            vM qQ kge2 notlast stg buf_valid dge1 notLE
            pad0 src0])

text \<open>Relation-generic unified single-tape advance scaffold
  (last tape).  As \<open>ar_advance_tape_step_gen\<close> but the boundary
  leaf transitions to \<open>AR_SimNext\<close>; both helper references
  (walk loop, finish step) are the \<open>leaf_loop\<close> and
  \<open>leaf_finish\<close> hypotheses, so the union- and sub-relation
  versions are thin instantiations.\<close>

lemma ar_advance_tape_finish_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_loop:
        "\<And>c0' n. \<lbrakk> valid_mttm M;
                    q \<in> Q_tm M;
                    mt_state c0' = (q, AR_SimAdvance, tk, 0, buf, dvec, posk);
                    \<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M};
                    n < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk);
                    \<And>j. j < n \<Longrightarrow> mt_tape c0' tk (mt_pos c0' tk - j) \<noteq> LE4;
                    \<forall>j \<ge> k_tm M. mt_tape c0' j (mt_pos c0' j) = BLANK4;
                    ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimAdvance, tk, 0, buf, dvec, posk) \<rbrakk>
                  \<Longrightarrow> \<exists>c'. (c0', c') \<in> R' ^^ n
                          \<and> mt_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
                          \<and> mt_pos c' tk = mt_pos c0' tk - n
                          \<and> mt_tape c' = mt_tape c0'
                          \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c' k' = mt_pos c0' k')"
      and leaf_finish:
        "\<And>cc i. \<lbrakk> valid_mttm M;
                   mt_state cc = (q, AR_SimAdvance, tk, i, buf, dvec, posk);
                   q \<in> Q_tm M;
                   is_last_k M tk;
                   (dvec tk = dir.R \<and> i = 0)
                     \<or> (dvec tk \<noteq> dir.R
                         \<and> mt_tape cc tk (mt_pos cc tk) \<noteq> LE4
                         \<and> Suc i = ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk));
                   ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk);
                   \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                   ar_stage_bounded (bl_tm M) (k_tm M)
                     (AR_SimAdvance, tk, i, buf, dvec, posk) \<rbrakk>
                 \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                          \<and> mt_state c'' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                              posk(tk := ar_newpos (dvec tk) (posk tk)))
                          \<and> mt_tape c'' = mt_tape cc
                          \<and> mt_pos c'' = (if dvec tk = dir.R then mt_pos cc
                                          else (mt_pos cc)(tk := mt_pos cc tk - 1))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> R'
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?R = R'
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "mt_pos c0 tk"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "dvec tk = dir.R")
    case True
    have vsrc0: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
      using kpos buf_valid by (simp add: ar_valid_stage_def)
    have fire: "(dvec tk = dir.R \<and> (0::nat) = 0)
                \<or> (dvec tk \<noteq> dir.R \<and> mt_tape c0 tk (mt_pos c0 tk) \<noteq> LE4
                    \<and> Suc 0 = ?D)"
      using True by simp
    obtain c' where
        step: "(c0, c') \<in> ?R"
      and st: "mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and tp: "mt_tape c' = mt_tape c0"
      and ps: "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                  else (mt_pos c0)(tk := mt_pos c0 tk - 1))"
      using leaf_finish[OF vM stg qQ last fire vsrc0 pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = dir.R then 1 else ?D)"
        using step True by simp
      show "mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule st)
      show "mt_tape c' = mt_tape c0" by (rule tp)
      show "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
              else (mt_pos c0)(tk := mt_pos c0 tk - ?D))"
        using ps True by simp
    qed
  next
    case False
    have Dpos: "0 < ?D" using dge1[OF False] by simp
    obtain DD where DD: "?D = Suc DD" using Dpos by (cases ?D) auto
    have ndisp: "DD < ?D" using DD by simp
    have notLE_loop: "\<And>j. j < DD \<Longrightarrow> mt_tape c0 tk (?start - j) \<noteq> LE4"
    proof -
      fix j assume "j < DD"
      hence "j < ?D" using DD by simp
      thus "mt_tape c0 tk (?start - j) \<noteq> LE4" by (rule notLE)
    qed
    obtain cmid where
        lstep: "(c0, cmid) \<in> ?R ^^ DD"
      and lst: "mt_state cmid = (q, AR_SimAdvance, tk, DD, buf, dvec, posk)"
      and lpos: "mt_pos cmid tk = ?start - DD"
      and ltape: "mt_tape cmid = mt_tape c0"
      and lother: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos cmid k' = mt_pos c0 k'"
      using leaf_loop[OF vM qQ stg buf_valid ndisp notLE_loop pad0 src0] by blast
    have DD_lt2k: "DD < 2 * ?k"
      using DD ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrcmid: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                     (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using DD_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cmid: "\<forall>j \<ge> k_tm M. mt_tape cmid j (mt_pos cmid j) = BLANK4"
    proof (intro allI impI)
      fix j assume jge: "k_tm M \<le> j"
      have jne: "j \<noteq> tk" using jge tk_lt by simp
      have "mt_tape cmid j (mt_pos cmid j) = mt_tape c0 j (mt_pos c0 j)"
        using ltape lother jne by simp
      thus "mt_tape cmid j (mt_pos cmid j) = BLANK4" using pad0 jge by simp
    qed
    have src_cmid: "ar_stage_bounded (bl_tm M) (k_tm M)
                      (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have notLE_b: "mt_tape cmid tk (mt_pos cmid tk) \<noteq> LE4"
      using ltape lpos notLE[OF ndisp] by simp
    have fire: "(dvec tk = dir.R \<and> DD = 0)
                \<or> (dvec tk \<noteq> dir.R
                    \<and> mt_tape cmid tk (mt_pos cmid tk) \<noteq> LE4
                    \<and> Suc DD = ?D)"
      using False notLE_b DD by simp
    obtain c' where
        bstep: "(cmid, c') \<in> ?R"
      and bst: "mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and btp: "mt_tape c' = mt_tape cmid"
      and bps: "mt_pos c' = (if dvec tk = dir.R then mt_pos cmid
                  else (mt_pos cmid)(tk := mt_pos cmid tk - 1))"
      using leaf_finish[OF vM lst qQ last fire vsrcmid pad_cmid src_cmid] by blast
    have bps_ne: "mt_pos c' = (mt_pos cmid)(tk := mt_pos cmid tk - 1)"
      using bps False by simp
    have chainD: "(c0, c') \<in> ?R ^^ ?D"
    proof -
      have "(c0, c') \<in> ?R ^^ Suc DD" by (rule relpow_Suc_I[OF lstep bstep])
      thus ?thesis using DD by simp
    qed
    have ps_final: "mt_pos c' = (mt_pos c0)(tk := ?start - ?D)"
    proof (rule ext)
      fix k'
      show "mt_pos c' k' = ((mt_pos c0)(tk := ?start - ?D)) k'"
      proof (cases "k' = tk")
        case True
        have "mt_pos c' tk = mt_pos cmid tk - 1" using bps_ne by simp
        also have "\<dots> = (?start - DD) - 1" using lpos by simp
        also have "\<dots> = ?start - ?D" using DD by simp
        finally show ?thesis using True by simp
      next
        case False
        have "mt_pos c' k' = mt_pos cmid k'" using bps_ne False by simp
        also have "\<dots> = mt_pos c0 k'" using lother False by simp
        finally show ?thesis using False by simp
      qed
    qed
    have tp_final: "mt_tape c' = mt_tape c0" using btp ltape by simp
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = dir.R then 1 else ?D)"
        using chainD False by simp
      show "mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule bst)
      show "mt_tape c' = mt_tape c0" by (rule tp_final)
      show "mt_pos c' = (if dvec tk = dir.R then mt_pos c0
              else (mt_pos c0)(tk := mt_pos c0 tk - ?D))"
        using ps_final False by simp
    qed
  qed
qed

text \<open>The unified single-tape advance, last tape: as
  \<open>ar_advance_tape_step\<close> but \<open>tk\<close> is the last tape, so the
  boundary step (\<open>ar_advance_finish_step\<close>) transitions to
  \<open>AR_SimNext\<close> (current-tape field reset to \<open>k_unidx 0\<close>)
  rather than advancing to \<open>k_succ tk\<close>.  Same \<open>R\<close>/non-\<open>R\<close>
  dispatch, the same walk-then-boundary decomposition, and the same
  conditional head conclusion.\<close>

lemma ar_advance_tape_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "dvec tk \<noteq> dir.R
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> mt_tape c0 tk (mt_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (mttm_step (alphabet_reduce_delta M))
                            ^^ (if dvec tk = dir.R then 1
                                else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk))
              \<and> mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> mt_tape c' = mt_tape c0
              \<and> mt_pos c' = (if dvec tk = dir.R then mt_pos c0
                            else (mt_pos c0)(tk := mt_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk) (posk tk)))"
  by (rule ar_advance_tape_finish_step_gen
        [OF ar_advance_walk_loop ar_advance_finish_step
            vM qQ kge2 last stg buf_valid dge1 notLE
            pad0 src0])

text \<open>Relation-generic advance prefix walk scaffold.  The single
  per-tape helper (\<open>ar_advance_tape_step\<close>) is the \<open>leaf_tape\<close>
  hypothesis, quantified over the per-tape config, tape index, and
  position-kind function; the union- and sub-relation prefixes are
  thin instantiations.\<close>

lemma ar_advance_prefix_gen:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_tape:
        "\<And>cc tk' pk'.
           \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
             \<not> is_last_k M tk';
             mt_state cc = (q, AR_SimAdvance, tk', 0, buf0, dvec, pk');
             \<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M};
             dvec tk' \<noteq> dir.R
               \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk');
             \<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk')
                \<Longrightarrow> mt_tape cc tk' (mt_pos cc tk' - m) \<noteq> LE4;
             \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
             ar_stage_bounded (bl_tm M) (k_tm M)
               (AR_SimAdvance, tk', 0, buf0, dvec, pk') \<rbrakk>
           \<Longrightarrow> \<exists>c'. (cc, c') \<in> R'
                          ^^ (if dvec tk' = dir.R then 1
                              else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk'))
                    \<and> mt_state c' = (q, AR_SimAdvance, k_succ tk', 0, buf0, dvec,
                          pk'(tk' := ar_newpos (dvec tk') (pk' tk')))
                    \<and> mt_tape c' = mt_tape cc
                    \<and> mt_pos c' = (if dvec tk' = dir.R then mt_pos cc
                          else (mt_pos cc)(tk' := mt_pos cc tk'
                                 - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk')))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> R' ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimAdvance, k_unidx j, 0, buf0, dvec,
              (\<lambda>k. if k_idx k < j then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k
                           - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k))"
proof (induction j)
  case 0
  let ?pk0 = "\<lambda>k. if k_idx k < (0::nat) then ar_newpos (dvec k) (posk0 k)
                  else posk0 k"
  have "(c0, c0) \<in> R' ^^ 0" by simp
  moreover have "mt_state c0 = (q, AR_SimAdvance, k_unidx 0, 0, buf0, dvec, ?pk0)"
    using stg0 by (simp add: k_unidx_zero)
  ultimately show ?case
    by (intro exI[where x = c0] exI[where x = 0]) simp
next
  case (Suc j)
  have sucle: "Suc j \<le> k_tm M - 1" by (rule Suc.prems)
  have jcard: "j < k_tm M" using sucle by simp
  have sjcard: "Suc j < k_tm M" using sucle by simp
  have jle: "j \<le> k_tm M - 1" using sucle by simp
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?R = R'
  let ?tk = "k_unidx j"
  let ?pk = "\<lambda>i. (\<lambda>k. if k_idx k < i then ar_newpos (dvec k) (posk0 k)
                    else posk0 k)"
  let ?ps = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if dvec k = dir.R then mt_pos c0 k
                          else mt_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                    else mt_pos c0 k)"
  have kpos: "0 < ?k" using kge2 by simp
  have tkidx: "k_idx ?tk = j" by (rule k_idx_unidx[OF jcard])
  have notlast: "\<not> is_last_k M ?tk"
    using is_last_k_unidx[OF jcard] sjcard by simp
  have ksucc: "k_succ ?tk = k_unidx (Suc j)" by (rule k_succ_unidx[OF sjcard])
  have inj: "inj_on k_idx UNIV" by (rule k_idx_inj)
  have kne: "\<And>k. k_idx k = j \<Longrightarrow> k = ?tk"
  proof -
    fix k assume "k_idx k = j"
    hence "k_idx k = k_idx ?tk" using tkidx by simp
    thus "k = ?tk" using inj_on_eq_iff[OF inj UNIV_I UNIV_I] by simp
  qed
  obtain c m where
      cm_rel: "(c0, c) \<in> ?R ^^ m"
    and m_le: "m \<le> j * (2 * ?k)"
    and c_st: "mt_state c = (q, AR_SimAdvance, ?tk, 0, buf0, dvec, ?pk j)"
    and c_tp: "mt_tape c = mt_tape c0"
    and c_ps: "mt_pos c = ?ps j"
    using Suc.IH[OF jle] by blast
  \<comment> \<open>per-tape entry facts for tape \<open>?tk\<close> at config \<open>c\<close>\<close>
  have pkj_tk: "?pk j ?tk = posk0 ?tk" using tkidx by simp
  have psj_tk: "?ps j ?tk = mt_pos c0 ?tk" using tkidx by simp
  have c_pos_tk: "mt_pos c ?tk = mt_pos c0 ?tk" using c_ps psj_tk by simp
  have tk_active: "?tk < k_tm M" using jcard by (simp add: k_unidx_def)
  have tk_dge1: "dvec ?tk \<noteq> dir.R \<Longrightarrow> 0 < ar_disp ?k (dvec ?tk) (?pk j ?tk)"
    using dge1[rule_format, OF tk_active] pkj_tk by simp
  have tk_notLE: "\<And>m. m < ar_disp ?k (dvec ?tk) (?pk j ?tk)
                    \<Longrightarrow> mt_tape c ?tk (mt_pos c ?tk - m) \<noteq> LE4"
  proof -
    fix m assume "m < ar_disp ?k (dvec ?tk) (?pk j ?tk)"
    hence mlt: "m < ar_disp ?k (dvec ?tk) (posk0 ?tk)" using pkj_tk by simp
    have "mt_tape c ?tk (mt_pos c ?tk - m) = mt_tape c0 ?tk (mt_pos c0 ?tk - m)"
      using c_tp c_pos_tk by simp
    thus "mt_tape c ?tk (mt_pos c ?tk - m) \<noteq> LE4"
      using notLE[rule_format, OF tk_active mlt] by simp
  qed
  have tail_idx: "\<And>j'. k_tm M \<le> j' \<Longrightarrow> \<not> k_idx j' < j"
    using jcard unfolding k_idx_def by linarith
  have pad_c: "\<forall>j' \<ge> k_tm M. mt_tape c j' (mt_pos c j') = BLANK4"
  proof (intro allI impI)
    fix j' assume jge: "k_tm M \<le> j'"
    have "mt_tape c j' (mt_pos c j') = mt_tape c0 j' (mt_pos c0 j')"
      using c_tp c_ps tail_idx[OF jge] by simp
    thus "mt_tape c j' (mt_pos c j') = BLANK4" using pad0 jge by simp
  qed
  have src_c: "ar_stage_bounded (bl_tm M) (k_tm M)
                 (AR_SimAdvance, ?tk, 0, buf0, dvec, ?pk j)"
    using src0 tk_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c' where
      step: "(c, c') \<in> ?R ^^ (if dvec ?tk = dir.R then 1
                else ar_disp ?k (dvec ?tk) (?pk j ?tk))"
    and c'_st: "mt_state c' = (q, AR_SimAdvance, k_succ ?tk, 0, buf0, dvec,
                  (?pk j)(?tk := ar_newpos (dvec ?tk) (?pk j ?tk)))"
    and c'_tp: "mt_tape c' = mt_tape c"
    and c'_ps: "mt_pos c' = (if dvec ?tk = dir.R then mt_pos c
                  else (mt_pos c)(?tk := mt_pos c ?tk
                         - ar_disp ?k (dvec ?tk) (?pk j ?tk)))"
    using leaf_tape[OF vM qQ kge2 notlast c_st buf_valid tk_dge1 tk_notLE
                       pad_c src_c]
    by blast
  \<comment> \<open>the post-state descriptors coincide with the \<open>Suc j\<close> ones\<close>
  have pk_eq: "(?pk j)(?tk := ar_newpos (dvec ?tk) (?pk j ?tk)) = ?pk (Suc j)"
  proof (rule ext)
    fix k
    show "((?pk j)(?tk := ar_newpos (dvec ?tk) (?pk j ?tk))) k = ?pk (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False by (simp add: less_Suc_eq)
    qed
  qed
  have ps_eq: "(if dvec ?tk = dir.R then mt_pos c
                 else (mt_pos c)(?tk := mt_pos c ?tk
                        - ar_disp ?k (dvec ?tk) (?pk j ?tk))) = ?ps (Suc j)"
  proof (rule ext)
    fix k
    show "(if dvec ?tk = dir.R then mt_pos c
            else (mt_pos c)(?tk := mt_pos c ?tk
                   - ar_disp ?k (dvec ?tk) (?pk j ?tk))) k = ?ps (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using c_ps tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False c_ps by (simp add: less_Suc_eq)
    qed
  qed
  have chain: "(c0, c') \<in> ?R ^^ (m + (if dvec ?tk = dir.R then 1
                  else ar_disp ?k (dvec ?tk) (?pk j ?tk)))"
  proof -
    have "(c0, c') \<in> ?R ^^ m
                       O ?R ^^ (if dvec ?tk = dir.R then 1
                                else ar_disp ?k (dvec ?tk) (?pk j ?tk))"
      using cm_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m + (if dvec ?tk = dir.R then 1
                 else ar_disp ?k (dvec ?tk) (?pk j ?tk)) \<le> Suc j * (2 * ?k)"
    using m_le kpos ar_disp_le_2k[OF kpos, of "dvec ?tk" "?pk j ?tk"]
    by (cases "dvec ?tk = dir.R") auto
  show ?case
  proof (intro exI[where x = c']
           exI[where x = "m + (if dvec ?tk = dir.R then 1
                  else ar_disp ?k (dvec ?tk) (?pk j ?tk))"] conjI)
    show "(c0, c') \<in> ?R ^^ (m + (if dvec ?tk = dir.R then 1
            else ar_disp ?k (dvec ?tk) (?pk j ?tk)))" by (rule chain)
    show "m + (if dvec ?tk = dir.R then 1
            else ar_disp ?k (dvec ?tk) (?pk j ?tk)) \<le> Suc j * (2 * ?k)"
      by (rule bound)
    show "mt_state c' = (q, AR_SimAdvance, k_unidx (Suc j), 0, buf0, dvec,
            ?pk (Suc j))"
      using c'_st ksucc pk_eq by simp
    show "mt_tape c' = mt_tape c0" using c'_tp c_tp by simp
    show "mt_pos c' = ?ps (Suc j)" using c'_ps ps_eq by simp
  qed
qed

text \<open>The advance prefix walk: a custom induction on the tape index
  \<open>j\<close> (\<open>j \<le> k_tm M - 1\<close>, so every tape it touches is
  non-last), iterating \<open>ar_advance_tape_step\<close> from the boundary
  tape \<open>k_unidx 0\<close>.  Like the read prefix, the tape is constant and the carried state is
  a \<open>k_idx k < j\<close> split: tapes already advanced
  (\<open>k_idx k < j\<close>) hold their \<open>ar_newpos\<close>-updated
  position-kind and their repositioned head, the rest hold boundary
  values.  The per-tape \<open>notLE\<close>/\<open>dge1\<close> entry facts hold of
  the current tape \<open>?tk\<close> because it is not yet visited
  (\<open>?pk j ?tk = posk0 ?tk\<close>, \<open>mt_pos c ?tk = mt_pos c0 ?tk\<close>).
  Aggregate cost \<open>\<le> j \<cdot> 2b\<close> (each per-tape move is at most
  \<open>2b\<close> cells, \<open>ar_disp_le_2k\<close>).\<close>

lemma ar_advance_prefix:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimAdvance, k_unidx j, 0, buf0, dvec,
              (\<lambda>k. if k_idx k < j then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k
                           - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k))"
  by (rule ar_advance_prefix_gen
        [OF ar_advance_tape_step vM qQ kge2 stg0 buf_valid dge1 notLE
            pad0 src0])

text \<open>Relation-generic full advance phase scaffold.  The two
  helpers (prefix walk, last-tape finish) are the \<open>leaf_prefix\<close>
  and \<open>leaf_finish\<close> hypotheses; the union- and sub-relation
  phases are thin instantiations.\<close>

lemma ar_advance_phase_gen:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_prefix:
        "\<And>jj. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                 mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0);
                 \<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M};
                 \<forall>k < k_tm M. dvec k \<noteq> dir.R
                    \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k);
                 \<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4;
                 \<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0);
                 jj \<le> k_tm M - 1 \<rbrakk>
               \<Longrightarrow> (\<exists>c m. (c0, c) \<in> R' ^^ m
                    \<and> m \<le> jj * (2 * block_width (\<Gamma>_tm M))
                    \<and> mt_state c = (q, AR_SimAdvance, k_unidx jj, 0, buf0, dvec,
                         (\<lambda>k. if k_idx k < jj then ar_newpos (dvec k) (posk0 k)
                               else posk0 k))
                    \<and> mt_tape c = mt_tape c0
                    \<and> mt_pos c = (\<lambda>k. if k_idx k < jj
                         then (if dvec k = dir.R then mt_pos c0 k
                               else mt_pos c0 k
                                      - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
                         else mt_pos c0 k))"
      and leaf_finish:
        "\<And>cc tk' pk'.
           \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
             is_last_k M tk';
             mt_state cc = (q, AR_SimAdvance, tk', 0, buf0, dvec, pk');
             \<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M};
             dvec tk' \<noteq> dir.R
               \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk');
             \<And>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk')
                \<Longrightarrow> mt_tape cc tk' (mt_pos cc tk' - m) \<noteq> LE4;
             \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
             ar_stage_bounded (bl_tm M) (k_tm M)
               (AR_SimAdvance, tk', 0, buf0, dvec, pk') \<rbrakk>
           \<Longrightarrow> \<exists>c'. (cc, c') \<in> R' ^^ (if dvec tk' = dir.R then 1
                          else ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk'))
                    \<and> mt_state c' = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
                          pk'(tk' := ar_newpos (dvec tk') (pk' tk')))
                    \<and> mt_tape c' = mt_tape cc
                    \<and> mt_pos c' = (if dvec tk' = dir.R then mt_pos cc
                          else (mt_pos cc)(tk' := mt_pos cc tk'
                                 - ar_disp (block_width (\<Gamma>_tm M)) (dvec tk') (pk' tk')))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> R' ^^ m
         \<and> m \<le> k_tm M * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
              (\<lambda>k. if k < k_tm M then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k)"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?N = "k_tm M"
  let ?m1 = "?N - 1"
  let ?tl = "k_unidx ?m1"
  have card1: "0 < ?N" using vM by (cases M) auto
  have m1suc: "?N = Suc ?m1" using card1 by simp
  have m1card: "?m1 < ?N" using card1 by simp
  have m1lt: "?m1 < k_tm M" using card1 by simp
  have kpos: "0 < ?k" using kge2 by simp
  have tl_eq: "?tl = ?m1" by (simp add: k_unidx_def)
  have tlidx: "k_idx ?tl = ?m1" by (rule k_idx_unidx[OF m1card])
  have tl_active: "?tl < k_tm M" using m1lt tl_eq by simp
  have islast: "is_last_k M ?tl" using is_last_k_unidx[OF m1card] m1suc by simp
  have cond: "(k < ?m1) = (k < k_tm M)" if "k \<noteq> ?m1" for k
    using that m1suc by (auto simp: less_Suc_eq)
  let ?pk = "\<lambda>k. if k_idx k < ?m1 then ar_newpos (dvec k) (posk0 k)
                  else posk0 k"
  let ?ps = "\<lambda>k. if k_idx k < ?m1
                  then (if dvec k = dir.R then mt_pos c0 k
                        else mt_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                  else mt_pos c0 k"
  have m1le: "?m1 \<le> k_tm M - 1" by simp
  obtain c1 m1 where
      c1_rel: "(c0, c1) \<in> R' ^^ m1"
    and m1_le: "m1 \<le> ?m1 * (2 * ?k)"
    and c1_st: "mt_state c1 = (q, AR_SimAdvance, ?tl, 0, buf0, dvec, ?pk)"
    and c1_tp: "mt_tape c1 = mt_tape c0"
    and c1_ps: "mt_pos c1 = ?ps"
    using leaf_prefix[OF vM qQ kge2 stg0 buf_valid dge1 notLE pad0 src0 m1le]
    by blast
  have pk_tl: "?pk ?tl = posk0 ?tl" using tlidx by simp
  have c1_pos_tl: "mt_pos c1 ?tl = mt_pos c0 ?tl" using c1_ps tlidx by simp
  have tl_dge1: "dvec ?tl \<noteq> dir.R \<Longrightarrow> 0 < ar_disp ?k (dvec ?tl) (?pk ?tl)"
    using dge1[rule_format, OF tl_active] pk_tl by simp
  have tl_notLE: "\<And>m. m < ar_disp ?k (dvec ?tl) (?pk ?tl)
                    \<Longrightarrow> mt_tape c1 ?tl (mt_pos c1 ?tl - m) \<noteq> LE4"
  proof -
    fix m assume "m < ar_disp ?k (dvec ?tl) (?pk ?tl)"
    hence mlt: "m < ar_disp ?k (dvec ?tl) (posk0 ?tl)" using pk_tl by simp
    have "mt_tape c1 ?tl (mt_pos c1 ?tl - m) = mt_tape c0 ?tl (mt_pos c0 ?tl - m)"
      using c1_tp c1_pos_tl by simp
    thus "mt_tape c1 ?tl (mt_pos c1 ?tl - m) \<noteq> LE4"
      using notLE[rule_format, OF tl_active mlt] by simp
  qed
  have tail_idx: "\<And>j. k_tm M \<le> j \<Longrightarrow> \<not> k_idx j < ?m1"
    using m1suc unfolding k_idx_def by linarith
  have pad_c1: "\<forall>j \<ge> k_tm M. mt_tape c1 j (mt_pos c1 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have "mt_tape c1 j (mt_pos c1 j) = mt_tape c0 j (mt_pos c0 j)"
      using c1_tp c1_ps tail_idx[OF jge] by simp
    thus "mt_tape c1 j (mt_pos c1 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c1: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimAdvance, ?tl, 0, buf0, dvec, ?pk)"
    using src0 tl_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c2 where
      step: "(c1, c2) \<in> R' ^^ (if dvec ?tl = dir.R then 1
                else ar_disp ?k (dvec ?tl) (?pk ?tl))"
    and c2_st: "mt_state c2 = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
                  ?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl)))"
    and c2_tp: "mt_tape c2 = mt_tape c1"
    and c2_ps: "mt_pos c2 = (if dvec ?tl = dir.R then mt_pos c1
                  else (mt_pos c1)(?tl := mt_pos c1 ?tl
                         - ar_disp ?k (dvec ?tl) (?pk ?tl)))"
    using leaf_finish[OF vM qQ kge2 islast c1_st buf_valid
                                          tl_dge1 tl_notLE pad_c1 src_c1]
    by blast
  \<comment> \<open>The last-tape \<open>fun_upd\<close>s collapse to active-guarded
     vectors: active tapes take the \<open>ar_newpos\<close> / displaced
     value, padding tapes stay frozen at the entry \<open>posk0\<close> /
     position.\<close>
  have pk_full: "?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl))
                   = (\<lambda>k. if k < k_tm M then ar_newpos (dvec k) (posk0 k)
                          else posk0 k)"
  proof (rule ext)
    fix k
    show "(?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl))) k
            = (if k < k_tm M then ar_newpos (dvec k) (posk0 k) else posk0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using pk_tl tl_active by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] by (simp add: k_idx_def)
    qed
  qed
  have ps_full: "(if dvec ?tl = dir.R then mt_pos c1
                   else (mt_pos c1)(?tl := mt_pos c1 ?tl
                          - ar_disp ?k (dvec ?tl) (?pk ?tl)))
                   = (\<lambda>k. if k < k_tm M
                          then (if dvec k = dir.R then mt_pos c0 k
                                else mt_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                          else mt_pos c0 k)"
  proof (rule ext)
    fix k
    show "(if dvec ?tl = dir.R then mt_pos c1
            else (mt_pos c1)(?tl := mt_pos c1 ?tl
                   - ar_disp ?k (dvec ?tl) (?pk ?tl))) k
            = (if k < k_tm M
               then (if dvec k = dir.R then mt_pos c0 k
                     else mt_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
               else mt_pos c0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using c1_pos_tl pk_tl tl_active by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] c1_ps by (simp add: k_idx_def)
    qed
  qed
  have chain: "(c0, c2) \<in> R' ^^ (m1 + (if dvec ?tl = dir.R then 1
                  else ar_disp ?k (dvec ?tl) (?pk ?tl)))"
  proof -
    have "(c0, c2) \<in> R' ^^ m1
                       O R' ^^ (if dvec ?tl = dir.R then 1
                                else ar_disp ?k (dvec ?tl) (?pk ?tl))"
      using c1_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m1 + (if dvec ?tl = dir.R then 1
                 else ar_disp ?k (dvec ?tl) (?pk ?tl)) \<le> ?N * (2 * ?k)"
  proof -
    obtain Nm where Nm: "?N = Suc Nm" using card1 by (cases ?N) auto
    have e1: "?N * (2 * ?k) = (2 * ?k) + Nm * (2 * ?k)" by (simp add: Nm)
    have e2: "m1 \<le> Nm * (2 * ?k)" using m1_le Nm by simp
    have e3: "(if dvec ?tl = dir.R then 1 else ar_disp ?k (dvec ?tl) (?pk ?tl))
                \<le> 2 * ?k"
      using ar_disp_le_2k[OF kpos, of "dvec ?tl" "?pk ?tl"] kpos
      by (cases "dvec ?tl = dir.R") auto
    show ?thesis using e1 e2 e3 by linarith
  qed
  show ?thesis
  proof (intro exI[where x = c2]
           exI[where x = "m1 + (if dvec ?tl = dir.R then 1
                  else ar_disp ?k (dvec ?tl) (?pk ?tl))"] conjI)
    show "(c0, c2) \<in> R' ^^ (m1 + (if dvec ?tl = dir.R then 1
            else ar_disp ?k (dvec ?tl) (?pk ?tl)))" by (rule chain)
    show "m1 + (if dvec ?tl = dir.R then 1
            else ar_disp ?k (dvec ?tl) (?pk ?tl)) \<le> ?N * (2 * ?k)"
      by (rule bound)
    show "mt_state c2 = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
            (\<lambda>k. if k < k_tm M then ar_newpos (dvec k) (posk0 k) else posk0 k))"
      using c2_st pk_full by simp
    show "mt_tape c2 = mt_tape c0" using c2_tp c1_tp by simp
    show "mt_pos c2 = (\<lambda>k. if k < k_tm M
            then (if dvec k = dir.R then mt_pos c0 k
                  else mt_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
            else mt_pos c0 k)"
      using c2_ps ps_full by simp
  qed
qed

text \<open>The full advance phase: the prefix walk over the first
  \<open>k_tm M - 1\<close> tapes followed by the unified last-tape advance
  \<open>ar_advance_tape_finish_step\<close>, landing at \<open>AR_SimNext\<close>
  (current-tape field \<open>k_unidx 0\<close>) with every tape's head moved to
  \<open>M\<close>'s new position (\<open>R\<close>: unchanged; otherwise
  \<open>- ar_disp\<close>) and every \<open>posk\<close> updated by
  \<open>ar_newpos\<close>.  The tape is unchanged throughout (advance only
  moves heads).  Aggregate cost \<open>\<le> k_tm M \<cdot> 2b\<close>.  The
  final \<open>posk\<close>/position vectors collapse from the
  \<open>k_idx k < ?m1\<close> split because, on the last tape, every other
  tape has index \<open>< k_tm M - 1\<close> (\<open>k_idx\<close> bijective into
  \<open>{..< k_tm M}\<close>).\<close>

lemma ar_advance_phase:
  fixes M :: "('q, 'a) mttm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and dge1: "\<forall>k < k_tm M. dvec k \<noteq> dir.R
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_tm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k)
                    \<longrightarrow> mt_tape c0 k (mt_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m
         \<and> m \<le> k_tm M * (2 * block_width (\<Gamma>_tm M))
         \<and> mt_state c = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
              (\<lambda>k. if k < k_tm M then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if dvec k = dir.R then mt_pos c0 k
                    else mt_pos c0 k - ar_disp (block_width (\<Gamma>_tm M)) (dvec k) (posk0 k))
              else mt_pos c0 k)"
  by (rule ar_advance_phase_gen
        [OF ar_advance_prefix ar_advance_tape_finish_step
            vM qQ kge2 stg0 buf_valid dge1 notLE pad0 src0])

end
