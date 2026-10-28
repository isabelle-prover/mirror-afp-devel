theory AlphabetReduction_ForwardAdvance
  imports AlphabetReduction_ForwardWrite
begin

subsection \<open>Advance phase\<close>

lemma ar_advance_walk_loop:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and stg: "ktc_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and ndisp: "n < ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>j. j < n \<Longrightarrow> ktc_tape c0 tk (ktc_pos c0 tk - j) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ n
              \<and> ktc_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)
              \<and> ktc_pos c' tk = ktc_pos c0 tk - n
              \<and> ktc_tape c' = ktc_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k')"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "ktc_pos c0 tk"
  have kpos: "0 < ?k" using block_width_pos[of "\<Gamma>_ktm M"] by simp
  let ?P = "\<lambda>j c.
       ktc_state c = (q, AR_SimAdvance, tk, j, buf, dvec, posk)
     \<and> ktc_pos c tk = ?start - j
     \<and> ktc_tape c = ktc_tape c0
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c k' = ktc_pos c0 k')"
  have mybase: "?P 0 c0" using stg by simp
  have mystep:
      "\<And>j cc. \<lbrakk> j < n; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M))
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < n" and Pj: "?P j cc"
    from Pj have st_cc:
        "ktc_state cc = (q, AR_SimAdvance, tk, j, buf, dvec, posk)"
      and pos_cc: "ktc_pos cc tk = ?start - j"
      and tape_cc: "ktc_tape cc = ktc_tape c0"
      and other_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos cc k' = ktc_pos c0 k'"
      by simp_all
    have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cc: "\<forall>j' \<ge> k_ktm M. ktc_tape cc j' (ktc_pos cc j') = BLANK4"
    proof (intro allI impI)
      fix j' assume jge: "k_ktm M \<le> j'"
      have jne: "j' \<noteq> tk" using jge tk_lt by simp
      have "ktc_tape cc j' (ktc_pos cc j') = ktc_tape c0 j' (ktc_pos c0 j')"
        using tape_cc other_cc jne by simp
      thus "ktc_tape cc j' (ktc_pos cc j') = BLANK4" using pad0 jge by simp
    qed
    have src_cc: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                    (AR_SimAdvance, tk, j, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have sucj_lt: "Suc j < ?D" using jlt ndisp by linarith
    have j_lt2k: "j < 2 * ?k"
      using sucj_lt ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrc_cc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                     (AR_SimAdvance, tk, j, buf, dvec, posk)"
      using j_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have notLE_cc: "ktc_tape cc tk (ktc_pos cc tk) \<noteq> LE4"
      using tape_cc pos_cc notLE[OF jlt] by simp
    obtain c'' where
        bstep: "(cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M))"
      and bst_state: "ktc_state c'' = (q, AR_SimAdvance, tk, Suc j, buf, dvec, posk)"
      and bst_tape: "ktc_tape c'' = ktc_tape cc"
      and bst_pos: "ktc_pos c'' = (ktc_pos cc)(tk := ktc_pos cc tk - 1)"
      using ar_advance_walk_step[OF vM st_cc qQ notLE_cc sucj_lt vsrc_cc pad_cc src_cc] by blast
    have pos_eq: "ktc_pos c'' tk = ?start - Suc j"
      using bst_pos pos_cc by simp
    have tape_eq: "ktc_tape c'' = ktc_tape c0" using bst_tape tape_cc by simp
    have other_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c'' k' = ktc_pos c0 k'"
      using bst_pos other_cc by simp
    show "\<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M))
                \<and> ?P (Suc j) c''"
      using bstep bst_state pos_eq tape_eq other_eq by blast
  qed
  have loop:
      "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ n
            \<and> ?P n c'"
    by (rule relpow_invariant_chain
          [where P = ?P and n = n, OF mystep mybase])
  obtain c' where
      chain: "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ n"
    and Pfin: "?P n c'"
    using loop by blast
  show ?thesis
  proof (intro exI[where x = c'] conjI)
    show "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ n" by (rule chain)
    show "ktc_state c' = (q, AR_SimAdvance, tk, n, buf, dvec, posk)"
      using Pfin by simp
    show "ktc_pos c' tk = ?start - n" using Pfin by simp
    show "ktc_tape c' = ktc_tape c0" using Pfin by simp
    show "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k'" using Pfin by simp
  qed
qed

lemma ar_advance_tape_step:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "ktc_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and dge1: "dvec tk \<noteq> MoveR
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> ktc_tape c0 tk (ktc_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M))
                            ^^ (if dvec tk = MoveR then 1
                                else ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk))
              \<and> ktc_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> ktc_tape c' = ktc_tape c0
              \<and> ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
                            else (ktc_pos c0)(tk := ktc_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)))"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)"
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "ktc_pos c0 tk"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "dvec tk = MoveR")
    case True
    have vsrc0: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
      using kpos buf_valid by (simp add: ar_valid_stage_def)
    have fire: "(dvec tk = MoveR \<and> (0::nat) = 0)
                \<or> (dvec tk \<noteq> MoveR \<and> ktc_tape c0 tk (ktc_pos c0 tk) \<noteq> LE4
                    \<and> Suc 0 = ?D)"
      using True by simp
    obtain c' where
        step: "(c0, c') \<in> ?R"
      and st: "ktc_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and tp: "ktc_tape c' = ktc_tape c0"
      and ps: "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
                  else (ktc_pos c0)(tk := ktc_pos c0 tk - 1))"
      using ar_advance_boundary_step[OF vM stg qQ notlast fire vsrc0 pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = MoveR then 1 else ?D)"
        using step True by simp
      show "ktc_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule st)
      show "ktc_tape c' = ktc_tape c0" by (rule tp)
      show "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
              else (ktc_pos c0)(tk := ktc_pos c0 tk - ?D))"
        using ps True by simp
    qed
  next
    case False
    have Dpos: "0 < ?D" using dge1[OF False] by simp
    obtain DD where DD: "?D = Suc DD" using Dpos by (cases ?D) auto
    have ndisp: "DD < ?D" using DD by simp
    have notLE_loop: "\<And>j. j < DD \<Longrightarrow> ktc_tape c0 tk (?start - j) \<noteq> LE4"
    proof -
      fix j assume "j < DD"
      hence "j < ?D" using DD by simp
      thus "ktc_tape c0 tk (?start - j) \<noteq> LE4" by (rule notLE)
    qed
    obtain cmid where
        lstep: "(c0, cmid) \<in> ?R ^^ DD"
      and lst: "ktc_state cmid = (q, AR_SimAdvance, tk, DD, buf, dvec, posk)"
      and lpos: "ktc_pos cmid tk = ?start - DD"
      and ltape: "ktc_tape cmid = ktc_tape c0"
      and lother: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos cmid k' = ktc_pos c0 k'"
      using ar_advance_walk_loop[OF vM qQ stg buf_valid ndisp notLE_loop pad0 src0] by blast
    have DD_lt2k: "DD < 2 * ?k"
      using DD ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrcmid: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                     (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using DD_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cmid: "\<forall>j \<ge> k_ktm M. ktc_tape cmid j (ktc_pos cmid j) = BLANK4"
    proof (intro allI impI)
      fix j assume jge: "k_ktm M \<le> j"
      have jne: "j \<noteq> tk" using jge tk_lt by simp
      have "ktc_tape cmid j (ktc_pos cmid j) = ktc_tape c0 j (ktc_pos c0 j)"
        using ltape lother jne by simp
      thus "ktc_tape cmid j (ktc_pos cmid j) = BLANK4" using pad0 jge by simp
    qed
    have src_cmid: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                      (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have notLE_b: "ktc_tape cmid tk (ktc_pos cmid tk) \<noteq> LE4"
      using ltape lpos notLE[OF ndisp] by simp
    have fire: "(dvec tk = MoveR \<and> DD = 0)
                \<or> (dvec tk \<noteq> MoveR
                    \<and> ktc_tape cmid tk (ktc_pos cmid tk) \<noteq> LE4
                    \<and> Suc DD = ?D)"
      using False notLE_b DD by simp
    obtain c' where
        bstep: "(cmid, c') \<in> ?R"
      and bst: "ktc_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and btp: "ktc_tape c' = ktc_tape cmid"
      and bps: "ktc_pos c' = (if dvec tk = MoveR then ktc_pos cmid
                  else (ktc_pos cmid)(tk := ktc_pos cmid tk - 1))"
      using ar_advance_boundary_step[OF vM lst qQ notlast fire vsrcmid pad_cmid src_cmid] by blast
    have bps_ne: "ktc_pos c' = (ktc_pos cmid)(tk := ktc_pos cmid tk - 1)"
      using bps False by simp
    have chainD: "(c0, c') \<in> ?R ^^ ?D"
    proof -
      have "(c0, c') \<in> ?R ^^ Suc DD" by (rule relpow_Suc_I[OF lstep bstep])
      thus ?thesis using DD by simp
    qed
    have ps_final: "ktc_pos c' = (ktc_pos c0)(tk := ?start - ?D)"
    proof (rule ext)
      fix k'
      show "ktc_pos c' k' = ((ktc_pos c0)(tk := ?start - ?D)) k'"
      proof (cases "k' = tk")
        case True
        have "ktc_pos c' tk = ktc_pos cmid tk - 1" using bps_ne by simp
        also have "\<dots> = (?start - DD) - 1" using lpos by simp
        also have "\<dots> = ?start - ?D" using DD by simp
        finally show ?thesis using True by simp
      next
        case False
        have "ktc_pos c' k' = ktc_pos cmid k'" using bps_ne False by simp
        also have "\<dots> = ktc_pos c0 k'" using lother False by simp
        finally show ?thesis using False by simp
      qed
    qed
    have tp_final: "ktc_tape c' = ktc_tape c0" using btp ltape by simp
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = MoveR then 1 else ?D)"
        using chainD False by simp
      show "ktc_state c' = (q, AR_SimAdvance, k_succ tk, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule bst)
      show "ktc_tape c' = ktc_tape c0" by (rule tp_final)
      show "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
              else (ktc_pos c0)(tk := ktc_pos c0 tk - ?D))"
        using ps_final False by simp
    qed
  qed
qed

lemma ar_advance_tape_finish_step:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and last: "is_last_k M tk"
      and stg: "ktc_state c0 = (q, AR_SimAdvance, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and dge1: "dvec tk \<noteq> MoveR
                  \<Longrightarrow> 0 < ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)"
      and notLE: "\<And>m. m < ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)
                    \<Longrightarrow> ktc_tape c0 tk (ktc_pos c0 tk - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M))
                            ^^ (if dvec tk = MoveR then 1
                                else ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk))
              \<and> ktc_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                                  posk(tk := ar_newpos (dvec tk) (posk tk)))
              \<and> ktc_tape c' = ktc_tape c0
              \<and> ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
                            else (ktc_pos c0)(tk := ktc_pos c0 tk
                                   - ar_disp (block_width (\<Gamma>_ktm M)) (dvec tk) (posk tk)))"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)"
  let ?D = "ar_disp ?k (dvec tk) (posk tk)"
  let ?start = "ktc_pos c0 tk"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "dvec tk = MoveR")
    case True
    have vsrc0: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimAdvance, tk, 0, buf, dvec, posk)"
      using kpos buf_valid by (simp add: ar_valid_stage_def)
    have fire: "(dvec tk = MoveR \<and> (0::nat) = 0)
                \<or> (dvec tk \<noteq> MoveR \<and> ktc_tape c0 tk (ktc_pos c0 tk) \<noteq> LE4
                    \<and> Suc 0 = ?D)"
      using True by simp
    obtain c' where
        step: "(c0, c') \<in> ?R"
      and st: "ktc_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and tp: "ktc_tape c' = ktc_tape c0"
      and ps: "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
                  else (ktc_pos c0)(tk := ktc_pos c0 tk - 1))"
      using ar_advance_finish_step[OF vM stg qQ last fire vsrc0 pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = MoveR then 1 else ?D)"
        using step True by simp
      show "ktc_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule st)
      show "ktc_tape c' = ktc_tape c0" by (rule tp)
      show "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
              else (ktc_pos c0)(tk := ktc_pos c0 tk - ?D))"
        using ps True by simp
    qed
  next
    case False
    have Dpos: "0 < ?D" using dge1[OF False] by simp
    obtain DD where DD: "?D = Suc DD" using Dpos by (cases ?D) auto
    have ndisp: "DD < ?D" using DD by simp
    have notLE_loop: "\<And>j. j < DD \<Longrightarrow> ktc_tape c0 tk (?start - j) \<noteq> LE4"
    proof -
      fix j assume "j < DD"
      hence "j < ?D" using DD by simp
      thus "ktc_tape c0 tk (?start - j) \<noteq> LE4" by (rule notLE)
    qed
    obtain cmid where
        lstep: "(c0, cmid) \<in> ?R ^^ DD"
      and lst: "ktc_state cmid = (q, AR_SimAdvance, tk, DD, buf, dvec, posk)"
      and lpos: "ktc_pos cmid tk = ?start - DD"
      and ltape: "ktc_tape cmid = ktc_tape c0"
      and lother: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos cmid k' = ktc_pos c0 k'"
      using ar_advance_walk_loop[OF vM qQ stg buf_valid ndisp notLE_loop pad0 src0] by blast
    have DD_lt2k: "DD < 2 * ?k"
      using DD ar_disp_le_2k[OF kpos, of "dvec tk" "posk tk"] by linarith
    have vsrcmid: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                     (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using DD_lt2k buf_valid by (simp add: ar_valid_stage_def)
    have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cmid: "\<forall>j \<ge> k_ktm M. ktc_tape cmid j (ktc_pos cmid j) = BLANK4"
    proof (intro allI impI)
      fix j assume jge: "k_ktm M \<le> j"
      have jne: "j \<noteq> tk" using jge tk_lt by simp
      have "ktc_tape cmid j (ktc_pos cmid j) = ktc_tape c0 j (ktc_pos c0 j)"
        using ltape lother jne by simp
      thus "ktc_tape cmid j (ktc_pos cmid j) = BLANK4" using pad0 jge by simp
    qed
    have src_cmid: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                      (AR_SimAdvance, tk, DD, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have notLE_b: "ktc_tape cmid tk (ktc_pos cmid tk) \<noteq> LE4"
      using ltape lpos notLE[OF ndisp] by simp
    have fire: "(dvec tk = MoveR \<and> DD = 0)
                \<or> (dvec tk \<noteq> MoveR
                    \<and> ktc_tape cmid tk (ktc_pos cmid tk) \<noteq> LE4
                    \<and> Suc DD = ?D)"
      using False notLE_b DD by simp
    obtain c' where
        bstep: "(cmid, c') \<in> ?R"
      and bst: "ktc_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
                  posk(tk := ar_newpos (dvec tk) (posk tk)))"
      and btp: "ktc_tape c' = ktc_tape cmid"
      and bps: "ktc_pos c' = (if dvec tk = MoveR then ktc_pos cmid
                  else (ktc_pos cmid)(tk := ktc_pos cmid tk - 1))"
      using ar_advance_finish_step[OF vM lst qQ last fire vsrcmid pad_cmid src_cmid] by blast
    have bps_ne: "ktc_pos c' = (ktc_pos cmid)(tk := ktc_pos cmid tk - 1)"
      using bps False by simp
    have chainD: "(c0, c') \<in> ?R ^^ ?D"
    proof -
      have "(c0, c') \<in> ?R ^^ Suc DD" by (rule relpow_Suc_I[OF lstep bstep])
      thus ?thesis using DD by simp
    qed
    have ps_final: "ktc_pos c' = (ktc_pos c0)(tk := ?start - ?D)"
    proof (rule ext)
      fix k'
      show "ktc_pos c' k' = ((ktc_pos c0)(tk := ?start - ?D)) k'"
      proof (cases "k' = tk")
        case True
        have "ktc_pos c' tk = ktc_pos cmid tk - 1" using bps_ne by simp
        also have "\<dots> = (?start - DD) - 1" using lpos by simp
        also have "\<dots> = ?start - ?D" using DD by simp
        finally show ?thesis using True by simp
      next
        case False
        have "ktc_pos c' k' = ktc_pos cmid k'" using bps_ne False by simp
        also have "\<dots> = ktc_pos c0 k'" using lother False by simp
        finally show ?thesis using False by simp
      qed
    qed
    have tp_final: "ktc_tape c' = ktc_tape c0" using btp ltape by simp
    show ?thesis
    proof (intro exI[where x = c'] conjI)
      show "(c0, c') \<in> ?R ^^ (if dvec tk = MoveR then 1 else ?D)"
        using chainD False by simp
      show "ktc_state c' = (q, AR_SimNext, k_unidx 0, 0, buf, dvec,
              posk(tk := ar_newpos (dvec tk) (posk tk)))" by (rule bst)
      show "ktc_tape c' = ktc_tape c0" by (rule tp_final)
      show "ktc_pos c' = (if dvec tk = MoveR then ktc_pos c0
              else (ktc_pos c0)(tk := ktc_pos c0 tk - ?D))"
        using ps_final False by simp
    qed
  qed
qed

lemma ar_advance_prefix:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and dge1: "\<forall>k < k_ktm M. dvec k \<noteq> MoveR
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_ktm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k)
                    \<longrightarrow> ktc_tape c0 k (ktc_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_ktm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_ktm M))
         \<and> ktc_state c = (q, AR_SimAdvance, k_unidx j, 0, buf0, dvec,
              (\<lambda>k. if k_idx k < j then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> ktc_tape c = ktc_tape c0
         \<and> ktc_pos c = (\<lambda>k. if k_idx k < j
              then (if dvec k = MoveR then ktc_pos c0 k
                    else ktc_pos c0 k
                           - ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k))
              else ktc_pos c0 k))"
proof (induction j)
  case 0
  let ?pk0 = "\<lambda>k. if k_idx k < (0::nat) then ar_newpos (dvec k) (posk0 k)
                  else posk0 k"
  have "(c0, c0) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ 0" by simp
  moreover have "ktc_state c0 = (q, AR_SimAdvance, k_unidx 0, 0, buf0, dvec, ?pk0)"
    using stg0 by (simp add: k_unidx_zero)
  ultimately show ?case
    by (intro exI[where x = c0] exI[where x = 0]) simp
next
  case (Suc j)
  have sucle: "Suc j \<le> k_ktm M - 1" by (rule Suc.prems)
  have jcard: "j < k_ktm M" using sucle by simp
  have sjcard: "Suc j < k_ktm M" using sucle by simp
  have jle: "j \<le> k_ktm M - 1" using sucle by simp
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)"
  let ?tk = "k_unidx j"
  let ?pk = "\<lambda>i. (\<lambda>k. if k_idx k < i then ar_newpos (dvec k) (posk0 k)
                    else posk0 k)"
  let ?ps = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if dvec k = MoveR then ktc_pos c0 k
                          else ktc_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                    else ktc_pos c0 k)"
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
    and c_st: "ktc_state c = (q, AR_SimAdvance, ?tk, 0, buf0, dvec, ?pk j)"
    and c_tp: "ktc_tape c = ktc_tape c0"
    and c_ps: "ktc_pos c = ?ps j"
    using Suc.IH[OF jle] by blast
  \<comment> \<open>per-tape entry facts for tape \<open>?tk\<close> at config \<open>c\<close>\<close>
  have pkj_tk: "?pk j ?tk = posk0 ?tk" using tkidx by simp
  have psj_tk: "?ps j ?tk = ktc_pos c0 ?tk" using tkidx by simp
  have c_pos_tk: "ktc_pos c ?tk = ktc_pos c0 ?tk" using c_ps psj_tk by simp
  have tk_active: "?tk < k_ktm M" using jcard by (simp add: k_unidx_def)
  have tk_dge1: "dvec ?tk \<noteq> MoveR \<Longrightarrow> 0 < ar_disp ?k (dvec ?tk) (?pk j ?tk)"
    using dge1[rule_format, OF tk_active] pkj_tk by simp
  have tk_notLE: "\<And>m. m < ar_disp ?k (dvec ?tk) (?pk j ?tk)
                    \<Longrightarrow> ktc_tape c ?tk (ktc_pos c ?tk - m) \<noteq> LE4"
  proof -
    fix m assume "m < ar_disp ?k (dvec ?tk) (?pk j ?tk)"
    hence mlt: "m < ar_disp ?k (dvec ?tk) (posk0 ?tk)" using pkj_tk by simp
    have "ktc_tape c ?tk (ktc_pos c ?tk - m) = ktc_tape c0 ?tk (ktc_pos c0 ?tk - m)"
      using c_tp c_pos_tk by simp
    thus "ktc_tape c ?tk (ktc_pos c ?tk - m) \<noteq> LE4"
      using notLE[rule_format, OF tk_active mlt] by simp
  qed
  have tail_idx: "\<And>j'. k_ktm M \<le> j' \<Longrightarrow> \<not> k_idx j' < j"
    using jcard unfolding k_idx_def by linarith
  have pad_c: "\<forall>j' \<ge> k_ktm M. ktc_tape c j' (ktc_pos c j') = BLANK4"
  proof (intro allI impI)
    fix j' assume jge: "k_ktm M \<le> j'"
    have "ktc_tape c j' (ktc_pos c j') = ktc_tape c0 j' (ktc_pos c0 j')"
      using c_tp c_ps tail_idx[OF jge] by simp
    thus "ktc_tape c j' (ktc_pos c j') = BLANK4" using pad0 jge by simp
  qed
  have src_c: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                 (AR_SimAdvance, ?tk, 0, buf0, dvec, ?pk j)"
    using src0 tk_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c' where
      step: "(c, c') \<in> ?R ^^ (if dvec ?tk = MoveR then 1
                else ar_disp ?k (dvec ?tk) (?pk j ?tk))"
    and c'_st: "ktc_state c' = (q, AR_SimAdvance, k_succ ?tk, 0, buf0, dvec,
                  (?pk j)(?tk := ar_newpos (dvec ?tk) (?pk j ?tk)))"
    and c'_tp: "ktc_tape c' = ktc_tape c"
    and c'_ps: "ktc_pos c' = (if dvec ?tk = MoveR then ktc_pos c
                  else (ktc_pos c)(?tk := ktc_pos c ?tk
                         - ar_disp ?k (dvec ?tk) (?pk j ?tk)))"
    using ar_advance_tape_step[OF vM qQ kge2 notlast c_st buf_valid tk_dge1 tk_notLE
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
  have ps_eq: "(if dvec ?tk = MoveR then ktc_pos c
                 else (ktc_pos c)(?tk := ktc_pos c ?tk
                        - ar_disp ?k (dvec ?tk) (?pk j ?tk))) = ?ps (Suc j)"
  proof (rule ext)
    fix k
    show "(if dvec ?tk = MoveR then ktc_pos c
            else (ktc_pos c)(?tk := ktc_pos c ?tk
                   - ar_disp ?k (dvec ?tk) (?pk j ?tk))) k = ?ps (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using c_ps tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False c_ps by (simp add: less_Suc_eq)
    qed
  qed
  have chain: "(c0, c') \<in> ?R ^^ (m + (if dvec ?tk = MoveR then 1
                  else ar_disp ?k (dvec ?tk) (?pk j ?tk)))"
  proof -
    have "(c0, c') \<in> ?R ^^ m
                       O ?R ^^ (if dvec ?tk = MoveR then 1
                                else ar_disp ?k (dvec ?tk) (?pk j ?tk))"
      using cm_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m + (if dvec ?tk = MoveR then 1
                 else ar_disp ?k (dvec ?tk) (?pk j ?tk)) \<le> Suc j * (2 * ?k)"
    using m_le kpos ar_disp_le_2k[OF kpos, of "dvec ?tk" "?pk j ?tk"]
    by (cases "dvec ?tk = MoveR") auto
  show ?case
  proof (intro exI[where x = c']
           exI[where x = "m + (if dvec ?tk = MoveR then 1
                  else ar_disp ?k (dvec ?tk) (?pk j ?tk))"] conjI)
    show "(c0, c') \<in> ?R ^^ (m + (if dvec ?tk = MoveR then 1
            else ar_disp ?k (dvec ?tk) (?pk j ?tk)))" by (rule chain)
    show "m + (if dvec ?tk = MoveR then 1
            else ar_disp ?k (dvec ?tk) (?pk j ?tk)) \<le> Suc j * (2 * ?k)"
      by (rule bound)
    show "ktc_state c' = (q, AR_SimAdvance, k_unidx (Suc j), 0, buf0, dvec,
            ?pk (Suc j))"
      using c'_st ksucc pk_eq by simp
    show "ktc_tape c' = ktc_tape c0" using c'_tp c_tp by simp
    show "ktc_pos c' = ?ps (Suc j)" using c'_ps ps_eq by simp
  qed
qed

lemma ar_advance_phase:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
      and buf_valid: "\<forall>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and dge1: "\<forall>k < k_ktm M. dvec k \<noteq> MoveR
                  \<longrightarrow> 0 < ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k)"
      and notLE: "\<forall>k < k_ktm M. \<forall>m. m < ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k)
                    \<longrightarrow> ktc_tape c0 k (ktc_pos c0 k - m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimAdvance, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ m
         \<and> m \<le> k_ktm M * (2 * block_width (\<Gamma>_ktm M))
         \<and> ktc_state c = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
              (\<lambda>k. if k < k_ktm M then ar_newpos (dvec k) (posk0 k)
                    else posk0 k))
         \<and> ktc_tape c = ktc_tape c0
         \<and> ktc_pos c = (\<lambda>k. if k < k_ktm M
              then (if dvec k = MoveR then ktc_pos c0 k
                    else ktc_pos c0 k - ar_disp (block_width (\<Gamma>_ktm M)) (dvec k) (posk0 k))
              else ktc_pos c0 k)"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?N = "k_ktm M"
  let ?m1 = "?N - 1"
  let ?tl = "k_unidx ?m1"
  have card1: "0 < ?N" using vM by (cases M) auto
  have m1suc: "?N = Suc ?m1" using card1 by simp
  have m1card: "?m1 < ?N" using card1 by simp
  have m1lt: "?m1 < k_ktm M" using card1 by simp
  have kpos: "0 < ?k" using kge2 by simp
  have tl_eq: "?tl = ?m1" by (simp add: k_unidx_def)
  have tlidx: "k_idx ?tl = ?m1" by (rule k_idx_unidx[OF m1card])
  have tl_active: "?tl < k_ktm M" using m1lt tl_eq by simp
  have islast: "is_last_k M ?tl" using is_last_k_unidx[OF m1card] m1suc by simp
  have cond: "(k < ?m1) = (k < k_ktm M)" if "k \<noteq> ?m1" for k
    using that m1suc by (auto simp: less_Suc_eq)
  let ?pk = "\<lambda>k. if k_idx k < ?m1 then ar_newpos (dvec k) (posk0 k)
                  else posk0 k"
  let ?ps = "\<lambda>k. if k_idx k < ?m1
                  then (if dvec k = MoveR then ktc_pos c0 k
                        else ktc_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                  else ktc_pos c0 k"
  have m1le: "?m1 \<le> k_ktm M - 1" by simp
  obtain c1 m1 where
      c1_rel: "(c0, c1) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ m1"
    and m1_le: "m1 \<le> ?m1 * (2 * ?k)"
    and c1_st: "ktc_state c1 = (q, AR_SimAdvance, ?tl, 0, buf0, dvec, ?pk)"
    and c1_tp: "ktc_tape c1 = ktc_tape c0"
    and c1_ps: "ktc_pos c1 = ?ps"
    using ar_advance_prefix[OF vM qQ kge2 stg0 buf_valid dge1 notLE pad0 src0 m1le]
    by blast
  have pk_tl: "?pk ?tl = posk0 ?tl" using tlidx by simp
  have c1_pos_tl: "ktc_pos c1 ?tl = ktc_pos c0 ?tl" using c1_ps tlidx by simp
  have tl_dge1: "dvec ?tl \<noteq> MoveR \<Longrightarrow> 0 < ar_disp ?k (dvec ?tl) (?pk ?tl)"
    using dge1[rule_format, OF tl_active] pk_tl by simp
  have tl_notLE: "\<And>m. m < ar_disp ?k (dvec ?tl) (?pk ?tl)
                    \<Longrightarrow> ktc_tape c1 ?tl (ktc_pos c1 ?tl - m) \<noteq> LE4"
  proof -
    fix m assume "m < ar_disp ?k (dvec ?tl) (?pk ?tl)"
    hence mlt: "m < ar_disp ?k (dvec ?tl) (posk0 ?tl)" using pk_tl by simp
    have "ktc_tape c1 ?tl (ktc_pos c1 ?tl - m) = ktc_tape c0 ?tl (ktc_pos c0 ?tl - m)"
      using c1_tp c1_pos_tl by simp
    thus "ktc_tape c1 ?tl (ktc_pos c1 ?tl - m) \<noteq> LE4"
      using notLE[rule_format, OF tl_active mlt] by simp
  qed
  have tail_idx: "\<And>j. k_ktm M \<le> j \<Longrightarrow> \<not> k_idx j < ?m1"
    using m1suc unfolding k_idx_def by linarith
  have pad_c1: "\<forall>j \<ge> k_ktm M. ktc_tape c1 j (ktc_pos c1 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have "ktc_tape c1 j (ktc_pos c1 j) = ktc_tape c0 j (ktc_pos c0 j)"
      using c1_tp c1_ps tail_idx[OF jge] by simp
    thus "ktc_tape c1 j (ktc_pos c1 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c1: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimAdvance, ?tl, 0, buf0, dvec, ?pk)"
    using src0 tl_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c2 where
      step: "(c1, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ (if dvec ?tl = MoveR then 1
                else ar_disp ?k (dvec ?tl) (?pk ?tl))"
    and c2_st: "ktc_state c2 = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
                  ?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl)))"
    and c2_tp: "ktc_tape c2 = ktc_tape c1"
    and c2_ps: "ktc_pos c2 = (if dvec ?tl = MoveR then ktc_pos c1
                  else (ktc_pos c1)(?tl := ktc_pos c1 ?tl
                         - ar_disp ?k (dvec ?tl) (?pk ?tl)))"
    using ar_advance_tape_finish_step[OF vM qQ kge2 islast c1_st buf_valid
                                          tl_dge1 tl_notLE pad_c1 src_c1]
    by blast
  \<comment> \<open>The last-tape \<open>fun_upd\<close>s collapse to active-guarded
     vectors: active tapes take the \<open>ar_newpos\<close> / displaced
     value, padding tapes stay frozen at the entry \<open>posk0\<close> /
     position.\<close>
  have pk_full: "?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl))
                   = (\<lambda>k. if k < k_ktm M then ar_newpos (dvec k) (posk0 k)
                          else posk0 k)"
  proof (rule ext)
    fix k
    show "(?pk(?tl := ar_newpos (dvec ?tl) (?pk ?tl))) k
            = (if k < k_ktm M then ar_newpos (dvec k) (posk0 k) else posk0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using pk_tl tl_active by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] by (simp add: k_idx_def)
    qed
  qed
  have ps_full: "(if dvec ?tl = MoveR then ktc_pos c1
                   else (ktc_pos c1)(?tl := ktc_pos c1 ?tl
                          - ar_disp ?k (dvec ?tl) (?pk ?tl)))
                   = (\<lambda>k. if k < k_ktm M
                          then (if dvec k = MoveR then ktc_pos c0 k
                                else ktc_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
                          else ktc_pos c0 k)"
  proof (rule ext)
    fix k
    show "(if dvec ?tl = MoveR then ktc_pos c1
            else (ktc_pos c1)(?tl := ktc_pos c1 ?tl
                   - ar_disp ?k (dvec ?tl) (?pk ?tl))) k
            = (if k < k_ktm M
               then (if dvec k = MoveR then ktc_pos c0 k
                     else ktc_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
               else ktc_pos c0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using c1_pos_tl pk_tl tl_active by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] c1_ps by (simp add: k_idx_def)
    qed
  qed
  have chain: "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ (m1 + (if dvec ?tl = MoveR then 1
                  else ar_disp ?k (dvec ?tl) (?pk ?tl)))"
  proof -
    have "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ m1
                       O (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ (if dvec ?tl = MoveR then 1
                                else ar_disp ?k (dvec ?tl) (?pk ?tl))"
      using c1_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m1 + (if dvec ?tl = MoveR then 1
                 else ar_disp ?k (dvec ?tl) (?pk ?tl)) \<le> ?N * (2 * ?k)"
  proof -
    obtain Nm where Nm: "?N = Suc Nm" using card1 by (cases ?N) auto
    have e1: "?N * (2 * ?k) = (2 * ?k) + Nm * (2 * ?k)" by (simp add: Nm)
    have e2: "m1 \<le> Nm * (2 * ?k)" using m1_le Nm by simp
    have e3: "(if dvec ?tl = MoveR then 1 else ar_disp ?k (dvec ?tl) (?pk ?tl))
                \<le> 2 * ?k"
      using ar_disp_le_2k[OF kpos, of "dvec ?tl" "?pk ?tl"] kpos
      by (cases "dvec ?tl = MoveR") auto
    show ?thesis using e1 e2 e3 by linarith
  qed
  show ?thesis
  proof (intro exI[where x = c2]
           exI[where x = "m1 + (if dvec ?tl = MoveR then 1
                  else ar_disp ?k (dvec ?tl) (?pk ?tl))"] conjI)
    show "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_advance M)) ^^ (m1 + (if dvec ?tl = MoveR then 1
            else ar_disp ?k (dvec ?tl) (?pk ?tl)))" by (rule chain)
    show "m1 + (if dvec ?tl = MoveR then 1
            else ar_disp ?k (dvec ?tl) (?pk ?tl)) \<le> ?N * (2 * ?k)"
      by (rule bound)
    show "ktc_state c2 = (q, AR_SimNext, k_unidx 0, 0, buf0, dvec,
            (\<lambda>k. if k < k_ktm M then ar_newpos (dvec k) (posk0 k) else posk0 k))"
      using c2_st pk_full by simp
    show "ktc_tape c2 = ktc_tape c0" using c2_tp c1_tp by simp
    show "ktc_pos c2 = (\<lambda>k. if k < k_ktm M
            then (if dvec k = MoveR then ktc_pos c0 k
                  else ktc_pos c0 k - ar_disp ?k (dvec k) (posk0 k))
            else ktc_pos c0 k)"
      using c2_ps ps_full by simp
  qed
qed

end
