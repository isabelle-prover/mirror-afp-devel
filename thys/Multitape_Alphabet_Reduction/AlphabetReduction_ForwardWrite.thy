theory AlphabetReduction_ForwardWrite
  imports AlphabetReduction_ForwardRead
begin

subsection \<open>Write phase composition\<close>

lemma ar_write_back_loop:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "ktc_state c0 = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c0 tk = base + block_width (\<Gamma>_ktm M)"
      and notLE: "\<And>m. \<lbrakk> 1 \<le> m; m \<le> block_width (\<Gamma>_ktm M) \<rbrakk>
                   \<Longrightarrow> ktc_tape c0 tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ block_width (\<Gamma>_ktm M)
              \<and> ktc_state c' = (q, AR_SimWrite, tk, block_width (\<Gamma>_ktm M),
                                  buf, dvec, posk)
              \<and> ktc_pos c' tk = base
              \<and> ktc_tape c' = ktc_tape c0
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k')"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?P = "\<lambda>j c.
       ktc_state c = (q, AR_SimWrite, tk, j, buf, dvec, posk)
     \<and> ktc_pos c tk = base + (?k - j)
     \<and> ktc_tape c = ktc_tape c0
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c k' = ktc_pos c0 k')"
  have mybase: "?P 0 c0" using stg pos_base by simp
  have mystep:
      "\<And>j cc. \<lbrakk> j < ?k; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < ?k" and Pj: "?P j cc"
    from Pj have st_cc:
        "ktc_state cc = (q, AR_SimWrite, tk, j, buf, dvec, posk)"
      and pos_cc: "ktc_pos cc tk = base + (?k - j)"
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
                    (AR_SimWrite, tk, j, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have mge1: "1 \<le> ?k - j" using jlt by simp
    have mlek: "?k - j \<le> ?k" by simp
    have suc_le: "Suc j \<le> ?k" using jlt by simp
    have jlt2: "j < 2 * ?k" using jlt by simp
    have ksub: "?k - j = Suc (?k - Suc j)" using jlt by simp
    have vsrc_cc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                     (AR_SimWrite, tk, j, buf, dvec, posk)"
      using jlt2 buf_valid by (simp add: ar_valid_stage_def)
    have notLE_cc: "ktc_tape cc tk (ktc_pos cc tk) \<noteq> LE4"
      using tape_cc pos_cc notLE[OF mge1 mlek] by simp
    obtain c'' where
        bstep: "(cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))"
      and bst_state: "ktc_state c'' = (q, AR_SimWrite, tk, Suc j, buf, dvec, posk)"
      and bst_tape: "ktc_tape c'' = ktc_tape cc"
      and bst_pos: "ktc_pos c'' = (ktc_pos cc)(tk := ktc_pos cc tk - 1)"
      using ar_write_walk_step
              [OF vM st_cc qQ poskproper notLE_cc suc_le vsrc_cc pad_cc src_cc]
      by blast
    have pos_eq: "ktc_pos c'' tk = base + (?k - Suc j)"
      using bst_pos pos_cc ksub by simp
    have tape_eq: "ktc_tape c'' = ktc_tape c0" using bst_tape tape_cc by simp
    have other_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c'' k' = ktc_pos c0 k'"
      using bst_pos other_cc by simp
    show "\<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))
                \<and> ?P (Suc j) c''"
      using bstep bst_state pos_eq tape_eq other_eq by blast
  qed
  have loop:
      "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ ?k
            \<and> ?P ?k c'"
    by (rule relpow_invariant_chain
          [where P = ?P and n = ?k, OF mystep mybase])
  obtain c' where
      chain: "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ ?k"
    and Pfin: "?P ?k c'"
    using loop by blast
  show ?thesis
  proof (intro exI[where x = c'] conjI)
    show "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ ?k" by (rule chain)
    show "ktc_state c' = (q, AR_SimWrite, tk, ?k, buf, dvec, posk)"
      using Pfin by simp
    show "ktc_pos c' tk = base" using Pfin by simp
    show "ktc_tape c' = ktc_tape c0" using Pfin by simp
    show "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k'" using Pfin by simp
  qed
qed

text \<open>The write forward bit-write loop, proper tape.  From an
  \<open>AR_SimWrite\<close> stage at bit-counter \<open>b\<close> with the head back
  at \<open>base\<close> (where \<open>ar_write_back_loop\<close> left it), the head
  walks \<open>R\<close> across the block writing each cell, reaching
  bit-counter \<open>b + (b - 1)\<close> with the head at \<open>base + (b -
  1)\<close>.  Unlike the read loops this loop \<^emph>\<open>mutates\<close> the
  tape: its invariant carries a partially-overwritten tape (cells
  \<open>base \<dots> base + j - 1\<close> already hold the new
  \<open>write_bit\<close> image, the rest hold old content), and each
  \<open>ar_write_bit_step\<close>'s \<open>\<noteq> LE4\<close> guard reads the
  \<^emph>\<open>not-yet-written\<close> current cell \<open>base + j\<close>, which
  still holds old content (supplied \<open>\<noteq> LE4\<close> by
  \<open>notLE\<close>).  Writes the first \<open>b - 1\<close> cells; the last is
  the boundary step's job.  Chain length \<open>b - 1\<close>.\<close>

lemma ar_write_fwd_loop:
  fixes M :: "('q, 'a) ktm"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "ktc_state c0 = (q, AR_SimWrite, tk, block_width (\<Gamma>_ktm M),
                                 buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c0 tk = base"
      and notLE: "\<And>m. m < block_width (\<Gamma>_ktm M)
                   \<Longrightarrow> ktc_tape c0 tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, block_width (\<Gamma>_ktm M), buf, dvec, posk)"
  shows "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (block_width (\<Gamma>_ktm M) - 1)
              \<and> ktc_state c' = (q, AR_SimWrite, tk,
                    block_width (\<Gamma>_ktm M) + (block_width (\<Gamma>_ktm M) - 1),
                    buf, dvec, posk)
              \<and> ktc_pos c' tk = base + (block_width (\<Gamma>_ktm M) - 1)
              \<and> ktc_tape c' tk = (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + (block_width (\<Gamma>_ktm M) - 1)
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
                    else ktc_tape c0 tk pos)
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape c' k' = ktc_tape c0 k')
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k')"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?G = "\<Gamma>_ktm M" and ?bl = "bl_ktm M"
  let ?wb = "\<lambda>m. write_bit ?G ?bl (buf tk) m"
  let ?tape = "\<lambda>j pos. if base \<le> pos \<and> pos < base + j
                        then ?wb (pos - base) else ktc_tape c0 tk pos"
  let ?P = "\<lambda>j c.
       ktc_state c = (q, AR_SimWrite, tk, ?k + j, buf, dvec, posk)
     \<and> ktc_pos c tk = base + j
     \<and> ktc_tape c tk = ?tape j
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape c k' = ktc_tape c0 k')
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c k' = ktc_pos c0 k')"
  have mybase: "?P 0 c0"
  proof -
    have "?tape 0 = ktc_tape c0 tk" by (rule ext) auto
    thus ?thesis using stg pos_base by simp
  qed
  have mystep:
      "\<And>j cc. \<lbrakk> j < ?k - 1; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < ?k - 1" and Pj: "?P j cc"
    from Pj have st_cc:
        "ktc_state cc = (q, AR_SimWrite, tk, ?k + j, buf, dvec, posk)"
      and pos_cc: "ktc_pos cc tk = base + j"
      and tape_cc: "ktc_tape cc tk = ?tape j"
      and otape_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape cc k' = ktc_tape c0 k'"
      and opos_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos cc k' = ktc_pos c0 k'"
      by simp_all
    have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cc: "\<forall>j' \<ge> k_ktm M. ktc_tape cc j' (ktc_pos cc j') = BLANK4"
    proof (intro allI impI)
      fix j' assume jge: "k_ktm M \<le> j'"
      have jne: "j' \<noteq> tk" using jge tk_lt by simp
      have "ktc_tape cc j' (ktc_pos cc j') = ktc_tape c0 j' (ktc_pos c0 j')"
        using otape_cc opos_cc jne by simp
      thus "ktc_tape cc j' (ktc_pos cc j') = BLANK4" using pad0 jge by simp
    qed
    have src_cc: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                    (AR_SimWrite, tk, ?k + j, buf, dvec, posk)"
      using src0 by (simp add: ar_stage_bounded_def)
    have jltk: "j < ?k" using jlt by simp
    have ilo: "?k \<le> ?k + j" by simp
    have ihi: "Suc (?k + j) < 2 * ?k" using jlt by simp
    have idx: "?k + j - ?k = j" by simp
    have vsrc_cc: "ar_valid_stage ?G ?bl
                     (AR_SimWrite, tk, ?k + j, buf, dvec, posk)"
      using ihi buf_valid by (simp add: ar_valid_stage_def)
    have cell_cur: "ktc_tape cc tk (ktc_pos cc tk) = ktc_tape c0 tk (base + j)"
      using tape_cc pos_cc by simp
    have notLE_cc: "ktc_tape cc tk (ktc_pos cc tk) \<noteq> LE4"
      using cell_cur notLE[OF jltk] by simp
    obtain c'' where
        bstep: "(cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))"
      and bst_state: "ktc_state c'' = (q, AR_SimWrite, tk, Suc (?k + j),
                                        buf, dvec, posk)"
      and bst_tape: "ktc_tape c'' = (ktc_tape cc)(tk :=
            (ktc_tape cc tk)(ktc_pos cc tk := ?wb (?k + j - ?k)))"
      and bst_pos: "ktc_pos c'' = (ktc_pos cc)(tk := Suc (ktc_pos cc tk))"
      using ar_write_bit_step
              [OF vM st_cc qQ poskproper notLE_cc ilo ihi vsrc_cc pad_cc src_cc]
      by blast
    have state_eq: "ktc_state c'' = (q, AR_SimWrite, tk, ?k + Suc j, buf, dvec, posk)"
      using bst_state by simp
    have pos_eq: "ktc_pos c'' tk = base + Suc j"
      using bst_pos pos_cc by simp
    have lhs: "ktc_tape c'' tk = (?tape j)(base + j := ?wb j)"
      using bst_tape tape_cc pos_cc idx by simp
    have tape_eq: "ktc_tape c'' tk = ?tape (Suc j)"
    proof (rule ext)
      fix pos
      show "ktc_tape c'' tk pos = ?tape (Suc j) pos"
      proof (cases "pos = base + j")
        case True
        thus ?thesis using lhs by simp
      next
        case False
        have "ktc_tape c'' tk pos = ?tape j pos" using lhs False by simp
        thus ?thesis using False by (auto simp: less_Suc_eq)
      qed
    qed
    have otape_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape c'' k' = ktc_tape c0 k'"
      using bst_tape otape_cc by simp
    have opos_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c'' k' = ktc_pos c0 k'"
      using bst_pos opos_cc by simp
    show "\<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M))
                \<and> ?P (Suc j) c''"
      using bstep state_eq pos_eq tape_eq otape_eq opos_eq by blast
  qed
  have loop:
      "\<exists>c'. (c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (?k - 1)
            \<and> ?P (?k - 1) c'"
    by (rule relpow_invariant_chain
          [where P = ?P and n = "?k - 1", OF mystep mybase])
  obtain c' where
      chain: "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (?k - 1)"
    and Pfin: "?P (?k - 1) c'"
    using loop by blast
  show ?thesis
  proof (intro exI[where x = c'] conjI)
    show "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (?k - 1)"
      by (rule chain)
    show "ktc_state c' = (q, AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
      using Pfin by simp
    show "ktc_pos c' tk = base + (?k - 1)" using Pfin by simp
    show "ktc_tape c' tk = (\<lambda>pos.
            if base \<le> pos \<and> pos < base + (?k - 1)
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
            else ktc_tape c0 tk pos)"
      using Pfin by simp
    show "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape c' k' = ktc_tape c0 k'" using Pfin by simp
    show "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c' k' = ktc_pos c0 k'" using Pfin by simp
  qed
qed

text \<open>The proper-cell single-tape write prefix: the part of a
  proper-cell single-tape write shared by the non-last
  (\<open>boundary\<close>) and last (\<open>finish\<close>) variants.  From an
  \<open>AR_SimWrite\<close> stage at bit-counter \<open>0\<close> with the head at
  the block end \<open>base + b\<close> and \<open>buf tk\<close> a proper symbol,
  it fires the back-walk loop (\<open>ar_write_back_loop\<close>, head to
  \<open>base\<close>) and the forward bit-write loop
  (\<open>ar_write_fwd_loop\<close>, writing the first \<open>b - 1\<close>
  cells), reaching bit-counter \<open>b + (b - 1)\<close> with the head at
  \<open>base + (b - 1)\<close>.  The remaining last-cell step (boundary or
  finish) is added by the consumer.  The two segment costs compose by
  \<open>relpow_add\<close> on \<open>relcompI\<close> (chain length \<open>b + (b
  - 1)\<close>).  The \<open>notLE\<close> hypothesis (every block cell and the
  next-block lead cell \<open>\<noteq> LE4\<close>) feeds both loops.\<close>

lemma ar_write_proper_prefix:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "ktc_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c' tk = base + block_width (\<Gamma>_ktm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_ktm M)
                   \<Longrightarrow> ktc_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c2. (c', c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (block_width (\<Gamma>_ktm M) + (block_width (\<Gamma>_ktm M) - 1))
              \<and> ktc_state c2 = (q, AR_SimWrite, tk,
                    block_width (\<Gamma>_ktm M) + (block_width (\<Gamma>_ktm M) - 1),
                    buf, dvec, posk)
              \<and> ktc_tape c2 = (ktc_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + (block_width (\<Gamma>_ktm M) - 1)
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
                    else ktc_tape c' tk pos))
              \<and> ktc_pos c2 = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)"
  have notLE_back: "\<And>m. \<lbrakk> 1 \<le> m; m \<le> ?k \<rbrakk>
                      \<Longrightarrow> ktc_tape c' tk (base + m) \<noteq> LE4"
    using notLE by blast
  obtain c1 where
      ch1: "(c', c1) \<in> ?R ^^ ?k"
    and st1: "ktc_state c1 = (q, AR_SimWrite, tk, ?k, buf, dvec, posk)"
    and pos1: "ktc_pos c1 tk = base"
    and tape1: "ktc_tape c1 = ktc_tape c'"
    and opos1: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c1 k' = ktc_pos c' k'"
    using ar_write_back_loop[OF vM qQ kge2 poskproper stg buf_valid pos_base notLE_back
                       pad0 src0]
    by blast
  have notLE_fwd: "\<And>m. m < ?k \<Longrightarrow> ktc_tape c1 tk (base + m) \<noteq> LE4"
  proof -
    fix m :: nat assume mlt: "m < ?k"
    have mle: "m \<le> ?k" using mlt by simp
    show "ktc_tape c1 tk (base + m) \<noteq> LE4"
      using notLE[OF mle] tape1 by simp
  qed
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c1: "\<forall>j \<ge> k_ktm M. ktc_tape c1 j (ktc_pos c1 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c1 j (ktc_pos c1 j) = ktc_tape c' j (ktc_pos c' j)"
      using tape1 opos1 jne by simp
    thus "ktc_tape c1 j (ktc_pos c1 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c1: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimWrite, tk, block_width (\<Gamma>_ktm M), buf, dvec, posk)"
    using src0 by (simp add: ar_stage_bounded_def)
  obtain c2 where
      ch2: "(c1, c2) \<in> ?R ^^ (?k - 1)"
    and st2: "ktc_state c2 = (q, AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
    and pos2: "ktc_pos c2 tk = base + (?k - 1)"
    and tape2: "ktc_tape c2 tk = (\<lambda>pos.
          if base \<le> pos \<and> pos < base + (?k - 1)
          then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
          else ktc_tape c1 tk pos)"
    and otape2: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_tape c2 k' = ktc_tape c1 k'"
    and opos2: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c2 k' = ktc_pos c1 k'"
    using ar_write_fwd_loop[OF vM qQ kge2 poskproper st1 buf_valid pos1 notLE_fwd
                      pad_c1 src_c1]
    by blast
  have ch12: "(c', c2) \<in> ?R ^^ (?k + (?k - 1))"
  proof -
    have "(c', c2) \<in> ?R ^^ ?k O ?R ^^ (?k - 1)" using ch1 ch2 by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have tape_final: "ktc_tape c2 = (ktc_tape c')(tk := (\<lambda>pos.
          if base \<le> pos \<and> pos < base + (?k - 1)
          then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
          else ktc_tape c' tk pos))"
  proof (rule ext)
    fix k'
    show "ktc_tape c2 k' = ((ktc_tape c')(tk := (\<lambda>pos.
            if base \<le> pos \<and> pos < base + (?k - 1)
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
            else ktc_tape c' tk pos))) k'"
    proof (cases "k' = tk")
      case True
      have "ktc_tape c2 tk = (\<lambda>pos.
              if base \<le> pos \<and> pos < base + (?k - 1)
              then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
              else ktc_tape c' tk pos)"
      proof (rule ext)
        fix pos
        show "ktc_tape c2 tk pos = (if base \<le> pos \<and> pos < base + (?k - 1)
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
                else ktc_tape c' tk pos)"
          using tape2 tape1 by simp
      qed
      thus ?thesis using True by simp
    next
      case False
      have "ktc_tape c2 k' = ktc_tape c1 k'" using otape2 False by simp
      also have "\<dots> = ktc_tape c' k'" using tape1 by simp
      finally show ?thesis using False by simp
    qed
  qed
  have pos_final: "ktc_pos c2 = (ktc_pos c')(tk := base + (?k - 1))"
  proof (rule ext)
    fix k'
    show "ktc_pos c2 k' = ((ktc_pos c')(tk := base + (?k - 1))) k'"
    proof (cases "k' = tk")
      case True thus ?thesis using pos2 by simp
    next
      case False
      have "ktc_pos c2 k' = ktc_pos c1 k'" using opos2 False by simp
      also have "\<dots> = ktc_pos c' k'" using opos1 False by simp
      finally show ?thesis using False by simp
    qed
  qed
  show ?thesis
  proof (intro exI[where x = c2] conjI)
    show "(c', c2) \<in> ?R ^^ (?k + (?k - 1))" by (rule ch12)
    show "ktc_state c2 = (q, AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
      by (rule st2)
    show "ktc_tape c2 = (ktc_tape c')(tk := (\<lambda>pos.
            if base \<le> pos \<and> pos < base + (?k - 1)
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
            else ktc_tape c' tk pos))"
      by (rule tape_final)
    show "ktc_pos c2 = (ktc_pos c')(tk := base + (?k - 1))" by (rule pos_final)
  qed
qed

text \<open>Extend a written block prefix by its last cell.  Both
  proper-write finishers reach a tape whose first \<open>b - 1\<close> block
  cells already hold the new \<open>write_bit\<close> image; the boundary /
  finish step writes the last cell \<open>base + (b - 1)\<close>.  This
  \<open>fun_upd\<close> closes the gap: updating the \<open>b - 1\<close>-prefix
  function at \<open>base + (b - 1)\<close> with \<open>f (b - 1)\<close> yields
  the full \<open>b\<close>-cell write.  Pure list/function arithmetic, shared
  by \<open>ar_write_proper_step\<close> and
  \<open>ar_write_proper_finish_step\<close>.\<close>

lemma write_block_extend:
  fixes k base :: nat and f g :: "nat \<Rightarrow> sym4"
  assumes "0 < k"
  shows "((\<lambda>pos. if base \<le> pos \<and> pos < base + (k - 1)
                  then f (pos - base) else g pos)
            (base + (k - 1) := f (k - 1)))
         = (\<lambda>pos. if base \<le> pos \<and> pos < base + k
                  then f (pos - base) else g pos)"
proof -
  obtain kk where k: "k = Suc kk" using assms by (cases k) auto
  show ?thesis
  proof (rule ext)
    fix pos
    show "((\<lambda>pos. if base \<le> pos \<and> pos < base + (k - 1)
                   then f (pos - base) else g pos)
             (base + (k - 1) := f (k - 1))) pos
          = (if base \<le> pos \<and> pos < base + k then f (pos - base) else g pos)"
    proof (cases "pos = base + (k - 1)")
      case True
      thus ?thesis using k by simp
    next
      case False
      thus ?thesis using k by (auto simp: less_Suc_eq)
    qed
  qed
qed

text \<open>The proper-cell single-tape write, non-last tape: the prefix
  followed by the bit-boundary step (\<open>ar_write_bit_boundary_step\<close>),
  writing the last block cell \<open>base + (b - 1)\<close> and landing at the
  next tape's \<open>AR_SimWrite\<close> (\<open>k_succ tk\<close>, counter
  \<open>0\<close>).  After the \<open>2b\<close>-step walk the \<open>b\<close>-cell
  block at \<open>base\<close> spells out \<open>write_bit (buf tk)\<close> (the
  encoded new symbol), every other cell unchanged, and the head returns
  to the block end \<open>base + b\<close>.  Chain length \<open>2b\<close>.\<close>

lemma ar_write_proper_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and notlast: "\<not> is_last_k M tk"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "ktc_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c' tk = base + block_width (\<Gamma>_ktm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_ktm M)
                   \<Longrightarrow> ktc_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (2 * block_width (\<Gamma>_ktm M))
              \<and> ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> ktc_tape c'' = (ktc_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + block_width (\<Gamma>_ktm M)
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
                    else ktc_tape c' tk pos))
              \<and> ktc_pos c'' = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)"
  let ?wb = "\<lambda>m. write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) m"
  let ?part = "\<lambda>pos. if base \<le> pos \<and> pos < base + (?k - 1)
                       then ?wb (pos - base) else ktc_tape c' tk pos"
  let ?full = "\<lambda>pos. if base \<le> pos \<and> pos < base + ?k
                       then ?wb (pos - base) else ktc_tape c' tk pos"
  have kpos: "0 < ?k" using kge2 by simp
  obtain kk where kdef: "?k = Suc kk" using kge2 by (cases ?k) auto
  obtain c2 where
      ch_pre: "(c', c2) \<in> ?R ^^ (?k + (?k - 1))"
    and st2: "ktc_state c2 = (q, AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
    and tape2: "ktc_tape c2 = (ktc_tape c')(tk := ?part)"
    and pos2: "ktc_pos c2 = (ktc_pos c')(tk := base + (?k - 1))"
    using ar_write_proper_prefix[OF vM qQ kge2 poskproper stg buf_valid pos_base notLE
                         pad0 src0]
    by blast
  have c2tk: "ktc_tape c2 tk = ?part" using tape2 by simp
  have pos2_tk: "ktc_pos c2 tk = base + (?k - 1)" using pos2 by simp
  have ihi: "Suc (?k + (?k - 1)) = 2 * ?k" using kdef by simp
  have lt2: "?k + (?k - 1) < 2 * ?k" using kdef by simp
  have vsrc2: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                 (AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
    using lt2 buf_valid by (simp add: ar_valid_stage_def)
  have cell_cur: "ktc_tape c2 tk (ktc_pos c2 tk) = ktc_tape c' tk (base + (?k - 1))"
  proof -
    have "ktc_tape c2 tk (base + (?k - 1)) = ktc_tape c' tk (base + (?k - 1))"
      using c2tk by simp
    thus ?thesis using pos2_tk by simp
  qed
  have km1le: "?k - 1 \<le> ?k" by simp
  have notLE2: "ktc_tape c2 tk (ktc_pos c2 tk) \<noteq> LE4"
    using cell_cur notLE[OF km1le] by simp
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c2: "\<forall>j \<ge> k_ktm M. ktc_tape c2 j (ktc_pos c2 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c2 j (ktc_pos c2 j) = ktc_tape c' j (ktc_pos c' j)"
      using tape2 pos2 jne by simp
    thus "ktc_tape c2 j (ktc_pos c2 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c2: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimWrite, tk, block_width (\<Gamma>_ktm M) + (block_width (\<Gamma>_ktm M) - 1),
                   buf, dvec, posk)"
    using src0 by (simp add: ar_stage_bounded_def)
  obtain c3 where
      s3: "(c2, c3) \<in> ?R"
    and st3: "ktc_state c3 = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
    and tape3: "ktc_tape c3 = (ktc_tape c2)(tk :=
          (ktc_tape c2 tk)(ktc_pos c2 tk := ?wb (?k + (?k - 1) - ?k)))"
    and pos3: "ktc_pos c3 = (ktc_pos c2)(tk := Suc (ktc_pos c2 tk))"
    using ar_write_bit_boundary_step[OF vM st2 qQ poskproper notLE2 notlast ihi vsrc2
                           pad_c2 src_c2]
    by blast
  \<comment> \<open>chain: prefix \<open>b + (b - 1)\<close> then one boundary step = \<open>2b\<close>\<close>
  have ch_full: "(c', c3) \<in> ?R ^^ (2 * ?k)"
  proof -
    have h: "(c', c3) \<in> ?R ^^ Suc (?k + (?k - 1))"
      by (rule relpow_Suc_I[OF ch_pre s3])
    from h show ?thesis by (simp only: ihi)
  qed
  \<comment> \<open>tape: the last block cell \<open>base + (b - 1)\<close> completes the write\<close>
  have tape3_tk: "ktc_tape c3 tk = (?part(base + (?k - 1) := ?wb (?k - 1)))"
    using tape3 pos2_tk c2tk by simp
  have tape3_tk_full: "ktc_tape c3 tk = ?full"
    using tape3_tk write_block_extend[OF kpos, of base ?wb "ktc_tape c' tk"] by simp
  have tape_final: "ktc_tape c3 = (ktc_tape c')(tk := ?full)"
  proof (rule ext)
    fix k'
    show "ktc_tape c3 k' = ((ktc_tape c')(tk := ?full)) k'"
    proof (cases "k' = tk")
      case True thus ?thesis using tape3_tk_full by simp
    next
      case False
      have "ktc_tape c3 k' = ktc_tape c2 k'" using tape3 False by simp
      also have "\<dots> = ktc_tape c' k'" using tape2 False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have pos_final: "ktc_pos c3 = (ktc_pos c')(tk := base + ?k)"
  proof -
    have "ktc_pos c3 = (ktc_pos c2)(tk := Suc (ktc_pos c2 tk))" by (rule pos3)
    also have "\<dots> = (ktc_pos c2)(tk := base + ?k)" using pos2_tk kdef by simp
    also have "\<dots> = (ktc_pos c')(tk := base + ?k)" using pos2 by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro exI[where x = c3] conjI)
    show "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (2 * ?k)"
      by (rule ch_full)
    show "ktc_state c3 = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
      by (rule st3)
    show "ktc_tape c3 = (ktc_tape c')(tk := (\<lambda>pos.
            if base \<le> pos \<and> pos < base + ?k
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
            else ktc_tape c' tk pos))"
      by (rule tape_final)
    show "ktc_pos c3 = (ktc_pos c')(tk := base + ?k)" by (rule pos_final)
  qed
qed

text \<open>The proper-cell single-tape write, last tape: as
  \<open>ar_write_proper_step\<close> but \<open>tk\<close> is the last tape, so after
  the last-cell write (\<open>ar_write_bit_finish_step\<close>) the phase
  transitions to \<open>AR_SimAdvance\<close> with the current-tape field reset
  to \<open>k_unidx 0\<close> (all tapes written).  Same \<open>b\<close>-cell block
  write and head return to \<open>base + b\<close>.  Chain length \<open>2b\<close>.\<close>

lemma ar_write_proper_finish_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and last: "is_last_k M tk"
      and poskproper: "posk tk \<noteq> AR_AtLE"
      and stg: "ktc_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c' tk = base + block_width (\<Gamma>_ktm M)"
      and notLE: "\<And>m. m \<le> block_width (\<Gamma>_ktm M)
                   \<Longrightarrow> ktc_tape c' tk (base + m) \<noteq> LE4"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (2 * block_width (\<Gamma>_ktm M))
              \<and> ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> ktc_tape c'' = (ktc_tape c')(tk := (\<lambda>pos.
                    if base \<le> pos \<and> pos < base + block_width (\<Gamma>_ktm M)
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
                    else ktc_tape c' tk pos))
              \<and> ktc_pos c'' = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)"
  let ?wb = "\<lambda>m. write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) m"
  let ?part = "\<lambda>pos. if base \<le> pos \<and> pos < base + (?k - 1)
                       then ?wb (pos - base) else ktc_tape c' tk pos"
  let ?full = "\<lambda>pos. if base \<le> pos \<and> pos < base + ?k
                       then ?wb (pos - base) else ktc_tape c' tk pos"
  have kpos: "0 < ?k" using kge2 by simp
  obtain kk where kdef: "?k = Suc kk" using kge2 by (cases ?k) auto
  obtain c2 where
      ch_pre: "(c', c2) \<in> ?R ^^ (?k + (?k - 1))"
    and st2: "ktc_state c2 = (q, AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
    and tape2: "ktc_tape c2 = (ktc_tape c')(tk := ?part)"
    and pos2: "ktc_pos c2 = (ktc_pos c')(tk := base + (?k - 1))"
    using ar_write_proper_prefix[OF vM qQ kge2 poskproper stg buf_valid pos_base notLE
                         pad0 src0]
    by blast
  have c2tk: "ktc_tape c2 tk = ?part" using tape2 by simp
  have pos2_tk: "ktc_pos c2 tk = base + (?k - 1)" using pos2 by simp
  have ihi: "Suc (?k + (?k - 1)) = 2 * ?k" using kdef by simp
  have lt2: "?k + (?k - 1) < 2 * ?k" using kdef by simp
  have vsrc2: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                 (AR_SimWrite, tk, ?k + (?k - 1), buf, dvec, posk)"
    using lt2 buf_valid by (simp add: ar_valid_stage_def)
  have cell_cur: "ktc_tape c2 tk (ktc_pos c2 tk) = ktc_tape c' tk (base + (?k - 1))"
  proof -
    have "ktc_tape c2 tk (base + (?k - 1)) = ktc_tape c' tk (base + (?k - 1))"
      using c2tk by simp
    thus ?thesis using pos2_tk by simp
  qed
  have km1le: "?k - 1 \<le> ?k" by simp
  have notLE2: "ktc_tape c2 tk (ktc_pos c2 tk) \<noteq> LE4"
    using cell_cur notLE[OF km1le] by simp
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c2: "\<forall>j \<ge> k_ktm M. ktc_tape c2 j (ktc_pos c2 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c2 j (ktc_pos c2 j) = ktc_tape c' j (ktc_pos c' j)"
      using tape2 pos2 jne by simp
    thus "ktc_tape c2 j (ktc_pos c2 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c2: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimWrite, tk, block_width (\<Gamma>_ktm M) + (block_width (\<Gamma>_ktm M) - 1),
                   buf, dvec, posk)"
    using src0 by (simp add: ar_stage_bounded_def)
  obtain c3 where
      s3: "(c2, c3) \<in> ?R"
    and st3: "ktc_state c3 = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
    and tape3: "ktc_tape c3 = (ktc_tape c2)(tk :=
          (ktc_tape c2 tk)(ktc_pos c2 tk := ?wb (?k + (?k - 1) - ?k)))"
    and pos3: "ktc_pos c3 = (ktc_pos c2)(tk := Suc (ktc_pos c2 tk))"
    using ar_write_bit_finish_step[OF vM st2 qQ poskproper notLE2 last ihi vsrc2
                         pad_c2 src_c2]
    by blast
  have ch_full: "(c', c3) \<in> ?R ^^ (2 * ?k)"
  proof -
    have h: "(c', c3) \<in> ?R ^^ Suc (?k + (?k - 1))"
      by (rule relpow_Suc_I[OF ch_pre s3])
    from h show ?thesis by (simp only: ihi)
  qed
  have tape3_tk: "ktc_tape c3 tk = (?part(base + (?k - 1) := ?wb (?k - 1)))"
    using tape3 pos2_tk c2tk by simp
  have tape3_tk_full: "ktc_tape c3 tk = ?full"
    using tape3_tk write_block_extend[OF kpos, of base ?wb "ktc_tape c' tk"] by simp
  have tape_final: "ktc_tape c3 = (ktc_tape c')(tk := ?full)"
  proof (rule ext)
    fix k'
    show "ktc_tape c3 k' = ((ktc_tape c')(tk := ?full)) k'"
    proof (cases "k' = tk")
      case True thus ?thesis using tape3_tk_full by simp
    next
      case False
      have "ktc_tape c3 k' = ktc_tape c2 k'" using tape3 False by simp
      also have "\<dots> = ktc_tape c' k'" using tape2 False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have pos_final: "ktc_pos c3 = (ktc_pos c')(tk := base + ?k)"
  proof -
    have "ktc_pos c3 = (ktc_pos c2)(tk := Suc (ktc_pos c2 tk))" by (rule pos3)
    also have "\<dots> = (ktc_pos c2)(tk := base + ?k)" using pos2_tk kdef by simp
    also have "\<dots> = (ktc_pos c')(tk := base + ?k)" using pos2 by simp
    finally show ?thesis .
  qed
  show ?thesis
  proof (intro exI[where x = c3] conjI)
    show "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (2 * ?k)"
      by (rule ch_full)
    show "ktc_state c3 = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
      by (rule st3)
    show "ktc_tape c3 = (ktc_tape c')(tk := (\<lambda>pos.
            if base \<le> pos \<and> pos < base + ?k
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - base)
            else ktc_tape c' tk pos))"
      by (rule tape_final)
    show "ktc_pos c3 = (ktc_pos c')(tk := base + ?k)" by (rule pos_final)
  qed
qed

text \<open>The unified single-tape write, non-last tape: the LE/proper
  dispatch, the AR analogue of \<open>ar_read_tape_step\<close>.  From an
  \<open>AR_SimWrite\<close> stage at bit-counter \<open>0\<close>, dispatch on
  \<open>posk tk = AR_AtLE\<close> (which the caller pins to \<open>p = 0\<close>,
  \<open>M\<close>'s head on the marker): the LE arm
  (\<open>ar_write_le_step\<close>, \<open>1\<close> step) leaves the tape and head
  untouched and hands off; the proper arm (\<open>ar_write_proper_step\<close>,
  \<open>2b\<close> steps) overwrites the \<open>b\<close>-cell block at \<open>sim_pos
  p\<close> with \<open>write_bit (buf tk)\<close>.  In \<^emph>\<open>both\<close>
  arms every head is unchanged (the LE arm is all-\<open>N\<close>; the proper
  arm back-walks then returns to the block end), so the conclusion is
  \<open>ktc_pos c'' = ktc_pos c'\<close> uniformly.  The proper-arm
  \<open>\<noteq> LE4\<close> facts come from the input correspondence
  \<open>tcorr\<close> (block-\<open>p\<close> cells and the block-\<open>(p+1)\<close>
  lead cell, all \<open>cell_repr\<close> cells via
  \<open>cell_repr_nth_not_LE4\<close>).\<close>

lemma ar_write_tape_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "ktc_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                    tM (ktc_tape c' tk)"
      and ppos: "ktc_pos c' tk = (if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
      and poskle: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if p = 0 then 1 else 2 * block_width (\<Gamma>_ktm M))
              \<and> ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)
              \<and> ktc_tape c'' = (if p = 0 then ktc_tape c'
                    else (ktc_tape c')(tk := (\<lambda>pos.
                      if sim_pos (block_width (\<Gamma>_ktm M)) p \<le> pos
                         \<and> pos < sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M)
                      then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk)
                             (pos - sim_pos (block_width (\<Gamma>_ktm M)) p)
                      else ktc_tape c' tk pos)))
              \<and> ktc_pos c'' = ktc_pos c'"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "p = 0")
    case True
    have poskLE: "posk tk = AR_AtLE" using poskle True by simp
    obtain c'' where
        step: "(c', c'') \<in> ?R"
      and st: "ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = ktc_pos c'"
      using ar_write_le_step[OF vM stg qQ poskLE notlast vsrc pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> ?R ^^ (if p = 0 then 1 else 2 * ?k)"
        using step True by simp
      show "ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
        by (rule st)
      show "ktc_tape c'' = (if p = 0 then ktc_tape c'
              else (ktc_tape c')(tk := (\<lambda>pos.
                if sim_pos ?k p \<le> pos \<and> pos < sim_pos ?k p + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - sim_pos ?k p)
                else ktc_tape c' tk pos)))"
        using tp True by simp
      show "ktc_pos c'' = ktc_pos c'" by (rule ps)
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have poskproper: "posk tk \<noteq> AR_AtLE" using poskle False by simp
    let ?base = "sim_pos ?k p"
    have pos_base: "ktc_pos c' tk = ?base + ?k" using ppos False by simp
    have notLE: "\<And>m. m \<le> ?k \<Longrightarrow> ktc_tape c' tk (?base + m) \<noteq> LE4"
    proof -
      fix m assume mle: "m \<le> ?k"
      show "ktc_tape c' tk (?base + m) \<noteq> LE4"
      proof (cases "m < ?k")
        case True
        have "ktc_tape c' tk (?base + m)
                = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! m"
          using tcorr pge1 True unfolding ar_tape_correspondence_def by blast
        thus ?thesis using cell_repr_nth_not_LE4[OF True] by simp
      next
        case False
        hence meq: "m = ?k" using mle by simp
        obtain pp where pp: "p = Suc pp" using pge1 by (cases p) auto
        have psuc1: "1 \<le> Suc p" by simp
        have base_succ: "?base + ?k = sim_pos ?k (Suc p)"
          using pp by (simp add: sim_pos_def)
        have corr_succ: "\<forall>j < ?k. ktc_tape c' tk (sim_pos ?k (Suc p) + j)
                            = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (Suc p)) ! j"
          using tcorr psuc1 unfolding ar_tape_correspondence_def by blast
        have "ktc_tape c' tk (?base + m)
                = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (Suc p)) ! 0"
          using meq base_succ corr_succ[rule_format, OF kpos] by simp
        thus ?thesis using cell_repr_nth_not_LE4[OF kpos] by simp
      qed
    qed
    obtain c'' where
        step: "(c', c'') \<in> ?R ^^ (2 * ?k)"
      and st: "ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
      and tp: "ktc_tape c'' = (ktc_tape c')(tk := (\<lambda>pos.
            if ?base \<le> pos \<and> pos < ?base + ?k
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - ?base)
            else ktc_tape c' tk pos))"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk := ?base + ?k)"
      using ar_write_proper_step[OF vM qQ kge2 notlast poskproper stg buf_valid
                                    pos_base notLE pad0 src0]
      by blast
    have ps': "ktc_pos c'' = ktc_pos c'"
    proof -
      have "(ktc_pos c')(tk := ?base + ?k) = ktc_pos c'"
        using pos_base by (rule fun_upd_idem)
      thus ?thesis using ps by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> ?R ^^ (if p = 0 then 1 else 2 * ?k)"
        using step False by simp
      show "ktc_state c'' = (q, AR_SimWrite, k_succ tk, 0, buf, dvec, posk)"
        by (rule st)
      show "ktc_tape c'' = (if p = 0 then ktc_tape c'
              else (ktc_tape c')(tk := (\<lambda>pos.
                if sim_pos ?k p \<le> pos \<and> pos < sim_pos ?k p + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - sim_pos ?k p)
                else ktc_tape c' tk pos)))"
        using tp False by simp
      show "ktc_pos c'' = ktc_pos c'" by (rule ps')
    qed
  qed
qed

text \<open>The unified single-tape write, last tape: as
  \<open>ar_write_tape_step\<close> but \<open>tk\<close> is the last tape, so both
  arms transition to \<open>AR_SimAdvance\<close> (current-tape field reset to
  \<open>k_unidx 0\<close>, all tapes written): the LE arm via
  \<open>ar_write_le_finish_step\<close>, the proper arm via
  \<open>ar_write_proper_finish_step\<close>.  Same tape edit and head
  invariance.\<close>

lemma ar_write_tape_finish_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and last: "is_last_k M tk"
      and stg: "ktc_state c' = (q, AR_SimWrite, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                    tM (ktc_tape c' tk)"
      and ppos: "ktc_pos c' tk = (if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
      and poskle: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if p = 0 then 1 else 2 * block_width (\<Gamma>_ktm M))
              \<and> ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
              \<and> ktc_tape c'' = (if p = 0 then ktc_tape c'
                    else (ktc_tape c')(tk := (\<lambda>pos.
                      if sim_pos (block_width (\<Gamma>_ktm M)) p \<le> pos
                         \<and> pos < sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M)
                      then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk)
                             (pos - sim_pos (block_width (\<Gamma>_ktm M)) p)
                      else ktc_tape c' tk pos)))
              \<and> ktc_pos c'' = ktc_pos c'"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?R = "ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)"
  have kpos: "0 < ?k" using kge2 by simp
  show ?thesis
  proof (cases "p = 0")
    case True
    have poskLE: "posk tk = AR_AtLE" using poskle True by simp
    obtain c'' where
        step: "(c', c'') \<in> ?R"
      and st: "ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = ktc_pos c'"
      using ar_write_le_finish_step[OF vM stg qQ poskLE last vsrc pad0 src0] by blast
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> ?R ^^ (if p = 0 then 1 else 2 * ?k)"
        using step True by simp
      show "ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
        by (rule st)
      show "ktc_tape c'' = (if p = 0 then ktc_tape c'
              else (ktc_tape c')(tk := (\<lambda>pos.
                if sim_pos ?k p \<le> pos \<and> pos < sim_pos ?k p + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - sim_pos ?k p)
                else ktc_tape c' tk pos)))"
        using tp True by simp
      show "ktc_pos c'' = ktc_pos c'" by (rule ps)
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have poskproper: "posk tk \<noteq> AR_AtLE" using poskle False by simp
    let ?base = "sim_pos ?k p"
    have pos_base: "ktc_pos c' tk = ?base + ?k" using ppos False by simp
    have notLE: "\<And>m. m \<le> ?k \<Longrightarrow> ktc_tape c' tk (?base + m) \<noteq> LE4"
    proof -
      fix m assume mle: "m \<le> ?k"
      show "ktc_tape c' tk (?base + m) \<noteq> LE4"
      proof (cases "m < ?k")
        case True
        have "ktc_tape c' tk (?base + m)
                = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! m"
          using tcorr pge1 True unfolding ar_tape_correspondence_def by blast
        thus ?thesis using cell_repr_nth_not_LE4[OF True] by simp
      next
        case False
        hence meq: "m = ?k" using mle by simp
        obtain pp where pp: "p = Suc pp" using pge1 by (cases p) auto
        have psuc1: "1 \<le> Suc p" by simp
        have base_succ: "?base + ?k = sim_pos ?k (Suc p)"
          using pp by (simp add: sim_pos_def)
        have corr_succ: "\<forall>j < ?k. ktc_tape c' tk (sim_pos ?k (Suc p) + j)
                            = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (Suc p)) ! j"
          using tcorr psuc1 unfolding ar_tape_correspondence_def by blast
        have "ktc_tape c' tk (?base + m)
                = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (Suc p)) ! 0"
          using meq base_succ corr_succ[rule_format, OF kpos] by simp
        thus ?thesis using cell_repr_nth_not_LE4[OF kpos] by simp
      qed
    qed
    obtain c'' where
        step: "(c', c'') \<in> ?R ^^ (2 * ?k)"
      and st: "ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
      and tp: "ktc_tape c'' = (ktc_tape c')(tk := (\<lambda>pos.
            if ?base \<le> pos \<and> pos < ?base + ?k
            then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - ?base)
            else ktc_tape c' tk pos))"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk := ?base + ?k)"
      using ar_write_proper_finish_step[OF vM qQ kge2 last poskproper stg buf_valid
                                           pos_base notLE pad0 src0]
      by blast
    have ps': "ktc_pos c'' = ktc_pos c'"
    proof -
      have "(ktc_pos c')(tk := ?base + ?k) = ktc_pos c'"
        using pos_base by (rule fun_upd_idem)
      thus ?thesis using ps by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> ?R ^^ (if p = 0 then 1 else 2 * ?k)"
        using step False by simp
      show "ktc_state c'' = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
        by (rule st)
      show "ktc_tape c'' = (if p = 0 then ktc_tape c'
              else (ktc_tape c')(tk := (\<lambda>pos.
                if sim_pos ?k p \<le> pos \<and> pos < sim_pos ?k p + ?k
                then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf tk) (pos - sim_pos ?k p)
                else ktc_tape c' tk pos)))"
        using tp False by simp
      show "ktc_pos c'' = ktc_pos c'" by (rule ps')
    qed
  qed
qed

text \<open>The write-phase prefix walk: from the write boundary
  (current-tape field \<open>k_unidx 0\<close>, bit-counter
  \<open>0\<close>, the head positions the read phase left), iterate the
  unified non-last per-tape write \<open>ar_write_tape_step\<close> over the
  first \<open>j\<close> tapes (\<open>j \<le> k_ktm M - 1\<close>, all non-last),
  landing back at \<open>AR_SimWrite\<close> on tape \<open>k_unidx j\<close>.
  Dual to \<open>ar_read_prefix\<close>: the read kept the tape constant and
  varied \<open>buf\<close>/\<open>posk\<close>; the write keeps
  \<open>buf\<close>/\<open>posk\<close>/positions constant and varies the
  \<^emph>\<open>tape\<close>.  The descriptor splits on \<open>k_idx k <
  j\<close>: visited tapes carry their overwritten block
  (\<open>?out\<close>, the \<open>write_bit\<close> image for proper tapes, or
  the unchanged tape for \<open>LE\<close> tapes); the rest are unchanged.
  Each per-tape step's \<open>tcorr\<close> / position entry facts hold
  because the current tape is not yet visited
  (\<open>ktc_tape c k_unidx j = ktc_tape c0 (k_unidx j)\<close>).  Variable
  per-tape cost (\<open>1\<close> or \<open>2b\<close>), aggregate bounded by
  \<open>j \<cdot> 2b\<close>.\<close>

lemma ar_write_prefix:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimWrite, 0, 0, buf, dvec, posk)"
      and tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c0 k)"
      and ppos: "\<forall>k < k_ktm M. ktc_pos c0 k = (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                              + block_width (\<Gamma>_ktm M))"
      and poskle: "\<forall>k < k_ktm M. posk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, 0, 0, buf, dvec, posk)"
  shows "j \<le> k_ktm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m
         \<and> m \<le> j * (2 * block_width (\<Gamma>_ktm M))
         \<and> ktc_state c = (q, AR_SimWrite, k_unidx j, 0, buf, dvec, posk)
         \<and> ktc_tape c = (\<lambda>k. if k_idx k < j
              then (if ktc_pos cM k = 0 then ktc_tape c0 k
                    else (\<lambda>pos. if sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k) \<le> pos
                                  \<and> pos < sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                                            + block_width (\<Gamma>_ktm M)
                               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                      (pos - sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k))
                               else ktc_tape c0 k pos))
              else ktc_tape c0 k)
         \<and> ktc_pos c = ktc_pos c0)"
proof (induction j)
  case 0
  let ?k = "block_width (\<Gamma>_ktm M)"
  have "(c0, c0) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ 0" by simp
  moreover have "ktc_tape c0 = (\<lambda>k. if k_idx k < 0
              then (if ktc_pos cM k = 0 then ktc_tape c0 k
                    else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                                  \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                      (pos - sim_pos ?k (ktc_pos cM k))
                               else ktc_tape c0 k pos))
              else ktc_tape c0 k)"
    by simp
  ultimately show ?case
    using stg0 by (intro exI[where x = c0] exI[where x = 0]) (simp add: k_unidx_zero)
next
  case (Suc j)
  have sucle: "Suc j \<le> k_ktm M - 1" by (rule Suc.prems)
  have jcard: "j < k_ktm M" using sucle by simp
  have sjcard: "Suc j < k_ktm M" using sucle by simp
  have jle: "j \<le> k_ktm M - 1" using sucle by simp
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?tk = "k_unidx j"
  let ?p = "ktc_pos cM ?tk"
  let ?out = "\<lambda>k. if ktc_pos cM k = 0 then ktc_tape c0 k
                   else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                                 \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                              then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                     (pos - sim_pos ?k (ktc_pos cM k))
                              else ktc_tape c0 k pos)"
  let ?tape = "\<lambda>i. (\<lambda>k. if k_idx k < i then ?out k else ktc_tape c0 k)"
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
      cm_rel: "(c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m"
    and m_le: "m \<le> j * (2 * ?k)"
    and c_st: "ktc_state c = (q, AR_SimWrite, ?tk, 0, buf, dvec, posk)"
    and c_tp: "ktc_tape c = ?tape j"
    and c_ps: "ktc_pos c = ktc_pos c0"
    using Suc.IH[OF jle] by blast
  \<comment> \<open>tape \<open>?tk\<close> is not yet visited, so still matches \<open>c0\<close>\<close>
  have tc_tk: "ktc_tape c ?tk = ktc_tape c0 ?tk" using c_tp tkidx by simp
  have tk_active: "?tk < k_ktm M" using jcard by (simp add: k_unidx_def)
  have tk_corr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM ?tk) (ktc_tape c ?tk)"
    using tcorr[rule_format, OF tk_active] tc_tk by simp
  have tk_ppos: "ktc_pos c ?tk
                   = (if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using c_ps ppos[rule_format, OF tk_active] by simp
  have tk_poskle: "posk ?tk = AR_AtLE \<longleftrightarrow> ?p = 0"
    by (rule poskle[rule_format, OF tk_active])
  have tk_vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimWrite, ?tk, 0, buf, dvec, posk)"
    using kge2 buf_valid by (auto simp: ar_valid_stage_def)
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
                 (AR_SimWrite, ?tk, 0, buf, dvec, posk)"
    using src0 tk_active by (auto simp: ar_stage_bounded_def)
  obtain c' where
      step: "(c, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if ?p = 0 then 1 else 2 * ?k)"
    and c'_st: "ktc_state c' = (q, AR_SimWrite, k_succ ?tk, 0, buf, dvec, posk)"
    and c'_tp: "ktc_tape c' = (if ?p = 0 then ktc_tape c
                  else (ktc_tape c)(?tk := (\<lambda>pos.
                    if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tk)
                           (pos - sim_pos ?k ?p)
                    else ktc_tape c ?tk pos)))"
    and c'_ps: "ktc_pos c' = ktc_pos c"
    using ar_write_tape_step[OF vM qQ kge2 notlast c_st tk_corr tk_ppos tk_poskle
                                buf_valid tk_vsrc pad_c src_c]
    by blast
  \<comment> \<open>the post-state tape descriptor coincides with the \<open>Suc j\<close> one\<close>
  have tape_eq: "ktc_tape c' = ?tape (Suc j)"
  proof (rule ext)
    fix k
    show "ktc_tape c' k = ?tape (Suc j) k"
    proof (cases "k = ?tk")
      case True
      show ?thesis
      proof (cases "?p = 0")
        case True
        have "ktc_tape c' k = ktc_tape c0 ?tk"
          using c'_tp \<open>k = ?tk\<close> \<open>?p = 0\<close> tc_tk by simp
        moreover have "?tape (Suc j) k = ktc_tape c0 ?tk"
          using \<open>k = ?tk\<close> tkidx \<open>?p = 0\<close> by simp
        ultimately show ?thesis by simp
      next
        case False
        show ?thesis
        proof (rule ext)
          fix pos
          have lhs: "ktc_tape c' k pos
                  = (if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                     then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tk) (pos - sim_pos ?k ?p)
                     else ktc_tape c ?tk pos)"
            using c'_tp \<open>k = ?tk\<close> \<open>?p \<noteq> 0\<close> by simp
          have rhs: "?tape (Suc j) k pos
                  = (if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                     then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tk) (pos - sim_pos ?k ?p)
                     else ktc_tape c0 ?tk pos)"
            using \<open>k = ?tk\<close> tkidx \<open>?p \<noteq> 0\<close> by simp
          show "ktc_tape c' k pos = ?tape (Suc j) k pos"
            using lhs rhs tc_tk by simp
        qed
      qed
    next
      case False
      hence kidx_ne: "k_idx k \<noteq> j" using kne by blast
      have "ktc_tape c' k = ktc_tape c k"
        using c'_tp False by (cases "?p = 0") simp_all
      also have "\<dots> = ?tape j k" using c_tp by simp
      also have "\<dots> = ?tape (Suc j) k" using kidx_ne by (simp add: less_Suc_eq)
      finally show ?thesis .
    qed
  qed
  have chain: "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (m + (if ?p = 0 then 1 else 2 * ?k))"
  proof -
    have "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m
                       O (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if ?p = 0 then 1 else 2 * ?k)"
      using cm_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m + (if ?p = 0 then 1 else 2 * ?k) \<le> Suc j * (2 * ?k)"
    using m_le kge2 by (cases "?p = 0") auto
  show ?case
  proof (intro exI[where x = c']
           exI[where x = "m + (if ?p = 0 then 1 else 2 * ?k)"] conjI)
    show "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (m + (if ?p = 0 then 1 else 2 * ?k))" by (rule chain)
    show "m + (if ?p = 0 then 1 else 2 * ?k) \<le> Suc j * (2 * ?k)"
      by (rule bound)
    show "ktc_state c' = (q, AR_SimWrite, k_unidx (Suc j), 0, buf, dvec, posk)"
      using c'_st ksucc by simp
    show "ktc_tape c' = (\<lambda>k. if k_idx k < Suc j
              then (if ktc_pos cM k = 0 then ktc_tape c0 k
                    else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                                  \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                      (pos - sim_pos ?k (ktc_pos cM k))
                               else ktc_tape c0 k pos))
              else ktc_tape c0 k)"
      using tape_eq by simp
    show "ktc_pos c' = ktc_pos c0" using c'_ps c_ps by simp
  qed
qed

text \<open>The full write phase: the prefix walk over the first
  \<open>k_ktm M - 1\<close> tapes followed by the unified last-tape write
  \<open>ar_write_tape_finish_step\<close>, landing at \<open>AR_SimAdvance\<close>
  (current-tape field \<open>k_unidx 0\<close>) with every proper tape's
  \<open>b\<close>-cell block overwritten by \<open>write_bit (buf k)\<close> (the
  encoded \<open>M\<close>-write symbol) and every \<open>LE\<close> tape and head
  position unchanged.  Aggregate cost \<open>\<le> k_ktm M \<cdot> 2b\<close>.
  The split tape descriptor collapses to the full per-tape overwrite on
  the last tape (every other tape has index \<open>< k_ktm M - 1\<close>).\<close>

lemma ar_write_phase:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimWrite, 0, 0, buf, dvec, posk)"
      and tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c0 k)"
      and ppos: "\<forall>k < k_ktm M. ktc_pos c0 k = (if ktc_pos cM k = 0 then Suc 0
                       else sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                              + block_width (\<Gamma>_ktm M))"
      and poskle: "\<forall>k < k_ktm M. posk k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
      and buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimWrite, 0, 0, buf, dvec, posk)"
  shows "\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m
         \<and> m \<le> k_ktm M * (2 * block_width (\<Gamma>_ktm M))
         \<and> ktc_state c = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)
         \<and> ktc_tape c = (\<lambda>k. if k < k_ktm M
              then (if ktc_pos cM k = 0 then ktc_tape c0 k
                    else (\<lambda>pos. if sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k) \<le> pos
                                  \<and> pos < sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                                            + block_width (\<Gamma>_ktm M)
                               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                      (pos - sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k))
                               else ktc_tape c0 k pos))
              else ktc_tape c0 k)
         \<and> ktc_pos c = ktc_pos c0"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?N = "k_ktm M"
  let ?m1 = "?N - 1"
  let ?tl = "k_unidx ?m1"
  let ?p = "ktc_pos cM ?tl"
  let ?out = "\<lambda>k. if ktc_pos cM k = 0 then ktc_tape c0 k
                   else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                                 \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                              then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                     (pos - sim_pos ?k (ktc_pos cM k))
                              else ktc_tape c0 k pos)"
  let ?tape = "\<lambda>i. (\<lambda>k. if k_idx k < i then ?out k else ktc_tape c0 k)"
  have card1: "0 < ?N" using vM by (cases M) auto
  have m1suc: "?N = Suc ?m1" using card1 by simp
  have m1card: "?m1 < ?N" using card1 by simp
  have m1lt: "?m1 < k_ktm M" using card1 by simp
  have tl_eq: "?tl = ?m1" by (simp add: k_unidx_def)
  have tlidx: "k_idx ?tl = ?m1" by (rule k_idx_unidx[OF m1card])
  have tl_active: "?tl < k_ktm M" using m1lt tl_eq by simp
  have islast: "is_last_k M ?tl" using is_last_k_unidx[OF m1card] m1suc by simp
  have cond: "(k < ?m1) = (k < k_ktm M)" if "k \<noteq> ?m1" for k
    using that m1suc by (auto simp: less_Suc_eq)
  obtain c1 m1 where
      c1_rel: "(c0, c1) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m1"
    and m1_le: "m1 \<le> ?m1 * (2 * ?k)"
    and c1_st: "ktc_state c1 = (q, AR_SimWrite, ?tl, 0, buf, dvec, posk)"
    and c1_tp: "ktc_tape c1 = ?tape ?m1"
    and c1_ps: "ktc_pos c1 = ktc_pos c0"
    using ar_write_prefix[OF vM qQ kge2 stg0 tcorr ppos poskle buf_valid pad0 src0,
                          of ?m1]
    by auto
  have tc_tl: "ktc_tape c1 ?tl = ktc_tape c0 ?tl" using c1_tp tlidx by simp
  have tl_corr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM ?tl) (ktc_tape c1 ?tl)"
    using tcorr[rule_format, OF tl_active] tc_tl by simp
  have tl_ppos: "ktc_pos c1 ?tl
                   = (if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using c1_ps ppos[rule_format, OF tl_active] by simp
  have tl_poskle: "posk ?tl = AR_AtLE \<longleftrightarrow> ?p = 0"
    by (rule poskle[rule_format, OF tl_active])
  have tl_vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimWrite, ?tl, 0, buf, dvec, posk)"
    using kge2 buf_valid by (auto simp: ar_valid_stage_def)
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
                  (AR_SimWrite, ?tl, 0, buf, dvec, posk)"
    using src0 tl_active by (auto simp: ar_stage_bounded_def)
  obtain c2 where
      step: "(c1, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if ?p = 0 then 1 else 2 * ?k)"
    and c2_st: "ktc_state c2 = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
    and c2_tp: "ktc_tape c2 = (if ?p = 0 then ktc_tape c1
                  else (ktc_tape c1)(?tl := (\<lambda>pos.
                    if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                    then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tl)
                           (pos - sim_pos ?k ?p)
                    else ktc_tape c1 ?tl pos)))"
    and c2_ps: "ktc_pos c2 = ktc_pos c1"
    using ar_write_tape_finish_step[OF vM qQ kge2 islast c1_st tl_corr tl_ppos
                                       tl_poskle buf_valid tl_vsrc pad_c1 src_c1]
    by blast
  \<comment> \<open>The last-tape \<open>fun_upd\<close> collapses to the active-guarded
     per-tape overwrite: active tapes get \<open>?out\<close>, padding tapes
     stay at \<open>c0\<close>'s tape (the walk never visits them).\<close>
  have tape_full: "ktc_tape c2 = (\<lambda>k. if k < k_ktm M then ?out k else ktc_tape c0 k)"
  proof (rule ext)
    fix k
    show "ktc_tape c2 k = (if k < k_ktm M then ?out k else ktc_tape c0 k)"
    proof (cases "k = ?tl")
      case True
      have out_tl: "ktc_tape c2 k = ?out k"
      proof (cases "?p = 0")
        case True
        have "ktc_tape c2 k = ktc_tape c0 ?tl"
          using c2_tp \<open>k = ?tl\<close> \<open>?p = 0\<close> tc_tl by simp
        moreover have "?out k = ktc_tape c0 ?tl"
          using \<open>k = ?tl\<close> \<open>?p = 0\<close> by simp
        ultimately show ?thesis by simp
      next
        case False
        show ?thesis
        proof (rule ext)
          fix pos
          have lhs: "ktc_tape c2 k pos
                  = (if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                     then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tl) (pos - sim_pos ?k ?p)
                     else ktc_tape c1 ?tl pos)"
            using c2_tp \<open>k = ?tl\<close> \<open>?p \<noteq> 0\<close> by simp
          have rhs: "?out k pos
                  = (if sim_pos ?k ?p \<le> pos \<and> pos < sim_pos ?k ?p + ?k
                     then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf ?tl) (pos - sim_pos ?k ?p)
                     else ktc_tape c0 ?tl pos)"
            using \<open>k = ?tl\<close> \<open>?p \<noteq> 0\<close> by simp
          show "ktc_tape c2 k pos = ?out k pos"
            using lhs rhs tc_tl by simp
        qed
      qed
      show ?thesis using out_tl \<open>k = ?tl\<close> tl_eq m1lt by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis
      proof (cases "k < ?m1")
        case True
        have klt: "k < k_ktm M" using True m1lt by simp
        have "ktc_tape c2 k = ktc_tape c1 k"
          using c2_tp \<open>k \<noteq> ?tl\<close> by (cases "?p = 0") simp_all
        also have "\<dots> = ?out k" using c1_tp True by (simp add: k_idx_def)
        finally show ?thesis using klt by simp
      next
        case False
        have kge: "\<not> k < k_ktm M" using False kne cond[OF kne] by simp
        have "ktc_tape c2 k = ktc_tape c1 k"
          using c2_tp \<open>k \<noteq> ?tl\<close> by (cases "?p = 0") simp_all
        also have "\<dots> = ktc_tape c0 k" using c1_tp False by (simp add: k_idx_def)
        finally show ?thesis using kge by simp
      qed
    qed
  qed
  have chain: "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (m1 + (if ?p = 0 then 1 else 2 * ?k))"
  proof -
    have "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ m1
                       O (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (if ?p = 0 then 1 else 2 * ?k)"
      using c1_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m1 + (if ?p = 0 then 1 else 2 * ?k) \<le> ?N * (2 * ?k)"
  proof -
    obtain Nm where Nm: "?N = Suc Nm" using card1 by (cases ?N) auto
    have e1: "?N * (2 * ?k) = (2 * ?k) + Nm * (2 * ?k)" by (simp add: Nm)
    have e2: "m1 \<le> Nm * (2 * ?k)" using m1_le Nm by simp
    have e3: "(if ?p = 0 then 1 else 2 * ?k) \<le> 2 * ?k" using kge2 by simp
    show ?thesis using e1 e2 e3 by linarith
  qed
  show ?thesis
  proof (intro exI[where x = c2]
           exI[where x = "m1 + (if ?p = 0 then 1 else 2 * ?k)"] conjI)
    show "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_write M)) ^^ (m1 + (if ?p = 0 then 1 else 2 * ?k))" by (rule chain)
    show "m1 + (if ?p = 0 then 1 else 2 * ?k) \<le> ?N * (2 * ?k)" by (rule bound)
    show "ktc_state c2 = (q, AR_SimAdvance, k_unidx 0, 0, buf, dvec, posk)"
      by (rule c2_st)
    show "ktc_tape c2 = (\<lambda>k. if k < k_ktm M
              then (if ktc_pos cM k = 0 then ktc_tape c0 k
                    else (\<lambda>pos. if sim_pos ?k (ktc_pos cM k) \<le> pos
                                  \<and> pos < sim_pos ?k (ktc_pos cM k) + ?k
                               then write_bit (\<Gamma>_ktm M) (bl_ktm M) (buf k)
                                      (pos - sim_pos ?k (ktc_pos cM k))
                               else ktc_tape c0 k pos))
              else ktc_tape c0 k)"
      using tape_full by simp
    show "ktc_pos c2 = ktc_pos c0" using c2_ps c1_ps by simp
  qed
qed

end
