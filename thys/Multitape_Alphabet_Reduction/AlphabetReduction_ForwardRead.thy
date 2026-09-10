theory AlphabetReduction_ForwardRead
  imports AlphabetReduction_ForwardSubsteps
begin

subsection \<open>Read phase\<close>

text \<open>The accumulator fold stays inside \<open>\<Gamma> \<union> {bl}\<close>:
  on a non-empty bit list the outermost \<open>ar_acc\<close> is a
  \<open>gamma_unenum\<close> image (always in range by \<open>gamma_unenum_mem\<close>);
  on the empty list it is the seed.  This is the read-loop's
  \<open>ar_valid_stage\<close> obligation discharged once for the running
  \<open>buf\<close> value, independent of how many bits have been folded so
  far.
  Throughout, \<open>b\<close> abbreviates \<open>block_width \<Gamma>\<close> (the per-symbol cell width).\<close>

lemma foldl_ar_acc_mem:
  assumes "finite \<Gamma>" and "a \<in> \<Gamma> \<union> {bl}"
  shows "foldl (ar_acc \<Gamma> bl) a xs \<in> \<Gamma> \<union> {bl}"
proof (induct xs rule: rev_induct)
  case Nil
  show ?case using assms(2) by simp
next
  case (snoc x ys)
  have "foldl (ar_acc \<Gamma> bl) a (ys @ [x])
          = ar_acc \<Gamma> bl (foldl (ar_acc \<Gamma> bl) a ys) x" by simp
  also have "\<dots> \<in> \<Gamma> \<union> {bl}"
    unfolding ar_acc_def by (rule gamma_unenum_mem[OF assms(1)])
  finally show ?case .
qed

text \<open>The inner read loop, single tape, proper cell: starting at
  bit-counter \<open>2\<close> with the partial decode \<open>buf0\<close> and the
  head at \<open>base\<close> (the first bit cell, \<open>sim_pos p\<close>), the
  \<open>ar_read_bit_step\<close> arm fires \<open>b - 1\<close> times, walking
  \<open>R\<close> across the first \<open>b - 1\<close> bit cells and folding each
  into \<open>buf tk\<close> via \<open>ar_acc\<close>.  After the loop the counter
  is \<open>Suc b\<close> (ready for the boundary substep that reads the
  \<open>b\<close>-th, last bit), the head is at \<open>base + (b - 1)\<close>, the
  tape is untouched, and every other tape's head is where it was.
  Instantiates \<open>relpow_invariant_chain\<close>
  with the loop-index-parameterised invariant whose \<open>buf tk\<close>
  field is the \<open>foldl (ar_acc) buf0_tk\<close> of the cells read so
  far — the same \<open>foldl\<close> the read-decode arithmetic
  (\<open>foldl_ar_acc_encode_symbol\<close>) is stated against, so the
  per-step buf update is one \<open>foldl_append\<close> rewrite.\<close>

text \<open>Relation-generic read bit-accumulation loop scaffold.  The
  bit-reading leaf (\<open>ar_read_bit_step\<close>) is the \<open>leaf\<close>
  hypothesis, quantified over config, counter, and buffer (the
  accumulator mutates each step); union and sub versions are thin
  instantiations.\<close>

lemma ar_read_bit_loop_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf:
        "\<And>cc i buf'. \<lbrakk> valid_mttm M;
                       mt_state cc = (q, AR_SimRead, tk, i, buf', dvec, posk);
                       q \<in> Q_tm M;
                       posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                       2 \<le> i;
                       Suc i \<le> Suc (block_width (\<Gamma>_tm M));
                       2 \<le> block_width (\<Gamma>_tm M);
                       ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                         (AR_SimRead, tk, i, buf', dvec, posk);
                       \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                       ar_stage_bounded (bl_tm M) (k_tm M)
                         (AR_SimRead, tk, i, buf', dvec, posk) \<rbrakk>
                     \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc i,
                                    buf'(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                                          (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf' tk)
                                             + bit_value (mt_tape cc tk (mt_pos cc tk)))),
                                    dvec, posk)
                              \<and> mt_tape c'' = mt_tape cc
                              \<and> mt_pos c'' = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 2, buf0, dvec, posk)"
      and buf0_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 2, buf0, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf0(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0 tk)
                            (map (\<lambda>m. mt_tape c' tk (base + m))
                                 [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec, posk)
              \<and> mt_pos c'' tk = base + (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_tape c'' = mt_tape c'
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c'' k' = mt_pos c' k')"
proof -
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  let ?fold = "\<lambda>j. foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0 tk)
                     (map (\<lambda>m. mt_tape c' tk (base + m)) [0..<j])"
  let ?P = "\<lambda>j c.
       mt_state c = (q, AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)
     \<and> mt_pos c tk = base + j
     \<and> mt_tape c = mt_tape c'
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c k' = mt_pos c' k')"
  have mybase: "?P 0 c'" using stg pos_base by simp
  have mystep:
      "\<And>j cc. \<lbrakk> j < block_width (\<Gamma>_tm M) - 1; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < block_width (\<Gamma>_tm M) - 1" and Pj: "?P j cc"
    from Pj have st_cc:
        "mt_state cc = (q, AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      and pos_cc: "mt_pos cc tk = base + j"
      and tape_cc: "mt_tape cc = mt_tape c'"
      and other_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos cc k' = mt_pos c' k'"
      by simp_all
    have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cc: "\<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4"
    proof (intro allI impI)
      fix j' assume jge: "k_tm M \<le> j'"
      have jne: "j' \<noteq> tk" using jge tk_lt by simp
      have "mt_tape cc j' (mt_pos cc j') = mt_tape c' j' (mt_pos c' j')"
        using tape_cc other_cc jne by simp
      thus "mt_tape cc j' (mt_pos cc j') = BLANK4" using pad0 jge by simp
    qed
    have src_cc: "ar_stage_bounded (bl_tm M) (k_tm M)
                    (AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      using src0 tk_lt by (auto simp: ar_stage_bounded_def)
    have jhi: "j + 2 \<le> block_width (\<Gamma>_tm M)" using jlt kge2 by linarith
    have foldj_mem: "?fold j \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      using buf0_valid by (intro foldl_ar_acc_mem[OF finG]) simp
    have bufj_valid: "\<forall>k. (buf0(tk := ?fold j)) k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      using buf0_valid foldj_mem by simp
    have vsrc_cc:
        "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
           (AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      using jhi kge2 bufj_valid by (auto simp: ar_valid_stage_def)
    obtain ccc where
        bstep: "(cc, ccc) \<in> R'"
      and bst_state: "mt_state ccc = (q, AR_SimRead, tk, Suc (j + 2),
            (buf0(tk := ?fold j))
              (tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                       (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) ((buf0(tk := ?fold j)) tk)
                          + bit_value (mt_tape cc tk (mt_pos cc tk)))),
            dvec, posk)"
      and bst_tape: "mt_tape ccc = mt_tape cc"
      and bst_pos: "mt_pos ccc = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      using leaf[OF vM st_cc qQ posk_proper _ _ kge2 vsrc_cc pad_cc src_cc]
            jhi by force
    have read_cell: "mt_tape cc tk (mt_pos cc tk) = mt_tape c' tk (base + j)"
      using tape_cc pos_cc by simp
    have fold_step:
        "gamma_unenum (\<Gamma>_tm M) (bl_tm M)
           (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (?fold j)
              + bit_value (mt_tape c' tk (base + j)))
         = ?fold (Suc j)"
    proof -
      have "?fold (Suc j)
              = foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0 tk)
                  (map (\<lambda>m. mt_tape c' tk (base + m)) [0..<j]
                     @ [mt_tape c' tk (base + j)])"
        by (simp add: upt_Suc_append)
      also have "\<dots> = ar_acc (\<Gamma>_tm M) (bl_tm M) (?fold j)
                        (mt_tape c' tk (base + j))"
        by simp
      finally show ?thesis by (simp add: ar_acc_def)
    qed
    have state_eq:
        "mt_state ccc = (q, AR_SimRead, tk, Suc j + 2,
                          buf0(tk := ?fold (Suc j)), dvec, posk)"
      using bst_state by (simp add: read_cell fold_step)
    have pos_eq: "mt_pos ccc tk = base + Suc j"
      using bst_pos pos_cc by simp
    have other_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos ccc k' = mt_pos c' k'"
      using bst_pos other_cc by simp
    have tape_eq: "mt_tape ccc = mt_tape c'" using bst_tape tape_cc by simp
    show "\<exists>c''. (cc, c'') \<in> R' \<and> ?P (Suc j) c''"
      using bstep state_eq pos_eq tape_eq other_eq by blast
  qed
  have loop:
      "\<exists>c''. (c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) - 1)
            \<and> ?P (block_width (\<Gamma>_tm M) - 1) c''"
    by (rule relpow_invariant_chain
          [where P = ?P and n = "block_width (\<Gamma>_tm M) - 1", OF mystep mybase])
  obtain c'' where
      chain: "(c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) - 1)"
    and Pfin: "?P (block_width (\<Gamma>_tm M) - 1) c''"
    using loop by blast
  have ctr: "(block_width (\<Gamma>_tm M) - 1) + 2 = Suc (block_width (\<Gamma>_tm M))"
    using kge2 by simp
  show ?thesis using chain Pfin ctr by (intro exI[where x = c'']) simp
qed

lemma ar_read_bit_loop:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 2, buf0, dvec, posk)"
      and buf0_valid: "\<forall>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pos_base: "mt_pos c' tk = base"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 2, buf0, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf0(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0 tk)
                            (map (\<lambda>m. mt_tape c' tk (base + m))
                                 [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec, posk)
              \<and> mt_pos c'' tk = base + (block_width (\<Gamma>_tm M) - 1)
              \<and> mt_tape c'' = mt_tape c'
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c'' k' = mt_pos c' k')"
  by (rule ar_read_bit_loop_gen
        [OF ar_read_bit_step vM qQ kge2 posk_proper stg buf0_valid pos_base
            pad0 src0])

text \<open>The proper-cell single-tape read, non-last tape.  From an
  \<open>AR_SimRead\<close> stage at bit-counter \<open>0\<close> with the head over a
  proper block \<open>base = sim_pos p\<close> (\<open>p \<ge> 1\<close>, so
  \<open>0 < base\<close>) whose current cell is not \<open>LE4\<close> and \<open>posk
  tk\<close> proper, the read fires the two look-back steps, the inner
  per-bit loop (\<open>ar_read_bit_loop\<close>), and the bit boundary,
  decoding the \<open>b\<close>-cell block at \<open>base\<close> into \<open>buf
  tk\<close> and landing at the next tape's \<open>AR_SimRead\<close>
  (\<open>k_succ tk\<close>, counter \<open>0\<close>).  The decoded \<open>buf
  tk\<close> is the abstract fold \<open>foldl (ar_acc \<Gamma> bl)
  (gamma_unenum \<Gamma> bl 0)\<close> over the block's \<open>b\<close> cells --
  the form the caller collapses to the source symbol via
  \<open>foldl_ar_acc_cell_repr\<close> once tape-correspondence pins those
  cells to \<open>cell_repr\<close>.  The chain has length \<open>b + 2\<close>
  (look-back 1, look-back 2, loop \<open>b - 1\<close>, boundary).  The
  refined \<open>posk tk\<close> records whether the look-back cell was
  \<open>LE4\<close> (the head sat at \<open>sim_pos 1\<close>).\<close>

text \<open>The snoc step of a left fold over a \<open>map f [0..<b]\<close>:
  for \<open>0 < b\<close> the fold equals one \<open>ar_acc\<close> applied to the
  fold over the first \<open>b - 1\<close> cells and the last cell
  \<open>f (b - 1)\<close>.  This is the boundary/finish step's last-bit
  accumulator collapse, shared by both proper-read consumers.\<close>

lemma ar_acc_foldl_upt_last:
  assumes "0 < k"
  shows "foldl (ar_acc \<Gamma> bl) a (map f [0..<k])
           = ar_acc \<Gamma> bl
               (foldl (ar_acc \<Gamma> bl) a (map f [0..<k - 1])) (f (k - 1))"
proof -
  obtain kk where "k = Suc kk" using assms by (cases k) auto
  thus ?thesis by (simp add: upt_Suc_append)
qed

text \<open>The proper-cell read prefix: the part of a proper-cell
  single-tape read shared by the non-last (\<open>boundary\<close>) and last
  (\<open>finish\<close>) variants.  From an \<open>AR_SimRead\<close> stage at
  bit-counter \<open>0\<close> with the head over a proper block
  \<open>base = sim_pos p\<close> (\<open>0 < base\<close>) whose cell is not
  \<open>LE4\<close> and \<open>posk tk\<close> proper, it fires look-back 1, look-back
  2, and the inner per-bit loop (\<open>ar_read_bit_loop\<close>), reaching
  bit-counter \<open>Suc b\<close> with the head at \<open>base + (b - 1)\<close> and
  \<open>buf tk\<close> the fold over the first \<open>b - 1\<close> cells.  The
  remaining last-bit step (boundary or finish) is added by the
  consumer.  Chain length \<open>Suc b\<close> (\<open>1 + 1 + (b - 1)\<close>).\<close>

text \<open>Relation-generic read proper-prefix scaffold.  The two
  lookback steps and the bit loop are the \<open>leaf_lb1\<close>,
  \<open>leaf_lb2\<close>, \<open>leaf_loop\<close> hypotheses; union and sub versions
  are thin instantiations.\<close>

lemma ar_read_proper_prefix_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_lb1:
        "\<And>cc. \<lbrakk> valid_mttm M;
                 mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                 q \<in> Q_tm M;
                 posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                 mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c1. (cc, c1) \<in> R'
                       \<and> mt_state c1 = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)
                       \<and> mt_tape c1 = mt_tape cc
                       \<and> mt_pos c1 = (mt_pos cc)(tk := mt_pos cc tk - 1)"
      and leaf_lb2:
        "\<And>cc. \<lbrakk> valid_mttm M;
                 mt_state cc = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk);
                 q \<in> Q_tm M;
                 posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                 2 \<le> block_width (\<Gamma>_tm M);
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, Suc 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, Suc 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c2. (cc, c2) \<in> R'
                       \<and> mt_state c2 = (q, AR_SimRead, tk, Suc (Suc 0),
                             buf(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0), dvec,
                             posk(tk := if mt_tape cc tk (mt_pos cc tk) = LE4
                                        then AR_AtFirstProper else AR_AtFurtherProper))
                       \<and> mt_tape c2 = mt_tape cc
                       \<and> mt_pos c2 = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and leaf_loop:
        "\<And>cc buf0' posk' base'. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                 posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                 mt_state cc = (q, AR_SimRead, tk, 2, buf0', dvec, posk');
                 \<forall>k. buf0' k \<in> \<Gamma>_tm M \<union> {bl_tm M};
                 mt_pos cc tk = base';
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 2, buf0', dvec, posk') \<rbrakk>
               \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) - 1)
                       \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                             buf0'(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) (buf0' tk)
                                     (map (\<lambda>m. mt_tape cc tk (base' + m))
                                          [0..<block_width (\<Gamma>_tm M) - 1])),
                             dvec, posk')
                       \<and> mt_pos c'' tk = base' + (block_width (\<Gamma>_tm M) - 1)
                       \<and> mt_tape c'' = mt_tape cc
                       \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c'' k' = mt_pos cc k')"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0"
  let ?cells1 = "map (\<lambda>m. mt_tape c' tk (base + m)) [0..<block_width (\<Gamma>_tm M) - 1]"
  let ?posk' = "posk(tk := if mt_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  have ksuc: "Suc (block_width (\<Gamma>_tm M) - 1) = block_width (\<Gamma>_tm M)"
    using kge2 by (cases "block_width (\<Gamma>_tm M)") auto
  have bsuc: "Suc (base - 1) = base" using base_pos by (cases base) auto
  have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_tm M \<union> {bl_tm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c1 where
      s1: "(c', c1) \<in> R'"
  and st1: "mt_state c1 = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  and tp1: "mt_tape c1 = mt_tape c'"
  and pp1: "mt_pos c1 = (mt_pos c')(tk := mt_pos c' tk - 1)"
    using leaf_lb1[OF vM stg qQ posk_proper notLE vsrc pad0 src0]
    by blast
  have pos1_tk: "mt_pos c1 tk = base - 1" using pp1 pos_base by simp
  have pad_c1: "\<forall>j \<ge> k_tm M. mt_tape c1 j (mt_pos c1 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "mt_tape c1 j (mt_pos c1 j) = mt_tape c' j (mt_pos c' j)"
      using tp1 pp1 jne by simp
    thus "mt_tape c1 j (mt_pos c1 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c1: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
    using src0 by (simp add: ar_stage_bounded_def)
  have i1lt: "Suc 0 < 2 * block_width (\<Gamma>_tm M)" using kge2 by linarith
  have vsrc1: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                 (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
    using i1lt buf_valid by (simp add: ar_valid_stage_def)
  obtain c2 where
      s2: "(c1, c2) \<in> R'"
  and st2: "mt_state c2 = (q, AR_SimRead, tk, Suc (Suc 0),
                buf(tk := ?g0), dvec,
                posk(tk := if mt_tape c1 tk (mt_pos c1 tk) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper))"
  and tp2: "mt_tape c2 = mt_tape c1"
  and pp2: "mt_pos c2 = (mt_pos c1)(tk := Suc (mt_pos c1 tk))"
    using leaf_lb2[OF vM st1 qQ posk_proper kge2 vsrc1 pad_c1 src_c1]
    by blast
  have posk2_eq: "posk(tk := if mt_tape c1 tk (mt_pos c1 tk) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper) = ?posk'"
    by (simp add: tp1 pos1_tk)
  have st2': "mt_state c2 = (q, AR_SimRead, tk, 2, buf(tk := ?g0), dvec, ?posk')"
    using st2 posk2_eq by (simp add: numeral_2_eq_2)
  have tp2': "mt_tape c2 = mt_tape c'" using tp2 tp1 by simp
  have pos2_tk: "mt_pos c2 tk = base" using pp2 pos1_tk bsuc by simp
  have pad_c2: "\<forall>j \<ge> k_tm M. mt_tape c2 j (mt_pos c2 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "mt_tape c2 j (mt_pos c2 j) = mt_tape c1 j (mt_pos c1 j)"
      using tp2 pp2 jne by simp
    thus "mt_tape c2 j (mt_pos c2 j) = BLANK4" using pad_c1 jge by simp
  qed
  have src_c2: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimRead, tk, 2, buf(tk := ?g0), dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have buf0_valid: "\<forall>k. (buf(tk := ?g0)) k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using buf_valid g0_mem by simp
  obtain c3 where
      s3: "(c2, c3) \<in> R' ^^ (block_width (\<Gamma>_tm M) - 1)"
  and st3: "mt_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                (buf(tk := ?g0))
                  (tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ((buf(tk := ?g0)) tk)
                          (map (\<lambda>m. mt_tape c2 tk (base + m))
                               [0..<block_width (\<Gamma>_tm M) - 1])),
                dvec, ?posk')"
  and pp3: "mt_pos c3 tk = base + (block_width (\<Gamma>_tm M) - 1)"
  and tp3: "mt_tape c3 = mt_tape c2"
  and pp3off: "\<forall>k'. k' \<noteq> tk \<longrightarrow> mt_pos c3 k' = mt_pos c2 k'"
    using leaf_loop[OF vM qQ kge2 posk'_proper st2' buf0_valid pos2_tk
                       pad_c2 src_c2]
    by blast
  have st3': "mt_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                dvec, ?posk')"
    using st3 by (simp add: tp2')
  have tp3': "mt_tape c3 = mt_tape c'" using tp3 tp2' by simp
  have pos3: "mt_pos c3 = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
  proof (rule ext)
    fix k'
    show "mt_pos c3 k' = ((mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))) k'"
    proof (cases "k' = tk")
      case True thus ?thesis using pp3 by simp
    next
      case False
      have "mt_pos c3 k' = mt_pos c2 k'" using pp3off False by simp
      also have "\<dots> = mt_pos c1 k'" using pp2 False by simp
      also have "\<dots> = mt_pos c' k'" using pp1 False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch13: "(c1, c3) \<in> R' ^^ Suc (block_width (\<Gamma>_tm M) - 1)"
    by (rule relpow_Suc_I2[OF s2 s3])
  have ch03: "(c', c3) \<in> R' ^^ Suc (Suc (block_width (\<Gamma>_tm M) - 1))"
    by (rule relpow_Suc_I2[OF s1 ch13])
  have eqn: "Suc (Suc (block_width (\<Gamma>_tm M) - 1)) = Suc (block_width (\<Gamma>_tm M))"
    using ksuc by simp
  show ?thesis
  proof (intro exI[where x = c3] conjI)
    show "(c', c3) \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))"
      using ch03 by (simp only: eqn[symmetric])
    show "mt_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
              buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
              dvec, ?posk')"
      by (rule st3')
    show "mt_tape c3 = mt_tape c'" by (rule tp3')
    show "mt_pos c3 = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
      by (rule pos3)
  qed
qed

lemma ar_read_proper_prefix:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ Suc (block_width (\<Gamma>_tm M))
              \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M) - 1])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
  by (rule ar_read_proper_prefix_gen
        [OF ar_read_lookback1_step ar_read_lookback2_step ar_read_bit_loop
            vM qQ kge2 posk_proper stg notLE base_pos pos_base vsrc pad0 src0])

text \<open>The proper-cell single-tape read, non-last tape: the prefix
  followed by the bit-boundary step (\<open>ar_read_bit_boundary_step\<close>),
  decoding the \<open>b\<close>-cell block at \<open>base\<close> into \<open>buf tk\<close>
  (the abstract fold \<open>foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma>
  bl 0)\<close>, collapsed to the source symbol by
  \<open>foldl_ar_acc_cell_repr\<close>) and landing at the next tape's
  \<open>AR_SimRead\<close> (\<open>k_succ tk\<close>, counter \<open>0\<close>).  Chain length
  \<open>b + 2\<close>.\<close>

text \<open>Relation-generic read proper-step scaffold.  The prefix walk
  and the closing bit-boundary step are the \<open>leaf_prefix\<close> and
  \<open>leaf_boundary\<close> hypotheses; union and sub versions are thin
  instantiations.\<close>

lemma ar_read_proper_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_prefix:
        "\<And>cc. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                 posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                 mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                 mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                 0 < base;
                 mt_pos cc tk = base;
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))
                       \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                             buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                                       (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                                       (map (\<lambda>m. mt_tape cc tk (base + m))
                                            [0..<block_width (\<Gamma>_tm M) - 1])),
                             dvec,
                             posk(tk := if mt_tape cc tk (base - 1) = LE4
                                        then AR_AtFirstProper else AR_AtFurtherProper))
                       \<and> mt_tape c'' = mt_tape cc
                       \<and> mt_pos c'' = (mt_pos cc)(tk := base + (block_width (\<Gamma>_tm M) - 1))"
      and leaf_boundary:
        "\<And>cc i buf' posk'. \<lbrakk> valid_mttm M;
                  mt_state cc = (q, AR_SimRead, tk, i, buf', dvec, posk');
                  q \<in> Q_tm M;
                  \<not> is_last_k M tk;
                  posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                  i = Suc (block_width (\<Gamma>_tm M));
                  ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                    (AR_SimRead, tk, i, buf', dvec, posk');
                  \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                  ar_stage_bounded (bl_tm M) (k_tm M)
                    (AR_SimRead, tk, i, buf', dvec, posk') \<rbrakk>
                \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                         \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                               buf'(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                                     (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf' tk)
                                        + bit_value (mt_tape cc tk (mt_pos cc tk)))),
                               dvec, posk')
                         \<and> mt_tape c'' = mt_tape cc
                         \<and> mt_pos c'' = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0"
  let ?cells1 = "map (\<lambda>m. mt_tape c' tk (base + m)) [0..<block_width (\<Gamma>_tm M) - 1]"
  let ?posk' = "posk(tk := if mt_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  have kpos: "0 < block_width (\<Gamma>_tm M)" using kge2 by simp
  have ksuc: "Suc (block_width (\<Gamma>_tm M) - 1) = block_width (\<Gamma>_tm M)"
    using kge2 by (cases "block_width (\<Gamma>_tm M)") auto
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_tm M \<union> {bl_tm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c3 where
      pre_chain: "(c', c3) \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))"
  and pre_st: "mt_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                  dvec, ?posk')"
  and pre_tp: "mt_tape c3 = mt_tape c'"
  and pre_pp: "mt_pos c3 = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
    using leaf_prefix[OF vM qQ kge2 posk_proper stg notLE
                                          base_pos pos_base vsrc pad0 src0] by blast
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have fold3_mem:
      "foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1 \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using g0_mem by (rule foldl_ar_acc_mem[OF finG])
  have buf3_valid:
      "\<forall>k. (buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1)) k
            \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using buf_valid fold3_mem by simp
  have ilt: "Suc (block_width (\<Gamma>_tm M)) < 2 * block_width (\<Gamma>_tm M)" using kge2 by linarith
  have vsrc3: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                 (AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                  dvec, ?posk')"
    using ilt buf3_valid by (simp add: ar_valid_stage_def)
  have pos3_tk: "mt_pos c3 tk = base + (block_width (\<Gamma>_tm M) - 1)" using pre_pp by simp
  have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c3: "\<forall>j \<ge> k_tm M. mt_tape c3 j (mt_pos c3 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "mt_tape c3 j (mt_pos c3 j) = mt_tape c' j (mt_pos c' j)"
      using pre_tp pre_pp jne by simp
    thus "mt_tape c3 j (mt_pos c3 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c3: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                   buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                   dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  obtain c4 where
      s4: "(c3, c4) \<in> R'"
  and st4: "mt_state c4 = (q, AR_SimRead, k_succ tk, 0,
                (buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1))
                  (tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                     (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M)
                            ((buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1)) tk)
                        + bit_value (mt_tape c3 tk (mt_pos c3 tk)))),
                dvec, ?posk')"
  and tp4: "mt_tape c4 = mt_tape c3"
  and pp4: "mt_pos c4 = (mt_pos c3)(tk := Suc (mt_pos c3 tk))"
    using leaf_boundary[OF vM pre_st qQ notlast posk'_proper
                                              refl vsrc3 pad_c3 src_c3] by blast
  have read_cell4: "mt_tape c3 tk (mt_pos c3 tk)
                      = mt_tape c' tk (base + (block_width (\<Gamma>_tm M) - 1))"
    using pre_tp pos3_tk by simp
  have st4': "mt_state c4 = (q, AR_SimRead, k_succ tk, 0,
                buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0
                          (map (\<lambda>m. mt_tape c' tk (base + m))
                               [0..<block_width (\<Gamma>_tm M)])),
                dvec, ?posk')"
    using st4 by (simp add: read_cell4 ar_acc_foldl_upt_last[OF kpos] ar_acc_def)
  have tape4: "mt_tape c4 = mt_tape c'" using tp4 pre_tp by simp
  have pos4: "mt_pos c4 = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  proof (rule ext)
    fix k'
    show "mt_pos c4 k' = ((mt_pos c')(tk := base + block_width (\<Gamma>_tm M))) k'"
    proof (cases "k' = tk")
      case True
      have "mt_pos c4 tk = Suc (mt_pos c3 tk)" using pp4 by simp
      also have "\<dots> = Suc (base + (block_width (\<Gamma>_tm M) - 1))" using pos3_tk by simp
      also have "\<dots> = base + block_width (\<Gamma>_tm M)" using ksuc by simp
      finally show ?thesis using True by simp
    next
      case False
      have "mt_pos c4 k' = mt_pos c3 k'" using pp4 False by simp
      also have "\<dots> = mt_pos c' k'" using pre_pp False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch04: "(c', c4) \<in> R' ^^ Suc (Suc (block_width (\<Gamma>_tm M)))"
    by (rule relpow_Suc_I[OF pre_chain s4])
  have eqn: "Suc (Suc (block_width (\<Gamma>_tm M))) = block_width (\<Gamma>_tm M) + 2" by simp
  show ?thesis
  proof (intro exI[where x = c4] conjI)
    show "(c', c4) \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)"
      using ch04 by (simp only: eqn[symmetric])
    show "mt_state c4 = (q, AR_SimRead, k_succ tk, 0,
              buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0
                        (map (\<lambda>m. mt_tape c' tk (base + m))
                             [0..<block_width (\<Gamma>_tm M)])),
              dvec, ?posk')"
      by (rule st4')
    show "mt_tape c4 = mt_tape c'" by (rule tape4)
    show "mt_pos c4 = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))" by (rule pos4)
  qed
qed

lemma ar_read_proper_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_read_proper_step_gen
        [OF ar_read_proper_prefix ar_read_bit_boundary_step
            vM qQ kge2 notlast posk_proper stg notLE base_pos pos_base vsrc
            pad0 src0])

text \<open>The proper-cell single-tape read, last tape: the prefix
  followed by the bit-finish step (\<open>ar_read_bit_finish_step\<close>),
  decoding the \<open>b\<close>-cell block at \<open>base\<close> into \<open>buf tk\<close>
  exactly as the non-last variant, but transitioning to
  \<open>AR_SimCompute\<close> with the current-tape field reset to
  \<open>k_unidx 0\<close> (all tapes decoded).  Chain length \<open>b + 2\<close>.\<close>

text \<open>Relation-generic read proper-finish-step scaffold.  As
  \<open>ar_read_proper_step_gen\<close> but the closing leaf is the last-tape
  bit-finish (transition to \<open>AR_SimCompute\<close>); the prefix and
  finish helpers are the \<open>leaf_prefix\<close> and \<open>leaf_finish\<close>
  hypotheses.\<close>

lemma ar_read_proper_finish_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_prefix:
        "\<And>cc. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                 posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                 mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                 mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                 0 < base;
                 mt_pos cc tk = base;
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))
                       \<and> mt_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                             buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                                       (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                                       (map (\<lambda>m. mt_tape cc tk (base + m))
                                            [0..<block_width (\<Gamma>_tm M) - 1])),
                             dvec,
                             posk(tk := if mt_tape cc tk (base - 1) = LE4
                                        then AR_AtFirstProper else AR_AtFurtherProper))
                       \<and> mt_tape c'' = mt_tape cc
                       \<and> mt_pos c'' = (mt_pos cc)(tk := base + (block_width (\<Gamma>_tm M) - 1))"
      and leaf_finish:
        "\<And>cc i buf' posk'. \<lbrakk> valid_mttm M;
                  mt_state cc = (q, AR_SimRead, tk, i, buf', dvec, posk');
                  q \<in> Q_tm M;
                  is_last_k M tk;
                  posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                  i = Suc (block_width (\<Gamma>_tm M));
                  ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                    (AR_SimRead, tk, i, buf', dvec, posk');
                  \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                  ar_stage_bounded (bl_tm M) (k_tm M)
                    (AR_SimRead, tk, i, buf', dvec, posk') \<rbrakk>
                \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                         \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                               buf'(tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                                     (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M) (buf' tk)
                                        + bit_value (mt_tape cc tk (mt_pos cc tk)))),
                               dvec, posk')
                         \<and> mt_tape c'' = mt_tape cc
                         \<and> mt_pos c'' = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0"
  let ?cells1 = "map (\<lambda>m. mt_tape c' tk (base + m)) [0..<block_width (\<Gamma>_tm M) - 1]"
  let ?posk' = "posk(tk := if mt_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  have kpos: "0 < block_width (\<Gamma>_tm M)" using kge2 by simp
  have ksuc: "Suc (block_width (\<Gamma>_tm M) - 1) = block_width (\<Gamma>_tm M)"
    using kge2 by (cases "block_width (\<Gamma>_tm M)") auto
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_tm M \<union> {bl_tm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c3 where
      pre_chain: "(c', c3) \<in> R' ^^ Suc (block_width (\<Gamma>_tm M))"
  and pre_st: "mt_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                  dvec, ?posk')"
  and pre_tp: "mt_tape c3 = mt_tape c'"
  and pre_pp: "mt_pos c3 = (mt_pos c')(tk := base + (block_width (\<Gamma>_tm M) - 1))"
    using leaf_prefix[OF vM qQ kge2 posk_proper stg notLE
                                          base_pos pos_base vsrc pad0 src0] by blast
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have fold3_mem:
      "foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1 \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using g0_mem by (rule foldl_ar_acc_mem[OF finG])
  have buf3_valid:
      "\<forall>k. (buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1)) k
            \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using buf_valid fold3_mem by simp
  have ilt: "Suc (block_width (\<Gamma>_tm M)) < 2 * block_width (\<Gamma>_tm M)" using kge2 by linarith
  have vsrc3: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                 (AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                  dvec, ?posk')"
    using ilt buf3_valid by (simp add: ar_valid_stage_def)
  have pos3_tk: "mt_pos c3 tk = base + (block_width (\<Gamma>_tm M) - 1)" using pre_pp by simp
  have tk_lt: "tk < k_tm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c3: "\<forall>j \<ge> k_tm M. mt_tape c3 j (mt_pos c3 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_tm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "mt_tape c3 j (mt_pos c3 j) = mt_tape c' j (mt_pos c' j)"
      using pre_tp pre_pp jne by simp
    thus "mt_tape c3 j (mt_pos c3 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c3: "ar_stage_bounded (bl_tm M) (k_tm M)
                  (AR_SimRead, tk, Suc (block_width (\<Gamma>_tm M)),
                   buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1),
                   dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  obtain c4 where
      s4: "(c3, c4) \<in> R'"
  and st4: "mt_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
                (buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1))
                  (tk := gamma_unenum (\<Gamma>_tm M) (bl_tm M)
                     (2 * gamma_enum (\<Gamma>_tm M) (bl_tm M)
                            ((buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0 ?cells1)) tk)
                        + bit_value (mt_tape c3 tk (mt_pos c3 tk)))),
                dvec, ?posk')"
  and tp4: "mt_tape c4 = mt_tape c3"
  and pp4: "mt_pos c4 = (mt_pos c3)(tk := Suc (mt_pos c3 tk))"
    using leaf_finish[OF vM pre_st qQ last posk'_proper
                                            refl vsrc3 pad_c3 src_c3] by blast
  have read_cell4: "mt_tape c3 tk (mt_pos c3 tk)
                      = mt_tape c' tk (base + (block_width (\<Gamma>_tm M) - 1))"
    using pre_tp pos3_tk by simp
  have st4': "mt_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
                buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0
                          (map (\<lambda>m. mt_tape c' tk (base + m))
                               [0..<block_width (\<Gamma>_tm M)])),
                dvec, ?posk')"
    using st4 by (simp add: read_cell4 ar_acc_foldl_upt_last[OF kpos] ar_acc_def)
  have tape4: "mt_tape c4 = mt_tape c'" using tp4 pre_tp by simp
  have pos4: "mt_pos c4 = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  proof (rule ext)
    fix k'
    show "mt_pos c4 k' = ((mt_pos c')(tk := base + block_width (\<Gamma>_tm M))) k'"
    proof (cases "k' = tk")
      case True
      have "mt_pos c4 tk = Suc (mt_pos c3 tk)" using pp4 by simp
      also have "\<dots> = Suc (base + (block_width (\<Gamma>_tm M) - 1))" using pos3_tk by simp
      also have "\<dots> = base + block_width (\<Gamma>_tm M)" using ksuc by simp
      finally show ?thesis using True by simp
    next
      case False
      have "mt_pos c4 k' = mt_pos c3 k'" using pp4 False by simp
      also have "\<dots> = mt_pos c' k'" using pre_pp False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch04: "(c', c4) \<in> R' ^^ Suc (Suc (block_width (\<Gamma>_tm M)))"
    by (rule relpow_Suc_I[OF pre_chain s4])
  have eqn: "Suc (Suc (block_width (\<Gamma>_tm M))) = block_width (\<Gamma>_tm M) + 2" by simp
  show ?thesis
  proof (intro exI[where x = c4] conjI)
    show "(c', c4) \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)"
      using ch04 by (simp only: eqn[symmetric])
    show "mt_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
              buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M)) ?g0
                        (map (\<lambda>m. mt_tape c' tk (base + m))
                             [0..<block_width (\<Gamma>_tm M)])),
              dvec, ?posk')"
      by (rule st4')
    show "mt_tape c4 = mt_tape c'" by (rule tape4)
    show "mt_pos c4 = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))" by (rule pos4)
  qed
qed

lemma ar_read_proper_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "mt_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ (block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                              (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                              (map (\<lambda>m. mt_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_tm M)])),
                    dvec,
                    posk(tk := if mt_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk := base + block_width (\<Gamma>_tm M))"
  by (rule ar_read_proper_finish_step_gen
        [OF ar_read_proper_prefix ar_read_bit_finish_step
            vM qQ kge2 last posk_proper stg notLE base_pos pos_base vsrc
            pad0 src0])

text \<open>Unified single-tape read, non-last tape: dispatches the per-tape
  read on whether \<open>M\<close>'s head sits on the left-end marker
  (\<open>p = 0\<close>, the LE arm) or in the proper region (\<open>p \<ge> 1\<close>,
  the proper arm) from the per-tape correspondence facts rather than the
  raw cell pattern.  Both arms land back at \<open>AR_SimRead\<close> on the
  successor tape with \<open>buf tk\<close> holding the decoded \<open>M\<close>-symbol
  \<open>tM p\<close> (via \<open>foldl_ar_acc_cell_repr\<close>) and \<open>posk tk\<close>
  re-synced exact to the head's position kind (\<open>AR_AtLE\<close> at
  \<open>0\<close>, \<open>AR_AtFirstProper\<close> at \<open>1\<close>,
  \<open>AR_AtFurtherProper\<close> beyond — the marker test
  \<open>tM' (base - 1) = LE4\<close> coincides with \<open>p = 1\<close> by the
  left-end discipline).  Cost \<open>1\<close> (LE) or \<open>b + 2\<close> (proper).
  This is the uniform per-tape step the read-phase tape walk iterates.\<close>

text \<open>Relation-generic read single-tape step scaffold (non-last).
  The two cases (\<open>p = 0\<close> le-step, \<open>p \<noteq> 0\<close> proper-step)
  are the \<open>leaf_le\<close> and \<open>leaf_proper\<close> hypotheses; union and
  sub versions are thin instantiations.\<close>

lemma ar_read_tape_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_le:
        "\<And>cc. \<lbrakk> valid_mttm M;
                 mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                 q \<in> Q_tm M;
                 \<not> is_last_k M tk;
                 posk tk = AR_AtLE;
                 mt_tape cc tk (mt_pos cc tk) = LE4;
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                       \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                             buf(tk := le_tm M), dvec, posk)
                       \<and> mt_tape c'' = mt_tape cc
                       \<and> mt_pos c'' = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and leaf_proper:
        "\<And>cc base'. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                       \<not> is_last_k M tk;
                       posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                       mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                       mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                       0 < base';
                       mt_pos cc tk = base';
                       ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                         (AR_SimRead, tk, 0, buf, dvec, posk);
                       \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                       ar_stage_bounded (bl_tm M) (k_tm M)
                         (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
                     \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)
                             \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                                   buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                                             (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                                             (map (\<lambda>m. mt_tape cc tk (base' + m))
                                                  [0..<block_width (\<Gamma>_tm M)])),
                                   dvec,
                                   posk(tk := if mt_tape cc tk (base' - 1) = LE4
                                              then AR_AtFirstProper else AR_AtFurtherProper))
                             \<and> mt_tape c'' = mt_tape cc
                             \<and> mt_pos c'' = (mt_pos cc)(tk := base' + block_width (\<Gamma>_tm M))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
proof -
  have kpos: "0 < block_width (\<Gamma>_tm M)" using kge2 by simp
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  have blG: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have tape0: "mt_tape c' tk 0 = LE4"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have tM0: "tM 0 = le_tm M"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have cr_wb: "\<And>x j. j < block_width (\<Gamma>_tm M) \<Longrightarrow>
                 cell_repr (\<Gamma>_tm M) (bl_tm M) x ! j
                   = write_bit (\<Gamma>_tm M) (bl_tm M) x j"
  proof -
    fix x :: 'a and j
    assume jk: "j < block_width (\<Gamma>_tm M)"
    show "cell_repr (\<Gamma>_tm M) (bl_tm M) x ! j
            = write_bit (\<Gamma>_tm M) (bl_tm M) x j"
      using jk by (cases "x = bl_tm M")
        (simp_all add: cell_repr_def write_bit_def length_encode_symbol)
  qed
  show ?thesis
  proof (cases "p = 0")
    case True
    have posk_le: "posk tk = AR_AtLE" using pkok True by simp
    have pos0: "mt_pos c' tk = 0" using ppos True by (simp add: sim_pos_def)
    have aLE: "mt_tape c' tk (mt_pos c' tk) = LE4" using tape0 pos0 by simp
    obtain c'' where
        step: "(c', c'') \<in> R'"
      and st: "mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                                 buf(tk := le_tm M), dvec, posk)"
      and tp: "mt_tape c'' = mt_tape c'"
      and ps: "mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
      using leaf_le[OF vM stg qQ notlast posk_le aLE vsrc pad0 src0] by blast
    have poskid: "posk(tk := AR_AtLE) = posk"
      using posk_le by (simp add: fun_upd_idem)
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> R'
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)"
        using step True by simp
      show "mt_state c'' = (q, AR_SimRead, k_succ tk, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st tM0 True poskid by simp
      show "mt_tape c'' = mt_tape c'" by (rule tp)
      show "mt_pos c'' = (mt_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
        using ps pos0 True by simp
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have bpos: "0 < sim_pos (block_width (\<Gamma>_tm M)) p"
      using pge1 by (simp add: sim_pos_def)
    have posk_ne: "posk tk \<noteq> AR_AtLE" using pkok False by simp
    have posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      using posk_ne by (cases "posk tk") auto
    have corr: "\<forall>j < block_width (\<Gamma>_tm M).
                  mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p + j)
                    = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! j"
      using tcorr pge1 unfolding ar_tape_correspondence_def by blast
    have cell0: "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p)
                   = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! 0"
      using corr[rule_format, OF kpos] by simp
    have notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
    proof -
      have "mt_tape c' tk (mt_pos c' tk)
              = write_bit (\<Gamma>_tm M) (bl_tm M) (tM p) 0"
        using ppos cell0 cr_wb[OF kpos] by simp
      thus ?thesis using write_bit_not_LE4[OF kpos] by simp
    qed
    obtain c'' where
        step: "(c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)"
      and st: "mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                            (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                            (map (\<lambda>m. mt_tape c' tk
                                       (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                                 [0..<block_width (\<Gamma>_tm M)])),
                  dvec,
                  posk(tk := if mt_tape c' tk
                                  (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper))"
      and tp: "mt_tape c'' = mt_tape c'"
      and ps: "mt_pos c'' = (mt_pos c')(tk :=
                  sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
      using leaf_proper[OF vM qQ kge2 notlast posk_proper stg
                                          notLE bpos ppos vsrc pad0 src0] by blast
    have len_cr: "length (cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p))
                    = block_width (\<Gamma>_tm M)"
      by (simp add: cell_repr_def length_encode_symbol)
    have cells_eq: "map (\<lambda>m. mt_tape c' tk
                              (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                         [0..<block_width (\<Gamma>_tm M)]
                      = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p)"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>m. mt_tape c' tk
                              (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                         [0..<block_width (\<Gamma>_tm M)])
              = length (cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p))"
        using len_cr by simp
    next
      fix j
      assume "j < length (map (\<lambda>m. mt_tape c' tk
                                 (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                            [0..<block_width (\<Gamma>_tm M)])"
      hence jk: "j < block_width (\<Gamma>_tm M)" by simp
      show "map (\<lambda>m. mt_tape c' tk
                       (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                  [0..<block_width (\<Gamma>_tm M)] ! j
              = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! j"
        using corr[rule_format, OF jk] jk by simp
    qed
    have decoded: "foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                     (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                     (map (\<lambda>m. mt_tape c' tk
                                (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                          [0..<block_width (\<Gamma>_tm M)])
                     = tM p"
      using cells_eq foldl_ar_acc_cell_repr[OF finG blG proper_mem[OF pge1]]
      by simp
    have resync: "(if mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4
                   then AR_AtFirstProper else AR_AtFurtherProper)
                    = (if p = 1 then AR_AtFirstProper else AR_AtFurtherProper)"
    proof (cases "p = 1")
      case True
      have "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4"
        using True tape0 by (simp add: sim_pos_def)
      thus ?thesis using True by simp
    next
      case False
      with pge1 have pge2: "2 \<le> p" by simp
      then obtain p2 where pp: "p = Suc (Suc p2)"
        using Suc_le_D by (metis Suc_1 le_Suc_ex add_2_eq_Suc)
      obtain k2 where kk: "block_width (\<Gamma>_tm M) = Suc k2"
        using kpos by (cases "block_width (\<Gamma>_tm M)") auto
      have idx_eq: "sim_pos (block_width (\<Gamma>_tm M)) p - 1
                      = sim_pos (block_width (\<Gamma>_tm M)) (p - 1) + (block_width (\<Gamma>_tm M) - 1)"
        by (simp add: sim_pos_def pp kk algebra_simps)
      have pm1: "1 \<le> p - 1" using pge2 by simp
      have corr2: "\<forall>j < block_width (\<Gamma>_tm M).
                     mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) (p - 1) + j)
                       = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM (p - 1)) ! j"
        using tcorr pm1 unfolding ar_tape_correspondence_def by blast
      have km1: "block_width (\<Gamma>_tm M) - 1 < block_width (\<Gamma>_tm M)" using kpos by simp
      have "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1)
              = write_bit (\<Gamma>_tm M) (bl_tm M) (tM (p - 1))
                  (block_width (\<Gamma>_tm M) - 1)"
        using corr2[rule_format, OF km1] idx_eq cr_wb[OF km1] by simp
      hence "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) \<noteq> LE4"
        using write_bit_not_LE4[OF km1] by simp
      thus ?thesis using False by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> R'
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)"
        using step False by simp
      show "mt_state c'' = (q, AR_SimRead, k_succ tk, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st decoded resync False by simp
      show "mt_tape c'' = mt_tape c'" by (rule tp)
      show "mt_pos c'' = (mt_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
        using ps False by simp
    qed
  qed
qed

lemma ar_read_tape_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
  by (rule ar_read_tape_step_gen
        [OF ar_read_le_step ar_read_proper_step
            vM qQ kge2 notlast stg tcorr ppos pkok proper_mem vsrc
            pad0 src0])

text \<open>Unified single-tape read, last tape: as \<open>ar_read_tape_step\<close>
  but \<open>tk\<close> is the last tape, so both arms transition to
  \<open>AR_SimCompute\<close> with the current-tape field reset to
  \<open>k_unidx 0\<close> (all tapes decoded, the read phase complete).  The
  \<open>buf tk\<close> decode and \<open>posk tk\<close> re-sync are identical to the
  non-last variant; only the hand-off target differs.\<close>

text \<open>Relation-generic read single-tape finish-step scaffold
  (last tape).  As \<open>ar_read_tape_step_gen\<close> but both cases use the
  last-tape finish leaves (transition to \<open>AR_SimCompute\<close>); the
  le-finish and proper-finish helpers are the \<open>leaf_le\<close> and
  \<open>leaf_proper\<close> hypotheses.\<close>

lemma ar_read_tape_finish_step_gen:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_le:
        "\<And>cc. \<lbrakk> valid_mttm M;
                 mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                 q \<in> Q_tm M;
                 is_last_k M tk;
                 posk tk = AR_AtLE;
                 mt_tape cc tk (mt_pos cc tk) = LE4;
                 ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk);
                 \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
               \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R'
                       \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                             buf(tk := le_tm M), dvec, posk)
                       \<and> mt_tape c'' = mt_tape cc
                       \<and> mt_pos c'' = (mt_pos cc)(tk := Suc (mt_pos cc tk))"
      and leaf_proper:
        "\<And>cc base'. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                       is_last_k M tk;
                       posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper};
                       mt_state cc = (q, AR_SimRead, tk, 0, buf, dvec, posk);
                       mt_tape cc tk (mt_pos cc tk) \<noteq> LE4;
                       0 < base';
                       mt_pos cc tk = base';
                       ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                         (AR_SimRead, tk, 0, buf, dvec, posk);
                       \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
                       ar_stage_bounded (bl_tm M) (k_tm M)
                         (AR_SimRead, tk, 0, buf, dvec, posk) \<rbrakk>
                     \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)
                             \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                                   buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                                             (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                                             (map (\<lambda>m. mt_tape cc tk (base' + m))
                                                  [0..<block_width (\<Gamma>_tm M)])),
                                   dvec,
                                   posk(tk := if mt_tape cc tk (base' - 1) = LE4
                                              then AR_AtFirstProper else AR_AtFurtherProper))
                             \<and> mt_tape c'' = mt_tape cc
                             \<and> mt_pos c'' = (mt_pos cc)(tk := base' + block_width (\<Gamma>_tm M))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> R' ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
proof -
  have kpos: "0 < block_width (\<Gamma>_tm M)" using kge2 by simp
  have finG: "finite (\<Gamma>_tm M)" by (rule valid_mttm_finite_Gamma[OF vM])
  have blG: "bl_tm M \<in> \<Gamma>_tm M" by (rule valid_mttm_blank_in_Gamma[OF vM])
  have tape0: "mt_tape c' tk 0 = LE4"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have tM0: "tM 0 = le_tm M"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have cr_wb: "\<And>x j. j < block_width (\<Gamma>_tm M) \<Longrightarrow>
                 cell_repr (\<Gamma>_tm M) (bl_tm M) x ! j
                   = write_bit (\<Gamma>_tm M) (bl_tm M) x j"
  proof -
    fix x :: 'a and j
    assume jk: "j < block_width (\<Gamma>_tm M)"
    show "cell_repr (\<Gamma>_tm M) (bl_tm M) x ! j
            = write_bit (\<Gamma>_tm M) (bl_tm M) x j"
      using jk by (cases "x = bl_tm M")
        (simp_all add: cell_repr_def write_bit_def length_encode_symbol)
  qed
  show ?thesis
  proof (cases "p = 0")
    case True
    have posk_le: "posk tk = AR_AtLE" using pkok True by simp
    have pos0: "mt_pos c' tk = 0" using ppos True by (simp add: sim_pos_def)
    have aLE: "mt_tape c' tk (mt_pos c' tk) = LE4" using tape0 pos0 by simp
    obtain c'' where
        step: "(c', c'') \<in> R'"
      and st: "mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                                 buf(tk := le_tm M), dvec, posk)"
      and tp: "mt_tape c'' = mt_tape c'"
      and ps: "mt_pos c'' = (mt_pos c')(tk := Suc (mt_pos c' tk))"
      using leaf_le[OF vM stg qQ last posk_le aLE vsrc pad0 src0]
      by blast
    have poskid: "posk(tk := AR_AtLE) = posk"
      using posk_le by (simp add: fun_upd_idem)
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> R'
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)"
        using step True by simp
      show "mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st tM0 True poskid by simp
      show "mt_tape c'' = mt_tape c'" by (rule tp)
      show "mt_pos c'' = (mt_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
        using ps pos0 True by simp
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have bpos: "0 < sim_pos (block_width (\<Gamma>_tm M)) p"
      using pge1 by (simp add: sim_pos_def)
    have posk_ne: "posk tk \<noteq> AR_AtLE" using pkok False by simp
    have posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      using posk_ne by (cases "posk tk") auto
    have corr: "\<forall>j < block_width (\<Gamma>_tm M).
                  mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p + j)
                    = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! j"
      using tcorr pge1 unfolding ar_tape_correspondence_def by blast
    have cell0: "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p)
                   = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! 0"
      using corr[rule_format, OF kpos] by simp
    have notLE: "mt_tape c' tk (mt_pos c' tk) \<noteq> LE4"
    proof -
      have "mt_tape c' tk (mt_pos c' tk)
              = write_bit (\<Gamma>_tm M) (bl_tm M) (tM p) 0"
        using ppos cell0 cr_wb[OF kpos] by simp
      thus ?thesis using write_bit_not_LE4[OF kpos] by simp
    qed
    obtain c'' where
        step: "(c', c'') \<in> R' ^^ (block_width (\<Gamma>_tm M) + 2)"
      and st: "mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                  buf(tk := foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                            (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                            (map (\<lambda>m. mt_tape c' tk
                                       (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                                 [0..<block_width (\<Gamma>_tm M)])),
                  dvec,
                  posk(tk := if mt_tape c' tk
                                  (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper))"
      and tp: "mt_tape c'' = mt_tape c'"
      and ps: "mt_pos c'' = (mt_pos c')(tk :=
                  sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
      using leaf_proper[OF vM qQ kge2 last posk_proper stg
                                                 notLE bpos ppos vsrc pad0 src0] by blast
    have len_cr: "length (cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p))
                    = block_width (\<Gamma>_tm M)"
      by (simp add: cell_repr_def length_encode_symbol)
    have cells_eq: "map (\<lambda>m. mt_tape c' tk
                              (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                         [0..<block_width (\<Gamma>_tm M)]
                      = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p)"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>m. mt_tape c' tk
                              (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                         [0..<block_width (\<Gamma>_tm M)])
              = length (cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p))"
        using len_cr by simp
    next
      fix j
      assume "j < length (map (\<lambda>m. mt_tape c' tk
                                 (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                            [0..<block_width (\<Gamma>_tm M)])"
      hence jk: "j < block_width (\<Gamma>_tm M)" by simp
      show "map (\<lambda>m. mt_tape c' tk
                       (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                  [0..<block_width (\<Gamma>_tm M)] ! j
              = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM p) ! j"
        using corr[rule_format, OF jk] jk by simp
    qed
    have decoded: "foldl (ar_acc (\<Gamma>_tm M) (bl_tm M))
                     (gamma_unenum (\<Gamma>_tm M) (bl_tm M) 0)
                     (map (\<lambda>m. mt_tape c' tk
                                (sim_pos (block_width (\<Gamma>_tm M)) p + m))
                          [0..<block_width (\<Gamma>_tm M)])
                     = tM p"
      using cells_eq foldl_ar_acc_cell_repr[OF finG blG proper_mem[OF pge1]]
      by simp
    have resync: "(if mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4
                   then AR_AtFirstProper else AR_AtFurtherProper)
                    = (if p = 1 then AR_AtFirstProper else AR_AtFurtherProper)"
    proof (cases "p = 1")
      case True
      have "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) = LE4"
        using True tape0 by (simp add: sim_pos_def)
      thus ?thesis using True by simp
    next
      case False
      with pge1 have pge2: "2 \<le> p" by simp
      then obtain p2 where pp: "p = Suc (Suc p2)"
        using Suc_le_D by (metis Suc_1 le_Suc_ex add_2_eq_Suc)
      obtain k2 where kk: "block_width (\<Gamma>_tm M) = Suc k2"
        using kpos by (cases "block_width (\<Gamma>_tm M)") auto
      have idx_eq: "sim_pos (block_width (\<Gamma>_tm M)) p - 1
                      = sim_pos (block_width (\<Gamma>_tm M)) (p - 1) + (block_width (\<Gamma>_tm M) - 1)"
        by (simp add: sim_pos_def pp kk algebra_simps)
      have pm1: "1 \<le> p - 1" using pge2 by simp
      have corr2: "\<forall>j < block_width (\<Gamma>_tm M).
                     mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) (p - 1) + j)
                       = cell_repr (\<Gamma>_tm M) (bl_tm M) (tM (p - 1)) ! j"
        using tcorr pm1 unfolding ar_tape_correspondence_def by blast
      have km1: "block_width (\<Gamma>_tm M) - 1 < block_width (\<Gamma>_tm M)" using kpos by simp
      have "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1)
              = write_bit (\<Gamma>_tm M) (bl_tm M) (tM (p - 1))
                  (block_width (\<Gamma>_tm M) - 1)"
        using corr2[rule_format, OF km1] idx_eq cr_wb[OF km1] by simp
      hence "mt_tape c' tk (sim_pos (block_width (\<Gamma>_tm M)) p - 1) \<noteq> LE4"
        using write_bit_not_LE4[OF km1] by simp
      thus ?thesis using False by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> R'
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)"
        using step False by simp
      show "mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st decoded resync False by simp
      show "mt_tape c'' = mt_tape c'" by (rule tp)
      show "mt_pos c'' = (mt_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
        using ps False by simp
    qed
  qed
qed

lemma ar_read_tape_finish_step:
  fixes M :: "('q, 'a) mttm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and last: "is_last_k M tk"
      and stg: "mt_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                    tM (mt_tape c' tk)"
      and ppos: "mt_pos c' tk = sim_pos (block_width (\<Gamma>_tm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_tm M"
      and vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c' j (mt_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (mttm_step (alphabet_reduce_delta M))
                              ^^ (if p = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
              \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> mt_tape c'' = mt_tape c'
              \<and> mt_pos c'' = (mt_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) p + block_width (\<Gamma>_tm M))"
  by (rule ar_read_tape_finish_step_gen
        [OF ar_read_le_finish_step ar_read_proper_finish_step
            vM qQ kge2 last stg tcorr ppos pkok proper_mem vsrc
            pad0 src0])

text \<open>The read-phase prefix walk: starting from the read boundary
  (current-tape field \<open>k_unidx 0\<close>, bit-counter
  \<open>0\<close>), iterate the unified non-last per-tape read
  \<open>ar_read_tape_step\<close> over the first \<open>j\<close> tapes of the
  enumeration (\<open>j \<le> k_tm M - 1\<close>, so every tape touched is
  non-last), landing back at \<open>AR_SimRead\<close> on tape
  \<open>k_unidx j\<close>.  The walk descriptor splits on \<open>k_idx k <
  j\<close>: tapes already visited carry the decoded \<open>M\<close>-symbol in
  \<open>buf\<close>, the exact re-synced \<open>posk\<close>, and the block-end
  head position; the rest retain their boundary values.  Variable
  per-tape cost (\<open>1\<close> or \<open>b + 2\<close>), aggregate bounded by
  \<open>j \<cdot> (b + 2)\<close>.  Custom induction on \<open>j\<close>; the
  inductive step's function-update bookkeeping rests on \<open>k_idx\<close>
  injectivity (\<open>k \<noteq> k_unidx j \<Longrightarrow> k_idx k \<noteq>
  j\<close>).\<close>

text \<open>Relation-generic read prefix walk scaffold.  The single
  per-tape helper (\<open>ar_read_tape_step\<close>) is the \<open>leaf\<close>
  hypothesis, quantified over the per-tape config, tape index,
  buffer, position-kind, tape-content function, and position; union
  and sub versions are thin instantiations.\<close>

lemma ar_read_prefix_gen:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf:
        "\<And>cc tk' buf' posk' tM' p'.
           \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
             \<not> is_last_k M tk';
             mt_state cc = (q, AR_SimRead, tk', 0, buf', dvec, posk');
             ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
               tM' (mt_tape cc tk');
             mt_pos cc tk' = sim_pos (block_width (\<Gamma>_tm M)) p';
             posk' tk' = AR_AtLE \<longleftrightarrow> p' = 0;
             1 \<le> p' \<Longrightarrow> tM' p' \<in> \<Gamma>_tm M;
             ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
               (AR_SimRead, tk', 0, buf', dvec, posk');
             \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
             ar_stage_bounded (bl_tm M) (k_tm M)
               (AR_SimRead, tk', 0, buf', dvec, posk') \<rbrakk>
           \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ (if p' = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
                    \<and> mt_state c'' = (q, AR_SimRead, k_succ tk', 0,
                          buf'(tk' := tM' p'), dvec,
                          posk'(tk' := if p' = 0 then AR_AtLE
                                     else if p' = 1 then AR_AtFirstProper
                                     else AR_AtFurtherProper))
                    \<and> mt_tape c'' = mt_tape cc
                    \<and> mt_pos c'' = (mt_pos cc)(tk' :=
                          if p' = 0 then Suc 0
                          else sim_pos (block_width (\<Gamma>_tm M)) p' + block_width (\<Gamma>_tm M))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> R' ^^ m
         \<and> m \<le> j * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimRead, k_unidx j, 0,
              (\<lambda>k. if k_idx k < j then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k_idx k < j
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                           + block_width (\<Gamma>_tm M))
              else mt_pos c0 k))"
proof (induction j)
  case 0
  have "(c0, c0) \<in> R' ^^ 0" by simp
  moreover have "mt_state c0 = (q, AR_SimRead, k_unidx 0, 0,
        (\<lambda>k. if k_idx k < 0 then mt_tape cM k (mt_pos cM k) else buf0 k), dvec,
        (\<lambda>k. if k_idx k < 0
              then (if mt_pos cM k = 0 then AR_AtLE
                    else if mt_pos cM k = 1 then AR_AtFirstProper
                    else AR_AtFurtherProper)
              else posk0 k))"
    using stg0 by (simp add: k_unidx_zero)
  ultimately show ?case
    by (intro exI[where x = c0] exI[where x = 0]) (simp add: ppos)
next
  case (Suc j)
  have sucle: "Suc j \<le> k_tm M - 1" by (rule Suc.prems)
  have jcard: "j < k_tm M" using sucle by simp
  have sjcard: "Suc j < k_tm M" using sucle by simp
  have jle: "j \<le> k_tm M - 1" using sucle by simp
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?tk = "k_unidx j"
  let ?p = "mt_pos cM ?tk"
  let ?aM = "\<lambda>k. mt_tape cM k (mt_pos cM k)"
  let ?bf = "\<lambda>i. (\<lambda>k. if k_idx k < i then ?aM k else buf0 k)"
  let ?pk = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k)"
  let ?ps = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if mt_pos cM k = 0 then Suc 0
                          else sim_pos ?k (mt_pos cM k) + ?k)
                    else mt_pos c0 k)"
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
      cm_rel: "(c0, c) \<in> R' ^^ m"
    and m_le: "m \<le> j * (?k + 2)"
    and c_st: "mt_state c = (q, AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    and c_tp: "mt_tape c = mt_tape c0"
    and c_ps: "mt_pos c = ?ps j"
    using Suc.IH[OF jle] by blast
  have tk_active: "?tk < k_tm M" using jcard by (simp add: k_unidx_def)
  have tk_corr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                   (mt_tape cM ?tk) (mt_tape c ?tk)"
    using tcorr[rule_format, OF tk_active] c_tp by simp
  have tk_pos: "mt_pos c ?tk = sim_pos ?k ?p"
    using c_ps ppos tkidx by simp
  have tk_pkok: "?pk j ?tk = AR_AtLE \<longleftrightarrow> ?p = 0"
    using pkok tkidx by simp
  have bf_in: "\<And>k. ?bf j k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using tapeG bufG by auto
  have tk_vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    using kge2 bf_in by (auto simp: ar_valid_stage_def)
  have pad_c: "\<forall>j' \<ge> k_tm M. mt_tape c j' (mt_pos c j') = BLANK4"
  proof (intro allI impI)
    fix j' assume jge: "k_tm M \<le> j'"
    have jnj: "\<not> k_idx j' < j" using jge jcard by (simp add: k_idx_def)
    have "mt_tape c j' (mt_pos c j') = mt_tape c0 j' (mt_pos c0 j')"
      using c_tp c_ps jnj by simp
    thus "mt_tape c j' (mt_pos c j') = BLANK4" using pad0 jge by simp
  qed
  have src_c: "ar_stage_bounded (bl_tm M) (k_tm M)
                 (AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    using src0 tk_active jcard by (auto simp: ar_stage_bounded_def k_idx_def)
  obtain c' where
      step: "(c, c') \<in> R' ^^ (if ?p = 0 then 1 else ?k + 2)"
    and c'_st: "mt_state c' = (q, AR_SimRead, k_succ ?tk, 0,
                  (?bf j)(?tk := ?aM ?tk), dvec,
                  (?pk j)(?tk := if ?p = 0 then AR_AtLE
                                 else if ?p = 1 then AR_AtFirstProper
                                 else AR_AtFurtherProper))"
    and c'_tp: "mt_tape c' = mt_tape c"
    and c'_ps: "mt_pos c' = (mt_pos c)(?tk :=
                  if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using leaf[OF vM qQ kge2 notlast c_st tk_corr tk_pos
                                      tk_pkok _ tk_vsrc pad_c src_c] tapeG by blast
  have bf_eq: "(?bf j)(?tk := ?aM ?tk) = ?bf (Suc j)"
  proof (rule ext)
    fix k
    show "((?bf j)(?tk := ?aM ?tk)) k = ?bf (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False by (simp add: less_Suc_eq)
    qed
  qed
  have pk_eq: "(?pk j)(?tk := if ?p = 0 then AR_AtLE
                              else if ?p = 1 then AR_AtFirstProper
                              else AR_AtFurtherProper) = ?pk (Suc j)"
  proof (rule ext)
    fix k
    show "((?pk j)(?tk := if ?p = 0 then AR_AtLE
                          else if ?p = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)) k = ?pk (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False by (simp add: less_Suc_eq)
    qed
  qed
  have ps_eq: "(?ps j)(?tk := if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)
                 = ?ps (Suc j)"
  proof (rule ext)
    fix k
    show "((?ps j)(?tk := if ?p = 0 then Suc 0
                          else sim_pos ?k ?p + ?k)) k = ?ps (Suc j) k"
    proof (cases "k = ?tk")
      case True thus ?thesis using tkidx by simp
    next
      case False
      hence "k_idx k \<noteq> j" using kne by blast
      thus ?thesis using False by (simp add: less_Suc_eq)
    qed
  qed
  have chain: "(c0, c') \<in> R' ^^ (m + (if ?p = 0 then 1 else ?k + 2))"
  proof -
    have "(c0, c') \<in> R' ^^ m
                       O R' ^^ (if ?p = 0 then 1 else ?k + 2)"
      using cm_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m + (if ?p = 0 then 1 else ?k + 2) \<le> Suc j * (?k + 2)"
    using m_le by (cases "?p = 0") auto
  show ?case
  proof (intro exI[where x = c'] exI[where x = "m + (if ?p = 0 then 1 else ?k + 2)"]
           conjI)
    show "(c0, c') \<in> R' ^^ (m + (if ?p = 0 then 1 else ?k + 2))" by (rule chain)
    show "m + (if ?p = 0 then 1 else ?k + 2) \<le> Suc j * (?k + 2)"
      by (rule bound)
    show "mt_state c' = (q, AR_SimRead, k_unidx (Suc j), 0, ?bf (Suc j), dvec,
            ?pk (Suc j))"
      using c'_st ksucc bf_eq pk_eq by simp
    show "mt_tape c' = mt_tape c0" using c'_tp c_tp by simp
    show "mt_pos c' = ?ps (Suc j)" using c'_ps c_ps ps_eq by simp
  qed
qed

lemma ar_read_prefix:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_tm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m
         \<and> m \<le> j * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimRead, k_unidx j, 0,
              (\<lambda>k. if k_idx k < j then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k_idx k < j
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k_idx k < j
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                           + block_width (\<Gamma>_tm M))
              else mt_pos c0 k))"
  by (rule ar_read_prefix_gen
        [OF _ vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0])
     (rule ar_read_tape_step; assumption)

text \<open>The full read phase: the prefix walk over the first
  \<open>k_tm M - 1\<close> tapes followed by the unified last-tape read
  \<open>ar_read_tape_finish_step\<close>, landing at \<open>AR_SimCompute\<close>
  (current-tape field \<open>k_unidx 0\<close>) with every tape's
  \<open>M\<close>-read symbol decoded into \<open>buf\<close>, every \<open>posk\<close>
  re-synced exact, and every head left at its block-end (or position
  \<open>1\<close> for an \<open>LE\<close> tape).  Aggregate cost \<open>\<le> k_tm M
  \<cdot> (b + 2)\<close>.  The final \<open>buf\<close>/\<open>posk\<close>/position
  vectors collapse from the \<open>k_idx k < j\<close> split because, on the
  last tape, every other tape has index \<open>< k_tm M - 1\<close>
  (\<open>k_idx\<close> bijective into \<open>{..< k_tm M}\<close>).\<close>

text \<open>Relation-generic full read phase scaffold.  The two helpers
  (prefix walk, last-tape finish) are the \<open>leaf_prefix\<close> and
  \<open>leaf_finish\<close> hypotheses; union and sub versions are thin
  instantiations.  The finish leaf is function-heavy, so it is
  discharged via \<open>(rule \<dots>; assumption)\<close> rather than positional
  \<open>OF\<close>.\<close>

lemma ar_read_phase_gen:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
    and R' :: "(sym4, 'q \<times> 'a ar_stage) mt_config rel"
  assumes leaf_prefix:
        "\<And>jj. \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
                 mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0);
                 \<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                          (mt_tape cM k) (mt_tape c0 k);
                 \<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k);
                 \<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0;
                 \<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M;
                 \<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M};
                 \<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4;
                 ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0);
                 jj \<le> k_tm M - 1 \<rbrakk>
               \<Longrightarrow> (\<exists>c m. (c0, c) \<in> R' ^^ m
                    \<and> m \<le> jj * (block_width (\<Gamma>_tm M) + 2)
                    \<and> mt_state c = (q, AR_SimRead, k_unidx jj, 0,
                         (\<lambda>k. if k_idx k < jj then mt_tape cM k (mt_pos cM k) else buf0 k),
                         dvec,
                         (\<lambda>k. if k_idx k < jj
                               then (if mt_pos cM k = 0 then AR_AtLE
                                     else if mt_pos cM k = 1 then AR_AtFirstProper
                                     else AR_AtFurtherProper)
                               else posk0 k))
                    \<and> mt_tape c = mt_tape c0
                    \<and> mt_pos c = (\<lambda>k. if k_idx k < jj
                         then (if mt_pos cM k = 0 then Suc 0
                               else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)
                                      + block_width (\<Gamma>_tm M))
                         else mt_pos c0 k))"
      and leaf_finish:
        "\<And>cc tk' buf' posk' tM' p'.
           \<lbrakk> valid_mttm M; q \<in> Q_tm M; 2 \<le> block_width (\<Gamma>_tm M);
             is_last_k M tk';
             mt_state cc = (q, AR_SimRead, tk', 0, buf', dvec, posk');
             ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
               tM' (mt_tape cc tk');
             mt_pos cc tk' = sim_pos (block_width (\<Gamma>_tm M)) p';
             posk' tk' = AR_AtLE \<longleftrightarrow> p' = 0;
             1 \<le> p' \<Longrightarrow> tM' p' \<in> \<Gamma>_tm M;
             ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
               (AR_SimRead, tk', 0, buf', dvec, posk');
             \<forall>j \<ge> k_tm M. mt_tape cc j (mt_pos cc j) = BLANK4;
             ar_stage_bounded (bl_tm M) (k_tm M)
               (AR_SimRead, tk', 0, buf', dvec, posk') \<rbrakk>
           \<Longrightarrow> \<exists>c''. (cc, c'') \<in> R' ^^ (if p' = 0 then 1 else block_width (\<Gamma>_tm M) + 2)
                    \<and> mt_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                          buf'(tk' := tM' p'), dvec,
                          posk'(tk' := if p' = 0 then AR_AtLE
                                     else if p' = 1 then AR_AtFirstProper
                                     else AR_AtFurtherProper))
                    \<and> mt_tape c'' = mt_tape cc
                    \<and> mt_pos c'' = (mt_pos cc)(tk' :=
                          if p' = 0 then Suc 0
                          else sim_pos (block_width (\<Gamma>_tm M)) p' + block_width (\<Gamma>_tm M))"
      and vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> R' ^^ m
         \<and> m \<le> k_tm M * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimCompute, k_unidx 0, 0,
              (\<lambda>k. if k < k_tm M then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k < k_tm M
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k) + block_width (\<Gamma>_tm M))
              else mt_pos c0 k)"
proof -
  let ?k = "block_width (\<Gamma>_tm M)"
  let ?N = "k_tm M"
  let ?m1 = "?N - 1"
  let ?tl = "k_unidx ?m1"
  let ?p = "mt_pos cM ?tl"
  let ?aM = "\<lambda>k. mt_tape cM k (mt_pos cM k)"
  have card1: "0 < ?N" using vM by (cases M) auto
  have m1suc: "?N = Suc ?m1" using card1 by simp
  have m1card: "?m1 < ?N" using card1 by simp
  have m1lt: "?m1 < k_tm M" using card1 by simp
  have tl_eq: "?tl = ?m1" by (simp add: k_unidx_def)
  have tlidx: "k_idx ?tl = ?m1" by (rule k_idx_unidx[OF m1card])
  have tl_active: "?tl < k_tm M" using m1lt tl_eq by simp
  have islast: "is_last_k M ?tl" using is_last_k_unidx[OF m1card] m1suc by simp
  \<comment> \<open>A tape index other than the last active one lies strictly below
     \<open>?m1\<close> exactly when it is active; this replaces the deleted
     \<open>k_idx\<close>-surjectivity step (false on padding).\<close>
  have cond: "(k < ?m1) = (k < k_tm M)" if "k \<noteq> ?m1" for k
    using that m1suc by (auto simp: less_Suc_eq)
  let ?bf = "\<lambda>k. if k_idx k < ?m1 then ?aM k else buf0 k"
  let ?pk = "\<lambda>k. if k_idx k < ?m1
                  then (if mt_pos cM k = 0 then AR_AtLE
                        else if mt_pos cM k = 1 then AR_AtFirstProper
                        else AR_AtFurtherProper)
                  else posk0 k"
  let ?ps = "\<lambda>k. if k_idx k < ?m1
                  then (if mt_pos cM k = 0 then Suc 0
                        else sim_pos ?k (mt_pos cM k) + ?k)
                  else mt_pos c0 k"
  obtain c1 m1 where
      c1_rel: "(c0, c1) \<in> R' ^^ m1"
    and m1_le: "m1 \<le> ?m1 * (?k + 2)"
    and c1_st: "mt_state c1 = (q, AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    and c1_tp: "mt_tape c1 = mt_tape c0"
    and c1_ps: "mt_pos c1 = ?ps"
    using leaf_prefix[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0,
                          of ?m1]
    by auto
  have tl_corr: "ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                   (mt_tape cM ?tl) (mt_tape c1 ?tl)"
    using tcorr[rule_format, OF tl_active] c1_tp by simp
  have tl_pos: "mt_pos c1 ?tl = sim_pos ?k ?p"
    using c1_ps ppos tlidx by simp
  have tl_pkok: "?pk ?tl = AR_AtLE \<longleftrightarrow> ?p = 0"
    using pkok tlidx by simp
  have bf_in: "\<And>k. ?bf k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
    using tapeG bufG by auto
  have tl_vsrc: "ar_valid_stage (\<Gamma>_tm M) (bl_tm M)
                   (AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    using kge2 bf_in by (auto simp: ar_valid_stage_def)
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
                  (AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    using src0 tl_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c2 where
      step: "(c1, c2) \<in> R' ^^ (if ?p = 0 then 1 else ?k + 2)"
    and c2_st: "mt_state c2 = (q, AR_SimCompute, k_unidx 0, 0,
                  ?bf(?tl := ?aM ?tl), dvec,
                  ?pk(?tl := if ?p = 0 then AR_AtLE
                             else if ?p = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))"
    and c2_tp: "mt_tape c2 = mt_tape c1"
    and c2_ps: "mt_pos c2 = (mt_pos c1)(?tl :=
                  if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using leaf_finish[OF vM qQ kge2 islast c1_st tl_corr
                                             tl_pos tl_pkok _ tl_vsrc pad_c1 src_c1] tapeG
    by blast
  \<comment> \<open>The last-tape \<open>fun_upd\<close> collapses to the active-guarded
     vector: active tapes (\<open>k < k_tm M\<close>) take the walked value,
     padding tapes stay at their entry value.\<close>
  have bf_full: "?bf(?tl := ?aM ?tl)
                   = (\<lambda>k. if k < k_tm M then ?aM k else buf0 k)"
  proof (rule ext)
    fix k
    show "(?bf(?tl := ?aM ?tl)) k = (if k < k_tm M then ?aM k else buf0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using tl_eq m1lt by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] by (simp add: k_idx_def)
    qed
  qed
  have pk_full: "?pk(?tl := if ?p = 0 then AR_AtLE
                            else if ?p = 1 then AR_AtFirstProper
                            else AR_AtFurtherProper)
                   = (\<lambda>k. if k < k_tm M
                          then (if mt_pos cM k = 0 then AR_AtLE
                                else if mt_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk0 k)"
  proof (rule ext)
    fix k
    show "(?pk(?tl := if ?p = 0 then AR_AtLE
                      else if ?p = 1 then AR_AtFirstProper
                      else AR_AtFurtherProper)) k
            = (if k < k_tm M
               then (if mt_pos cM k = 0 then AR_AtLE
                     else if mt_pos cM k = 1 then AR_AtFirstProper
                     else AR_AtFurtherProper)
               else posk0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using tl_eq m1lt by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis using False kne cond[OF kne] by (simp add: k_idx_def)
    qed
  qed
  have ps_full: "(mt_pos c1)(?tl := if ?p = 0 then Suc 0
                                     else sim_pos ?k ?p + ?k)
                   = (\<lambda>k. if k < k_tm M
                          then (if mt_pos cM k = 0 then Suc 0
                                else sim_pos ?k (mt_pos cM k) + ?k)
                          else mt_pos c0 k)"
  proof (rule ext)
    fix k
    show "((mt_pos c1)(?tl := if ?p = 0 then Suc 0
                              else sim_pos ?k ?p + ?k)) k
            = (if k < k_tm M
               then (if mt_pos cM k = 0 then Suc 0
                     else sim_pos ?k (mt_pos cM k) + ?k)
               else mt_pos c0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using tl_eq m1lt by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis
        using False kne cond[OF kne] c1_ps by (simp add: k_idx_def)
    qed
  qed
  have chain: "(c0, c2) \<in> R' ^^ (m1 + (if ?p = 0 then 1 else ?k + 2))"
  proof -
    have "(c0, c2) \<in> R' ^^ m1
                       O R' ^^ (if ?p = 0 then 1 else ?k + 2)"
      using c1_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m1 + (if ?p = 0 then 1 else ?k + 2) \<le> ?N * (?k + 2)"
  proof -
    obtain Nm where Nm: "?N = Suc Nm" using card1 by (cases ?N) auto
    have e1: "?N * (?k + 2) = (?k + 2) + Nm * (?k + 2)" by (simp add: Nm)
    have e2: "m1 \<le> Nm * (?k + 2)" using m1_le Nm by simp
    have e3: "(if ?p = 0 then 1 else ?k + 2) \<le> ?k + 2" by simp
    show ?thesis using e1 e2 e3 by linarith
  qed
  show ?thesis
  proof (intro exI[where x = c2]
           exI[where x = "m1 + (if ?p = 0 then 1 else ?k + 2)"] conjI)
    show "(c0, c2) \<in> R' ^^ (m1 + (if ?p = 0 then 1 else ?k + 2))" by (rule chain)
    show "m1 + (if ?p = 0 then 1 else ?k + 2) \<le> ?N * (?k + 2)" by (rule bound)
    show "mt_state c2 = (q, AR_SimCompute, k_unidx 0, 0,
            (\<lambda>k. if k < k_tm M then ?aM k else buf0 k), dvec,
            (\<lambda>k. if k < k_tm M
                  then (if mt_pos cM k = 0 then AR_AtLE
                        else if mt_pos cM k = 1 then AR_AtFirstProper
                        else AR_AtFurtherProper)
                  else posk0 k))"
      using c2_st bf_full pk_full by simp
    show "mt_tape c2 = mt_tape c0" using c2_tp c1_tp by simp
    show "mt_pos c2 = (\<lambda>k. if k < k_tm M
            then (if mt_pos cM k = 0 then Suc 0
                  else sim_pos ?k (mt_pos cM k) + ?k)
            else mt_pos c0 k)"
      using c2_ps ps_full by simp
  qed
qed

lemma ar_read_phase:
  fixes M :: "('q, 'a) mttm"
    and cM :: "('a, 'q) mt_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) mt_config"
  assumes vM: "valid_mttm M"
      and qQ: "q \<in> Q_tm M"
      and kge2: "2 \<le> block_width (\<Gamma>_tm M)"
      and stg0: "mt_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_tm M. ar_tape_correspondence (\<Gamma>_tm M) (le_tm M) (bl_tm M)
                       (mt_tape cM k) (mt_tape c0 k)"
      and ppos: "\<And>k. mt_pos c0 k = sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> mt_pos cM k = 0"
      and tapeG: "\<And>k. mt_tape cM k (mt_pos cM k) \<in> \<Gamma>_tm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_tm M \<union> {bl_tm M}"
      and pad0: "\<forall>j \<ge> k_tm M. mt_tape c0 j (mt_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_tm M) (k_tm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (mttm_step (alphabet_reduce_delta M)) ^^ m
         \<and> m \<le> k_tm M * (block_width (\<Gamma>_tm M) + 2)
         \<and> mt_state c = (q, AR_SimCompute, k_unidx 0, 0,
              (\<lambda>k. if k < k_tm M then mt_tape cM k (mt_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k < k_tm M
                    then (if mt_pos cM k = 0 then AR_AtLE
                          else if mt_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> mt_tape c = mt_tape c0
         \<and> mt_pos c = (\<lambda>k. if k < k_tm M
              then (if mt_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_tm M)) (mt_pos cM k) + block_width (\<Gamma>_tm M))
              else mt_pos c0 k)"
  by (rule ar_read_phase_gen
        [OF _ _ vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0];
      (rule ar_read_prefix ar_read_tape_finish_step; assumption))

end
