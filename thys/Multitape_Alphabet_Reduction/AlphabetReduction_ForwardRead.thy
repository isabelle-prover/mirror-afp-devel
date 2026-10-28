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

lemma ar_read_bit_loop:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 2, buf0, dvec, posk)"
      and buf0_valid: "\<forall>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pos_base: "ktc_pos c' tk = base"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 2, buf0, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) - 1)
              \<and> ktc_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                    buf0(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) (buf0 tk)
                            (map (\<lambda>m. ktc_tape c' tk (base + m))
                                 [0..<block_width (\<Gamma>_ktm M) - 1])),
                    dvec, posk)
              \<and> ktc_pos c'' tk = base + (block_width (\<Gamma>_ktm M) - 1)
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c'' k' = ktc_pos c' k')"
proof -
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  let ?fold = "\<lambda>j. foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) (buf0 tk)
                     (map (\<lambda>m. ktc_tape c' tk (base + m)) [0..<j])"
  let ?P = "\<lambda>j c.
       ktc_state c = (q, AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)
     \<and> ktc_pos c tk = base + j
     \<and> ktc_tape c = ktc_tape c'
     \<and> (\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c k' = ktc_pos c' k')"
  have mybase: "?P 0 c'" using stg pos_base by simp
  have mystep:
      "\<And>j cc. \<lbrakk> j < block_width (\<Gamma>_ktm M) - 1; ?P j cc \<rbrakk>
              \<Longrightarrow> \<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))
                          \<and> ?P (Suc j) c''"
  proof -
    fix j cc
    assume jlt: "j < block_width (\<Gamma>_ktm M) - 1" and Pj: "?P j cc"
    from Pj have st_cc:
        "ktc_state cc = (q, AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      and pos_cc: "ktc_pos cc tk = base + j"
      and tape_cc: "ktc_tape cc = ktc_tape c'"
      and other_cc: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos cc k' = ktc_pos c' k'"
      by simp_all
    have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
    have pad_cc: "\<forall>j \<ge> k_ktm M. ktc_tape cc j (ktc_pos cc j) = BLANK4"
    proof (intro allI impI)
      fix j' assume jge: "k_ktm M \<le> j'"
      have jne: "j' \<noteq> tk" using jge tk_lt by simp
      have "ktc_tape cc j' (ktc_pos cc j') = ktc_tape c' j' (ktc_pos c' j')"
        using tape_cc other_cc jne by simp
      thus "ktc_tape cc j' (ktc_pos cc j') = BLANK4" using pad0 jge by simp
    qed
    have src_cc: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                    (AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      using src0 tk_lt by (auto simp: ar_stage_bounded_def)
    have jhi: "j + 2 \<le> block_width (\<Gamma>_ktm M)" using jlt kge2 by linarith
    have foldj_mem: "?fold j \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      using buf0_valid by (intro foldl_ar_acc_mem[OF finG]) simp
    have bufj_valid: "\<forall>k. (buf0(tk := ?fold j)) k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      using buf0_valid foldj_mem by simp
    have vsrc_cc:
        "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
           (AR_SimRead, tk, j + 2, buf0(tk := ?fold j), dvec, posk)"
      using jhi kge2 bufj_valid by (auto simp: ar_valid_stage_def)
    obtain ccc where
        bstep: "(cc, ccc) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
      and bst_state: "ktc_state ccc = (q, AR_SimRead, tk, Suc (j + 2),
            (buf0(tk := ?fold j))
              (tk := gamma_unenum (\<Gamma>_ktm M) (bl_ktm M)
                       (2 * gamma_enum (\<Gamma>_ktm M) (bl_ktm M) ((buf0(tk := ?fold j)) tk)
                          + bit_value (ktc_tape cc tk (ktc_pos cc tk)))),
            dvec, posk)"
      and bst_tape: "ktc_tape ccc = ktc_tape cc"
      and bst_pos: "ktc_pos ccc = (ktc_pos cc)(tk := Suc (ktc_pos cc tk))"
      using ar_read_bit_step[OF vM st_cc qQ posk_proper _ _ kge2 vsrc_cc pad_cc src_cc]
            jhi by force
    have read_cell: "ktc_tape cc tk (ktc_pos cc tk) = ktc_tape c' tk (base + j)"
      using tape_cc pos_cc by simp
    have fold_step:
        "gamma_unenum (\<Gamma>_ktm M) (bl_ktm M)
           (2 * gamma_enum (\<Gamma>_ktm M) (bl_ktm M) (?fold j)
              + bit_value (ktc_tape c' tk (base + j)))
         = ?fold (Suc j)"
    proof -
      have "?fold (Suc j)
              = foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) (buf0 tk)
                  (map (\<lambda>m. ktc_tape c' tk (base + m)) [0..<j]
                     @ [ktc_tape c' tk (base + j)])"
        by (simp add: upt_Suc_append)
      also have "\<dots> = ar_acc (\<Gamma>_ktm M) (bl_ktm M) (?fold j)
                        (ktc_tape c' tk (base + j))"
        by simp
      finally show ?thesis by (simp add: ar_acc_def)
    qed
    have state_eq:
        "ktc_state ccc = (q, AR_SimRead, tk, Suc j + 2,
                          buf0(tk := ?fold (Suc j)), dvec, posk)"
      using bst_state by (simp add: read_cell fold_step)
    have pos_eq: "ktc_pos ccc tk = base + Suc j"
      using bst_pos pos_cc by simp
    have other_eq: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos ccc k' = ktc_pos c' k'"
      using bst_pos other_cc by simp
    have tape_eq: "ktc_tape ccc = ktc_tape c'" using bst_tape tape_cc by simp
    show "\<exists>c''. (cc, c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) \<and> ?P (Suc j) c''"
      using bstep state_eq pos_eq tape_eq other_eq by blast
  qed
  have loop:
      "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) - 1)
            \<and> ?P (block_width (\<Gamma>_ktm M) - 1) c''"
    by (rule relpow_invariant_chain
          [where P = ?P and n = "block_width (\<Gamma>_ktm M) - 1", OF mystep mybase])
  obtain c'' where
      chain: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) - 1)"
    and Pfin: "?P (block_width (\<Gamma>_ktm M) - 1) c''"
    using loop by blast
  have ctr: "(block_width (\<Gamma>_ktm M) - 1) + 2 = Suc (block_width (\<Gamma>_ktm M))"
    using kge2 by simp
  show ?thesis using chain Pfin ctr by (intro exI[where x = c'']) simp
qed

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

lemma ar_read_proper_prefix:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "ktc_tape c' tk (ktc_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "ktc_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (block_width (\<Gamma>_ktm M))
              \<and> ktc_state c'' = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                    buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                              (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                              (map (\<lambda>m. ktc_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_ktm M) - 1])),
                    dvec,
                    posk(tk := if ktc_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0"
  let ?cells1 = "map (\<lambda>m. ktc_tape c' tk (base + m)) [0..<block_width (\<Gamma>_ktm M) - 1]"
  let ?posk' = "posk(tk := if ktc_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  have ksuc: "Suc (block_width (\<Gamma>_ktm M) - 1) = block_width (\<Gamma>_ktm M)"
    using kge2 by (cases "block_width (\<Gamma>_ktm M)") auto
  have bsuc: "Suc (base - 1) = base" using base_pos by (cases base) auto
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c1 where
      s1: "(c', c1) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
  and st1: "ktc_state c1 = (q, AR_SimRead, tk, Suc 0, buf, dvec, posk)"
  and tp1: "ktc_tape c1 = ktc_tape c'"
  and pp1: "ktc_pos c1 = (ktc_pos c')(tk := ktc_pos c' tk - 1)"
    using ar_read_lookback1_step[OF vM stg qQ posk_proper notLE vsrc pad0 src0]
    by blast
  have pos1_tk: "ktc_pos c1 tk = base - 1" using pp1 pos_base by simp
  have pad_c1: "\<forall>j \<ge> k_ktm M. ktc_tape c1 j (ktc_pos c1 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c1 j (ktc_pos c1 j) = ktc_tape c' j (ktc_pos c' j)"
      using tp1 pp1 jne by simp
    thus "ktc_tape c1 j (ktc_pos c1 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c1: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
    using src0 by (simp add: ar_stage_bounded_def)
  have i1lt: "Suc 0 < 2 * block_width (\<Gamma>_ktm M)" using kge2 by linarith
  have vsrc1: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                 (AR_SimRead, tk, Suc 0, buf, dvec, posk)"
    using i1lt buf_valid by (simp add: ar_valid_stage_def)
  obtain c2 where
      s2: "(c1, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
  and st2: "ktc_state c2 = (q, AR_SimRead, tk, Suc (Suc 0),
                buf(tk := ?g0), dvec,
                posk(tk := if ktc_tape c1 tk (ktc_pos c1 tk) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper))"
  and tp2: "ktc_tape c2 = ktc_tape c1"
  and pp2: "ktc_pos c2 = (ktc_pos c1)(tk := Suc (ktc_pos c1 tk))"
    using ar_read_lookback2_step[OF vM st1 qQ posk_proper kge2 vsrc1 pad_c1 src_c1]
    by blast
  have posk2_eq: "posk(tk := if ktc_tape c1 tk (ktc_pos c1 tk) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper) = ?posk'"
    by (simp add: tp1 pos1_tk)
  have st2': "ktc_state c2 = (q, AR_SimRead, tk, 2, buf(tk := ?g0), dvec, ?posk')"
    using st2 posk2_eq by (simp add: numeral_2_eq_2)
  have tp2': "ktc_tape c2 = ktc_tape c'" using tp2 tp1 by simp
  have pos2_tk: "ktc_pos c2 tk = base" using pp2 pos1_tk bsuc by simp
  have pad_c2: "\<forall>j \<ge> k_ktm M. ktc_tape c2 j (ktc_pos c2 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c2 j (ktc_pos c2 j) = ktc_tape c1 j (ktc_pos c1 j)"
      using tp2 pp2 jne by simp
    thus "ktc_tape c2 j (ktc_pos c2 j) = BLANK4" using pad_c1 jge by simp
  qed
  have src_c2: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, tk, 2, buf(tk := ?g0), dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have buf0_valid: "\<forall>k. (buf(tk := ?g0)) k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using buf_valid g0_mem by simp
  obtain c3 where
      s3: "(c2, c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) - 1)"
  and st3: "ktc_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                (buf(tk := ?g0))
                  (tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ((buf(tk := ?g0)) tk)
                          (map (\<lambda>m. ktc_tape c2 tk (base + m))
                               [0..<block_width (\<Gamma>_ktm M) - 1])),
                dvec, ?posk')"
  and pp3: "ktc_pos c3 tk = base + (block_width (\<Gamma>_ktm M) - 1)"
  and tp3: "ktc_tape c3 = ktc_tape c2"
  and pp3off: "\<forall>k'. k' \<noteq> tk \<longrightarrow> ktc_pos c3 k' = ktc_pos c2 k'"
    using ar_read_bit_loop[OF vM qQ kge2 posk'_proper st2' buf0_valid pos2_tk
                       pad_c2 src_c2]
    by blast
  have st3': "ktc_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                dvec, ?posk')"
    using st3 by (simp add: tp2')
  have tp3': "ktc_tape c3 = ktc_tape c'" using tp3 tp2' by simp
  have pos3: "ktc_pos c3 = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
  proof (rule ext)
    fix k'
    show "ktc_pos c3 k' = ((ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))) k'"
    proof (cases "k' = tk")
      case True thus ?thesis using pp3 by simp
    next
      case False
      have "ktc_pos c3 k' = ktc_pos c2 k'" using pp3off False by simp
      also have "\<dots> = ktc_pos c1 k'" using pp2 False by simp
      also have "\<dots> = ktc_pos c' k'" using pp1 False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch13: "(c1, c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (block_width (\<Gamma>_ktm M) - 1)"
    by (rule relpow_Suc_I2[OF s2 s3])
  have ch03: "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (Suc (block_width (\<Gamma>_ktm M) - 1))"
    by (rule relpow_Suc_I2[OF s1 ch13])
  have eqn: "Suc (Suc (block_width (\<Gamma>_ktm M) - 1)) = Suc (block_width (\<Gamma>_ktm M))"
    using ksuc by simp
  show ?thesis
  proof (intro exI[where x = c3] conjI)
    show "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (block_width (\<Gamma>_ktm M))"
      using ch03 by (simp only: eqn[symmetric])
    show "ktc_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
              buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
              dvec, ?posk')"
      by (rule st3')
    show "ktc_tape c3 = ktc_tape c'" by (rule tp3')
    show "ktc_pos c3 = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
      by (rule pos3)
  qed
qed

text \<open>The proper-cell single-tape read, non-last tape: the prefix
  followed by the bit-boundary step (\<open>ar_read_bit_boundary_step\<close>),
  decoding the \<open>b\<close>-cell block at \<open>base\<close> into \<open>buf tk\<close>
  (the abstract fold \<open>foldl (ar_acc \<Gamma> bl) (gamma_unenum \<Gamma>
  bl 0)\<close>, collapsed to the source symbol by
  \<open>foldl_ar_acc_cell_repr\<close>) and landing at the next tape's
  \<open>AR_SimRead\<close> (\<open>k_succ tk\<close>, counter \<open>0\<close>).  Chain length
  \<open>b + 2\<close>.\<close>

lemma ar_read_proper_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and notlast: "\<not> is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "ktc_tape c' tk (ktc_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "ktc_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)
              \<and> ktc_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                              (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                              (map (\<lambda>m. ktc_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_ktm M)])),
                    dvec,
                    posk(tk := if ktc_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0"
  let ?cells1 = "map (\<lambda>m. ktc_tape c' tk (base + m)) [0..<block_width (\<Gamma>_ktm M) - 1]"
  let ?posk' = "posk(tk := if ktc_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using kge2 by simp
  have ksuc: "Suc (block_width (\<Gamma>_ktm M) - 1) = block_width (\<Gamma>_ktm M)"
    using kge2 by (cases "block_width (\<Gamma>_ktm M)") auto
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c3 where
      pre_chain: "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (block_width (\<Gamma>_ktm M))"
  and pre_st: "ktc_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                  dvec, ?posk')"
  and pre_tp: "ktc_tape c3 = ktc_tape c'"
  and pre_pp: "ktc_pos c3 = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
    using ar_read_proper_prefix[OF vM qQ kge2 posk_proper stg notLE
                                          base_pos pos_base vsrc pad0 src0] by blast
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have fold3_mem:
      "foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1 \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using g0_mem by (rule foldl_ar_acc_mem[OF finG])
  have buf3_valid:
      "\<forall>k. (buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1)) k
            \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using buf_valid fold3_mem by simp
  have ilt: "Suc (block_width (\<Gamma>_ktm M)) < 2 * block_width (\<Gamma>_ktm M)" using kge2 by linarith
  have vsrc3: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                 (AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                  dvec, ?posk')"
    using ilt buf3_valid by (simp add: ar_valid_stage_def)
  have pos3_tk: "ktc_pos c3 tk = base + (block_width (\<Gamma>_ktm M) - 1)" using pre_pp by simp
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c3: "\<forall>j \<ge> k_ktm M. ktc_tape c3 j (ktc_pos c3 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c3 j (ktc_pos c3 j) = ktc_tape c' j (ktc_pos c' j)"
      using pre_tp pre_pp jne by simp
    thus "ktc_tape c3 j (ktc_pos c3 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c3: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                   buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                   dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  obtain c4 where
      s4: "(c3, c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
  and st4: "ktc_state c4 = (q, AR_SimRead, k_succ tk, 0,
                (buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1))
                  (tk := gamma_unenum (\<Gamma>_ktm M) (bl_ktm M)
                     (2 * gamma_enum (\<Gamma>_ktm M) (bl_ktm M)
                            ((buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1)) tk)
                        + bit_value (ktc_tape c3 tk (ktc_pos c3 tk)))),
                dvec, ?posk')"
  and tp4: "ktc_tape c4 = ktc_tape c3"
  and pp4: "ktc_pos c4 = (ktc_pos c3)(tk := Suc (ktc_pos c3 tk))"
    using ar_read_bit_boundary_step[OF vM pre_st qQ notlast posk'_proper
                                              refl vsrc3 pad_c3 src_c3] by blast
  have read_cell4: "ktc_tape c3 tk (ktc_pos c3 tk)
                      = ktc_tape c' tk (base + (block_width (\<Gamma>_ktm M) - 1))"
    using pre_tp pos3_tk by simp
  have st4': "ktc_state c4 = (q, AR_SimRead, k_succ tk, 0,
                buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0
                          (map (\<lambda>m. ktc_tape c' tk (base + m))
                               [0..<block_width (\<Gamma>_ktm M)])),
                dvec, ?posk')"
    using st4 by (simp add: read_cell4 ar_acc_foldl_upt_last[OF kpos] ar_acc_def)
  have tape4: "ktc_tape c4 = ktc_tape c'" using tp4 pre_tp by simp
  have pos4: "ktc_pos c4 = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
  proof (rule ext)
    fix k'
    show "ktc_pos c4 k' = ((ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))) k'"
    proof (cases "k' = tk")
      case True
      have "ktc_pos c4 tk = Suc (ktc_pos c3 tk)" using pp4 by simp
      also have "\<dots> = Suc (base + (block_width (\<Gamma>_ktm M) - 1))" using pos3_tk by simp
      also have "\<dots> = base + block_width (\<Gamma>_ktm M)" using ksuc by simp
      finally show ?thesis using True by simp
    next
      case False
      have "ktc_pos c4 k' = ktc_pos c3 k'" using pp4 False by simp
      also have "\<dots> = ktc_pos c' k'" using pre_pp False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch04: "(c', c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (Suc (block_width (\<Gamma>_ktm M)))"
    by (rule relpow_Suc_I[OF pre_chain s4])
  have eqn: "Suc (Suc (block_width (\<Gamma>_ktm M))) = block_width (\<Gamma>_ktm M) + 2" by simp
  show ?thesis
  proof (intro exI[where x = c4] conjI)
    show "(c', c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)"
      using ch04 by (simp only: eqn[symmetric])
    show "ktc_state c4 = (q, AR_SimRead, k_succ tk, 0,
              buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0
                        (map (\<lambda>m. ktc_tape c' tk (base + m))
                             [0..<block_width (\<Gamma>_ktm M)])),
              dvec, ?posk')"
      by (rule st4')
    show "ktc_tape c4 = ktc_tape c'" by (rule tape4)
    show "ktc_pos c4 = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))" by (rule pos4)
  qed
qed

text \<open>The proper-cell single-tape read, last tape: the prefix
  followed by the bit-finish step (\<open>ar_read_bit_finish_step\<close>),
  decoding the \<open>b\<close>-cell block at \<open>base\<close> into \<open>buf tk\<close>
  exactly as the non-last variant, but transitioning to
  \<open>AR_SimCompute\<close> with the current-tape field reset to
  \<open>k_unidx 0\<close> (all tapes decoded).  Chain length \<open>b + 2\<close>.\<close>

lemma ar_read_proper_finish_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and last: "is_last_k M tk"
      and posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and notLE: "ktc_tape c' tk (ktc_pos c' tk) \<noteq> LE4"
      and base_pos: "0 < base"
      and pos_base: "ktc_pos c' tk = base"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)
              \<and> ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                              (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                              (map (\<lambda>m. ktc_tape c' tk (base + m))
                                   [0..<block_width (\<Gamma>_ktm M)])),
                    dvec,
                    posk(tk := if ktc_tape c' tk (base - 1) = LE4
                               then AR_AtFirstProper else AR_AtFurtherProper))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
proof -
  let ?g0 = "gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0"
  let ?cells1 = "map (\<lambda>m. ktc_tape c' tk (base + m)) [0..<block_width (\<Gamma>_ktm M) - 1]"
  let ?posk' = "posk(tk := if ktc_tape c' tk (base - 1) = LE4
                           then AR_AtFirstProper else AR_AtFurtherProper)"
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using kge2 by simp
  have ksuc: "Suc (block_width (\<Gamma>_ktm M) - 1) = block_width (\<Gamma>_ktm M)"
    using kge2 by (cases "block_width (\<Gamma>_ktm M)") auto
  have buf_valid: "\<forall>k. buf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using vsrc by (simp add: ar_valid_stage_def)
  have g0_mem: "?g0 \<in> \<Gamma>_ktm M \<union> {bl_ktm M}" by (rule gamma_unenum_mem[OF finG])
  obtain c3 where
      pre_chain: "(c', c3) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (block_width (\<Gamma>_ktm M))"
  and pre_st: "ktc_state c3 = (q, AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                  dvec, ?posk')"
  and pre_tp: "ktc_tape c3 = ktc_tape c'"
  and pre_pp: "ktc_pos c3 = (ktc_pos c')(tk := base + (block_width (\<Gamma>_ktm M) - 1))"
    using ar_read_proper_prefix[OF vM qQ kge2 posk_proper stg notLE
                                          base_pos pos_base vsrc pad0 src0] by blast
  have posk'_proper: "?posk' tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}" by simp
  have fold3_mem:
      "foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1 \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using g0_mem by (rule foldl_ar_acc_mem[OF finG])
  have buf3_valid:
      "\<forall>k. (buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1)) k
            \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using buf_valid fold3_mem by simp
  have ilt: "Suc (block_width (\<Gamma>_ktm M)) < 2 * block_width (\<Gamma>_ktm M)" using kge2 by linarith
  have vsrc3: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                 (AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                  dvec, ?posk')"
    using ilt buf3_valid by (simp add: ar_valid_stage_def)
  have pos3_tk: "ktc_pos c3 tk = base + (block_width (\<Gamma>_ktm M) - 1)" using pre_pp by simp
  have tk_lt: "tk < k_ktm M" using src0 by (simp add: ar_stage_bounded_def)
  have pad_c3: "\<forall>j \<ge> k_ktm M. ktc_tape c3 j (ktc_pos c3 j) = BLANK4"
  proof (intro allI impI)
    fix j assume jge: "k_ktm M \<le> j"
    have jne: "j \<noteq> tk" using jge tk_lt by simp
    have "ktc_tape c3 j (ktc_pos c3 j) = ktc_tape c' j (ktc_pos c' j)"
      using pre_tp pre_pp jne by simp
    thus "ktc_tape c3 j (ktc_pos c3 j) = BLANK4" using pad0 jge by simp
  qed
  have src_c3: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                  (AR_SimRead, tk, Suc (block_width (\<Gamma>_ktm M)),
                   buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1),
                   dvec, ?posk')"
    using src0 tk_lt by (auto simp: ar_stage_bounded_def)
  obtain c4 where
      s4: "(c3, c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
  and st4: "ktc_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
                (buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1))
                  (tk := gamma_unenum (\<Gamma>_ktm M) (bl_ktm M)
                     (2 * gamma_enum (\<Gamma>_ktm M) (bl_ktm M)
                            ((buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0 ?cells1)) tk)
                        + bit_value (ktc_tape c3 tk (ktc_pos c3 tk)))),
                dvec, ?posk')"
  and tp4: "ktc_tape c4 = ktc_tape c3"
  and pp4: "ktc_pos c4 = (ktc_pos c3)(tk := Suc (ktc_pos c3 tk))"
    using ar_read_bit_finish_step[OF vM pre_st qQ last posk'_proper
                                            refl vsrc3 pad_c3 src_c3] by blast
  have read_cell4: "ktc_tape c3 tk (ktc_pos c3 tk)
                      = ktc_tape c' tk (base + (block_width (\<Gamma>_ktm M) - 1))"
    using pre_tp pos3_tk by simp
  have st4': "ktc_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
                buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0
                          (map (\<lambda>m. ktc_tape c' tk (base + m))
                               [0..<block_width (\<Gamma>_ktm M)])),
                dvec, ?posk')"
    using st4 by (simp add: read_cell4 ar_acc_foldl_upt_last[OF kpos] ar_acc_def)
  have tape4: "ktc_tape c4 = ktc_tape c'" using tp4 pre_tp by simp
  have pos4: "ktc_pos c4 = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))"
  proof (rule ext)
    fix k'
    show "ktc_pos c4 k' = ((ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))) k'"
    proof (cases "k' = tk")
      case True
      have "ktc_pos c4 tk = Suc (ktc_pos c3 tk)" using pp4 by simp
      also have "\<dots> = Suc (base + (block_width (\<Gamma>_ktm M) - 1))" using pos3_tk by simp
      also have "\<dots> = base + block_width (\<Gamma>_ktm M)" using ksuc by simp
      finally show ?thesis using True by simp
    next
      case False
      have "ktc_pos c4 k' = ktc_pos c3 k'" using pp4 False by simp
      also have "\<dots> = ktc_pos c' k'" using pre_pp False by simp
      finally show ?thesis using False by simp
    qed
  qed
  have ch04: "(c', c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ Suc (Suc (block_width (\<Gamma>_ktm M)))"
    by (rule relpow_Suc_I[OF pre_chain s4])
  have eqn: "Suc (Suc (block_width (\<Gamma>_ktm M))) = block_width (\<Gamma>_ktm M) + 2" by simp
  show ?thesis
  proof (intro exI[where x = c4] conjI)
    show "(c', c4) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)"
      using ch04 by (simp only: eqn[symmetric])
    show "ktc_state c4 = (q, AR_SimCompute, k_unidx 0, 0,
              buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M)) ?g0
                        (map (\<lambda>m. ktc_tape c' tk (base + m))
                             [0..<block_width (\<Gamma>_ktm M)])),
              dvec, ?posk')"
      by (rule st4')
    show "ktc_tape c4 = ktc_tape c'" by (rule tape4)
    show "ktc_pos c4 = (ktc_pos c')(tk := base + block_width (\<Gamma>_ktm M))" by (rule pos4)
  qed
qed

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

lemma ar_read_tape_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and notlast: "\<not> is_last_k M tk"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                    tM (ktc_tape c' tk)"
      and ppos: "ktc_pos c' tk = sim_pos (block_width (\<Gamma>_ktm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_ktm M"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)
              \<and> ktc_state c'' = (q, AR_SimRead, k_succ tk, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = (ktc_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
proof -
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using kge2 by simp
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  have blG: "bl_ktm M \<in> \<Gamma>_ktm M" by (rule valid_ktm_blank_in_Gamma[OF vM])
  have tape0: "ktc_tape c' tk 0 = LE4"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have tM0: "tM 0 = le_ktm M"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have cr_wb: "\<And>x j. j < block_width (\<Gamma>_ktm M) \<Longrightarrow>
                 cell_repr (\<Gamma>_ktm M) (bl_ktm M) x ! j
                   = write_bit (\<Gamma>_ktm M) (bl_ktm M) x j"
  proof -
    fix x :: 'a and j
    assume jk: "j < block_width (\<Gamma>_ktm M)"
    show "cell_repr (\<Gamma>_ktm M) (bl_ktm M) x ! j
            = write_bit (\<Gamma>_ktm M) (bl_ktm M) x j"
      using jk by (cases "x = bl_ktm M")
        (simp_all add: cell_repr_def write_bit_def length_encode_symbol)
  qed
  show ?thesis
  proof (cases "p = 0")
    case True
    have posk_le: "posk tk = AR_AtLE" using pkok True by simp
    have pos0: "ktc_pos c' tk = 0" using ppos True by (simp add: sim_pos_def)
    have aLE: "ktc_tape c' tk (ktc_pos c' tk) = LE4" using tape0 pos0 by simp
    obtain c'' where
        step: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
      and st: "ktc_state c'' = (q, AR_SimRead, k_succ tk, 0,
                                 buf(tk := le_ktm M), dvec, posk)"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk := Suc (ktc_pos c' tk))"
      using ar_read_le_step[OF vM stg qQ notlast posk_le aLE vsrc pad0 src0] by blast
    have poskid: "posk(tk := AR_AtLE) = posk"
      using posk_le by (simp add: fun_upd_idem)
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)"
        using step True by simp
      show "ktc_state c'' = (q, AR_SimRead, k_succ tk, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st tM0 True poskid by simp
      show "ktc_tape c'' = ktc_tape c'" by (rule tp)
      show "ktc_pos c'' = (ktc_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
        using ps pos0 True by simp
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have bpos: "0 < sim_pos (block_width (\<Gamma>_ktm M)) p"
      using pge1 by (simp add: sim_pos_def)
    have posk_ne: "posk tk \<noteq> AR_AtLE" using pkok False by simp
    have posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      using posk_ne by (cases "posk tk") auto
    have corr: "\<forall>j < block_width (\<Gamma>_ktm M).
                  ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p + j)
                    = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! j"
      using tcorr pge1 unfolding ar_tape_correspondence_def by blast
    have cell0: "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p)
                   = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! 0"
      using corr[rule_format, OF kpos] by simp
    have notLE: "ktc_tape c' tk (ktc_pos c' tk) \<noteq> LE4"
    proof -
      have "ktc_tape c' tk (ktc_pos c' tk)
              = write_bit (\<Gamma>_ktm M) (bl_ktm M) (tM p) 0"
        using ppos cell0 cr_wb[OF kpos] by simp
      thus ?thesis using write_bit_not_LE4[OF kpos] by simp
    qed
    obtain c'' where
        step: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)"
      and st: "ktc_state c'' = (q, AR_SimRead, k_succ tk, 0,
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                            (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                            (map (\<lambda>m. ktc_tape c' tk
                                       (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                                 [0..<block_width (\<Gamma>_ktm M)])),
                  dvec,
                  posk(tk := if ktc_tape c' tk
                                  (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper))"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk :=
                  sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
      using ar_read_proper_step[OF vM qQ kge2 notlast posk_proper stg
                                          notLE bpos ppos vsrc pad0 src0] by blast
    have len_cr: "length (cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p))
                    = block_width (\<Gamma>_ktm M)"
      by (simp add: cell_repr_def length_encode_symbol)
    have cells_eq: "map (\<lambda>m. ktc_tape c' tk
                              (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                         [0..<block_width (\<Gamma>_ktm M)]
                      = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p)"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>m. ktc_tape c' tk
                              (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                         [0..<block_width (\<Gamma>_ktm M)])
              = length (cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p))"
        using len_cr by simp
    next
      fix j
      assume "j < length (map (\<lambda>m. ktc_tape c' tk
                                 (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                            [0..<block_width (\<Gamma>_ktm M)])"
      hence jk: "j < block_width (\<Gamma>_ktm M)" by simp
      show "map (\<lambda>m. ktc_tape c' tk
                       (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                  [0..<block_width (\<Gamma>_ktm M)] ! j
              = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! j"
        using corr[rule_format, OF jk] jk by simp
    qed
    have decoded: "foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                     (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                     (map (\<lambda>m. ktc_tape c' tk
                                (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                          [0..<block_width (\<Gamma>_ktm M)])
                     = tM p"
      using cells_eq foldl_ar_acc_cell_repr[OF finG blG proper_mem[OF pge1]]
      by simp
    have resync: "(if ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4
                   then AR_AtFirstProper else AR_AtFurtherProper)
                    = (if p = 1 then AR_AtFirstProper else AR_AtFurtherProper)"
    proof (cases "p = 1")
      case True
      have "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4"
        using True tape0 by (simp add: sim_pos_def)
      thus ?thesis using True by simp
    next
      case False
      with pge1 have pge2: "2 \<le> p" by simp
      then obtain p2 where pp: "p = Suc (Suc p2)"
        using Suc_le_D by (metis Suc_1 le_Suc_ex add_2_eq_Suc)
      obtain k2 where kk: "block_width (\<Gamma>_ktm M) = Suc k2"
        using kpos by (cases "block_width (\<Gamma>_ktm M)") auto
      have idx_eq: "sim_pos (block_width (\<Gamma>_ktm M)) p - 1
                      = sim_pos (block_width (\<Gamma>_ktm M)) (p - 1) + (block_width (\<Gamma>_ktm M) - 1)"
        by (simp add: sim_pos_def pp kk algebra_simps)
      have pm1: "1 \<le> p - 1" using pge2 by simp
      have corr2: "\<forall>j < block_width (\<Gamma>_ktm M).
                     ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) (p - 1) + j)
                       = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (p - 1)) ! j"
        using tcorr pm1 unfolding ar_tape_correspondence_def by blast
      have km1: "block_width (\<Gamma>_ktm M) - 1 < block_width (\<Gamma>_ktm M)" using kpos by simp
      have "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1)
              = write_bit (\<Gamma>_ktm M) (bl_ktm M) (tM (p - 1))
                  (block_width (\<Gamma>_ktm M) - 1)"
        using corr2[rule_format, OF km1] idx_eq cr_wb[OF km1] by simp
      hence "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) \<noteq> LE4"
        using write_bit_not_LE4[OF km1] by simp
      thus ?thesis using False by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)"
        using step False by simp
      show "ktc_state c'' = (q, AR_SimRead, k_succ tk, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st decoded resync False by simp
      show "ktc_tape c'' = ktc_tape c'" by (rule tp)
      show "ktc_pos c'' = (ktc_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
        using ps False by simp
    qed
  qed
qed

text \<open>Unified single-tape read, last tape: as \<open>ar_read_tape_step\<close>
  but \<open>tk\<close> is the last tape, so both arms transition to
  \<open>AR_SimCompute\<close> with the current-tape field reset to
  \<open>k_unidx 0\<close> (all tapes decoded, the read phase complete).  The
  \<open>buf tk\<close> decode and \<open>posk tk\<close> re-sync are identical to the
  non-last variant; only the hand-off target differs.\<close>

lemma ar_read_tape_finish_step:
  fixes M :: "('q, 'a) ktm"
    and c' :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
    and tM :: "nat \<Rightarrow> 'a"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and last: "is_last_k M tk"
      and stg: "ktc_state c' = (q, AR_SimRead, tk, 0, buf, dvec, posk)"
      and tcorr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                    tM (ktc_tape c' tk)"
      and ppos: "ktc_pos c' tk = sim_pos (block_width (\<Gamma>_ktm M)) p"
      and pkok: "posk tk = AR_AtLE \<longleftrightarrow> p = 0"
      and proper_mem: "1 \<le> p \<Longrightarrow> tM p \<in> \<Gamma>_ktm M"
      and vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c' j (ktc_pos c' j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, tk, 0, buf, dvec, posk)"
  shows "\<exists>c''. (c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)
              \<and> ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                    buf(tk := tM p), dvec,
                    posk(tk := if p = 0 then AR_AtLE
                               else if p = 1 then AR_AtFirstProper
                               else AR_AtFurtherProper))
              \<and> ktc_tape c'' = ktc_tape c'
              \<and> ktc_pos c'' = (ktc_pos c')(tk :=
                    if p = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
proof -
  have kpos: "0 < block_width (\<Gamma>_ktm M)" using kge2 by simp
  have finG: "finite (\<Gamma>_ktm M)" by (rule valid_ktm_finite_Gamma[OF vM])
  have blG: "bl_ktm M \<in> \<Gamma>_ktm M" by (rule valid_ktm_blank_in_Gamma[OF vM])
  have tape0: "ktc_tape c' tk 0 = LE4"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have tM0: "tM 0 = le_ktm M"
    using tcorr by (simp add: ar_tape_correspondence_def)
  have cr_wb: "\<And>x j. j < block_width (\<Gamma>_ktm M) \<Longrightarrow>
                 cell_repr (\<Gamma>_ktm M) (bl_ktm M) x ! j
                   = write_bit (\<Gamma>_ktm M) (bl_ktm M) x j"
  proof -
    fix x :: 'a and j
    assume jk: "j < block_width (\<Gamma>_ktm M)"
    show "cell_repr (\<Gamma>_ktm M) (bl_ktm M) x ! j
            = write_bit (\<Gamma>_ktm M) (bl_ktm M) x j"
      using jk by (cases "x = bl_ktm M")
        (simp_all add: cell_repr_def write_bit_def length_encode_symbol)
  qed
  show ?thesis
  proof (cases "p = 0")
    case True
    have posk_le: "posk tk = AR_AtLE" using pkok True by simp
    have pos0: "ktc_pos c' tk = 0" using ppos True by (simp add: sim_pos_def)
    have aLE: "ktc_tape c' tk (ktc_pos c' tk) = LE4" using tape0 pos0 by simp
    obtain c'' where
        step: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))"
      and st: "ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                                 buf(tk := le_ktm M), dvec, posk)"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk := Suc (ktc_pos c' tk))"
      using ar_read_le_finish_step[OF vM stg qQ last posk_le aLE vsrc pad0 src0]
      by blast
    have poskid: "posk(tk := AR_AtLE) = posk"
      using posk_le by (simp add: fun_upd_idem)
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)"
        using step True by simp
      show "ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st tM0 True poskid by simp
      show "ktc_tape c'' = ktc_tape c'" by (rule tp)
      show "ktc_pos c'' = (ktc_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
        using ps pos0 True by simp
    qed
  next
    case False
    hence pge1: "1 \<le> p" by simp
    have bpos: "0 < sim_pos (block_width (\<Gamma>_ktm M)) p"
      using pge1 by (simp add: sim_pos_def)
    have posk_ne: "posk tk \<noteq> AR_AtLE" using pkok False by simp
    have posk_proper: "posk tk \<in> {AR_AtFirstProper, AR_AtFurtherProper}"
      using posk_ne by (cases "posk tk") auto
    have corr: "\<forall>j < block_width (\<Gamma>_ktm M).
                  ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p + j)
                    = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! j"
      using tcorr pge1 unfolding ar_tape_correspondence_def by blast
    have cell0: "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p)
                   = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! 0"
      using corr[rule_format, OF kpos] by simp
    have notLE: "ktc_tape c' tk (ktc_pos c' tk) \<noteq> LE4"
    proof -
      have "ktc_tape c' tk (ktc_pos c' tk)
              = write_bit (\<Gamma>_ktm M) (bl_ktm M) (tM p) 0"
        using ppos cell0 cr_wb[OF kpos] by simp
      thus ?thesis using write_bit_not_LE4[OF kpos] by simp
    qed
    obtain c'' where
        step: "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (block_width (\<Gamma>_ktm M) + 2)"
      and st: "ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0,
                  buf(tk := foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                            (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                            (map (\<lambda>m. ktc_tape c' tk
                                       (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                                 [0..<block_width (\<Gamma>_ktm M)])),
                  dvec,
                  posk(tk := if ktc_tape c' tk
                                  (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4
                             then AR_AtFirstProper else AR_AtFurtherProper))"
      and tp: "ktc_tape c'' = ktc_tape c'"
      and ps: "ktc_pos c'' = (ktc_pos c')(tk :=
                  sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
      using ar_read_proper_finish_step[OF vM qQ kge2 last posk_proper stg
                                                 notLE bpos ppos vsrc pad0 src0] by blast
    have len_cr: "length (cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p))
                    = block_width (\<Gamma>_ktm M)"
      by (simp add: cell_repr_def length_encode_symbol)
    have cells_eq: "map (\<lambda>m. ktc_tape c' tk
                              (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                         [0..<block_width (\<Gamma>_ktm M)]
                      = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p)"
    proof (rule nth_equalityI)
      show "length (map (\<lambda>m. ktc_tape c' tk
                              (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                         [0..<block_width (\<Gamma>_ktm M)])
              = length (cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p))"
        using len_cr by simp
    next
      fix j
      assume "j < length (map (\<lambda>m. ktc_tape c' tk
                                 (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                            [0..<block_width (\<Gamma>_ktm M)])"
      hence jk: "j < block_width (\<Gamma>_ktm M)" by simp
      show "map (\<lambda>m. ktc_tape c' tk
                       (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                  [0..<block_width (\<Gamma>_ktm M)] ! j
              = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM p) ! j"
        using corr[rule_format, OF jk] jk by simp
    qed
    have decoded: "foldl (ar_acc (\<Gamma>_ktm M) (bl_ktm M))
                     (gamma_unenum (\<Gamma>_ktm M) (bl_ktm M) 0)
                     (map (\<lambda>m. ktc_tape c' tk
                                (sim_pos (block_width (\<Gamma>_ktm M)) p + m))
                          [0..<block_width (\<Gamma>_ktm M)])
                     = tM p"
      using cells_eq foldl_ar_acc_cell_repr[OF finG blG proper_mem[OF pge1]]
      by simp
    have resync: "(if ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4
                   then AR_AtFirstProper else AR_AtFurtherProper)
                    = (if p = 1 then AR_AtFirstProper else AR_AtFurtherProper)"
    proof (cases "p = 1")
      case True
      have "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) = LE4"
        using True tape0 by (simp add: sim_pos_def)
      thus ?thesis using True by simp
    next
      case False
      with pge1 have pge2: "2 \<le> p" by simp
      then obtain p2 where pp: "p = Suc (Suc p2)"
        using Suc_le_D by (metis Suc_1 le_Suc_ex add_2_eq_Suc)
      obtain k2 where kk: "block_width (\<Gamma>_ktm M) = Suc k2"
        using kpos by (cases "block_width (\<Gamma>_ktm M)") auto
      have idx_eq: "sim_pos (block_width (\<Gamma>_ktm M)) p - 1
                      = sim_pos (block_width (\<Gamma>_ktm M)) (p - 1) + (block_width (\<Gamma>_ktm M) - 1)"
        by (simp add: sim_pos_def pp kk algebra_simps)
      have pm1: "1 \<le> p - 1" using pge2 by simp
      have corr2: "\<forall>j < block_width (\<Gamma>_ktm M).
                     ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) (p - 1) + j)
                       = cell_repr (\<Gamma>_ktm M) (bl_ktm M) (tM (p - 1)) ! j"
        using tcorr pm1 unfolding ar_tape_correspondence_def by blast
      have km1: "block_width (\<Gamma>_ktm M) - 1 < block_width (\<Gamma>_ktm M)" using kpos by simp
      have "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1)
              = write_bit (\<Gamma>_ktm M) (bl_ktm M) (tM (p - 1))
                  (block_width (\<Gamma>_ktm M) - 1)"
        using corr2[rule_format, OF km1] idx_eq cr_wb[OF km1] by simp
      hence "ktc_tape c' tk (sim_pos (block_width (\<Gamma>_ktm M)) p - 1) \<noteq> LE4"
        using write_bit_not_LE4[OF km1] by simp
      thus ?thesis using False by simp
    qed
    show ?thesis
    proof (intro exI[where x = c''] conjI)
      show "(c', c'') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M))
                          ^^ (if p = 0 then 1 else block_width (\<Gamma>_ktm M) + 2)"
        using step False by simp
      show "ktc_state c'' = (q, AR_SimCompute, k_unidx 0, 0, buf(tk := tM p), dvec,
              posk(tk := if p = 0 then AR_AtLE
                         else if p = 1 then AR_AtFirstProper
                         else AR_AtFurtherProper))"
        using st decoded resync False by simp
      show "ktc_tape c'' = ktc_tape c'" by (rule tp)
      show "ktc_pos c'' = (ktc_pos c')(tk :=
              if p = 0 then Suc 0
              else sim_pos (block_width (\<Gamma>_ktm M)) p + block_width (\<Gamma>_ktm M))"
        using ps False by simp
    qed
  qed
qed

text \<open>The read-phase prefix walk: starting from the read boundary
  (current-tape field \<open>k_unidx 0\<close>, bit-counter
  \<open>0\<close>), iterate the unified non-last per-tape read
  \<open>ar_read_tape_step\<close> over the first \<open>j\<close> tapes of the
  enumeration (\<open>j \<le> k_ktm M - 1\<close>, so every tape touched is
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

lemma ar_read_prefix:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c0 k)"
      and ppos: "\<And>k. ktc_pos c0 k = sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
      and tapeG: "\<And>k. ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "j \<le> k_ktm M - 1 \<Longrightarrow>
    (\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m
         \<and> m \<le> j * (block_width (\<Gamma>_ktm M) + 2)
         \<and> ktc_state c = (q, AR_SimRead, k_unidx j, 0,
              (\<lambda>k. if k_idx k < j then ktc_tape cM k (ktc_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k_idx k < j
                    then (if ktc_pos cM k = 0 then AR_AtLE
                          else if ktc_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> ktc_tape c = ktc_tape c0
         \<and> ktc_pos c = (\<lambda>k. if k_idx k < j
              then (if ktc_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)
                           + block_width (\<Gamma>_ktm M))
              else ktc_pos c0 k))"
proof (induction j)
  case 0
  have "(c0, c0) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ 0" by simp
  moreover have "ktc_state c0 = (q, AR_SimRead, k_unidx 0, 0,
        (\<lambda>k. if k_idx k < 0 then ktc_tape cM k (ktc_pos cM k) else buf0 k), dvec,
        (\<lambda>k. if k_idx k < 0
              then (if ktc_pos cM k = 0 then AR_AtLE
                    else if ktc_pos cM k = 1 then AR_AtFirstProper
                    else AR_AtFurtherProper)
              else posk0 k))"
    using stg0 by (simp add: k_unidx_zero)
  ultimately show ?case
    by (intro exI[where x = c0] exI[where x = 0]) (simp add: ppos)
next
  case (Suc j)
  have sucle: "Suc j \<le> k_ktm M - 1" by (rule Suc.prems)
  have jcard: "j < k_ktm M" using sucle by simp
  have sjcard: "Suc j < k_ktm M" using sucle by simp
  have jle: "j \<le> k_ktm M - 1" using sucle by simp
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?tk = "k_unidx j"
  let ?p = "ktc_pos cM ?tk"
  let ?aM = "\<lambda>k. ktc_tape cM k (ktc_pos cM k)"
  let ?bf = "\<lambda>i. (\<lambda>k. if k_idx k < i then ?aM k else buf0 k)"
  let ?pk = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if ktc_pos cM k = 0 then AR_AtLE
                          else if ktc_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k)"
  let ?ps = "\<lambda>i. (\<lambda>k. if k_idx k < i
                    then (if ktc_pos cM k = 0 then Suc 0
                          else sim_pos ?k (ktc_pos cM k) + ?k)
                    else ktc_pos c0 k)"
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
      cm_rel: "(c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m"
    and m_le: "m \<le> j * (?k + 2)"
    and c_st: "ktc_state c = (q, AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    and c_tp: "ktc_tape c = ktc_tape c0"
    and c_ps: "ktc_pos c = ?ps j"
    using Suc.IH[OF jle] by blast
  have tk_active: "?tk < k_ktm M" using jcard by (simp add: k_unidx_def)
  have tk_corr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM ?tk) (ktc_tape c ?tk)"
    using tcorr[rule_format, OF tk_active] c_tp by simp
  have tk_pos: "ktc_pos c ?tk = sim_pos ?k ?p"
    using c_ps ppos tkidx by simp
  have tk_pkok: "?pk j ?tk = AR_AtLE \<longleftrightarrow> ?p = 0"
    using pkok tkidx by simp
  have bf_in: "\<And>k. ?bf j k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using tapeG bufG by auto
  have tk_vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    using kge2 bf_in by (auto simp: ar_valid_stage_def)
  have pad_c: "\<forall>j' \<ge> k_ktm M. ktc_tape c j' (ktc_pos c j') = BLANK4"
  proof (intro allI impI)
    fix j' assume jge: "k_ktm M \<le> j'"
    have jnj: "\<not> k_idx j' < j" using jge jcard by (simp add: k_idx_def)
    have "ktc_tape c j' (ktc_pos c j') = ktc_tape c0 j' (ktc_pos c0 j')"
      using c_tp c_ps jnj by simp
    thus "ktc_tape c j' (ktc_pos c j') = BLANK4" using pad0 jge by simp
  qed
  have src_c: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                 (AR_SimRead, ?tk, 0, ?bf j, dvec, ?pk j)"
    using src0 tk_active jcard by (auto simp: ar_stage_bounded_def k_idx_def)
  obtain c' where
      step: "(c, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if ?p = 0 then 1 else ?k + 2)"
    and c'_st: "ktc_state c' = (q, AR_SimRead, k_succ ?tk, 0,
                  (?bf j)(?tk := ?aM ?tk), dvec,
                  (?pk j)(?tk := if ?p = 0 then AR_AtLE
                                 else if ?p = 1 then AR_AtFirstProper
                                 else AR_AtFurtherProper))"
    and c'_tp: "ktc_tape c' = ktc_tape c"
    and c'_ps: "ktc_pos c' = (ktc_pos c)(?tk :=
                  if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using ar_read_tape_step[OF vM qQ kge2 notlast c_st tk_corr tk_pos
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
  have chain: "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (m + (if ?p = 0 then 1 else ?k + 2))"
  proof -
    have "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m
                       O (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if ?p = 0 then 1 else ?k + 2)"
      using cm_rel step by (rule relcompI)
    thus ?thesis by (simp add: relpow_add)
  qed
  have bound: "m + (if ?p = 0 then 1 else ?k + 2) \<le> Suc j * (?k + 2)"
    using m_le by (cases "?p = 0") auto
  show ?case
  proof (intro exI[where x = c'] exI[where x = "m + (if ?p = 0 then 1 else ?k + 2)"]
           conjI)
    show "(c0, c') \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (m + (if ?p = 0 then 1 else ?k + 2))" by (rule chain)
    show "m + (if ?p = 0 then 1 else ?k + 2) \<le> Suc j * (?k + 2)"
      by (rule bound)
    show "ktc_state c' = (q, AR_SimRead, k_unidx (Suc j), 0, ?bf (Suc j), dvec,
            ?pk (Suc j))"
      using c'_st ksucc bf_eq pk_eq by simp
    show "ktc_tape c' = ktc_tape c0" using c'_tp c_tp by simp
    show "ktc_pos c' = ?ps (Suc j)" using c'_ps c_ps ps_eq by simp
  qed
qed

text \<open>The full read phase: the prefix walk over the first
  \<open>k_ktm M - 1\<close> tapes followed by the unified last-tape read
  \<open>ar_read_tape_finish_step\<close>, landing at \<open>AR_SimCompute\<close>
  (current-tape field \<open>k_unidx 0\<close>) with every tape's
  \<open>M\<close>-read symbol decoded into \<open>buf\<close>, every \<open>posk\<close>
  re-synced exact, and every head left at its block-end (or position
  \<open>1\<close> for an \<open>LE\<close> tape).  Aggregate cost \<open>\<le> k_ktm M
  \<cdot> (b + 2)\<close>.  The final \<open>buf\<close>/\<open>posk\<close>/position
  vectors collapse from the \<open>k_idx k < j\<close> split because, on the
  last tape, every other tape has index \<open>< k_ktm M - 1\<close>
  (\<open>k_idx\<close> bijective into \<open>{..< k_ktm M}\<close>).\<close>

lemma ar_read_phase:
  fixes M :: "('q, 'a) ktm"
    and cM :: "('a, 'q) ktc_config"
    and c0 :: "(sym4, 'q \<times> 'a ar_stage) ktc_config"
  assumes vM: "valid_ktm M"
      and qQ: "q \<in> Q_ktm M"
      and kge2: "2 \<le> block_width (\<Gamma>_ktm M)"
      and stg0: "ktc_state c0 = (q, AR_SimRead, 0, 0, buf0, dvec, posk0)"
      and tcorr: "\<forall>k < k_ktm M. ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                       (ktc_tape cM k) (ktc_tape c0 k)"
      and ppos: "\<And>k. ktc_pos c0 k = sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k)"
      and pkok: "\<And>k. posk0 k = AR_AtLE \<longleftrightarrow> ktc_pos cM k = 0"
      and tapeG: "\<And>k. ktc_tape cM k (ktc_pos cM k) \<in> \<Gamma>_ktm M"
      and bufG: "\<And>k. buf0 k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
      and pad0: "\<forall>j \<ge> k_ktm M. ktc_tape c0 j (ktc_pos c0 j) = BLANK4"
      and src0: "ar_stage_bounded (bl_ktm M) (k_ktm M)
                   (AR_SimRead, 0, 0, buf0, dvec, posk0)"
  shows "\<exists>c m. (c0, c) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m
         \<and> m \<le> k_ktm M * (block_width (\<Gamma>_ktm M) + 2)
         \<and> ktc_state c = (q, AR_SimCompute, k_unidx 0, 0,
              (\<lambda>k. if k < k_ktm M then ktc_tape cM k (ktc_pos cM k) else buf0 k),
              dvec,
              (\<lambda>k. if k < k_ktm M
                    then (if ktc_pos cM k = 0 then AR_AtLE
                          else if ktc_pos cM k = 1 then AR_AtFirstProper
                          else AR_AtFurtherProper)
                    else posk0 k))
         \<and> ktc_tape c = ktc_tape c0
         \<and> ktc_pos c = (\<lambda>k. if k < k_ktm M
              then (if ktc_pos cM k = 0 then Suc 0
                    else sim_pos (block_width (\<Gamma>_ktm M)) (ktc_pos cM k) + block_width (\<Gamma>_ktm M))
              else ktc_pos c0 k)"
proof -
  let ?k = "block_width (\<Gamma>_ktm M)"
  let ?N = "k_ktm M"
  let ?m1 = "?N - 1"
  let ?tl = "k_unidx ?m1"
  let ?p = "ktc_pos cM ?tl"
  let ?aM = "\<lambda>k. ktc_tape cM k (ktc_pos cM k)"
  have card1: "0 < ?N" using vM by (cases M) auto
  have m1suc: "?N = Suc ?m1" using card1 by simp
  have m1card: "?m1 < ?N" using card1 by simp
  have m1lt: "?m1 < k_ktm M" using card1 by simp
  have tl_eq: "?tl = ?m1" by (simp add: k_unidx_def)
  have tlidx: "k_idx ?tl = ?m1" by (rule k_idx_unidx[OF m1card])
  have tl_active: "?tl < k_ktm M" using m1lt tl_eq by simp
  have islast: "is_last_k M ?tl" using is_last_k_unidx[OF m1card] m1suc by simp
  \<comment> \<open>A tape index other than the last active one lies strictly below
     \<open>?m1\<close> exactly when it is active; this replaces the deleted
     \<open>k_idx\<close>-surjectivity step (false on padding).\<close>
  have cond: "(k < ?m1) = (k < k_ktm M)" if "k \<noteq> ?m1" for k
    using that m1suc by (auto simp: less_Suc_eq)
  let ?bf = "\<lambda>k. if k_idx k < ?m1 then ?aM k else buf0 k"
  let ?pk = "\<lambda>k. if k_idx k < ?m1
                  then (if ktc_pos cM k = 0 then AR_AtLE
                        else if ktc_pos cM k = 1 then AR_AtFirstProper
                        else AR_AtFurtherProper)
                  else posk0 k"
  let ?ps = "\<lambda>k. if k_idx k < ?m1
                  then (if ktc_pos cM k = 0 then Suc 0
                        else sim_pos ?k (ktc_pos cM k) + ?k)
                  else ktc_pos c0 k"
  obtain c1 m1 where
      c1_rel: "(c0, c1) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m1"
    and m1_le: "m1 \<le> ?m1 * (?k + 2)"
    and c1_st: "ktc_state c1 = (q, AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    and c1_tp: "ktc_tape c1 = ktc_tape c0"
    and c1_ps: "ktc_pos c1 = ?ps"
    using ar_read_prefix[OF vM qQ kge2 stg0 tcorr ppos pkok tapeG bufG pad0 src0,
                          of ?m1]
    by auto
  have tl_corr: "ar_tape_correspondence (\<Gamma>_ktm M) (le_ktm M) (bl_ktm M)
                   (ktc_tape cM ?tl) (ktc_tape c1 ?tl)"
    using tcorr[rule_format, OF tl_active] c1_tp by simp
  have tl_pos: "ktc_pos c1 ?tl = sim_pos ?k ?p"
    using c1_ps ppos tlidx by simp
  have tl_pkok: "?pk ?tl = AR_AtLE \<longleftrightarrow> ?p = 0"
    using pkok tlidx by simp
  have bf_in: "\<And>k. ?bf k \<in> \<Gamma>_ktm M \<union> {bl_ktm M}"
    using tapeG bufG by auto
  have tl_vsrc: "ar_valid_stage (\<Gamma>_ktm M) (bl_ktm M)
                   (AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    using kge2 bf_in by (auto simp: ar_valid_stage_def)
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
                  (AR_SimRead, ?tl, 0, ?bf, dvec, ?pk)"
    using src0 tl_active tail_idx by (auto simp: ar_stage_bounded_def)
  obtain c2 where
      step: "(c1, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if ?p = 0 then 1 else ?k + 2)"
    and c2_st: "ktc_state c2 = (q, AR_SimCompute, k_unidx 0, 0,
                  ?bf(?tl := ?aM ?tl), dvec,
                  ?pk(?tl := if ?p = 0 then AR_AtLE
                             else if ?p = 1 then AR_AtFirstProper
                             else AR_AtFurtherProper))"
    and c2_tp: "ktc_tape c2 = ktc_tape c1"
    and c2_ps: "ktc_pos c2 = (ktc_pos c1)(?tl :=
                  if ?p = 0 then Suc 0 else sim_pos ?k ?p + ?k)"
    using ar_read_tape_finish_step[OF vM qQ kge2 islast c1_st tl_corr
                                             tl_pos tl_pkok _ tl_vsrc pad_c1 src_c1] tapeG
    by blast
  \<comment> \<open>The last-tape \<open>fun_upd\<close> collapses to the active-guarded
     vector: active tapes (\<open>k < k_ktm M\<close>) take the walked value,
     padding tapes stay at their entry value.\<close>
  have bf_full: "?bf(?tl := ?aM ?tl)
                   = (\<lambda>k. if k < k_ktm M then ?aM k else buf0 k)"
  proof (rule ext)
    fix k
    show "(?bf(?tl := ?aM ?tl)) k = (if k < k_ktm M then ?aM k else buf0 k)"
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
                   = (\<lambda>k. if k < k_ktm M
                          then (if ktc_pos cM k = 0 then AR_AtLE
                                else if ktc_pos cM k = 1 then AR_AtFirstProper
                                else AR_AtFurtherProper)
                          else posk0 k)"
  proof (rule ext)
    fix k
    show "(?pk(?tl := if ?p = 0 then AR_AtLE
                      else if ?p = 1 then AR_AtFirstProper
                      else AR_AtFurtherProper)) k
            = (if k < k_ktm M
               then (if ktc_pos cM k = 0 then AR_AtLE
                     else if ktc_pos cM k = 1 then AR_AtFirstProper
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
  have ps_full: "(ktc_pos c1)(?tl := if ?p = 0 then Suc 0
                                     else sim_pos ?k ?p + ?k)
                   = (\<lambda>k. if k < k_ktm M
                          then (if ktc_pos cM k = 0 then Suc 0
                                else sim_pos ?k (ktc_pos cM k) + ?k)
                          else ktc_pos c0 k)"
  proof (rule ext)
    fix k
    show "((ktc_pos c1)(?tl := if ?p = 0 then Suc 0
                              else sim_pos ?k ?p + ?k)) k
            = (if k < k_ktm M
               then (if ktc_pos cM k = 0 then Suc 0
                     else sim_pos ?k (ktc_pos cM k) + ?k)
               else ktc_pos c0 k)"
    proof (cases "k = ?tl")
      case True thus ?thesis using tl_eq m1lt by simp
    next
      case False
      hence kne: "k \<noteq> ?m1" using tl_eq by simp
      show ?thesis
        using False kne cond[OF kne] c1_ps by (simp add: k_idx_def)
    qed
  qed
  have chain: "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (m1 + (if ?p = 0 then 1 else ?k + 2))"
  proof -
    have "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ m1
                       O (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (if ?p = 0 then 1 else ?k + 2)"
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
    show "(c0, c2) \<in> (ktm_step (alphabet_reduce_delta M \<inter> ar_delta_read M)) ^^ (m1 + (if ?p = 0 then 1 else ?k + 2))" by (rule chain)
    show "m1 + (if ?p = 0 then 1 else ?k + 2) \<le> ?N * (?k + 2)" by (rule bound)
    show "ktc_state c2 = (q, AR_SimCompute, k_unidx 0, 0,
            (\<lambda>k. if k < k_ktm M then ?aM k else buf0 k), dvec,
            (\<lambda>k. if k < k_ktm M
                  then (if ktc_pos cM k = 0 then AR_AtLE
                        else if ktc_pos cM k = 1 then AR_AtFirstProper
                        else AR_AtFurtherProper)
                  else posk0 k))"
      using c2_st bf_full pk_full by simp
    show "ktc_tape c2 = ktc_tape c0" using c2_tp c1_tp by simp
    show "ktc_pos c2 = (\<lambda>k. if k < k_ktm M
            then (if ktc_pos cM k = 0 then Suc 0
                  else sim_pos ?k (ktc_pos cM k) + ?k)
            else ktc_pos c0 k)"
      using c2_ps ps_full by simp
  qed
qed

end
